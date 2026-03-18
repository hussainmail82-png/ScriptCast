import os
import re
import hashlib
import asyncio
from pathlib import Path
from flask import Flask, request, jsonify, render_template
from collections import Counter

import pdfplumber
import xml.etree.ElementTree as ET
import edge_tts

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
app = Flask(__name__, template_folder=os.path.join(BASE_DIR, 'Templates'))
CACHE_DIR = Path(os.path.join(BASE_DIR, 'audio_cache'))
CACHE_DIR.mkdir(exist_ok=True)

# ---------------------------------------------------------------------------
# Spec constants (from FDX ElementSettings, US Letter, Courier 12pt)
# Page: 8.5" wide. 1pt = 1/72". 1char = 0.1" in Courier 12pt.
# Indents measured from LEFT PAGE EDGE in inches.
# ---------------------------------------------------------------------------
ELEMENT_INDENTS = {
    # (left_inch, right_inch)  right = right boundary from left edge
    'scene_heading': (1.50, 7.50),  # 60 chars
    'action':        (1.50, 7.50),  # 60 chars
    'character':     (3.50, 7.25),  # 37 chars
    'parenthetical': (3.00, 5.50),  # 25 chars
    'dialogue':      (2.50, 6.00),  # 35 chars
    'transition':    (5.50, 7.10),  # 16 chars, right-aligned
    'shot':          (1.50, 7.50),  # same as action
}
PAGE_WIDTH_INCH = 8.5

# ---------------------------------------------------------------------------
# Unicode normalisation
# ---------------------------------------------------------------------------
UNICODE_MAP = {
    "\u2018": "'", "\u2019": "'",
    "\u201c": '"', "\u201d": '"',
    "\u2026": "...", "\u2013": "-", "\u2014": "--",
}

def normalise_unicode(text):
    for src, dst in UNICODE_MAP.items():
        text = text.replace(src, dst)
    return text

# ---------------------------------------------------------------------------
# TTS abbreviation expansion
# ---------------------------------------------------------------------------
ABBREV = {
    r"\bMR\.": "Mister", r"\bMRS\.": "Missus", r"\bDR\.": "Doctor",
    r"\bINT\.": "Interior", r"\bEXT\.": "Exterior",
    r"\bV\.O\.": "Voice Over", r"\bO\.S\.": "Off Screen",
    r"\bO\.C\.": "Off Camera", r"\bSGT\.": "Sergeant",
    r"\.\.\.": " (pause) ", r"--": " (pause) ",
}

def expand_abbrevs(text):
    for pattern, replacement in ABBREV.items():
        text = re.sub(pattern, replacement, text, flags=re.IGNORECASE)
    # "/" in dialogue/action → natural spoken form
    # "mid/late" → "mid to late", "INT./EXT." already handled
    text = re.sub(r'(\w+)/(\w+)', lambda m: f"{m.group(1)} to {m.group(2)}", text)
    # Remove double spaces
    text = re.sub(r'  +', ' ', text)
    return text

# Scene heading tokens → spoken form
_SCENE_INT_EXT = [
    (re.compile(r'INT\./EXT\.', re.I), 'Interior Exterior'),
    (re.compile(r'EXT\./INT\.', re.I), 'Exterior Interior'),
    (re.compile(r'I/E\.?',      re.I), 'Interior Exterior'),
    (re.compile(r'INT\.?',      re.I), 'Interior'),
    (re.compile(r'EXT\.?',      re.I), 'Exterior'),
]
# Scene number pattern: leading/trailing digits
_SCENE_NUM = re.compile(r'^(\d+[A-Z]?)\s+(.*?)(?:\s+(\d+[A-Z]?))?\s*$')

def format_scene_heading_tts(raw):
    """
    Convert a scene heading to natural spoken form for TTS.
    "1 EXT. BOAT. DAY. 1"  →  "Scene 1. Exterior. Boat. Day."
    "2 INT. CHARLES HOUSE. CONTINUOUS. 2"  →  "Scene 2. Interior. Charles House. Continuous."
    """
    text = raw.strip()

    # Extract scene number if present
    m = _SCENE_NUM.match(text)
    if m:
        scene_num   = m.group(1)
        heading_body = m.group(2).strip()
        prefix = f"Scene {scene_num}. "
    else:
        scene_num    = None
        heading_body = text
        prefix       = "Scene. "

    # Replace INT./EXT. abbreviations
    for pat, rep in _SCENE_INT_EXT:
        heading_body = pat.sub(rep, heading_body)

    # Replace separator dashes with pauses
    heading_body = re.sub(r'\s*[-–—]+\s*', '. ', heading_body)

    # Remove trailing dots/spaces then add final period
    heading_body = heading_body.strip('. ').strip()

    # Capitalise each segment nicely
    parts = [p.strip().capitalize() for p in heading_body.split('.') if p.strip()]
    spoken = prefix + '. '.join(parts) + '.'

    return spoken

# ---------------------------------------------------------------------------
# Character ID normalisation (Spec §6.2)
# Handles: "JiM:", "GrACE:", "Jim", "GRACE (CONT'D)" → "JIM", "GRACE"
# ---------------------------------------------------------------------------
QUALIFIER_PAT = re.compile(r"\s*\([^)]*\)\s*$")
STRIP_COLON   = re.compile(r":+$")
STRIP_ENDS    = re.compile(r"^[^A-Z0-9']+|[^A-Z0-9']+$")
SLUGIFY       = re.compile(r"[\s\-]+")

def normalise_character_id(raw):
    s = raw.strip().upper()
    # Strip ALL parenthetical content anywhere in string (spec §6.2)
    s = re.sub(r"\s*\([^)]*\)\s*", " ", s).strip()
    # Strip trailing colon(s)
    s = STRIP_COLON.sub("", s).strip()
    # Collapse whitespace
    s = re.sub(r"\s+", " ", s)
    # Strip non-name chars from ends
    s = STRIP_ENDS.sub("", s).strip()
    return s

# Auto-inserted strings to strip from character/dialogue (Spec §10)
AUTO_CONTINUEDS = re.compile(
    r"\s*\((?:MORE|CONT'D|CONTINUED)\)\s*$", re.IGNORECASE
)

# ---------------------------------------------------------------------------
# FDX Parser (Spec §11.1)
# ---------------------------------------------------------------------------
def parse_fdx(file_path):
    tree = ET.parse(file_path)
    root = tree.getroot()

    # Read auto-insert strings to strip
    more_str = "(MORE)"
    contd_str = "(CONT'D)"
    db = root.find(".//DialogueBreaks")
    if db is not None:
        more_str  = db.get("DialogueBottom", more_str)
        contd_str = db.get("DialogueTop", contd_str)

    elements = []
    pending_char = None
    pending_char_id = None

    for para in root.findall("./Content/Paragraph"):
        ptype = para.get("Type", "Action")

        # Concatenate ALL <Text> children (Spec §3.2 multi-Text)
        raw = "".join(t.text or "" for t in para.iter("Text")).strip()
        raw = normalise_unicode(raw)
        if not raw:
            continue

        # Strip auto-inserted continueds (Spec §10)
        raw = AUTO_CONTINUEDS.sub("", raw).strip()
        if not raw:
            continue

        if ptype == "Scene Heading":
            text = raw.upper()  # Spec §11.3 — always uppercase
            scene_num = para.get("Number", "")
            sp = para.find("SceneProperties")
            fdx_page = int(sp.get("Page", 1)) if sp is not None else 1
            display = f"{scene_num} {text} {scene_num}".strip() if scene_num else text
            elements.append({
                "type": "scene_heading",
                "text": text,
                "display_text": display,
                "scene_number": scene_num,
                "page": fdx_page,
            })
            pending_char = None
            pending_char_id = None

        elif ptype == "Transition":
            text = raw.upper()
            elements.append({
                "type": "transition",
                "text": text,
                "display_text": text,
                "page": 1,
            })
            pending_char = None
            pending_char_id = None

        elif ptype == "Shot":
            text = raw.upper()
            elements.append({
                "type": "shot",
                "text": text,
                "display_text": text,
                "page": 1,
            })

        elif ptype == "Character":
            # Normalise character ID (Spec §6.2)
            char_id = normalise_character_id(raw)
            display  = raw.upper()
            pending_char    = display
            pending_char_id = char_id
            elements.append({
                "type": "character",
                "text": char_id,
                "display_text": display,
                "character": char_id,
                "page": 1,
            })

        elif ptype == "Parenthetical":
            text = raw if raw.startswith("(") else f"({raw})"
            elements.append({
                "type": "parenthetical",
                "text": text,
                "display_text": text,
                "character": pending_char_id,
                "page": 1,
            })

        elif ptype == "Dialogue":
            # Strip trailing (MORE) / (CONT'D) from dialogue text
            text = AUTO_CONTINUEDS.sub("", raw).strip()
            elements.append({
                "type": "dialogue",
                "text": text,
                "display_text": text,
                "character": pending_char_id,
                "page": 1,
            })

        else:  # Action, General, Cast List, etc.
            # Treat END. / THE END / FADE OUT. etc as transitions
            el_type = "action"
            if re.match(r"^\s*(END\.|THE END\.?|FADE OUT\.?|FADE TO BLACK\.?)\s*$", raw, re.I):
                el_type = "transition"
                raw = raw.upper()
            elements.append({
                "type": el_type,
                "text": raw,
                "display_text": raw,
                "page": 1,
            })
            pending_char    = None
            pending_char_id = None

    return elements, {}


# ---------------------------------------------------------------------------
# PDF Parser — uses measured x0 positions to classify elements
# Spec §2.1: indents in inches from left page edge
# At 72dpi equivalent: 1" = 72pt. pdfplumber returns pt coords.
# ---------------------------------------------------------------------------

# Spec §3.1 scene heading tokens
SCENE_PREFIXES = re.compile(
    r"^\s*(INT\.|EXT\.|INT\./EXT\.|EXT\./INT\.|I/E\.?|I/E\s)\s*",
    re.IGNORECASE
)
SCENE_NUMBERED = re.compile(
    r"^\s*(\d+[A-Z]?)\s+(INT\.|EXT\.|INT\./EXT\.|EXT\./INT\.|I/E)\s*",
    re.IGNORECASE
)

# Spec §3.6 transitions
TRANSITION_PAT = re.compile(
    r"^\s*(CUT TO:|FADE OUT\.|FADE TO:|FADE TO BLACK\.|DISSOLVE TO:|"
    r"SMASH CUT TO:|MATCH CUT TO:|JUMP CUT TO:|BACK TO:|FADE IN:)\s*$",
    re.IGNORECASE
)

# Strings to strip from any line
STRIP_PAT = re.compile(
    r"^\s*\(?(CONTINUED|CONT'D|MORE)\)?:?\s*$", re.IGNORECASE
)
PAGE_NUM_PAT = re.compile(r"^\s*\d+\.?\s*$")
# Doubled page number artefact from some PDF renderers: "22.." "33.." "44.."
DOUBLED_PAGE_PAT = re.compile(r"^(\d)\1\.{2}$|^(\d{2})\2\.{2}$")
NON_CHAR_PAT = re.compile(
    r"^\s*(WRITTEN BY|DIRECTED BY|PRODUCED BY|THE END|TITLE CARD|SUPER|"
    r"FADE IN\.?|FADE OUT\.?|SMASH CUT|CUT TO|DISSOLVE TO|BLACK|"
    r"CONTINUED|MORE|END\.)\s*$", re.IGNORECASE
)

# Spec §2.1 — indent thresholds in points (1" = 72pt)
# US Letter 8.5" page. pdfplumber x0 is from left edge of page.
THRESH = {
    # If x0 < action_right (1.5" = 108pt) → action/scene heading territory
    'action_left':       108,   # 1.50" × 72
    # dialogue left = 2.50" = 180pt
    'dialogue_left':     180,
    # parenthetical left = 3.00" = 216pt
    'parenthetical_left':216,
    # character left = 3.50" = 252pt
    'character_left':    252,
    # transition left = 5.50" = 396pt
    'transition_left':   396,
}

def classify_line(x0, text):
    """Classify a line by its x0 indentation (in pt) and content."""
    stripped = text.strip()
    if not stripped:
        return None, stripped

    # Scene heading — starts with INT./EXT. etc regardless of indent
    if SCENE_PREFIXES.match(stripped) or SCENE_NUMBERED.match(stripped):
        return 'scene_heading', stripped.upper()

    # Transition
    if TRANSITION_PAT.match(stripped):
        return 'transition', stripped.upper()

    # Use x0 to classify by indent bucket
    if x0 >= THRESH['transition_left']:
        # Transition zone — check for ALL CAPS ending in colon/period
        if stripped.isupper() or re.match(r'^[A-Z ]+[:.]\s*$', stripped):
            return 'transition', stripped.upper()
        return 'action', stripped  # fallback

    if x0 >= THRESH['character_left']:
        # Character zone — must be ALL CAPS, not a known non-character phrase
        if (not any(c.islower() for c in stripped) and
                not NON_CHAR_PAT.match(stripped)):
            return 'character', stripped
        return 'dialogue', stripped  # wrapped dialogue line

    if x0 >= THRESH['parenthetical_left']:
        if stripped.startswith('(') and stripped.endswith(')'):
            return 'parenthetical', stripped
        return 'dialogue', stripped

    if x0 >= THRESH['dialogue_left']:
        return 'dialogue', stripped

    # Action / scene heading zone (x0 < 180pt)
    return 'action', stripped


def parse_pdf(file_path):
    elements = []
    page_headers = {}

    all_annotated = []
    title_page_elements = []  # raw title page lines, displayed but not parsed as script

    with pdfplumber.open(file_path) as pdf:
        for page_num, page in enumerate(pdf.pages, 1):
            words = page.extract_words(extra_attrs=["size"])
            if not words:
                continue

            # Page header zone: y < 50pt
            header_words = [w for w in words if float(w["top"]) < 50]
            if header_words:
                hl = " ".join(w["text"] for w in
                              sorted(header_words, key=lambda w: w["x0"]))
                # Fix double-rendered headers e.g. "BBlluuee RReevv.."
                if (len(hl) >= 8 and
                        all(hl[i] == hl[i+1]
                            for i in range(0, min(8, len(hl)-1), 2))):
                    hl = hl[::2]
                # Fix doubled page numbers e.g. "22.." → "2."
                hl = re.sub(r"^(\d)(\.)\s*$", r"\1\2", hl.strip())
                hl = re.sub(r"^(\d+)(\.+)\s*$",
                            lambda m: m.group(1)[:len(m.group(1))//2 or 1] + ".",
                            hl.strip()) if re.match(r"^\d+\.+$", hl.strip()) else hl
                page_headers[page_num] = hl

            # Content words
            content_words = [w for w in words if float(w["top"]) >= 50]

            # Group into lines by y (±3pt)
            lines_dict = {}
            for w in content_words:
                y_key = round(float(w["top"]) / 3) * 3
                lines_dict.setdefault(y_key, []).append(w)

            sorted_ys = sorted(lines_dict.keys())

            # Estimate normal line spacing
            gaps = [sorted_ys[i+1] - sorted_ys[i]
                    for i in range(len(sorted_ys)-1)]
            gap_counts = Counter(round(g/2)*2 for g in gaps if 8 < g < 30)
            normal_lh = gap_counts.most_common(1)[0][0] if gap_counts else 14
            para_threshold = normal_lh * 1.4

            # Build annotated line list: (text, x0, is_para_break)
            annotated = []
            for idx, y_key in enumerate(sorted_ys):
                lw = sorted(lines_dict[y_key], key=lambda w: w["x0"])
                text = normalise_unicode(
                    " ".join(w["text"] for w in lw))
                x0 = float(lw[0]["x0"])
                para_break = (idx > 0 and
                              (y_key - sorted_ys[idx-1]) > para_threshold)
                annotated.append((page_num, text, x0, para_break))

            # Capture title page (page 1) content directly as action elements
            # so it displays without being classified as script elements
            if page_num == 1:
                for pg, text, x0, pb in annotated:
                    stripped = text.strip()
                    if stripped and not PAGE_NUM_PAT.match(stripped) and not STRIP_PAT.match(stripped) and not DOUBLED_PAGE_PAT.match(stripped):
                        title_page_elements.append({
                            "type": "action",
                            "text": stripped,
                            "display_text": stripped,
                            "page": 1,
                        })
            else:
                all_annotated.extend(annotated)

    script_elements = _classify_annotated(all_annotated)
    # Prepend title page elements so pageMap includes page 1
    elements = title_page_elements + script_elements
    return elements, page_headers


def _classify_annotated(lines):
    """
    Two-pass PDF classification:
    Pass 1: classify each line individually
    Pass 2: group consecutive lines of the same paragraph
    """
    classified = []
    pending_char_id = None
    state = 'action'
    found_first_scene = False  # skip title page content

    for page_num, text, x0, para_break in lines:
        stripped = text.strip()

        # Skip page numbers and auto-continueds
        if not stripped:
            if state == 'action':
                pending_char_id = None
            continue
        if PAGE_NUM_PAT.match(stripped):
            continue
        if DOUBLED_PAGE_PAT and DOUBLED_PAGE_PAT.match(stripped):
            continue
        if STRIP_PAT.match(stripped):
            continue

        # Track first scene heading — skip title page content before it
        if not found_first_scene:
            if SCENE_PREFIXES.match(stripped) or SCENE_NUMBERED.match(stripped):
                found_first_scene = True
            else:
                continue  # skip title page

        etype, norm_text = classify_line(x0, stripped)
        if etype is None:
            continue

        if etype == 'scene_heading':
            pending_char_id = None
            state = 'action'
            classified.append({
                "type": "scene_heading",
                "text": norm_text,
                "x0": x0,
                "page": page_num,
                "para_break": para_break,
            })

        elif etype == 'transition':
            pending_char_id = None
            state = 'action'
            classified.append({
                "type": "transition",
                "text": norm_text,
                "x0": x0,
                "page": page_num,
                "para_break": para_break,
            })

        elif etype == 'character':
            char_id = normalise_character_id(norm_text)
            pending_char_id = char_id
            state = 'dialogue'
            classified.append({
                "type": "character",
                "text": char_id,
                "display_text": norm_text.upper(),
                "character": char_id,
                "x0": x0,
                "page": page_num,
                "para_break": para_break,
            })

        elif etype == 'parenthetical':
            classified.append({
                "type": "parenthetical",
                "text": norm_text,
                "character": pending_char_id,
                "x0": x0,
                "page": page_num,
                "para_break": para_break,
            })

        elif etype == 'dialogue':
            # Check x0 — if near action zone, it's inter-speech action
            if state == 'dialogue' and pending_char_id and x0 > THRESH['dialogue_left'] - 20:
                classified.append({
                    "type": "dialogue",
                    "text": norm_text,
                    "character": pending_char_id,
                    "x0": x0,
                    "page": page_num,
                    "para_break": para_break,
                })
            else:
                # Inter-speech action line
                state = 'action'
                pending_char_id = None
                classified.append({
                    "type": "action",
                    "text": norm_text,
                    "x0": x0,
                    "page": page_num,
                    "para_break": para_break,
                })

        else:  # action
            state = 'action'
            pending_char_id = None
            classified.append({
                "type": "action",
                "text": norm_text,
                "x0": x0,
                "page": page_num,
                "para_break": para_break,
            })

    # Pass 2: group consecutive lines into paragraphs
    elements = []
    i = 0
    while i < len(classified):
        el = classified[i]
        etype = el["type"]

        # Scene headings, characters, parentheticals, transitions → single elements
        if etype in ("scene_heading", "character", "parenthetical", "transition"):
            out = dict(el)
            out.setdefault("display_text", el["text"])
            elements.append(out)
            i += 1
            continue

        # Action and dialogue: group lines belonging to same paragraph
        j = i + 1
        parts = [el["text"]]
        while (j < len(classified) and
               classified[j]["type"] == etype and
               classified[j].get("character") == el.get("character") and
               not classified[j]["para_break"]):
            parts.append(classified[j]["text"])
            j += 1

        out = dict(el)
        out["text"] = " ".join(parts)
        out["display_text"] = " ".join(parts)
        elements.append(out)
        i = j

    return elements


# ---------------------------------------------------------------------------
# Auto-cast engine
# ---------------------------------------------------------------------------
GENDER_MALE   = {"he","him","his","man","boy","father","dad","brother","son",
                 "uncle","grandfather","husband","mr","sir","gentleman",
                 "male","guy","dude","lad"}
GENDER_FEMALE = {"she","her","woman","girl","mother","mom","mum","sister",
                 "daughter","aunt","grandmother","wife","mrs","ms","miss",
                 "lady","female","gal","lass"}
AGE_KEYWORDS  = {
    "child":   {"child","kid","young","teenager","teen","baby","infant"},
    "20s":     {"twenties","twenty","college"},
    "30s":     {"thirties","thirty","adult"},
    "40s":     {"forties","forty","middle-aged"},
    "50s":     {"fifties","fifty","mature"},
    "60s":     {"sixties","sixty","senior"},
    "elderly": {"elderly","old","aged","ancient","veteran","weathered"},
}
ACCENT_KEYWORDS = {
    "british":    {"british","english","london","cockney","scottish",
                   "irish","welsh","posh","oxford"},
    "american":   {"american","brooklyn","texan","southern",
                   "midwestern","california","boston"},
    "australian": {"australian","aussie"},
}
TRAIT_KEYWORDS = {
    "deep":   {"deep","bass","baritone","low","booming"},
    "high":   {"high","squeaky","shrill"},
    "raspy":  {"raspy","gruff","gravelly","hoarse"},
    "soft":   {"soft","gentle","quiet","whispery"},
    "warm":   {"warm","friendly","inviting"},
    "bright": {"bright","cheerful","energetic","bubbly"},
}

VOICE_LIBRARY = [
    {"id":"en-GB-RyanNeural","gender":"male","accent":"british","age":"30s","traits":["warm","smooth"]},
    {"id":"en-GB-SoniaNeural","gender":"female","accent":"british","age":"30s","traits":["warm","clear"]},
    {"id":"en-GB-LibbyNeural","gender":"female","accent":"british","age":"20s","traits":["bright","soft"]},
    {"id":"en-GB-MaisieNeural","gender":"female","accent":"british","age":"child","traits":["bright"]},
    {"id":"en-GB-OliverNeural","gender":"male","accent":"british","age":"20s","traits":["warm","friendly"]},
    {"id":"en-GB-ThomasNeural","gender":"male","accent":"british","age":"40s","traits":["deep","authoritative"]},
    {"id":"en-US-GuyNeural","gender":"male","accent":"american","age":"30s","traits":["deep","authoritative"]},
    {"id":"en-US-JennyNeural","gender":"female","accent":"american","age":"30s","traits":["warm","clear"]},
    {"id":"en-US-AriaNeural","gender":"female","accent":"american","age":"30s","traits":["expressive","bright"]},
    {"id":"en-US-DavisNeural","gender":"male","accent":"american","age":"30s","traits":["deep","smooth"]},
    {"id":"en-US-TonyNeural","gender":"male","accent":"american","age":"40s","traits":["deep","raspy"]},
    {"id":"en-US-NancyNeural","gender":"female","accent":"american","age":"40s","traits":["warm","authoritative"]},
    {"id":"en-AU-NatashaNeural","gender":"female","accent":"australian","age":"30s","traits":["bright","clear"]},
    {"id":"en-AU-WilliamNeural","gender":"male","accent":"australian","age":"30s","traits":["warm","deep"]},
    {"id":"en-US-AnaNeural","gender":"female","accent":"american","age":"child","traits":["bright"]},
    {"id":"en-US-BrandonNeural","gender":"male","accent":"american","age":"20s","traits":["bright","warm"]},
    {"id":"en-US-ChristopherNeural","gender":"male","accent":"american","age":"40s","traits":["deep","authoritative"]},
    {"id":"en-US-ElizabethNeural","gender":"female","accent":"american","age":"50s","traits":["warm","mature"]},
    {"id":"en-IE-ConnorNeural","gender":"male","accent":"british","age":"30s","traits":["warm","friendly"]},
    {"id":"en-IE-EmilyNeural","gender":"female","accent":"british","age":"20s","traits":["soft","warm"]},
]

def scrape_character_profile(char_id, elements):
    first_idx = next((i for i, e in enumerate(elements)
                      if e.get("character") == char_id), None)
    if first_idx is None:
        return {}
    words = set()
    for el in elements[max(0,first_idx-5):min(len(elements),first_idx+10)]:
        if el["type"] == "action":
            tl = el["text"].lower()
            # char_id may contain underscores — check both forms
            name_variants = [char_id.lower(), char_id.lower().replace("_"," ")]
            for variant in name_variants:
                if variant in tl:
                    idx = tl.index(variant)
                    words.update(tl[max(0,idx-50):idx+80].split())
    pw = set(); pc = 0
    for el in elements:
        if el.get("character") == char_id and el["type"] == "parenthetical" and pc < 3:
            pw.update(el["text"].lower().split()); pc += 1
    all_w = words | pw
    ms = sum(1 for w in all_w if w in GENDER_MALE)
    fs = sum(1 for w in all_w if w in GENDER_FEMALE)
    gender = "male" if ms > fs else ("female" if fs > ms else None)
    age    = next((ag for ag, kws in AGE_KEYWORDS.items()
                   if any(w in all_w for w in kws)), None)
    accent = next((ac for ac, kws in ACCENT_KEYWORDS.items()
                   if any(w in all_w for w in kws)), None)
    traits = [t for t, kws in TRAIT_KEYWORDS.items()
              if any(w in all_w for w in kws)]
    return {"gender": gender, "age": age, "accent": accent, "traits": traits}

def score_voice(v, p):
    s = 0
    if p.get("gender") and v["gender"] == p["gender"]: s += 10
    if p.get("age")    and v["age"]    == p["age"]:    s += 5
    if p.get("accent") and v["accent"] == p["accent"]: s += 5
    elif not p.get("accent") and v["accent"] == "british": s += 3
    for t in p.get("traits", []):
        if t in v["traits"]: s += 3
    return s

def auto_cast(characters, elements):
    counts = {}
    for el in elements:
        if el.get("character"):
            counts[el["character"]] = counts.get(el["character"], 0) + 1
    used = set(); casting = {}
    for char in sorted(characters, key=lambda c: counts.get(c, 0), reverse=True):
        profile   = scrape_character_profile(char, elements)
        available = [v for v in VOICE_LIBRARY if v["id"] not in used] or VOICE_LIBRARY
        best      = max(available, key=lambda v: score_voice(v, profile))
        casting[char] = {
            "voice_id": best["id"], "gender": best["gender"],
            "accent": best["accent"], "age": best["age"], "profile": profile
        }
        used.add(best["id"])
    return casting


# ---------------------------------------------------------------------------
# Sentiment detection → TTS parameters
# ---------------------------------------------------------------------------
SENTIMENT_PARAMS = {
    "whisper": {"rate":"-20%","volume":"-30%","pitch":"-5Hz"},
    "shout":   {"rate":"+10%","volume":"+20%","pitch":"+10Hz"},
    "angry":   {"rate":"+10%","volume":"+10%","pitch":"+5Hz"},
    "sad":     {"rate":"-10%","volume":"-10%","pitch":"-10Hz"},
    "excited": {"rate":"+15%","volume":"+10%","pitch":"+8Hz"},
    "scared":  {"rate":"+10%","volume":"-5%", "pitch":"+5Hz"},
    "calm":    {"rate":"-5%", "volume":"0%",  "pitch":"-5Hz"},
}
SENTIMENT_KEYWORDS = {
    "whisper": {"whisper","sotto voce","quietly","hushed"},
    "shout":   {"shout","yell","scream","bellowing"},
    "angry":   {"angry","furious","rage","irate","livid"},
    "sad":     {"sad","crying","sobbing","weeping","tearful"},
    "excited": {"excited","enthusiasm","eager","thrilled"},
    "scared":  {"scared","frightened","terrified","trembling"},
    "calm":    {"calm","soothing","gentle","peaceful"},
}

def detect_sentiment(text):
    words = set(text.lower().split())
    for s, kws in SENTIMENT_KEYWORDS.items():
        if words & kws:
            return SENTIMENT_PARAMS[s]
    return {}


# ---------------------------------------------------------------------------
# Audio cache (SHA256 keyed MP3 files)
# ---------------------------------------------------------------------------
def cache_key(text, voice_id):
    return hashlib.sha256(f"{text}|{voice_id}|edge-tts".encode()).hexdigest()

def get_cached(text, voice_id):
    p = CACHE_DIR / f"{cache_key(text, voice_id)}.mp3"
    return p.read_bytes() if p.exists() else None

def save_cache(text, voice_id, audio_bytes):
    (CACHE_DIR / f"{cache_key(text, voice_id)}.mp3").write_bytes(audio_bytes)

async def _synth_async(text, voice_id, rate, volume, pitch):
    comm = edge_tts.Communicate(text, voice_id,
                                 rate=rate, volume=volume, pitch=pitch)
    chunks = []
    async for chunk in comm.stream():
        if chunk["type"] == "audio":
            chunks.append(chunk["data"])
    return b"".join(chunks)

def synthesise(text, voice_id, sentiment_params=None):
    cached = get_cached(text, voice_id)
    if cached:
        return cached
    p = sentiment_params or {}
    loop = asyncio.new_event_loop()
    try:
        audio = loop.run_until_complete(_synth_async(
            expand_abbrevs(text), voice_id,
            p.get("rate","+0%"), p.get("volume","+0%"), p.get("pitch","+0Hz")))
    finally:
        loop.close()
    save_cache(text, voice_id, audio)
    return audio


# ---------------------------------------------------------------------------
# Flask routes
# ---------------------------------------------------------------------------
@app.route("/health")
def health():
    return jsonify({"status": "ok"})

@app.route("/")
def index():
    return render_template("index.html")

@app.route("/upload", methods=["POST"])
def upload():
    if "file" not in request.files:
        return jsonify({"error": "No file uploaded"}), 400
    f   = request.files["file"]
    ext = (f.filename or "").rsplit(".", 1)[-1].lower()
    tmp = f"/tmp/scriptcast_upload.{ext}"
    f.save(tmp)
    try:
        if ext == "pdf":
            elements, page_headers = parse_pdf(tmp)
        elif ext == "fdx":
            elements, page_headers = parse_fdx(tmp)
        else:
            return jsonify({"error": "Unsupported file type. Use .pdf or .fdx"}), 400
    except Exception as e:
        return jsonify({"error": f"Parse error: {str(e)}"}), 500

    characters = list({e["character"] for e in elements if e.get("character")})
    casting    = auto_cast(characters, elements)
    page_map   = {}
    for i, el in enumerate(elements):
        page_map.setdefault(str(el.get("page", 1)), []).append(i)

    return jsonify({
        "elements":     elements,
        "casting":      casting,
        "page_map":     page_map,
        "page_headers": page_headers,
        "characters":   characters,
    })

@app.route("/tts", methods=["POST"])
def tts():
    data     = request.get_json()
    text     = data.get("text", "").strip()
    voice    = data.get("voice_id", "en-GB-RyanNeural")
    paren    = data.get("parenthetical", "")
    el_type  = data.get("element_type", "")
    if not text:
        return jsonify({"error": "No text provided"}), 400
    # Format text for natural narration based on element type
    if el_type == "scene_heading":
        tts_text = format_scene_heading_tts(text)
    elif el_type == "parenthetical":
        # Strip brackets: "(Mumbles, slow)" → "Mumbles, slow"
        tts_text = re.sub(r"^\s*\(|\)\s*$", "", text).strip()
    elif el_type == "transition":
        # Natural reading: "CUT TO:" → "Cut to."
        tts_text = text.rstrip(":").replace(".", "").title() + "."
    else:
        tts_text = text
    try:
        audio = synthesise(tts_text, voice, detect_sentiment(paren) if paren else {})
    except Exception as e:
        return jsonify({"error": f"TTS error: {str(e)}"}), 500
    import base64
    return jsonify({"audio": base64.b64encode(audio).decode(), "format": "mp3"})

@app.route("/voices", methods=["GET"])
def voices():
    return jsonify({"voices": VOICE_LIBRARY})

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8080))
    app.run(host="0.0.0.0", port=port, debug=False)
