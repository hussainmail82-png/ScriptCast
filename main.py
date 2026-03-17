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

UNICODE_MAP = {
    "\u2018": "'", "\u2019": "'",
    "\u201c": '"', "\u201d": '"',
    "\u2026": "...", "\u2013": "-", "\u2014": "--",
}

def normalise(text):
    for src, dst in UNICODE_MAP.items():
        text = text.replace(src, dst)
    return text

ABBREV = {
    r"\bMR\.": "Mister", r"\bMRS\.": "Missus", r"\bDR\.": "Doctor",
    r"\bINT\.": "Interior", r"\bEXT\.": "Exterior",
    r"\bV\.O\.": "Voice Over", r"\bO\.S\.": "Off Screen",
    r"\bO\.C\.": "Off Camera", r"\bSGT\.": "Sergeant",
    r"\bCONT'D\b": "Continued",
    r"\.\.\.": " (pause) ", r"--": " (pause) ",
}

def expand_abbrevs(text):
    for pattern, replacement in ABBREV.items():
        text = re.sub(pattern, replacement, text, flags=re.IGNORECASE)
    return text

SCENE_HEADING = re.compile(
    r"^\s*(?:(\d+[A-Z]?)\s+)?(?:[A-Z]+\.\s*)?(INT\.?|EXT\.?|INT\.?/EXT\.?|I/E\.?|EST\.?)\s*-?\s*(.+?)(?:\s+(\d+[A-Z]?))?\s*$",
    re.IGNORECASE
)
SCENE_HEADING_NUMBERED = re.compile(
    r"^\s*(\d+[A-Z]?)\s+(.+?)\s*-\s*(DAY|NIGHT|MORNING|EVENING|DAWN|DUSK|CONTINUOUS|LATER|MOMENTS LATER|SAME TIME|SAME)\s*(\d+[A-Z]?)?\s*$",
    re.IGNORECASE
)
TRANSITION_PAT    = re.compile(r"^\s*([A-Z ]+TO:|FADE (?:IN|OUT)\.|FADE TO BLACK\.|SMASH CUT TO:|DISSOLVE TO:|CUT TO:)\s*$")
CHARACTER_CUE     = re.compile(r"^\s*([A-Z0-9][A-Z0-9 .\'\-]*)\s*(?:\(([^)]+)\))?\s*$")
PARENTHETICAL_PAT = re.compile(r"^\s*\((.+)\)\s*$")
PAGE_NUMBER_PAT   = re.compile(r"^\d+\.?$")
CONTINUED_PAT     = re.compile(r"^\s*\(?(?:CONTINUED|CONT'D)\)?:?\s*$", re.IGNORECASE)
PAGE_HEADER_PAT   = re.compile(r"^\s*\d+\s*(?:CONTINUED|CONT'D)", re.IGNORECASE)
REVISION_HEADER   = re.compile(r"(?:Blue|Pink|Yellow|Green|Goldenrod|Buff|Salmon|Cherry|White)\s+Rev\.", re.IGNORECASE)
NON_CHARACTER_PAT = re.compile(
    r"^\s*(?:WRITTEN BY|DIRECTED BY|PRODUCED BY|FADE IN\.?|FADE OUT\.?|THE END|TITLE CARD|SUPER|SMASH CUT|CUT TO|DISSOLVE TO|BLACK)\s*$",
    re.IGNORECASE
)
CHAR_EXTENSION = re.compile(r"\s*\([^)]*\)\s*")

def strip_extension(name):
    return CHAR_EXTENSION.sub("", name).strip()

def is_skip_line(s):
    return bool(PAGE_NUMBER_PAT.match(s) or CONTINUED_PAT.match(s) or
                PAGE_HEADER_PAT.match(s) or REVISION_HEADER.search(s))

# ---------------------------------------------------------------------------
# PDF Parser — line-by-line with paragraph grouping for display only
# ---------------------------------------------------------------------------
def parse_pdf(file_path):
    elements = []
    page_headers = {}

    with pdfplumber.open(file_path) as pdf:
        for page_num, page in enumerate(pdf.pages, 1):
            words = page.extract_words(extra_attrs=["fontname", "size"])
            if not words:
                continue

            # Page header zone (y < 50)
            header_words = [w for w in words if float(w["top"]) < 50]
            if header_words:
                hl = " ".join(w["text"] for w in sorted(header_words, key=lambda w: w["x0"]))
                if len(hl) >= 8 and all(hl[i] == hl[i+1] for i in range(0, min(8, len(hl)-1), 2)):
                    hl = hl[::2]
                page_headers[page_num] = hl

            # Group words into lines by y-coordinate (±3pt tolerance)
            content_words = [w for w in words if float(w["top"]) >= 50]
            lines_dict = {}
            for w in content_words:
                y_key = round(float(w["top"]) / 3) * 3
                lines_dict.setdefault(y_key, []).append(w)

            sorted_ykeys = sorted(lines_dict.keys())

            # Estimate normal line height from most common gap
            gaps = [sorted_ykeys[i+1] - sorted_ykeys[i] for i in range(len(sorted_ykeys)-1)]
            gap_counts = Counter(round(g/2)*2 for g in gaps if 8 < g < 30)
            normal_lh = gap_counts.most_common(1)[0][0] if gap_counts else 14
            para_threshold = normal_lh * 1.35

            # Build list of (page, text, x0, is_para_break_before)
            annotated = []
            for idx, y_key in enumerate(sorted_ykeys):
                line_words = sorted(lines_dict[y_key], key=lambda w: w["x0"])
                text = normalise(" ".join(w["text"] for w in line_words))
                x0 = float(line_words[0]["x0"])
                para_break = (idx > 0 and (y_key - sorted_ykeys[idx-1]) > para_threshold)
                annotated.append((page_num, text, x0, para_break))

            elements.extend(parse_annotated_lines(annotated))

    return elements, page_headers


def parse_annotated_lines(lines):
    """
    Parse lines with paragraph-break hints.
    Key insight: classify line-by-line (for character detection etc.)
    but group consecutive lines of the SAME paragraph into one element
    for display so text reflows correctly.
    """
    elements = []
    state = "action"
    pending_char = None

    # First pass: classify each line
    classified = []
    i = 0
    while i < len(lines):
        page_num, text, x0, para_break = lines[i]
        stripped = text.strip()

        if is_skip_line(stripped):
            i += 1
            continue

        if not stripped:
            if state == "action":
                pending_char = None
            i += 1
            continue

        # Scene heading
        if SCENE_HEADING.match(stripped) or SCENE_HEADING_NUMBERED.match(stripped):
            classified.append({"type": "scene_heading", "text": stripped.upper(),
                               "page": page_num, "para_break": para_break})
            state = "action"; pending_char = None; i += 1; continue

        # Transition
        if TRANSITION_PAT.match(stripped):
            classified.append({"type": "transition", "text": stripped,
                               "page": page_num, "para_break": para_break})
            state = "action"; pending_char = None; i += 1; continue

        # Character cue — must be ALL CAPS single line, not a non-character
        has_lower = any(c.islower() for c in stripped)
        if (CHARACTER_CUE.match(stripped) and not has_lower and
                not NON_CHARACTER_PAT.match(stripped)):
            # Peek ahead: next non-blank must be dialogue/paren
            next_text = next((lines[j][1].strip() for j in range(i+1, min(i+5, len(lines)))
                             if lines[j][1].strip()), "")
            if (next_text and not SCENE_HEADING.match(next_text) and
                    not TRANSITION_PAT.match(next_text) and
                    not (CHARACTER_CUE.match(next_text) and not any(c.islower() for c in next_text))):
                char_name = strip_extension(stripped)
                if char_name:
                    pending_char = char_name; state = "dialogue"
                    classified.append({"type": "character", "text": char_name,
                                       "display_text": stripped, "character": char_name,
                                       "page": page_num, "para_break": para_break})
                    i += 1; continue

        # Parenthetical
        if state == "dialogue" and PARENTHETICAL_PAT.match(stripped):
            classified.append({"type": "parenthetical", "text": stripped,
                               "character": pending_char, "page": page_num, "para_break": para_break})
            i += 1; continue

        # Dialogue vs action-between-speeches:
        # Dialogue is indented (x0 > action_threshold).
        # Action lines between speeches have x0 near left margin.
        # We use x0 > 100 as the threshold (dialogue is typically indented ~150pt+)
        if state == "dialogue" and pending_char and x0 > 150:
            classified.append({"type": "dialogue", "text": stripped,
                               "character": pending_char, "page": page_num, "para_break": para_break})
            i += 1; continue

        # Action (including action lines between dialogue speeches)
        classified.append({"type": "action", "text": stripped,
                           "page": page_num, "para_break": para_break})
        # Don't reset pending_char for action between speeches — next speech still belongs to same char
        # Only reset if there's a scene heading or explicit break
        state = "action"; i += 1

    # Second pass: group consecutive same-type/same-character lines into paragraphs
    # Lines with para_break=True start a new element even if same type
    i = 0
    while i < len(classified):
        el = classified[i]
        etype = el["type"]

        # Character cues and scene headings are always single elements
        if etype in ("character", "scene_heading", "transition", "parenthetical"):
            out = dict(el)
            out.setdefault("display_text", el["text"])
            elements.append(out)
            i += 1
            continue

        # Action and dialogue: group lines that belong to the same paragraph
        j = i + 1
        group_texts = [el["text"]]
        while (j < len(classified) and
               classified[j]["type"] == etype and
               classified[j].get("character") == el.get("character") and
               not classified[j]["para_break"]):
            group_texts.append(classified[j]["text"])
            j += 1

        out = dict(el)
        out["text"] = " ".join(group_texts)
        out["display_text"] = " ".join(group_texts)  # reflow — no \n
        elements.append(out)
        i = j

    return elements


# ---------------------------------------------------------------------------
# FDX Parser
# ---------------------------------------------------------------------------
def parse_fdx(file_path):
    tree = ET.parse(file_path)
    root = tree.getroot()
    elements = []
    pending_char = None
    for para in root.iter("Paragraph"):
        ptype = para.get("Type", "Action")
        text = normalise("".join(t.text or "" for t in para.iter("Text")).strip())
        if not text:
            continue
        if ptype == "Scene Heading":
            elements.append({"type": "scene_heading", "text": text.upper(),
                             "display_text": text.upper(), "page": 1})
            pending_char = None
        elif ptype == "Transition":
            elements.append({"type": "transition", "text": text, "display_text": text, "page": 1})
            pending_char = None
        elif ptype == "Character":
            char_name = strip_extension(text); pending_char = char_name
            elements.append({"type": "character", "text": char_name, "display_text": text,
                             "character": char_name, "page": 1})
        elif ptype == "Parenthetical":
            elements.append({"type": "parenthetical", "text": text, "display_text": text,
                             "character": pending_char, "page": 1})
        elif ptype == "Dialogue":
            elements.append({"type": "dialogue", "text": text, "display_text": text,
                             "character": pending_char, "page": 1})
        else:
            elements.append({"type": "action", "text": text, "display_text": text, "page": 1})
            pending_char = None
    return elements, {}


# ---------------------------------------------------------------------------
# Auto-cast
# ---------------------------------------------------------------------------
GENDER_MALE   = {"he","him","his","man","boy","father","dad","brother","son","uncle","grandfather","husband","mr","sir","gentleman","male","guy","dude","lad"}
GENDER_FEMALE = {"she","her","woman","girl","mother","mom","mum","sister","daughter","aunt","grandmother","wife","mrs","ms","miss","lady","female","gal","lass"}
AGE_KEYWORDS  = {
    "child":{"child","kid","young","teenager","teen","baby","infant","toddler"},
    "20s":{"twenties","twenty","college"},"30s":{"thirties","thirty","adult"},
    "40s":{"forties","forty","middle-aged"},"50s":{"fifties","fifty","mature"},
    "60s":{"sixties","sixty","senior"},"elderly":{"elderly","old","aged","ancient","veteran"},
}
ACCENT_KEYWORDS = {
    "british":{"british","english","london","cockney","scottish","irish","welsh","posh"},
    "american":{"american","brooklyn","texan","southern","midwestern","california"},
    "australian":{"australian","aussie"},
}
TRAIT_KEYWORDS = {
    "deep":{"deep","bass","baritone","low","booming"},"high":{"high","squeaky","shrill"},
    "raspy":{"raspy","gruff","gravelly","hoarse"},"soft":{"soft","gentle","quiet","whispery"},
    "warm":{"warm","friendly","inviting"},"bright":{"bright","cheerful","energetic","bubbly"},
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

def scrape_character_profile(char_name, elements):
    first_idx = next((i for i, e in enumerate(elements) if e.get("character") == char_name), None)
    if first_idx is None: return {}
    words = set()
    for el in elements[max(0,first_idx-5):min(len(elements),first_idx+10)]:
        if el["type"] == "action":
            tl = el["text"].lower()
            if char_name.lower() in tl:
                idx = tl.index(char_name.lower())
                words.update(tl[max(0,idx-50):idx+80].split())
    pw = set(); pc = 0
    for el in elements:
        if el.get("character") == char_name and el["type"] == "parenthetical" and pc < 3:
            pw.update(el["text"].lower().split()); pc += 1
    all_w = words | pw
    ms = sum(1 for w in all_w if w in GENDER_MALE)
    fs = sum(1 for w in all_w if w in GENDER_FEMALE)
    gender = "male" if ms > fs else ("female" if fs > ms else None)
    age    = next((ag for ag, kws in AGE_KEYWORDS.items() if any(w in all_w for w in kws)), None)
    accent = next((ac for ac, kws in ACCENT_KEYWORDS.items() if any(w in all_w for w in kws)), None)
    traits = [t for t, kws in TRAIT_KEYWORDS.items() if any(w in all_w for w in kws)]
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
        if el.get("character"): counts[el["character"]] = counts.get(el["character"],0)+1
    used = set(); casting = {}
    for char in sorted(characters, key=lambda c: counts.get(c,0), reverse=True):
        profile   = scrape_character_profile(char, elements)
        available = [v for v in VOICE_LIBRARY if v["id"] not in used] or VOICE_LIBRARY
        best      = max(available, key=lambda v: score_voice(v, profile))
        casting[char] = {"voice_id": best["id"], "gender": best["gender"],
                         "accent": best["accent"], "age": best["age"], "profile": profile}
        used.add(best["id"])
    return casting


# ---------------------------------------------------------------------------
# Sentiment / TTS
# ---------------------------------------------------------------------------
SENTIMENT_PARAMS = {
    "whisper":{"rate":"-20%","volume":"-30%","pitch":"-5Hz"},
    "shout":  {"rate":"+10%","volume":"+20%","pitch":"+10Hz"},
    "angry":  {"rate":"+10%","volume":"+10%","pitch":"+5Hz"},
    "sad":    {"rate":"-10%","volume":"-10%","pitch":"-10Hz"},
    "excited":{"rate":"+15%","volume":"+10%","pitch":"+8Hz"},
    "scared": {"rate":"+10%","volume":"-5%", "pitch":"+5Hz"},
    "calm":   {"rate":"-5%", "volume":"0%",  "pitch":"-5Hz"},
}
SENTIMENT_KEYWORDS = {
    "whisper":{"whisper","sotto voce","quietly","hushed"},
    "shout":  {"shout","yell","scream","bellowing"},
    "angry":  {"angry","furious","rage","irate","livid"},
    "sad":    {"sad","crying","sobbing","weeping","tearful"},
    "excited":{"excited","enthusiasm","eager","thrilled"},
    "scared": {"scared","frightened","terrified","trembling"},
    "calm":   {"calm","soothing","gentle","peaceful"},
}

def detect_sentiment(text):
    words = set(text.lower().split())
    for s, kws in SENTIMENT_KEYWORDS.items():
        if words & kws: return SENTIMENT_PARAMS[s]
    return {}

def cache_key(text, voice_id):
    return hashlib.sha256(f"{text}|{voice_id}|edge-tts".encode()).hexdigest()

def get_cached(text, voice_id):
    p = CACHE_DIR / f"{cache_key(text, voice_id)}.mp3"
    return p.read_bytes() if p.exists() else None

def save_cache(text, voice_id, audio_bytes):
    (CACHE_DIR / f"{cache_key(text, voice_id)}.mp3").write_bytes(audio_bytes)

async def synthesise_async(text, voice_id, rate, volume, pitch):
    communicate = edge_tts.Communicate(text, voice_id, rate=rate, volume=volume, pitch=pitch)
    chunks = []
    async for chunk in communicate.stream():
        if chunk["type"] == "audio": chunks.append(chunk["data"])
    return b"".join(chunks)

def synthesise(text, voice_id, sentiment_params=None):
    cached = get_cached(text, voice_id)
    if cached: return cached
    p = sentiment_params or {}
    loop = asyncio.new_event_loop()
    try:
        audio = loop.run_until_complete(synthesise_async(
            expand_abbrevs(text), voice_id,
            p.get("rate","+0%"), p.get("volume","+0%"), p.get("pitch","+0Hz")))
    finally:
        loop.close()
    save_cache(text, voice_id, audio)
    return audio


# ---------------------------------------------------------------------------
# Routes
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
        if ext == "pdf":   elements, page_headers = parse_pdf(tmp)
        elif ext == "fdx": elements, page_headers = parse_fdx(tmp)
        else: return jsonify({"error": "Unsupported file type. Use .pdf or .fdx"}), 400
    except Exception as e:
        return jsonify({"error": f"Parse error: {str(e)}"}), 500

    characters = list({e["character"] for e in elements if e.get("character")})
    casting    = auto_cast(characters, elements)
    page_map   = {}
    for i, el in enumerate(elements):
        page_map.setdefault(str(el.get("page", 1)), []).append(i)

    return jsonify({"elements": elements, "casting": casting,
                    "page_map": page_map, "page_headers": page_headers,
                    "characters": characters})

@app.route("/tts", methods=["POST"])
def tts():
    data  = request.get_json()
    text  = data.get("text", "").strip()
    voice = data.get("voice_id", "en-GB-RyanNeural")
    paren = data.get("parenthetical", "")
    if not text: return jsonify({"error": "No text provided"}), 400
    try:
        audio = synthesise(text, voice, detect_sentiment(paren) if paren else {})
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
