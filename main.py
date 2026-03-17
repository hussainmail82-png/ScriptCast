import os
import re
import json
import hashlib
import asyncio
import unicodedata
from pathlib import Path
from flask import Flask, request, jsonify, render_template, send_from_directory

import pdfplumber
import xml.etree.ElementTree as ET
import edge_tts

app = Flask(__name__)
CACHE_DIR = Path("./audio_cache")
CACHE_DIR.mkdir(exist_ok=True)

# ---------------------------------------------------------------------------
# Unicode normalisation
# ---------------------------------------------------------------------------
UNICODE_MAP = {
    "\u2018": "'", "\u2019": "'",
    "\u201c": '"', "\u201d": '"',
    "\u2026": "...", "\u2013": "-", "\u2014": "--",
}

def normalise(text):
    for src, dst in UNICODE_MAP.items():
        text = text.replace(src, dst)
    return text

# ---------------------------------------------------------------------------
# Abbreviation expansion for TTS
# ---------------------------------------------------------------------------
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

# ---------------------------------------------------------------------------
# Compiled regex patterns
# ---------------------------------------------------------------------------
SCENE_HEADING = re.compile(
    r"^\s*(?:(\d+[A-Z]?)\s+)?(?:[A-Z]+\.\s*)?(INT\.?|EXT\.?|INT\.?/EXT\.?|I/E\.?|EST\.?)\s*-?\s*(.+?)(?:\s+(\d+[A-Z]?))?\s*$",
    re.IGNORECASE
)
SCENE_HEADING_NUMBERED = re.compile(
    r"^\s*(\d+[A-Z]?)\s+(.+?)\s*-\s*(DAY|NIGHT|MORNING|EVENING|DAWN|DUSK|CONTINUOUS|LATER|MOMENTS LATER|SAME TIME|SAME)\s*(\d+[A-Z]?)?\s*$",
    re.IGNORECASE
)
TRANSITION_PAT = re.compile(
    r"^\s*([A-Z ]+TO:|FADE (?:IN|OUT)\.|FADE TO BLACK\.|SMASH CUT TO:|DISSOLVE TO:|CUT TO:)\s*$"
)
CHARACTER_CUE = re.compile(
    r"^\s*([A-Z0-9][A-Z0-9 .\'\-]*)\s*(?:\(([^)]+)\))?\s*$"
)
PARENTHETICAL_PAT = re.compile(r"^\s*\((.+)\)\s*$")
PAGE_NUMBER_PAT = re.compile(r"^\d+\.?$")
CONTINUED_PAT = re.compile(r"^\s*\(?(CONTINUED|CONT'D)\)?:?\s*$", re.IGNORECASE)
PAGE_HEADER_PAT = re.compile(r"^\s*\d+\s*(CONTINUED|CONT'D)", re.IGNORECASE)
REVISION_HEADER = re.compile(
    r"(Blue|Pink|Yellow|Green|Goldenrod|Buff|Salmon|Cherry|White)\s+Rev\.", re.IGNORECASE
)
CHAR_EXTENSION = re.compile(r"\s*\([^)]*\)\s*")

def strip_extension(name):
    return CHAR_EXTENSION.sub("", name).strip()

def is_skip_line(line):
    s = line.strip()
    return bool(
        PAGE_NUMBER_PAT.match(s) or
        CONTINUED_PAT.match(s) or
        PAGE_HEADER_PAT.match(s) or
        REVISION_HEADER.search(s)
    )

# ---------------------------------------------------------------------------
# PDF Parser
# ---------------------------------------------------------------------------
def parse_pdf(file_path):
    elements = []
    page_headers = {}

    with pdfplumber.open(file_path) as pdf:
        for page_num, page in enumerate(pdf.pages, 1):
            words = page.extract_words(extra_attrs=["fontname", "size"])
            if not words:
                continue

            # Extract header (y < 50)
            header_words = [w for w in words if float(w["top"]) < 50]
            if header_words:
                header_line = " ".join(w["text"] for w in sorted(header_words, key=lambda w: w["x0"]))
                # Fix double-character rendering (e.g. "BBlluuee RReevv")
                if len(header_line) >= 8 and all(
                    header_line[i] == header_line[i+1] for i in range(0, min(8, len(header_line)-1), 2)
                ):
                    header_line = header_line[::2]
                page_headers[page_num] = header_line

            # Group words into lines by y-coordinate (tolerance ±3pt)
            content_words = [w for w in words if float(w["top"]) >= 50]
            lines_dict = {}
            for w in content_words:
                y_key = round(float(w["top"]) / 3) * 3
                lines_dict.setdefault(y_key, []).append(w)

            page_lines = []
            for y_key in sorted(lines_dict.keys()):
                line_words = sorted(lines_dict[y_key], key=lambda w: w["x0"])
                text = normalise(" ".join(w["text"] for w in line_words))
                page_lines.append((page_num, text))

            elements.extend(parse_lines(page_lines))

    return merge_elements(elements), page_headers

def parse_lines(page_lines):
    elements = []
    state = "action"
    pending_char = None

    i = 0
    while i < len(page_lines):
        page_num, line = page_lines[i]
        stripped = line.strip()

        if not stripped or is_skip_line(stripped):
            i += 1
            continue

        # 1. Scene heading
        if SCENE_HEADING.match(stripped) or SCENE_HEADING_NUMBERED.match(stripped):
            elements.append({
                "type": "scene_heading",
                "text": stripped.upper(),
                "display_text": stripped.upper(),
                "page": page_num
            })
            state = "action"
            pending_char = None
            i += 1
            continue

        # 2. Transition
        if TRANSITION_PAT.match(stripped):
            elements.append({
                "type": "transition",
                "text": stripped,
                "display_text": stripped,
                "page": page_num
            })
            state = "action"
            pending_char = None
            i += 1
            continue

        # 3. Character cue — ALL CAPS, no lowercase
        if (CHARACTER_CUE.match(stripped) and
                not any(c.islower() for c in stripped) and
                stripped.upper() == stripped.upper()):
            # Adjacency test: next non-blank line must be dialogue/parenthetical
            next_content = next(
                (page_lines[j][1].strip() for j in range(i+1, min(i+4, len(page_lines)))
                 if page_lines[j][1].strip()), ""
            )
            if next_content and not SCENE_HEADING.match(next_content) and not TRANSITION_PAT.match(next_content):
                char_name = strip_extension(stripped)
                if char_name:
                    pending_char = char_name
                    state = "dialogue"
                    elements.append({
                        "type": "character",
                        "text": char_name,
                        "display_text": stripped,
                        "character": char_name,
                        "page": page_num
                    })
                    i += 1
                    continue

        # 4. Parenthetical
        if state == "dialogue" and PARENTHETICAL_PAT.match(stripped):
            elements.append({
                "type": "parenthetical",
                "text": stripped,
                "display_text": stripped,
                "character": pending_char,
                "page": page_num
            })
            i += 1
            continue

        # 5. Dialogue
        if state == "dialogue" and pending_char:
            elements.append({
                "type": "dialogue",
                "text": stripped,
                "display_text": stripped,
                "character": pending_char,
                "page": page_num
            })
            i += 1
            continue

        # 6. Action (default)
        elements.append({
            "type": "action",
            "text": stripped,
            "display_text": stripped,
            "page": page_num
        })
        state = "action"
        pending_char = None
        i += 1

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
            elements.append({"type": "scene_heading", "text": text.upper(), "display_text": text.upper(), "page": 1})
            pending_char = None

        elif ptype == "Transition":
            elements.append({"type": "transition", "text": text, "display_text": text, "page": 1})
            pending_char = None

        elif ptype == "Character":
            char_name = strip_extension(text)
            pending_char = char_name
            elements.append({"type": "character", "text": char_name, "display_text": text, "character": char_name, "page": 1})

        elif ptype == "Parenthetical":
            elements.append({"type": "parenthetical", "text": text, "display_text": text, "character": pending_char, "page": 1})

        elif ptype == "Dialogue":
            elements.append({"type": "dialogue", "text": text, "display_text": text, "character": pending_char, "page": 1})

        else:
            elements.append({"type": "action", "text": text, "display_text": text, "page": 1})
            pending_char = None

    return merge_elements(elements), {}

# ---------------------------------------------------------------------------
# Element merging
# ---------------------------------------------------------------------------
def merge_elements(elements):
    if not elements:
        return []
    merged = []
    i = 0
    while i < len(elements):
        el = elements[i]
        if el["type"] in ("dialogue", "action"):
            j = i + 1
            texts, displays = [el["text"]], [el["display_text"]]
            while j < len(elements) and elements[j]["type"] == el["type"] and elements[j].get("character") == el.get("character"):
                texts.append(elements[j]["text"])
                displays.append(elements[j]["display_text"])
                j += 1
            merged_el = dict(el)
            merged_el["text"] = " ".join(texts)
            merged_el["display_text"] = "\n".join(displays)
            merged.append(merged_el)
            i = j
        else:
            merged.append(el)
            i += 1
    return merged

# ---------------------------------------------------------------------------
# Auto-cast engine
# ---------------------------------------------------------------------------
GENDER_MALE = {"he","him","his","man","boy","father","dad","brother","son","uncle","grandfather","husband","mr","sir","gentleman","male","guy","dude","lad"}
GENDER_FEMALE = {"she","her","woman","girl","mother","mom","mum","sister","daughter","aunt","grandmother","wife","mrs","ms","miss","lady","female","gal","lass"}
AGE_KEYWORDS = {
    "child": {"child","kid","young","teenager","teen","baby","infant","toddler","juvenile","youth"},
    "20s": {"twenties","twenty","college"},
    "30s": {"thirties","thirty","adult"},
    "40s": {"forties","forty","middle-aged"},
    "50s": {"fifties","fifty","mature"},
    "60s": {"sixties","sixty","senior"},
    "elderly": {"elderly","old","aged","ancient","veteran","weathered","grizzled","grandfather","grandmother"},
}
ACCENT_KEYWORDS = {
    "british": {"british","english","london","cockney","scottish","irish","welsh","posh","oxford"},
    "american": {"american","brooklyn","texan","southern","midwestern","california","boston"},
    "australian": {"australian","aussie"},
}
TRAIT_KEYWORDS = {
    "deep": {"deep","bass","baritone","low","booming"},
    "high": {"high","squeaky","shrill"},
    "raspy": {"raspy","gruff","gravelly","hoarse","scratchy"},
    "soft": {"soft","gentle","quiet","whispery"},
    "warm": {"warm","friendly","inviting","comforting"},
    "bright": {"bright","cheerful","energetic","bubbly","peppy"},
}

# Curated edge-tts voices mapped to ScriptCast character profiles
VOICE_LIBRARY = [
    {"id": "en-GB-RyanNeural",       "gender": "male",   "accent": "british",    "age": "30s",  "traits": ["warm","smooth"]},
    {"id": "en-GB-SoniaNeural",      "gender": "female", "accent": "british",    "age": "30s",  "traits": ["warm","clear"]},
    {"id": "en-GB-LibbyNeural",      "gender": "female", "accent": "british",    "age": "20s",  "traits": ["bright","soft"]},
    {"id": "en-GB-MaisieNeural",     "gender": "female", "accent": "british",    "age": "child","traits": ["bright"]},
    {"id": "en-GB-OliverNeural",     "gender": "male",   "accent": "british",    "age": "20s",  "traits": ["warm","friendly"]},
    {"id": "en-GB-ThomasNeural",     "gender": "male",   "accent": "british",    "age": "40s",  "traits": ["deep","authoritative"]},
    {"id": "en-US-GuyNeural",        "gender": "male",   "accent": "american",   "age": "30s",  "traits": ["deep","authoritative"]},
    {"id": "en-US-JennyNeural",      "gender": "female", "accent": "american",   "age": "30s",  "traits": ["warm","clear"]},
    {"id": "en-US-AriaNeural",       "gender": "female", "accent": "american",   "age": "30s",  "traits": ["expressive","bright"]},
    {"id": "en-US-DavisNeural",      "gender": "male",   "accent": "american",   "age": "30s",  "traits": ["deep","smooth"]},
    {"id": "en-US-TonyNeural",       "gender": "male",   "accent": "american",   "age": "40s",  "traits": ["deep","raspy"]},
    {"id": "en-US-NancyNeural",      "gender": "female", "accent": "american",   "age": "40s",  "traits": ["warm","authoritative"]},
    {"id": "en-AU-NatashaNeural",    "gender": "female", "accent": "australian", "age": "30s",  "traits": ["bright","clear"]},
    {"id": "en-AU-WilliamNeural",    "gender": "male",   "accent": "australian", "age": "30s",  "traits": ["warm","deep"]},
    {"id": "en-US-AnaNeural",        "gender": "female", "accent": "american",   "age": "child","traits": ["bright"]},
    {"id": "en-US-BrandonNeural",    "gender": "male",   "accent": "american",   "age": "20s",  "traits": ["bright","warm"]},
    {"id": "en-US-ChristopherNeural","gender": "male",   "accent": "american",   "age": "40s",  "traits": ["deep","authoritative"]},
    {"id": "en-US-ElizabethNeural",  "gender": "female", "accent": "american",   "age": "50s",  "traits": ["warm","mature"]},
    {"id": "en-IE-ConnorNeural",     "gender": "male",   "accent": "british",    "age": "30s",  "traits": ["warm","friendly"]},
    {"id": "en-IE-EmilyNeural",      "gender": "female", "accent": "british",    "age": "20s",  "traits": ["soft","warm"]},
]

def scrape_character_profile(char_name, elements):
    """Extract gender/age/accent/trait clues from surrounding action lines."""
    first_idx = next((i for i, e in enumerate(elements) if e.get("character") == char_name), None)
    if first_idx is None:
        return {}

    context_words = set()
    window_start = max(0, first_idx - 5)
    window_end = min(len(elements), first_idx + 10)
    for el in elements[window_start:window_end]:
        if el["type"] == "action":
            text_lower = el["text"].lower()
            if char_name.lower() in text_lower:
                idx = text_lower.index(char_name.lower())
                snippet = text_lower[max(0, idx-50):idx+80]
                context_words.update(snippet.split())

    # Also scan first 3 parentheticals
    paren_words = set()
    paren_count = 0
    for el in elements:
        if el.get("character") == char_name and el["type"] == "parenthetical" and paren_count < 3:
            paren_words.update(el["text"].lower().split())
            paren_count += 1

    all_words = context_words | paren_words

    gender = None
    male_score = sum(1 for w in all_words if w in GENDER_MALE)
    female_score = sum(1 for w in all_words if w in GENDER_FEMALE)
    if male_score > female_score:
        gender = "male"
    elif female_score > male_score:
        gender = "female"

    age = None
    for age_group, keywords in AGE_KEYWORDS.items():
        if any(w in all_words for w in keywords):
            age = age_group
            break

    accent = None
    for acc, keywords in ACCENT_KEYWORDS.items():
        if any(w in all_words for w in keywords):
            accent = acc
            break

    traits = [t for t, keywords in TRAIT_KEYWORDS.items() if any(w in all_words for w in keywords)]

    return {"gender": gender, "age": age, "accent": accent, "traits": traits}

def score_voice(voice, profile):
    score = 0
    if profile.get("gender") and voice["gender"] == profile["gender"]:
        score += 10
    if profile.get("age") and voice["age"] == profile["age"]:
        score += 5
    if profile.get("accent") and voice["accent"] == profile["accent"]:
        score += 5
    elif profile.get("accent") is None and voice["accent"] == "british":
        score += 3  # British accent bonus
    for trait in profile.get("traits", []):
        if trait in voice["traits"]:
            score += 3
    return score

def auto_cast(characters, elements):
    """Assign a unique edge-tts voice to each character."""
    char_line_counts = {}
    for el in elements:
        if el.get("character"):
            char_line_counts[el["character"]] = char_line_counts.get(el["character"], 0) + 1

    sorted_chars = sorted(characters, key=lambda c: char_line_counts.get(c, 0), reverse=True)
    used_voices = set()
    casting = {}

    for char in sorted_chars:
        profile = scrape_character_profile(char, elements)
        available = [v for v in VOICE_LIBRARY if v["id"] not in used_voices]
        if not available:
            available = VOICE_LIBRARY  # reuse if exhausted

        best = max(available, key=lambda v: score_voice(v, profile))
        casting[char] = {
            "voice_id": best["id"],
            "gender": best["gender"],
            "accent": best["accent"],
            "age": best["age"],
            "profile": profile
        }
        used_voices.add(best["id"])

    return casting

# ---------------------------------------------------------------------------
# Sentiment → TTS rate/pitch/volume
# ---------------------------------------------------------------------------
SENTIMENT_PARAMS = {
    "whisper":  {"rate": "-20%", "volume": "-30%", "pitch": "-5Hz"},
    "shout":    {"rate": "+10%", "volume": "+20%", "pitch": "+10Hz"},
    "angry":    {"rate": "+10%", "volume": "+10%", "pitch": "+5Hz"},
    "sad":      {"rate": "-10%", "volume": "-10%", "pitch": "-10Hz"},
    "excited":  {"rate": "+15%", "volume": "+10%", "pitch": "+8Hz"},
    "scared":   {"rate": "+10%", "volume": "-5%",  "pitch": "+5Hz"},
    "calm":     {"rate": "-5%",  "volume": "0%",   "pitch": "-5Hz"},
}
SENTIMENT_KEYWORDS = {
    "whisper": {"whisper","sotto voce","quietly","hushed","under breath"},
    "shout":   {"shout","yell","scream","bellowing","roars"},
    "angry":   {"angry","furious","rage","irate","livid","seething"},
    "sad":     {"sad","crying","sobbing","weeping","tearful","mournful"},
    "excited": {"excited","enthusiasm","eager","thrilled"},
    "scared":  {"scared","frightened","terrified","trembling","anxious"},
    "calm":    {"calm","soothing","gentle","peaceful","measured"},
}

def detect_sentiment(parenthetical_text):
    words = set(parenthetical_text.lower().split())
    for sentiment, keywords in SENTIMENT_KEYWORDS.items():
        if words & keywords:
            return SENTIMENT_PARAMS[sentiment]
    return {}

# ---------------------------------------------------------------------------
# Audio caching
# ---------------------------------------------------------------------------
def cache_key(text, voice_id):
    raw = f"{text}|{voice_id}|edge-tts"
    return hashlib.sha256(raw.encode()).hexdigest()

def get_cached(text, voice_id):
    key = cache_key(text, voice_id)
    path = CACHE_DIR / f"{key}.mp3"
    if path.exists():
        return path.read_bytes()
    return None

def save_cache(text, voice_id, audio_bytes):
    key = cache_key(text, voice_id)
    path = CACHE_DIR / f"{key}.mp3"
    path.write_bytes(audio_bytes)

# ---------------------------------------------------------------------------
# edge-tts synthesis
# ---------------------------------------------------------------------------
async def synthesise_async(text, voice_id, rate="+0%", volume="+0%", pitch="+0Hz"):
    communicate = edge_tts.Communicate(text, voice_id, rate=rate, volume=volume, pitch=pitch)
    audio_chunks = []
    async for chunk in communicate.stream():
        if chunk["type"] == "audio":
            audio_chunks.append(chunk["data"])
    return b"".join(audio_chunks)

def synthesise(text, voice_id, sentiment_params=None):
    cached = get_cached(text, voice_id)
    if cached:
        return cached

    params = sentiment_params or {}
    rate   = params.get("rate",   "+0%")
    volume = params.get("volume", "+0%")
    pitch  = params.get("pitch",  "+0Hz")

    tts_text = expand_abbrevs(text)

    loop = asyncio.new_event_loop()
    try:
        audio = loop.run_until_complete(synthesise_async(tts_text, voice_id, rate, volume, pitch))
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

    f = request.files["file"]
    filename = f.filename or ""
    ext = filename.rsplit(".", 1)[-1].lower()

    tmp_path = f"/tmp/scriptcast_upload.{ext}"
    f.save(tmp_path)

    try:
        if ext == "pdf":
            elements, page_headers = parse_pdf(tmp_path)
        elif ext == "fdx":
            elements, page_headers = parse_fdx(tmp_path)
        else:
            return jsonify({"error": "Unsupported file type. Use .pdf or .fdx"}), 400
    except Exception as e:
        return jsonify({"error": f"Parse error: {str(e)}"}), 500

    # Extract unique characters
    characters = list({e["character"] for e in elements if e.get("character")})
    casting = auto_cast(characters, elements)

    # Build page map
    page_map = {}
    for i, el in enumerate(elements):
        pg = str(el.get("page", 1))
        page_map.setdefault(pg, []).append(i)

    return jsonify({
        "elements": elements,
        "casting": casting,
        "page_map": page_map,
        "page_headers": page_headers,
        "characters": characters,
    })

@app.route("/tts", methods=["POST"])
def tts():
    data = request.get_json()
    text        = data.get("text", "").strip()
    voice_id    = data.get("voice_id", "en-GB-RyanNeural")
    parenthetical = data.get("parenthetical", "")

    if not text:
        return jsonify({"error": "No text provided"}), 400

    sentiment_params = detect_sentiment(parenthetical) if parenthetical else {}

    try:
        audio_bytes = synthesise(text, voice_id, sentiment_params)
    except Exception as e:
        return jsonify({"error": f"TTS error: {str(e)}"}), 500

    import base64
    audio_b64 = base64.b64encode(audio_bytes).decode()
    return jsonify({"audio": audio_b64, "format": "mp3"})

@app.route("/voices", methods=["GET"])
def voices():
    return jsonify({"voices": VOICE_LIBRARY})

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5000))
    app.run(host="0.0.0.0", port=port, debug=False)
