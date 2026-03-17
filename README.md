# ScriptCast

Professional screenplay audio player. Upload a PDF or FDX screenplay, auto-cast characters to distinct voices, and listen with a page-accurate visual display.

## Stack

- **Backend**: Python / Flask
- **Parser**: pdfplumber (PDF) + ElementTree (FDX)
- **TTS**: edge-tts (Microsoft Edge Neural voices — free, no API key)
- **Hosting**: Railway

## Local development

```bash
pip install -r requirements.txt
python main.py
# → http://localhost:5000
```

## Deploy to Railway

1. Push this repo to GitHub
2. Go to [railway.app](https://railway.app) → New Project → Deploy from GitHub repo
3. Select your repo — Railway auto-detects Python and runs gunicorn
4. Done. Your app is live at `https://your-app.railway.app`

No environment variables required for the free edge-tts provider.

## Upgrade to ElevenLabs / OpenAI (post-funding)

Add these env vars in Railway dashboard:

```
ELEVENLABS_API_KEY=your_key
OPENAI_API_KEY=your_key
TTS_PROVIDER=elevenlabs   # or "openai"
```

The `/tts` endpoint in `main.py` is designed to swap providers with minimal changes.

## Project structure

```
main.py              # Flask app, parser, auto-cast engine, TTS
templates/index.html # Single-page frontend (upload → cast → playback)
requirements.txt
railway.json
audio_cache/         # SHA256-keyed MP3 cache (auto-created)
```

## Features

- PDF + FDX parsing with state machine element detection
- Auto-cast engine: scrapes action lines for gender/age/accent/trait clues
- 20 curated edge-tts voices (British, American, Australian, Irish)
- Sentiment detection from parentheticals → rate/pitch/volume modulation
- SHA256 audio cache (identical lines never regenerated)
- Page-accurate screenplay display with Final Draft formatting
- Actor's Dojo: mute any character to rehearse your own lines
- Scene jump dropdown, keyword search, speed control (1×–2×)
- 3-line preload queue for seamless playback
