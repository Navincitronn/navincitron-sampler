from __future__ import annotations

import csv
import hashlib
import io
import json
import os
import signal
import subprocess
import sys
import time
import threading
from collections import deque
from pathlib import Path
from typing import Any
from urllib.request import Request, urlopen

from dotenv import load_dotenv
from flask import Flask, jsonify, redirect, request, send_from_directory, session
from flask_cors import CORS

try:
    import spotipy
    from spotipy.oauth2 import SpotifyOAuth
except ImportError:
    spotipy = None
    SpotifyOAuth = None


BASE_DIR = Path(__file__).resolve().parent
load_dotenv(BASE_DIR / ".env")

SAMPLER_PATH = BASE_DIR / "sampler.py"
DEFAULT_ALBUMS_FILE = BASE_DIR / "albums.txt"
GRID_FILE = BASE_DIR / "grid.txt"
RANKED_SHEET_ID = "1JiZwXGPANDlhkobNPo0Xdw_5MrNpG1fWTbEbL-I1dcA"
RANKED_SHEET_GID = "0"
UPLOAD_DIR = BASE_DIR / ".sampler_uploads"
STATE_FILE = BASE_DIR / "sampler_state.json"

SCOPE = (
    "user-read-playback-state "
    "user-modify-playback-state "
    "user-read-private "
    "playlist-read-private "
    "playlist-read-collaborative"
)

FRONTEND_ORIGIN = os.getenv("FRONTEND_ORIGIN", "https://www.navincitron.com")

app = Flask(__name__, static_folder=str(BASE_DIR), static_url_path="")
app.secret_key = os.getenv("FLASK_SECRET_KEY", "dev-only-change-this")

# Cookies must be usable from www.navincitron.com -> api.navincitron.com fetch(..., credentials:"include").
# For local http testing, set FRONTEND_ORIGIN=http://127.0.0.1:5000 to avoid Secure-cookie requirements.
app.config.update(
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SECURE=FRONTEND_ORIGIN.startswith("https://"),
    SESSION_COOKIE_SAMESITE="None" if FRONTEND_ORIGIN.startswith("https://") else "Lax",
)

CORS(
    app,
    origins=[FRONTEND_ORIGIN],
    supports_credentials=True,
)


def require_env_vars(*names: str) -> None:
    missing = [name for name in names if not os.getenv(name)]
    if missing:
        raise RuntimeError(f"Missing environment variables: {', '.join(missing)}")


def make_oauth() -> SpotifyOAuth:
    if SpotifyOAuth is None:
        raise RuntimeError("spotipy is not installed. Run: pip install -r requirements.txt")

    require_env_vars(
        "SPOTIPY_CLIENT_ID",
        "SPOTIPY_CLIENT_SECRET",
        "SPOTIPY_REDIRECT_URI",
    )

    return SpotifyOAuth(
        client_id=os.getenv("SPOTIPY_CLIENT_ID"),
        client_secret=os.getenv("SPOTIPY_CLIENT_SECRET"),
        redirect_uri=os.getenv("SPOTIPY_REDIRECT_URI"),
        scope=SCOPE,
        cache_path=None,
        open_browser=False,
    )


def get_session_token_info() -> dict[str, Any]:
    token_info = session.get("spotify_token_info")

    if not token_info:
        raise RuntimeError("Not logged in with Spotify.")

    oauth = make_oauth()

    if oauth.is_token_expired(token_info):
        token_info = oauth.refresh_access_token(token_info["refresh_token"])
        session["spotify_token_info"] = token_info

    return token_info


@app.route("/login")
def login():
    return redirect(make_oauth().get_authorize_url())


@app.route("/callback")
def callback():
    code = request.args.get("code")

    if not code:
        return "Spotify authorization failed: missing code.", 400

    token_info = make_oauth().get_access_token(code, as_dict=True)
    session["spotify_token_info"] = token_info

    return redirect(FRONTEND_ORIGIN.rstrip("/") + "/shuffle.html")


@app.route("/api/auth-status")
def auth_status():
    try:
        get_session_token_info()
        return jsonify({"ok": True, "authenticated": True})
    except Exception:
        return jsonify({"ok": True, "authenticated": False})


sampler_process: subprocess.Popen[str] | None = None
sampler_lock = threading.Lock()
log_lines: deque[str] = deque(maxlen=300)
last_command: list[str] = []
current_cover_cache: dict[str, Any] = {"timestamp": 0.0, "data": None}


def append_log(line: str) -> None:
    line = line.rstrip()
    if line:
        log_lines.append(line)


def stream_process_output(process: subprocess.Popen[str]) -> None:
    if process.stdout is None:
        return

    for line in process.stdout:
        append_log(line)

    process.wait()
    append_log(f"[sampler exited with code {process.returncode}]")


def get_spotify_client():
    if spotipy is None:
        raise RuntimeError("spotipy is not installed. Run: pip install -r requirements.txt")

    token_info = get_session_token_info()
    return spotipy.Spotify(auth=token_info["access_token"])


def pause_spotify() -> None:
    try:
        sp = get_spotify_client()
        sp.pause_playback()
        append_log("[Spotify playback paused]")
    except Exception as error:
        append_log(f"[warning: could not pause Spotify playback: {error}]")


def process_is_running() -> bool:
    global sampler_process
    return sampler_process is not None and sampler_process.poll() is None


def form_bool(value: Any, default: bool = False) -> bool:
    if value is None:
        return default

    if isinstance(value, bool):
        return value

    return str(value).strip().lower() in {"1", "true", "yes", "on"}


def save_uploaded_albums_file() -> Path | None:
    uploaded_file = request.files.get("albumsFile")

    if uploaded_file is None or not uploaded_file.filename:
        return None

    UPLOAD_DIR.mkdir(parents=True, exist_ok=True)
    upload_path = UPLOAD_DIR / f"uploaded_albums_{int(time.time())}.txt"
    uploaded_file.save(upload_path)

    if upload_path.stat().st_size == 0:
        upload_path.unlink(missing_ok=True)
        raise ValueError("Uploaded text file is empty.")

    return upload_path



def write_sampler_token_cache() -> Path:
    """
    Writes the logged-in user's Spotify token info to a temporary Spotipy cache
    file so the sampler subprocess can authenticate without opening a browser.
    """

    token_info = get_session_token_info()

    UPLOAD_DIR.mkdir(parents=True, exist_ok=True)
    token_cache_path = UPLOAD_DIR / f"spotify_token_{int(time.time())}_{os.getpid()}.json"
    token_cache_path.write_text(json.dumps(token_info), encoding="utf-8")

    return token_cache_path


@app.route("/api/start", methods=["POST"])
def start_sampler():
    global sampler_process, last_command

    with sampler_lock:
        if process_is_running():
            return jsonify({"ok": False, "error": "sampler.py is already running."}), 409

        is_form_request = bool(request.form or request.files)

        if is_form_request:
            data = request.form
        else:
            data = request.get_json(silent=True) or {}

        try:
            start_index = int(data.get("startIndex", 1))
            assumed_duration_seconds = int(data.get("assumedDurationSeconds", 180))
            local_seek_delay_seconds = float(data.get("localSeekDelaySeconds", 0))
        except (TypeError, ValueError):
            return jsonify({"ok": False, "error": "Invalid numeric input."}), 400

        source_mode = str(data.get("sourceMode", "file")).strip().lower()
        if source_mode not in {"file", "playlist"}:
            return jsonify({"ok": False, "error": "Invalid source mode."}), 400

        playlist_link = str(data.get("playlistLink", "")).strip()

        clip_mode = str(data.get("clipMode", "defined")).strip().lower()

        try:
            if clip_mode == "random":
                clip_min_seconds = int(data.get("clipMinSeconds", 15))
                clip_max_seconds = int(data.get("clipMaxSeconds", 30))
                clip_seconds = None
            else:
                clip_seconds = int(data.get("clipSeconds", 15))
                clip_min_seconds = None
                clip_max_seconds = None
        except (TypeError, ValueError):
            return jsonify({"ok": False, "error": "Invalid clip-length input."}), 400

        if start_index < 1:
            return jsonify({"ok": False, "error": "Start index must be 1 or greater."}), 400

        if clip_mode == "random":
            if clip_min_seconds < 1 or clip_max_seconds < 1:
                return jsonify({"ok": False, "error": "Clip min/max must be 1 or greater."}), 400
            if clip_min_seconds > clip_max_seconds:
                return jsonify({"ok": False, "error": "Clip minimum cannot be greater than clip maximum."}), 400
        elif clip_seconds is None or clip_seconds < 1:
            return jsonify({"ok": False, "error": "Clip seconds must be 1 or greater."}), 400

        if assumed_duration_seconds < 1:
            return jsonify({"ok": False, "error": "Assumed duration must be 1 or greater."}), 400
        if local_seek_delay_seconds < 0:
            return jsonify({"ok": False, "error": "Local-file seek delay cannot be negative."}), 400

        albums_file: Path | None = None

        if source_mode == "playlist":
            if not playlist_link:
                return jsonify({"ok": False, "error": "Enter a Spotify playlist link first."}), 400
            if "open.spotify.com/playlist/" not in playlist_link and not playlist_link.startswith("spotify:playlist:"):
                return jsonify({"ok": False, "error": "The playlist link must be a Spotify playlist URL or URI."}), 400
        else:
            try:
                uploaded_albums_file = save_uploaded_albums_file()
            except ValueError as error:
                return jsonify({"ok": False, "error": str(error)}), 400
            except Exception as error:
                return jsonify({"ok": False, "error": f"Could not save uploaded text file: {error}"}), 500

            if uploaded_albums_file is None:
                if is_form_request:
                    return jsonify({"ok": False, "error": "Upload a .txt file containing album or playlist links."}), 400

                # Backward-compatible fallback for direct JSON/API calls.
                if not DEFAULT_ALBUMS_FILE.exists():
                    return jsonify({"ok": False, "error": "No uploaded text file was provided and albums.txt was not found."}), 400
                albums_file = DEFAULT_ALBUMS_FILE
            else:
                albums_file = uploaded_albums_file

        random_start = form_bool(data.get("randomStart"), True)

        try:
            spotify_token_cache = write_sampler_token_cache()
        except RuntimeError:
            return jsonify({"ok": False, "error": "Press Login with Spotify before starting the sampler."}), 401
        except Exception as error:
            return jsonify({"ok": False, "error": f"Could not prepare Spotify token cache: {error}"}), 500

        cmd = [
            sys.executable,
            "-u",
            str(SAMPLER_PATH),
            "--delay-seconds",
            "0",
            "--assumed-duration-seconds",
            str(assumed_duration_seconds),
            "--local-seek-delay-seconds",
            str(local_seek_delay_seconds),
            "--spotify-token-cache",
            str(spotify_token_cache),
        ]

        if source_mode == "playlist":
            cmd.extend(["--playlist-link", playlist_link])
        else:
            cmd.extend(
                [
                    "--albums-file",
                    str(albums_file),
                    "--start-index",
                    str(start_index),
                ]
            )

        if clip_mode == "random":
            cmd.extend(
                [
                    "--clip-min-seconds",
                    str(clip_min_seconds),
                    "--clip-max-seconds",
                    str(clip_max_seconds),
                ]
            )
        else:
            cmd.extend(["--clip-seconds", str(clip_seconds)])

        if random_start:
            cmd.append("--random-start")

        log_lines.clear()
        append_log("[starting sampler.py]")
        append_log(" ".join(cmd))
        last_command = cmd[:]

        env = os.environ.copy()
        env["PYTHONUNBUFFERED"] = "1"

        try:
            sampler_process = subprocess.Popen(
                cmd,
                cwd=str(BASE_DIR),
                env=env,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                bufsize=1,
            )
        except Exception as error:
            sampler_process = None
            return jsonify({"ok": False, "error": str(error)}), 500

        threading.Thread(target=stream_process_output, args=(sampler_process,), daemon=True).start()

        return jsonify({"ok": True, "running": True})


@app.route("/api/stop", methods=["POST"])
def stop_sampler():
    global sampler_process

    with sampler_lock:
        was_running = process_is_running()

        if was_running and sampler_process is not None:
            append_log("[stopping sampler.py]")
            try:
                sampler_process.terminate()
                sampler_process.wait(timeout=3)
            except subprocess.TimeoutExpired:
                sampler_process.kill()
                sampler_process.wait(timeout=3)
            except Exception as error:
                append_log(f"[warning: could not terminate sampler.py cleanly: {error}]")

        pause_spotify()

        return jsonify({"ok": True, "running": process_is_running(), "wasRunning": was_running})



def best_spotify_image(images: list[dict[str, Any]] | None) -> dict[str, Any] | None:
    if not images:
        return None

    valid_images = [image for image in images if isinstance(image, dict) and image.get("url")]
    if not valid_images:
        return None

    # Prefer the largest image. Spotify album artwork is commonly exposed as
    # 640x640, but the page displays it in a fixed 300x300 frame.
    return max(valid_images, key=lambda image: int(image.get("width") or 0))


def parse_spotify_uri_id(uri: str | None, expected_type: str) -> str | None:
    if not uri:
        return None

    parts = uri.split(":")
    if len(parts) == 3 and parts[0] == "spotify" and parts[1] == expected_type:
        return parts[2]

    return None


def get_current_cover_art() -> dict[str, Any] | None:
    """
    Reads current track/cover data written locally by sampler.py.

    This intentionally avoids Spotify current_playback() polling. The browser
    can keep polling /api/status, but /api/status no longer spends a Spotify Web
    API call every second or two.
    """

    if not STATE_FILE.exists():
        return None

    try:
        state = json.loads(STATE_FILE.read_text(encoding="utf-8"))
    except Exception:
        return None

    cover_art = state.get("coverArt")
    if isinstance(cover_art, dict):
        return cover_art

    return None


@app.route("/api/status", methods=["GET"])
def status():
    return jsonify(
        {
            "ok": True,
            "running": process_is_running(),
            "returnCode": None if sampler_process is None else sampler_process.poll(),
            "lastCommand": last_command,
            "log": list(log_lines),
            "coverArt": get_current_cover_art(),
        }
    )


def text_signature(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


@app.route("/api/grid-text", methods=["GET"])
def grid_text():
    if not GRID_FILE.exists():
        return jsonify({"ok": False, "error": "grid.txt was not found."}), 404

    text = GRID_FILE.read_text(encoding="utf-8")
    return jsonify(
        {
            "ok": True,
            "text": text,
            "signature": text_signature(text),
            "source": "grid.txt",
        }
    )


def ranked_sheet_csv_url() -> str:
    return (
        f"https://docs.google.com/spreadsheets/d/{RANKED_SHEET_ID}/"
        f"export?format=csv&gid={RANKED_SHEET_GID}"
    )


def fetch_ranked_sheet_csv() -> str:
    request = Request(
        ranked_sheet_csv_url(),
        headers={"User-Agent": "Mozilla/5.0 NavincitronTopster/1.0"},
    )
    with urlopen(request, timeout=20) as response:
        data = response.read()
    return data.decode("utf-8-sig", errors="replace")


def ranked_sheet_csv_to_album_text(csv_text: str) -> str:
    rows = csv.reader(io.StringIO(csv_text))
    lines: list[str] = []

    for row_index, row in enumerate(rows):
        if len(row) < 5:
            continue

        album_title = row[2].strip()
        artist_name = row[3].strip()
        date_text = row[4].strip()

        if row_index == 0 and album_title.lower().replace(" ", "") == "albumname":
            continue

        if not album_title or not artist_name:
            continue

        if date_text:
            lines.append(f"{artist_name} - {album_title} ({date_text})")
        else:
            lines.append(f"{artist_name} - {album_title}")

    return "\n".join(lines)


@app.route("/api/ranked-grid-text", methods=["GET"])
def ranked_grid_text():
    try:
        csv_text = fetch_ranked_sheet_csv()
    except Exception as error:
        return jsonify(
            {
                "ok": False,
                "error": (
                    "Could not read the ranked Google Sheet. Make sure it is shared "
                    f"publicly. Detail: {error}"
                ),
            }
        ), 502

    if csv_text.lstrip().lower().startswith(("<!doctype html", "<html")):
        return jsonify(
            {
                "ok": False,
                "error": "The Google Sheet returned HTML instead of CSV. Share it publicly first.",
            }
        ), 502

    text = ranked_sheet_csv_to_album_text(csv_text)
    return jsonify(
        {
            "ok": True,
            "text": text,
            "signature": text_signature(text),
            "source": "Google Sheets ranked albums",
        }
    )


@app.route("/")
def root():
    return send_from_directory(BASE_DIR, "index.html")


@app.route("/<path:filename>")
def static_files(filename: str):
    target = BASE_DIR / filename
    if target.is_file():
        return send_from_directory(BASE_DIR, filename)
    return send_from_directory(BASE_DIR, "index.html")


if __name__ == "__main__":
    app.run(host="127.0.0.1", port=5000, debug=True)
