from __future__ import annotations

import csv
import hashlib
import hmac
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
from urllib.parse import urlparse
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
TOPSTER_COVER_CACHE_FILE = BASE_DIR / "topster_cover_cache.json"
TOPSTER_SETTINGS_FILE = BASE_DIR / "topster_settings.json"

SCOPE = (
    "user-read-playback-state "
    "user-modify-playback-state "
    "user-read-private "
    "playlist-read-private "
    "playlist-read-collaborative"
)

def parse_csv_env(name: str, fallback: str) -> list[str]:
    raw = os.getenv(name) or os.getenv("FRONTEND_ORIGIN") or fallback
    values = [item.strip().rstrip("/") for item in raw.split(",") if item.strip()]

    # navincitron.com and www.navincitron.com both serve the static frontend.
    # Include both unless the deployment explicitly provides FRONTEND_ORIGINS.
    if name == "FRONTEND_ORIGINS" and not os.getenv(name):
        expanded = []
        for value in values:
            expanded.append(value)
            if value == "https://www.navincitron.com":
                expanded.append("https://navincitron.com")
            elif value == "https://navincitron.com":
                expanded.append("https://www.navincitron.com")
        values = expanded

    return list(dict.fromkeys(values)) or [fallback.rstrip("/")]


FRONTEND_ORIGINS = parse_csv_env("FRONTEND_ORIGINS", "https://www.navincitron.com,https://navincitron.com")
FRONTEND_ORIGIN = FRONTEND_ORIGINS[0]
TOPSTER_ADMIN_ALLOWED_IPS = {
    item.strip()
    for item in os.getenv("TOPSTER_ADMIN_ALLOWED_IPS", "").split(",")
    if item.strip()
}


def normalize_secret_text(value: Any) -> str:
    text = str(value or "").replace("\ufeff", "").strip()
    if len(text) >= 2 and text[0] == text[-1] and text[0] in {"'", '"'}:
        text = text[1:-1].strip()
    return text


def read_env_file_value(name: str) -> str:
    """
    Fallback reader for deployments where the process was not restarted after
    editing .env. Environment variables from the hosting platform still take
    precedence, but this lets the admin password be read directly from the local
    backend .env file when it exists.
    """

    env_path = BASE_DIR / ".env"
    if not env_path.exists():
        return ""

    try:
        for raw_line in env_path.read_text(encoding="utf-8-sig").splitlines():
            line = raw_line.strip()
            if not line or line.startswith("#") or "=" not in line:
                continue
            key, raw_value = line.split("=", 1)
            if key.strip() == name:
                return normalize_secret_text(raw_value)
    except Exception:
        return ""

    return ""


def get_topster_admin_password() -> str:
    return normalize_secret_text(os.getenv("TOPSTER_ADMIN_PASSWORD") or read_env_file_value("TOPSTER_ADMIN_PASSWORD"))


def topster_admin_password_is_configured() -> bool:
    return bool(get_topster_admin_password())


def submitted_topster_password_is_valid(submitted_password: str) -> bool:
    configured_password = get_topster_admin_password()
    if not configured_password:
        return False
    return hmac.compare_digest(normalize_secret_text(submitted_password), configured_password)


app = Flask(__name__, static_folder=str(BASE_DIR), static_url_path="")
app.secret_key = os.getenv("FLASK_SECRET_KEY", "dev-only-change-this")

# Cookies must be usable from www.navincitron.com -> api.navincitron.com fetch(..., credentials:"include").
# For local http testing, set FRONTEND_ORIGINS=http://127.0.0.1:5000 to avoid Secure-cookie requirements.
USES_HTTPS_FRONTEND = any(origin.startswith("https://") for origin in FRONTEND_ORIGINS)
app.config.update(
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SECURE=USES_HTTPS_FRONTEND,
    SESSION_COOKIE_SAMESITE="None" if USES_HTTPS_FRONTEND else "Lax",
)

CORS(
    app,
    origins=FRONTEND_ORIGINS,
    supports_credentials=True,
)



def request_ip_address() -> str:
    remote_addr = request.headers.get("X-Forwarded-For", request.remote_addr or "")
    return remote_addr.split(",")[0].strip()


def is_local_request() -> bool:
    """
    Allows local development on the host computer to use grid.html/ranked_grid.html
    without a password when the browser is hitting this Flask app directly.
    """

    return request_ip_address() in {"127.0.0.1", "::1", "localhost"}


def is_admin_ip_allowed() -> bool:
    # Leave TOPSTER_ADMIN_ALLOWED_IPS unset to allow password login from any IP.
    # Set it to a comma-separated list to restrict admin login/session use to those IPs.
    return not TOPSTER_ADMIN_ALLOWED_IPS or request_ip_address() in TOPSTER_ADMIN_ALLOWED_IPS


def is_topster_admin() -> bool:
    if is_local_request():
        return True
    return bool(session.get("topster_admin")) and is_admin_ip_allowed()


def is_allowed_frontend_url(url: str) -> bool:
    try:
        parsed = urlparse(url)
    except Exception:
        return False

    if not parsed.scheme and not parsed.netloc and url.startswith("/"):
        return True

    origin = f"{parsed.scheme}://{parsed.netloc}".rstrip("/")
    return origin in FRONTEND_ORIGINS


def safe_frontend_redirect_url(raw_next: str | None, fallback_path: str = "/grid.html") -> str:
    candidate = (raw_next or "").strip()
    if candidate and is_allowed_frontend_url(candidate):
        return candidate
    return FRONTEND_ORIGIN.rstrip("/") + fallback_path


def require_topster_admin_response():
    if is_topster_admin():
        return None
    return jsonify({"ok": False, "error": "Topster editor access is restricted to the host/admin computer."}), 403


def read_json_file(path: Path, fallback: Any) -> Any:
    if not path.exists():
        return fallback

    try:
        raw = path.read_text(encoding="utf-8")
        if not raw.strip():
            return fallback
        parsed = json.loads(raw)
        return parsed if parsed is not None else fallback
    except Exception:
        return fallback


def write_json_file(path: Path, data: Any) -> None:
    temp_path = path.with_suffix(path.suffix + ".tmp")
    temp_path.write_text(json.dumps(data, indent=2, ensure_ascii=False), encoding="utf-8")
    temp_path.replace(path)


def get_topster_settings() -> dict[str, Any]:
    settings = read_json_file(TOPSTER_SETTINGS_FILE, {})
    return settings if isinstance(settings, dict) else {}


def get_topster_cover_cache() -> dict[str, Any]:
    cover_cache = read_json_file(TOPSTER_COVER_CACHE_FILE, {})
    return cover_cache if isinstance(cover_cache, dict) else {}


def normalize_topster_cover_cache(value: Any) -> dict[str, Any]:
    if not isinstance(value, dict):
        return {}

    normalized: dict[str, Any] = {}
    for key, item in value.items():
        if not isinstance(key, str) or not isinstance(item, dict):
            continue
        image_src = item.get("imageSrc")
        if not isinstance(image_src, str) or not image_src.startswith(("http://", "https://")):
            continue
        normalized[key] = {
            "title": str(item.get("title") or ""),
            "artist": str(item.get("artist") or ""),
            "imageSrc": image_src,
            "href": str(item.get("href") or ""),
            "source": str(item.get("source") or ""),
            "selectedManually": bool(item.get("selectedManually")),
            "savedAt": str(item.get("savedAt") or time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())),
        }
    return normalized


def normalize_topster_settings(value: Any) -> dict[str, Any]:
    if not isinstance(value, dict):
        return {}

    allowed_fonts = {
        "Arial", "Verdana", "Helvetica Neue", "Sans-serif", "Monospace",
        "Open Sans", "Helvetica", "Georgia", "Tahoma", "Calibri",
    }
    allowed_sidebar_modes = {"artist-title", "title-only", "hidden"}

    def clamp_int(raw: Any, minimum: int, maximum: int, fallback: int) -> int:
        try:
            number = int(round(float(raw)))
        except Exception:
            return fallback
        return min(maximum, max(minimum, number))

    return {
        "width": clamp_int(value.get("width"), 1, 25, 10),
        "height": clamp_int(value.get("height"), 1, 10, 10),
        "sidebarMode": value.get("sidebarMode") if value.get("sidebarMode") in allowed_sidebar_modes else "artist-title",
        "roundCorners": clamp_int(value.get("roundCorners"), 0, 24, 0),
        "albumGap": clamp_int(value.get("albumGap"), 0, 100, 4),
        "font": value.get("font") if value.get("font") in allowed_fonts else "Arial",
    }


@app.route("/topster-admin-login", methods=["GET", "POST"])
def topster_admin_login():
    next_url = safe_frontend_redirect_url(request.values.get("next"))

    if request.method == "POST":
        submitted_password = request.form.get("password", "")
        if not is_admin_ip_allowed():
            return "Topster admin login is not allowed from this IP address.", 403
        if not topster_admin_password_is_configured():
            return (
                "Topster admin password is not configured on the live backend. "
                "Set TOPSTER_ADMIN_PASSWORD in the backend hosting environment and restart/redeploy the service."
            ), 500
        if submitted_topster_password_is_valid(submitted_password):
            session["topster_admin"] = True
            return redirect(next_url)
        return "Invalid Topster admin password.", 403

    if is_topster_admin():
        return redirect(next_url)

    escaped_next = next_url.replace('&', '&amp;').replace('"', '&quot;').replace('<', '&lt;').replace('>', '&gt;')

    return f"""
    <!doctype html>
    <html lang=\"en\">
    <head>
        <meta charset=\"utf-8\">
        <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">
        <title>Topster Admin Login</title>
        <style>
            body {{ background:#333; color:#fff; font-family:Arial,sans-serif; display:grid; place-items:center; min-height:100vh; margin:0; }}
            form {{ background:#444; border-radius:10px; padding:24px; width:min(420px, calc(100vw - 32px)); }}
            input {{ box-sizing:border-box; width:100%; padding:10px; margin:10px 0 16px; }}
            button {{ background:#1974D2; border:0; border-radius:5px; color:white; cursor:pointer; padding:10px 18px; }}
        </style>
    </head>
    <body>
        <form method=\"post\">
            <h1>Topster Admin Login</h1>
            <p>Only the host/admin computer can edit Grid and Ranked Grid.</p>
            {"<p style='color:#ffcf85;font-weight:bold;'>Admin password is not configured on this backend.</p>" if not topster_admin_password_is_configured() else ""}
            <input type=\"hidden\" name=\"next\" value=\"{escaped_next}\">
            <label for=\"password\">Password</label>
            <input id=\"password\" name=\"password\" type=\"password\" autofocus required>
            <button type=\"submit\">Log in</button>
        </form>
    </body>
    </html>
    """


@app.route("/api/topster-admin-logout", methods=["POST"])
def topster_admin_logout():
    session.pop("topster_admin", None)
    return jsonify({"ok": True})


@app.route("/api/topster-admin-status", methods=["GET"])
def topster_admin_status():
    return jsonify(
        {
            "ok": True,
            "authenticated": is_topster_admin(),
            "writable": is_topster_admin(),
            "passwordConfigured": topster_admin_password_is_configured(),
            "ipAllowed": is_admin_ip_allowed(),
            "frontendOrigins": FRONTEND_ORIGINS,
        }
    )


@app.route("/api/topster-shared-store", methods=["GET", "PUT", "DELETE"])
def topster_shared_store():
    if request.method == "GET":
        return jsonify(
            {
                "ok": True,
                "writable": is_topster_admin(),
                "settings": get_topster_settings(),
                "coverCache": get_topster_cover_cache(),
            }
        )

    admin_error = require_topster_admin_response()
    if admin_error is not None:
        return admin_error

    if request.method == "DELETE":
        write_json_file(TOPSTER_COVER_CACHE_FILE, {})
        return jsonify(
            {
                "ok": True,
                "writable": True,
                "settings": get_topster_settings(),
                "coverCache": {},
            }
        )

    payload = request.get_json(silent=True) or {}

    settings = get_topster_settings()
    if isinstance(payload.get("settings"), dict):
        settings = normalize_topster_settings(payload["settings"])
        write_json_file(TOPSTER_SETTINGS_FILE, settings)

    cover_cache = get_topster_cover_cache()
    if isinstance(payload.get("coverCache"), dict):
        cover_cache = normalize_topster_cover_cache(payload["coverCache"])
        write_json_file(TOPSTER_COVER_CACHE_FILE, cover_cache)

    return jsonify(
        {
            "ok": True,
            "writable": True,
            "settings": settings,
            "coverCache": cover_cache,
        }
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
        single_link_random_order = form_bool(data.get("singleLinkRandomOrder"), True)

        clip_mode = str(data.get("clipMode", "defined")).strip().lower()

        try:
            if clip_mode == "random":
                clip_min_seconds = int(data.get("clipMinSeconds", 18))
                clip_max_seconds = int(data.get("clipMaxSeconds", 25))
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
                return jsonify({"ok": False, "error": "Enter a Spotify album or playlist link first."}), 400
            valid_single_link = (
                "open.spotify.com/playlist/" in playlist_link
                or "open.spotify.com/album/" in playlist_link
                or playlist_link.startswith("spotify:playlist:")
                or playlist_link.startswith("spotify:album:")
            )
            if not valid_single_link:
                return jsonify({"ok": False, "error": "The link must be a Spotify album or playlist URL/URI."}), 400
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
            cmd.extend(["--single-link", playlist_link])
            cmd.extend(["--single-link-order", "random" if single_link_random_order else "ordered"])
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
    protected_topster_pages = {"grid.html", "ranked_grid.html"}

    if filename in protected_topster_pages and not is_topster_admin():
        if TOPSTER_ADMIN_PASSWORD:
            return redirect("/topster-admin-login")
        return "Topster editor access is restricted to the host computer.", 403

    target = BASE_DIR / filename
    if target.is_file():
        return send_from_directory(BASE_DIR, filename)
    return send_from_directory(BASE_DIR, "index.html")


if __name__ == "__main__":
    app.run(host="127.0.0.1", port=5000, debug=True)
