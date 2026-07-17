from __future__ import annotations

import csv
import hashlib
import hmac
import io
import json
import os
import random
import re
import secrets
import signal
import subprocess
import sys
import time
import threading
import unicodedata
from collections import deque
from datetime import timedelta
from pathlib import Path
from typing import Any
from urllib.error import HTTPError, URLError
from urllib.parse import quote_plus, unquote, urlencode, urlparse
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

try:
    import sampler as sampler_tools
except ImportError:
    sampler_tools = None

try:
    import redis
    from redis.exceptions import RedisError
except ImportError:
    redis = None

    class RedisError(Exception):
        pass


BASE_DIR = Path(__file__).resolve().parent
load_dotenv(BASE_DIR / ".env")

SAMPLER_PATH = BASE_DIR / "sampler.py"
DEFAULT_ALBUMS_FILE = BASE_DIR / "albums.txt"
GRID_FILE = BASE_DIR / "grid.txt"
RANKED_SHEET_ID = "1JiZwXGPANDlhkobNPo0Xdw_5MrNpG1fWTbEbL-I1dcA"
RANKED_SHEET_GID = "0"
UPLOAD_DIR = BASE_DIR / ".sampler_uploads"
STATE_FILE = BASE_DIR / "sampler_state.json"
CONTROL_FILE = BASE_DIR / "sampler_control.json"
TOPSTER_COVER_CACHE_FILE = BASE_DIR / "topster_cover_cache.json"
TOPSTER_SETTINGS_FILE = BASE_DIR / "topster_settings.json"
TOPSTER_SOURCE_TEXT_FILE = BASE_DIR / "topster_source_text.json"
TOPSTER_REDIS_KEY_PREFIX = os.getenv("TOPSTER_REDIS_KEY_PREFIX", "navincitron:topster").strip() or "navincitron:topster"
TOPSTER_REDIS_CLIENT: Any | None = None
TOPSTER_REDIS_CLIENT_ERROR = ""

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

TOPSTER_STORE_KEYS = {"grid", "ranked", "draft", "checklist"}
TOPSTER_STORE_ALIASES = {
    "grid": "grid",
    "grid-file": "grid",
    "album-list": "grid",
    "album_list": "grid",
    "albums": "grid",
    "draft": "draft",
    "draft-file": "draft",
    "draft_grid": "draft",
    "draft-grid": "draft",
    "draft_album_list": "draft",
    "draft-album-list": "draft",
    "checklist": "checklist",
    "checklist-file": "checklist",
    "draft_checklist": "checklist",
    "draft-checklist": "checklist",
    "checklist_album_list": "checklist",
    "checklist-album-list": "checklist",
    "ranked": "ranked",
    "ranked-sheet": "ranked",
    "ranked_album_list": "ranked",
    "ranked-album-list": "ranked",
}


def normalize_topster_store_key(value: Any = None) -> str:
    raw = str(value or request.args.get("source") or request.args.get("kind") or "grid").strip().lower()
    return TOPSTER_STORE_ALIASES.get(raw, "grid")


def is_topster_source_container(value: Any) -> bool:
    return isinstance(value, dict) and any(key in value for key in TOPSTER_STORE_KEYS)


def get_topster_source_map(path: Path) -> dict[str, dict[str, Any]]:
    data = read_json_file(path, {})
    if not isinstance(data, dict):
        data = {}

    if is_topster_source_container(data):
        return {
            "grid": data.get("grid") if isinstance(data.get("grid"), dict) else {},
            "ranked": data.get("ranked") if isinstance(data.get("ranked"), dict) else {},
            "draft": data.get("draft") if isinstance(data.get("draft"), dict) else {},
            "checklist": data.get("checklist") if isinstance(data.get("checklist"), dict) else {},
        }

    # Backward-compatible migration path: older builds stored one flat object.
    # Seed the existing public stores from that flat object until each one is saved independently.
    # Draft starts empty because it is based on a host-uploaded Notepad file, not grid.txt.
    return {
        "grid": data,
        "ranked": data,
        "draft": {},
        "checklist": {},
    }


def write_topster_source_map(path: Path, source_key: str, source_value: dict[str, Any]) -> dict[str, dict[str, Any]]:
    source_key = normalize_topster_store_key(source_key)
    source_map = get_topster_source_map(path)
    source_map[source_key] = source_value
    write_json_file(path, source_map)
    return source_map


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
try:
    SPOTIFY_DEVICE_SESSION_DAYS = max(1, int(os.getenv("SPOTIFY_DEVICE_SESSION_DAYS", "180") or 180))
except (TypeError, ValueError):
    SPOTIFY_DEVICE_SESSION_DAYS = 180

try:
    TOPSTER_ADMIN_SESSION_DAYS = max(1, int(os.getenv("TOPSTER_ADMIN_SESSION_DAYS", "365") or 365))
except (TypeError, ValueError):
    TOPSTER_ADMIN_SESSION_DAYS = 365

TOPSTER_ADMIN_DEVICE_COOKIE_NAME = (
    os.getenv("TOPSTER_ADMIN_DEVICE_COOKIE_NAME", "navincitron_topster_admin_device").strip()
    or "navincitron_topster_admin_device"
)
TOPSTER_ADMIN_DEVICE_SESSION_SECONDS = TOPSTER_ADMIN_SESSION_DAYS * 24 * 60 * 60
TOPSTER_ADMIN_DEVICE_ID_PATTERN = re.compile(r"^[A-Za-z0-9_-]{32,160}$")
TOPSTER_ADMIN_DEVICE_REDIS_KEY_PREFIX = (
    os.getenv("TOPSTER_ADMIN_DEVICE_REDIS_KEY_PREFIX", "navincitron:topster-admin-device").strip(":")
    or "navincitron:topster-admin-device"
)

app.config.update(
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SECURE=USES_HTTPS_FRONTEND,
    SESSION_COOKIE_SAMESITE="None" if USES_HTTPS_FRONTEND else "Lax",
    # Spotify's access token expires quickly, but the refresh token and this
    # browser session should survive ordinary browser restarts and long idle
    # periods. The OAuth token itself is refreshed server-side when required.
    PERMANENT_SESSION_LIFETIME=timedelta(days=max(SPOTIFY_DEVICE_SESSION_DAYS, TOPSTER_ADMIN_SESSION_DAYS)),
    SESSION_REFRESH_EACH_REQUEST=False,
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


def valid_topster_admin_device_id(value: Any) -> str:
    candidate = str(value or "").strip()
    return candidate if TOPSTER_ADMIN_DEVICE_ID_PATTERN.fullmatch(candidate) else ""


def topster_admin_device_redis_key(device_id: str) -> str:
    digest = hashlib.sha256(device_id.encode("utf-8", errors="ignore")).hexdigest()
    return f"{TOPSTER_ADMIN_DEVICE_REDIS_KEY_PREFIX}:{digest}"


def get_topster_admin_device_id(create: bool = False) -> str:
    device_id = valid_topster_admin_device_id(request.cookies.get(TOPSTER_ADMIN_DEVICE_COOKIE_NAME))
    if not device_id:
        device_id = valid_topster_admin_device_id(session.get("topster_admin_device_id"))

    if not device_id and create:
        device_id = secrets.token_urlsafe(36)

    if device_id:
        if not session.permanent:
            session.permanent = True
        session["topster_admin_device_id"] = device_id

    return device_id


def topster_admin_device_is_remembered() -> bool:
    if not is_admin_ip_allowed():
        return False

    device_id = get_topster_admin_device_id(create=False)
    if not device_id or not topster_redis_is_configured():
        return False

    try:
        client = get_topster_redis_client()
        if client is None:
            return False
        key = topster_admin_device_redis_key(device_id)
        if not client.get(key):
            return False
        client.expire(key, TOPSTER_ADMIN_DEVICE_SESSION_SECONDS)
        session.permanent = True
        session["topster_admin"] = True
        return True
    except Exception:
        return False


def remember_topster_admin_device(response: Any) -> Any:
    session.permanent = True
    session["topster_admin"] = True
    device_id = get_topster_admin_device_id(create=True)

    if device_id and topster_redis_is_configured():
        try:
            client = get_topster_redis_client()
            if client is not None:
                client.setex(
                    topster_admin_device_redis_key(device_id),
                    TOPSTER_ADMIN_DEVICE_SESSION_SECONDS,
                    json.dumps(
                        {
                            "createdAt": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                            "lastIp": request_ip_address(),
                        },
                        ensure_ascii=False,
                    ),
                )
        except Exception:
            # The permanent signed Flask session remains the fallback.
            pass

    if device_id:
        response.set_cookie(
            TOPSTER_ADMIN_DEVICE_COOKIE_NAME,
            device_id,
            max_age=TOPSTER_ADMIN_DEVICE_SESSION_SECONDS,
            secure=USES_HTTPS_FRONTEND,
            httponly=True,
            samesite="None" if USES_HTTPS_FRONTEND else "Lax",
            path="/",
        )

    return response


def forget_topster_admin_device(response: Any) -> Any:
    device_id = get_topster_admin_device_id(create=False)
    if device_id and topster_redis_is_configured():
        try:
            client = get_topster_redis_client()
            if client is not None:
                client.delete(topster_admin_device_redis_key(device_id))
        except Exception:
            pass

    session.pop("topster_admin", None)
    session.pop("topster_admin_device_id", None)
    response.delete_cookie(
        TOPSTER_ADMIN_DEVICE_COOKIE_NAME,
        secure=USES_HTTPS_FRONTEND,
        httponly=True,
        samesite="None" if USES_HTTPS_FRONTEND else "Lax",
        path="/",
    )
    return response


def is_topster_admin() -> bool:
    if is_local_request():
        return True
    if not is_admin_ip_allowed():
        return False
    return bool(session.get("topster_admin")) or topster_admin_device_is_remembered()


def redirect_topster_frontend_page(filename: str):
    """
    Prevent the backend/API domain from serving stale copies of the static Topster
    pages. The canonical Topster UI lives in navincitron-website.
    Local Flask development can still serve a local copy if it exists.
    """

    if is_local_request() and (BASE_DIR / filename).exists():
        return send_from_directory(BASE_DIR, filename)

    target = FRONTEND_ORIGIN.rstrip("/") + "/" + filename
    if request.query_string:
        target += "?" + request.query_string.decode("utf-8", errors="ignore")
    return redirect(target, code=302)


@app.route("/grid.html")
def redirect_grid_html():
    return redirect_topster_frontend_page("grid.html")


@app.route("/ranked_grid.html")
def redirect_ranked_grid_html():
    return redirect_topster_frontend_page("ranked_grid.html")


@app.route("/album_list.html")
def redirect_album_list_html():
    return redirect_topster_frontend_page("album_list.html")


@app.route("/ranked_album_list.html")
def redirect_ranked_album_list_html():
    return redirect_topster_frontend_page("ranked_album_list.html")


@app.route("/draft_grid.html")
def redirect_draft_grid_html():
    return redirect_topster_frontend_page("draft_grid.html")


@app.route("/draft_album_list.html")
def redirect_draft_album_list_html():
    return redirect_topster_frontend_page("draft_album_list.html")


@app.route("/draft_checklist.html")
def redirect_draft_checklist_html():
    return redirect_topster_frontend_page("draft_checklist.html")


@app.route("/checklist.html")
def redirect_checklist_html():
    return redirect_topster_frontend_page("checklist.html")


@app.route("/lyrics.html")
def redirect_lyrics_html():
    return redirect_topster_frontend_page("lyrics.html")


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


def get_topster_redis_url() -> str:
    # REDIS_URL is the standard Render Key Value / Redis-style connection env var.
    # TOPSTER_REDIS_URL can be used instead if the sampler later gets another Redis dependency.
    return normalize_secret_text(os.getenv("TOPSTER_REDIS_URL") or os.getenv("REDIS_URL") or "")


def topster_redis_is_configured() -> bool:
    return bool(get_topster_redis_url())


def get_topster_redis_client() -> Any | None:
    global TOPSTER_REDIS_CLIENT, TOPSTER_REDIS_CLIENT_ERROR

    redis_url = get_topster_redis_url()
    if not redis_url:
        return None

    if redis is None:
        TOPSTER_REDIS_CLIENT_ERROR = "Redis client package is not installed. Add redis>=5.0.0 to requirements.txt and redeploy."
        return None

    if TOPSTER_REDIS_CLIENT is None:
        try:
            TOPSTER_REDIS_CLIENT = redis.from_url(
                redis_url,
                decode_responses=True,
                socket_connect_timeout=3,
                socket_timeout=5,
                health_check_interval=30,
            )
            TOPSTER_REDIS_CLIENT_ERROR = ""
        except Exception as error:
            TOPSTER_REDIS_CLIENT_ERROR = f"Could not create Redis client: {error}"
            TOPSTER_REDIS_CLIENT = None

    return TOPSTER_REDIS_CLIENT


def get_topster_storage_backend_name() -> str:
    if topster_redis_is_configured():
        return "redis" if redis is not None else "json-fallback-redis-package-missing"
    return "json"


def topster_redis_key(kind: str, source_key: str | None = None) -> str:
    source_key = normalize_topster_store_key(source_key)
    safe_prefix = TOPSTER_REDIS_KEY_PREFIX.strip(":") or "navincitron:topster"
    return f"{safe_prefix}:{kind}:{source_key}"


def read_topster_redis_json(kind: str, source_key: str | None = None) -> dict[str, Any] | None:
    client = get_topster_redis_client()
    if client is None:
        if topster_redis_is_configured():
            raise RuntimeError(TOPSTER_REDIS_CLIENT_ERROR or "Redis is configured but unavailable.")
        return None

    key = topster_redis_key(kind, source_key)
    try:
        raw = client.get(key)
    except RedisError as error:
        raise RuntimeError(f"Topster Redis read failed for {key}: {error}") from error

    if raw is None:
        return None

    try:
        parsed = json.loads(raw)
    except json.JSONDecodeError as error:
        raise RuntimeError(f"Topster Redis value for {key} is not valid JSON: {error}") from error

    if not isinstance(parsed, dict):
        raise RuntimeError(f"Topster Redis value for {key} is not a JSON object.")

    return parsed


def write_topster_redis_json(kind: str, source_key: str | None, value: dict[str, Any]) -> None:
    client = get_topster_redis_client()
    if client is None:
        raise RuntimeError(TOPSTER_REDIS_CLIENT_ERROR or "Redis is configured but unavailable.")

    key = topster_redis_key(kind, source_key)
    try:
        client.set(key, json.dumps(value, ensure_ascii=False))
    except RedisError as error:
        raise RuntimeError(f"Topster Redis write failed for {key}: {error}") from error


def delete_topster_redis_key(kind: str, source_key: str | None = None) -> None:
    client = get_topster_redis_client()
    if client is None:
        raise RuntimeError(TOPSTER_REDIS_CLIENT_ERROR or "Redis is configured but unavailable.")

    key = topster_redis_key(kind, source_key)
    try:
        client.delete(key)
    except RedisError as error:
        raise RuntimeError(f"Topster Redis delete failed for {key}: {error}") from error


def get_topster_json_settings(source_key: str | None = None) -> dict[str, Any]:
    settings_map = get_topster_source_map(TOPSTER_SETTINGS_FILE)
    settings = settings_map.get(normalize_topster_store_key(source_key), {})
    return settings if isinstance(settings, dict) else {}


def get_topster_json_cover_cache(source_key: str | None = None) -> dict[str, Any]:
    cover_cache_map = get_topster_source_map(TOPSTER_COVER_CACHE_FILE)
    cover_cache = cover_cache_map.get(normalize_topster_store_key(source_key), {})
    return cover_cache if isinstance(cover_cache, dict) else {}


def get_topster_json_source_text(source_key: str | None = None) -> dict[str, Any]:
    source_text_map = get_topster_source_map(TOPSTER_SOURCE_TEXT_FILE)
    source_text = source_text_map.get(normalize_topster_store_key(source_key), {})
    return normalize_topster_source_text(source_text) if isinstance(source_text, dict) else {}


def get_topster_settings(source_key: str | None = None) -> dict[str, Any]:
    source_key = normalize_topster_store_key(source_key)

    if topster_redis_is_configured():
        redis_settings = read_topster_redis_json("settings", source_key)
        if isinstance(redis_settings, dict):
            return redis_settings

        # One-time migration path: if older JSON files exist in local/dev storage,
        # seed Redis the first time this source is requested.
        json_settings = get_topster_json_settings(source_key)
        if json_settings:
            json_settings = normalize_topster_settings(json_settings)
            write_topster_redis_json("settings", source_key, json_settings)
            return json_settings

        return {}

    return get_topster_json_settings(source_key)


def get_topster_cover_cache(source_key: str | None = None) -> dict[str, Any]:
    source_key = normalize_topster_store_key(source_key)

    if topster_redis_is_configured():
        redis_cover_cache = read_topster_redis_json("cover_cache", source_key)
        if isinstance(redis_cover_cache, dict):
            return redis_cover_cache

        # One-time migration path: if older JSON files exist in local/dev storage,
        # seed Redis the first time this source is requested.
        json_cover_cache = get_topster_json_cover_cache(source_key)
        if json_cover_cache:
            json_cover_cache = normalize_topster_cover_cache(json_cover_cache)
            write_topster_redis_json("cover_cache", source_key, json_cover_cache)
            return json_cover_cache

        return {}

    return get_topster_json_cover_cache(source_key)


def get_topster_source_text(source_key: str | None = None) -> dict[str, Any]:
    source_key = normalize_topster_store_key(source_key)

    if topster_redis_is_configured():
        redis_source_text = read_topster_redis_json("source_text", source_key)
        if isinstance(redis_source_text, dict):
            return normalize_topster_source_text(redis_source_text)

        json_source_text = get_topster_json_source_text(source_key)
        if json_source_text:
            write_topster_redis_json("source_text", source_key, json_source_text)
            return json_source_text

        return {}

    return get_topster_json_source_text(source_key)


def normalize_topster_source_text(value: Any) -> dict[str, Any]:
    if not isinstance(value, dict):
        return {}

    text = value.get("text")
    if not isinstance(text, str):
        return {}

    # Keep the stored source intentionally small. A Topster draft text file should be text lines, not binary content.
    max_chars = 3_000_000
    if len(text) > max_chars:
        text = text[:max_chars]

    signature = value.get("signature")
    if not isinstance(signature, str) or not signature.strip():
        signature = hashlib.sha256(text.encode("utf-8", errors="ignore")).hexdigest()[:16]

    source_name = value.get("sourceName") or value.get("source") or "draft notepad file"
    if not isinstance(source_name, str):
        source_name = "draft notepad file"

    updated_at = value.get("updatedAt")
    if not isinstance(updated_at, str) or not updated_at.strip():
        updated_at = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())

    return {
        "text": text,
        "signature": signature,
        "sourceName": source_name[:240],
        "updatedAt": updated_at,
    }


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
    allowed_fonts = {
        "Arial", "Verdana", "Helvetica Neue", "Sans-serif", "Monospace",
        "Open Sans", "Helvetica", "Georgia", "Tahoma", "Calibri",
    }
    allowed_sidebar_modes = {"artist-title", "title-only", "hidden"}
    allowed_cover_overlays = {"none", "index", "year"}

    def clamp_int(raw: Any, minimum: int, maximum: int, fallback: int) -> int:
        try:
            number = int(round(float(raw)))
        except Exception:
            return fallback
        return min(maximum, max(minimum, number))

    def normalize_single_settings(raw_value: Any) -> dict[str, Any]:
        raw = raw_value if isinstance(raw_value, dict) else {}
        return {
            "width": clamp_int(raw.get("width"), 1, 25, 10),
            "height": clamp_int(raw.get("height"), 1, 10, 10),
            "sidebarMode": raw.get("sidebarMode") if raw.get("sidebarMode") in allowed_sidebar_modes else "artist-title",
            "roundCorners": clamp_int(raw.get("roundCorners"), 0, 24, 0),
            "albumGap": clamp_int(raw.get("albumGap"), 0, 100, 4),
            "font": raw.get("font") if raw.get("font") in allowed_fonts else "Arial",
            "coverOverlay": raw.get("coverOverlay") if raw.get("coverOverlay") in allowed_cover_overlays else "none",
        }

    raw = value if isinstance(value, dict) else {}
    has_device_profiles = isinstance(raw.get("desktop"), dict) or isinstance(raw.get("mobile"), dict)

    if has_device_profiles:
        desktop_settings = normalize_single_settings(raw.get("desktop") or raw.get("mobile") or {})
        mobile_settings = normalize_single_settings(raw.get("mobile") or raw.get("desktop") or {})
    else:
        desktop_settings = normalize_single_settings(raw)
        mobile_settings = normalize_single_settings(raw)

    return {
        "desktop": desktop_settings,
        "mobile": mobile_settings,
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
            session.permanent = True
            session["topster_admin"] = True
            return remember_topster_admin_device(redirect(next_url))
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
            <p>Only the host/admin computer can edit Grid, Ranked Grid, Draft Grid, and Checklist pages.</p>
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
    return forget_topster_admin_device(jsonify({"ok": True}))


@app.route("/api/topster-admin-status", methods=["GET"])
def topster_admin_status():
    return jsonify(
        {
            "ok": True,
            "authenticated": is_topster_admin(),
            "writable": is_topster_admin(),
            "passwordConfigured": topster_admin_password_is_configured(),
            "ipAllowed": is_admin_ip_allowed(),
            "rememberedDevice": bool(valid_topster_admin_device_id(request.cookies.get(TOPSTER_ADMIN_DEVICE_COOKIE_NAME))),
            "adminSessionDays": TOPSTER_ADMIN_SESSION_DAYS,
            "frontendOrigins": FRONTEND_ORIGINS,
            "topsterStorageBackend": get_topster_storage_backend_name(),
            "topsterRedisConfigured": topster_redis_is_configured(),
            "topsterRedisPackageInstalled": redis is not None,
            "topsterRedisClientError": TOPSTER_REDIS_CLIENT_ERROR,
        }
    )


@app.route("/api/topster-shared-store", methods=["GET", "PUT", "DELETE"])
def topster_shared_store():
    source_key = normalize_topster_store_key()
    storage_backend = get_topster_storage_backend_name()

    if request.method == "GET":
        try:
            settings = get_topster_settings(source_key)
            cover_cache = get_topster_cover_cache(source_key)
            source_text = get_topster_source_text(source_key)
        except RuntimeError as error:
            return jsonify(
                {
                    "ok": False,
                    "source": source_key,
                    "writable": is_topster_admin(),
                    "storageBackend": storage_backend,
                    "error": str(error),
                }
            ), 503

        return jsonify(
            {
                "ok": True,
                "source": source_key,
                "writable": is_topster_admin(),
                "storageBackend": storage_backend,
                "settings": settings,
                "coverCache": cover_cache,
                "sourceText": source_text.get("text", ""),
                "sourceSignature": source_text.get("signature", ""),
                "sourceName": source_text.get("sourceName", ""),
                "sourceUpdatedAt": source_text.get("updatedAt", ""),
            }
        )

    admin_error = require_topster_admin_response()
    if admin_error is not None:
        return admin_error

    if request.method == "DELETE":
        try:
            if topster_redis_is_configured():
                write_topster_redis_json("cover_cache", source_key, {})
                cover_cache = {}
            else:
                source_map = write_topster_source_map(TOPSTER_COVER_CACHE_FILE, source_key, {})
                cover_cache = source_map.get(source_key, {})

            settings = get_topster_settings(source_key)
            source_text = get_topster_source_text(source_key)
        except RuntimeError as error:
            return jsonify(
                {
                    "ok": False,
                    "source": source_key,
                    "writable": True,
                    "storageBackend": storage_backend,
                    "error": str(error),
                }
            ), 503

        return jsonify(
            {
                "ok": True,
                "source": source_key,
                "writable": True,
                "storageBackend": storage_backend,
                "settings": settings,
                "coverCache": cover_cache,
                "sourceText": source_text.get("text", ""),
                "sourceSignature": source_text.get("signature", ""),
                "sourceName": source_text.get("sourceName", ""),
                "sourceUpdatedAt": source_text.get("updatedAt", ""),
            }
        )

    payload = request.get_json(silent=True) or {}
    payload_source = payload.get("source")
    if payload_source is not None:
        normalized_payload_source = normalize_topster_store_key(payload_source)
        if normalized_payload_source != source_key:
            return jsonify(
                {
                    "ok": False,
                    "source": source_key,
                    "writable": True,
                    "storageBackend": storage_backend,
                    "error": (
                        f"Topster source mismatch: URL targets {source_key!r} "
                        f"but payload targets {normalized_payload_source!r}."
                    ),
                }
            ), 409

    try:
        settings = get_topster_settings(source_key)
        if isinstance(payload.get("settings"), dict):
            settings = normalize_topster_settings(payload["settings"])
            if source_key == "checklist":
                for profile_name in ("desktop", "mobile"):
                    profile = settings.get(profile_name)
                    if isinstance(profile, dict):
                        profile["coverOverlay"] = "none"
            if topster_redis_is_configured():
                write_topster_redis_json("settings", source_key, settings)
            else:
                write_topster_source_map(TOPSTER_SETTINGS_FILE, source_key, settings)

        cover_cache = get_topster_cover_cache(source_key)
        if isinstance(payload.get("coverCache"), dict):
            cover_cache = normalize_topster_cover_cache(payload["coverCache"])
            if topster_redis_is_configured():
                write_topster_redis_json("cover_cache", source_key, cover_cache)
            else:
                write_topster_source_map(TOPSTER_COVER_CACHE_FILE, source_key, cover_cache)

        source_text = get_topster_source_text(source_key)
        if isinstance(payload.get("sourceText"), str):
            source_text = normalize_topster_source_text(
                {
                    "text": payload.get("sourceText", ""),
                    "signature": payload.get("sourceSignature", ""),
                    "sourceName": payload.get(
                        "sourceName",
                        "checklist notepad file" if source_key == "checklist" else "draft notepad file",
                    ),
                    "updatedAt": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                }
            )
            if topster_redis_is_configured():
                write_topster_redis_json("source_text", source_key, source_text)
            else:
                write_topster_source_map(TOPSTER_SOURCE_TEXT_FILE, source_key, source_text)
    except RuntimeError as error:
        return jsonify(
            {
                "ok": False,
                "source": source_key,
                "writable": True,
                "storageBackend": storage_backend,
                "error": str(error),
            }
        ), 503

    return jsonify(
        {
            "ok": True,
            "source": source_key,
            "writable": True,
            "storageBackend": storage_backend,
            "settings": settings,
            "coverCache": cover_cache,
            "sourceText": source_text.get("text", ""),
            "sourceSignature": source_text.get("signature", ""),
            "sourceName": source_text.get("sourceName", ""),
            "sourceUpdatedAt": source_text.get("updatedAt", ""),
        }
    )


@app.route("/api/topster-storage-status", methods=["GET"])
def topster_storage_status():
    source_key = normalize_topster_store_key()
    storage_backend = get_topster_storage_backend_name()
    status: dict[str, Any] = {
        "ok": True,
        "source": source_key,
        "storageBackend": storage_backend,
        "redisConfigured": topster_redis_is_configured(),
        "redisPackageInstalled": redis is not None,
        "redisClientError": TOPSTER_REDIS_CLIENT_ERROR,
        "keys": {},
    }

    if topster_redis_is_configured():
        try:
            client = get_topster_redis_client()
            if client is None:
                raise RuntimeError(TOPSTER_REDIS_CLIENT_ERROR or "Redis is configured but unavailable.")
            for kind in ("settings", "cover_cache", "source_text"):
                key = topster_redis_key(kind, source_key)
                raw = client.get(key)
                status["keys"][kind] = {
                    "key": key,
                    "exists": raw is not None,
                    "bytes": len(raw.encode("utf-8")) if isinstance(raw, str) else 0,
                }
            client.ping()
        except Exception as error:
            status["ok"] = False
            status["error"] = str(error)
            return jsonify(status), 503

    return jsonify(status)


@app.route("/api/draft-grid-text", methods=["GET"])
def draft_grid_text():
    source_key = "draft"
    try:
        source_text = get_topster_source_text(source_key)
    except RuntimeError as error:
        return jsonify({"ok": False, "source": source_key, "error": str(error)}), 503

    text = source_text.get("text", "")
    if not text:
        return jsonify({"ok": False, "source": source_key, "error": "No draft Topster file has been published yet."}), 404

    return jsonify(
        {
            "ok": True,
            "source": source_text.get("sourceName") or "draft notepad file",
            "signature": source_text.get("signature") or hashlib.sha256(text.encode("utf-8", errors="ignore")).hexdigest()[:16],
            "updatedAt": source_text.get("updatedAt", ""),
            "text": text,
        }
    )


@app.route("/api/checklist-text", methods=["GET"])
def checklist_text():
    source_key = "checklist"
    try:
        source_text = get_topster_source_text(source_key)
    except RuntimeError as error:
        return jsonify({"ok": False, "source": source_key, "error": str(error)}), 503

    text = source_text.get("text", "")
    if not text:
        return jsonify({"ok": False, "source": source_key, "error": "No checklist file has been published yet."}), 404

    return jsonify(
        {
            "ok": True,
            "source": source_text.get("sourceName") or "checklist notepad file",
            "signature": source_text.get("signature") or hashlib.sha256(text.encode("utf-8", errors="ignore")).hexdigest()[:16],
            "updatedAt": source_text.get("updatedAt", ""),
            "text": text,
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


SPOTIFY_DEVICE_COOKIE_NAME = (
    os.getenv("SPOTIFY_DEVICE_COOKIE_NAME", "navincitron_spotify_device").strip()
    or "navincitron_spotify_device"
)
SPOTIFY_DEVICE_SESSION_SECONDS = SPOTIFY_DEVICE_SESSION_DAYS * 24 * 60 * 60
SPOTIFY_AUTH_REDIS_KEY_PREFIX = (
    os.getenv("SPOTIFY_AUTH_REDIS_KEY_PREFIX", "navincitron:spotify-auth").strip(":")
    or "navincitron:spotify-auth"
)
SPOTIFY_DEVICE_ID_PATTERN = re.compile(r"^[A-Za-z0-9_-]{32,160}$")


class SpotifyLoginRequired(RuntimeError):
    """The browser has no usable Spotify authorization grant."""


class SpotifyTokenRefreshTemporarilyUnavailable(RuntimeError):
    """The browser is still authorized, but token renewal temporarily failed."""


def valid_spotify_device_id(value: Any) -> str:
    candidate = str(value or "").strip()
    return candidate if SPOTIFY_DEVICE_ID_PATTERN.fullmatch(candidate) else ""


def get_spotify_device_id(create: bool = False) -> str:
    # The dedicated opaque cookie allows a browser to recover its server-side
    # token after a Render restart or after Flask's ordinary session cookie is
    # no longer available. It is intentionally not tied to an IP address.
    device_id = valid_spotify_device_id(request.cookies.get(SPOTIFY_DEVICE_COOKIE_NAME))
    if not device_id:
        device_id = valid_spotify_device_id(session.get("spotify_device_id"))

    if not device_id and create:
        device_id = secrets.token_urlsafe(36)

    if device_id:
        if not session.permanent:
            session.permanent = True
        if session.get("spotify_device_id") != device_id:
            session["spotify_device_id"] = device_id

    return device_id


def set_spotify_device_cookie(response: Any, device_id: str) -> Any:
    device_id = valid_spotify_device_id(device_id)
    if not device_id:
        return response

    response.set_cookie(
        SPOTIFY_DEVICE_COOKIE_NAME,
        device_id,
        max_age=SPOTIFY_DEVICE_SESSION_SECONDS,
        secure=USES_HTTPS_FRONTEND,
        httponly=True,
        samesite="None" if USES_HTTPS_FRONTEND else "Lax",
        path="/",
    )
    return response


def spotify_auth_redis_key(device_id: str) -> str:
    digest = hashlib.sha256(device_id.encode("utf-8", errors="ignore")).hexdigest()
    return f"{SPOTIFY_AUTH_REDIS_KEY_PREFIX}:{digest}"


def token_expiration_value(token_info: Any) -> int:
    if not isinstance(token_info, dict):
        return 0
    try:
        return int(token_info.get("expires_at") or 0)
    except Exception:
        return 0


def load_spotify_token_info() -> dict[str, Any] | None:
    candidates: list[dict[str, Any]] = []
    device_id = get_spotify_device_id(create=False)

    if device_id and topster_redis_is_configured():
        try:
            client = get_topster_redis_client()
            if client is not None:
                raw = client.get(spotify_auth_redis_key(device_id))
                if raw:
                    parsed = json.loads(raw)
                    if isinstance(parsed, dict) and parsed.get("access_token"):
                        candidates.append(parsed)
                        client.expire(spotify_auth_redis_key(device_id), SPOTIFY_DEVICE_SESSION_SECONDS)
        except Exception:
            # A temporary Redis outage must not log the browser out. The
            # permanent Flask-session copy below remains an availability fallback.
            pass

    session_token = session.get("spotify_token_info")
    if isinstance(session_token, dict) and session_token.get("access_token"):
        candidates.append(session_token)

    if not candidates:
        return None

    # Prefer the newest copy when both Redis and the signed session cookie exist.
    return max(candidates, key=token_expiration_value)


def save_spotify_token_info(token_info: dict[str, Any], device_id: str | None = None) -> None:
    if not isinstance(token_info, dict) or not token_info.get("access_token"):
        raise RuntimeError("Spotify returned an invalid token response.")

    if not session.permanent:
        session.permanent = True
    session["spotify_token_info"] = token_info
    device_id = valid_spotify_device_id(device_id) or get_spotify_device_id(create=True)

    if device_id and topster_redis_is_configured():
        try:
            client = get_topster_redis_client()
            if client is not None:
                client.setex(
                    spotify_auth_redis_key(device_id),
                    SPOTIFY_DEVICE_SESSION_SECONDS,
                    json.dumps(token_info, ensure_ascii=False),
                )
        except Exception:
            # The permanent signed-cookie copy remains usable when Redis is down.
            pass


def clear_spotify_token_info() -> None:
    device_id = get_spotify_device_id(create=False)
    session.pop("spotify_token_info", None)

    if device_id and topster_redis_is_configured():
        try:
            client = get_topster_redis_client()
            if client is not None:
                client.delete(spotify_auth_redis_key(device_id))
        except Exception:
            pass


def spotify_refresh_requires_login(error: Exception) -> bool:
    message = str(error or "").lower()
    permanent_markers = (
        "invalid_grant",
        "invalid refresh token",
        "refresh token expired",
        "refresh token has expired",
        "refresh token revoked",
        "refresh token was revoked",
    )
    return any(marker in message for marker in permanent_markers)


def get_session_token_info() -> dict[str, Any]:
    token_info = load_spotify_token_info()

    if not token_info:
        raise SpotifyLoginRequired("Not logged in with Spotify.")

    oauth = make_oauth()

    if oauth.is_token_expired(token_info):
        refresh_token = str(token_info.get("refresh_token") or "").strip()
        if not refresh_token:
            clear_spotify_token_info()
            raise SpotifyLoginRequired("Spotify authorization cannot be refreshed. Please log in again.")

        try:
            refreshed = oauth.refresh_access_token(refresh_token)
        except Exception as error:
            if spotify_refresh_requires_login(error):
                clear_spotify_token_info()
                raise SpotifyLoginRequired(
                    "Spotify authorization expired or was revoked. Please log in again."
                ) from error
            raise SpotifyTokenRefreshTemporarilyUnavailable(
                "Spotify token refresh is temporarily unavailable. The saved browser login was retained and will be retried automatically."
            ) from error

        if not isinstance(refreshed, dict) or not refreshed.get("access_token"):
            raise SpotifyTokenRefreshTemporarilyUnavailable(
                "Spotify returned an incomplete token refresh response. The saved browser login was retained and will be retried automatically."
            )

        # Spotify may omit a replacement refresh token. In that case the prior
        # refresh token remains the one the application must retain.
        if not refreshed.get("refresh_token"):
            refreshed["refresh_token"] = refresh_token

        token_info = refreshed
        save_spotify_token_info(token_info)

    return token_info


@app.route("/login")
def login():
    # Preserve the page that initiated OAuth so lyrics.html can reconnect without
    # changing the existing shuffle.html login behavior.
    session.permanent = True
    device_id = get_spotify_device_id(create=True)
    session["spotify_oauth_next"] = safe_frontend_redirect_url(
        request.args.get("next"),
        "/shuffle.html",
    )
    response = redirect(make_oauth().get_authorize_url())
    return set_spotify_device_cookie(response, device_id)


@app.route("/callback")
def callback():
    code = request.args.get("code")

    if not code:
        return "Spotify authorization failed: missing code.", 400

    device_id = get_spotify_device_id(create=True)
    token_info = make_oauth().get_access_token(code, as_dict=True)
    save_spotify_token_info(token_info, device_id=device_id)

    next_url = session.pop(
        "spotify_oauth_next",
        FRONTEND_ORIGIN.rstrip("/") + "/shuffle.html",
    )
    response = redirect(safe_frontend_redirect_url(next_url, "/shuffle.html"))
    return set_spotify_device_cookie(response, device_id)


@app.route("/api/auth-status")
def auth_status():
    try:
        get_session_token_info()
        return jsonify({"ok": True, "authenticated": True})
    except SpotifyTokenRefreshTemporarilyUnavailable as error:
        return jsonify(
            {
                "ok": True,
                "authenticated": True,
                "temporarilyUnavailable": True,
                "error": str(error),
            }
        )
    except SpotifyLoginRequired:
        return jsonify({"ok": True, "authenticated": False})
    except Exception as error:
        return jsonify(
            {
                "ok": False,
                "authenticated": True,
                "temporarilyUnavailable": True,
                "error": f"Could not verify Spotify authorization: {error}",
            }
        ), 503


sampler_process: subprocess.Popen[str] | None = None
sampler_lock = threading.Lock()
log_lines: deque[str] = deque(maxlen=300)
last_command: list[str] = []
current_cover_cache: dict[str, Any] = {"timestamp": 0.0, "data": None}
songguesser_games: dict[str, dict[str, Any]] = {}
SONGGUESSER_CLIP_SECONDS = 30
SONGGUESSER_ASSUMED_DURATION_SECONDS = 180
SONGGUESSER_LOCAL_SEEK_DELAY_SECONDS = 0.0
SONGGUESSER_SONG_COUNT = 5


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


# lyrics.html uses Spotify only to identify the user's current track. Genius
# metadata and the official Genius lyrics/annotation embed are resolved here so
# no Spotify or Genius credentials are exposed to browser JavaScript.
GENIUS_LOOKUP_CACHE: dict[str, dict[str, Any]] = {}
GENIUS_LOOKUP_CACHE_LOCK = threading.Lock()
GENIUS_LOOKUP_CACHE_MAX_ITEMS = 500
GENIUS_MATCH_TTL_SECONDS = 7 * 24 * 60 * 60
GENIUS_MISS_TTL_SECONDS = 60 * 60


def get_genius_access_token() -> str:
    # Genius's official API requires a Client Access Token. Accept a few common
    # environment-variable names so existing deployments can add the token
    # without changing code. The token must remain server-side.
    return normalize_secret_text(
        os.getenv("GENIUS_ACCESS_TOKEN")
        or os.getenv("GENIUS_CLIENT_ACCESS_TOKEN")
        or os.getenv("GENIUS_API_TOKEN")
        or ""
    )


def genius_json_request(url: str, access_token: str) -> dict[str, Any]:
    if not access_token:
        raise RuntimeError(
            "Genius API access token is not configured. Add GENIUS_ACCESS_TOKEN "
            "to the backend environment and redeploy."
        )

    headers = {
        "Accept": "application/json",
        "Authorization": f"Bearer {access_token}",
        "User-Agent": "NavincitronLyrics/1.1 (+https://www.navincitron.com)",
    }
    genius_request = Request(url, headers=headers)

    try:
        with urlopen(genius_request, timeout=12) as response:
            payload = json.loads(response.read().decode("utf-8", errors="replace"))
    except HTTPError as error:
        if error.code in {401, 403}:
            raise RuntimeError(
                f"Genius rejected the configured access token (HTTP {error.code}). "
                "Generate a Client Access Token in the Genius API Clients dashboard "
                "and update GENIUS_ACCESS_TOKEN."
            ) from error
        raise RuntimeError(f"Genius API request failed with HTTP {error.code}.") from error
    except URLError as error:
        raise RuntimeError(f"Could not reach the Genius API: {error.reason}") from error
    except json.JSONDecodeError as error:
        raise RuntimeError("Genius returned an unreadable JSON response.") from error

    if not isinstance(payload, dict):
        raise RuntimeError("Genius returned an invalid JSON response.")

    meta = payload.get("meta")
    if isinstance(meta, dict):
        status = int(meta.get("status") or 0)
        if status and status >= 400:
            message = str(meta.get("message") or "Genius API request failed.").strip()
            raise RuntimeError(f"Genius API error {status}: {message}")

    return payload


def genius_search_request(query: str) -> dict[str, Any]:
    access_token = get_genius_access_token()
    encoded_query = quote_plus(query)
    return genius_json_request(
        f"https://api.genius.com/search?q={encoded_query}",
        access_token,
    )


def genius_song_request(song_id: int) -> dict[str, Any]:
    access_token = get_genius_access_token()
    return genius_json_request(
        f"https://api.genius.com/songs/{song_id}?text_format=plain",
        access_token,
    )

def genius_song_hits(payload: dict[str, Any]) -> list[dict[str, Any]]:
    response = payload.get("response")
    if not isinstance(response, dict):
        return []

    hits: list[dict[str, Any]] = []

    direct_hits = response.get("hits")
    if isinstance(direct_hits, list):
        hits.extend(item for item in direct_hits if isinstance(item, dict))

    sections = response.get("sections")
    if isinstance(sections, list):
        for section in sections:
            if not isinstance(section, dict):
                continue
            section_type = str(section.get("type") or "").lower()
            if section_type and section_type not in {"song", "songs", "top_hit", "top hits"}:
                continue
            section_hits = section.get("hits")
            if isinstance(section_hits, list):
                hits.extend(item for item in section_hits if isinstance(item, dict))

    songs: list[dict[str, Any]] = []
    seen_ids: set[int] = set()

    for hit in hits:
        result = hit.get("result") if isinstance(hit.get("result"), dict) else hit
        if not isinstance(result, dict):
            continue
        try:
            song_id = int(result.get("id"))
        except (TypeError, ValueError):
            continue
        if song_id in seen_ids:
            continue
        seen_ids.add(song_id)
        songs.append(result)

    return songs


def normalize_lyrics_match_text(value: Any) -> str:
    text = unicodedata.normalize(
        "NFKD",
        str(value or "").casefold().replace("&", " and "),
    )
    text = "".join(character for character in text if not unicodedata.combining(character))
    text = re.sub(r"[’']", "", text)
    text = "".join(character if character.isalnum() else " " for character in text)
    return re.sub(r"\s+", " ", text).strip()


def clean_lyrics_track_title(value: Any) -> str:
    text = str(value or "").strip()
    if not text:
        return ""

    qualifier_words = (
        r"remaster(?:ed|ing)?|live|radio edit|single edit|album version|"
        r"mono|stereo|bonus track|deluxe|version|mix|edit|instrumental|karaoke"
    )
    text = re.sub(
        rf"\s*[\[(][^\])]*(?:{qualifier_words})[^\])]*[\])]\s*",
        " ",
        text,
        flags=re.IGNORECASE,
    )
    text = re.sub(
        rf"\s+-\s+[^-]*(?:{qualifier_words})[^-]*$",
        "",
        text,
        flags=re.IGNORECASE,
    )
    return re.sub(r"\s+", " ", text).strip(" -")


def lyrics_token_overlap(left: Any, right: Any) -> float:
    left_tokens = set(normalize_lyrics_match_text(left).split())
    right_tokens = set(normalize_lyrics_match_text(right).split())
    if not left_tokens or not right_tokens:
        return 0.0
    return len(left_tokens & right_tokens) / max(len(left_tokens), len(right_tokens))


def genius_result_artist_names(song: dict[str, Any]) -> list[str]:
    names: list[str] = []

    primary_artist = song.get("primary_artist")
    if isinstance(primary_artist, dict) and primary_artist.get("name"):
        names.append(str(primary_artist["name"]))

    for key in ("featured_artists", "artist_names"):
        value = song.get(key)
        if isinstance(value, str):
            names.append(value)
        elif isinstance(value, list):
            for artist in value:
                if isinstance(artist, dict) and artist.get("name"):
                    names.append(str(artist["name"]))
                elif isinstance(artist, str):
                    names.append(artist)

    return list(dict.fromkeys(name.strip() for name in names if name.strip()))


def score_genius_song_match(
    song: dict[str, Any],
    track_title: str,
    track_artists: list[str],
    album_name: str,
) -> float:
    candidate_title = str(song.get("title") or song.get("title_with_featured") or "")
    requested_title = normalize_lyrics_match_text(track_title)
    requested_clean_title = normalize_lyrics_match_text(clean_lyrics_track_title(track_title))
    candidate_title_norm = normalize_lyrics_match_text(candidate_title)
    candidate_clean_title = normalize_lyrics_match_text(clean_lyrics_track_title(candidate_title))

    score = 0.0
    if requested_title and candidate_title_norm == requested_title:
        score += 72.0
    elif requested_clean_title and candidate_clean_title == requested_clean_title:
        score += 65.0
    elif requested_clean_title and (
        requested_clean_title in candidate_clean_title
        or candidate_clean_title in requested_clean_title
    ):
        score += 48.0
    else:
        score += 45.0 * lyrics_token_overlap(requested_clean_title, candidate_clean_title)

    requested_artist_text = " ".join(track_artists)
    candidate_artists = genius_result_artist_names(song)
    candidate_artist_text = " ".join(candidate_artists)
    requested_artist_norm = normalize_lyrics_match_text(requested_artist_text)
    candidate_artist_norm = normalize_lyrics_match_text(candidate_artist_text)

    if requested_artist_norm and candidate_artist_norm == requested_artist_norm:
        score += 35.0
    elif requested_artist_norm and candidate_artist_norm and (
        requested_artist_norm in candidate_artist_norm
        or candidate_artist_norm in requested_artist_norm
    ):
        score += 28.0
    else:
        score += 28.0 * lyrics_token_overlap(requested_artist_text, candidate_artist_text)

    candidate_album = song.get("album")
    candidate_album_name = (
        str(candidate_album.get("name") or "")
        if isinstance(candidate_album, dict)
        else ""
    )
    if album_name and candidate_album_name:
        album_overlap = lyrics_token_overlap(album_name, candidate_album_name)
        if normalize_lyrics_match_text(album_name) == normalize_lyrics_match_text(candidate_album_name):
            score += 10.0
        else:
            score += 8.0 * album_overlap

    return score


def plain_text_from_genius_value(value: Any) -> str:
    if isinstance(value, str):
        # The API normally supplies plain text when text_format=plain. Strip tags
        # defensively if a deployment receives an HTML fallback instead.
        text = re.sub(r"<[^>]+>", " ", value)
        return re.sub(r"\s+", " ", text).strip()

    if isinstance(value, list):
        parts = [plain_text_from_genius_value(item) for item in value]
        return " ".join(part for part in parts if part).strip()

    if not isinstance(value, dict):
        return ""

    for key in ("plain", "markdown", "html"):
        if value.get(key):
            text = plain_text_from_genius_value(value.get(key))
            if text:
                return text

    if value.get("children"):
        text = plain_text_from_genius_value(value.get("children"))
        if text:
            return text

    return ""


def genius_song_description(song: dict[str, Any]) -> str:
    description = plain_text_from_genius_value(song.get("description"))
    if description:
        return description

    description_annotation = song.get("description_annotation")
    if isinstance(description_annotation, dict):
        body = plain_text_from_genius_value(description_annotation.get("body"))
        if body:
            return body

        annotations = description_annotation.get("annotations")
        if isinstance(annotations, list):
            for annotation in annotations:
                if not isinstance(annotation, dict):
                    continue
                body = plain_text_from_genius_value(annotation.get("body"))
                if body:
                    return body

    return ""



LASTFM_ART_CACHE: dict[str, dict[str, Any]] = {}
LASTFM_ART_CACHE_LOCK = threading.Lock()
LASTFM_ART_CACHE_MAX_ITEMS = 500
LASTFM_ART_MATCH_TTL_SECONDS = 30 * 24 * 60 * 60
LASTFM_ART_MISS_TTL_SECONDS = 6 * 60 * 60


def get_lyrics_lastfm_api_key() -> str:
    key = normalize_secret_text(
        os.getenv("LASTFM_API_KEY")
        or os.getenv("TOPSTER_LASTFM_API_KEY")
        or ""
    )
    if key:
        return key

    # sampler.py already carries the site's Last.fm key resolution logic. Reuse
    # it when available instead of maintaining a second key in app.py.
    sampler_key_getter = getattr(sampler_tools, "get_lastfm_api_key", None)
    if callable(sampler_key_getter):
        try:
            return normalize_secret_text(sampler_key_getter())
        except Exception:
            return ""

    return ""


def useful_lastfm_image_url(url: Any) -> str:
    value = str(url or "").strip()
    if not value:
        return ""
    # Last.fm's historical placeholder image is not useful as album art.
    if "2a96cbd8b46e442fc41c2b86b821562f" in value.lower():
        return ""
    return value


def best_lastfm_image_url(images: Any) -> str:
    if not isinstance(images, list):
        return ""

    preferred_sizes = ("mega", "extralarge", "large", "medium", "small")
    for preferred_size in preferred_sizes:
        for image in images:
            if not isinstance(image, dict):
                continue
            if str(image.get("size") or "").lower() != preferred_size:
                continue
            url = useful_lastfm_image_url(image.get("#text") or image.get("url"))
            if url:
                return url

    for image in reversed(images):
        if not isinstance(image, dict):
            continue
        url = useful_lastfm_image_url(image.get("#text") or image.get("url"))
        if url:
            return url

    return ""


def lastfm_json_request(params: dict[str, Any]) -> dict[str, Any]:
    api_key = get_lyrics_lastfm_api_key()
    if not api_key:
        raise RuntimeError(
            "Last.fm API key is not configured. Add LASTFM_API_KEY to the backend environment."
        )

    query = dict(params)
    query.update({"api_key": api_key, "format": "json", "autocorrect": "1"})
    url = "https://ws.audioscrobbler.com/2.0/?" + urlencode(query)
    lastfm_request = Request(
        url,
        headers={
            "Accept": "application/json",
            "User-Agent": "NavincitronLyrics/1.1 (+https://www.navincitron.com)",
        },
    )

    try:
        with urlopen(lastfm_request, timeout=10) as response:
            payload = json.loads(response.read().decode("utf-8", errors="replace"))
    except HTTPError as error:
        raise RuntimeError(f"Last.fm request failed with HTTP {error.code}.") from error
    except URLError as error:
        raise RuntimeError(f"Could not reach Last.fm: {error.reason}") from error
    except json.JSONDecodeError as error:
        raise RuntimeError("Last.fm returned an unreadable JSON response.") from error

    if not isinstance(payload, dict):
        raise RuntimeError("Last.fm returned an invalid JSON response.")
    if payload.get("error"):
        raise RuntimeError(
            f"Last.fm API error {payload.get('error')}: "
            f"{str(payload.get('message') or 'lookup failed').strip()}"
        )
    return payload


def lookup_lastfm_local_album_art(track: dict[str, Any]) -> dict[str, str] | None:
    if not bool(track.get("isLocal")):
        return None

    title = str(track.get("title") or "").strip()
    artists = [str(value).strip() for value in (track.get("artists") or []) if str(value).strip()]
    primary_artist = artists[0] if artists else str(track.get("artist") or "").strip()
    supplied_album = str(track.get("album") or "").strip()
    if supplied_album.lower() == "unknown album":
        supplied_album = ""

    if not title or not primary_artist or primary_artist.lower() == "unknown artist":
        return None

    cache_key = "::".join(
        [
            normalize_lyrics_match_text(primary_artist),
            normalize_lyrics_match_text(title),
            normalize_lyrics_match_text(supplied_album),
        ]
    )
    now = time.time()

    with LASTFM_ART_CACHE_LOCK:
        cached = LASTFM_ART_CACHE.get(cache_key)
        if isinstance(cached, dict):
            ttl = (
                LASTFM_ART_MATCH_TTL_SECONDS
                if cached.get("value")
                else LASTFM_ART_MISS_TTL_SECONDS
            )
            if now - float(cached.get("timestamp") or 0) < ttl:
                return cached.get("value")

    canonical_artist = primary_artist
    canonical_album = supplied_album
    cover_url = ""
    lastfm_url = ""

    # track.getInfo is the key step for local files: it identifies the canonical
    # release containing the artist/title pair, rather than blindly trusting an
    # incomplete or incorrect local-file album tag.
    try:
        track_payload = lastfm_json_request(
            {"method": "track.getInfo", "artist": primary_artist, "track": title}
        )
        track_info = track_payload.get("track")
        if isinstance(track_info, dict):
            album_info = track_info.get("album")
            if isinstance(album_info, dict):
                canonical_artist = str(album_info.get("artist") or canonical_artist).strip()
                canonical_album = str(
                    album_info.get("title") or album_info.get("name") or canonical_album
                ).strip()
                cover_url = best_lastfm_image_url(album_info.get("image"))
                lastfm_url = str(album_info.get("url") or "").strip()
    except Exception:
        # A supplied local album tag can still resolve through album.getInfo.
        pass

    # Fetch the full album record when track.getInfo found the album but omitted
    # usable artwork, or when Spotify's local URI supplied an album directly.
    if canonical_album and not cover_url:
        try:
            album_payload = lastfm_json_request(
                {
                    "method": "album.getInfo",
                    "artist": canonical_artist or primary_artist,
                    "album": canonical_album,
                }
            )
            album_info = album_payload.get("album")
            if isinstance(album_info, dict):
                canonical_artist = str(album_info.get("artist") or canonical_artist).strip()
                canonical_album = str(album_info.get("name") or canonical_album).strip()
                cover_url = best_lastfm_image_url(album_info.get("image"))
                lastfm_url = str(album_info.get("url") or lastfm_url).strip()
        except Exception:
            pass

    result = None
    if cover_url:
        result = {
            "coverUrl": cover_url,
            "album": canonical_album,
            "artist": canonical_artist,
            "lastfmUrl": lastfm_url,
            "source": "lastfm",
        }

    with LASTFM_ART_CACHE_LOCK:
        LASTFM_ART_CACHE[cache_key] = {"timestamp": now, "value": result}
        if len(LASTFM_ART_CACHE) > LASTFM_ART_CACHE_MAX_ITEMS:
            oldest_key = min(
                LASTFM_ART_CACHE,
                key=lambda key: float(LASTFM_ART_CACHE[key].get("timestamp") or 0),
            )
            LASTFM_ART_CACHE.pop(oldest_key, None)

    return result

def local_spotify_uri_metadata(uri: str) -> dict[str, str]:
    # Local Spotify URIs use spotify:local:artist:album:title:duration. Artist,
    # album, and title may be percent encoded.
    parts = str(uri or "").split(":")
    if len(parts) < 6 or parts[0:2] != ["spotify", "local"]:
        return {}

    return {
        "artist": unquote(parts[2]).replace("+", " ").strip(),
        "album": unquote(parts[3]).replace("+", " ").strip(),
        "title": unquote(parts[4]).replace("+", " ").strip(),
    }


def spotify_current_track_snapshot(playback: dict[str, Any] | None) -> dict[str, Any] | None:
    if not isinstance(playback, dict):
        return None

    item = playback.get("item")
    if not isinstance(item, dict) or item.get("type") not in {None, "track"}:
        return None

    uri = str(item.get("uri") or "")
    local_metadata = local_spotify_uri_metadata(uri)

    title = str(item.get("name") or local_metadata.get("title") or "").strip()
    artists = [
        str(artist.get("name") or "").strip()
        for artist in (item.get("artists") or [])
        if isinstance(artist, dict) and str(artist.get("name") or "").strip()
    ]
    if not artists and local_metadata.get("artist"):
        artists = [local_metadata["artist"]]

    album = item.get("album") if isinstance(item.get("album"), dict) else {}
    album_name = str(album.get("name") or local_metadata.get("album") or "").strip()
    album_images = album.get("images") if isinstance(album.get("images"), list) else []
    best_image = best_spotify_image(album_images)
    cover_url = str((best_image or {}).get("url") or "").strip()

    if not title:
        return None

    is_local = bool(item.get("is_local")) or uri.startswith("spotify:local:")
    external_urls = item.get("external_urls") if isinstance(item.get("external_urls"), dict) else {}
    spotify_url = "" if is_local else str(external_urls.get("spotify") or "").strip()

    track_key = str(item.get("id") or uri or "").strip()
    if not track_key:
        track_key = "local::" + "::".join(
            [
                normalize_lyrics_match_text(" ".join(artists)),
                normalize_lyrics_match_text(album_name),
                normalize_lyrics_match_text(title),
            ]
        )

    return {
        "key": track_key,
        "id": item.get("id"),
        "uri": uri,
        "title": title,
        "artists": artists,
        "artist": ", ".join(artists) or "Unknown artist",
        "album": album_name or "Unknown album",
        "coverUrl": cover_url,
        "artworkSource": "spotify" if cover_url else "",
        "spotifyUrl": spotify_url,
        "isLocal": is_local,
        "isPlaying": bool(playback.get("is_playing")),
        "progressMs": int(playback.get("progress_ms") or 0),
        "durationMs": int(item.get("duration_ms") or 0),
    }


def build_genius_song_payload(song: dict[str, Any]) -> dict[str, Any]:
    song_id = int(song["id"])
    primary_artist = song.get("primary_artist")
    artist_name = (
        str(primary_artist.get("name") or "").strip()
        if isinstance(primary_artist, dict)
        else ""
    )
    album = song.get("album")
    album_name = (
        str(album.get("name") or "").strip()
        if isinstance(album, dict)
        else ""
    )

    path = str(song.get("path") or "").strip()
    url = str(song.get("url") or "").strip()
    if not url and path:
        url = "https://genius.com" + path

    return {
        "id": song_id,
        "title": str(song.get("title") or song.get("title_with_featured") or "").strip(),
        "artist": artist_name,
        "album": album_name,
        "url": url,
        "thumbnailUrl": str(
            song.get("song_art_image_thumbnail_url")
            or song.get("header_image_thumbnail_url")
            or song.get("song_art_image_url")
            or ""
        ).strip(),
        "imageUrl": str(
            song.get("song_art_image_url")
            or song.get("header_image_url")
            or song.get("song_art_image_thumbnail_url")
            or ""
        ).strip(),
        "description": genius_song_description(song),
        "annotationCount": int(song.get("annotation_count") or 0),
        "embedScriptUrl": f"https://genius.com/songs/{song_id}/embed.js",
    }


def lookup_genius_song(track: dict[str, Any]) -> dict[str, Any] | None:
    cache_key = str(track.get("key") or "")
    now = time.time()

    with GENIUS_LOOKUP_CACHE_LOCK:
        cached = GENIUS_LOOKUP_CACHE.get(cache_key)
        if isinstance(cached, dict):
            ttl = GENIUS_MATCH_TTL_SECONDS if cached.get("value") else GENIUS_MISS_TTL_SECONDS
            if now - float(cached.get("timestamp") or 0) < ttl:
                return cached.get("value")

    title = str(track.get("title") or "").strip()
    artists = [str(value).strip() for value in (track.get("artists") or []) if str(value).strip()]
    album_name = str(track.get("album") or "").strip()
    primary_artist = artists[0] if artists else ""

    queries = [" ".join(part for part in (title, primary_artist) if part).strip()]
    cleaned_title = clean_lyrics_track_title(title)
    cleaned_query = " ".join(part for part in (cleaned_title, primary_artist) if part).strip()
    if cleaned_query and cleaned_query not in queries:
        queries.append(cleaned_query)

    candidates: dict[int, dict[str, Any]] = {}
    for query in queries[:2]:
        if not query:
            continue
        payload = genius_search_request(query)
        for song in genius_song_hits(payload):
            try:
                song_id = int(song.get("id"))
            except (TypeError, ValueError):
                continue
            candidates[song_id] = song
        if candidates:
            # A second query is useful only when the exact Spotify title did not
            # produce plausible candidates.
            best_now = max(
                score_genius_song_match(song, title, artists, album_name)
                for song in candidates.values()
            )
            if best_now >= 90:
                break

    best_song: dict[str, Any] | None = None
    best_score = 0.0
    for candidate in candidates.values():
        score = score_genius_song_match(candidate, title, artists, album_name)
        if score > best_score:
            best_score = score
            best_song = candidate

    result: dict[str, Any] | None = None
    if best_song is not None and best_score >= 48.0:
        try:
            details_payload = genius_song_request(int(best_song["id"]))
            response = details_payload.get("response")
            detailed_song = response.get("song") if isinstance(response, dict) else None
            if isinstance(detailed_song, dict):
                best_song = detailed_song
        except Exception:
            # Search results still provide the ID, URL, title, artist, and art,
            # so the official Genius embed remains usable if detail lookup fails.
            pass

        result = build_genius_song_payload(best_song)
        result["matchScore"] = round(best_score, 1)

    with GENIUS_LOOKUP_CACHE_LOCK:
        GENIUS_LOOKUP_CACHE[cache_key] = {"timestamp": now, "value": result}
        if len(GENIUS_LOOKUP_CACHE) > GENIUS_LOOKUP_CACHE_MAX_ITEMS:
            oldest_key = min(
                GENIUS_LOOKUP_CACHE,
                key=lambda key: float(GENIUS_LOOKUP_CACHE[key].get("timestamp") or 0),
            )
            GENIUS_LOOKUP_CACHE.pop(oldest_key, None)

    return result


@app.route("/api/lyrics/current", methods=["GET"])
def current_lyrics():
    try:
        spotify_client = get_spotify_client()
    except SpotifyLoginRequired as error:
        response = jsonify(
            {
                "ok": False,
                "authenticated": False,
                "error": str(error),
            }
        )
        response.status_code = 401
        response.headers["Cache-Control"] = "no-store"
        return response
    except SpotifyTokenRefreshTemporarilyUnavailable as error:
        response = jsonify(
            {
                "ok": False,
                "authenticated": True,
                "temporarilyUnavailable": True,
                "error": str(error),
            }
        )
        response.status_code = 503
        response.headers["Retry-After"] = "6"
        response.headers["Cache-Control"] = "no-store"
        return response

    try:
        try:
            playback = spotify_client.current_playback(additional_types="track")
        except TypeError:
            # Compatibility with older Spotipy builds whose current_playback()
            # method predates the additional_types keyword.
            playback = spotify_client.current_playback()
    except Exception as error:
        response = jsonify(
            {
                "ok": False,
                "authenticated": True,
                "error": f"Could not read Spotify playback: {error}",
            }
        )
        response.status_code = 502
        response.headers["Cache-Control"] = "no-store"
        return response

    track = spotify_current_track_snapshot(playback)
    if track is None:
        response = jsonify(
            {
                "ok": True,
                "authenticated": True,
                "playing": False,
                "track": None,
                "genius": None,
            }
        )
        response.headers["Cache-Control"] = "no-store"
        return response

    lastfm_art = None
    lastfm_error = ""
    if track.get("isLocal") and not track.get("coverUrl"):
        try:
            lastfm_art = lookup_lastfm_local_album_art(track)
        except Exception as error:
            lastfm_error = str(error)

        if lastfm_art:
            track["coverUrl"] = lastfm_art.get("coverUrl") or ""
            track["artworkSource"] = "lastfm"
            track["lastfmUrl"] = lastfm_art.get("lastfmUrl") or ""
            canonical_album = str(lastfm_art.get("album") or "").strip()
            if canonical_album and str(track.get("album") or "").strip().lower() in {"", "unknown album"}:
                track["album"] = canonical_album

    genius_song = None
    genius_error = ""
    genius_error_code = ""
    if not get_genius_access_token():
        genius_error_code = "not_configured"
        genius_error = (
            "Genius API access token is not configured. Add GENIUS_ACCESS_TOKEN "
            "to the backend environment and redeploy."
        )
    else:
        try:
            genius_song = lookup_genius_song(track)
        except Exception as error:
            genius_error = str(error)
            lowered_error = genius_error.lower()
            if "rejected the configured access token" in lowered_error:
                genius_error_code = "authentication_failed"
            else:
                genius_error_code = "lookup_failed"

    # Non-local tracks retain Spotify's exact album art. Local tracks deliberately
    # use Last.fm only for album-art recovery so Genius matching cannot substitute
    # unrelated song-page artwork.

    response = jsonify(
        {
            "ok": True,
            "authenticated": True,
            "playing": True,
            "track": track,
            "genius": genius_song,
            "geniusConfigured": bool(get_genius_access_token()),
            "geniusError": genius_error,
            "geniusErrorCode": genius_error_code,
            "lastfmArt": lastfm_art,
            "lastfmError": lastfm_error,
        }
    )
    response.headers["Cache-Control"] = "no-store"
    return response


@app.route("/api/lyrics/control/<action>", methods=["POST"])
def lyrics_playback_control(action: str):
    action = str(action or "").strip().lower()
    allowed_actions = {"previous", "pause", "play", "next"}
    if action not in allowed_actions:
        return jsonify(
            {
                "ok": False,
                "authenticated": True,
                "error": "Unsupported Spotify playback control.",
            }
        ), 400

    try:
        spotify_client = get_spotify_client()
    except SpotifyLoginRequired as error:
        response = jsonify(
            {
                "ok": False,
                "authenticated": False,
                "error": str(error),
            }
        )
        response.status_code = 401
        response.headers["Cache-Control"] = "no-store"
        return response
    except SpotifyTokenRefreshTemporarilyUnavailable as error:
        response = jsonify(
            {
                "ok": False,
                "authenticated": True,
                "temporarilyUnavailable": True,
                "error": str(error),
            }
        )
        response.status_code = 503
        response.headers["Retry-After"] = "6"
        response.headers["Cache-Control"] = "no-store"
        return response

    sampler_running = process_is_running()

    try:
        if action == "pause":
            if sampler_running:
                write_sampler_control("pause", paused=True)
            spotify_client.pause_playback()
            message = "Spotify playback paused."

        elif action == "play":
            if sampler_running:
                write_sampler_control("resume", paused=False)
            spotify_client.start_playback()
            message = "Spotify playback resumed."

        elif action == "next":
            if sampler_running:
                # Keep sampler.py's current clip timer and history synchronized
                # with transport changes initiated from lyrics.html.
                write_sampler_control("next", paused=False)
                append_log("[lyrics page requested: next track]")
                message = "Next track requested from the sampler."
            else:
                spotify_client.next_track()
                message = "Skipped to the next Spotify track."

        else:  # previous
            if sampler_running:
                write_sampler_control("previous", paused=False)
                append_log("[lyrics page requested: previous track]")
                message = "Previous track requested from the sampler."
            else:
                spotify_client.previous_track()
                message = "Returned to the previous Spotify track."

    except Exception as error:
        response = jsonify(
            {
                "ok": False,
                "authenticated": True,
                "error": f"Could not control Spotify playback: {error}",
            }
        )
        response.status_code = 502
        response.headers["Cache-Control"] = "no-store"
        return response

    response = jsonify(
        {
            "ok": True,
            "authenticated": True,
            "action": action,
            "samplerRunning": sampler_running,
            "message": message,
        }
    )
    response.headers["Cache-Control"] = "no-store"
    return response


def pause_spotify() -> None:
    try:
        sp = get_spotify_client()
        sp.pause_playback()
        append_log("[Spotify playback paused]")
    except Exception as error:
        append_log(f"[warning: could not pause Spotify playback: {error}]")


def read_sampler_control_file() -> dict[str, Any]:
    if not CONTROL_FILE.exists():
        return {"seq": 0, "paused": False, "command": None}

    try:
        data = json.loads(CONTROL_FILE.read_text(encoding="utf-8"))
        return data if isinstance(data, dict) else {"seq": 0, "paused": False, "command": None}
    except Exception:
        return {"seq": 0, "paused": False, "command": None}


def write_sampler_control(command: str | None, paused: bool | None = None) -> dict[str, Any]:
    UPLOAD_DIR.mkdir(parents=True, exist_ok=True)
    current = read_sampler_control_file()
    state = {
        "seq": int(current.get("seq") or 0) + 1,
        "command": command,
        "paused": bool(current.get("paused", False)) if paused is None else bool(paused),
        "updatedAt": time.time(),
    }

    temp_path = CONTROL_FILE.with_suffix(CONTROL_FILE.suffix + ".tmp")
    temp_path.write_text(json.dumps(state, indent=2), encoding="utf-8")
    temp_path.replace(CONTROL_FILE)
    return state


def reset_sampler_control() -> None:
    state = {"seq": 0, "command": None, "paused": False, "updatedAt": time.time()}
    temp_path = CONTROL_FILE.with_suffix(CONTROL_FILE.suffix + ".tmp")
    temp_path.write_text(json.dumps(state, indent=2), encoding="utf-8")
    temp_path.replace(CONTROL_FILE)


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


def configure_sampler_tools() -> None:
    if sampler_tools is None:
        raise RuntimeError("sampler.py could not be imported by app.py.")

    sampler_tools.CACHE_FILE = str(BASE_DIR / "album_cache.json")
    sampler_tools.STATE_FILE = str(STATE_FILE)


def songguesser_release_year_from_text(value: Any) -> str:
    text = str(value or "").strip()
    if len(text) >= 4 and text[:4].isdigit():
        return text[:4]
    return ""


def songguesser_release_decade_from_year(year: str) -> str:
    if len(year) == 4 and year.isdigit():
        return f"{year[:3]}0s"
    return ""


def songguesser_track_answer(prepared: dict[str, Any]) -> dict[str, Any]:
    configure_sampler_tools()

    track = prepared.get("track") or {}
    album = track.get("album") if isinstance(track.get("album"), dict) else {}

    artist = sampler_tools.format_track_artist(track)
    song = sampler_tools.format_track_name(track)
    album_name = album.get("name") or prepared.get("album_name") or "Unknown album"
    cover_url = sampler_tools.prepared_cover_url(prepared)
    release_year = songguesser_release_year_from_text(album.get("release_date") or prepared.get("release_date"))
    release_decade = songguesser_release_decade_from_year(release_year)

    return {
        "artist": artist,
        "album": album_name,
        "song": song,
        "releaseYear": release_year,
        "releaseDecade": release_decade,
        "coverUrl": cover_url,
    }


def songguesser_candidate_from_album_track(album: dict[str, Any], track: dict[str, Any]) -> dict[str, Any]:
    configure_sampler_tools()

    prepared = sampler_tools.prepare_album_track_clip(
        album=album,
        track=track,
        clip_seconds=SONGGUESSER_CLIP_SECONDS,
        random_start=True,
        assumed_duration_seconds=SONGGUESSER_ASSUMED_DURATION_SECONDS,
    )
    prepared["release_date"] = album.get("release_date")

    return {"prepared": prepared, "answer": songguesser_track_answer(prepared)}


def songguesser_candidate_from_playlist_item(playlist_bundle: dict[str, Any], item: dict[str, Any]) -> dict[str, Any]:
    configure_sampler_tools()

    prepared = sampler_tools.prepare_playlist_item_clip(
        playlist_bundle=playlist_bundle,
        item=item,
        clip_seconds=SONGGUESSER_CLIP_SECONDS,
        random_start=True,
        assumed_duration_seconds=SONGGUESSER_ASSUMED_DURATION_SECONDS,
    )

    return {"prepared": prepared, "answer": songguesser_track_answer(prepared)}



def songguesser_answer_has_unknown_album(answer: dict[str, Any]) -> bool:
    album = str(answer.get("album") or "").strip().lower()
    return not album or album in {"unknown album", "none", "null"}


def songguesser_should_lookup_answer(answer: dict[str, Any], hints_enabled: dict[str, Any]) -> bool:
    if not any(hints_enabled.get(key) for key in ("releaseYear", "releaseDecade", "album")):
        return False

    if songguesser_answer_has_unknown_album(answer):
        return True

    if (hints_enabled.get("releaseYear") or hints_enabled.get("releaseDecade")) and not answer.get("releaseYear"):
        return True

    return False


def songguesser_search_track_metadata(sp: Any, answer: dict[str, Any]) -> dict[str, Any] | None:
    """
    Uses Spotify Search as the music metadata source for local-file entries or
    entries with missing album/release metadata.

    This avoids adding another third-party API key and is only used when the user
    enabled a hint that needs album/year/decade data.
    """

    artist = str(answer.get("artist") or "").strip()
    song = str(answer.get("song") or "").strip()

    if not song or song.lower() == "unknown track":
        return None

    queries = []
    if artist and artist.lower() != "unknown artist":
        queries.extend(
            [
                f'track:"{song}" artist:"{artist}"',
                f'{song} {artist}',
            ]
        )
    queries.append(song)

    for query in queries:
        try:
            results = sp.search(q=query, type="track", limit=5)
        except Exception as error:
            append_log(f"[songguesser warning: metadata lookup failed for {song!r}: {error}]")
            return None

        tracks = (results.get("tracks") or {}).get("items") or []
        if not tracks:
            continue

        # Prefer a track whose artist token appears in the requested local artist
        # when that information exists.
        selected = tracks[0]
        if artist and artist.lower() != "unknown artist":
            artist_norm = artist.lower()
            for track in tracks:
                spotify_artists = " ".join(
                    item.get("name", "") for item in track.get("artists", []) if isinstance(item, dict)
                ).lower()
                if any(token and token in spotify_artists for token in re.split(r"[\s,&+]+", artist_norm)):
                    selected = track
                    break

        album = selected.get("album") if isinstance(selected.get("album"), dict) else {}
        if not album:
            continue

        images = album.get("images") or []
        release_year = songguesser_release_year_from_text(album.get("release_date"))
        release_decade = songguesser_release_decade_from_year(release_year)

        return {
            "artist": ", ".join(
                item.get("name", "")
                for item in selected.get("artists", [])
                if isinstance(item, dict) and item.get("name")
            ) or answer.get("artist"),
            "album": album.get("name") or answer.get("album"),
            "song": selected.get("name") or answer.get("song"),
            "releaseYear": release_year or answer.get("releaseYear") or "",
            "releaseDecade": release_decade or answer.get("releaseDecade") or "",
            "coverUrl": (sampler_tools.best_image_url(images) if sampler_tools is not None else None)
                or answer.get("coverUrl"),
        }

    return None


def songguesser_enrich_queue_answers(sp: Any, queue: list[dict[str, Any]], hints_enabled: dict[str, Any]) -> None:
    for candidate in queue:
        answer = candidate.get("answer")
        if not isinstance(answer, dict):
            continue

        if not songguesser_should_lookup_answer(answer, hints_enabled):
            continue

        looked_up = songguesser_search_track_metadata(sp, answer)
        if not looked_up:
            continue

        for key in ("artist", "album", "song", "releaseYear", "releaseDecade", "coverUrl"):
            value = looked_up.get(key)
            if value and (key not in answer or not answer.get(key) or (key == "album" and songguesser_answer_has_unknown_album(answer))):
                answer[key] = value


def songguesser_summary_payload(game: dict[str, Any]) -> list[dict[str, Any]]:
    summary = []

    for index, candidate in enumerate(game.get("queue") or [], start=1):
        answer = candidate.get("answer") or {}
        summary.append(
            {
                "index": index,
                "artist": answer.get("artist") or "Unknown artist",
                "song": answer.get("song") or "Unknown song",
                "album": answer.get("album") or "Unknown album",
                "coverUrl": answer.get("coverUrl"),
            }
        )

    return summary



def songguesser_build_album_candidates(
    sp: Any,
    cache: dict[str, Any],
    album_line: str,
    used_by_source: dict[str, set[str]],
    maximum: int,
) -> list[dict[str, Any]]:
    configure_sampler_tools()

    album = sampler_tools.resolve_album(sp, album_line, cache)
    tracks = sampler_tools.get_album_tracks_cached(sp, album, cache)
    playable_tracks = sampler_tools.get_unique_playable_album_tracks(
        tracks=tracks,
        required_clip_seconds=SONGGUESSER_CLIP_SECONDS,
    )
    random.shuffle(playable_tracks)

    source_key = f"album::{album.get('id') or album_line}"
    used_keys = used_by_source.setdefault(source_key, set())
    candidates: list[dict[str, Any]] = []

    for track in playable_tracks:
        track_key = sampler_tools.track_dedupe_key(track)
        if track_key in used_keys:
            continue
        used_keys.add(track_key)
        candidates.append(songguesser_candidate_from_album_track(album, track))
        if len(candidates) >= maximum:
            break

    return candidates


def songguesser_build_playlist_candidates(
    sp: Any,
    cache: dict[str, Any],
    playlist_link: str,
    used_by_source: dict[str, set[str]],
    maximum: int,
) -> list[dict[str, Any]]:
    configure_sampler_tools()

    playlist_id = sampler_tools.extract_spotify_playlist_id(playlist_link)
    if not playlist_id:
        raise RuntimeError("Invalid Spotify playlist link or URI.")

    playlist_bundle = sampler_tools.get_playlist_bundle_cached(sp, playlist_id, cache)
    playlist_items = sampler_tools.get_unique_playable_playlist_items(
        playlist_items=playlist_bundle.get("items") or [],
        required_clip_seconds=SONGGUESSER_CLIP_SECONDS,
    )
    random.shuffle(playlist_items)

    source_key = f"playlist::{playlist_id}"
    used_keys = used_by_source.setdefault(source_key, set())
    candidates: list[dict[str, Any]] = []

    for item in playlist_items:
        item_key = sampler_tools.playlist_item_dedupe_key(item)
        if item_key in used_keys:
            continue
        used_keys.add(item_key)
        candidates.append(songguesser_candidate_from_playlist_item(playlist_bundle, item))
        if len(candidates) >= maximum:
            break

    return candidates


def songguesser_build_candidates_from_file(sp: Any, cache: dict[str, Any], albums_file: Path) -> list[dict[str, Any]]:
    configure_sampler_tools()

    lines = sampler_tools.load_album_lines(str(albums_file))
    if not lines:
        raise RuntimeError("No album or playlist links were found in the uploaded text file.")

    used_by_source: dict[str, set[str]] = {}
    candidates: list[dict[str, Any]] = []

    # Multiple passes allow a short file to contribute more than one unique song
    # from the same album/playlist while still preventing repeats from that source.
    for _pass_index in range(max(1, SONGGUESSER_SONG_COUNT)):
        shuffled_lines = lines[:]
        random.shuffle(shuffled_lines)
        progress_before = len(candidates)

        for line in shuffled_lines:
            remaining = SONGGUESSER_SONG_COUNT - len(candidates)
            if remaining <= 0:
                break

            try:
                if sampler_tools.extract_spotify_playlist_id(line):
                    candidates.extend(songguesser_build_playlist_candidates(sp, cache, line, used_by_source, 1))
                else:
                    candidates.extend(songguesser_build_album_candidates(sp, cache, line, used_by_source, 1))
            except Exception as error:
                append_log(f"[songguesser warning: skipped source {line!r}: {error}]")

        if len(candidates) >= SONGGUESSER_SONG_COUNT:
            break
        if len(candidates) == progress_before:
            break

    if len(candidates) < SONGGUESSER_SONG_COUNT:
        raise RuntimeError(
            f"Songguesser requires five playable unique songs, but only found {len(candidates)} in the uploaded text file."
        )

    return candidates[:SONGGUESSER_SONG_COUNT]


def songguesser_build_candidates_from_single_link(sp: Any, cache: dict[str, Any], link: str) -> list[dict[str, Any]]:
    configure_sampler_tools()

    used_by_source: dict[str, set[str]] = {}

    if sampler_tools.extract_spotify_album_id(link):
        candidates = songguesser_build_album_candidates(
            sp=sp,
            cache=cache,
            album_line=link,
            used_by_source=used_by_source,
            maximum=SONGGUESSER_SONG_COUNT,
        )
    elif sampler_tools.extract_spotify_playlist_id(link):
        candidates = songguesser_build_playlist_candidates(
            sp=sp,
            cache=cache,
            playlist_link=link,
            used_by_source=used_by_source,
            maximum=SONGGUESSER_SONG_COUNT,
        )
    else:
        raise RuntimeError("Invalid Spotify album or playlist link/URI.")

    if len(candidates) < SONGGUESSER_SONG_COUNT:
        raise RuntimeError(
            f"Songguesser requires five playable unique songs, but only found {len(candidates)} in that album/playlist."
        )

    return candidates[:SONGGUESSER_SONG_COUNT]


def songguesser_public_payload(game: dict[str, Any], candidate: dict[str, Any], position_ms: int) -> dict[str, Any]:
    answer = candidate.get("answer") or {}
    hints_enabled = game.get("hints") or {}
    release_year = answer.get("releaseYear") or ""
    release_decade = answer.get("releaseDecade") or ""

    hints = {
        "releaseYear": release_year if hints_enabled.get("releaseYear") and release_year else None,
        "releaseDecade": release_decade if hints_enabled.get("releaseDecade") and release_decade else None,
        "artist": answer.get("artist") if hints_enabled.get("artist") else None,
        "album": answer.get("album") if hints_enabled.get("album") else None,
    }

    now = time.time()
    return {
        "ok": True,
        "complete": False,
        "progress": int(game.get("current_index", 0)) + 1,
        "total": len(game.get("queue") or []),
        "clipSeconds": SONGGUESSER_CLIP_SECONDS,
        "positionMs": position_ms,
        "startedAt": now,
        "endsAt": now + SONGGUESSER_CLIP_SECONDS,
        "answer": answer,
        "hints": hints,
    }


def songguesser_start_current(game: dict[str, Any]) -> dict[str, Any]:
    configure_sampler_tools()

    queue = game.get("queue") or []
    current_index = int(game.get("current_index", 0))

    if current_index >= len(queue):
        return {
            "ok": True,
            "complete": True,
            "message": "Songguesser complete.",
            "summary": songguesser_summary_payload(game),
        }

    sp = get_spotify_client()
    device_id = sampler_tools.get_device_id(sp, None)
    candidate = queue[current_index]
    prepared = candidate["prepared"]
    position_ms = sampler_tools.start_prepared_clip(
        sp=sp,
        device_id=device_id,
        prepared=prepared,
        local_seek_delay_seconds=SONGGUESSER_LOCAL_SEEK_DELAY_SECONDS,
    )

    # Public playlists owned by other users can be playable but not item-readable
    # through the Web API. sampler.py discovers the actual current track after
    # playback starts; refresh the Songguesser answer from that discovered track.
    candidate["answer"] = songguesser_track_answer(prepared)
    try:
        songguesser_enrich_queue_answers(
            sp=sp,
            queue=[candidate],
            hints_enabled=game.get("hints") or {},
            prefer_grid=False,
        )
    except Exception as error:
        append_log(f"[songguesser warning: could not enrich discovered public playlist track: {error}]")

    game["started_at"] = time.time()
    game["position_ms"] = position_ms
    return songguesser_public_payload(game, candidate, position_ms)


def get_current_songguesser_game() -> dict[str, Any] | None:
    game_id = session.get("songguesser_game_id")
    if not game_id:
        return None
    return songguesser_games.get(game_id)


@app.route("/api/songguesser/start", methods=["POST"])
def songguesser_start():
    with sampler_lock:
        if process_is_running():
            return jsonify({"ok": False, "error": "Stop the regular sampler before starting Songguesser."}), 409

        is_form_request = bool(request.form or request.files)
        data = request.form if is_form_request else (request.get_json(silent=True) or {})
        source_mode = str(data.get("sourceMode", "file")).strip().lower()
        if source_mode not in {"file", "playlist"}:
            return jsonify({"ok": False, "error": "Invalid source mode."}), 400

        hints = {
            "releaseYear": form_bool(data.get("hintReleaseYear"), False),
            "releaseDecade": form_bool(data.get("hintReleaseDecade"), False),
            "artist": form_bool(data.get("hintArtist"), False),
            "album": form_bool(data.get("hintAlbum"), False),
        }

        try:
            sp = get_spotify_client()
        except RuntimeError:
            return jsonify({"ok": False, "error": "Press Login with Spotify before starting Songguesser."}), 401
        except Exception as error:
            return jsonify({"ok": False, "error": f"Could not connect to Spotify: {error}"}), 500

        configure_sampler_tools()
        cache = sampler_tools.load_cache()

        try:
            if source_mode == "playlist":
                link = str(data.get("playlistLink", "")).strip()
                if not link:
                    return jsonify({"ok": False, "error": "Enter a Spotify album or playlist link first."}), 400
                queue = songguesser_build_candidates_from_single_link(sp, cache, link)
            else:
                uploaded_albums_file = save_uploaded_albums_file()
                if uploaded_albums_file is None:
                    return jsonify({"ok": False, "error": "Upload a .txt file containing album or playlist links."}), 400
                queue = songguesser_build_candidates_from_file(sp, cache, uploaded_albums_file)
        except Exception as error:
            return jsonify({"ok": False, "error": str(error)}), 400

        songguesser_enrich_queue_answers(sp, queue, hints)

        random.shuffle(queue)
        game_id = secrets.token_urlsafe(16)
        game = {
            "id": game_id,
            "queue": queue[:SONGGUESSER_SONG_COUNT],
            "current_index": 0,
            "hints": hints,
            "created_at": time.time(),
        }
        songguesser_games[game_id] = game
        session["songguesser_game_id"] = game_id
        append_log("[starting Songguesser]")

        try:
            return jsonify(songguesser_start_current(game))
        except Exception as error:
            songguesser_games.pop(game_id, None)
            session.pop("songguesser_game_id", None)
            return jsonify({"ok": False, "error": str(error)}), 500


@app.route("/api/songguesser/next", methods=["POST"])
def songguesser_next():
    game = get_current_songguesser_game()
    if game is None:
        return jsonify({"ok": False, "error": "No active Songguesser game."}), 404

    game["current_index"] = int(game.get("current_index", 0)) + 1
    if game["current_index"] >= len(game.get("queue") or []):
        summary = songguesser_summary_payload(game)
        songguesser_games.pop(game.get("id"), None)
        session.pop("songguesser_game_id", None)
        try:
            pause_spotify()
        except Exception:
            pass
        return jsonify({
            "ok": True,
            "complete": True,
            "message": "Songguesser complete.",
            "summary": summary,
        })

    try:
        return jsonify(songguesser_start_current(game))
    except Exception as error:
        return jsonify({"ok": False, "error": str(error)}), 500


@app.route("/api/songguesser/stop", methods=["POST"])
def songguesser_stop():
    game = get_current_songguesser_game()
    if game is not None:
        songguesser_games.pop(game.get("id"), None)
    session.pop("songguesser_game_id", None)
    pause_spotify()
    return jsonify({"ok": True})


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
            "--control-file",
            str(CONTROL_FILE),
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

        reset_sampler_control()
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



@app.route("/api/control/pause", methods=["POST"])
def sampler_control_pause():
    if not process_is_running():
        return jsonify({"ok": False, "error": "sampler.py is not running."}), 409

    write_sampler_control("pause", paused=True)
    pause_spotify()
    return jsonify({"ok": True, "running": process_is_running(), "samplerControl": read_sampler_control_file()})


@app.route("/api/control/play", methods=["POST"])
def sampler_control_play():
    if not process_is_running():
        return jsonify({"ok": False, "error": "sampler.py is not running."}), 409

    write_sampler_control("resume", paused=False)

    try:
        sp = get_spotify_client()
        sp.start_playback()
        append_log("[Spotify playback resumed]")
    except Exception as error:
        append_log(f"[warning: could not resume Spotify playback directly: {error}]")

    return jsonify({"ok": True, "running": process_is_running(), "samplerControl": read_sampler_control_file()})


@app.route("/api/control/next", methods=["POST"])
def sampler_control_next():
    if not process_is_running():
        return jsonify({"ok": False, "error": "sampler.py is not running."}), 409

    write_sampler_control("next", paused=False)
    append_log("[sampler control requested: next track]")
    return jsonify({"ok": True, "running": process_is_running(), "samplerControl": read_sampler_control_file()})


@app.route("/api/control/previous", methods=["POST"])
def sampler_control_previous():
    if not process_is_running():
        return jsonify({"ok": False, "error": "sampler.py is not running."}), 409

    write_sampler_control("previous", paused=False)
    append_log("[sampler control requested: previous track]")
    return jsonify({"ok": True, "running": process_is_running(), "samplerControl": read_sampler_control_file()})


@app.route("/api/stop", methods=["POST"])
def stop_sampler():
    global sampler_process

    game = get_current_songguesser_game()
    if game is not None:
        songguesser_games.pop(game.get("id"), None)
    session.pop("songguesser_game_id", None)

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

        write_sampler_control("stop", paused=False)
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
            "samplerControl": read_sampler_control_file(),
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
    protected_topster_pages = {"grid.html", "ranked_grid.html", "draft_grid.html", "draft_checklist.html"}

    if filename in protected_topster_pages and not is_topster_admin():
        if topster_admin_password_is_configured():
            return redirect("/topster-admin-login")
        return "Topster editor access is restricted to the host computer.", 403

    target = BASE_DIR / filename
    if target.is_file():
        return send_from_directory(BASE_DIR, filename)
    return send_from_directory(BASE_DIR, "index.html")


if __name__ == "__main__":
    app.run(host="127.0.0.1", port=5000, debug=True)
