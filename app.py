from __future__ import annotations

import base64
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
from concurrent.futures import ThreadPoolExecutor
from functools import lru_cache
from html import escape as html_escape, unescape as html_unescape
from html.parser import HTMLParser
from collections import deque
from datetime import timedelta
from pathlib import Path
from typing import Any
from urllib.error import HTTPError, URLError
from urllib.parse import quote, quote_plus, unquote, urlencode, urlparse
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
TOPSTER_DISCOGS_OWNERSHIP_OVERRIDES_FILE = BASE_DIR / "topster_discogs_ownership_overrides.json"
TOPSTER_DISCOGS_OWNERSHIP_OVERRIDES_LOCK = threading.Lock()
LYRICS_GENIUS_ALBUM_LINKS_FILE = BASE_DIR / "lyrics_genius_album_links.json"
LYRICS_GENIUS_ALBUM_LINKS_LOCK = threading.Lock()
LYRICS_GENIUS_ALBUM_LINK_MEMORY_CACHE: dict[str, dict[str, Any] | None] = {}
LYRICS_DISCOGS_COVER_OVERRIDES_FILE = BASE_DIR / "lyrics_discogs_cover_overrides.json"
LYRICS_MY_ALBUMS_FILE = BASE_DIR / "my_albums.txt"
LYRICS_GITHUB_REPOSITORY = (os.getenv("LYRICS_GITHUB_REPOSITORY") or os.getenv("GITHUB_REPOSITORY") or "").strip()
LYRICS_GITHUB_BRANCH = (os.getenv("LYRICS_GITHUB_BRANCH") or "main").strip() or "main"
LYRICS_GITHUB_MY_ALBUMS_PATH = (os.getenv("LYRICS_GITHUB_MY_ALBUMS_PATH") or "my_albums.txt").strip().lstrip("/") or "my_albums.txt"
TOPSTER_REDIS_KEY_PREFIX = os.getenv("TOPSTER_REDIS_KEY_PREFIX", "navincitron:topster").strip() or "navincitron:topster"
TOPSTER_REDIS_CLIENT: Any | None = None
TOPSTER_REDIS_CLIENT_ERROR = ""
DISCOGS_COLLECTION_USERNAME = (os.getenv("DISCOGS_COLLECTION_USERNAME", "NNavincitron").strip() or "NNavincitron")
DISCOGS_COLLECTION_MEMORY_CACHE: dict[str, Any] = {}
DISCOGS_RELEASE_MEMORY_CACHE: dict[int, dict[str, Any]] = {}
try:
    DISCOGS_COLLECTION_CACHE_SECONDS = max(60, int(os.getenv("DISCOGS_COLLECTION_CACHE_SECONDS", "604800") or 604800))
except (TypeError, ValueError):
    DISCOGS_COLLECTION_CACHE_SECONDS = 604800
try:
    DISCOGS_RELEASE_CACHE_SECONDS = max(60, int(os.getenv("DISCOGS_RELEASE_CACHE_SECONDS", str(DISCOGS_COLLECTION_CACHE_SECONDS)) or DISCOGS_COLLECTION_CACHE_SECONDS))
except (TypeError, ValueError):
    DISCOGS_RELEASE_CACHE_SECONDS = DISCOGS_COLLECTION_CACHE_SECONDS

# Increment this whenever the collection payload/matching contract changes. The
# version is part of the Redis key, so a deploy cannot silently keep serving a
# week-old collection snapshot produced by an older matcher revision.
DISCOGS_COLLECTION_CACHE_VERSION = 12
DISCOGS_RELEASE_CACHE_VERSION = 2


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

TOPSTER_STORE_KEYS = {"grid", "ranked", "draft", "checklist", "rolling_stone_500_albums_2003", "rolling_stone_500_albums_2012", "rolling_stone_500_albums_2020", "rolling_stone_500_albums_2023", "nme_500_albums", "1001_albums_you_must_hear_before_you_die", "rate_your_music", "rolling_stone_greatest_singers_of_all_time_2023", "rolling_stone_greatest_singers_of_all_time_2008", "rolling_stone_greatest_artists_2010", "rolling_stone_greatest_guitarists_2023", "rolling_stone_greatest_guitarists_2011"}
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
    "rolling_stone_500_albums_2003": "rolling_stone_500_albums_2003",
    "rolling-stone-500-albums-2003": "rolling_stone_500_albums_2003",
    "rolling-stone-500-albums-2003-file": "rolling_stone_500_albums_2003",
    "rolling_stone_500_albums_2003_draft": "rolling_stone_500_albums_2003",
    "rolling_stone_500_albums_2003_list": "rolling_stone_500_albums_2003",
    "rolling_stone_500_albums_2012": "rolling_stone_500_albums_2012",
    "rolling-stone-500-albums-2012": "rolling_stone_500_albums_2012",
    "rolling-stone-500-albums-2012-file": "rolling_stone_500_albums_2012",
    "rolling_stone_500_albums_2012_draft": "rolling_stone_500_albums_2012",
    "rolling_stone_500_albums_2012_list": "rolling_stone_500_albums_2012",
    "rolling_stone_500_albums_2020": "rolling_stone_500_albums_2020",
    "rolling-stone-500-albums-2020": "rolling_stone_500_albums_2020",
    "rolling-stone-500-albums-2020-file": "rolling_stone_500_albums_2020",
    "rolling_stone_500_albums_2020_draft": "rolling_stone_500_albums_2020",
    "rolling_stone_500_albums_2020_list": "rolling_stone_500_albums_2020",
    "rolling_stone_500_albums_2023": "rolling_stone_500_albums_2023",
    "rolling-stone-500-albums-2023": "rolling_stone_500_albums_2023",
    "rolling-stone-500-albums-2023-file": "rolling_stone_500_albums_2023",
    "rolling_stone_500_albums_2023_draft": "rolling_stone_500_albums_2023",
    "rolling_stone_500_albums_2023_list": "rolling_stone_500_albums_2023",
    "nme_500_albums": "nme_500_albums",
    "nme-500-albums": "nme_500_albums",
    "nme-500-albums-file": "nme_500_albums",
    "nme_500_albums_draft": "nme_500_albums",
    "nme_500_albums_list": "nme_500_albums",
    "1001_albums_you_must_hear_before_you_die": "1001_albums_you_must_hear_before_you_die",
    "1001-albums-you-must-hear-before-you-die": "1001_albums_you_must_hear_before_you_die",
    "1001-albums-you-must-hear-before-you-die-file": "1001_albums_you_must_hear_before_you_die",
    "1001_albums_you_must_hear_before_you_die_draft": "1001_albums_you_must_hear_before_you_die",
    "1001_albums_you_must_hear_before_you_die_list": "1001_albums_you_must_hear_before_you_die",
    "rate_your_music": "rate_your_music",
    "rate-your-music": "rate_your_music",
    "rate-your-music-chart": "rate_your_music",
    "rate_your_music_draft": "rate_your_music",
    "rate_your_music_list": "rate_your_music",
    "rolling_stone_greatest_singers_of_all_time_2023": "rolling_stone_greatest_singers_of_all_time_2023",
    "rolling-stone-greatest-singers-of-all-time-2023": "rolling_stone_greatest_singers_of_all_time_2023",
    "rolling-stone-greatest-singers-of-all-time-2023-file": "rolling_stone_greatest_singers_of_all_time_2023",
    "rolling_stone_greatest_singers_of_all_time_2023_draft": "rolling_stone_greatest_singers_of_all_time_2023",
    "rolling_stone_greatest_singers_of_all_time_2023_list": "rolling_stone_greatest_singers_of_all_time_2023",
    "rolling_stone_greatest_artists_2010": "rolling_stone_greatest_artists_2010",
    "rolling-stone-greatest-artists-2010": "rolling_stone_greatest_artists_2010",
    "rolling-stone-greatest-artists-2010-file": "rolling_stone_greatest_artists_2010",
    "rolling_stone_greatest_artists_2010_draft": "rolling_stone_greatest_artists_2010",
    "rolling_stone_greatest_artists_2010_list": "rolling_stone_greatest_artists_2010",
    "rolling_stone_greatest_guitarists_2023": "rolling_stone_greatest_guitarists_2023",
    "rolling-stone-greatest-guitarists-2023": "rolling_stone_greatest_guitarists_2023",
    "rolling-stone-greatest-guitarists-2023-file": "rolling_stone_greatest_guitarists_2023",
    "rolling_stone_greatest_guitarists_2023_draft": "rolling_stone_greatest_guitarists_2023",
    "rolling_stone_greatest_guitarists_2023_list": "rolling_stone_greatest_guitarists_2023",
    "rolling_stone_greatest_guitarists_2011": "rolling_stone_greatest_guitarists_2011",
    "rolling-stone-greatest-guitarists-2011": "rolling_stone_greatest_guitarists_2011",
    "rolling-stone-greatest-guitarists-2011-file": "rolling_stone_greatest_guitarists_2011",
    "rolling_stone_greatest_guitarists_2011_draft": "rolling_stone_greatest_guitarists_2011",
    "rolling_stone_greatest_guitarists_2011_list": "rolling_stone_greatest_guitarists_2011",
    "rolling_stone_greatest_singers_of_all_time_2008": "rolling_stone_greatest_singers_of_all_time_2008",
    "rolling-stone-greatest-singers-of-all-time-2008": "rolling_stone_greatest_singers_of_all_time_2008",
    "rolling-stone-greatest-singers-of-all-time-2008-file": "rolling_stone_greatest_singers_of_all_time_2008",
    "rolling_stone_greatest_singers_of_all_time_2008_draft": "rolling_stone_greatest_singers_of_all_time_2008",
    "rolling_stone_greatest_singers_of_all_time_2008_list": "rolling_stone_greatest_singers_of_all_time_2008",
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
            "rolling_stone_500_albums_2003": data.get("rolling_stone_500_albums_2003") if isinstance(data.get("rolling_stone_500_albums_2003"), dict) else {},
            "rolling_stone_500_albums_2012": data.get("rolling_stone_500_albums_2012") if isinstance(data.get("rolling_stone_500_albums_2012"), dict) else {},
            "rolling_stone_500_albums_2020": data.get("rolling_stone_500_albums_2020") if isinstance(data.get("rolling_stone_500_albums_2020"), dict) else {},
            "rolling_stone_500_albums_2023": data.get("rolling_stone_500_albums_2023") if isinstance(data.get("rolling_stone_500_albums_2023"), dict) else {},
            "nme_500_albums": data.get("nme_500_albums") if isinstance(data.get("nme_500_albums"), dict) else {},
            "1001_albums_you_must_hear_before_you_die": data.get("1001_albums_you_must_hear_before_you_die") if isinstance(data.get("1001_albums_you_must_hear_before_you_die"), dict) else {},
            "rate_your_music": data.get("rate_your_music") if isinstance(data.get("rate_your_music"), dict) else {},
            "rolling_stone_greatest_singers_of_all_time_2023": data.get("rolling_stone_greatest_singers_of_all_time_2023") if isinstance(data.get("rolling_stone_greatest_singers_of_all_time_2023"), dict) else {},
            "rolling_stone_greatest_artists_2010": data.get("rolling_stone_greatest_artists_2010") if isinstance(data.get("rolling_stone_greatest_artists_2010"), dict) else {},
            "rolling_stone_greatest_guitarists_2023": data.get("rolling_stone_greatest_guitarists_2023") if isinstance(data.get("rolling_stone_greatest_guitarists_2023"), dict) else {},
            "rolling_stone_greatest_guitarists_2011": data.get("rolling_stone_greatest_guitarists_2011") if isinstance(data.get("rolling_stone_greatest_guitarists_2011"), dict) else {},
            "rolling_stone_greatest_singers_of_all_time_2008": data.get("rolling_stone_greatest_singers_of_all_time_2008") if isinstance(data.get("rolling_stone_greatest_singers_of_all_time_2008"), dict) else {},
        }

    # Backward-compatible migration path: older builds stored one flat object.
    # Seed the existing public stores from that flat object until each one is saved independently.
    # Draft starts empty because it is based on a host-uploaded Notepad file, not grid.txt.
    return {
        "grid": data,
        "ranked": data,
        "draft": {},
        "checklist": {},
        "rolling_stone_500_albums_2003": {},
        "rolling_stone_500_albums_2012": {},
        "rolling_stone_500_albums_2020": {},
        "rolling_stone_500_albums_2023": {},
        "nme_500_albums": {},
        "1001_albums_you_must_hear_before_you_die": {},
        "rate_your_music": {},
        "rolling_stone_greatest_singers_of_all_time_2023": {},
        "rolling_stone_greatest_artists_2010": {},
        "rolling_stone_greatest_guitarists_2023": {},
        "rolling_stone_greatest_guitarists_2011": {},
        "rolling_stone_greatest_singers_of_all_time_2008": {},
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


def get_topster_admin_username() -> str:
    # Existing deployments only had TOPSTER_ADMIN_PASSWORD. The username therefore
    # defaults to "admin" unless TOPSTER_ADMIN_USERNAME is configured explicitly.
    return normalize_secret_text(
        os.getenv("TOPSTER_ADMIN_USERNAME")
        or read_env_file_value("TOPSTER_ADMIN_USERNAME")
        or "admin"
    ) or "admin"


def get_topster_admin_password() -> str:
    return normalize_secret_text(os.getenv("TOPSTER_ADMIN_PASSWORD") or read_env_file_value("TOPSTER_ADMIN_PASSWORD"))


def topster_admin_password_is_configured() -> bool:
    return bool(get_topster_admin_password())


def submitted_topster_password_is_valid(submitted_password: str) -> bool:
    configured_password = get_topster_admin_password()
    if not configured_password:
        return False
    return hmac.compare_digest(normalize_secret_text(submitted_password), configured_password)


def submitted_topster_credentials_are_valid(submitted_username: str, submitted_password: str) -> bool:
    username_valid = hmac.compare_digest(
        normalize_secret_text(submitted_username),
        get_topster_admin_username(),
    )
    password_valid = submitted_topster_password_is_valid(submitted_password)
    return username_valid and password_valid


def is_topster_admin_protected_page(filename: str) -> bool:
    name = str(filename or "").strip().lower()
    if name in {"hub.html", "grid.html", "ranked_grid.html", "draft_album_list.html", "lyrics.html", "last_fm.html"}:
        return True
    if name.startswith("draft_") and name.endswith(".html"):
        return True
    if name.endswith("_draft.html"):
        return True
    return False


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
    session.pop("topster_admin_username", None)
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
    Protected draft/grid/admin pages require an authenticated admin session.
    """

    if is_local_request() and (BASE_DIR / filename).exists():
        return send_from_directory(BASE_DIR, filename)

    target = FRONTEND_ORIGIN.rstrip("/") + "/" + filename
    if request.query_string:
        target += "?" + request.query_string.decode("utf-8", errors="ignore")

    if is_topster_admin_protected_page(filename) and not is_topster_admin():
        if topster_admin_password_is_configured():
            return redirect("/topster-admin-login?next=" + quote_plus(target))
        return "Admin access is locked because TOPSTER_ADMIN_PASSWORD is not configured.", 403

    return redirect(target, code=302)


@app.route("/hub.html")
def redirect_hub_html():
    return redirect_topster_frontend_page("hub.html")


@app.route("/lyrics.html")
def redirect_lyrics_html():
    return redirect_topster_frontend_page("lyrics.html")


@app.route("/last_fm.html")
def redirect_last_fm_html():
    return redirect_topster_frontend_page("last_fm.html")


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


@app.route("/rolling_stone_500_albums_2003_draft.html")
def redirect_rolling_stone_500_albums_2003_draft_html():
    return redirect_topster_frontend_page("rolling_stone_500_albums_2003_draft.html")


@app.route("/rolling_stone_500_albums_2003_list.html")
def redirect_rolling_stone_500_albums_2003_list_html():
    return redirect_topster_frontend_page("rolling_stone_500_albums_2003_list.html")


@app.route("/rolling_stone_500_albums_2012_draft.html")
def redirect_rolling_stone_500_albums_2012_draft_html():
    return redirect_topster_frontend_page("rolling_stone_500_albums_2012_draft.html")


@app.route("/rolling_stone_500_albums_2012_list.html")
def redirect_rolling_stone_500_albums_2012_list_html():
    return redirect_topster_frontend_page("rolling_stone_500_albums_2012_list.html")


@app.route("/rolling_stone_500_albums_2020_draft.html")
def redirect_rolling_stone_500_albums_2020_draft_html():
    return redirect_topster_frontend_page("rolling_stone_500_albums_2020_draft.html")


@app.route("/rolling_stone_500_albums_2020_list.html")
def redirect_rolling_stone_500_albums_2020_list_html():
    return redirect_topster_frontend_page("rolling_stone_500_albums_2020_list.html")


@app.route("/rolling_stone_500_albums_2023_draft.html")
def redirect_rolling_stone_500_albums_2023_draft_html():
    return redirect_topster_frontend_page("rolling_stone_500_albums_2023_draft.html")


@app.route("/rolling_stone_500_albums_2023_list.html")
def redirect_rolling_stone_500_albums_2023_list_html():
    return redirect_topster_frontend_page("rolling_stone_500_albums_2023_list.html")


@app.route("/nme_500_albums_draft.html")
def redirect_nme_500_albums_draft_html():
    return redirect_topster_frontend_page("nme_500_albums_draft.html")


@app.route("/nme_500_albums_list.html")
def redirect_nme_500_albums_list_html():
    return redirect_topster_frontend_page("nme_500_albums_list.html")


@app.route("/1001_albums_you_must_hear_before_you_die_draft.html")
def redirect_1001_albums_you_must_hear_before_you_die_draft_html():
    return redirect_topster_frontend_page("1001_albums_you_must_hear_before_you_die_draft.html")


@app.route("/1001_albums_you_must_hear_before_you_die_list.html")
def redirect_1001_albums_you_must_hear_before_you_die_list_html():
    return redirect_topster_frontend_page("1001_albums_you_must_hear_before_you_die_list.html")


@app.route("/rate_your_music_draft.html")
def redirect_rate_your_music_draft_html():
    return redirect_topster_frontend_page("rate_your_music_draft.html")


@app.route("/rate_your_music_list.html")
def redirect_rate_your_music_list_html():
    return redirect_topster_frontend_page("rate_your_music_list.html")


@app.route("/rolling_stone_greatest_singers_of_all_time_2023_draft.html")
def redirect_rolling_stone_greatest_singers_2023_draft_html():
    return redirect_topster_frontend_page("rolling_stone_greatest_singers_of_all_time_2023_draft.html")


@app.route("/rolling_stone_greatest_singers_of_all_time_2023_list.html")
def redirect_rolling_stone_greatest_singers_2023_list_html():
    return redirect_topster_frontend_page("rolling_stone_greatest_singers_of_all_time_2023_list.html")


@app.route("/rolling_stone_greatest_artists_2010_draft.html")
def redirect_rolling_stone_greatest_artists_2010_draft_html():
    return redirect_topster_frontend_page("rolling_stone_greatest_artists_2010_draft.html")


@app.route("/rolling_stone_greatest_artists_2010_list.html")
def redirect_rolling_stone_greatest_artists_2010_list_html():
    return redirect_topster_frontend_page("rolling_stone_greatest_artists_2010_list.html")


@app.route("/rolling_stone_greatest_guitarists_2023_draft.html")
def redirect_rolling_stone_greatest_guitarists_2023_draft_html():
    return redirect_topster_frontend_page("rolling_stone_greatest_guitarists_2023_draft.html")


@app.route("/rolling_stone_greatest_guitarists_2011_draft.html")
def redirect_rolling_stone_greatest_guitarists_2011_draft_html():
    return redirect_topster_frontend_page("rolling_stone_greatest_guitarists_2011_draft.html")


@app.route("/rolling_stone_greatest_guitarists_2011_list.html")
def redirect_rolling_stone_greatest_guitarists_2011_list_html():
    return redirect_topster_frontend_page("rolling_stone_greatest_guitarists_2011_list.html")


@app.route("/rolling_stone_greatest_guitarists_2023_list.html")
def redirect_rolling_stone_greatest_guitarists_2023_list_html():
    return redirect_topster_frontend_page("rolling_stone_greatest_guitarists_2023_list.html")


@app.route("/rolling_stone_greatest_singers_of_all_time_2008_draft.html")
def redirect_rolling_stone_greatest_singers_2008_draft_html():
    return redirect_topster_frontend_page("rolling_stone_greatest_singers_of_all_time_2008_draft.html")


@app.route("/rolling_stone_greatest_singers_of_all_time_2008_list.html")
def redirect_rolling_stone_greatest_singers_2008_list_html():
    return redirect_topster_frontend_page("rolling_stone_greatest_singers_of_all_time_2008_list.html")


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
            "sidebarWidth": clamp_int(raw.get("sidebarWidth"), 10, 50, 20),
            "sidebarTextScale": clamp_int(raw.get("sidebarTextScale"), 50, 200, 100),
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


def get_discogs_token() -> str:
    return normalize_secret_text(os.getenv("DISCOGS_TOKEN") or read_env_file_value("DISCOGS_TOKEN") or "")


WIKIPEDIA_MOVIE_TITLE_ALIASES = {
    "3 WOMEN": "3 Women",
    "TRAINSPOTTING": "Trainspotting (film)",
    "ALL THE PRESIDENT'S MEN": "All the President's Men (film)",
    "CRIA!": "Cría cuervos",
}

MOVIE_POSTER_ALLOWED_HOST_SUFFIXES = (
    "media-amazon.com",
    "filmaffinity.com",
    "wikimedia.org",
    "tmdb.org",
    "ltrbxd.com",
    "letterboxd.com",
    "impawards.com",
)


def movie_poster_host_is_allowed(raw_url: str) -> bool:
    try:
        parsed = urlparse(str(raw_url or "").strip())
    except Exception:
        return False
    if parsed.scheme.lower() != "https":
        return False
    host = (parsed.hostname or "").lower().rstrip(".")
    if not host:
        return False
    return any(host == suffix or host.endswith("." + suffix) for suffix in MOVIE_POSTER_ALLOWED_HOST_SUFFIXES)


def fetch_remote_movie_poster(raw_url: str) -> tuple[bytes, str] | None:
    url = str(raw_url or "").strip()
    if not movie_poster_host_is_allowed(url):
        return None

    parsed = urlparse(url)
    referer = f"{parsed.scheme}://{parsed.netloc}/" if parsed.scheme and parsed.netloc else ""
    headers = {
        "Accept": "image/avif,image/webp,image/apng,image/svg+xml,image/*,*/*;q=0.8",
        "User-Agent": "Mozilla/5.0 (compatible; Navincitron/1.0; +https://www.navincitron.com)",
    }
    if referer:
        headers["Referer"] = referer

    try:
        with urlopen(Request(url, headers=headers), timeout=10) as response:
            final_url = response.geturl()
            if not movie_poster_host_is_allowed(final_url):
                return None
            content_type = str(response.headers.get("Content-Type") or "").split(";", 1)[0].strip().lower()
            if not content_type.startswith("image/"):
                return None
            data = response.read(8 * 1024 * 1024 + 1)
    except (HTTPError, URLError, TimeoutError):
        return None

    if not data or len(data) > 8 * 1024 * 1024:
        return None
    return data, content_type or "image/jpeg"


def fetch_wikipedia_movie_poster_url(title: str) -> str:
    requested_title = str(title or "").strip()
    if not requested_title:
        return ""

    mapped = WIKIPEDIA_MOVIE_TITLE_ALIASES.get(requested_title.upper())
    candidates = list(dict.fromkeys(filter(None, [mapped, f"{requested_title} (film)", requested_title])))
    headers = {
        "Accept": "application/json",
        "User-Agent": "Navincitron/1.0 +https://www.navincitron.com",
    }

    for candidate in candidates:
        params = urlencode(
            {
                "action": "query",
                "format": "json",
                "formatversion": "2",
                "redirects": "1",
                "prop": "pageimages",
                "piprop": "thumbnail|original",
                "pithumbsize": "330",
                "titles": candidate,
            }
        )
        url = f"https://en.wikipedia.org/w/api.php?{params}"
        try:
            with urlopen(Request(url, headers=headers), timeout=8) as response:
                payload = json.loads(response.read().decode("utf-8", errors="replace"))
        except (HTTPError, URLError, TimeoutError, json.JSONDecodeError):
            continue

        query = payload.get("query") if isinstance(payload, dict) else None
        pages = query.get("pages") if isinstance(query, dict) else None
        if not isinstance(pages, list):
            continue

        for page in pages:
            if not isinstance(page, dict) or page.get("missing") is not None:
                continue
            thumbnail = page.get("thumbnail") if isinstance(page.get("thumbnail"), dict) else {}
            original = page.get("original") if isinstance(page.get("original"), dict) else {}
            image_url = str(thumbnail.get("source") or original.get("source") or "").strip()
            if image_url.startswith(("https://", "http://")):
                return image_url

    return ""


@app.route("/api/movie-poster", methods=["GET"])
def api_movie_poster():
    direct_url = str(request.args.get("url") or "").strip()
    title = str(request.args.get("title") or "").strip()

    poster_url = direct_url
    if not poster_url and title:
        poster_url = fetch_wikipedia_movie_poster_url(title)

    if not poster_url:
        return "Movie poster was not found.", 404

    fetched = fetch_remote_movie_poster(poster_url)
    if not fetched:
        if direct_url and not movie_poster_host_is_allowed(direct_url):
            return "Movie poster host is not allowed.", 400
        return "Movie poster could not be loaded.", 502

    image_bytes, content_type = fetched
    response = app.response_class(image_bytes, status=200, mimetype=content_type)
    response.headers["Cache-Control"] = "public, max-age=86400"
    response.headers["X-Content-Type-Options"] = "nosniff"
    return response


def discogs_collection_cache_scope(username: str) -> str:
    token = get_discogs_token()
    auth_scope = "public"
    if token:
        # Changing/removing the Discogs token must never leave a week-old public or
        # differently-authenticated collection snapshot active. Only a short hash is
        # used in internal cache keys; the token itself is never stored there.
        auth_scope = "token-" + hashlib.sha256(token.encode("utf-8", errors="ignore")).hexdigest()[:12]
    return f"{username}::{auth_scope}"


def discogs_collection_redis_key(username: str) -> str:
    safe_username = re.sub(r"[^A-Za-z0-9_.-]+", "_", str(username or DISCOGS_COLLECTION_USERNAME))
    scope = discogs_collection_cache_scope(username).rsplit("::", 1)[-1]
    return (
        f"{TOPSTER_REDIS_KEY_PREFIX.strip(':') or 'navincitron:topster'}:"
        f"discogs-collection-v{DISCOGS_COLLECTION_CACHE_VERSION}:{safe_username}:{scope}"
    )


def read_discogs_collection_cache(username: str) -> dict[str, Any] | None:
    now = time.time()
    memory_key = discogs_collection_cache_scope(username)
    memory = DISCOGS_COLLECTION_MEMORY_CACHE.get(memory_key)
    if isinstance(memory, dict) and (now - float(memory.get("cachedAtEpoch", 0))) < DISCOGS_COLLECTION_CACHE_SECONDS:
        return memory.get("payload") if isinstance(memory.get("payload"), dict) else None

    if topster_redis_is_configured():
        try:
            client = get_topster_redis_client()
            if client is not None:
                raw = client.get(discogs_collection_redis_key(username))
                if raw:
                    parsed = json.loads(raw)
                    if isinstance(parsed, dict):
                        DISCOGS_COLLECTION_MEMORY_CACHE[memory_key] = {
                            "cachedAtEpoch": now,
                            "payload": parsed,
                        }
                        return parsed
        except Exception:
            pass

    return None


def write_discogs_collection_cache(username: str, payload: dict[str, Any]) -> None:
    now = time.time()
    memory_key = discogs_collection_cache_scope(username)
    DISCOGS_COLLECTION_MEMORY_CACHE[memory_key] = {
        "cachedAtEpoch": now,
        "payload": payload,
    }

    if topster_redis_is_configured():
        try:
            client = get_topster_redis_client()
            if client is not None:
                client.setex(
                    discogs_collection_redis_key(username),
                    DISCOGS_COLLECTION_CACHE_SECONDS,
                    json.dumps(payload, ensure_ascii=False),
                )
        except Exception:
            pass


def fetch_discogs_collection_page(username: str, page: int, per_page: int = 100) -> dict[str, Any]:
    params = urlencode({"page": max(1, int(page)), "per_page": min(100, max(1, int(per_page)))})
    url = f"https://api.discogs.com/users/{quote_plus(username)}/collection/folders/0/releases?{params}"
    headers = {
        "Accept": "application/json",
        "User-Agent": "Navincitron/1.0 +https://www.navincitron.com",
    }
    token = get_discogs_token()
    if token:
        headers["Authorization"] = f"Discogs token={token}"

    last_error: Exception | None = None
    for attempt in range(2):
        try:
            with urlopen(Request(url, headers=headers), timeout=20) as response:
                payload = json.loads(response.read().decode("utf-8", errors="replace"))
            if not isinstance(payload, dict):
                raise RuntimeError("Discogs returned an invalid collection response.")
            return payload
        except HTTPError as error:
            last_error = error
            if error.code == 429 and attempt == 0:
                retry_after = error.headers.get("Retry-After", "2") if error.headers else "2"
                try:
                    wait_seconds = min(8.0, max(1.0, float(retry_after)))
                except (TypeError, ValueError):
                    wait_seconds = 2.0
                time.sleep(wait_seconds)
                continue
            if error.code in {401, 403} and token:
                # A stale/wrong personal token should not make a public collection
                # unusable. Retry this page anonymously; owner-only collection fields
                # will remain unavailable and the frontend will report that clearly.
                public_headers = {
                    "Accept": "application/json",
                    "User-Agent": "Navincitron/1.0 +https://www.navincitron.com",
                }
                try:
                    with urlopen(Request(url, headers=public_headers), timeout=20) as response:
                        payload = json.loads(response.read().decode("utf-8", errors="replace"))
                    if isinstance(payload, dict):
                        return payload
                except Exception:
                    pass
            if error.code in {401, 403} and not token:
                raise RuntimeError(
                    "Discogs rejected the public collection request. Configure DISCOGS_TOKEN in Render for reliable authenticated collection access."
                ) from error
            raise RuntimeError(f"Discogs collection request failed with HTTP {error.code}.") from error
        except (URLError, TimeoutError, json.JSONDecodeError) as error:
            last_error = error
            if attempt == 0:
                time.sleep(1.0)
                continue
            break

    raise RuntimeError(f"Discogs collection request failed: {last_error}")


def normalize_discogs_formats(raw_formats: Any) -> list[dict[str, Any]]:
    formats: list[dict[str, Any]] = []
    if not isinstance(raw_formats, list):
        return formats

    for item in raw_formats:
        if not isinstance(item, dict):
            continue
        name = str(item.get("name") or "").strip()
        descriptions = [
            str(value).strip()
            for value in (item.get("descriptions") or [])
            if str(value).strip()
        ] if isinstance(item.get("descriptions"), list) else []
        text = str(item.get("text") or "").strip()
        quantity = item.get("qty")
        formats.append(
            {
                "name": name,
                "qty": str(quantity).strip() if quantity is not None else "",
                "descriptions": descriptions,
                "text": text,
            }
        )
    return formats


def discogs_formats_include_vinyl(formats: Any) -> bool:
    for item in formats if isinstance(formats, list) else []:
        if not isinstance(item, dict):
            continue
        values = [str(item.get("name") or "")]
        descriptions = item.get("descriptions")
        if isinstance(descriptions, list):
            values.extend(str(value or "") for value in descriptions)
        if any("vinyl" in value.casefold() for value in values):
            return True
    return False


def fetch_discogs_authenticated_username() -> str:
    token = get_discogs_token()
    if not token:
        return ""

    request_headers = {
        "Accept": "application/json",
        "Authorization": f"Discogs token={token}",
        "User-Agent": "Navincitron/1.0 +https://www.navincitron.com",
    }
    try:
        with urlopen(Request("https://api.discogs.com/oauth/identity", headers=request_headers), timeout=15) as response:
            payload = json.loads(response.read().decode("utf-8", errors="replace"))
    except Exception:
        return ""
    return str(payload.get("username") or "").strip() if isinstance(payload, dict) else ""


def fetch_discogs_collection_field_names(username: str) -> dict[str, str]:
    """Return Discogs collection custom-field IDs mapped to their display names.

    Media Condition and Sleeve Condition are collection fields rather than release-
    database metadata. The user's authenticated Discogs token is therefore used
    when available so private collection values can be read. A field lookup failure
    must never prevent the collection itself from loading.
    """

    url = f"https://api.discogs.com/users/{quote_plus(username)}/collection/fields"
    headers = {
        "Accept": "application/json",
        "User-Agent": "Navincitron/1.0 +https://www.navincitron.com",
    }
    token = get_discogs_token()
    if token:
        headers["Authorization"] = f"Discogs token={token}"

    try:
        with urlopen(Request(url, headers=headers), timeout=15) as response:
            payload = json.loads(response.read().decode("utf-8", errors="replace"))
    except Exception:
        return {}

    fields = payload.get("fields") if isinstance(payload, dict) else None
    if not isinstance(fields, list):
        return {}

    names: dict[str, str] = {}
    for field in fields:
        if not isinstance(field, dict):
            continue
        field_id = field.get("id")
        name = str(field.get("name") or "").strip()
        if field_id is None or not name:
            continue
        names[str(field_id)] = name
    return names


def discogs_collection_item_conditions(
    item: dict[str, Any],
    field_names: dict[str, str],
) -> tuple[str, str]:
    """Extract the owner's media/sleeve grading for one collection instance."""

    media_condition = ""
    sleeve_condition = ""

    # Be tolerant of direct fields if Discogs changes/extends the collection shape.
    for key in ("media_condition", "mediaCondition"):
        value = str(item.get(key) or "").strip()
        if value:
            media_condition = value
            break
    for key in ("sleeve_condition", "sleeveCondition"):
        value = str(item.get(key) or "").strip()
        if value:
            sleeve_condition = value
            break

    notes = item.get("notes")
    if isinstance(notes, list):
        for note in notes:
            if not isinstance(note, dict):
                continue
            field_id = str(note.get("field_id") if note.get("field_id") is not None else note.get("fieldId") or "")
            value = str(note.get("value") or "").strip()
            if not value:
                continue
            field_name = str(field_names.get(field_id) or "").strip().casefold()
            normalized_name = re.sub(r"[^a-z]+", " ", field_name).strip()
            if "media" in normalized_name and "condition" in normalized_name:
                media_condition = value
            elif "sleeve" in normalized_name and "condition" in normalized_name:
                sleeve_condition = value
            elif not field_name:
                # Discogs's default collection fields are historically IDs 1 and 2.
                # Use this only as a fallback when the field-definition request was
                # unavailable; named fields above always take precedence.
                if field_id == "1" and not media_condition:
                    media_condition = value
                elif field_id == "2" and not sleeve_condition:
                    sleeve_condition = value

    return media_condition, sleeve_condition


def fetch_discogs_collection_release_instances(username: str, release_id: int) -> list[dict[str, Any]]:
    token = get_discogs_token()
    if not token or release_id <= 0:
        return []
    url = f"https://api.discogs.com/users/{quote_plus(username)}/collection/releases/{release_id}"
    headers = {
        "Accept": "application/json",
        "Authorization": f"Discogs token={token}",
        "User-Agent": "Navincitron/1.0 +https://www.navincitron.com",
    }
    try:
        with urlopen(Request(url, headers=headers), timeout=15) as response:
            payload = json.loads(response.read().decode("utf-8", errors="replace"))
    except Exception:
        return []
    releases = payload.get("releases") if isinstance(payload, dict) else None
    return [item for item in releases if isinstance(item, dict)] if isinstance(releases, list) else []


def refresh_discogs_owned_release_conditions(
    username: str,
    owned_release: dict[str, Any],
    field_names: dict[str, str],
) -> dict[str, Any]:
    refreshed = dict(owned_release)
    if refreshed.get("mediaCondition") and refreshed.get("sleeveCondition"):
        return refreshed
    release_id_raw = refreshed.get("releaseId")
    if not str(release_id_raw or "").isdigit() or not get_discogs_token():
        return refreshed
    release_id = int(release_id_raw)
    instance_id = refreshed.get("instanceId")
    folder_id = refreshed.get("folderId")
    instances = fetch_discogs_collection_release_instances(username, release_id)
    if not instances:
        return refreshed

    selected = None
    if instance_id is not None:
        selected = next((item for item in instances if str(item.get("instance_id")) == str(instance_id)), None)
    if selected is None and folder_id is not None:
        selected = next((item for item in instances if str(item.get("folder_id")) == str(folder_id)), None)
    if selected is None and len(instances) == 1:
        selected = instances[0]
    if selected is None:
        return refreshed

    media_condition, sleeve_condition = discogs_collection_item_conditions(selected, field_names)
    if media_condition and not refreshed.get("mediaCondition"):
        refreshed["mediaCondition"] = media_condition
    if sleeve_condition and not refreshed.get("sleeveCondition"):
        refreshed["sleeveCondition"] = sleeve_condition
    return refreshed


def fetch_full_discogs_collection(username: str) -> dict[str, Any]:
    first = fetch_discogs_collection_page(username, 1, 100)
    pagination = first.get("pagination") if isinstance(first.get("pagination"), dict) else {}
    total_pages = max(1, int(pagination.get("pages") or 1))
    total_items = max(0, int(pagination.get("items") or 0))
    total_pages = min(total_pages, 100)

    releases: list[dict[str, Any]] = []
    first_releases = first.get("releases")
    if isinstance(first_releases, list):
        releases.extend(item for item in first_releases if isinstance(item, dict))

    for page in range(2, total_pages + 1):
        payload = fetch_discogs_collection_page(username, page, 100)
        page_releases = payload.get("releases")
        if isinstance(page_releases, list):
            releases.extend(item for item in page_releases if isinstance(item, dict))

    authenticated_username = fetch_discogs_authenticated_username()
    authenticated_owner = bool(authenticated_username and authenticated_username.casefold() == username.casefold())
    collection_field_names = fetch_discogs_collection_field_names(username)

    unique: dict[str, dict[str, Any]] = {}
    release_instances_by_key: dict[str, set[tuple[int, int]]] = {}
    for item in releases:
        basic = item.get("basic_information") if isinstance(item.get("basic_information"), dict) else {}
        title = str(basic.get("title") or "").strip()
        if not title:
            continue

        artist_names: list[str] = []
        raw_artists = basic.get("artists")
        if isinstance(raw_artists, list):
            for artist in raw_artists:
                if not isinstance(artist, dict):
                    continue
                name = str(artist.get("name") or "").strip()
                if name:
                    artist_names.append(name)

        release_id_raw = basic.get("id") or item.get("id")
        release_id = int(release_id_raw) if str(release_id_raw or "").isdigit() else None
        master_id_raw = basic.get("master_id")
        master_id = int(master_id_raw) if str(master_id_raw or "").isdigit() and int(master_id_raw) > 0 else None
        year_raw = basic.get("year")
        year = int(year_raw) if str(year_raw or "").isdigit() else None
        formats = normalize_discogs_formats(basic.get("formats"))
        vinyl = discogs_formats_include_vinyl(formats)
        instance_id_raw = item.get("instance_id")
        instance_id = int(instance_id_raw) if str(instance_id_raw or "").isdigit() else None
        media_condition, sleeve_condition = discogs_collection_item_conditions(item, collection_field_names)

        key = f"{' | '.join(artist_names).casefold()}::{title.casefold()}"
        if key not in unique:
            unique[key] = {
                "artist": ", ".join(artist_names),
                "artists": artist_names,
                "title": title,
                "year": year,
                "releaseId": release_id,
                "masterId": master_id,
                # Preserve every distinct owned physical release so lyrics.html can
                # choose an actual vinyl copy after using the same album matcher as
                # the Topster "Exclude releases that I have" option.
                "ownedReleases": [],
                "vinylReleaseIds": [],
            }
            release_instances_by_key[key] = set()
        else:
            if unique[key].get("year") is None and year is not None:
                unique[key]["year"] = year
            if unique[key].get("masterId") is None and master_id is not None:
                unique[key]["masterId"] = master_id

        if release_id is None:
            continue
        instance_key = (release_id, instance_id if instance_id is not None else -1)
        if instance_key in release_instances_by_key[key]:
            continue
        release_instances_by_key[key].add(instance_key)

        folder_id_raw = item.get("folder_id")
        folder_id = int(folder_id_raw) if str(folder_id_raw or "").isdigit() else None
        owned_release = {
            "releaseId": release_id,
            "masterId": master_id,
            "year": year,
            "instanceId": instance_id,
            "folderId": folder_id,
            "formats": formats,
            "vinyl": vinyl,
            "mediaCondition": media_condition,
            "sleeveCondition": sleeve_condition,
        }
        unique[key]["ownedReleases"].append(owned_release)
        if vinyl:
            unique[key]["vinylReleaseIds"].append(release_id)

    payload = {
        "ok": True,
        "username": username,
        "itemCount": total_items or len(releases),
        "uniqueAlbumCount": len(unique),
        "albums": list(unique.values()),
        "cachedSeconds": DISCOGS_COLLECTION_CACHE_SECONDS,
        "cacheVersion": DISCOGS_COLLECTION_CACHE_VERSION,
        "fetchedAt": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "discogsTokenConfigured": bool(get_discogs_token()),
        "authenticatedToDiscogs": authenticated_owner,
        "authenticatedDiscogsUsername": authenticated_username,
        "conditionFieldNames": collection_field_names,
    }
    return payload


def discogs_collection_json_response(payload: dict[str, Any], status_code: int = 200):
    response = jsonify(payload)
    response.status_code = status_code
    # The application already maintains its own versioned Redis/browser cache.
    # Do not let a browser, proxy, or CDN pin an older collection payload on top
    # of that cache contract.
    response.headers["Cache-Control"] = "no-store, no-cache, must-revalidate, max-age=0"
    response.headers["Pragma"] = "no-cache"
    response.headers["Expires"] = "0"
    return response


@app.route("/api/discogs-collection", methods=["GET"])
def api_discogs_collection():
    username = str(request.args.get("username") or DISCOGS_COLLECTION_USERNAME).strip() or DISCOGS_COLLECTION_USERNAME
    if username.casefold() != DISCOGS_COLLECTION_USERNAME.casefold():
        return discogs_collection_json_response({"ok": False, "error": "Only the configured Navincitron Discogs collection is available."}, 400)

    force_refresh = str(request.args.get("refresh") or "").strip().lower() in {"1", "true", "yes"}
    if force_refresh:
        DISCOGS_COLLECTION_MEMORY_CACHE.pop(username, None)
        if topster_redis_is_configured():
            try:
                client = get_topster_redis_client()
                if client is not None:
                    client.delete(discogs_collection_redis_key(username))
            except Exception:
                pass
    else:
        cached = read_discogs_collection_cache(username)
        if cached and int(cached.get("cacheVersion") or 0) == DISCOGS_COLLECTION_CACHE_VERSION:
            return discogs_collection_json_response(cached)

    try:
        payload = fetch_full_discogs_collection(username)
        write_discogs_collection_cache(username, payload)
        return discogs_collection_json_response(payload)
    except Exception as error:
        cached = read_discogs_collection_cache(username)
        if cached:
            cached = dict(cached)
            cached["stale"] = True
            cached["warning"] = str(error)
            return discogs_collection_json_response(cached)
        return discogs_collection_json_response({"ok": False, "error": str(error)}, 502)



def topster_discogs_ownership_overrides_redis_key(username: str) -> str:
    safe_username = re.sub(r"[^A-Za-z0-9_.-]+", "_", str(username or DISCOGS_COLLECTION_USERNAME))
    return (
        f"{TOPSTER_REDIS_KEY_PREFIX.strip(':') or 'navincitron:topster'}:"
        f"discogs-ownership-overrides:{safe_username}"
    )


def normalize_topster_discogs_ownership_override(value: Any) -> dict[str, Any] | None:
    if not isinstance(value, dict):
        return None

    identity = str(value.get("identity") or "").strip()
    artist = str(value.get("artist") or "").strip()
    title = str(value.get("title") or value.get("album") or "").strip()
    state = str(value.get("state") or "").strip().lower().replace("-", "_")

    if state not in {"owned", "not_owned"}:
        return None
    if not identity or len(identity) > 1200 or "::" not in identity:
        return None
    if not title or len(title) > 600 or len(artist) > 600:
        return None

    release_id_raw = value.get("releaseId")
    release_id = int(release_id_raw) if str(release_id_raw or "").isdigit() and int(release_id_raw) > 0 else None
    release_url = str(value.get("releaseUrl") or "").strip()
    if release_url and not release_url.startswith(("http://", "https://")):
        release_url = ""

    normalized = {
        "identity": identity,
        "artist": artist,
        "title": title,
        "state": state,
        "savedAt": str(value.get("savedAt") or time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())).strip(),
    }
    if release_id:
        normalized["releaseId"] = release_id
    if release_url:
        normalized["releaseUrl"] = release_url
    return normalized


def topster_discogs_ownership_override_digest(identity: str) -> str:
    return hashlib.sha256(str(identity or "").encode("utf-8", errors="ignore")).hexdigest()


def read_topster_discogs_ownership_overrides(username: str) -> list[dict[str, Any]]:
    records: dict[str, dict[str, Any]] = {}

    # JSON is a no-Redis fallback and also a best-effort mirror. Merge it first so
    # a Redis value with the same identity remains authoritative.
    with TOPSTER_DISCOGS_OWNERSHIP_OVERRIDES_LOCK:
        json_data = read_json_file(TOPSTER_DISCOGS_OWNERSHIP_OVERRIDES_FILE, {})
    if isinstance(json_data, dict):
        for raw in json_data.values():
            normalized = normalize_topster_discogs_ownership_override(raw)
            if normalized:
                records[normalized["identity"]] = normalized

    if topster_redis_is_configured():
        try:
            client = get_topster_redis_client()
            if client is not None:
                raw_values = client.hgetall(topster_discogs_ownership_overrides_redis_key(username)) or {}
                for raw in raw_values.values():
                    try:
                        parsed = json.loads(raw)
                    except Exception:
                        continue
                    normalized = normalize_topster_discogs_ownership_override(parsed)
                    if normalized:
                        records[normalized["identity"]] = normalized
        except Exception:
            # The JSON mirror/fallback can still make previously saved flags readable.
            pass

    return sorted(records.values(), key=lambda item: (str(item.get("artist") or "").casefold(), str(item.get("title") or "").casefold()))


def write_topster_discogs_ownership_override(username: str, value: dict[str, Any]) -> dict[str, Any]:
    normalized = normalize_topster_discogs_ownership_override(value)
    if not normalized:
        raise ValueError("A valid ownership identity, album title, and owned/not-owned state are required.")

    digest = topster_discogs_ownership_override_digest(normalized["identity"])
    redis_saved = False
    if topster_redis_is_configured():
        client = get_topster_redis_client()
        if client is None:
            raise RuntimeError(TOPSTER_REDIS_CLIENT_ERROR or "Redis is configured but unavailable.")
        # HSET has no TTL here by design. Manual ownership flags must not expire with
        # the seven-day Discogs collection cache or any browser-side Topster cache.
        client.hset(
            topster_discogs_ownership_overrides_redis_key(username),
            digest,
            json.dumps(normalized, ensure_ascii=False),
        )
        redis_saved = True

    # Keep a JSON mirror for local/no-Redis deployments. Failure to mirror must not
    # invalidate a successful durable Redis write.
    try:
        with TOPSTER_DISCOGS_OWNERSHIP_OVERRIDES_LOCK:
            json_data = read_json_file(TOPSTER_DISCOGS_OWNERSHIP_OVERRIDES_FILE, {})
            if not isinstance(json_data, dict):
                json_data = {}
            json_data[digest] = normalized
            write_json_file(TOPSTER_DISCOGS_OWNERSHIP_OVERRIDES_FILE, json_data)
    except Exception:
        if not redis_saved:
            raise

    return normalized


@app.route("/api/topster-discogs-ownership-overrides", methods=["GET", "POST"])
def api_topster_discogs_ownership_overrides():
    username = str(request.args.get("username") or DISCOGS_COLLECTION_USERNAME).strip() or DISCOGS_COLLECTION_USERNAME
    if username.casefold() != DISCOGS_COLLECTION_USERNAME.casefold():
        return discogs_collection_json_response({"ok": False, "error": "Only the configured Navincitron Discogs collection is available."}, 400)

    if request.method == "GET":
        try:
            return discogs_collection_json_response({
                "ok": True,
                "username": username,
                "overrides": read_topster_discogs_ownership_overrides(username),
            })
        except Exception as error:
            return discogs_collection_json_response({"ok": False, "error": str(error)}, 502)

    admin_error = require_topster_admin_response()
    if admin_error is not None:
        return admin_error

    payload = request.get_json(silent=True) or {}
    submitted_username = str(payload.get("username") or username).strip() or username
    if submitted_username.casefold() != DISCOGS_COLLECTION_USERNAME.casefold():
        return discogs_collection_json_response({"ok": False, "error": "Only the configured Navincitron Discogs collection is available."}, 400)

    try:
        saved = write_topster_discogs_ownership_override(submitted_username, payload)
        return discogs_collection_json_response({
            "ok": True,
            "username": submitted_username,
            "override": saved,
        })
    except ValueError as error:
        return discogs_collection_json_response({"ok": False, "error": str(error)}, 400)
    except Exception as error:
        return discogs_collection_json_response({"ok": False, "error": str(error)}, 502)


def discogs_release_redis_key(release_id: int) -> str:
    return (
        f"{TOPSTER_REDIS_KEY_PREFIX.strip(':') or 'navincitron:topster'}:"
        f"discogs-release-v{DISCOGS_RELEASE_CACHE_VERSION}:{int(release_id)}"
    )


def read_discogs_release_cache(release_id: int) -> dict[str, Any] | None:
    release_id = int(release_id)
    now = time.time()
    memory = DISCOGS_RELEASE_MEMORY_CACHE.get(release_id)
    if isinstance(memory, dict) and (now - float(memory.get("cachedAtEpoch", 0))) < DISCOGS_RELEASE_CACHE_SECONDS:
        payload = memory.get("payload")
        return payload if isinstance(payload, dict) else None

    if topster_redis_is_configured():
        try:
            client = get_topster_redis_client()
            if client is not None:
                raw = client.get(discogs_release_redis_key(release_id))
                if raw:
                    parsed = json.loads(raw)
                    if isinstance(parsed, dict):
                        DISCOGS_RELEASE_MEMORY_CACHE[release_id] = {
                            "cachedAtEpoch": now,
                            "payload": parsed,
                        }
                        return parsed
        except Exception:
            pass
    return None


def write_discogs_release_cache(release_id: int, payload: dict[str, Any]) -> None:
    release_id = int(release_id)
    now = time.time()
    DISCOGS_RELEASE_MEMORY_CACHE[release_id] = {
        "cachedAtEpoch": now,
        "payload": payload,
    }
    if topster_redis_is_configured():
        try:
            client = get_topster_redis_client()
            if client is not None:
                client.setex(
                    discogs_release_redis_key(release_id),
                    DISCOGS_RELEASE_CACHE_SECONDS,
                    json.dumps(payload, ensure_ascii=False),
                )
        except Exception:
            pass


def fetch_discogs_release(release_id: int) -> dict[str, Any]:
    release_id = int(release_id)
    cached = read_discogs_release_cache(release_id)
    if cached:
        return cached

    headers = {
        "Accept": "application/json",
        "User-Agent": "Navincitron/1.0 +https://www.navincitron.com",
    }
    token = get_discogs_token()
    if token:
        headers["Authorization"] = f"Discogs token={token}"

    url = f"https://api.discogs.com/releases/{release_id}"
    last_error: Exception | None = None
    for attempt in range(2):
        try:
            with urlopen(Request(url, headers=headers), timeout=20) as response:
                raw = json.loads(response.read().decode("utf-8", errors="replace"))
            if not isinstance(raw, dict):
                raise RuntimeError("Discogs returned an invalid release response.")

            artists: list[str] = []
            for artist in raw.get("artists") if isinstance(raw.get("artists"), list) else []:
                if isinstance(artist, dict):
                    name = str(artist.get("name") or "").strip()
                    if name:
                        artists.append(name)

            def normalize_track_entry(entry: Any) -> dict[str, Any] | None:
                if not isinstance(entry, dict):
                    return None
                sub_tracks = []
                for sub_track in entry.get("sub_tracks") if isinstance(entry.get("sub_tracks"), list) else []:
                    normalized_sub_track = normalize_track_entry(sub_track)
                    if normalized_sub_track:
                        sub_tracks.append(normalized_sub_track)

                track_artists: list[str] = []
                for artist in entry.get("artists") if isinstance(entry.get("artists"), list) else []:
                    if not isinstance(artist, dict):
                        continue
                    name = str(artist.get("name") or "").strip()
                    if name:
                        track_artists.append(name)

                return {
                    "position": str(entry.get("position") or "").strip(),
                    "title": str(entry.get("title") or "").strip(),
                    "duration": str(entry.get("duration") or "").strip(),
                    "type": str(entry.get("type_") or entry.get("type") or "track").strip().lower(),
                    "artists": track_artists,
                    "subTracks": sub_tracks,
                }

            tracklist: list[dict[str, Any]] = []
            for entry in raw.get("tracklist") if isinstance(raw.get("tracklist"), list) else []:
                normalized_entry = normalize_track_entry(entry)
                if normalized_entry:
                    tracklist.append(normalized_entry)

            payload = {
                "releaseId": release_id,
                "masterId": int(raw.get("master_id")) if str(raw.get("master_id") or "").isdigit() and int(raw.get("master_id")) > 0 else None,
                "title": str(raw.get("title") or "").strip(),
                "artists": artists,
                "year": int(raw.get("year")) if str(raw.get("year") or "").isdigit() else None,
                "formats": normalize_discogs_formats(raw.get("formats")),
                "vinyl": discogs_formats_include_vinyl(normalize_discogs_formats(raw.get("formats"))),
                "discogsUrl": str(raw.get("uri") or f"https://www.discogs.com/release/{release_id}").strip(),
                "tracklist": tracklist,
            }
            write_discogs_release_cache(release_id, payload)
            return payload
        except HTTPError as error:
            last_error = error
            if error.code == 429 and attempt == 0:
                retry_after = error.headers.get("Retry-After", "2") if error.headers else "2"
                try:
                    wait_seconds = min(8.0, max(1.0, float(retry_after)))
                except (TypeError, ValueError):
                    wait_seconds = 2.0
                time.sleep(wait_seconds)
                continue
            raise RuntimeError(f"Discogs release request failed with HTTP {error.code}.") from error
        except (URLError, TimeoutError, json.JSONDecodeError) as error:
            last_error = error
            if attempt == 0:
                time.sleep(1.0)
                continue
            break

    raise RuntimeError(f"Discogs release request failed: {last_error}")


def lyrics_discogs_cover_redis_key(release_id: int) -> str:
    return (
        f"{TOPSTER_REDIS_KEY_PREFIX.strip(':') or 'navincitron:topster'}:"
        f"lyrics-discogs-cover:{int(release_id)}"
    )


def normalize_lyrics_discogs_cover_override(value: Any) -> dict[str, Any] | None:
    if not isinstance(value, dict):
        return None
    image_url = str(value.get("imageUrl") or value.get("imageSrc") or "").strip()
    if not image_url.startswith(("http://", "https://")):
        return None
    source = str(value.get("source") or "Manual").strip()[:120]
    href = str(value.get("href") or "").strip()
    if href and not href.startswith(("http://", "https://")):
        href = ""
    saved_at = str(value.get("savedAt") or time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())).strip()
    normalized = {
        "imageUrl": image_url,
        "source": source or "Manual",
        "href": href,
        "savedAt": saved_at,
    }
    release_id_raw = value.get("releaseId")
    if str(release_id_raw or "").isdigit() and int(release_id_raw) > 0:
        normalized["releaseId"] = int(release_id_raw)
    artist = str(value.get("artist") or "").strip()
    album = str(value.get("album") or "").strip()
    if artist:
        normalized["artist"] = artist
    if album:
        normalized["album"] = album
    return normalized


def read_lyrics_discogs_cover_override(release_id: int) -> dict[str, Any] | None:
    release_id = int(release_id)
    if topster_redis_is_configured():
        try:
            client = get_topster_redis_client()
            if client is not None:
                raw = client.get(lyrics_discogs_cover_redis_key(release_id))
                if raw:
                    return normalize_lyrics_discogs_cover_override(json.loads(raw))
        except Exception:
            pass

    data = read_json_file(LYRICS_DISCOGS_COVER_OVERRIDES_FILE, {})
    if not isinstance(data, dict):
        return None
    return normalize_lyrics_discogs_cover_override(data.get(str(release_id)))


def write_lyrics_discogs_cover_override(release_id: int, value: dict[str, Any]) -> dict[str, Any]:
    release_id = int(release_id)
    normalized = normalize_lyrics_discogs_cover_override(value)
    if not normalized:
        raise ValueError("A valid http:// or https:// image URL is required.")

    if topster_redis_is_configured():
        client = get_topster_redis_client()
        if client is None:
            raise RuntimeError(TOPSTER_REDIS_CLIENT_ERROR or "Redis is configured but unavailable.")
        client.set(lyrics_discogs_cover_redis_key(release_id), json.dumps(normalized, ensure_ascii=False))
        return normalized

    data = read_json_file(LYRICS_DISCOGS_COVER_OVERRIDES_FILE, {})
    if not isinstance(data, dict):
        data = {}
    data[str(release_id)] = normalized
    write_json_file(LYRICS_DISCOGS_COVER_OVERRIDES_FILE, data)
    return normalized


def delete_lyrics_discogs_cover_override(release_id: int) -> None:
    release_id = int(release_id)
    if topster_redis_is_configured():
        client = get_topster_redis_client()
        if client is None:
            raise RuntimeError(TOPSTER_REDIS_CLIENT_ERROR or "Redis is configured but unavailable.")
        client.delete(lyrics_discogs_cover_redis_key(release_id))
        return

    data = read_json_file(LYRICS_DISCOGS_COVER_OVERRIDES_FILE, {})
    if not isinstance(data, dict):
        return
    if str(release_id) in data:
        data.pop(str(release_id), None)
        write_json_file(LYRICS_DISCOGS_COVER_OVERRIDES_FILE, data)


def lyrics_album_cover_identity(artist: Any, album: Any) -> str:
    artist_key = normalize_lyrics_match_text(artist)
    album_key = normalize_lyrics_match_text(album)
    if not album_key or album_key in {"unknown album", "none", "null"}:
        return ""
    return f"{artist_key}::{album_key}"


def lyrics_album_cover_json_key(artist: Any, album: Any) -> str:
    identity = lyrics_album_cover_identity(artist, album)
    return f"album::{identity}" if identity else ""


def lyrics_album_cover_redis_key(artist: Any, album: Any) -> str:
    identity = lyrics_album_cover_identity(artist, album)
    if not identity:
        return ""
    digest = hashlib.sha256(identity.encode("utf-8", errors="ignore")).hexdigest()
    return (
        f"{TOPSTER_REDIS_KEY_PREFIX.strip(':') or 'navincitron:topster'}:"
        f"lyrics-album-cover:{digest}"
    )


def read_lyrics_album_cover_override(artist: Any, album: Any) -> dict[str, Any] | None:
    json_key = lyrics_album_cover_json_key(artist, album)
    if not json_key:
        return None

    if topster_redis_is_configured():
        try:
            client = get_topster_redis_client()
            redis_key = lyrics_album_cover_redis_key(artist, album)
            if client is not None and redis_key:
                raw = client.get(redis_key)
                if raw:
                    return normalize_lyrics_discogs_cover_override(json.loads(raw))
        except Exception:
            pass

    data = read_json_file(LYRICS_DISCOGS_COVER_OVERRIDES_FILE, {})
    if not isinstance(data, dict):
        return None
    return normalize_lyrics_discogs_cover_override(data.get(json_key))


def write_lyrics_album_cover_override(artist: Any, album: Any, value: dict[str, Any]) -> dict[str, Any]:
    json_key = lyrics_album_cover_json_key(artist, album)
    if not json_key:
        raise ValueError("A valid artist and album name are required for a non-Discogs cover override.")

    normalized = normalize_lyrics_discogs_cover_override(value)
    if not normalized:
        raise ValueError("A valid http:// or https:// image URL is required.")

    if topster_redis_is_configured():
        client = get_topster_redis_client()
        redis_key = lyrics_album_cover_redis_key(artist, album)
        if client is None or not redis_key:
            raise RuntimeError(TOPSTER_REDIS_CLIENT_ERROR or "Redis is configured but unavailable.")
        client.set(redis_key, json.dumps(normalized, ensure_ascii=False))
        return normalized

    data = read_json_file(LYRICS_DISCOGS_COVER_OVERRIDES_FILE, {})
    if not isinstance(data, dict):
        data = {}
    data[json_key] = normalized
    write_json_file(LYRICS_DISCOGS_COVER_OVERRIDES_FILE, data)
    return normalized


def delete_lyrics_album_cover_override(artist: Any, album: Any) -> None:
    json_key = lyrics_album_cover_json_key(artist, album)
    if not json_key:
        return

    if topster_redis_is_configured():
        client = get_topster_redis_client()
        redis_key = lyrics_album_cover_redis_key(artist, album)
        if client is None:
            raise RuntimeError(TOPSTER_REDIS_CLIENT_ERROR or "Redis is configured but unavailable.")
        if redis_key:
            client.delete(redis_key)
        return

    data = read_json_file(LYRICS_DISCOGS_COVER_OVERRIDES_FILE, {})
    if not isinstance(data, dict):
        return
    if json_key in data:
        data.pop(json_key, None)
        write_json_file(LYRICS_DISCOGS_COVER_OVERRIDES_FILE, data)


def read_saved_cover_override(release_id: Any = None, artist: Any = "", album: Any = "") -> dict[str, Any] | None:
    if str(release_id or "").isdigit() and int(release_id) > 0:
        release_override = read_lyrics_discogs_cover_override(int(release_id))
        if release_override:
            return release_override
    return read_lyrics_album_cover_override(artist, album)


def write_saved_cover_override(
    value: dict[str, Any],
    release_id: Any = None,
    artist: Any = "",
    album: Any = "",
) -> dict[str, Any]:
    saved: dict[str, Any] | None = None
    release_id_int = int(release_id) if str(release_id or "").isdigit() and int(release_id) > 0 else None
    enriched_value = dict(value)
    if release_id_int:
        enriched_value["releaseId"] = release_id_int
    if str(artist or "").strip():
        enriched_value["artist"] = str(artist).strip()
    if str(album or "").strip():
        enriched_value["album"] = str(album).strip()

    if release_id_int:
        saved = write_lyrics_discogs_cover_override(release_id_int, enriched_value)

    # Mirror every manually chosen cover to the Spotify-facing artist/album identity.
    # This is what lets shuffle.html reuse a cover without needing to rerun the
    # Discogs ownership matcher. For albums that are not owned, this identity is
    # the primary persistent key.
    if lyrics_album_cover_identity(artist, album):
        saved = write_lyrics_album_cover_override(artist, album, enriched_value)

    if not saved:
        raise ValueError("Provide either a Discogs releaseId or a valid artist/album identity.")
    return saved


def delete_saved_cover_override(release_id: Any = None, artist: Any = "", album: Any = "") -> None:
    deleted_any = False
    if str(release_id or "").isdigit() and int(release_id) > 0:
        delete_lyrics_discogs_cover_override(int(release_id))
        deleted_any = True
    if lyrics_album_cover_identity(artist, album):
        delete_lyrics_album_cover_override(artist, album)
        deleted_any = True
    if not deleted_any:
        raise ValueError("Provide either a Discogs releaseId or a valid artist/album identity.")


@app.route("/api/manual-cover", methods=["GET", "POST", "DELETE"])
@app.route("/api/lyrics/discogs-cover", methods=["GET", "POST", "DELETE"])
def lyrics_discogs_cover_override():
    admin_error = require_topster_admin_response()
    if admin_error is not None:
        return admin_error

    payload = request.get_json(silent=True) or {}
    release_id_raw = payload.get("releaseId") or request.args.get("release_id") or request.args.get("releaseId")
    artist = str(payload.get("artist") or request.args.get("artist") or "").strip()
    album = str(payload.get("album") or request.args.get("album") or "").strip()
    release_id = int(release_id_raw) if str(release_id_raw or "").isdigit() and int(release_id_raw) > 0 else None

    if release_id is None and not lyrics_album_cover_identity(artist, album):
        return jsonify({"ok": False, "error": "A valid Discogs releaseId or artist/album identity is required."}), 400

    try:
        if request.method == "GET":
            override = read_saved_cover_override(release_id, artist, album)
            return jsonify({
                "ok": True,
                "releaseId": release_id,
                "artist": artist,
                "album": album,
                "coverOverride": override,
            })

        if request.method == "DELETE" or bool(payload.get("reset")):
            delete_saved_cover_override(release_id, artist, album)
            return jsonify({
                "ok": True,
                "releaseId": release_id,
                "artist": artist,
                "album": album,
                "coverOverride": None,
            })

        value = {
            "imageUrl": payload.get("imageUrl") or payload.get("imageSrc"),
            "source": payload.get("source") or "Manual",
            "href": payload.get("href") or "",
            "savedAt": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        }
        override = write_saved_cover_override(value, release_id, artist, album)
        return jsonify({
            "ok": True,
            "releaseId": release_id,
            "artist": artist,
            "album": album,
            "coverOverride": override,
        })
    except ValueError as error:
        return jsonify({"ok": False, "error": str(error)}), 400
    except Exception as error:
        return jsonify({"ok": False, "error": f"Could not save the cover override: {error}"}), 500


def normalize_discogs_artist_for_lookup(value: Any) -> str:
    text = str(value or "").strip()
    text = re.sub(r"\s*\*+\s*$", "", text)
    text = re.sub(r"\s*\(\d+\)\s*$", "", text)
    text = re.sub(r'\s*["“][^"”]+["”]\s*', " ", text)
    return normalize_lyrics_match_text(re.sub(r"\s+", " ", text).strip())


def find_discogs_collection_album_record(
    collection_payload: dict[str, Any],
    collection_title: str,
    collection_artist: str,
) -> dict[str, Any] | None:
    title_key = normalize_lyrics_match_text(collection_title)
    artist_key = normalize_discogs_artist_for_lookup(collection_artist)
    if not title_key:
        return None

    title_matches: list[dict[str, Any]] = []
    for album in collection_payload.get("albums") if isinstance(collection_payload.get("albums"), list) else []:
        if not isinstance(album, dict):
            continue
        if normalize_lyrics_match_text(album.get("title")) != title_key:
            continue
        title_matches.append(album)
        if not artist_key:
            return album
        album_artists = album.get("artists") if isinstance(album.get("artists"), list) else [album.get("artist")]
        if any(normalize_discogs_artist_for_lookup(value) == artist_key for value in album_artists):
            return album

    return title_matches[0] if len(title_matches) == 1 else None


def discogs_composite_position_from_subtracks(sub_tracks: Any) -> str:
    positions = [
        str(entry.get("position") or "").strip().upper()
        for entry in (sub_tracks if isinstance(sub_tracks, list) else [])
        if isinstance(entry, dict) and str(entry.get("position") or "").strip()
    ]
    if not positions:
        return ""

    # Discogs represents composite songs in several ways:
    # A1.1/A1.2/... and B3.1/B3.2/... use numeric child sections, while
    # B3-I/B3-II/... uses Roman-numeral child sections. In both cases the
    # shared parent position (A1 or B3) is the actual song position.
    bases = [
        re.sub(r"(?:[-.](?:\d+|[IVXLCDM]+))$", "", position, flags=re.IGNORECASE)
        for position in positions
    ]
    if bases[0] and all(base == bases[0] for base in bases):
        return bases[0]

    sides = []
    for position in positions:
        match = re.match(r"^([A-Z]{1,3})(?=\d|$|[-.])", position)
        if match:
            sides.append(match.group(1))
    if sides and len(sides) == len(positions) and all(side == sides[0] for side in sides):
        return sides[0]
    return ""


def iter_discogs_release_track_titles(tracklist: Any):
    """Yield only song-level Discogs titles, not headings or movement sections.

    Discogs uses type_=index for both structural headings and composite works. An
    untimed index such as "Le Sacre Du Printemps" is only a heading, so recurse
    into its A/B children. A timed index such as Rush's "Cygnus X-1 Book II:
    Hemispheres" or "La Villa Strangiato" is the song itself; its A-I/A-II or
    B3-I/B3-II children are sections and must not become independent songs.
    """
    for entry in tracklist if isinstance(tracklist, list) else []:
        if not isinstance(entry, dict):
            continue
        title = str(entry.get("title") or "").strip()
        entry_type = str(entry.get("type") or "track").strip().lower()
        duration = str(entry.get("duration") or "").strip()
        sub_tracks = entry.get("subTracks") if isinstance(entry.get("subTracks"), list) else []

        if entry_type == "index":
            composite_position = discogs_composite_position_from_subtracks(sub_tracks)
            composite_song = bool(composite_position and re.search(r"\d", composite_position))
            if title and (duration or composite_song):
                # A timed index is a composite song. An untimed index is also
                # the song when its children are sections of one numbered
                # parent position (A1.1/A1.2 -> A1, B3.1/B3.2 -> B3).
                yield title
            elif sub_tracks:
                # Pure structural headings whose children are separate A1/A2,
                # B1/B2 tracks still recurse normally.
                yield from iter_discogs_release_track_titles(sub_tracks)
            continue

        if title and entry_type == "track":
            yield title
        if sub_tracks and not duration:
            yield from iter_discogs_release_track_titles(sub_tracks)


def lyrics_discogs_track_title_variants(value: Any) -> list[str]:
    raw = str(value or "").strip()
    if not raw:
        return []

    variants: list[str] = []
    seen: set[str] = set()

    def add(candidate: Any) -> None:
        text = re.sub(r"\s+", " ", str(candidate or "")).strip()
        key = normalize_lyrics_match_text(text)
        if not text or not key or key in seen:
            return
        seen.add(key)
        variants.append(text)

    add(raw)
    add(clean_lyrics_track_title(raw))
    add(re.sub(r"\s*[\[(][^\])]*[\])]\s*$", "", raw))
    add(re.sub(r"\s+(?:feat\.?|featuring)\s+.+$", "", raw, flags=re.IGNORECASE))

    dash_index = raw.find(" - ")
    if dash_index >= 3:
        add(raw[:dash_index])
    return variants


def lyrics_discogs_levenshtein_distance(left_value: Any, right_value: Any) -> int:
    left = str(left_value or "")
    right = str(right_value or "")
    if left == right:
        return 0
    if not left:
        return len(right)
    if not right:
        return len(left)

    previous = list(range(len(right) + 1))
    for i, left_char in enumerate(left, start=1):
        current = [i]
        for j, right_char in enumerate(right, start=1):
            current.append(
                min(
                    current[-1] + 1,
                    previous[j] + 1,
                    previous[j - 1] + (0 if left_char == right_char else 1),
                )
            )
        previous = current
    return previous[-1]


def discogs_track_title_match_score(current_title: Any, discogs_title: Any) -> float:
    current_variants = lyrics_discogs_track_title_variants(current_title)
    candidate_variants = lyrics_discogs_track_title_variants(discogs_title)
    if not current_variants or not candidate_variants:
        return 0.0

    best = 0.0
    for current_variant in current_variants:
        for candidate_variant in candidate_variants:
            current_key = normalize_lyrics_match_text(current_variant)
            candidate_key = normalize_lyrics_match_text(candidate_variant)
            if not current_key or not candidate_key:
                continue
            if current_key == candidate_key:
                return 1.0

            current_compact = current_key.replace(" ", "")
            candidate_compact = candidate_key.replace(" ", "")
            if current_compact and current_compact == candidate_compact:
                return 0.99

            shorter = current_compact if len(current_compact) <= len(candidate_compact) else candidate_compact
            longer = candidate_compact if len(current_compact) <= len(candidate_compact) else current_compact
            if len(shorter) >= 4 and longer.startswith(shorter):
                best = max(best, 0.93)

            left_tokens = set(current_key.split())
            right_tokens = set(candidate_key.split())
            if left_tokens and right_tokens:
                intersection = len(left_tokens & right_tokens)
                containment = intersection / max(1, min(len(left_tokens), len(right_tokens)))
                overlap = intersection / max(len(left_tokens), len(right_tokens))
                if containment == 1 and min(len(left_tokens), len(right_tokens)) >= 2:
                    best = max(best, 0.91)
                elif containment >= 0.8:
                    best = max(best, 0.84)
                elif overlap >= 0.6:
                    best = max(best, 0.72)

            if min(len(current_compact), len(candidate_compact)) >= 4:
                distance = lyrics_discogs_levenshtein_distance(current_compact, candidate_compact)
                max_length = max(len(current_compact), len(candidate_compact))
                if distance <= 1:
                    best = max(best, 0.90)
                elif distance <= 2 and max_length >= 8:
                    best = max(best, 0.78)

    return best


def discogs_release_track_match_score(release: dict[str, Any], current_track_title: str) -> float:
    if not current_track_title:
        return 0.0
    return max(
        (discogs_track_title_match_score(current_track_title, title) for title in iter_discogs_release_track_titles(release.get("tracklist"))),
        default=0.0,
    )


def discogs_release_has_side_positions(release: dict[str, Any]) -> bool:
    def positions(tracklist: Any):
        for entry in tracklist if isinstance(tracklist, list) else []:
            if not isinstance(entry, dict):
                continue
            position = str(entry.get("position") or "").strip()
            if position:
                yield position
            if isinstance(entry.get("subTracks"), list):
                yield from positions(entry.get("subTracks"))

    return any(re.match(r"^[A-Za-z]{1,3}(?:\d|$)", position) for position in positions(release.get("tracklist")))


def get_discogs_collection_payload_for_lyrics(username: str) -> dict[str, Any]:
    cached = read_discogs_collection_cache(username)
    if cached and int(cached.get("cacheVersion") or 0) == DISCOGS_COLLECTION_CACHE_VERSION:
        return cached
    payload = fetch_full_discogs_collection(username)
    write_discogs_collection_cache(username, payload)
    return payload


@app.route("/api/lyrics/discogs-vinyl-tracklist", methods=["GET"])
def lyrics_discogs_vinyl_tracklist():
    collection_title = str(request.args.get("collection_title") or "").strip()
    collection_artist = str(request.args.get("collection_artist") or "").strip()
    source_artist = str(request.args.get("artist") or "").strip()
    source_track_artist = str(request.args.get("track_artist") or "").strip()
    source_album = str(request.args.get("album") or "").strip()
    current_track_title = str(request.args.get("track") or "").strip()

    requested_collection_matches: list[dict[str, str]] = []
    raw_collection_matches = str(request.args.get("collection_matches") or "").strip()
    if raw_collection_matches:
        try:
            parsed_matches = json.loads(raw_collection_matches)
            if isinstance(parsed_matches, list):
                for item in parsed_matches[:16]:
                    if not isinstance(item, dict):
                        continue
                    title = str(item.get("title") or "").strip()
                    artist = str(item.get("artist") or "").strip()
                    if title:
                        requested_collection_matches.append({"title": title, "artist": artist})
        except json.JSONDecodeError:
            requested_collection_matches = []

    if collection_title:
        requested_collection_matches.insert(0, {"title": collection_title, "artist": collection_artist})

    deduped_requests: list[dict[str, str]] = []
    seen_request_keys: set[str] = set()
    for item in requested_collection_matches:
        key = f"{normalize_discogs_artist_for_lookup(item.get('artist'))}::{normalize_lyrics_match_text(item.get('title'))}"
        if not key or key in seen_request_keys:
            continue
        seen_request_keys.add(key)
        deduped_requests.append(item)

    if not deduped_requests:
        return discogs_collection_json_response({"ok": False, "error": "At least one matched Discogs collection title is required."}, 400)

    username = DISCOGS_COLLECTION_USERNAME
    try:
        collection_payload = get_discogs_collection_payload_for_lyrics(username)
    except Exception as error:
        return discogs_collection_json_response({"ok": False, "error": str(error)}, 502)

    matched_albums: list[dict[str, Any]] = []
    seen_album_keys: set[str] = set()
    for requested_match in deduped_requests:
        album = find_discogs_collection_album_record(
            collection_payload,
            requested_match.get("title", ""),
            requested_match.get("artist", ""),
        )
        if not album:
            continue
        album_key = f"{normalize_discogs_artist_for_lookup((album.get('artists') or [''])[0] if isinstance(album.get('artists'), list) and album.get('artists') else album.get('artist'))}::{normalize_lyrics_match_text(album.get('title'))}"
        if album_key in seen_album_keys:
            continue
        seen_album_keys.add(album_key)
        matched_albums.append(album)

    if not matched_albums:
        return discogs_collection_json_response(
            {
                "ok": True,
                "matched": False,
                "vinylFound": False,
                "message": "Album not owned.",
            }
        )

    candidate_releases: list[tuple[int, dict[str, Any], bool, dict[str, Any]]] = []
    seen_release_instances: set[tuple[int, int]] = set()

    def add_album_vinyl_release_ids(album: dict[str, Any], primary: bool) -> None:
        owned_releases = album.get("ownedReleases") if isinstance(album.get("ownedReleases"), list) else []
        for owned_release in owned_releases:
            if not isinstance(owned_release, dict) or not owned_release.get("vinyl"):
                continue
            release_id = owned_release.get("releaseId")
            if not str(release_id or "").isdigit():
                continue
            release_id_int = int(release_id)
            instance_id_raw = owned_release.get("instanceId")
            instance_id_int = int(instance_id_raw) if str(instance_id_raw or "").isdigit() else -1
            candidate_key = (release_id_int, instance_id_int)
            if candidate_key in seen_release_instances:
                continue
            seen_release_instances.add(candidate_key)
            candidate_releases.append((release_id_int, album, primary, owned_release))

    for album in matched_albums:
        add_album_vinyl_release_ids(album, True)

    # Related releases remain a fallback for container/multi-release ownership
    # cases. They are considered only when none of the exact collection matches
    # contains the currently playing song.
    related_albums: list[dict[str, Any]] = []
    related_artist_keys = {
        normalize_discogs_artist_for_lookup(source_artist),
        *{
            normalize_discogs_artist_for_lookup(artist)
            for album in matched_albums
            for artist in (album.get("artists") if isinstance(album.get("artists"), list) else [album.get("artist")])
        },
    }
    related_artist_keys.discard("")
    if related_artist_keys:
        for album in collection_payload.get("albums") if isinstance(collection_payload.get("albums"), list) else []:
            if not isinstance(album, dict) or album in matched_albums:
                continue
            album_artists = album.get("artists") if isinstance(album.get("artists"), list) else [album.get("artist")]
            if any(normalize_discogs_artist_for_lookup(value) in related_artist_keys for value in album_artists):
                related_albums.append(album)

    loaded_releases: list[tuple[float, float, int, dict[str, Any], dict[str, Any], dict[str, Any]]] = []
    errors: list[str] = []

    def load_candidates(candidates: list[tuple[int, dict[str, Any], bool, dict[str, Any]]]) -> None:
        for release_id, album, primary, owned_release in candidates:
            if len(loaded_releases) >= 20:
                break
            try:
                release = fetch_discogs_release(release_id)
                if not release.get("vinyl"):
                    continue
                track_score = discogs_release_track_match_score(release, current_track_title)
                score = track_score * 100.0
                # Distinguish separate Bob Dylan (and other artists') releases
                # containing the same song. For example Spotify's "Bootleg Series,
                # Vol 5 ... Rolling Thunder Revue" identifies the Rolling Thunder
                # Revue release by album name even though More Blood, More Tracks
                # also contains "Simple Twist of Fate". Require a distinctive
                # multiword release title wholly inside the Spotify album title.
                context_title = normalize_lyrics_match_text(source_album)
                release_title = normalize_lyrics_match_text(release.get("title") or album.get("title") or "")
                if (
                    len(release_title) >= 15
                    and len(release_title.split()) >= 3
                    and release_title in context_title
                ):
                    score += 35.0
                if primary:
                    score += 15.0
                if discogs_release_has_side_positions(release):
                    score += 5.0
                # If the same physical Discogs release exists in the collection more
                # than once, prefer the collection instance that actually has grading
                # filled in. This does not outweigh release/track matching.
                if str(owned_release.get("mediaCondition") or "").strip():
                    score += 0.25
                if str(owned_release.get("sleeveCondition") or "").strip():
                    score += 0.25
                loaded_releases.append((score, track_score, release_id, release, album, owned_release))
            except Exception as error:
                errors.append(f"Release {release_id}: {error}")

    load_candidates(list(candidate_releases))

    primary_has_track = any(track_score >= 0.55 for _score, track_score, _release_id, _release, _album, _owned_release in loaded_releases)
    if current_track_title and not primary_has_track:
        related_candidates: list[tuple[int, dict[str, Any], bool, dict[str, Any]]] = []
        before_instances = set(seen_release_instances)
        for album in related_albums:
            add_album_vinyl_release_ids(album, False)
        for candidate in candidate_releases:
            release_id = candidate[0]
            owned_release = candidate[3]
            instance_id_raw = owned_release.get("instanceId")
            instance_id_int = int(instance_id_raw) if str(instance_id_raw or "").isdigit() else -1
            if (release_id, instance_id_int) not in before_instances:
                related_candidates.append(candidate)
        load_candidates(related_candidates)

    if not loaded_releases:
        primary_album = matched_albums[0]
        return discogs_collection_json_response(
            {
                "ok": True,
                "matched": True,
                "vinylFound": False,
                "collectionAlbum": {
                    "title": primary_album.get("title"),
                    "artists": primary_album.get("artists") or [],
                    "year": primary_album.get("year"),
                },
                "message": "Album owned, but no owned vinyl release tracklist could be loaded.",
                "errors": errors[:5],
            }
        )

    loaded_releases.sort(key=lambda item: item[0], reverse=True)
    _score, _track_score, _release_id, selected_release, selected_album, selected_owned_release = loaded_releases[0]
    selected_owned_release = refresh_discogs_owned_release_conditions(
        username,
        selected_owned_release,
        collection_payload.get("conditionFieldNames") if isinstance(collection_payload.get("conditionFieldNames"), dict) else {},
    )

    # Release database metadata is shared by every owner, whereas media/sleeve
    # grading belongs to this exact collection instance. Merge the latter only
    # into this response; do not put private collection grading in release cache.
    selected_release = dict(selected_release)
    selected_release["mediaCondition"] = str(selected_owned_release.get("mediaCondition") or "").strip()
    selected_release["sleeveCondition"] = str(selected_owned_release.get("sleeveCondition") or "").strip()
    selected_release["collectionInstanceId"] = selected_owned_release.get("instanceId")

    selected_release_id = int(selected_release.get("releaseId") or 0) if str(selected_release.get("releaseId") or "").isdigit() else 0
    release_cover_override = read_lyrics_discogs_cover_override(selected_release_id) if selected_release_id > 0 else None
    if release_cover_override:
        # Existing v4 release-specific overrides predate the shared artist/album
        # cache. Mirror them lazily to both album-artist and track-artist Spotify
        # identities so shuffle.html can immediately reuse them.
        for mirror_artist in dict.fromkeys([source_track_artist, source_artist]):
            if not lyrics_album_cover_identity(mirror_artist, source_album):
                continue
            try:
                if not read_lyrics_album_cover_override(mirror_artist, source_album):
                    mirror_value = dict(release_cover_override)
                    if selected_release_id > 0:
                        mirror_value["releaseId"] = selected_release_id
                    mirror_value["artist"] = mirror_artist
                    mirror_value["album"] = source_album
                    write_lyrics_album_cover_override(mirror_artist, source_album, mirror_value)
            except Exception:
                pass

    response_payload = {
        "ok": True,
        "matched": True,
        "vinylFound": True,
        "collectionAlbum": {
            "title": selected_album.get("title"),
            "artists": selected_album.get("artists") or [],
            "year": selected_album.get("year"),
        },
        "matchedCollectionAlbums": [
            {
                "title": album.get("title"),
                "artists": album.get("artists") or [],
                "year": album.get("year"),
            }
            for album in matched_albums
        ],
        "sourceAlbum": source_album,
        "sourceArtist": source_artist,
        "discogsAuth": {
            "tokenConfigured": bool(collection_payload.get("discogsTokenConfigured")),
            "ownerAuthenticated": bool(collection_payload.get("authenticatedToDiscogs")),
            "authenticatedUsername": str(collection_payload.get("authenticatedDiscogsUsername") or ""),
            "collectionUsername": username,
            "conditionFields": collection_payload.get("conditionFieldNames") if isinstance(collection_payload.get("conditionFieldNames"), dict) else {},
        },
        "release": selected_release,
        "coverOverride": release_cover_override or read_lyrics_album_cover_override(source_artist, source_album),
    }
    return discogs_collection_json_response(response_payload)


def lyrics_manual_album_relation_key(value: Any) -> str:
    normalized = normalize_lyrics_match_text(value)
    return re.sub(r"\s+", "", normalized)


def lyrics_manual_album_identity(artist: Any, album: Any) -> str:
    artist_text = str(artist or "").strip()
    artist_text = re.sub(r"\s*\*+\s*$", "", artist_text)
    artist_text = re.sub(r"\s*\(\d+\)\s*$", "", artist_text)
    artist_text = re.sub(r'\s*["“][^"”]+["”]\s*', " ", artist_text)
    artist_key = lyrics_manual_album_relation_key(artist_text)
    album_key = lyrics_manual_album_relation_key(album)
    return f"{artist_key}::{album_key}" if album_key else ""


def parse_discogs_release_id_from_url(raw_url: Any) -> tuple[int, str]:
    url = str(raw_url or "").strip()
    try:
        parsed = urlparse(url)
    except Exception as error:
        raise ValueError("Enter a valid Discogs release URL.") from error
    host = (parsed.hostname or "").casefold().rstrip(".")
    if host not in {"discogs.com", "www.discogs.com"} and not host.endswith(".discogs.com"):
        raise ValueError("Enter a Discogs release URL from discogs.com.")
    match = re.search(r"/release/(\d+)(?:[-/]|$)", parsed.path, flags=re.IGNORECASE)
    if not match:
        raise ValueError("The Discogs link must point to a specific /release/<id> page.")
    return int(match.group(1)), url


def find_manual_discogs_ownership_override(artist: str, album: str) -> dict[str, Any] | None:
    identity = lyrics_manual_album_identity(artist, album)
    if not identity:
        return None
    for record in read_topster_discogs_ownership_overrides(DISCOGS_COLLECTION_USERNAME):
        if str(record.get("identity") or "") != identity:
            continue
        if str(record.get("state") or "").strip().lower() != "owned":
            return None
        release_id = record.get("releaseId")
        if str(release_id or "").isdigit() and int(release_id) > 0:
            return record
    return None


def build_manual_discogs_tracklist_payload(artist: str, album: str, record: dict[str, Any]) -> dict[str, Any]:
    release_id = int(record.get("releaseId") or 0)
    if release_id <= 0:
        raise ValueError("The saved Discogs ownership override does not contain a release ID.")
    release = dict(fetch_discogs_release(release_id))
    if not release.get("tracklist"):
        raise ValueError("The linked Discogs release does not contain a tracklist.")
    release["mediaCondition"] = ""
    release["sleeveCondition"] = ""
    cover_override = read_lyrics_discogs_cover_override(release_id) or read_lyrics_album_cover_override(artist, album)
    return {
        "ok": True,
        "matched": True,
        "vinylFound": True,
        "manualOwnership": True,
        "collectionAlbum": {
            "title": release.get("title") or album,
            "artists": release.get("artists") or ([artist] if artist else []),
            "year": release.get("year"),
        },
        "matchedCollectionAlbums": [],
        "sourceAlbum": album,
        "sourceArtist": artist,
        "release": release,
        "coverOverride": cover_override,
        "discogsAuth": {
            "tokenConfigured": bool(get_discogs_token()),
            "ownerAuthenticated": False,
            "authenticatedUsername": "",
            "collectionUsername": DISCOGS_COLLECTION_USERNAME,
            "conditionFields": {},
        },
    }


@app.route("/api/lyrics/discogs-manual-ownership", methods=["GET", "POST"])
def lyrics_discogs_manual_ownership():
    if request.method == "GET":
        artist = str(request.args.get("artist") or "").strip()
        album = str(request.args.get("album") or "").strip()
        if not album:
            return discogs_collection_json_response({"ok": False, "error": "Album is required."}, 400)
        record = find_manual_discogs_ownership_override(artist, album)
        if not record:
            return discogs_collection_json_response({"ok": True, "matched": False, "manualOwnership": False})
        try:
            payload = build_manual_discogs_tracklist_payload(artist, album, record)
            payload["override"] = record
            return discogs_collection_json_response(payload)
        except Exception as error:
            return discogs_collection_json_response({"ok": False, "error": str(error)}, 502)

    admin_error = require_topster_admin_response()
    if admin_error is not None:
        return admin_error

    payload = request.get_json(silent=True) or {}
    artist = str(payload.get("artist") or "").strip()
    album = str(payload.get("album") or "").strip()
    if not album:
        return discogs_collection_json_response({"ok": False, "error": "The currently playing album does not have a usable title."}, 400)
    try:
        release_id, release_url = parse_discogs_release_id_from_url(payload.get("releaseUrl") or payload.get("url"))
        release = fetch_discogs_release(release_id)
        if not release.get("tracklist"):
            raise ValueError("The linked Discogs release does not contain a tracklist.")
        identity = lyrics_manual_album_identity(artist, album)
        if not identity:
            raise ValueError("The currently playing album does not have a usable identity.")
        saved = write_topster_discogs_ownership_override(
            DISCOGS_COLLECTION_USERNAME,
            {
                "identity": identity,
                "artist": artist,
                "title": album,
                "state": "owned",
                "releaseId": release_id,
                "releaseUrl": release_url,
            },
        )
        response_payload = build_manual_discogs_tracklist_payload(artist, album, saved)
        response_payload["override"] = saved
        return discogs_collection_json_response(response_payload)
    except ValueError as error:
        return discogs_collection_json_response({"ok": False, "error": str(error)}, 400)
    except Exception as error:
        return discogs_collection_json_response({"ok": False, "error": str(error)}, 502)


@app.route("/topster-admin-login", methods=["GET", "POST"])
def topster_admin_login():
    next_url = safe_frontend_redirect_url(request.values.get("next"))

    if request.method == "POST":
        submitted_username = request.form.get("username", "")
        submitted_password = request.form.get("password", "")
        if not is_admin_ip_allowed():
            return "Topster admin login is not allowed from this IP address.", 403
        if not topster_admin_password_is_configured():
            return (
                "Topster admin password is not configured on the live backend. "
                "Set TOPSTER_ADMIN_PASSWORD in the backend hosting environment and restart/redeploy the service."
            ), 500
        if submitted_topster_credentials_are_valid(submitted_username, submitted_password):
            session.permanent = True
            session["topster_admin"] = True
            session["topster_admin_username"] = get_topster_admin_username()
            return remember_topster_admin_device(redirect(next_url))
        return "Invalid admin username or password.", 403

    if is_topster_admin():
        return redirect(next_url)

    escaped_next = next_url.replace('&', '&amp;').replace('"', '&quot;').replace('<', '&lt;').replace('>', '&gt;')

    return f"""
    <!doctype html>
    <html lang=\"en\">
    <head>
        <meta charset=\"utf-8\">
        <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">
        <title>Navincitron Admin Login</title>
        <style>
            body {{ background:#333; color:#fff; font-family:Arial,sans-serif; display:grid; place-items:center; min-height:100vh; margin:0; }}
            form {{ background:#444; border-radius:10px; padding:24px; width:min(420px, calc(100vw - 32px)); }}
            input {{ box-sizing:border-box; width:100%; padding:10px; margin:10px 0 16px; }}
            button {{ background:#40bcf4; border:0; border-radius:5px; color:white; cursor:pointer; padding:10px 18px; }}
        </style>
    </head>
    <body>
        <form method=\"post\">
            <h1>Navincitron Admin Login</h1>
            <p>Admin authentication is required for the Admin Hub, Lyrics, and all draft/grid pages.</p>
            {"<p style='color:#ffcf85;font-weight:bold;'>Admin password is not configured on this backend.</p>" if not topster_admin_password_is_configured() else ""}
            <input type=\"hidden\" name=\"next\" value=\"{escaped_next}\">
            <label for=\"username\">Admin username</label>
            <input id=\"username\" name=\"username\" type=\"text\" autocomplete=\"username\" autofocus required>
            <label for=\"password\">Admin password</label>
            <input id=\"password\" name=\"password\" type=\"password\" autocomplete=\"current-password\" required>
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
# History is scoped to each *loaded* shuffle.html page (not each 5-track game).
# A page refresh generates a fresh pageSessionId, resetting the no-repeat rule.
songguesser_page_histories: dict[str, dict[str, Any]] = {}
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


def spotify_accessible_playback_devices(sp: Any) -> list[dict[str, Any]]:
    """Only devices returned for the account authorized by this browser."""
    payload = sp.devices() or {}
    devices = payload.get("devices") if isinstance(payload, dict) else []
    return [device for device in (devices or []) if isinstance(device, dict) and device.get("id")]


def spotify_account_identity(sp: Any) -> tuple[str, str]:
    account = sp.me() or {}
    return (str(account.get("id") or ""), str(account.get("display_name") or account.get("id") or "Spotify account"))


def spotify_selected_device_id_for_account(sp: Any, validate_presence: bool = True) -> str | None:
    """Never use a stored device selected while a different account was logged in."""
    selected = str(session.get("spotify_playback_device_id") or "").strip()
    if not selected:
        return None
    account_id, _ = spotify_account_identity(sp)
    if not account_id or account_id != str(session.get("spotify_playback_account_id") or ""):
        session.pop("spotify_playback_device_id", None)
        session.pop("spotify_playback_account_id", None)
        return None
    if validate_presence:
        matching = next((d for d in spotify_accessible_playback_devices(sp) if d.get("id") == selected), None)
        if not matching:
            raise RuntimeError("The selected Spotify device is no longer available to this Spotify account. Refresh the device list and select an available player.")
        if matching.get("is_restricted"):
            raise RuntimeError("The selected Spotify device is restricted and cannot receive Spotify playback commands. Select another player.")
    return selected


@app.route("/api/spotify/devices", methods=["GET"])
def spotify_available_playback_devices():
    try:
        sp = get_spotify_client()
        account_id, display_name = spotify_account_identity(sp)
        devices = spotify_accessible_playback_devices(sp)
        selected_id = spotify_selected_device_id_for_account(sp, validate_presence=False)
        return jsonify({
            "ok": True,
            "accountName": display_name,
            "devices": [
                {
                    "id": str(device["id"]),
                    "name": str(device.get("name") or "Unnamed Spotify device"),
                    "type": str(device.get("type") or ""),
                    "isActive": bool(device.get("is_active")),
                    "isRestricted": bool(device.get("is_restricted")),
                }
                for device in devices
            ],
            "selectedDeviceId": selected_id or "",
        })
    except SpotifyLoginRequired as error:
        return jsonify({"ok": False, "error": str(error)}), 401
    except Exception as error:
        return jsonify({"ok": False, "error": f"Could not list Spotify playback devices: {error}"}), 503


@app.route("/api/spotify/device", methods=["POST"])
def spotify_choose_playback_device():
    try:
        sp = get_spotify_client()
        payload = request.get_json(silent=True) or {}
        selected = str(payload.get("deviceId") or "").strip()
        account_id, _ = spotify_account_identity(sp)
        if selected:
            device = next((d for d in spotify_accessible_playback_devices(sp) if str(d.get("id")) == selected), None)
            if not device:
                return jsonify({"ok": False, "error": "That Spotify device was not found under the current account. Refresh devices and try again."}), 400
            if device.get("is_restricted"):
                return jsonify({"ok": False, "error": "Spotify marks that device as restricted. Choose another player."}), 400
            session["spotify_playback_device_id"] = selected
            session["spotify_playback_account_id"] = account_id
            session.permanent = True
            device_name = str(device.get("name") or "Unnamed Spotify device")
        else:
            session.pop("spotify_playback_device_id", None)
            session.pop("spotify_playback_account_id", None)
            device_name = "Automatic (Spotify active device)"
        # Selection is routing only. Do not transfer playback or interrupt audio.
        return jsonify({"ok": True, "selectedDeviceId": selected, "name": device_name})
    except SpotifyLoginRequired as error:
        return jsonify({"ok": False, "error": str(error)}), 401
    except Exception as error:
        return jsonify({"ok": False, "error": f"Could not select Spotify device: {error}"}), 503


# lyrics.html uses Spotify only to identify the user's current track. Genius
# metadata and the official Genius lyrics/annotation embed are resolved here so
# no Spotify or Genius credentials are exposed to browser JavaScript.
GENIUS_LOOKUP_CACHE: dict[str, dict[str, Any]] = {}
GENIUS_LOOKUP_CACHE_LOCK = threading.Lock()
GENIUS_LOOKUP_CACHE_MAX_ITEMS = 500
GENIUS_LOOKUP_CACHE_VERSION = 2
GENIUS_MATCH_TTL_SECONDS = 7 * 24 * 60 * 60
GENIUS_MISS_TTL_SECONDS = 60 * 60


def lyrics_genius_album_links_redis_key() -> str:
    return f"{TOPSTER_REDIS_KEY_PREFIX.strip(':') or 'navincitron:topster'}:lyrics-genius-album-links"


def normalize_lyrics_genius_album_link(value: Any) -> dict[str, Any] | None:
    if not isinstance(value, dict):
        return None
    artist = str(value.get("artist") or "").strip()
    album = str(value.get("album") or "").strip()
    identity = str(value.get("identity") or lyrics_manual_album_identity(artist, album)).strip()
    url = str(value.get("url") or "").strip()
    album_id_raw = value.get("albumId")
    album_id = int(album_id_raw) if str(album_id_raw or "").isdigit() and int(album_id_raw) > 0 else None
    if not identity or not album or not url or not album_id:
        return None
    try:
        parsed = urlparse(url)
    except Exception:
        return None
    host = (parsed.hostname or "").casefold().rstrip(".")
    if host not in {"genius.com", "www.genius.com"} or not parsed.path.casefold().startswith("/albums/"):
        return None

    tracks: list[dict[str, Any]] = []
    for raw_track in value.get("tracks") if isinstance(value.get("tracks"), list) else []:
        if not isinstance(raw_track, dict):
            continue
        song_id_raw = raw_track.get("songId") or raw_track.get("id")
        song_id = int(song_id_raw) if str(song_id_raw or "").isdigit() and int(song_id_raw) > 0 else None
        title = str(raw_track.get("title") or "").strip()
        if not song_id or not title:
            continue
        tracks.append({
            "songId": song_id,
            "title": title,
            "url": str(raw_track.get("url") or "").strip(),
            "position": str(raw_track.get("position") or "").strip(),
        })
    if not tracks:
        return None
    return {
        "identity": identity,
        "artist": artist,
        "album": album,
        "url": url,
        "albumId": album_id,
        "tracks": tracks,
        "savedAt": str(value.get("savedAt") or time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())).strip(),
    }


def read_lyrics_genius_album_link(artist: str, album: str) -> dict[str, Any] | None:
    identity = lyrics_manual_album_identity(artist, album)
    if not identity:
        return None
    with LYRICS_GENIUS_ALBUM_LINKS_LOCK:
        if identity in LYRICS_GENIUS_ALBUM_LINK_MEMORY_CACHE:
            cached = LYRICS_GENIUS_ALBUM_LINK_MEMORY_CACHE[identity]
            return dict(cached) if isinstance(cached, dict) else None

    record = None
    digest = hashlib.sha256(identity.encode("utf-8", errors="ignore")).hexdigest()
    if topster_redis_is_configured():
        try:
            client = get_topster_redis_client()
            if client is not None:
                raw = client.hget(lyrics_genius_album_links_redis_key(), digest)
                if raw:
                    record = normalize_lyrics_genius_album_link(json.loads(raw))
        except Exception:
            record = None
    if record is None:
        try:
            with LYRICS_GENIUS_ALBUM_LINKS_LOCK:
                data = read_json_file(LYRICS_GENIUS_ALBUM_LINKS_FILE, {})
            if isinstance(data, dict):
                record = normalize_lyrics_genius_album_link(data.get(digest))
        except Exception:
            record = None

    with LYRICS_GENIUS_ALBUM_LINKS_LOCK:
        LYRICS_GENIUS_ALBUM_LINK_MEMORY_CACHE[identity] = dict(record) if isinstance(record, dict) else None
    return record


def write_lyrics_genius_album_link(value: dict[str, Any]) -> dict[str, Any]:
    normalized = normalize_lyrics_genius_album_link(value)
    if not normalized:
        raise ValueError("A valid Genius album link and tracklist are required.")
    identity = normalized["identity"]
    digest = hashlib.sha256(identity.encode("utf-8", errors="ignore")).hexdigest()
    redis_saved = False
    if topster_redis_is_configured():
        client = get_topster_redis_client()
        if client is None:
            raise RuntimeError(TOPSTER_REDIS_CLIENT_ERROR or "Redis is configured but unavailable.")
        client.hset(lyrics_genius_album_links_redis_key(), digest, json.dumps(normalized, ensure_ascii=False))
        redis_saved = True
    try:
        with LYRICS_GENIUS_ALBUM_LINKS_LOCK:
            data = read_json_file(LYRICS_GENIUS_ALBUM_LINKS_FILE, {})
            if not isinstance(data, dict):
                data = {}
            data[digest] = normalized
            write_json_file(LYRICS_GENIUS_ALBUM_LINKS_FILE, data)
            LYRICS_GENIUS_ALBUM_LINK_MEMORY_CACHE[identity] = dict(normalized)
    except Exception:
        if not redis_saved:
            raise
        with LYRICS_GENIUS_ALBUM_LINKS_LOCK:
            LYRICS_GENIUS_ALBUM_LINK_MEMORY_CACHE[identity] = dict(normalized)
    return normalized


def validate_genius_album_url(raw_url: Any) -> str:
    """Validate and canonicalize a Genius album URL.

    Genius commonly exposes both /albums/... and /amp/albums/... variants.  The
    latter is a valid public Genius URL, but the album API/matching code should
    operate on the canonical non-AMP path so URL comparisons remain stable.
    """
    url = str(raw_url or "").strip()
    try:
        parsed = urlparse(url)
    except Exception as error:
        raise ValueError("Enter a valid Genius album URL.") from error

    host = (parsed.hostname or "").casefold().rstrip(".")
    path = parsed.path or ""
    path_folded = path.casefold()

    if host not in {"genius.com", "www.genius.com"}:
        raise ValueError("Enter a Genius album URL in the form https://genius.com/albums/Artist/Album.")

    if path_folded.startswith("/amp/albums/"):
        path = path[4:]  # /amp/albums/... -> /albums/...
        path_folded = path.casefold()

    if not path_folded.startswith("/albums/"):
        raise ValueError("Enter a Genius album URL in the form https://genius.com/albums/Artist/Album.")

    # Store a stable canonical Genius URL. Query/fragment components are not
    # needed for album identity and can make exact-path matching unreliable.
    canonical = parsed._replace(scheme="https", netloc="genius.com", path=path.rstrip("/"), params="", query="", fragment="")
    return canonical.geturl()


def genius_album_id_from_page_html(html: str) -> int | None:
    decoded = html_unescape(str(html or ""))
    patterns = (
        r'"album_ids"\s*:\s*\[\s*(\d+)',
        r'\\"album_ids\\"\s*:\s*\[\s*(\d+)',
        r'"album_id"\s*:\s*(\d+)',
        r'"albumId"\s*:\s*(\d+)',
        r'/api/albums/(\d+)',
    )
    for pattern in patterns:
        match = re.search(pattern, decoded, flags=re.IGNORECASE)
        if match and int(match.group(1)) > 0:
            return int(match.group(1))
    return None


def fetch_genius_album_id_from_url(
    url: str,
    context_artist: str = "",
    context_album: str = "",
    context_track: str = "",
) -> int:
    """Resolve a Genius album URL without depending on Genius page HTML.

    Render/VPS requests to public genius.com album pages can receive HTTP 403.
    The direct HTML read remains a fast path, but the durable fallback uses the
    authenticated api.genius.com search/song endpoints and matches the returned
    song's album metadata back to the exact album URL/title supplied by the user.
    """
    validated_url = validate_genius_album_url(url)
    headers = {
        "Accept": "text/html,application/xhtml+xml",
        "User-Agent": "Mozilla/5.0 (compatible; NavincitronLyrics/1.3; +https://www.navincitron.com)",
    }
    page_error = None
    try:
        with urlopen(Request(validated_url, headers=headers), timeout=15) as response:
            html = response.read(6 * 1024 * 1024).decode("utf-8", errors="replace")
        album_id = genius_album_id_from_page_html(html)
        if album_id:
            return album_id
    except Exception as error:
        # Genius commonly denies datacenter HTML requests with 403. Do not
        # consider that fatal; the official API fallback below is the primary
        # resolution path in production.
        page_error = error

    if not get_genius_access_token():
        detail = f" ({page_error})" if page_error else ""
        raise RuntimeError(
            "Could not determine the Genius album ID because the album page "
            f"could not be read and GENIUS_ACCESS_TOKEN is unavailable{detail}."
        )

    parsed = urlparse(validated_url)
    parts = [unquote(part) for part in parsed.path.split("/") if part]
    url_artist_hint = parts[1].replace("-", " ") if len(parts) > 1 else ""
    url_album_hint = parts[2].replace("-", " ") if len(parts) > 2 else ""
    target_path = parsed.path.rstrip("/").casefold()
    target_artist_key = normalize_lyrics_match_text(url_artist_hint or context_artist)
    target_album_key = normalize_lyrics_match_text(url_album_hint)
    context_album_key = normalize_lyrics_match_text(clean_lyrics_album_title(context_album))

    # Put the distinctive album-slug words first. This matters for titles such
    # as "Live/Hhaï", where a broad "Magma Live Hhai" search can bury the album's
    # songs beneath unrelated "live" results.
    url_album_tokens = [token for token in normalize_lyrics_match_text(url_album_hint).split() if token]
    distinctive_tokens = [token for token in url_album_tokens if len(token) >= 4 and token not in {"live", "album", "deluxe", "remastered"}]

    # Genius search is song-centric, not album-centric.  When the user links the
    # album from lyrics.html we already know the currently playing track, which
    # is a much stronger way to discover one song from the requested album and
    # then read its album.id from /songs/<id>.  Strip common featured-artist
    # suffixes used by Spotify so they do not dilute that exact-song query.
    track_hint = clean_lyrics_track_title(context_track)
    track_hint = re.sub(
        r"\s*[\[(](?:feat(?:uring)?\.?|ft\.?|with)\b[^\])]*[\])]\s*",
        " ",
        track_hint,
        flags=re.IGNORECASE,
    )
    track_hint = re.sub(r"\s+", " ", track_hint).strip()

    queries: list[str] = []
    def add_query(*values: Any) -> None:
        query = " ".join(str(value or "").strip() for value in values if str(value or "").strip())
        query = re.sub(r"\s+", " ", query).strip()
        if query and query.casefold() not in {existing.casefold() for existing in queries}:
            queries.append(query)

    if track_hint:
        # Exact current-track searches go first because /search ranks songs, not
        # albums.  A matching song's detailed API payload contains album.id.
        add_query(context_artist or url_artist_hint, track_hint)
        add_query(track_hint, context_artist or url_artist_hint)
        add_query(track_hint)

    for token in distinctive_tokens:
        add_query(url_artist_hint or context_artist, token)
        add_query(token, url_artist_hint or context_artist)
    add_query(url_artist_hint or context_artist, url_album_hint)
    add_query(context_artist, context_album)
    add_query(url_album_hint, url_artist_hint or context_artist)
    add_query(url_artist_hint or context_artist, clean_lyrics_album_title(context_album))

    best_candidate: tuple[float, int] | None = None
    seen_song_ids: set[int] = set()

    for query in queries[:12]:
        try:
            search_payload = genius_search_request(query)
        except Exception:
            continue

        for hit in genius_song_hits(search_payload)[:20]:
            song_id_raw = hit.get("id")
            if not str(song_id_raw or "").isdigit():
                continue
            song_id = int(song_id_raw)
            if song_id in seen_song_ids:
                continue
            seen_song_ids.add(song_id)

            song = hit
            album_data = hit.get("album") if isinstance(hit.get("album"), dict) else None
            if not album_data:
                try:
                    details_payload = genius_song_request(song_id)
                    response = details_payload.get("response")
                    detailed_song = response.get("song") if isinstance(response, dict) else None
                    if isinstance(detailed_song, dict):
                        song = detailed_song
                        album_data = song.get("album") if isinstance(song.get("album"), dict) else None
                except Exception:
                    album_data = None
            if not album_data:
                continue

            album_id_raw = album_data.get("id")
            if not str(album_id_raw or "").isdigit() or int(album_id_raw) <= 0:
                continue
            album_id = int(album_id_raw)
            album_url = str(album_data.get("url") or "").strip()
            album_name = str(album_data.get("name") or album_data.get("full_title") or "").strip()

            if album_url:
                try:
                    if urlparse(album_url).path.rstrip("/").casefold() == target_path:
                        return album_id
                except Exception:
                    pass

            candidate_album_key = normalize_lyrics_match_text(album_name)
            candidate_artist_names: list[str] = []
            album_artist = album_data.get("artist")
            if isinstance(album_artist, dict) and album_artist.get("name"):
                candidate_artist_names.append(str(album_artist.get("name")))
            primary_artist = song.get("primary_artist")
            if isinstance(primary_artist, dict) and primary_artist.get("name"):
                candidate_artist_names.append(str(primary_artist.get("name")))
            candidate_artist_key = normalize_lyrics_match_text(" ".join(candidate_artist_names))

            album_score = 0.0
            if target_album_key and candidate_album_key == target_album_key:
                album_score = 1.0
            elif target_album_key:
                album_score = lyrics_token_overlap(target_album_key, candidate_album_key)
            if context_album_key and candidate_album_key == context_album_key:
                album_score = max(album_score, 0.92)

            artist_score = 0.0
            if target_artist_key and candidate_artist_key:
                if target_artist_key == candidate_artist_key:
                    artist_score = 1.0
                elif target_artist_key in candidate_artist_key or candidate_artist_key in target_artist_key:
                    artist_score = 0.9
                else:
                    artist_score = lyrics_token_overlap(target_artist_key, candidate_artist_key)

            total_score = album_score * 0.75 + artist_score * 0.25
            if album_score >= 0.92 and artist_score >= 0.75:
                return album_id
            if best_candidate is None or total_score > best_candidate[0]:
                best_candidate = (total_score, album_id)

    if best_candidate and best_candidate[0] >= 0.82:
        return best_candidate[1]

    detail = f" The direct Genius page request failed with {page_error}." if page_error else ""
    raise RuntimeError(
        "Could not determine the Genius album ID from that link using either "
        f"the album page or the Genius API.{detail}"
    )


def fetch_genius_album_tracks(album_id: int) -> list[dict[str, Any]]:
    access_token = get_genius_access_token()
    if not access_token:
        raise RuntimeError("Genius album linking requires GENIUS_ACCESS_TOKEN on the backend.")
    tracks: list[dict[str, Any]] = []
    page = 1
    while page <= 20:
        payload = genius_json_request(
            f"https://api.genius.com/albums/{int(album_id)}/tracks?per_page=50&page={page}&text_format=plain",
            access_token,
        )
        response = payload.get("response") if isinstance(payload, dict) else None
        raw_tracks = response.get("tracks") if isinstance(response, dict) and isinstance(response.get("tracks"), list) else []
        for raw_track in raw_tracks:
            if not isinstance(raw_track, dict):
                continue
            song = raw_track.get("song") if isinstance(raw_track.get("song"), dict) else raw_track
            song_id_raw = song.get("id")
            title = str(song.get("title") or song.get("title_with_featured") or "").strip()
            if not str(song_id_raw or "").isdigit() or not title:
                continue
            tracks.append({
                "songId": int(song_id_raw),
                "title": title,
                "url": str(song.get("url") or "").strip(),
                "position": str(raw_track.get("number") or raw_track.get("track_number") or len(tracks) + 1),
            })
        next_page = response.get("next_page") if isinstance(response, dict) else None
        if not next_page or not raw_tracks:
            break
        try:
            page = int(next_page)
        except (TypeError, ValueError):
            page += 1
    if not tracks:
        raise RuntimeError("Genius returned no tracks for that album page.")
    return tracks


def track_album_artist_for_manual_link(track: dict[str, Any]) -> str:
    album_artists = track.get("albumArtists") if isinstance(track.get("albumArtists"), list) else []
    if album_artists:
        return str(album_artists[0] or "").strip()
    artists = track.get("artists") if isinstance(track.get("artists"), list) else []
    if artists:
        return str(artists[0] or "").strip()
    return str(track.get("albumArtist") or track.get("artist") or "").split(",", 1)[0].strip()


def lookup_genius_song_from_manual_album_link(track: dict[str, Any]) -> dict[str, Any] | None:
    artist = track_album_artist_for_manual_link(track)
    album = str(track.get("album") or "").strip()
    mapping = read_lyrics_genius_album_link(artist, album)
    if not mapping:
        return None
    title = str(track.get("title") or "").strip()
    best_track = None
    best_score = 0.0
    for candidate in mapping.get("tracks") if isinstance(mapping.get("tracks"), list) else []:
        score = discogs_track_title_match_score(title, candidate.get("title"))
        if score > best_score:
            best_score = score
            best_track = candidate
    if best_track is None or best_score < 0.55:
        return None
    song_id = int(best_track.get("songId") or 0)
    if song_id <= 0:
        return None
    try:
        details_payload = genius_song_request(song_id)
        response = details_payload.get("response")
        song = response.get("song") if isinstance(response, dict) else None
        if isinstance(song, dict):
            result = build_genius_song_payload(song)
            result["manualAlbumUrl"] = mapping.get("url")
            return result
    except Exception:
        pass
    stub = {
        "id": song_id,
        "title": best_track.get("title") or title,
        "url": best_track.get("url") or "",
        "primary_artist": {"name": artist},
        "album": {"name": album},
    }
    result = build_genius_song_payload(stub)
    result["manualAlbumUrl"] = mapping.get("url")
    return result


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
        if error.code == 401:
            raise RuntimeError(
                "Genius rejected the configured access token (HTTP 401). "
                "Generate a Client Access Token in the Genius API Clients dashboard "
                "and update GENIUS_ACCESS_TOKEN."
            ) from error
        if error.code == 429:
            retry_after = str(error.headers.get("Retry-After") or "").strip() if error.headers else ""
            retry_note = f" Retry-After: {retry_after}." if retry_after else ""
            raise RuntimeError(
                "Genius API rate limit reached (HTTP 429)." + retry_note
            ) from error
        if error.code == 403:
            raise RuntimeError(
                "Genius API request was forbidden (HTTP 403). This is distinct from HTTP 401 "
                "and is not automatically classified as token expiration."
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



GENIUS_PAGE_MAX_BYTES = 8 * 1024 * 1024
GENIUS_REFERENT_PATH_PATTERN = re.compile(r"^/(\d+)(?:/|$)")
GENIUS_SAFE_LYRIC_TAGS = {"a", "b", "br", "div", "em", "genius-referent", "i", "p", "span", "strong"}
GENIUS_VOID_TAGS = {"br", "hr", "img", "input", "link", "meta", "source", "wbr"}
GENIUS_SECTION_HEADING_PATTERN = re.compile(r"^(\s*)(\[[^\[\]\r\n]{1,160}\])(\s*)$")


def render_genius_section_heading_text(value: Any) -> str:
    """Escape lyric text while retaining Genius-style [Verse]/[Chorus] labels verbatim."""
    text = str(value or "")
    match = GENIUS_SECTION_HEADING_PATTERN.fullmatch(text)
    if not match:
        return html_escape(text, quote=False)
    leading, heading, trailing = match.groups()
    return (
        html_escape(leading, quote=False)
        + '<span class="lyrics-genius-section-heading">'
        + html_escape(heading, quote=False)
        + "</span>"
        + html_escape(trailing, quote=False)
    )


def escape_genius_fallback_lyrics(value: Any) -> str:
    """Escape fallback transcription without changing words or bracketed section labels."""
    text = str(value or "")
    if not text:
        return ""
    rendered: list[str] = []
    for raw_line in text.splitlines(keepends=True):
        body = raw_line.rstrip("\r\n")
        has_line_break = len(body) != len(raw_line)
        rendered.append(render_genius_section_heading_text(body))
        if has_line_break:
            rendered.append("<br>\n")
    # splitlines(keepends=True) returns nothing only for an empty string, handled above.
    return "".join(rendered)


def genius_referent_id_from_url(raw_url: Any) -> int | None:
    value = str(raw_url or "").strip()
    if not value:
        return None
    try:
        parsed = urlparse(value if value.startswith(("http://", "https://")) else "https://genius.com" + (value if value.startswith("/") else "/" + value))
    except Exception:
        return None
    host = (parsed.hostname or "").casefold().rstrip(".")
    if host not in {"genius.com", "www.genius.com"}:
        return None
    match = GENIUS_REFERENT_PATH_PATTERN.match(parsed.path or "")
    if not match:
        return None
    try:
        referent_id = int(match.group(1))
    except (TypeError, ValueError):
        return None
    return referent_id if referent_id > 0 else None


def normalize_genius_page_url(raw_url: Any, song_id: int) -> str:
    value = str(raw_url or "").strip()
    if value:
        try:
            parsed = urlparse(value)
            host = (parsed.hostname or "").casefold().rstrip(".")
            if parsed.scheme == "https" and host in {"genius.com", "www.genius.com"}:
                return value
        except Exception:
            pass
    return f"https://genius.com/songs/{int(song_id)}"


class GeniusLyricsPageParser(HTMLParser):
    """Extract only Genius's lyric containers and mark annotation referents.

    The public Genius page is never returned wholesale. Only a small allowlist of
    lyric-formatting tags is retained, attributes are rebuilt from scratch, and
    annotation links are converted into same-page referent controls for lyrics.js.
    """

    def __init__(self) -> None:
        super().__init__(convert_charrefs=False)
        self.containers: list[str] = []
        self._parts: list[str] = []
        self._container_depth = 0
        self._skip_depth = 0
        self._emitted_tags: list[str] = []

    @staticmethod
    def _attrs(attrs: list[tuple[str, str | None]]) -> dict[str, str]:
        return {str(key or "").casefold(): str(value or "") for key, value in attrs}

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        tag = str(tag or "").casefold()
        attr_map = self._attrs(attrs)

        if self._container_depth <= 0:
            if tag == "div" and "data-lyrics-container" in attr_map:
                self._container_depth = 1
                self._parts = []
                self._emitted_tags = []
            return

        if self._skip_depth > 0:
            if tag not in GENIUS_VOID_TAGS:
                self._skip_depth += 1
            return

        if attr_map.get("data-exclude-from-selection", "").casefold() == "true":
            if tag not in GENIUS_VOID_TAGS:
                self._skip_depth = 1
            return

        if tag == "div":
            self._container_depth += 1

        if tag not in GENIUS_SAFE_LYRIC_TAGS:
            return

        if tag == "br":
            self._parts.append("<br>")
            return

        if tag in {"a", "genius-referent"}:
            href = attr_map.get("href", "").strip()
            raw_referent_id = attr_map.get("data-genius-referent-id", "").strip()
            referent_id = int(raw_referent_id) if raw_referent_id.isdigit() and int(raw_referent_id) > 0 else genius_referent_id_from_url(href)
            if referent_id:
                absolute_href = (
                    href if href.startswith("https://")
                    else "https://genius.com" + (href if href.startswith("/") else "/" + href)
                    if href
                    else "https://genius.com"
                )
                self._parts.append(
                    '<a class="lyrics-genius-annotated-fragment" '
                    f'data-genius-referent-id="{referent_id}" '
                    f'href="{html_escape(absolute_href, quote=True)}">'
                )
                self._emitted_tags.append("a")
                return

            safe_href = ""
            if href:
                try:
                    parsed = urlparse(href if href.startswith(("http://", "https://")) else "https://genius.com" + (href if href.startswith("/") else "/" + href))
                    if parsed.scheme == "https" and (parsed.hostname or "").casefold().rstrip(".") in {"genius.com", "www.genius.com"}:
                        safe_href = parsed.geturl()
                except Exception:
                    safe_href = ""
            if safe_href:
                self._parts.append(
                    f'<a href="{html_escape(safe_href, quote=True)}" target="_blank" rel="noopener noreferrer">'
                )
                self._emitted_tags.append("a")
            else:
                self._parts.append("<span>")
                self._emitted_tags.append("span")
            return

        self._parts.append(f"<{tag}>")
        self._emitted_tags.append(tag)

    def handle_startendtag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        self.handle_starttag(tag, attrs)
        if str(tag or "").casefold() not in GENIUS_VOID_TAGS:
            self.handle_endtag(tag)

    def handle_endtag(self, tag: str) -> None:
        tag = str(tag or "").casefold()
        if self._container_depth <= 0:
            return

        if self._skip_depth > 0:
            self._skip_depth -= 1
            return

        if tag == "div" and self._container_depth == 1:
            content = "".join(self._parts).strip()
            if content:
                self.containers.append(content)
            self._parts = []
            self._emitted_tags = []
            self._container_depth = 0
            return

        if tag == "div":
            self._container_depth = max(1, self._container_depth - 1)

        if tag not in GENIUS_SAFE_LYRIC_TAGS or tag == "br":
            return
        if self._emitted_tags:
            emitted_tag = self._emitted_tags.pop()
            self._parts.append(f"</{emitted_tag}>")

    def handle_data(self, data: str) -> None:
        if self._container_depth > 0 and self._skip_depth <= 0:
            self._parts.append(render_genius_section_heading_text(data))

    def handle_entityref(self, name: str) -> None:
        if self._container_depth > 0 and self._skip_depth <= 0:
            self._parts.append(f"&{html_escape(str(name or ''), quote=False)};")

    def handle_charref(self, name: str) -> None:
        if self._container_depth > 0 and self._skip_depth <= 0:
            self._parts.append(f"&#{html_escape(str(name or ''), quote=False)};")


def extract_genius_lyrics_html(page_html: str) -> str:
    parser = GeniusLyricsPageParser()
    parser.feed(str(page_html or ""))
    parser.close()
    if not parser.containers:
        raise RuntimeError("Genius song page did not contain readable lyric containers.")
    return "\n".join(f'<div class="lyrics-genius-verse">{content}</div>' for content in parser.containers)


def genius_public_json_request(url: str, timeout: float = 4.0) -> dict[str, Any]:
    """Read one of Genius's public genius.com/api JSON endpoints.

    These endpoints do not require the developer Client Access Token.  Keeping
    lyrics retrieval on a JSON endpoint avoids depending on the normal Genius
    HTML song page, which may be challenged/blocked for server-side requests.
    """
    headers = {
        "Accept": "application/json, text/plain, */*",
        "Accept-Language": "en-US,en;q=0.9",
        "Referer": "https://genius.com/",
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/140.0.0.0 Safari/537.36"
        ),
        "X-Requested-With": "XMLHttpRequest",
    }
    public_request = Request(url, headers=headers)
    try:
        with urlopen(public_request, timeout=max(1.0, float(timeout))) as response:
            payload = json.loads(response.read().decode("utf-8", errors="replace"))
    except HTTPError as error:
        raise RuntimeError(f"Genius public API request failed with HTTP {error.code}.") from error
    except URLError as error:
        raise RuntimeError(f"Could not reach the Genius public API: {error.reason}") from error
    except json.JSONDecodeError as error:
        raise RuntimeError("Genius public API returned unreadable JSON.") from error

    if not isinstance(payload, dict):
        raise RuntimeError("Genius public API returned an invalid JSON response.")

    meta = payload.get("meta")
    if isinstance(meta, dict):
        try:
            status = int(meta.get("status") or 0)
        except (TypeError, ValueError):
            status = 0
        if status >= 400:
            message = str(meta.get("message") or "Genius public API request failed.").strip()
            raise RuntimeError(f"Genius public API error {status}: {message}")
    return payload


def genius_page_data_path(song: dict[str, Any]) -> str:
    """Build the page_path expected by Genius's public /api/page_data endpoint."""
    song_path = str(song.get("path") or "").strip()
    if not song_path:
        try:
            song_path = urlparse(str(song.get("url") or "")).path
        except Exception:
            song_path = ""
    song_path = "/" + song_path.lstrip("/") if song_path else ""

    primary_artist = song.get("primary_artist")
    artist_slug = ""
    if isinstance(primary_artist, dict):
        artist_slug = str(primary_artist.get("slug") or "").strip().strip("/")
        if not artist_slug:
            artist_url = str(primary_artist.get("url") or "").strip()
            try:
                artist_path = urlparse(artist_url).path.strip("/")
            except Exception:
                artist_path = ""
            if artist_path.casefold().startswith("artists/"):
                artist_slug = artist_path.split("/", 1)[1].strip("/")

    raw_song_path = song_path.lstrip("/")
    if raw_song_path.casefold().endswith("-lyrics"):
        raw_song_path = raw_song_path[:-7]

    if not raw_song_path:
        raise RuntimeError("Genius song metadata did not include a usable song path.")
    if not artist_slug:
        raise RuntimeError("Genius song metadata did not include the primary artist slug needed for page data.")

    prefix = artist_slug + "-"
    if raw_song_path.casefold().startswith(prefix.casefold()):
        title_slug = raw_song_path[len(prefix):]
    else:
        # Match LyricsGenius's public page_data convention as closely as possible.
        # A rare Genius path whose prefix differs from primary_artist.slug may still
        # fail here, in which case the legacy HTML-page fallback below gets a turn.
        marker = raw_song_path.casefold().find(prefix.casefold())
        title_slug = raw_song_path[marker + len(prefix):] if marker >= 0 else raw_song_path

    title_slug = title_slug.strip("/")
    if not title_slug:
        raise RuntimeError("Could not derive the Genius title slug needed for page data.")
    return f"/songs/{artist_slug}/{title_slug}"



GENIUS_INSTRUMENTAL_TEXT_PATTERN = re.compile(
    r"\bthis\s+song\s+is\s+an\s+instrumental\b",
    flags=re.IGNORECASE,
)


def genius_payload_says_instrumental(value: Any) -> bool:
    """Return True only when Genius data explicitly identifies an instrumental.

    Genius can expose the designation in more than one representation:
      * visible text such as "This song is an instrumental"
      * an ``instrumental`` boolean on song/page data
      * a lyrics placeholder reason whose value names an instrumental

    The previous detector only searched string values, so ``{"instrumental": true}``
    was silently ignored and genuine instrumental pages fell through to LRCLIB /
    lyrics.ovh before surfacing the generic no-lyrics error.
    """
    if value is None:
        return False

    if isinstance(value, str):
        normalized = html_unescape(value).strip()
        return bool(
            GENIUS_INSTRUMENTAL_TEXT_PATTERN.search(normalized)
            or normalized.casefold() in {"instrumental", "[instrumental]"}
        )

    if isinstance(value, dict):
        # Current Genius song/page payloads may carry an explicit boolean.
        for key, raw in value.items():
            normalized_key = re.sub(r"[^a-z0-9]+", "", str(key or "").casefold())
            if normalized_key == "instrumental":
                if raw is True:
                    return True
                if isinstance(raw, (int, float)) and raw == 1:
                    return True
                if isinstance(raw, str) and raw.strip().casefold() in {"true", "1", "yes", "instrumental"}:
                    return True

            # Genius web data has also used lyrics_placeholder_reason /
            # lyricsPlaceholderReason for pages that intentionally have no lyrics.
            if normalized_key == "lyricsplaceholderreason" and genius_payload_says_instrumental(raw):
                return True

        return any(genius_payload_says_instrumental(item) for item in value.values())

    if isinstance(value, (list, tuple)):
        return any(genius_payload_says_instrumental(item) for item in value)

    return False


def genius_instrumental_lyrics_html() -> str:
    return (
        '<div class="lyrics-genius-verse lyrics-genius-instrumental" '
        'data-genius-instrumental="true">This song is an instrumental track.</div>'
    )


def genius_reader_confirms_instrumental(song: dict[str, Any]) -> bool:
    """Check the exact Genius song page through Jina Reader for the instrumental notice.

    The Render backend is routinely denied by genius.com (HTTP 403), and the
    authenticated /songs API does not consistently include Genius's web-only
    instrumental designation for older catalog pages.  Reader renders the exact
    public Genius URL without sending our Genius token, cookies, Spotify data, or
    user credentials.  This is deliberately only a yes/no fallback; it is not used
    as a lyrics source.
    """
    raw_url = str(song.get("url") or "").strip()
    if not raw_url:
        path = str(song.get("path") or "").strip()
        if path:
            raw_url = "https://genius.com" + (path if path.startswith("/") else "/" + path)
    if not raw_url:
        return False

    try:
        parsed = urlparse(raw_url)
    except Exception:
        return False
    host = (parsed.hostname or "").casefold().rstrip(".")
    if parsed.scheme != "https" or host not in {"genius.com", "www.genius.com"}:
        return False

    # Jina Reader's documented URL form is https://r.jina.ai/<target-url>.
    reader_url = "https://r.jina.ai/" + raw_url
    headers = {
        "Accept": "text/plain, text/markdown, */*",
        "User-Agent": "NavincitronLyrics/1.6 (+https://www.navincitron.com)",
    }
    try:
        with urlopen(Request(reader_url, headers=headers), timeout=8) as response:
            raw = response.read(2 * 1024 * 1024 + 1)
    except (HTTPError, URLError, TimeoutError, OSError):
        return False

    if not raw or len(raw) > 2 * 1024 * 1024:
        return False
    rendered = html_unescape(raw.decode("utf-8", errors="replace"))
    if GENIUS_INSTRUMENTAL_TEXT_PATTERN.search(rendered):
        return True

    # Reader may normalize the Genius empty-lyrics notice to a standalone
    # "Instrumental" / "[Instrumental]" line rather than the full sentence.
    for line in rendered.splitlines():
        normalized = re.sub(r"[\s*_`>#-]+", " ", line).strip().casefold()
        normalized = normalized.strip("[](){}.:;!?")
        if normalized in {"instrumental", "this song is instrumental", "this song is an instrumental"}:
            return True
    return False


def extract_genius_page_data_lyrics(payload: dict[str, Any]) -> str:
    """Extract and sanitize lyrics_data.body.html from Genius page_data JSON."""
    response = payload.get("response") if isinstance(payload.get("response"), dict) else payload
    page_data = response.get("page_data") if isinstance(response, dict) else None
    if not isinstance(page_data, dict):
        page_data = payload.get("page_data")
    if not isinstance(page_data, dict):
        if genius_payload_says_instrumental(payload):
            return genius_instrumental_lyrics_html()
        raise RuntimeError("Genius page data did not contain page_data.")

    if genius_payload_says_instrumental(page_data):
        return genius_instrumental_lyrics_html()

    lyrics_data = page_data.get("lyrics_data")
    if not isinstance(lyrics_data, dict):
        raise RuntimeError("Genius page data did not contain lyrics_data.")
    body = lyrics_data.get("body")
    if isinstance(body, dict):
        body_html = str(body.get("html") or "")
    else:
        body_html = str(body or "")
    if not body_html.strip():
        raise RuntimeError("Genius page data did not contain lyric HTML.")

    # Reuse the same allowlist parser by presenting the page-data body as one lyric
    # container. Annotation hrefs/referent IDs are rebuilt into local clickable links.
    wrapped = f'<div data-lyrics-container="true">{body_html}</div>'
    return extract_genius_lyrics_html(wrapped)


def fetch_genius_song_page_data(song: dict[str, Any]) -> tuple[str, str]:
    page_path = genius_page_data_path(song)
    page_data_url = "https://genius.com/api/page_data?" + urlencode({"page_path": page_path})
    payload = genius_public_json_request(page_data_url)
    return extract_genius_page_data_lyrics(payload), page_data_url


def fetch_public_genius_through_allorigins(target_url: str, *, expect_json: bool, timeout: float = 6.0) -> Any:
    """Fetch a public Genius URL through AllOrigins when Genius blocks the cloud host.

    Only public genius.com URLs generated by this backend are accepted. No Genius
    token, cookies, Spotify data, or user credentials are sent to the proxy.
    """
    parsed = urlparse(str(target_url or "").strip())
    host = (parsed.hostname or "").casefold().rstrip(".")
    if parsed.scheme != "https" or host not in {"genius.com", "www.genius.com"}:
        raise RuntimeError("Refusing to proxy a non-Genius URL.")

    proxy_url = "https://api.allorigins.win/raw?" + urlencode({"url": target_url})
    request_headers = {
        "Accept": "application/json, text/plain, text/html, */*",
        "User-Agent": "NavincitronLyrics/1.4 (+https://www.navincitron.com)",
    }
    try:
        with urlopen(Request(proxy_url, headers=request_headers), timeout=max(1.0, float(timeout))) as response:
            raw = response.read(GENIUS_PAGE_MAX_BYTES + 1)
    except HTTPError as error:
        raise RuntimeError(f"Genius proxy request failed with HTTP {error.code}.") from error
    except URLError as error:
        raise RuntimeError(f"Could not reach the Genius proxy: {error.reason}") from error

    if len(raw) > GENIUS_PAGE_MAX_BYTES:
        raise RuntimeError("Genius proxy response exceeded the allowed size.")
    text = raw.decode("utf-8", errors="replace")
    if not expect_json:
        return text
    try:
        payload = json.loads(text)
    except json.JSONDecodeError as error:
        raise RuntimeError("Genius proxy returned unreadable page-data JSON.") from error
    if not isinstance(payload, dict):
        raise RuntimeError("Genius proxy returned invalid page-data JSON.")
    return payload


def fetch_genius_song_page_data_proxy(song: dict[str, Any]) -> tuple[str, str]:
    page_path = genius_page_data_path(song)
    page_data_url = "https://genius.com/api/page_data?" + urlencode({"page_path": page_path})
    payload = fetch_public_genius_through_allorigins(page_data_url, expect_json=True)
    return extract_genius_page_data_lyrics(payload), page_data_url


def fetch_genius_song_html_proxy(song: dict[str, Any], song_id: int) -> tuple[str, str]:
    page_url = normalize_genius_page_url(song.get("url") or song.get("path"), song_id)
    page_html = fetch_public_genius_through_allorigins(page_url, expect_json=False)
    return extract_genius_lyrics_html(page_html), page_url


def fetch_genius_song_html_fallback(song: dict[str, Any], song_id: int) -> tuple[str, str]:
    """Legacy last-resort reader for Genius's normal HTML song page."""
    page_url = normalize_genius_page_url(song.get("url") or song.get("path"), song_id)
    headers = {
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.9",
        "Cache-Control": "no-cache",
        "Pragma": "no-cache",
        "Referer": "https://genius.com/",
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/140.0.0.0 Safari/537.36"
        ),
    }
    try:
        with urlopen(Request(page_url, headers=headers), timeout=15) as page_response:
            final_url = page_response.geturl()
            final_host = (urlparse(final_url).hostname or "").casefold().rstrip(".")
            if final_host not in {"genius.com", "www.genius.com"}:
                raise RuntimeError("Genius redirected the song page to an unexpected host.")
            raw = page_response.read(GENIUS_PAGE_MAX_BYTES + 1)
    except HTTPError as error:
        raise RuntimeError(f"Genius song page request failed with HTTP {error.code}.") from error
    except URLError as error:
        raise RuntimeError(f"Could not reach the Genius song page: {error.reason}") from error

    if len(raw) > GENIUS_PAGE_MAX_BYTES:
        raise RuntimeError("Genius song page exceeded the allowed response size.")
    page_html = raw.decode("utf-8", errors="replace")
    return extract_genius_lyrics_html(page_html), page_url


LYRICS_TEXT_MAX_BYTES = 4 * 1024 * 1024
GENIUS_REFERENTS_MAX_PAGES = 10


def generic_json_request(url: str, user_agent: str, timeout: int = 6) -> Any:
    request_headers = {
        "Accept": "application/json",
        "User-Agent": user_agent,
    }
    try:
        with urlopen(Request(url, headers=request_headers), timeout=timeout) as response:
            raw = response.read(LYRICS_TEXT_MAX_BYTES + 1)
    except HTTPError as error:
        raise RuntimeError(f"Request failed with HTTP {error.code} for {urlparse(url).netloc}.") from error
    except URLError as error:
        raise RuntimeError(f"Could not reach {urlparse(url).netloc}: {error.reason}") from error

    if len(raw) > LYRICS_TEXT_MAX_BYTES:
        raise RuntimeError(f"Response from {urlparse(url).netloc} exceeded the allowed size.")
    try:
        return json.loads(raw.decode("utf-8", errors="replace"))
    except json.JSONDecodeError as error:
        raise RuntimeError(f"{urlparse(url).netloc} returned unreadable JSON.") from error


def lyrics_text_from_synced(value: Any) -> str:
    lines: list[str] = []
    for raw_line in str(value or "").splitlines():
        line = re.sub(r"^(?:\[[^\]]+\])+\s*", "", raw_line).rstrip()
        lines.append(line)
    return "\n".join(lines).strip()


def token_overlap_score(left: Any, right: Any) -> float:
    left_tokens = set(normalize_lyrics_match_text(left).split())
    right_tokens = set(normalize_lyrics_match_text(right).split())
    if not left_tokens or not right_tokens:
        return 0.0
    return len(left_tokens & right_tokens) / max(len(left_tokens), len(right_tokens))


def score_external_lyrics_candidate(candidate: dict[str, Any], song: dict[str, Any]) -> float:
    target_title = clean_lyrics_track_title(song.get("title") or song.get("title_with_featured") or "")
    primary_artist = song.get("primary_artist") if isinstance(song.get("primary_artist"), dict) else {}
    target_artist = str(primary_artist.get("name") or song.get("artist_names") or "").strip()
    album = song.get("album") if isinstance(song.get("album"), dict) else {}
    target_album = str(album.get("name") or "").strip()

    candidate_title = clean_lyrics_track_title(candidate.get("trackName") or candidate.get("name") or "")
    candidate_artist = str(candidate.get("artistName") or "").strip()
    candidate_album = str(candidate.get("albumName") or "").strip()

    title_norm = normalize_lyrics_match_text(target_title)
    candidate_title_norm = normalize_lyrics_match_text(candidate_title)
    artist_norm = normalize_lyrics_match_text(target_artist)
    candidate_artist_norm = normalize_lyrics_match_text(candidate_artist)
    album_norm = normalize_lyrics_match_text(target_album)
    candidate_album_norm = normalize_lyrics_match_text(candidate_album)

    score = 0.0
    if title_norm and candidate_title_norm:
        if title_norm == candidate_title_norm:
            score += 100.0
        elif title_norm in candidate_title_norm or candidate_title_norm in title_norm:
            score += 72.0
        else:
            score += 60.0 * token_overlap_score(target_title, candidate_title)

    if artist_norm and candidate_artist_norm:
        if artist_norm == candidate_artist_norm:
            score += 70.0
        elif artist_norm in candidate_artist_norm or candidate_artist_norm in artist_norm:
            score += 52.0
        else:
            score += 45.0 * token_overlap_score(target_artist, candidate_artist)

    if album_norm and candidate_album_norm:
        if album_norm == candidate_album_norm:
            score += 20.0
        elif album_norm in candidate_album_norm or candidate_album_norm in album_norm:
            score += 12.0
        else:
            score += 8.0 * token_overlap_score(target_album, candidate_album)

    if str(candidate.get("plainLyrics") or "").strip() or str(candidate.get("syncedLyrics") or "").strip():
        score += 5.0
    return score


def fetch_lrclib_lyrics(song: dict[str, Any]) -> tuple[str, str]:
    title = clean_lyrics_track_title(song.get("title") or song.get("title_with_featured") or "")
    primary_artist = song.get("primary_artist") if isinstance(song.get("primary_artist"), dict) else {}
    artist = str(primary_artist.get("name") or song.get("artist_names") or "").strip()
    album = song.get("album") if isinstance(song.get("album"), dict) else {}
    album_name = str(album.get("name") or "").strip()
    if not title or not artist:
        raise RuntimeError("Genius song metadata did not contain enough information to find lyric text.")

    searches = [
        {"track_name": title, "artist_name": artist, **({"album_name": album_name} if album_name else {})},
        {"q": f"{artist} {title}"},
    ]
    seen_ids: set[str] = set()
    candidates: list[dict[str, Any]] = []
    errors: list[str] = []

    for params in searches:
        url = "https://lrclib.net/api/search?" + urlencode(params)
        try:
            payload = generic_json_request(
                url,
                "NavincitronLyrics/1.2 (+https://www.navincitron.com)",
            )
        except Exception as error:
            errors.append(str(error))
            continue
        if not isinstance(payload, list):
            continue
        for item in payload:
            if not isinstance(item, dict):
                continue
            item_id = str(item.get("id") or "")
            if item_id and item_id in seen_ids:
                continue
            if item_id:
                seen_ids.add(item_id)
            candidates.append(item)
        if candidates:
            break

    usable: list[tuple[float, dict[str, Any], str]] = []
    for candidate in candidates:
        plain = str(candidate.get("plainLyrics") or "").strip()
        if not plain:
            plain = lyrics_text_from_synced(candidate.get("syncedLyrics"))
        if not plain or bool(candidate.get("instrumental")):
            continue
        usable.append((score_external_lyrics_candidate(candidate, song), candidate, plain))

    if not usable:
        detail = f" ({'; '.join(errors)})" if errors else ""
        raise RuntimeError(f"LRCLIB did not return lyric text for this song{detail}.")

    usable.sort(key=lambda item: item[0], reverse=True)
    score, candidate, plain = usable[0]
    if score < 80.0:
        raise RuntimeError(
            "LRCLIB returned candidates, but none matched the Genius song confidently enough "
            f"(best score {score:.1f})."
        )
    source_id = str(candidate.get("id") or "").strip()
    source_url = f"https://lrclib.net/tracks/{source_id}" if source_id else "https://lrclib.net/"
    return plain, source_url


def fetch_lyrics_ovh(song: dict[str, Any]) -> tuple[str, str]:
    title = clean_lyrics_track_title(song.get("title") or song.get("title_with_featured") or "")
    primary_artist = song.get("primary_artist") if isinstance(song.get("primary_artist"), dict) else {}
    artist = str(primary_artist.get("name") or song.get("artist_names") or "").strip()
    if not title or not artist:
        raise RuntimeError("Genius song metadata did not contain enough information for lyrics.ovh.")
    url = f"https://api.lyrics.ovh/v1/{quote(artist, safe='')}/{quote(title, safe='')}"
    payload = generic_json_request(url, "NavincitronLyrics/1.2 (+https://www.navincitron.com)")
    if not isinstance(payload, dict):
        raise RuntimeError("lyrics.ovh returned an invalid response.")
    lyrics = str(payload.get("lyrics") or "").strip()
    if not lyrics:
        raise RuntimeError(str(payload.get("error") or "lyrics.ovh did not return lyric text."))
    return lyrics, "https://lyrics.ovh/"


def fetch_lyrics_ovh_suggested(song: dict[str, Any]) -> tuple[str, str]:
    """Resolve lyrics.ovh using its Deezer-backed suggestion search.

    The direct /v1/{artist}/{title} endpoint is exact-string sensitive.  This
    fallback asks /suggest for close catalog matches, ranks them against the
    Genius song metadata, and retries only the strongest few candidates.
    """
    title = clean_lyrics_track_title(song.get("title") or song.get("title_with_featured") or "")
    primary_artist = song.get("primary_artist") if isinstance(song.get("primary_artist"), dict) else {}
    artist = str(primary_artist.get("name") or song.get("artist_names") or "").strip()
    album = song.get("album") if isinstance(song.get("album"), dict) else {}
    album_name = str(album.get("name") or "").strip()
    if not title or not artist:
        raise RuntimeError("Genius song metadata did not contain enough information for lyrics.ovh suggestions.")

    suggestion_url = "https://api.lyrics.ovh/suggest/" + quote(f"{artist} {title}", safe="")
    payload = generic_json_request(
        suggestion_url,
        "NavincitronLyrics/1.3 (+https://www.navincitron.com)",
    )
    raw_items = payload.get("data") if isinstance(payload, dict) else payload
    if not isinstance(raw_items, list):
        raise RuntimeError("lyrics.ovh suggestions returned an invalid response.")

    ranked: list[tuple[float, str, str, str]] = []
    seen: set[tuple[str, str]] = set()
    for item in raw_items:
        if not isinstance(item, dict):
            continue
        item_title = clean_lyrics_track_title(item.get("title") or item.get("title_short") or "")
        item_artist_obj = item.get("artist") if isinstance(item.get("artist"), dict) else {}
        item_album_obj = item.get("album") if isinstance(item.get("album"), dict) else {}
        item_artist = str(item_artist_obj.get("name") or "").strip()
        item_album = str(item_album_obj.get("title") or "").strip()
        if not item_title or not item_artist:
            continue
        identity = (normalize_lyrics_match_text(item_artist), normalize_lyrics_match_text(item_title))
        if not all(identity) or identity in seen:
            continue
        seen.add(identity)
        score = score_external_lyrics_candidate(
            {
                "trackName": item_title,
                "artistName": item_artist,
                "albumName": item_album,
                "plainLyrics": "candidate",
            },
            song,
        )
        ranked.append((score, item_artist, item_title, item_album))

    ranked.sort(key=lambda item: item[0], reverse=True)
    errors: list[str] = []
    original_identity = (normalize_lyrics_match_text(artist), normalize_lyrics_match_text(title))
    for score, candidate_artist, candidate_title, candidate_album in ranked[:6]:
        if score < 95.0:
            continue
        candidate_identity = (
            normalize_lyrics_match_text(candidate_artist),
            normalize_lyrics_match_text(candidate_title),
        )
        if candidate_identity == original_identity:
            continue
        url = f"https://api.lyrics.ovh/v1/{quote(candidate_artist, safe='')}/{quote(candidate_title, safe='')}"
        try:
            candidate_payload = generic_json_request(
                url,
                "NavincitronLyrics/1.3 (+https://www.navincitron.com)",
            )
        except Exception as error:
            errors.append(str(error))
            continue
        lyrics = str(candidate_payload.get("lyrics") or "").strip() if isinstance(candidate_payload, dict) else ""
        if lyrics:
            return lyrics, url

    detail = f" ({'; '.join(errors[:3])})" if errors else ""
    raise RuntimeError(f"lyrics.ovh suggestions did not produce usable lyric text{detail}.")


def genius_song_referents(song_id: int) -> list[dict[str, Any]]:
    access_token = get_genius_access_token()
    referents: list[dict[str, Any]] = []
    seen_ids: set[int] = set()

    for page in range(1, GENIUS_REFERENTS_MAX_PAGES + 1):
        url = (
            "https://api.genius.com/referents?"
            + urlencode({
                "song_id": int(song_id),
                "per_page": 50,
                "page": page,
                "text_format": "html,plain",
            })
        )
        payload = genius_json_request(url, access_token)
        response = payload.get("response")
        page_referents = response.get("referents") if isinstance(response, dict) else None
        if not isinstance(page_referents, list) or not page_referents:
            break
        for referent in page_referents:
            if not isinstance(referent, dict) or bool(referent.get("is_description")):
                continue
            try:
                referent_id = int(referent.get("id") or 0)
            except (TypeError, ValueError):
                continue
            if referent_id <= 0 or referent_id in seen_ids:
                continue
            fragment = str(referent.get("fragment") or "").strip()
            annotations = referent.get("annotations")
            if not fragment or not isinstance(annotations, list) or not annotations:
                continue
            seen_ids.add(referent_id)
            referents.append(referent)
        if len(page_referents) < 50:
            break

    return referents


def lyrics_match_projection(value: Any) -> tuple[str, list[int]]:
    original = str(value or "")
    chars: list[str] = []
    indexes: list[int] = []

    for original_index, original_char in enumerate(original):
        expanded = " and " if original_char == "&" else unicodedata.normalize("NFKD", original_char.casefold())
        for character in expanded:
            if unicodedata.combining(character) or character in {"’", "'"}:
                continue
            output = character if character.isalnum() else " "
            if output == " ":
                if not chars or chars[-1] == " ":
                    continue
                chars.append(" ")
                indexes.append(original_index)
                continue
            chars.append(output)
            indexes.append(original_index)

    while chars and chars[-1] == " ":
        chars.pop()
        indexes.pop()
    return "".join(chars), indexes


def find_referent_span(
    lyrics_projection: str,
    projection_indexes: list[int],
    fragment_projection: str,
    start_at: int = 0,
) -> tuple[int, int, int] | None:
    search_at = max(0, int(start_at))
    while fragment_projection and search_at <= len(lyrics_projection):
        position = lyrics_projection.find(fragment_projection, search_at)
        if position < 0:
            return None
        end_position = position + len(fragment_projection)
        left_ok = position == 0 or lyrics_projection[position - 1] == " " or fragment_projection[0] == " "
        right_ok = end_position == len(lyrics_projection) or lyrics_projection[end_position:end_position + 1] == " " or fragment_projection[-1:] == " "
        if left_ok and right_ok and end_position - 1 < len(projection_indexes):
            original_start = projection_indexes[position]
            original_end = projection_indexes[end_position - 1] + 1
            return original_start, original_end, end_position
        search_at = position + 1
    return None


def spans_overlap(start: int, end: int, intervals: list[tuple[int, int, dict[str, Any]]]) -> bool:
    return any(start < existing_end and end > existing_start for existing_start, existing_end, _ in intervals)


def build_genius_annotated_lyrics_html(lyrics_text: str, referents: list[dict[str, Any]]) -> tuple[str, int]:
    lyrics_projection, projection_indexes = lyrics_match_projection(lyrics_text)
    prepared: list[tuple[int, int, dict[str, Any], str]] = []
    for order, referent in enumerate(referents):
        fragment_projection, _ = lyrics_match_projection(referent.get("fragment") or "")
        if not fragment_projection:
            continue
        prepared.append((len(fragment_projection), order, referent, fragment_projection))

    # Longer referents are anchored first so a one-word annotation cannot consume
    # the location needed by a more specific multi-line/multi-word referent.
    prepared.sort(key=lambda item: (-item[0], item[1]))
    intervals: list[tuple[int, int, dict[str, Any]]] = []
    fragment_cursors: dict[str, int] = {}

    for _, _, referent, fragment_projection in prepared:
        cursor = fragment_cursors.get(fragment_projection, 0)
        while True:
            match = find_referent_span(lyrics_projection, projection_indexes, fragment_projection, cursor)
            if match is None:
                break
            start, end, next_cursor = match
            fragment_cursors[fragment_projection] = next_cursor
            cursor = next_cursor
            if not spans_overlap(start, end, intervals):
                intervals.append((start, end, referent))
                break

    intervals.sort(key=lambda item: item[0])
    pieces: list[str] = []
    position = 0

    def escaped_lyrics(value: str) -> str:
        return escape_genius_fallback_lyrics(value)

    for start, end, referent in intervals:
        if start < position:
            continue
        pieces.append(escaped_lyrics(lyrics_text[position:start]))
        try:
            referent_id = int(referent.get("id") or 0)
        except (TypeError, ValueError):
            referent_id = 0
        referent_url = str(referent.get("url") or "").strip()
        href = html_escape(referent_url or "https://genius.com", quote=True)
        fragment_html = escaped_lyrics(lyrics_text[start:end])
        pieces.append(
            f'<a class="lyrics-genius-annotated-fragment" '
            f'data-genius-referent-id="{referent_id}" href="{href}" '
            f'target="_blank" rel="noopener noreferrer">{fragment_html}</a>'
        )
        position = end

    pieces.append(escaped_lyrics(lyrics_text[position:]))
    html = '<div class="lyrics-genius-verse">' + "".join(pieces) + "</div>"
    return html, len(intervals)


def fetch_genius_song_lyrics(song_id: int) -> dict[str, Any]:
    """Return same-origin lyric HTML with exact Genius referent IDs embedded.

    Keep this request bounded.  The previous implementation synchronously tried
    four Genius/third-party page fetches (15s + 15s + 20s + 20s timeouts)
    before even reaching the normal lyric-text fallbacks.  On a hosted Flask
    deployment that can exceed the reverse-proxy request lifetime, which makes
    browser fetch() reject with the unhelpful message ``Failed to fetch``.

    Source order is therefore intentionally narrow:
      1. Genius public page_data directly (verbatim Genius markup)
      2. The same page_data through AllOrigins (verbatim Genius markup)
      3. LRCLIB text + Genius API referents
      4. lyrics.ovh text + Genius API referents

    We do not fetch Genius referents until they are actually needed for an
    external-text fallback.  Native Genius page_data already contains its own
    annotation anchors/referent IDs.
    """
    details_payload = genius_song_request(song_id)
    response = details_payload.get("response")
    song = response.get("song") if isinstance(response, dict) else None
    if not isinstance(song, dict):
        raise RuntimeError("Genius did not return song metadata for the requested song.")

    song_payload = build_genius_song_payload(song)
    source_errors: list[str] = []

    # Check the authenticated Genius song payload before any scraping/fallbacks.
    if genius_payload_says_instrumental(song):
        return {
            "song": song_payload,
            "lyricsHtml": genius_instrumental_lyrics_html(),
            "url": str(song.get("url") or ""),
            "lyricsSource": "genius_instrumental_metadata",
            "lyricsTextSourceUrl": str(song.get("url") or ""),
            "geniusReferentCount": 0,
            "annotationMatchCount": 0,
            "instrumental": True,
            "sourceErrors": source_errors,
        }

    # Prefer the actual Genius transcription, including section headings and
    # Genius's own annotation boundaries.  Only page_data is needed; trying the
    # entire song HTML as a second and fourth long-running path was redundant.
    for source_name, reader in (
        ("genius_page_data", lambda: fetch_genius_song_page_data(song)),
        ("genius_page_data_proxy", lambda: fetch_genius_song_page_data_proxy(song)),
    ):
        try:
            lyrics_html, source_url = reader()
            referent_ids = {
                int(value)
                for value in re.findall(r"data-genius-referent-id=['\"](\d+)['\"]", lyrics_html)
                if str(value).isdigit() and int(value) > 0
            }
            instrumental = 'data-genius-instrumental="true"' in lyrics_html
            return {
                "song": song_payload,
                "lyricsHtml": lyrics_html,
                "url": str(song.get("url") or source_url or ""),
                "lyricsSource": source_name,
                "lyricsTextSourceUrl": source_url,
                "geniusReferentCount": 0 if instrumental else int(song_payload.get("annotationCount") or len(referent_ids)),
                "annotationMatchCount": 0 if instrumental else len(referent_ids),
                "instrumental": instrumental,
                "sourceErrors": source_errors,
            }
        except Exception as error:
            source_errors.append(f"{source_name}: {error}")

    # The exact Genius page can explicitly say that a track is instrumental even
    # when /songs/{id} omits that flag and Render cannot read genius.com directly.
    # Verify that notice through a browser-rendering reader before treating the
    # absence of lyric text as an error.
    if genius_reader_confirms_instrumental(song):
        return {
            "song": song_payload,
            "lyricsHtml": genius_instrumental_lyrics_html(),
            "url": str(song.get("url") or ""),
            "lyricsSource": "genius_instrumental_page_notice",
            "lyricsTextSourceUrl": str(song.get("url") or ""),
            "geniusReferentCount": 0,
            "annotationMatchCount": 0,
            "instrumental": True,
            "sourceErrors": source_errors,
        }

    # Genius's authenticated API remains reachable on this deployment.  Fetch
    # referents only now, because they are required to anchor annotations onto a
    # non-Genius fallback transcription.
    referents = genius_song_referents(song_id)

    lyrics_text = ""
    source_url = ""
    source = ""
    for source_name, reader in (
        ("lrclib_text+genius_api_annotations", fetch_lrclib_lyrics),
        ("lyrics_ovh_text+genius_api_annotations", fetch_lyrics_ovh),
    ):
        try:
            lyrics_text, source_url = reader(song)
            source = source_name
            if lyrics_text:
                break
        except Exception as error:
            source_errors.append(f"{source_name}: {error}")

    if not lyrics_text:
        # If every bounded lyrics source fails to return usable text, treat the
        # track as instrumental instead of exposing a provider/network failure to
        # the lyrics UI. This is intentionally the final no-lyrics fallback.
        return {
            "song": song_payload,
            "lyricsHtml": genius_instrumental_lyrics_html(),
            "url": str(song.get("url") or ""),
            "lyricsSource": "no_lyrics_default_instrumental",
            "lyricsTextSourceUrl": str(song.get("url") or ""),
            "geniusReferentCount": 0,
            "annotationMatchCount": 0,
            "instrumental": True,
            "sourceErrors": source_errors,
        }

    lyrics_html, annotation_match_count = build_genius_annotated_lyrics_html(lyrics_text, referents)
    if referents and annotation_match_count == 0:
        raise RuntimeError(
            "Lyric text was found, but none of the Genius annotation fragments matched it. "
            "This transcription differs too much from Genius to anchor annotations safely. "
            + " ".join(source_errors)
        )

    return {
        "song": song_payload,
        "lyricsHtml": lyrics_html,
        "url": str(song.get("url") or source_url or ""),
        "lyricsSource": source,
        "lyricsTextSourceUrl": source_url,
        "geniusReferentCount": len(referents),
        "annotationMatchCount": annotation_match_count,
        "sourceErrors": source_errors,
    }

def genius_referent_request(referent_id: int) -> dict[str, Any]:
    # Do not fall back to genius.com/api here. The deployed backend is receiving
    # HTTP 403 from genius.com, while api.genius.com is already working for song
    # matching. Referent/annotation reads are supported by the authenticated API.
    access_token = get_genius_access_token()
    return genius_json_request(
        f"https://api.genius.com/referents/{int(referent_id)}?text_format=html%2Cplain",
        access_token,
    )



GENIUS_ANNOTATION_ALLOWED_TAGS = {
    "a", "b", "blockquote", "br", "code", "div", "em", "figcaption", "figure",
    "h1", "h2", "h3", "h4", "h5", "h6", "hr", "i", "img", "li", "ol", "p",
    "pre", "span", "strong", "u", "ul",
}
GENIUS_ANNOTATION_VOID_TAGS = {"br", "hr", "img"}
GENIUS_ANNOTATION_BLOCKED_TAGS = {"script", "style", "noscript", "svg", "object", "embed", "form", "input", "textarea", "button"}


def _safe_genius_annotation_url(value: Any, *, image: bool = False) -> str:
    raw = str(value or "").strip()
    if not raw:
        return ""
    if raw.startswith("//"):
        raw = "https:" + raw
    try:
        parsed = urlparse(raw)
    except Exception:
        return ""
    if parsed.scheme not in {"http", "https"} or not parsed.netloc:
        return ""
    return parsed.geturl()


class GeniusAnnotationHTMLSanitizer(HTMLParser):
    """Keep Genius annotation presentation HTML while stripping active content.

    This preserves paragraph/line-break structure and ordinary embedded images so
    NAVINCITRON can display the annotation as Genius authored it without executing
    Genius scripts or arbitrary event handlers.
    """

    def __init__(self) -> None:
        super().__init__(convert_charrefs=False)
        self.parts: list[str] = []
        self.skip_depth = 0
        self.open_tags: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        tag = str(tag or "").casefold()
        if self.skip_depth:
            if tag not in GENIUS_ANNOTATION_VOID_TAGS:
                self.skip_depth += 1
            return
        if tag in GENIUS_ANNOTATION_BLOCKED_TAGS:
            if tag not in GENIUS_ANNOTATION_VOID_TAGS:
                self.skip_depth = 1
            return
        if tag not in GENIUS_ANNOTATION_ALLOWED_TAGS:
            return

        attr_map = {str(key or "").casefold(): str(value or "") for key, value in attrs}
        safe_attrs: list[str] = []
        if tag == "a":
            href = _safe_genius_annotation_url(attr_map.get("href"))
            if href:
                safe_attrs.extend([
                    f'href="{html_escape(href, quote=True)}"',
                    'target="_blank"',
                    'rel="noopener noreferrer"',
                ])
            title = attr_map.get("title", "").strip()
            if title:
                safe_attrs.append(f'title="{html_escape(title, quote=True)}"')
        elif tag == "img":
            src = _safe_genius_annotation_url(attr_map.get("src"), image=True)
            if not src:
                return
            safe_attrs.append(f'src="{html_escape(src, quote=True)}"')
            for attr_name in ("alt", "title"):
                value = attr_map.get(attr_name, "").strip()
                if value:
                    safe_attrs.append(f'{attr_name}="{html_escape(value, quote=True)}"')
            for attr_name in ("width", "height"):
                value = attr_map.get(attr_name, "").strip()
                if value.isdigit() and 0 < int(value) <= 5000:
                    safe_attrs.append(f'{attr_name}="{value}"')
            safe_attrs.extend(['loading="lazy"', 'decoding="async"'])

        suffix = (" " + " ".join(safe_attrs)) if safe_attrs else ""
        self.parts.append(f"<{tag}{suffix}>")
        if tag not in GENIUS_ANNOTATION_VOID_TAGS:
            self.open_tags.append(tag)

    def handle_startendtag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        self.handle_starttag(tag, attrs)

    def handle_endtag(self, tag: str) -> None:
        tag = str(tag or "").casefold()
        if self.skip_depth:
            self.skip_depth -= 1
            return
        if tag not in GENIUS_ANNOTATION_ALLOWED_TAGS or tag in GENIUS_ANNOTATION_VOID_TAGS:
            return
        if tag in self.open_tags:
            # Close only tags we emitted. Pop back to this tag to keep malformed
            # upstream markup from producing an invalid local tree.
            while self.open_tags:
                open_tag = self.open_tags.pop()
                self.parts.append(f"</{open_tag}>")
                if open_tag == tag:
                    break

    def handle_data(self, data: str) -> None:
        if not self.skip_depth:
            self.parts.append(html_escape(str(data or ""), quote=False))

    def handle_entityref(self, name: str) -> None:
        if not self.skip_depth:
            self.parts.append(f"&{html_escape(str(name or ''), quote=False)};")

    def handle_charref(self, name: str) -> None:
        if not self.skip_depth:
            self.parts.append(f"&#{html_escape(str(name or ''), quote=False)};")

    def html(self) -> str:
        while self.open_tags:
            self.parts.append(f"</{self.open_tags.pop()}>")
        return "".join(self.parts).strip()


def sanitized_genius_annotation_html(value: Any) -> str:
    raw_html = ""
    if isinstance(value, dict):
        raw_html = str(value.get("html") or "")
    elif isinstance(value, str) and "<" in value:
        raw_html = value
    if not raw_html.strip():
        return ""
    parser = GeniusAnnotationHTMLSanitizer()
    parser.feed(raw_html)
    parser.close()
    return parser.html()

def build_genius_referent_payload(payload: dict[str, Any], referent_id: int) -> dict[str, Any]:
    response = payload.get("response")
    referent = response.get("referent") if isinstance(response, dict) else None
    if not isinstance(referent, dict) and isinstance(response, dict):
        referents = response.get("referents")
        if isinstance(referents, list):
            referent = next((item for item in referents if isinstance(item, dict)), None)
    if not isinstance(referent, dict):
        raise RuntimeError("Genius did not return the requested annotation referent.")

    fragment = str(referent.get("fragment") or "").strip()
    referent_url = str(referent.get("url") or "").strip()
    annotations_payload: list[dict[str, Any]] = []
    annotations = referent.get("annotations")
    if isinstance(annotations, list):
        for annotation in annotations:
            if not isinstance(annotation, dict):
                continue
            annotation_body = annotation.get("body")
            body = plain_text_from_genius_value(annotation_body)
            body_html = sanitized_genius_annotation_html(annotation_body)
            if not body and not body_html:
                continue
            authors: list[str] = []
            raw_authors = annotation.get("authors")
            if isinstance(raw_authors, list):
                for author in raw_authors:
                    if isinstance(author, dict):
                        name = str(author.get("name") or author.get("login") or "").strip()
                        if name and name not in authors:
                            authors.append(name)
            created_by = annotation.get("created_by")
            if isinstance(created_by, dict):
                name = str(created_by.get("name") or created_by.get("login") or "").strip()
                if name and name not in authors:
                    authors.append(name)
            annotation_url = str(annotation.get("url") or referent_url or "").strip()
            annotations_payload.append({
                "id": annotation.get("id"),
                "body": body,
                "bodyHtml": body_html,
                "authors": authors,
                "verified": bool(annotation.get("verified")),
                "votesTotal": int(annotation.get("votes_total") or 0),
                "url": annotation_url,
            })

    return {
        "id": int(referent.get("id") or referent_id),
        "fragment": fragment,
        "url": referent_url,
        "annotations": annotations_payload,
    }


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

    # Spotify commonly chains version qualifiers with multiple " - " segments,
    # e.g. "Deuce - Live/1975 - 2025 Remaster". The previous one-shot suffix
    # regex could not cross the second hyphen, leaving the whole version string
    # in the Genius query. Peel qualifying suffix segments from right to left.
    parts = re.split(r"\s+-\s+", text)
    while len(parts) > 1:
        suffix = parts[-1].strip()
        if (
            re.search(rf"(?:{qualifier_words})", suffix, flags=re.IGNORECASE)
            or re.search(r"\b(?:19|20)\d{2}\b", suffix)
        ):
            parts.pop()
            continue
        break
    text = " - ".join(parts)

    text = re.sub(
        rf"\s+-\s+[^-]*(?:{qualifier_words})[^-]*$",
        "",
        text,
        flags=re.IGNORECASE,
    )
    return re.sub(r"\s+", " ", text).strip(" -")


def clean_lyrics_album_title(value: Any) -> str:
    """Remove edition/live/remaster packaging while preserving the album identity."""
    text = str(value or "").strip()
    if not text:
        return ""

    qualifier_words = (
        r"\blive\b|remaster(?:ed|ing)?|deluxe|expanded|anniversary|"
        r"bonus track|edition|mono|stereo"
    )
    text = re.sub(
        rf"\s*[\[(][^\])]*(?:{qualifier_words})[^\])]*[\])]\s*",
        " ",
        text,
        flags=re.IGNORECASE,
    )

    parts = re.split(r"\s+-\s+", text)
    while len(parts) > 1:
        suffix = parts[-1].strip()
        if (
            re.search(rf"(?:{qualifier_words})", suffix, flags=re.IGNORECASE)
            or re.search(r"\b(?:19|20)\d{2}\b", suffix)
        ):
            parts.pop()
            continue
        break

    return re.sub(r"\s+", " ", " - ".join(parts)).strip(" -")


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
    requested_album_clean = clean_lyrics_album_title(album_name)
    candidate_album_clean = clean_lyrics_album_title(candidate_album_name)
    requested_album_norm = normalize_lyrics_match_text(requested_album_clean)
    candidate_album_norm = normalize_lyrics_match_text(candidate_album_clean)

    if requested_album_norm and candidate_album_norm:
        album_overlap = lyrics_token_overlap(requested_album_clean, candidate_album_clean)
        if requested_album_norm == candidate_album_norm:
            # Album-specific live pages should outrank a studio page with the same
            # base song title and artist.
            score += 18.0
        else:
            score += 10.0 * album_overlap

    # Genius search results do not always include an album object. Live pages often
    # carry the album/version in the song title or URL slug instead
    # ("Deuce (Alive!)" / "Kiss-deuce-alive-lyrics"). Use that as a secondary hint.
    if requested_album_norm and requested_album_norm != candidate_album_norm:
        candidate_hint = " ".join(
            str(value or "")
            for value in (
                candidate_title,
                song.get("path"),
                song.get("url"),
            )
        )
        candidate_hint_norm = normalize_lyrics_match_text(candidate_hint)
        album_tokens = [token for token in requested_album_norm.split() if token]
        if album_tokens and all(token in candidate_hint_norm.split() for token in album_tokens):
            score += 12.0

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

    # Long custom-range charts can require many Last.fm calls. A single
    # transient 500/502/503/504 (or Last.fm's temporary-error/rate-limit
    # response) should not abort the entire chart.
    max_attempts = 4
    transient_http_codes = {429, 500, 502, 503, 504}
    transient_lastfm_codes = {11, 16, 29}
    last_error: Exception | None = None

    for attempt in range(max_attempts):
        payload: Any = None
        try:
            with urlopen(lastfm_request, timeout=10) as response:
                payload = json.loads(response.read().decode("utf-8", errors="replace"))
        except HTTPError as error:
            last_error = error
            if error.code in transient_http_codes and attempt < max_attempts - 1:
                retry_after = error.headers.get("Retry-After") if error.headers else None
                try:
                    wait_seconds = float(retry_after) if retry_after is not None else 0.0
                except (TypeError, ValueError):
                    wait_seconds = 0.0
                if wait_seconds <= 0:
                    wait_seconds = min(4.0, 0.6 * (2 ** attempt))
                time.sleep(max(0.25, min(8.0, wait_seconds)))
                continue
            raise RuntimeError(f"Last.fm request failed with HTTP {error.code}.") from error
        except URLError as error:
            last_error = error
            if attempt < max_attempts - 1:
                time.sleep(min(4.0, 0.6 * (2 ** attempt)))
                continue
            raise RuntimeError(f"Could not reach Last.fm: {error.reason}") from error
        except json.JSONDecodeError as error:
            last_error = error
            if attempt < max_attempts - 1:
                time.sleep(min(2.0, 0.4 * (2 ** attempt)))
                continue
            raise RuntimeError("Last.fm returned an unreadable JSON response.") from error

        if not isinstance(payload, dict):
            last_error = RuntimeError("Last.fm returned an invalid JSON response.")
            if attempt < max_attempts - 1:
                time.sleep(min(2.0, 0.4 * (2 ** attempt)))
                continue
            raise last_error

        if payload.get("error"):
            error_code = lastfm_int_value(payload.get("error"), 0)
            message = str(payload.get("message") or "lookup failed").strip()
            if error_code in transient_lastfm_codes and attempt < max_attempts - 1:
                time.sleep(min(5.0, 0.75 * (2 ** attempt)))
                continue
            raise RuntimeError(f"Last.fm API error {payload.get('error')}: {message}")

        return payload

    raise RuntimeError(f"Last.fm request failed after retries: {last_error}")


LASTFM_PROFILE_USERNAME = (os.getenv("LASTFM_PROFILE_USERNAME", "Navincitron").strip() or "Navincitron")
LASTFM_CHART_MAX_ITEMS = 1000
LASTFM_RECENT_MAX_SCROBBLES = 50_000
LASTFM_WEEKLY_CHART_CACHE: dict[str, dict[str, Any]] = {}
LASTFM_WEEKLY_CHART_CACHE_LOCK = threading.Lock()
LASTFM_WEEKLY_CHART_CACHE_TTL_SECONDS = 30 * 24 * 60 * 60
LASTFM_WEEKLY_CHART_CACHE_MAX_ITEMS = 1200
LASTFM_WEB_IMAGE_CACHE: dict[str, dict[str, Any]] = {}
LASTFM_WEB_IMAGE_CACHE_LOCK = threading.Lock()
LASTFM_WEB_IMAGE_MATCH_TTL_SECONDS = 30 * 24 * 60 * 60
LASTFM_WEB_IMAGE_MISS_TTL_SECONDS = 6 * 60 * 60
LASTFM_WEB_IMAGE_CACHE_MAX_ITEMS = 1500


def lastfm_music_path_component(value: str) -> str:
    # Last.fm uses '+' for spaces in music paths, while a literal plus sign in
    # an artist name needs to survive that convention. Double-encode literal
    # plus signs so Florence + the Machine resolves to the same canonical page
    # Last.fm itself emits.
    encoded = quote_plus(str(value or "").strip(), safe="")
    return encoded.replace("%2B", "%252B").replace("%2b", "%252B")


def lastfm_web_image_cache_get(key: str) -> str | None:
    now = time.time()
    with LASTFM_WEB_IMAGE_CACHE_LOCK:
        cached = LASTFM_WEB_IMAGE_CACHE.get(key)
        if not isinstance(cached, dict):
            return None
        value = str(cached.get("value") or "")
        age = now - float(cached.get("timestamp") or 0)
        ttl = LASTFM_WEB_IMAGE_MATCH_TTL_SECONDS if value else LASTFM_WEB_IMAGE_MISS_TTL_SECONDS
        if age > ttl:
            LASTFM_WEB_IMAGE_CACHE.pop(key, None)
            return None
        return value


def lastfm_web_image_cache_put(key: str, value: str) -> str:
    now = time.time()
    with LASTFM_WEB_IMAGE_CACHE_LOCK:
        LASTFM_WEB_IMAGE_CACHE[key] = {"timestamp": now, "value": value}
        if len(LASTFM_WEB_IMAGE_CACHE) > LASTFM_WEB_IMAGE_CACHE_MAX_ITEMS:
            oldest_key = min(
                LASTFM_WEB_IMAGE_CACHE,
                key=lambda item_key: float(LASTFM_WEB_IMAGE_CACHE[item_key].get("timestamp") or 0),
            )
            LASTFM_WEB_IMAGE_CACHE.pop(oldest_key, None)
    return value


def fetch_lastfm_html(url: str) -> str:
    target = str(url or "").strip()
    if not target.startswith("https://www.last.fm/"):
        return ""
    request_obj = Request(
        target,
        headers={
            "Accept": "text/html,application/xhtml+xml",
            "Accept-Language": "en-US,en;q=0.9",
            "User-Agent": "Mozilla/5.0 (compatible; Navincitron/1.0; +https://www.navincitron.com)",
        },
    )
    try:
        with urlopen(request_obj, timeout=10) as response:
            return response.read(3 * 1024 * 1024).decode("utf-8", errors="replace")
    except (HTTPError, URLError, TimeoutError):
        return ""


def extract_lastfm_header_image(html_text: str) -> str:
    if not html_text:
        return ""
    decoded = html_unescape(html_text)

    # The large image shown on Last.fm music pages is stored as a CSS
    # background on .header-new-background-image. This is also used on artist
    # pages and provides a much better fallback than the historical API star
    # placeholder.
    for tag in re.findall(r"<[^>]*header-new-background-image[^>]*>", decoded, flags=re.IGNORECASE):
        style_match = re.search(r"style\s*=\s*([\"'])(.*?)\1", tag, flags=re.IGNORECASE | re.DOTALL)
        if not style_match:
            continue
        image_match = re.search(
            r"background-image\s*:\s*url\(\s*([\"']?)(https?://[^)\"']+)\1\s*\)",
            style_match.group(2),
            flags=re.IGNORECASE,
        )
        if image_match:
            image_url = useful_lastfm_image_url(image_match.group(2))
            if image_url:
                return image_url

    # Do not fall back to arbitrary <img> / avatar elements here. User-library
    # pages contain the Last.fm account avatar, and treating that as an artist
    # image caused every artist tile to resolve to the Navincitron profile photo.
    # Artist pages are handled by extract_lastfm_artist_gallery_image() first;
    # music pages that lack a CSS hero can still use their page metadata below.

    # Final non-personalized fallback for page variants that use metadata.
    meta_match = re.search(
        r"<meta[^>]+(?:property|name)=[\"'](?:og:image|twitter:image)[\"'][^>]+content=[\"'](https?://[^\"']+)[\"']",
        decoded,
        flags=re.IGNORECASE,
    )
    if meta_match:
        return useful_lastfm_image_url(meta_match.group(1))
    return ""


def extract_lastfm_artist_gallery_image(html_text: str) -> str:
    """Return the large CDN form of the first artist-gallery image hash on a Last.fm page."""
    if not html_text:
        return ""
    decoded = html_unescape(html_text)

    # Last.fm's artist hero / preferred image links point at
    # /music/<artist>/+images/<32-hex-image-id>. The same id is accepted by
    # Last.fm's public image CDN, which avoids depending on CSS background
    # markup that changes between page variants.
    patterns = (
        r"href\s*=\s*['\"][^'\"]*/\+images/([0-9a-f]{32})(?:[^'\"]*)['\"]",
        r"href\s*=\s*['\"][^'\"]*/%2Bimages(?:/|%2F)([0-9a-f]{32})(?:[^'\"]*)['\"]",
    )
    for pattern in patterns:
        match = re.search(pattern, decoded, flags=re.IGNORECASE)
        if match:
            return f"https://lastfm-img.freetls.fastly.net/i/u/770x0/{match.group(1).lower()}.jpg"
    return ""


def extract_lastfm_artist_page_image(html_text: str) -> str:
    # Prefer the gallery id because Pro preferred images are represented by the
    # artist image/gallery selection. Fall back to the page's hero/meta image.
    return extract_lastfm_artist_gallery_image(html_text) or extract_lastfm_header_image(html_text)


def extract_lastfm_page_image_candidates(html_text: str, include_artist_gallery: bool = False, limit: int = 24) -> list[str]:
    """Extract page-specific Last.fm artwork without accepting account/profile avatars."""
    if not html_text:
        return []

    decoded = html_unescape(html_text)
    candidates: list[str] = []

    def add(raw_url: Any) -> None:
        url = useful_lastfm_image_url(raw_url)
        if not url or url in candidates:
            return
        parsed = urlparse(url)
        host = (parsed.hostname or "").lower()
        # Keep automatic picker results on Last.fm's image infrastructure. A
        # user may still paste any http(s) image URL explicitly in the UI.
        if not (host.endswith("last.fm") or "lastfm" in host or "audioscrobbler" in host):
            return
        candidates.append(url)

    # Page hero / metadata image is the safest album/track candidate and also a
    # useful artist fallback. This helper deliberately never scans arbitrary img
    # tags, because Last.fm user/library pages contain account avatars.
    add(extract_lastfm_header_image(decoded))

    if include_artist_gallery:
        patterns = (
            r"href\s*=\s*['\"][^'\"]*/\+images/([0-9a-f]{32})(?:[^'\"]*)['\"]",
            r"href\s*=\s*['\"][^'\"]*/%2Bimages(?:/|%2F)([0-9a-f]{32})(?:[^'\"]*)['\"]",
        )
        for pattern in patterns:
            for match in re.finditer(pattern, decoded, flags=re.IGNORECASE):
                add(f"https://lastfm-img.freetls.fastly.net/i/u/770x0/{match.group(1).lower()}.jpg")
                if len(candidates) >= limit:
                    break
            if len(candidates) >= limit:
                break

    return candidates[: max(1, int(limit))]


def normalize_lastfm_music_url(raw_url: str) -> str:
    candidate = str(raw_url or "").strip()
    if candidate.startswith("http://www.last.fm/"):
        candidate = "https://www.last.fm/" + candidate[len("http://www.last.fm/"):]
    if not candidate.startswith("https://www.last.fm/"):
        return ""
    try:
        parsed = urlparse(candidate)
    except Exception:
        return ""
    if (parsed.hostname or "").lower() != "www.last.fm" or not parsed.path.startswith("/music/"):
        return ""
    return candidate


def lastfm_cover_option_pages(mode: str, artist: str, title: str, album: str, item_url: str = "") -> list[str]:
    artist_name = str(artist or "").strip()
    title_name = str(title or "").strip()
    album_name = str(album or "").strip()
    pages: list[str] = []

    direct = normalize_lastfm_music_url(item_url)
    if direct:
        pages.append(direct)

    if not artist_name:
        return list(dict.fromkeys(pages))

    encoded_artist = lastfm_music_path_component(artist_name)
    if mode == "artists":
        pages.append(f"https://www.last.fm/music/{encoded_artist}")
    elif mode == "albums":
        release_name = album_name or title_name
        if release_name:
            pages.append(f"https://www.last.fm/music/{encoded_artist}/{lastfm_music_path_component(release_name)}")
    else:
        # Songs/recently-played entries may expose both a track page and a known
        # release page. Both are legitimate Last.fm-only artwork sources.
        if title_name:
            pages.append(f"https://www.last.fm/music/{encoded_artist}/_/{lastfm_music_path_component(title_name)}")
        if album_name:
            pages.append(f"https://www.last.fm/music/{encoded_artist}/{lastfm_music_path_component(album_name)}")

    return list(dict.fromkeys(filter(None, pages)))


def lastfm_artist_image_url(username: str, artist: str, artist_url: str = "") -> str:
    artist_name = str(artist or "").strip()
    if not artist_name:
        return ""

    # v3 invalidates the v2 artist-image cache. v2 checked the user's public
    # library page first; that page exposes the user's account avatar and can
    # therefore return the same Navincitron profile picture for every artist.
    cache_key = f"artist-v3::{str(username or '').casefold()}::{artist_name.casefold()}"
    cached = lastfm_web_image_cache_get(cache_key)
    if cached is not None:
        return cached

    encoded_artist = lastfm_music_path_component(artist_name)
    candidates = []
    canonical_url = str(artist_url or "").strip()
    if canonical_url.startswith("http://www.last.fm/"):
        canonical_url = "https://www.last.fm/" + canonical_url[len("http://www.last.fm/"):]
    if canonical_url.startswith("https://www.last.fm/") and "/music/" in canonical_url:
        candidates.append(canonical_url)
    # Always include the canonical public artist page. Unlike /user/.../library,
    # this page's +images hero belongs to the requested artist rather than the
    # account whose library is being viewed.
    candidates.append(f"https://www.last.fm/music/{encoded_artist}")

    for candidate in dict.fromkeys(candidates):
        html_text = fetch_lastfm_html(candidate)
        image_url = useful_lastfm_image_url(extract_lastfm_artist_page_image(html_text))
        if image_url:
            return lastfm_web_image_cache_put(cache_key, image_url)

    # Documented API fallback. Supplying username gives user-context playcount;
    # Last.fm does not document a preferred-image field here, but the ordinary
    # image array is still useful when it is not the historical placeholder.
    try:
        payload = lastfm_json_request(
            {
                "method": "artist.getInfo",
                "artist": artist_name,
                "username": str(username or LASTFM_PROFILE_USERNAME).strip(),
                "autocorrect": 1,
            }
        )
        artist_info = payload.get("artist") if isinstance(payload.get("artist"), dict) else {}
        image_url = useful_lastfm_image_url(best_lastfm_image_url(artist_info.get("image")))
        if image_url:
            return lastfm_web_image_cache_put(cache_key, image_url)
    except Exception:
        pass

    return lastfm_web_image_cache_put(cache_key, "")


def lastfm_track_album_image_url(artist: str, track: str, track_url: str = "") -> tuple[str, str]:
    artist_name = str(artist or "").strip()
    track_name = str(track or "").strip()
    if not artist_name or not track_name:
        return "", ""
    cache_key = f"track::{artist_name.casefold()}::{track_name.casefold()}"
    cached = lastfm_web_image_cache_get(cache_key)
    if cached is not None:
        if "\u241f" in cached:
            image_url, album_name = cached.split("\u241f", 1)
            return image_url, album_name
        return cached, ""

    image_url = ""
    album_name = ""
    try:
        payload = lastfm_json_request(
            {
                "method": "track.getInfo",
                "artist": artist_name,
                "track": track_name,
                "username": LASTFM_PROFILE_USERNAME,
            }
        )
        track_info = payload.get("track") if isinstance(payload.get("track"), dict) else {}
        album_info = track_info.get("album") if isinstance(track_info.get("album"), dict) else {}
        image_url = best_lastfm_image_url(album_info.get("image"))
        album_name = str(album_info.get("title") or "").strip()
    except Exception:
        pass

    if not image_url:
        candidate = str(track_url or "").strip()
        if candidate.startswith("http://www.last.fm/"):
            candidate = "https://www.last.fm/" + candidate[len("http://www.last.fm/"):]
        if not candidate.startswith("https://www.last.fm/"):
            encoded_artist = lastfm_music_path_component(artist_name)
            encoded_track = lastfm_music_path_component(track_name)
            candidate = f"https://www.last.fm/music/{encoded_artist}/_/{encoded_track}"
        image_url = extract_lastfm_header_image(fetch_lastfm_html(candidate))

    lastfm_web_image_cache_put(cache_key, f"{image_url}\u241f{album_name}")
    return image_url, album_name


def enrich_lastfm_chart_images(username: str, mode: str, items: list[dict[str, Any]]) -> None:
    if not items:
        return

    if mode == "artists":
        # Artist photos are deliberately resolved lazily by /api/lastfm-artist-image
        # as their tiles enter the browser viewport. Resolving hundreds or 1,000
        # public Last.fm artist pages here would make the chart request block for
        # far too long.
        for item in items:
            item["image"] = ""
        return

    missing = [item for item in items if not useful_lastfm_image_url(item.get("image"))]
    if not missing:
        return

    def resolve_song(item: dict[str, Any]) -> tuple[str, str]:
        return lastfm_track_album_image_url(
            str(item.get("artist") or ""),
            str(item.get("title") or ""),
            str(item.get("url") or ""),
        )

    workers = min(8, len(missing))
    with ThreadPoolExecutor(max_workers=max(1, workers)) as pool:
        futures = [(item, pool.submit(resolve_song, item)) for item in missing]
        for item, future in futures:
            try:
                image_url, album_name = future.result()
            except Exception:
                image_url, album_name = "", ""
            if image_url:
                item["image"] = image_url
                item["imageSource"] = "Last.fm album/release page"
            if album_name and not str(item.get("album") or "").strip():
                item["album"] = album_name



def lastfm_text_value(value: Any) -> str:
    if isinstance(value, dict):
        return str(value.get("name") or value.get("#text") or "").strip()
    return str(value or "").strip()


def lastfm_int_value(value: Any, fallback: int = 0) -> int:
    try:
        return int(str(value or fallback).strip())
    except (TypeError, ValueError):
        return fallback


def lastfm_recent_track_rows(
    username: str,
    from_ts: int | None = None,
    to_ts: int | None = None,
    max_scrobbles: int = LASTFM_RECENT_MAX_SCROBBLES,
) -> tuple[list[dict[str, Any]], bool]:
    rows: list[dict[str, Any]] = []
    page = 1
    truncated = False

    while len(rows) < max_scrobbles:
        params: dict[str, Any] = {
            "method": "user.getRecentTracks",
            "user": username,
            "limit": 200,
            "page": page,
            "extended": 0,
        }
        if from_ts is not None:
            params["from"] = int(from_ts)
        if to_ts is not None:
            params["to"] = int(to_ts)

        payload = lastfm_json_request(params)
        recent = payload.get("recenttracks") if isinstance(payload.get("recenttracks"), dict) else {}
        raw_tracks = recent.get("track")
        if isinstance(raw_tracks, dict):
            raw_tracks = [raw_tracks]
        if not isinstance(raw_tracks, list):
            raw_tracks = []

        for raw in raw_tracks:
            if not isinstance(raw, dict):
                continue
            attrs = raw.get("@attr") if isinstance(raw.get("@attr"), dict) else {}
            now_playing = str(attrs.get("nowplaying") or "").lower() == "true"
            date_data = raw.get("date") if isinstance(raw.get("date"), dict) else {}
            uts = lastfm_int_value(date_data.get("uts"), 0)
            artist = lastfm_text_value(raw.get("artist"))
            track_name = str(raw.get("name") or "").strip()
            album = lastfm_text_value(raw.get("album"))
            if not artist or not track_name:
                continue
            rows.append(
                {
                    "artist": artist,
                    "track": track_name,
                    "album": album,
                    "image": best_lastfm_image_url(raw.get("image")),
                    "url": str(raw.get("url") or "").strip(),
                    "timestamp": uts,
                    "nowPlaying": now_playing,
                }
            )
            if len(rows) >= max_scrobbles:
                truncated = True
                break

        attrs = recent.get("@attr") if isinstance(recent.get("@attr"), dict) else {}
        total_pages = max(1, lastfm_int_value(attrs.get("totalPages"), 1))
        if page >= total_pages or not raw_tracks or truncated:
            break
        page += 1

    return rows, truncated


def lastfm_period_bounds(period: str, custom_from: int | None = None, custom_to: int | None = None) -> tuple[int | None, int | None]:
    now_ts = int(time.time())
    if period == "1day":
        return now_ts - 24 * 60 * 60, now_ts
    if period == "14day":
        return now_ts - 14 * 24 * 60 * 60, now_ts
    if period == "custom":
        return custom_from, custom_to
    return None, None


def lastfm_direct_period(period: str) -> str | None:
    return {
        "7day": "7day",
        "1month": "1month",
        "3month": "3month",
        "6month": "6month",
        "12month": "12month",
        "overall": "overall",
    }.get(period)


def lastfm_direct_chart(username: str, mode: str, period: str, limit: int) -> list[dict[str, Any]]:
    method_map = {
        "albums": ("user.getTopAlbums", "topalbums", "album"),
        "songs": ("user.getTopTracks", "toptracks", "track"),
        "artists": ("user.getTopArtists", "topartists", "artist"),
    }
    method, root_key, item_key = method_map[mode]
    requested = min(LASTFM_CHART_MAX_ITEMS, max(1, int(limit)))
    items: list[dict[str, Any]] = []
    page = 1

    # The top-chart methods expose page + limit. Use conservative 100-item pages
    # rather than relying on an undocumented very-large per-page limit.
    while len(items) < requested:
        per_page = min(100, requested - len(items))
        payload = lastfm_json_request(
            {
                "method": method,
                "user": username,
                "period": period,
                "limit": per_page,
                "page": page,
            }
        )
        root = payload.get(root_key) if isinstance(payload.get(root_key), dict) else {}
        raw_items = root.get(item_key)
        if isinstance(raw_items, dict):
            raw_items = [raw_items]
        if not isinstance(raw_items, list) or not raw_items:
            break

        before = len(items)
        for raw in raw_items:
            if len(items) >= requested:
                break
            if not isinstance(raw, dict):
                continue
            playcount = max(0, lastfm_int_value(raw.get("playcount"), 0))
            image = best_lastfm_image_url(raw.get("image"))
            if mode == "albums":
                title = str(raw.get("name") or "").strip()
                artist = lastfm_text_value(raw.get("artist"))
                album = title
            elif mode == "songs":
                title = str(raw.get("name") or "").strip()
                artist = lastfm_text_value(raw.get("artist"))
                album = ""
            else:
                artist = str(raw.get("name") or "").strip()
                title = artist
                album = ""
            if not title:
                continue
            items.append(
                {
                    "rank": len(items) + 1,
                    "artist": artist,
                    "title": title,
                    "album": album,
                    "playcount": playcount,
                    "image": image,
                    "url": str(raw.get("url") or "").strip(),
                    "timestamp": 0,
                    "nowPlaying": False,
                }
            )

        attrs = root.get("@attr") if isinstance(root.get("@attr"), dict) else {}
        total_pages = max(1, lastfm_int_value(attrs.get("totalPages"), page))
        if page >= total_pages or len(items) == before or len(raw_items) < per_page:
            break
        page += 1

    return items



def lastfm_weekly_chart_cache_key(username: str, mode: str, from_ts: int, to_ts: int) -> str:
    return f"{username.casefold()}\u241f{mode}\u241f{int(from_ts)}\u241f{int(to_ts)}"


def lastfm_weekly_chart_cache_get(username: str, mode: str, from_ts: int, to_ts: int) -> list[dict[str, Any]] | None:
    key = lastfm_weekly_chart_cache_key(username, mode, from_ts, to_ts)
    now = time.time()
    with LASTFM_WEEKLY_CHART_CACHE_LOCK:
        cached = LASTFM_WEEKLY_CHART_CACHE.get(key)
        if not isinstance(cached, dict):
            return None
        if now - float(cached.get("timestamp") or 0) >= LASTFM_WEEKLY_CHART_CACHE_TTL_SECONDS:
            LASTFM_WEEKLY_CHART_CACHE.pop(key, None)
            return None
        items = cached.get("items")
        if not isinstance(items, list):
            return None
        return [dict(item) for item in items if isinstance(item, dict)]


def lastfm_weekly_chart_cache_put(
    username: str,
    mode: str,
    from_ts: int,
    to_ts: int,
    items: list[dict[str, Any]],
) -> None:
    key = lastfm_weekly_chart_cache_key(username, mode, from_ts, to_ts)
    with LASTFM_WEEKLY_CHART_CACHE_LOCK:
        LASTFM_WEEKLY_CHART_CACHE[key] = {
            "timestamp": time.time(),
            "items": [dict(item) for item in items if isinstance(item, dict)],
        }
        if len(LASTFM_WEEKLY_CHART_CACHE) > LASTFM_WEEKLY_CHART_CACHE_MAX_ITEMS:
            oldest_keys = sorted(
                LASTFM_WEEKLY_CHART_CACHE,
                key=lambda cache_key: float(
                    (LASTFM_WEEKLY_CHART_CACHE.get(cache_key) or {}).get("timestamp") or 0
                ),
            )
            remove_count = max(
                1,
                len(LASTFM_WEEKLY_CHART_CACHE) - LASTFM_WEEKLY_CHART_CACHE_MAX_ITEMS,
            )
            for cache_key in oldest_keys[:remove_count]:
                LASTFM_WEEKLY_CHART_CACHE.pop(cache_key, None)


def lastfm_weekly_chart_ranges(username: str) -> list[tuple[int, int]]:
    payload = lastfm_json_request(
        {
            "method": "user.getWeeklyChartList",
            "user": username,
        }
    )
    root = payload.get("weeklychartlist") if isinstance(payload.get("weeklychartlist"), dict) else {}
    raw_charts = root.get("chart")
    if isinstance(raw_charts, dict):
        raw_charts = [raw_charts]
    if not isinstance(raw_charts, list):
        return []

    ranges: list[tuple[int, int]] = []
    seen: set[tuple[int, int]] = set()
    for raw in raw_charts:
        if not isinstance(raw, dict):
            continue
        start = lastfm_int_value(raw.get("from"), 0)
        end = lastfm_int_value(raw.get("to"), 0)
        if start <= 0 or end <= start:
            continue
        pair = (start, end)
        if pair in seen:
            continue
        seen.add(pair)
        ranges.append(pair)

    ranges.sort(key=lambda pair: (pair[0], pair[1]))
    return ranges


def lastfm_weekly_chart_items(
    username: str,
    mode: str,
    from_ts: int,
    to_ts: int,
) -> list[dict[str, Any]]:
    cached = lastfm_weekly_chart_cache_get(username, mode, from_ts, to_ts)
    if cached is not None:
        return cached

    method_map = {
        "albums": ("user.getWeeklyAlbumChart", "weeklyalbumchart", "album"),
        "songs": ("user.getWeeklyTrackChart", "weeklytrackchart", "track"),
        "artists": ("user.getWeeklyArtistChart", "weeklyartistchart", "artist"),
    }
    method, root_key, item_key = method_map[mode]
    payload = lastfm_json_request(
        {
            "method": method,
            "user": username,
            "from": int(from_ts),
            "to": int(to_ts),
        }
    )
    root = payload.get(root_key) if isinstance(payload.get(root_key), dict) else {}
    raw_items = root.get(item_key)
    if isinstance(raw_items, dict):
        raw_items = [raw_items]
    if not isinstance(raw_items, list):
        raw_items = []

    items: list[dict[str, Any]] = []
    for raw in raw_items:
        if not isinstance(raw, dict):
            continue
        playcount = max(0, lastfm_int_value(raw.get("playcount"), 0))
        if playcount <= 0:
            continue

        image = best_lastfm_image_url(raw.get("image"))
        if mode == "artists":
            artist = str(raw.get("name") or "").strip()
            title = artist
            album = ""
        elif mode == "albums":
            title = str(raw.get("name") or "").strip()
            artist = lastfm_text_value(raw.get("artist"))
            album = title
        else:
            title = str(raw.get("name") or "").strip()
            artist = lastfm_text_value(raw.get("artist"))
            album = ""

        if not title:
            continue
        items.append(
            {
                "artist": artist,
                "title": title,
                "album": album,
                "playcount": playcount,
                "image": image,
                "url": str(raw.get("url") or "").strip(),
                "timestamp": int(to_ts),
                "nowPlaying": False,
            }
        )

    lastfm_weekly_chart_cache_put(username, mode, from_ts, to_ts, items)
    return items


def lastfm_merge_counted_items(
    buckets: dict[str, dict[str, Any]],
    items: list[dict[str, Any]],
    mode: str,
) -> None:
    for raw in items:
        if not isinstance(raw, dict):
            continue
        artist = str(raw.get("artist") or "").strip()
        title = str(raw.get("title") or "").strip()
        album = str(raw.get("album") or "").strip()
        playcount = max(0, lastfm_int_value(raw.get("playcount"), 0))
        if playcount <= 0:
            continue

        if mode == "artists":
            key = artist.casefold()
            display_title = artist
        else:
            key = f"{artist.casefold()}\u241f{title.casefold()}"
            display_title = title
        if not key or not display_title:
            continue

        item = buckets.setdefault(
            key,
            {
                "artist": artist,
                "title": display_title,
                "album": album if mode != "artists" else "",
                "playcount": 0,
                "image": str(raw.get("image") or ""),
                "url": str(raw.get("url") or ""),
                "timestamp": lastfm_int_value(raw.get("timestamp"), 0),
                "nowPlaying": False,
            },
        )
        item["playcount"] += playcount

        raw_ts = lastfm_int_value(raw.get("timestamp"), 0)
        if raw_ts >= lastfm_int_value(item.get("timestamp"), 0):
            item["timestamp"] = raw_ts
            if raw.get("image"):
                item["image"] = str(raw.get("image") or "")
            if raw.get("url"):
                item["url"] = str(raw.get("url") or "")
            if mode != "artists" and album:
                item["album"] = album


def lastfm_recent_rows_as_counted_items(rows: list[dict[str, Any]], mode: str) -> list[dict[str, Any]]:
    counted: list[dict[str, Any]] = []
    for row in rows:
        if not isinstance(row, dict) or row.get("nowPlaying"):
            continue
        artist = str(row.get("artist") or "").strip()
        track = str(row.get("track") or "").strip()
        album = str(row.get("album") or "").strip()

        if mode == "albums":
            if not album:
                continue
            title = album
        elif mode == "songs":
            if not track:
                continue
            title = track
        else:
            if not artist:
                continue
            title = artist

        counted.append(
            {
                "artist": artist,
                "title": title,
                "album": album if mode != "artists" else "",
                "playcount": 1,
                "image": str(row.get("image") or ""),
                "url": str(row.get("url") or ""),
                "timestamp": lastfm_int_value(row.get("timestamp"), 0),
                "nowPlaying": False,
            }
        )
    return counted


def lastfm_uncovered_ranges(
    from_ts: int,
    to_ts: int,
    covered_ranges: list[tuple[int, int]],
) -> list[tuple[int, int]]:
    cursor = int(from_ts)
    end_limit = int(to_ts)
    gaps: list[tuple[int, int]] = []

    for start, end in sorted(covered_ranges, key=lambda pair: (pair[0], pair[1])):
        if end < cursor:
            continue
        if start > end_limit:
            break
        if start > cursor:
            gaps.append((cursor, min(end_limit, start - 1)))
        cursor = max(cursor, end + 1)
        if cursor > end_limit:
            break

    if cursor <= end_limit:
        gaps.append((cursor, end_limit))

    return [(start, end) for start, end in gaps if end >= start]


def lastfm_custom_aggregate_weekly(
    username: str,
    mode: str,
    from_ts: int,
    to_ts: int,
    limit: int,
) -> tuple[list[dict[str, Any]], int, bool, int, int]:
    """
    Build a long custom-range chart without paging through every raw scrobble.

    Last.fm exposes historical weekly chart ranges explicitly. For complete weeks
    inside the requested custom interval, fetch the already-aggregated weekly
    artist/album/track chart. Only the partial edge ranges (and any week whose
    weekly-chart request ultimately fails) fall back to recent-track pagination.

    Returns:
        items,
        sampled_recent_scrobbles,
        recent_fallback_truncated,
        weekly_ranges_used,
        weekly_ranges_failed
    """
    available_ranges = lastfm_weekly_chart_ranges(username)
    complete_ranges = [
        (start, end)
        for start, end in available_ranges
        if start >= int(from_ts) and end <= int(to_ts)
    ]

    # If there is no complete historical week in the requested window, the
    # existing recent-track path is simpler and exact.
    if not complete_ranges:
        rows, truncated = lastfm_recent_track_rows(
            username,
            int(from_ts),
            int(to_ts),
            max_scrobbles=LASTFM_RECENT_MAX_SCROBBLES,
        )
        return (
            lastfm_aggregate_recent(rows, mode, limit),
            len(rows),
            truncated,
            0,
            0,
        )

    buckets: dict[str, dict[str, Any]] = {}
    failed_ranges: list[tuple[int, int]] = []

    # Fetch the historical weekly aggregates concurrently, but keep the worker
    # count deliberately modest to remain friendly to Last.fm's API.
    max_workers = min(4, max(1, len(complete_ranges)))
    with ThreadPoolExecutor(max_workers=max_workers) as pool:
        future_rows = [
            (
                date_range,
                pool.submit(
                    lastfm_weekly_chart_items,
                    username,
                    mode,
                    date_range[0],
                    date_range[1],
                ),
            )
            for date_range in complete_ranges
        ]
        for date_range, future in future_rows:
            try:
                weekly_items = future.result()
            except Exception:
                failed_ranges.append(date_range)
                continue
            lastfm_merge_counted_items(buckets, weekly_items, mode)

    successful_ranges = [
        date_range for date_range in complete_ranges if date_range not in set(failed_ranges)
    ]
    fallback_ranges = lastfm_uncovered_ranges(
        int(from_ts),
        int(to_ts),
        successful_ranges,
    )

    sampled_recent = 0
    truncated = False
    for gap_from, gap_to in fallback_ranges:
        rows, gap_truncated = lastfm_recent_track_rows(
            username,
            gap_from,
            gap_to,
            max_scrobbles=LASTFM_RECENT_MAX_SCROBBLES,
        )
        sampled_recent += len(rows)
        truncated = truncated or gap_truncated
        lastfm_merge_counted_items(
            buckets,
            lastfm_recent_rows_as_counted_items(rows, mode),
            mode,
        )

    ordered = sorted(
        buckets.values(),
        key=lambda item: (
            -lastfm_int_value(item.get("playcount"), 0),
            -lastfm_int_value(item.get("timestamp"), 0),
            str(item.get("title") or "").casefold(),
        ),
    )
    final_items = ordered[:limit]
    for index, item in enumerate(final_items, start=1):
        item["rank"] = index

    return (
        final_items,
        sampled_recent,
        truncated,
        len(successful_ranges),
        len(failed_ranges),
    )


def lastfm_aggregate_recent(rows: list[dict[str, Any]], mode: str, limit: int) -> list[dict[str, Any]]:
    buckets: dict[str, dict[str, Any]] = {}
    for row in rows:
        if row.get("nowPlaying"):
            # Current playback has not been scrobbled yet, so it should not add to
            # a most-listened count.
            continue
        artist = str(row.get("artist") or "").strip()
        track = str(row.get("track") or "").strip()
        album = str(row.get("album") or "").strip()
        if mode == "albums":
            if not album:
                continue
            key = f"{artist.casefold()}\u241f{album.casefold()}"
            title = album
        elif mode == "songs":
            key = f"{artist.casefold()}\u241f{track.casefold()}"
            title = track
        else:
            key = artist.casefold()
            title = artist
        if not key or not title:
            continue
        item = buckets.setdefault(
            key,
            {
                "artist": artist,
                "title": title,
                "album": album if mode != "artists" else "",
                "playcount": 0,
                "image": str(row.get("image") or ""),
                "url": str(row.get("url") or ""),
                "timestamp": lastfm_int_value(row.get("timestamp"), 0),
                "nowPlaying": False,
            },
        )
        item["playcount"] += 1
        row_ts = lastfm_int_value(row.get("timestamp"), 0)
        if row_ts >= lastfm_int_value(item.get("timestamp"), 0):
            item["timestamp"] = row_ts
            if row.get("image"):
                item["image"] = str(row.get("image") or "")
            if row.get("url"):
                item["url"] = str(row.get("url") or "")
            if mode == "artists" and album:
                item["album"] = album

    ordered = sorted(
        buckets.values(),
        key=lambda item: (-lastfm_int_value(item.get("playcount"), 0), -lastfm_int_value(item.get("timestamp"), 0), str(item.get("title") or "").casefold()),
    )
    for index, item in enumerate(ordered[:limit], start=1):
        item["rank"] = index
    return ordered[:limit]


def lastfm_recent_items(rows: list[dict[str, Any]], limit: int) -> list[dict[str, Any]]:
    items: list[dict[str, Any]] = []
    for raw in rows[:limit]:
        artist = str(raw.get("artist") or "").strip()
        track = str(raw.get("track") or "").strip()
        if not artist or not track:
            continue
        items.append(
            {
                "rank": len(items) + 1,
                "artist": artist,
                "title": track,
                "album": str(raw.get("album") or "").strip(),
                "playcount": 1,
                "image": str(raw.get("image") or ""),
                "url": str(raw.get("url") or ""),
                "timestamp": lastfm_int_value(raw.get("timestamp"), 0),
                "nowPlaying": bool(raw.get("nowPlaying")),
            }
        )
    return items


@app.route("/api/lastfm-artist-image", methods=["GET"])
def api_lastfm_artist_image():
    username = str(request.args.get("user") or LASTFM_PROFILE_USERNAME).strip() or LASTFM_PROFILE_USERNAME
    if username.casefold() != LASTFM_PROFILE_USERNAME.casefold():
        return "Unknown Last.fm profile.", 400

    artist = str(request.args.get("artist") or "").strip()
    artist_url = str(request.args.get("url") or "").strip()
    if not artist:
        return "Artist is required.", 400

    image_url = lastfm_artist_image_url(username, artist, artist_url)
    if not image_url:
        return "Artist image was not found.", 404

    response = redirect(image_url, code=302)
    # Artist-image choice may change independently of the chart. Avoid pinning a
    # bad redirect (such as the former profile-avatar result) in the browser.
    response.headers["Cache-Control"] = "no-store, max-age=0"
    response.headers["Pragma"] = "no-cache"
    return response


@app.route("/api/lastfm-cover-options", methods=["GET"])
def api_lastfm_cover_options():
    admin_error = require_topster_admin_response()
    if admin_error is not None:
        return admin_error

    username = str(request.args.get("user") or LASTFM_PROFILE_USERNAME).strip() or LASTFM_PROFILE_USERNAME
    if username.casefold() != LASTFM_PROFILE_USERNAME.casefold():
        return jsonify({"ok": False, "error": "Unknown Last.fm profile."}), 400

    mode = str(request.args.get("mode") or "albums").strip().lower()
    if mode not in {"albums", "songs", "artists", "recent"}:
        return jsonify({"ok": False, "error": "Unsupported Last.fm display mode."}), 400

    artist = str(request.args.get("artist") or "").strip()
    title = str(request.args.get("title") or "").strip()
    album = str(request.args.get("album") or "").strip()
    item_url = str(request.args.get("url") or "").strip()
    if not artist and not title:
        return jsonify({"ok": False, "error": "Artist or title is required."}), 400

    # Top-track responses do not always include the album name. Resolve it with
    # Last.fm's own API so the picker can also inspect the corresponding release
    # page; no non-Last.fm image provider is queried here.
    if mode in {"songs", "recent"} and artist and title and not album:
        try:
            payload = lastfm_json_request(
                {
                    "method": "track.getInfo",
                    "artist": artist,
                    "track": title,
                    "username": username,
                }
            )
            track_info = payload.get("track") if isinstance(payload.get("track"), dict) else {}
            album_info = track_info.get("album") if isinstance(track_info.get("album"), dict) else {}
            album = str(album_info.get("title") or "").strip()
        except Exception:
            pass

    source_pages = lastfm_cover_option_pages(mode, artist, title, album, item_url)
    image_urls: list[str] = []
    for page_url in source_pages:
        html_text = fetch_lastfm_html(page_url)
        for image_url in extract_lastfm_page_image_candidates(
            html_text,
            include_artist_gallery=(mode == "artists"),
            limit=24,
        ):
            if image_url not in image_urls:
                image_urls.append(image_url)
        if len(image_urls) >= 24:
            break

    # Last.fm API image arrays are a legitimate final Last.fm-only fallback when
    # the public page markup exposes no usable hero image.
    if not image_urls:
        try:
            if mode == "artists":
                payload = lastfm_json_request({"method": "artist.getInfo", "artist": artist or title, "username": username})
                info = payload.get("artist") if isinstance(payload.get("artist"), dict) else {}
                fallback = best_lastfm_image_url(info.get("image"))
            elif mode == "albums":
                release = album or title
                payload = lastfm_json_request({"method": "album.getInfo", "artist": artist, "album": release, "username": username})
                info = payload.get("album") if isinstance(payload.get("album"), dict) else {}
                fallback = best_lastfm_image_url(info.get("image"))
            else:
                payload = lastfm_json_request({"method": "track.getInfo", "artist": artist, "track": title, "username": username})
                track_info = payload.get("track") if isinstance(payload.get("track"), dict) else {}
                album_info = track_info.get("album") if isinstance(track_info.get("album"), dict) else {}
                fallback = best_lastfm_image_url(album_info.get("image"))
            fallback = useful_lastfm_image_url(fallback)
            if fallback:
                image_urls.append(fallback)
        except Exception:
            pass

    return jsonify(
        {
            "ok": True,
            "mode": mode,
            "artist": artist,
            "title": title,
            "album": album,
            "sourcePages": source_pages,
            "candidates": [
                {"imageSrc": url, "source": "Last.fm", "href": source_pages[0] if source_pages else ""}
                for url in image_urls[:24]
            ],
        }
    )


@app.route("/api/lastfm-chart", methods=["GET"])
def api_lastfm_chart():
    restricted = require_topster_admin_response()
    if restricted is not None:
        return restricted

    username = str(request.args.get("user") or LASTFM_PROFILE_USERNAME).strip() or LASTFM_PROFILE_USERNAME
    if username.casefold() != LASTFM_PROFILE_USERNAME.casefold():
        return jsonify({"ok": False, "error": "Only the configured Last.fm profile is available."}), 400

    mode = str(request.args.get("mode") or "albums").strip().lower()
    period = str(request.args.get("period") or "7day").strip().lower()
    if mode not in {"albums", "songs", "artists", "recent"}:
        return jsonify({"ok": False, "error": "Unknown Last.fm chart mode."}), 400
    if period not in {"1day", "7day", "14day", "1month", "3month", "6month", "12month", "overall", "custom"}:
        return jsonify({"ok": False, "error": "Unknown Last.fm period."}), 400

    limit = min(LASTFM_CHART_MAX_ITEMS, max(1, lastfm_int_value(request.args.get("limit"), 100)))
    custom_from = lastfm_int_value(request.args.get("from"), 0) or None
    custom_to = lastfm_int_value(request.args.get("to"), 0) or None
    if period == "custom":
        if custom_from is None or custom_to is None or custom_from >= custom_to:
            return jsonify({"ok": False, "error": "Custom Last.fm windows require a valid start and end time."}), 400

    try:
        direct_period = lastfm_direct_period(period)
        truncated = False
        sampled_scrobbles = 0
        weekly_ranges_used = 0
        weekly_ranges_failed = 0

        if mode != "recent" and direct_period:
            items = lastfm_direct_chart(username, mode, direct_period, limit)
            source = "Last.fm top chart"
        elif mode != "recent" and period == "custom":
            (
                items,
                sampled_scrobbles,
                truncated,
                weekly_ranges_used,
                weekly_ranges_failed,
            ) = lastfm_custom_aggregate_weekly(
                username,
                mode,
                int(custom_from),
                int(custom_to),
                limit,
            )
            source = "Last.fm weekly-chart aggregation"
        else:
            from_ts, to_ts = lastfm_period_bounds(period, custom_from, custom_to)
            recent_cap = limit if mode == "recent" else LASTFM_RECENT_MAX_SCROBBLES
            rows, truncated = lastfm_recent_track_rows(username, from_ts, to_ts, max_scrobbles=recent_cap)
            sampled_scrobbles = len(rows)
            if mode == "recent":
                items = lastfm_recent_items(rows, limit)
                # Reaching the requested display limit is normal for Recently Played;
                # only aggregate modes need to report the 50k safety cap.
                truncated = False
                source = "Last.fm recent tracks"
            else:
                items = lastfm_aggregate_recent(rows, mode, limit)
                source = "Last.fm recent-track aggregation"

        enrich_lastfm_chart_images(username, mode, items)

        return jsonify(
            {
                "ok": True,
                "user": username,
                "mode": mode,
                "period": period,
                "from": custom_from if period == "custom" else lastfm_period_bounds(period)[0],
                "to": custom_to if period == "custom" else lastfm_period_bounds(period)[1],
                "items": items,
                "itemCount": len(items),
                "sampledScrobbles": sampled_scrobbles,
                "truncated": truncated,
                "weeklyRangesUsed": weekly_ranges_used,
                "weeklyRangesFailed": weekly_ranges_failed,
                "source": source,
                "generatedAt": int(time.time()),
            }
        )
    except Exception as error:
        return jsonify({"ok": False, "error": str(error)}), 502


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
    album_artists = [
        str(artist.get("name") or "").strip()
        for artist in (album.get("artists") or [])
        if isinstance(artist, dict) and str(artist.get("name") or "").strip()
    ]
    if not album_artists:
        album_artists = list(artists)
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

    playback_context = playback.get("context") if isinstance(playback.get("context"), dict) else {}
    context_uri = str(playback_context.get("uri") or "").strip()
    context_type = str(playback_context.get("type") or "").strip()

    return {
        "key": track_key,
        "id": item.get("id"),
        "uri": uri,
        "title": title,
        "artists": artists,
        "artist": ", ".join(artists) or "Unknown artist",
        "albumArtists": album_artists,
        "albumArtist": ", ".join(album_artists) or (", ".join(artists) or "Unknown artist"),
        "album": album_name or "Unknown album",
        "albumId": album.get("id"),
        "albumUri": str(album.get("uri") or "").strip(),
        "contextUri": context_uri,
        "contextType": context_type,
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
    cache_key = f"v{GENIUS_LOOKUP_CACHE_VERSION}::" + str(track.get("key") or "")
    now = time.time()

    # Check the per-track cache before the manual album mapping path. A manually
    # linked Genius album resolves a song ID and then performs /songs/{id}; with
    # /api/lyrics/current polled every few seconds, doing manual resolution first
    # caused that details request to bypass the normal seven-day cache entirely.
    with GENIUS_LOOKUP_CACHE_LOCK:
        cached = GENIUS_LOOKUP_CACHE.get(cache_key)
        if isinstance(cached, dict):
            ttl = GENIUS_MATCH_TTL_SECONDS if cached.get("value") else GENIUS_MISS_TTL_SECONDS
            if now - float(cached.get("timestamp") or 0) < ttl:
                return cached.get("value")

    manual_result = lookup_genius_song_from_manual_album_link(track)
    if manual_result is not None:
        with GENIUS_LOOKUP_CACHE_LOCK:
            GENIUS_LOOKUP_CACHE[cache_key] = {"timestamp": now, "value": manual_result}
            if len(GENIUS_LOOKUP_CACHE) > GENIUS_LOOKUP_CACHE_MAX_ITEMS:
                oldest_key = min(
                    GENIUS_LOOKUP_CACHE,
                    key=lambda key: float(GENIUS_LOOKUP_CACHE[key].get("timestamp") or 0),
                )
                GENIUS_LOOKUP_CACHE.pop(oldest_key, None)
        return manual_result

    title = str(track.get("title") or "").strip()
    artists = [str(value).strip() for value in (track.get("artists") or []) if str(value).strip()]
    album_name = str(track.get("album") or "").strip()
    primary_artist = artists[0] if artists else ""

    cleaned_title = clean_lyrics_track_title(title)
    cleaned_album = clean_lyrics_album_title(album_name)
    exact_query = " ".join(part for part in (title, primary_artist) if part).strip()
    cleaned_query = " ".join(part for part in (cleaned_title, primary_artist) if part).strip()
    album_query = " ".join(
        part for part in (cleaned_title, primary_artist, cleaned_album) if part
    ).strip()

    title_was_simplified = (
        normalize_lyrics_match_text(cleaned_title)
        != normalize_lyrics_match_text(title)
    )
    album_was_simplified = (
        normalize_lyrics_match_text(cleaned_album)
        != normalize_lyrics_match_text(album_name)
    )
    versioned_track = title_was_simplified or album_was_simplified

    queries: list[str] = []
    def add_query(value: str) -> None:
        query = str(value or "").strip()
        if query and query not in queries:
            queries.append(query)

    # For live/remastered Spotify tracks, ask Genius for the base song + album
    # identity first. This makes "Deuce ... 2025 Remaster" favor the Alive! page
    # instead of a studio Deuce result or a remaster metadata stub.
    if versioned_track:
        add_query(album_query)
    add_query(exact_query)
    add_query(cleaned_query)
    if not versioned_track:
        add_query(album_query)

    candidates: dict[int, dict[str, Any]] = {}
    for query in queries[:3]:
        payload = genius_search_request(query)
        for song in genius_song_hits(payload):
            try:
                song_id = int(song.get("id"))
            except (TypeError, ValueError):
                continue
            candidates[song_id] = song
        if candidates:
            best_now = max(
                score_genius_song_match(song, title, artists, album_name)
                for song in candidates.values()
            )
            # Normal tracks keep the fast one-query path. Versioned/live tracks
            # require a stronger match before short-circuiting so a generic studio
            # result cannot prevent the album-specific query from being considered.
            threshold = 105.0 if versioned_track else 90.0
            if best_now >= threshold:
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



def lyrics_my_albums_redis_key() -> str:
    safe_prefix = TOPSTER_REDIS_KEY_PREFIX.strip(":") or "navincitron:topster"
    return f"{safe_prefix}:lyrics:my-albums"


def get_lyrics_github_token() -> str:
    return normalize_secret_text(os.getenv("LYRICS_GITHUB_TOKEN") or os.getenv("GITHUB_TOKEN"))


def lyrics_github_repository_parts() -> tuple[str, str] | None:
    repository = str(LYRICS_GITHUB_REPOSITORY or "").strip().strip("/")
    if repository.startswith("https://github.com/"):
        repository = repository[len("https://github.com/"):]
    if repository.endswith(".git"):
        repository = repository[:-4]
    parts = repository.split("/", 1)
    if len(parts) != 2 or not all(part.strip() for part in parts):
        return None
    return parts[0].strip(), parts[1].strip()


def lyrics_github_is_configured() -> bool:
    return lyrics_github_repository_parts() is not None


def lyrics_github_contents_url() -> str:
    parts = lyrics_github_repository_parts()
    if parts is None:
        raise RuntimeError(
            "GitHub score synchronization is not configured. Set LYRICS_GITHUB_REPOSITORY to owner/repository."
        )
    owner, repository = parts
    path = quote(LYRICS_GITHUB_MY_ALBUMS_PATH, safe="/")
    return f"https://api.github.com/repos/{quote(owner)}/{quote(repository)}/contents/{path}"


def lyrics_github_request_json(
    url: str,
    *,
    method: str = "GET",
    payload: dict[str, Any] | None = None,
    require_token: bool = False,
) -> dict[str, Any]:
    token = get_lyrics_github_token()
    if require_token and not token:
        raise RuntimeError(
            "GitHub score saving requires LYRICS_GITHUB_TOKEN (or GITHUB_TOKEN) with Contents read/write access."
        )

    headers = {
        "Accept": "application/vnd.github+json",
        "User-Agent": "navincitron-lyrics-score-sync/1.0",
        "X-GitHub-Api-Version": "2022-11-28",
    }
    if token:
        headers["Authorization"] = f"Bearer {token}"

    data = None
    if payload is not None:
        data = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        headers["Content-Type"] = "application/json"

    github_request = Request(url, data=data, headers=headers, method=method)
    try:
        with urlopen(github_request, timeout=12) as github_response:
            raw = github_response.read().decode("utf-8", errors="replace")
    except HTTPError as error:
        body = error.read().decode("utf-8", errors="replace")
        try:
            detail = (json.loads(body) or {}).get("message") or body
        except Exception:
            detail = body
        detail = str(detail or error.reason or f"HTTP {error.code}").strip()
        raise RuntimeError(f"GitHub my_albums.txt request failed ({error.code}): {detail}") from error
    except URLError as error:
        raise RuntimeError(f"GitHub my_albums.txt request failed: {error.reason}") from error

    if not raw.strip():
        return {}
    try:
        decoded = json.loads(raw)
    except json.JSONDecodeError as error:
        raise RuntimeError("GitHub returned an invalid JSON response for my_albums.txt.") from error
    return decoded if isinstance(decoded, dict) else {}


def read_lyrics_my_albums_from_github() -> tuple[str, str]:
    if not lyrics_github_is_configured():
        raise RuntimeError(
            "GitHub score synchronization is not configured. Set LYRICS_GITHUB_REPOSITORY to owner/repository."
        )
    url = lyrics_github_contents_url() + "?" + urlencode({"ref": LYRICS_GITHUB_BRANCH})
    payload = lyrics_github_request_json(url)
    encoded = str(payload.get("content") or "").replace("\n", "")
    if not encoded:
        raise RuntimeError(
            f"GitHub did not return {LYRICS_GITHUB_MY_ALBUMS_PATH} from branch {LYRICS_GITHUB_BRANCH}."
        )
    try:
        text = base64.b64decode(encoded, validate=False).decode("utf-8")
    except Exception as error:
        raise RuntimeError("GitHub returned my_albums.txt in an unreadable encoding.") from error
    return text.replace("\r\n", "\n").replace("\r", "\n"), str(payload.get("sha") or "")


def synchronize_lyrics_my_albums_backend_text(text: str) -> tuple[list[str], list[str]]:
    """Mirror the canonical GitHub text into Redis and the Render runtime file."""
    written: list[str] = []
    warnings: list[str] = []
    normalized = str(text or "").replace("\r\n", "\n").replace("\r", "\n")

    if topster_redis_is_configured():
        client = get_topster_redis_client()
        if client is None:
            warnings.append(TOPSTER_REDIS_CLIENT_ERROR or "Redis is configured but unavailable.")
        else:
            try:
                client.set(lyrics_my_albums_redis_key(), normalized)
                written.append("redis")
            except RedisError as error:
                warnings.append(f"Lyrics score Redis write failed: {error}")

    try:
        temp_path = LYRICS_MY_ALBUMS_FILE.with_suffix(LYRICS_MY_ALBUMS_FILE.suffix + ".tmp")
        temp_path.write_text(normalized, encoding="utf-8")
        temp_path.replace(LYRICS_MY_ALBUMS_FILE)
        written.append("file")
    except OSError as error:
        warnings.append(f"Could not write runtime {LYRICS_MY_ALBUMS_FILE.name}: {error}")

    return written, warnings


def read_lyrics_my_albums_text() -> tuple[str, str, str, list[str]]:
    """
    Return score text, source, GitHub revision, and warnings.

    When GitHub synchronization is configured, the repository copy is canonical.
    This means a desktop edit becomes authoritative after it is committed/pushed to
    the configured branch; the next Lyrics score read mirrors it into Redis and the
    Render runtime file automatically.
    """
    warnings: list[str] = []
    if lyrics_github_is_configured():
        try:
            text, revision = read_lyrics_my_albums_from_github()
            _, sync_warnings = synchronize_lyrics_my_albums_backend_text(text)
            warnings.extend(sync_warnings)
            return text, "github", revision, warnings
        except RuntimeError as error:
            warnings.append(str(error))

    if topster_redis_is_configured():
        client = get_topster_redis_client()
        if client is None:
            warnings.append(TOPSTER_REDIS_CLIENT_ERROR or "Redis is configured but unavailable.")
        else:
            try:
                stored = client.get(lyrics_my_albums_redis_key())
            except RedisError as error:
                warnings.append(f"Lyrics score Redis read failed: {error}")
            else:
                if stored is not None:
                    return str(stored), "redis", "", warnings

    if LYRICS_MY_ALBUMS_FILE.exists():
        try:
            return LYRICS_MY_ALBUMS_FILE.read_text(encoding="utf-8"), "file", "", warnings
        except OSError as error:
            warnings.append(f"Could not read {LYRICS_MY_ALBUMS_FILE.name}: {error}")

    return "", "none", "", warnings


def lyrics_score_file_tracklist_blocks(text: str) -> dict[tuple[str, int], set[str]]:
    """Index existing album sections, not their editable numeric score values."""
    found: dict[tuple[str, int], set[str]] = {}
    seen: dict[str, int] = {}
    for block in re.split(r"\n\s*\n", str(text or "").replace("\r\n", "\n")):
        lines = [line.strip() for line in block.splitlines() if line.strip()]
        if len(lines) < 2:
            continue
        header = re.fullmatch(r"(.+?):\s*(?:(?:-?\d+(?:\.\d+)?%)?)\s*", lines[0])
        if not header:
            continue
        album_title = normalize_lyrics_match_text(header.group(1))
        if not album_title:
            continue
        titles: set[str] = set()
        for line in lines[1:]:
            track = re.fullmatch(r"(.+?):\s*(?:-?\d+(?:\.\d+)?\**(?:\s+.*)?|-|\u2014)?\s*", line)
            if track:
                track_title = normalize_lyrics_match_text(track.group(1))
                if track_title:
                    titles.add(track_title)
        if not titles:
            continue
        occurrence = seen.get(album_title, 0)
        seen[album_title] = occurrence + 1
        found[(album_title, occurrence)] = titles
    return found


def assert_my_albums_tracklists_not_replaced(current_text: str, proposed_text: str) -> None:
    """Refuse destructive same-heading, different-album tracklist replacement.

    The Lyrics editor updates scores, not the identity of an album. A client-side
    title collision once replaced the self-titled Bob Dylan album's 13 songs with
    the 22-song Rolling Thunder Revue tracklist, preserving the old percentage.
    Reject that mutation even if the browser is stale or has a matching bug.
    """
    existing = lyrics_score_file_tracklist_blocks(current_text)
    proposed = lyrics_score_file_tracklist_blocks(proposed_text)
    for key, original_titles in existing.items():
        replacement_titles = proposed.get(key)
        if replacement_titles is None:
            continue
        if min(len(original_titles), len(replacement_titles)) < 5:
            continue
        common = len(original_titles & replacement_titles)
        if common < 3 or common / min(len(original_titles), len(replacement_titles)) < 0.40:
            raise RuntimeError(
                f"Refusing to replace the tracklist of existing album '{key[0]}': "
                "the submitted tracks belong to a different release. "
                "Restore or deliberately restructure albums directly in my_albums.txt "
                "on GitHub instead of replacing them through the Lyrics score editor."
            )


def write_lyrics_my_albums_text(text: str, base_revision: str = "") -> tuple[str, str, list[str]]:
    """
    Save score text to GitHub first, then mirror that exact committed text to the
    Lyrics backend stores. GitHub is therefore the canonical copy shared by GitHub
    Pages, website edits, and later desktop commits.
    """
    if not lyrics_github_is_configured():
        raise RuntimeError(
            "Score saving is configured to update both GitHub Pages and the Lyrics backend, but "
            "LYRICS_GITHUB_REPOSITORY is not set."
        )
    if not get_lyrics_github_token():
        raise RuntimeError(
            "Score saving requires LYRICS_GITHUB_TOKEN (or GITHUB_TOKEN) with Contents read/write access."
        )

    normalized = str(text or "").replace("\r\n", "\n").replace("\r", "\n")
    current_text, current_revision = read_lyrics_my_albums_from_github()
    requested_base = str(base_revision or "").strip()
    if not requested_base or not current_revision:
        raise RuntimeError(
            "Cannot safely save scores without the current GitHub revision. "
            "Refresh the Lyrics page before editing to avoid overwriting newer entries."
        )
    if requested_base != current_revision:
        raise RuntimeError(
            "my_albums.txt changed on GitHub after this page loaded. Refresh the page before saving so newer desktop/GitHub edits are not overwritten."
        )

    assert_my_albums_tracklists_not_replaced(current_text, normalized)

    revision = current_revision
    if normalized != current_text:
        body: dict[str, Any] = {
            "message": "Update my_albums.txt from Lyrics score editor",
            "content": base64.b64encode(normalized.encode("utf-8")).decode("ascii"),
            "branch": LYRICS_GITHUB_BRANCH,
        }
        if current_revision:
            body["sha"] = current_revision
        result = lyrics_github_request_json(
            lyrics_github_contents_url(),
            method="PUT",
            payload=body,
            require_token=True,
        )
        content = result.get("content") if isinstance(result.get("content"), dict) else {}
        revision = str(content.get("sha") or revision)

    written, warnings = synchronize_lyrics_my_albums_backend_text(normalized)
    storage_parts = ["github", *written]
    return "+".join(dict.fromkeys(storage_parts)), revision, warnings


@app.route("/api/lyrics/my-albums", methods=["GET", "PUT"])
def lyrics_my_albums():
    if request.method == "PUT":
        admin_error = require_topster_admin_response()
        if admin_error is not None:
            return admin_error

        payload = request.get_json(silent=True) or {}
        text = payload.get("text")
        base_revision = str(payload.get("baseRevision") or "").strip()
        if not isinstance(text, str):
            return jsonify({"ok": False, "error": "A complete my_albums text string is required."}), 400
        if len(text.encode("utf-8")) > 2_000_000:
            return jsonify({"ok": False, "error": "my_albums.txt exceeds the 2 MB edit limit."}), 413

        try:
            storage, revision, warnings = write_lyrics_my_albums_text(text, base_revision=base_revision)
        except RuntimeError as error:
            message = str(error)
            status_code = 409 if (
                "changed on GitHub after this page loaded" in message
                or "Refusing to replace the tracklist" in message
                or "Cannot safely save scores" in message
            ) else 503
            return jsonify({"ok": False, "error": message}), status_code

        response = jsonify({
            "ok": True,
            "text": text.replace("\r\n", "\n").replace("\r", "\n"),
            "storage": storage,
            "revision": revision,
            "warnings": warnings,
        })
        response.headers["Cache-Control"] = "no-store"
        return response

    text, storage, revision, warnings = read_lyrics_my_albums_text()
    response = jsonify({
        "ok": True,
        "text": text,
        "storage": storage,
        "revision": revision,
        "warnings": warnings,
        "githubConfigured": lyrics_github_is_configured(),
        "githubWritable": bool(lyrics_github_is_configured() and get_lyrics_github_token()),
        "writable": is_topster_admin(),
    })
    response.headers["Cache-Control"] = "no-store"
    return response


@app.route("/api/lyrics/genius-album-link", methods=["GET", "POST"])
def lyrics_genius_album_link():
    if request.method == "GET":
        artist = str(request.args.get("artist") or "").strip()
        album = str(request.args.get("album") or "").strip()
        if not album:
            return jsonify({"ok": False, "error": "Album is required."}), 400
        mapping = read_lyrics_genius_album_link(artist, album)
        return jsonify({
            "ok": True,
            "linked": bool(mapping),
            "mapping": {
                "artist": mapping.get("artist"),
                "album": mapping.get("album"),
                "url": mapping.get("url"),
                "albumId": mapping.get("albumId"),
                "trackCount": len(mapping.get("tracks") or []),
            } if mapping else None,
        })

    admin_error = require_topster_admin_response()
    if admin_error is not None:
        return admin_error
    payload = request.get_json(silent=True) or {}
    artist = str(payload.get("artist") or "").strip()
    album = str(payload.get("album") or "").strip()
    track = str(payload.get("track") or "").strip()
    if not album:
        return jsonify({"ok": False, "error": "The currently playing album does not have a usable title."}), 400
    try:
        url = validate_genius_album_url(payload.get("url"))
        album_id = fetch_genius_album_id_from_url(url, artist, album, track)
        tracks = fetch_genius_album_tracks(album_id)
        identity = lyrics_manual_album_identity(artist, album)
        if not identity:
            raise ValueError("The currently playing album does not have a usable identity.")
        saved = write_lyrics_genius_album_link({
            "identity": identity,
            "artist": artist,
            "album": album,
            "url": url,
            "albumId": album_id,
            "tracks": tracks,
        })
        with GENIUS_LOOKUP_CACHE_LOCK:
            GENIUS_LOOKUP_CACHE.clear()
        return jsonify({
            "ok": True,
            "linked": True,
            "mapping": {
                "artist": saved.get("artist"),
                "album": saved.get("album"),
                "url": saved.get("url"),
                "albumId": saved.get("albumId"),
                "trackCount": len(saved.get("tracks") or []),
            },
        })
    except ValueError as error:
        return jsonify({"ok": False, "error": str(error)}), 400
    except Exception as error:
        return jsonify({"ok": False, "error": str(error)}), 502




@app.route("/api/lyrics/genius-content/<int:song_id>", methods=["GET"])
def api_lyrics_genius_content(song_id: int):
    if song_id <= 0:
        return jsonify({"ok": False, "error": "Invalid Genius song ID."}), 400
    try:
        content = fetch_genius_song_lyrics(song_id)
        response = jsonify({"ok": True, **content})
        response.headers["Cache-Control"] = "public, max-age=21600"
        return response
    except Exception as error:
        response = jsonify({"ok": False, "error": str(error)})
        response.status_code = 502
        response.headers["Cache-Control"] = "no-store"
        return response


@app.route("/api/lyrics/genius-referents/<int:song_id>", methods=["GET"])
def api_lyrics_genius_referents(song_id: int):
    """Return all non-description Genius referents for one song.

    The official Genius embed is cross-origin, so the frontend cannot read the
    clicked lyric anchor out of the embedded frame. Keeping the referents
    available through our same-origin API lets the host page show annotations
    without scraping genius.com or depending on a second lyrics provider.
    """
    if song_id <= 0:
        return jsonify({"ok": False, "error": "Invalid Genius song ID."}), 400
    try:
        raw_referents = genius_song_referents(song_id)
        referents: list[dict[str, Any]] = []
        for raw_referent in raw_referents:
            try:
                referent_id = int(raw_referent.get("id") or 0)
            except (TypeError, ValueError):
                continue
            if referent_id <= 0:
                continue
            referent = build_genius_referent_payload(
                {"response": {"referent": raw_referent}},
                referent_id,
            )
            if referent.get("fragment") and referent.get("annotations"):
                referents.append(referent)

        response = jsonify({
            "ok": True,
            "songId": int(song_id),
            "referents": referents,
            "count": sum(len(item.get("annotations") or []) for item in referents),
        })
        response.headers["Cache-Control"] = "public, max-age=3600"
        return response
    except Exception as error:
        response = jsonify({"ok": False, "error": str(error)})
        response.status_code = 502
        response.headers["Cache-Control"] = "no-store"
        return response


@app.route("/api/lyrics/genius-referent/<int:referent_id>", methods=["GET"])
def api_lyrics_genius_referent(referent_id: int):
    if referent_id <= 0:
        return jsonify({"ok": False, "error": "Invalid Genius referent ID."}), 400
    try:
        payload = genius_referent_request(referent_id)
        referent = build_genius_referent_payload(payload, referent_id)
        response = jsonify({"ok": True, "referent": referent})
        response.headers["Cache-Control"] = "public, max-age=3600"
        return response
    except Exception as error:
        response = jsonify({"ok": False, "error": str(error)})
        response.status_code = 502
        response.headers["Cache-Control"] = "no-store"
        return response


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

    track["manualCoverOverride"] = read_lyrics_album_cover_override(
        track.get("artist") or "",
        track.get("album") or "",
    )

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



def spotify_track_part_range_signature(value: Any) -> str:
    text = unicodedata.normalize("NFKD", str(value or ""))
    text = "".join(ch for ch in text if not unicodedata.combining(ch))
    text = text.replace("–", "-").replace("\u2014", "-").replace("−", "-")
    match = re.search(r"\b(?:parts?|pts?\.?)\s*(\d+)\s*-\s*(\d+)\b", text, flags=re.IGNORECASE)
    if not match:
        return ""
    return f"{int(match.group(1))}-{int(match.group(2))}"


def spotify_discogs_track_match_score(target_title: Any, spotify_title: Any) -> float:
    target_part_range = spotify_track_part_range_signature(target_title)
    spotify_part_range = spotify_track_part_range_signature(spotify_title)
    if target_part_range and spotify_part_range and target_part_range != spotify_part_range:
        return 0.0

    target_key = normalize_lyrics_match_text(target_title)
    spotify_key = normalize_lyrics_match_text(spotify_title)
    if target_key and target_key == spotify_key:
        return 1.0

    score = discogs_track_title_match_score(target_title, spotify_title)
    if target_part_range and spotify_part_range and target_part_range == spotify_part_range:
        score = max(score, 0.98)
    return score


def spotify_album_name_matches(left: Any, right: Any) -> bool:
    left_text = str(left or "").strip()
    right_text = str(right or "").strip()
    if not left_text or not right_text:
        return True

    left_key = normalize_lyrics_match_text(clean_lyrics_album_title(left_text))
    right_key = normalize_lyrics_match_text(clean_lyrics_album_title(right_text))
    if left_key and left_key == right_key:
        return True

    raw_left = normalize_lyrics_match_text(left_text)
    raw_right = normalize_lyrics_match_text(right_text)
    return bool(raw_left and raw_left == raw_right)


def spotify_album_tracks_all(spotify_client: Any, album_id: str) -> list[dict[str, Any]]:
    tracks: list[dict[str, Any]] = []
    offset = 0
    limit = 50
    while True:
        page = spotify_client.album_tracks(album_id, limit=limit, offset=offset)
        items = page.get("items") if isinstance(page, dict) else None
        if isinstance(items, list):
            tracks.extend(item for item in items if isinstance(item, dict))
        if not isinstance(page, dict) or not page.get("next"):
            break
        offset += limit
    return tracks


def spotify_playlist_items_all(spotify_client: Any, playlist_id: str) -> list[tuple[int, dict[str, Any]]]:
    results: list[tuple[int, dict[str, Any]]] = []
    offset = 0
    limit = 100

    while True:
        try:
            page = spotify_client.playlist_items(
                playlist_id,
                limit=limit,
                offset=offset,
                additional_types=("track",),
            )
        except TypeError:
            page = spotify_client.playlist_items(
                playlist_id,
                limit=limit,
                offset=offset,
            )

        raw_items = page.get("items") if isinstance(page, dict) else None
        if not isinstance(raw_items, list):
            break

        for index, wrapper in enumerate(raw_items):
            if not isinstance(wrapper, dict):
                continue
            item = wrapper.get("item")
            if not isinstance(item, dict):
                item = wrapper.get("track")
            if not isinstance(item, dict):
                continue
            results.append((offset + index, item))

        if not page.get("next"):
            break
        offset += limit

    return results


def spotify_best_target_track(
    candidates: list[dict[str, Any]],
    target_title: str,
) -> tuple[dict[str, Any] | None, float]:
    best_item: dict[str, Any] | None = None
    best_score = 0.0
    for item in candidates:
        title = str(item.get("name") or "").strip()
        score = spotify_discogs_track_match_score(target_title, title)
        if score > best_score:
            best_score = score
            best_item = item
    return best_item, best_score


@app.route("/api/lyrics/play-track", methods=["POST"])
def lyrics_play_track():
    payload = request.get_json(silent=True) or {}
    target_title = str(payload.get("title") or "").strip()
    requested_album = str(payload.get("album") or "").strip()

    if not target_title:
        return jsonify({
            "ok": False,
            "authenticated": True,
            "error": "A track title is required.",
        }), 400

    try:
        spotify_client = get_spotify_client()
    except SpotifyLoginRequired as error:
        response = jsonify({
            "ok": False,
            "authenticated": False,
            "error": str(error),
        })
        response.status_code = 401
        response.headers["Cache-Control"] = "no-store"
        return response
    except SpotifyTokenRefreshTemporarilyUnavailable as error:
        response = jsonify({
            "ok": False,
            "authenticated": True,
            "temporarilyUnavailable": True,
            "error": str(error),
        })
        response.status_code = 503
        response.headers["Retry-After"] = "6"
        response.headers["Cache-Control"] = "no-store"
        return response

    try:
        try:
            playback = spotify_client.current_playback(additional_types="track")
        except TypeError:
            playback = spotify_client.current_playback()

        if not isinstance(playback, dict):
            raise RuntimeError("Spotify does not currently have an active playback context.")

        current_item = playback.get("item") if isinstance(playback.get("item"), dict) else {}
        current_album = current_item.get("album") if isinstance(current_item.get("album"), dict) else {}
        current_album_name = str(current_album.get("name") or requested_album or "").strip()
        album_id = str(current_album.get("id") or "").strip()
        album_uri = str(current_album.get("uri") or "").strip()
        if album_id and not album_uri:
            album_uri = f"spotify:album:{album_id}"

        # Preferred path: use the current Spotify album itself. This keeps playback
        # in album context, so selecting a Tracklist row still gives Spotify the
        # rest of that album as the queue/context.
        if album_id:
            album_tracks = spotify_album_tracks_all(spotify_client, album_id)
            matched_track, match_score = spotify_best_target_track(album_tracks, target_title)
            matched_uri = str((matched_track or {}).get("uri") or "").strip()
            if matched_track is not None and match_score >= 0.55 and matched_uri:
                spotify_client.start_playback(
                    context_uri=album_uri,
                    offset={"uri": matched_uri},
                    position_ms=0,
                )
                if process_is_running():
                    append_log(f"[lyrics page selected album track: {matched_track.get('name') or target_title}]")
                response = jsonify({
                    "ok": True,
                    "authenticated": True,
                    "matchedTitle": str(matched_track.get("name") or target_title),
                    "source": "album",
                    "message": f"Playing {matched_track.get('name') or target_title} on Spotify.",
                })
                response.headers["Cache-Control"] = "no-store"
                return response

        # Fallback for local files or playlist-only album copies: if the current
        # playback context is a playlist, find the requested Discogs row among
        # playlist items belonging to the same currently playing Spotify album.
        context = playback.get("context") if isinstance(playback.get("context"), dict) else {}
        context_uri = str(context.get("uri") or "").strip()
        context_type = str(context.get("type") or "").strip().lower()

        if context_type == "playlist" and context_uri.startswith("spotify:playlist:"):
            playlist_id = context_uri.rsplit(":", 1)[-1]
            playlist_items = spotify_playlist_items_all(spotify_client, playlist_id)

            best_position: int | None = None
            best_item: dict[str, Any] | None = None
            best_score = 0.0

            for position, item in playlist_items:
                if str(item.get("type") or "track").lower() not in {"", "track"}:
                    continue

                item_album = item.get("album") if isinstance(item.get("album"), dict) else {}
                item_album_name = str(item_album.get("name") or "").strip()
                if not item_album_name:
                    local_meta = local_spotify_uri_metadata(str(item.get("uri") or ""))
                    item_album_name = str(local_meta.get("album") or "").strip()
                if current_album_name and item_album_name and not spotify_album_name_matches(
                    current_album_name,
                    item_album_name,
                ):
                    continue

                score = spotify_discogs_track_match_score(
                    target_title,
                    item.get("name") or "",
                )
                if score > best_score:
                    best_score = score
                    best_position = position
                    best_item = item

            if best_item is not None and best_position is not None and best_score >= 0.55:
                spotify_client.start_playback(
                    context_uri=context_uri,
                    offset={"position": int(best_position)},
                    position_ms=0,
                )
                if process_is_running():
                    append_log(f"[lyrics page selected playlist track: {best_item.get('name') or target_title}]")
                response = jsonify({
                    "ok": True,
                    "authenticated": True,
                    "matchedTitle": str(best_item.get("name") or target_title),
                    "source": "playlist",
                    "message": f"Playing {best_item.get('name') or target_title} on Spotify.",
                })
                response.headers["Cache-Control"] = "no-store"
                return response

        raise RuntimeError(
            f'Could not find a Spotify track corresponding to "{target_title}" '
            "in the current album or playlist context."
        )

    except Exception as error:
        response = jsonify({
            "ok": False,
            "authenticated": True,
            "error": f"Could not play the selected Spotify track: {error}",
        })
        response.status_code = 502
        response.headers["Cache-Control"] = "no-store"
        return response


@app.route("/api/lyrics/control/<action>", methods=["POST"])
def lyrics_playback_control(action: str):
    action = str(action or "").strip().lower()
    allowed_actions = {"restart", "previous", "pause", "play", "next"}
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
        if action == "restart":
            # Spotify's native Previous button restarts the current song before
            # skipping back. lyrics.js handles the short double-press window;
            # this endpoint performs only the restart-to-zero operation.
            spotify_client.seek_track(0)
            if sampler_running:
                append_log("[lyrics page requested: restart current track at 0:00]")
            message = "Restarted the current Spotify track at 0:00."

        elif action == "pause":
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


def songguesser_grid_normalize_artist(value: Any) -> str:
    """Normalized artist identity; tolerate 'The', accents and &/and."""
    text = unicodedata.normalize("NFKD", str(value or "").casefold())
    text = "".join(char for char in text if not unicodedata.combining(char))
    text = re.sub(r"^the\s+", "", text)
    text = text.replace("&", " and ")
    return "".join(re.findall(r"[a-z0-9]+", text))


def songguesser_grid_normalize_album(value: Any) -> str:
    """Normalize edition labels without discarding meaningful album title text."""
    title = str(value or "").strip()
    # A grid entry like 'Arthur (Or The Decline ...)' is preserved. Only
    # recognizable reissue / edition suffixes are removed.
    edition = (
        r"remaster(?:ed|ing)?|deluxe|expanded|anniversary|edition|"
        r"reissue|re-release|re release|bonus|stereo|mono|sampler|"
        r"ultimate\s+collection|(?:19|20)\d{2}\s+mix"
    )
    previous = None
    while title != previous:
        previous = title
        title = re.sub(
            rf"\s*[\[(][^\])]*(?:{edition})[^\])]*[\])]\s*$",
            "", title, flags=re.IGNORECASE,
        )
        title = re.sub(
            rf"\s+[-–\u2014]\s+(?:(?:19|20)\d{{2}}\s+)?(?:{edition})\b.*$",
            "", title, flags=re.IGNORECASE,
        )
        title = re.sub(
            rf"\s+[-–\u2014]\s+(?:19|20)\d{{2}}\s+(?:remaster(?:ed)?|edition|deluxe|mix)\b.*$",
            "", title, flags=re.IGNORECASE,
        )
        title = title.strip()
    text = unicodedata.normalize("NFKD", title.casefold())
    text = "".join(char for char in text if not unicodedata.combining(char))
    text = text.replace("&", " and ")
    return "".join(re.findall(r"[a-z0-9]+", text))


@lru_cache(maxsize=4)
def songguesser_grid_release_year_index(
    path: str, modified_ns: int, file_size: int,
) -> tuple[dict[tuple[str, str], str], dict[str, str]]:
    """Index the live grid.txt file, reloading when its contents change."""
    return songguesser_index_grid_year_lines(
        Path(path).read_text(encoding="utf-8-sig").splitlines()
    )


def songguesser_index_grid_year_lines(lines: list[str]) -> tuple[dict[tuple[str, str], str], dict[str, str]]:
    """Build the same normalized index for the live and bundled Grid data."""
    by_artist_album: dict[tuple[str, str], str] = {}
    by_album: dict[str, tuple[str, str] | None] = {}

    for line in lines:
        line = line.strip()
        # 'The Beatles - Abbey Road (September 26, 1969)'
        match = re.match(r"^(.+?)\s+-\s+(.+?)\s+\([^()]*\b((?:18|19|20)\d{2})\)\s*$", line)
        if not match:
            continue
        artist, title, year = match.groups()
        artist_key = songguesser_grid_normalize_artist(artist)
        album_key = songguesser_grid_normalize_album(title)
        if not artist_key or not album_key:
            continue

        # Square-bracketed AKA labels in the Grid (for example, "The Beatles
        # [The White Album]") are part of the display title, but the underlying
        # Spotify album may be named simply "The Beatles". Index that base as
        # a second, artist-qualified identity; never change the displayed name.
        album_keys = [album_key]
        # The Grid sometimes prefixes an album with the artist, such as
        # 'John Lennon / Plastic Ono Band', where Spotify says 'Plastic Ono
        # Band (The Ultimate Collection)'. Only derive an alias when the
        # prefix is exactly the indexed artist, never for arbitrary slashes.
        artist_prefixed = re.fullmatch(r"(.+?)\s*/\s*(.+)", title)
        if artist_prefixed:
            prefix, remainder = artist_prefixed.groups()
            if songguesser_grid_normalize_artist(prefix) == artist_key:
                alias_key = songguesser_grid_normalize_album(remainder)
                if alias_key and alias_key not in album_keys:
                    album_keys.append(alias_key)
        bracketed = re.fullmatch(r"(.+?)\s+\[([^\[\]]+)\]", title)
        if bracketed:
            base_title, alias_title = bracketed.groups()
            for alternative in (base_title, alias_title):
                alternative_key = songguesser_grid_normalize_album(alternative)
                if alternative_key and alternative_key not in album_keys:
                    album_keys.append(alternative_key)

        for key_album in album_keys:
            key = (artist_key, key_album)
            if key not in by_artist_album:
                by_artist_album[key] = year
            elif by_artist_album[key] != year:
                by_artist_album[key] = ""  # Conflicting dates are ambiguous.

            current = by_album.get(key_album)
            if key_album not in by_album:
                by_album[key_album] = (artist_key, year)
            elif current is not None and current != (artist_key, year):
                by_album[key_album] = None  # Different artist/year is ambiguous.

    # Only permit title-only matching when we have no usable artist identity.
    unique_titles = {
        album_key: item[1] for album_key, item in by_album.items()
        if item is not None and by_artist_album.get((item[0], album_key)) == item[1]
    }
    return by_artist_album, unique_titles



# Offline release-year index generated from the user-provided Grid on 2026-10-19.
# It is a fallback, not a replacement: live grid.txt takes priority.
# Keeping the complete album/year index in app.py allows code-only deployments
# to resolve original years even if Render lacks an up-to-date grid.txt.
SONGGUESSER_GRID_YEAR_SNAPSHOT = (
    "c-ox3TW=i8mL~SzzoLWz)MsNvX-gtSN``Sz#o|rktyz@VdpG(asw!BOn^_rk@<OWgbo$ZH0~;8l4a|X!X>S<)V0h3ljPs`UA2|c~cX)kkt"
    "+-@XQCmHYK3lBJ$XmpUwZ3&fHf6c$jTTuw?``$^MLl=9o2`28w%1?SGMkv9cj)rF-dR&+liu%MzJ2xPhrc>?O;+{#<)W%fSIp?j>$&Y6yS"
    "jIn-CH_SOnW1HZ;Ohr*!|(JuH4v`b??2K7nLjMf)5#8cX7)X4sBkW-XL%2(h(iEC13ZNt{d2*SoMyan=VYD&p9*;*Hk?ku-Dr+WnpI-J>2"
    "AZ@4fl*rMK^j37&;J?EN=9`IF0^_g?wS_gz!ey@9Fd8C$)JGMi<E$?3w$#PqK0#FbOJPTu$J4}Wz-Z%Xgm)bo-r7&aAM?H+QvMV^}}58VE"
    "drqG&cZ(#F$rC)WHO^a+cuY04Von-U~41D>+U*R0T^1jP$@4C#KUeGy+;oIvka6PA$IyJN)Cspq!*Oc-@M-TWOrK`qxjWY{k*rzM2dST>M"
    "clZr*S7ey;GgsWvz$05^^ou6(%uQ`sMC#banl;njrF)=n(>Lue%ojW;If0=xU1wQNGe0!<^pab>K~@qO>eB2x$HR7LvW^Ws_9n~o%q%dl_"
    "4_Y>{ExluAA3ioHMOPLKF;dOUpT6XYChPa=9NDw3U_bn%n@Cl6l?Fk!^=|jE=}X#{M<hDMnnPACw{=Wsgs%C>a~COYrgC<Glkpy4*OZX!Y"
    "3Z(rV6jQKR0Dg%XMkWJ6mE@`@jvh=cq0{rQw<bA}88z^%o*qlTYa)J~HAlM?}c;hpc$)tv?pGuAJGrHe>p|`7N-ChuN1eL`^i)wpubh(Hc"
    "$tDSzRxxwCjWJwQJ4%v7~4>4FJO=U|nb!xb-Ong`}{%^!P})eX_RuKUQ`o0;_k2UujVmOPsp(CDeVr;E-^xYf`Rxe^KC<OLSh6*=#t0Ub&"
    "nr>pA!B&w<6@+O-e<1b5hYpcr9W+C=AHyK_NgD=Y58ls-Kz%=^M5Wx-IA}g>puiWIWSAZz596nnXFCBx+UTyfa&Vf-_?N{Hw2jAgKnuXPG"
    "p)1dtDKUf_+8br%_hVr5I%b`pk4!z8FC204(iUcF!;7q~b^QC|vUU%}qo3C=dIuyDK!rRdodLM)wXnOtX|kfWHC@9Doi-H_RApDf<o!Ump"
    "v9b*OhO}vxgttSj_SBeJEIRhwM@LZp~cyEx3|{%^Fvxtx_?<`_?q-rTmTwIPar`gOIpbjli&P7%*ACb_`Uz8q5Ig{-{G(X*P@%6x-{XP4~"
    "fW#Ez_hhWy|xnu^BB$*t3K1Bfb<3I?d{u_V10!Whdbc2H=527436+L7yZcO~M_`Wt`-G@0>Rb%`<j)PV(WIY>1cPL2CrkJ#v|w70tu*-u`"
    "p2=jqB{dXR&;UzWDYt(SG9hGv&G7;|DBw>CWwpp*kst)BQHBU74r?~`e0OBPI|>2E)Ad3H<8jf86nYJ5to`I*+qOaO4caq^MZAUT0Iz9E7"
    "cEkJ(9Btzw;Ni+^=+??jPnuq-$hu%X_>7Zkq+k%B_#v-x(TL*pfwdEMNt{gcj2zM-9Nt=4=Z*WkSM2x*703xOtg+bU9m~w0U$oCEQ9dWiP"
    "zp(rybZ|`9otuUA<32F<BK|rz3y{fe>9+Qpu}<}Gz4NGUhzMx<<fLBm2&Yl<VJ@j7*Eyby=`bK24Q2xNKqU5*5I{wrzp!=X`EkEwF3-3k#"
    "{s?Uh*qK?c-gQ3#pxrLPYE#2h^)#?vBKZc;5UEI*St|NNeuCf-k`w~E@|^y0?Gur+>(wQly*`#l^_53zGo88SXRj9e-f@~i4?|gCsis$!p"
    "QFSYX1(eKsbTWY6jAHLF|NZ{fwCVYO$O<TH}jyGAFjduQwp3<?h~j`f>cGae$wMZ!LXa0CNGzVwC~D5!O!Yf1fc;(42`tD$R`Wm&^+Dty>"
    "#EZX?D?jtDyxyhz;c(v{$LxEY~tcjs^P4XH&hOOl;7Q+Q93thV<lqt7Sgk4*=9f{sAi#*%R={rw9B#lS7YLL3vwm$kfc`7J<@Gld*b9ulF"
    "6zl4=9QUc7aBVLS6Yx32ya{n#gf90mEzPzAqK;N=91y^R(^Q5bi!ozKXK>1^jeA-*zvOES8Bd5MeiQ(z@S#Lya`p$qk3Ff9ppA^%~yrb74"
    "LZPimVxCAd?_K@tKg>*(5)Mn$Gm;rrv^4pI?oqu!-s`f=7Dfk>vM_~U)B)?T(o9#$WQs=k*oId&qFimatH#ihUopGsk6lwo#ZCvSV7|&Gb"
    "l)k<gVHh_?VQo^-$WkIQslb34)noSz&h~C*AP<Su4deTcbVK_tIwQ2(PdZtluh+-ZwU-P@niSr4e`<etBnv4y!R$^Xl^Rr{mAz`1}N;*KJ"
    "YB{iD7?$Vo^TpofDVgKi_S@r@P-|hyG1yiF%i|ypuT^8rr?|h;g$3m9@@3Hm&Bf12<$&;;O0%BfEr6bBc*1)V68;Bd#J1_D(rMfQK6f`Y&"
    "i18v08D2VfkejAijF*C;Xjr7?v8YnjF`>%b)7=L`xNX`y+(Vp7wg>q2%=vRX~AvhRQ-l3D2TqSK6+>WJhlCXHT|Y3<P);~#!>)VF0^Z@<h"
    "YcOtC$=R70Tk?j(C+|!Vo7g!vk%fc!fhWJo5cdxq-`xSBU$~Gm51=v04>0f`Pt#xafslTF2?SKuv!+a%6c4ot!NwQ@%sE<(5%J{?WMPu5n"
    "iA*QGv+}tf){z58$Z$Fp3QB(X)2yWtKVo}O`b!63>zt9!9;{%XE(P{`-JN(r^D}f`2xa0(rmT#H0n}hkNDm;25N^`YhhCaVcB`wh_ZU52k"
    ")ZngodmtNfzOHUZrtQ}gAKfHZv$VBU};D%46^_FYpN;jeN(nWy3AY^=g<{+7)?q+`+?}@1#9&`x$>@eInQ!>l?74lgzW^x5hf+gV*^1#AG"
    "TPA8~t14@=3|uf}ROuKwB*DJtm20HxVw5gx#W^BbN}+6F)@w8Hv#HPIyla_|??4teB@0QxvWkLy_rENmZ3QViVVM8F-LacJqGXUo@?eoVv"
    "TG{afaM;bW1D7D7sgjWmr7jdv#X33^EKi|Grn3pQmS4c_ZVO;(#SeDT3_nqePI=4IFw?PF(l;Y!$2MH1+B*VxFHjTOixqT-COn)&U`cnb6"
    "OyWXoGSx=z-#a74ao7_Ymp!`H${%uPW@2h6A4sjxc)T_GoxEG2BMm24x@T-dzM%mQ%J}&)D&guQ=*upUv)s1+Rk%;73)=@m0w9n|PQ?$N*"
    "^smL_pqI5thVb}IK9I&#e$2mR`y5#qD)|;CG^fF^+1^NRqn#WS>doXN`A$tavzuRzMo)nb(yxZ;2NO6R%LE=Z#Vx=aaawP{=j9@)lPh!5E"
    "7$RLw9uvJboiPm*FXC6-p7R>^xl2_Umccv%$gV*f@Y>S1aE4lW*T05owE_Uo|CrXR0pR|{O@3a3r?LDw0LCt08D!~(20Bf8Hw2^>EIJaLk"
    "Ve&<|InOkRujFXAMyzWY$x9wSw+7uEbK+Ielg!=hGn@RxC=Q8&`fWvZ8xj5RR#9(Ga5-iIkD0#p3X`yLPf!lMkeOks?qwV@s0N+wuUpXxK"
    "$l$AwHKFRwdzLht&47|g175TO6tbp&(7Kx<T65iM_i+&~wiiaaHnbafcT=8l7Vn4)#9p!pI})>v5nA|1I|D?5SteRB8Y(WmMk!&PCbdgX`"
    "RScY@;jHW7l?nyyna+<-Bzz-HKjhXEX*PEPW#F7`paqsNd@T1b-I%s{(=oN`A2Ja9}Zj;_K-Pj{Sjj&g+Zo5=`h+$p+e4Y_!CNdJiXR1}4"
    "k7hi^o~5-H%PJ`?wNP8<oL=$X!5(1j7nWrHZ#}u0m-gv}Ya2<pJ3=pJXV;k<dr{p$u(M^#k2nR5sh~J^OVxqWqse=W2wvM<xs+qglwmo$y"
    "F9V-oF*2X8!U50Q}84jdibhC(%YwQK^ojcZ$t}k1KriNffbaW!+f}^1G#m45{U^0=L3;D%<};DXkG!QJLRyX2e!2IH!r_apn6j`EHX`zRU"
    "-3od3S4uKf`9CLBxr5*KIKi=(s93-REpYnD?GgNUaKZc;QWKNw($%X)8fX!cdwC+KPGLT_pENX3yZA0k{{JPt|+*jwB7S?5Dkt1+B3)m6("
    "Tdi?(=D(e&?yoc{aPNB-1Q_LkPGwiafr1NP+=;wK9)|2|tRV%z|DiT8cNxOhj5ocOEQS>LD=oA$Yx$m5T*=g*%LQ4tB1w%0nT7YuFA=Awc"
    "T{Z&(#2ct?^ddj~IOwC91aY8EmlU}DC9H3)2`x*MV^L{B&`gn!%49>=Ln@i+Cq&ZJv{V|N96Z-NJYLs4gKq8j(uY5UQDWTBVGTipq7La`e"
    "3$r3)mD`%TTbgE`!tD0e6s)AbQz8iTe&%@BUuF~HefBYm>)%4c6Brzn>SEqZZP>c4g&$^Nvc+6JYQjS{0gM~KKE{@#+9@x7xk)yS=w@c+3"
    "FH%<hllqQ@$*J?zfIq9k&~(yey4<F%6p=2`Wl9qOy{g{UpmAs1gf|sWDboe<J%EDd6<|g+^HinNJQZsX}dz(W57<I;W5D`!nq>4+3If%@e"
    "ls<Bz?zWncXHHSN{{dSTzS9roa@@wH<d3VA!kg))^|Joa5Cu*xFzI_>WL#{_@BF<(upBYSVhcr}#ybatjunJ_~k=V=+xYbt)49^s3Fs;@^"
    "6*&7#zks%+;3U(pnGDW49~YsGHh`ZW-9G4K6k&D@_~+xhwzM=M1eXWTZgG<f64(&s)6K^cP;n=^RoM`od*<<+`Lk@-cLO+^90h)Y|;-pR2"
    "Dcr1}JSj5J|dWq_1v;dIlIsKoTxGiM`Vdgi151z9S3-wKE@XJGVdGK5e$fOxN%ty_BH~JPMPK75M=;CRQ<biNm#Fo&)O`5WV`$Wg4SmH$S"
    "Mz#pg6~8r358R5kV^iMBYK+V+sVV6ae*GtxRp9C6lp!cvlW5tA|I;aYn}eEvvqd>9<duV)Yn(++-p}(beu;ME5Y)9~Y#>}F>Fek8t;~a-A"
    "3f*K*uv#BZ5M@iX7fao?8}&k$n(IR4n9u^1T2zS8Cs5jIdY|VVvn3ZLz)*yt=-e{52iG~7}%=BhD28+wkp|Z>dB)=p3{?d0zne4W;-Fn!T"
    "S)Obc~I%=#Bo+050t3&G;FR*K5A+^*61zLz=9GAJ;LxJ?(V~>^BDJZPpCCF;s5DQ(p8s8~sJg`ABa{{PBHL%<@McaI#pIN%(<&GDxt_Q=#"
    "Hzi|vfsM5rI1kDm9R`+?wPBuFM4BF2!@`!(f#V3fda+foj4Q2n7HxlB0v-uY4De;;5c@x}^{ByX_bTQS5IFKl~}`%7X(;bvV33F-eZw^qe"
    "Wn;E}ulTOerX>astZ_TVk5c;W&HoPm1tvn<h<6SEpB^{@iZuF~3h|Y+VwmJwoV$`5|wv6hv|JDsMu(qDNdt1DVUhi}Fy!ZB-D~rtuyO@rF"
    "acFMBYmuOw(#jY{v{3nP%zcYe*q*YmMG~;dKVf?zVeP_XcNqaI039RE`eKiuW(PL9M#HeF^pZnQ{4h)oN0}08W1T2Qd>#=@@gYf%Q4XHS>"
    "LQ6^;vW4i*36@r-+tVj@U4IJ(vE7#vBwgb8%DH^(xhKCpsY_OC)S!NSJ~dQqH{vxL(E+oBZr}#8DVwi+JTjbTXb)W#=ZT)4^KhCnu(5&zl"
    "cZlnv0rV_sUMEB3mzEl|T&Y3Z$bFdb?|zO@DQyIgLFc%>y1jdQB3yy_1s@sB8E1Z2=o>Z}PmROoC}h1i&#dqNbds(<e}727F&IO&t(dC93"
    "~x4xLny$(EZkEFdDDNi$p`SoJouY~Jn5Hrgk?P8z9<@UPcl&Hm+lBwG49(E4U&wsp!|4iVJ0^g8&Z*EY8|_{yN95Wt&8BI@(%^!lqDQeD-"
    "QWmZZk>c=8`{0;X>bWFSy-|p_ZJ_8fPqe_Hnu&8XJNcg}<&0=9C(A1AhcU-?<Ymn$!Fjlu1_4Y<()Adf9VlsacmW0TmKqz4OK)N}{=icGx"
    "N*!yhv*8-}m9JbCmEBQ8Qd12&sfXTw8u7O~wX5F+a!@36HaWFM0xaRi6Z6%D+KYAE9~x$EHfQCJxO8TEZ?-p0%4QqL^WK|xLO-}734tSWY"
    "I*m9IbeGe)Zsf2H?Lvata)>UjZfc9w}4D$!N{>?-hSw#XoLZ#M&VKYTtj8BG_WZwy~QYOv?A!UL|)9uW^IRQ7_yP<{9hbaX7a!UAt%`YQc"
    "N5#{lQ|nDzOx>-?whoFS3Qnt4<hcdghT0(HGCZk_V4M)T1Nzgsqp~hY($UJ+_E3P3y>woM!zX!bBdP_=^V52SHIu8QPVdN$vy&9m4N_?Uw"
    "$A@%LJ`0ETyXbhPESPKa-cS33o&I~(?Q=fJg_n$?qZG_i05R}LIJQD9iv7ug!hx7Z9rt3dSiX2)Mh7ZLXnwS%ziGzYhXUeS7y6yt6P`{p?"
    "WkzPDl9&tj?xQDNY_6x~)2wV*vy@s#LuWFZ`&P)bt#wWMZsC|qgj#1hNnp?)LmkwZ#zG7&XB<j5BYNulkC|LuaVb6gtvJgIYk)ZG@KfA>^"
    "Q-Y_#;-N~;kFdWh@4D)%aZ!)zxNo31an)Y35756NCl8U5D}lJlFC8FCKdb{x=BIE;5-olV&qJ{Dm5)O^Ccy0=J;1eZT$xYBOTlBFd0=u;g"
    "s<Ywc4+1ycKVuDzq-w4O{q*24orA5-#g?pnR=c~NQbq7f63o|p}xnW#D+rb+<qSDfP_Z@fh_TsFuDHH_;YOxbJDwPKvD#+=<<sqKudYUMI"
    "g=@@k)t==fnO%qC#JCC{P^(vV$^&c<eA)EvqzdDB33?_{Gkf?$lK|tyDL^ChSA^0eaNbl8yUWW%Uqo$iHK=ksM$tUp;y9!#7!)dJF*W3G="
    "P74dvuSA<Muc+F191RLslgfw^_fS$0|5#aJK_G1;F8SGJyUZ5PX0Lz=hNxj~n$bCCW#TW;E{$MnH4$iI0>Y>{3r(?IkMT$F!8V}0=$7u`r"
    "UmvB4eiHk=+f^B4jh9qGr=u$=u)JgOkBm9<JIFS66gO}eGf%X#@#gStP?0{X}mRe@?9eyH&H_n85jtz(R^lAIvbC5-F=fzRUr5+>szk44X"
    "@dA!#3JbxZ$GxM*AQU1Cu?*4v$ogL^O^?@)7$!bu|GCEDz(m<Ol)TB!+$R#^FIf(v8U#O=(Yx5$E7wg~JZb%RBcX~@Y_ZI3ZCld$GH+%xB"
    "9(J&=Nvd~XY($&YQ|#@<c{>gq(O}K$dtEDamO%Gt;67;^a7YR41Ti#qi`%BzUuD|rWt?U%fI)7#i@X)^n`F}mMjoXZkb)}!=y@_+tQbC4&"
    "}j0oj?bEkLhj1XL;Blm{s5gI3WE2R>cue=E0A@wB>}j6{$osyyDHA<Y=Gy5AYP-p9F+=XN2(ido_y^f-G)1qm8)HG#KUl*Ek_Fv8FJ`4~B"
    "v_?Ik@Vm48l3z(VII86w>H%2bnx3){zZ@CM+-D;L79cu88!890N;?ack+l5mc1u}=;!UU>PYuXtU$*$ih9;2k5J`FU-PVjm`A`o^u(um8y"
    "p=}Iw@QRWWO$Orcdd9Y02C&c9}dsg|?fO*8(;-%14Hf_&tDmE@{ow`robbt>DY3O!^|Esl*5(>bP^7l{+oVxDlJ%jr6<{Q2ZRr5{q@N2f!"
    "BX3#4S^STek8K{WM{#J$GE!tq&mNJup-%=*@R_qd(>Tym!Z)uR5GIE`0QOl`2mI5|%nC{xGgH=Z_j9w9@J?mtm;&3`e35<Fd&hc*o*g=5{"
    "uUzDkgUb(3dpH=?4!>t@d=fde$`r75X=<`;c?HjB^XnrhTh*~aV9qLF@l_k&v`}*HM7s4cH4z1Jt$i(Y<F|ppd|TU8z^gCP1baQ?RSYC!E"
    "4NKp78~L`Qtxc5t!%Ai|>W93@>47d|Kb~!)$`7!aFAkCH{?HzD5dc?ua%Ha(i!T7d)ev)oL=ggupom$aC{YFG_CeMd=~bOcK=mZ*rbCGu~"
    "K*(oyM}C5K!QVq<r2WTwBtV2_(cc&YXCo|SZQsw_MGnudcqv~Nlpc}}<~=Nye|0OONd;_2z%lkl0WSA)YN^T?&|`E3}4n2oI)jmpF&zmE`"
    "S1<z?FF)VN2(8Ci6Mtp^2v(0khG5WWj{7`;bRbOg%OPB@Da+a!fHY1j-K3L?+uq5KEt9fs~E0+Xx^bw(l%~OO0J19s|0W+b!u6hH$kGAbI"
    "{tJQ3^5?#(>+HTY8ABK8N&d#k-R^FoyNCF(bl2#>Q+tb0{(>z#Hzp@F4iNXs7GHlwr0r!%Yq(;apC+&{>9uRZYGCUJ=;yoz@$N-<)_Z$<E"
    "7t#hRxWc7wo96;95L<_qL(~(59$5Aux9DYe3LfrPwWKO+-ZzFb$CV7J6#n;;=kn}2G*qeTSIztFKd~(27(sNtb{p!`a^hEb~x;tvXqAhu?"
    ">F4O5#)li~XC@R-LeNds#NolG8ovZ=bOGr!l-{?0I`Ir(QWT^%rq^o{w`+egxos<f>_!W2o0{4t+lZ2z%E0=ZU{!L-;%JOCCSq47Z_IoXw"
    "1uMG&KUX}t0bv&w=^Wc1yfT++-4f2yO1t7Y8YA_=Q)G2e7lFX+=E&y4{3oMre4m<ijE?`b^*Lh^1S(m2thUhCeNn}ZhyjNwcyQZp)*oV(w"
    "0NNmWKd$S=+2Lmp0Q#ZvgnHM7O6be_hNS{zg#ouI8V!;Gih$55xiKozF@hP0)<*MF$(&!dp!8Kq6h7rFshZ*}R13hYlm4X%~YmQcT(^X2<"
    "pDdw?T0$FU5*+muN{m;b9zUPlgaB|x>U}XSv(LSQ&r3+;f<44ARAGVQ!Rhb)m6xTPIOH~$&4SIt$xnatM*!Wc&3q8Xhd*#UbC*+Y1e^VF1"
    "(y=?HrNuBvZVmHMzi`k;oK#?zoarsq6ho7DzTvl1swavk(P8+A_5zHIsDMm>uE~o&>QROU97-E=T^67QYZ1ChgnG!l_H9RGO+0gc$Cvbi@"
    "|^hp5rpE=^YY&v8>^x8(4cgXCIx<1wP}9Wxc`3+!A@gjhWy1OV?784o%5IIf;?oUBghk6$oP=G^LAkF`8%hcMYLIxW5Rna$sNfOK&i5DoB"
    "A3W?UM{`puT5sfbb14sPhL%t%IYD6R4dqHEPzzy`vVFp+3@Kn6Z=g4e0U2aKArs|)cRsX@QLT;{fl;#5)aZrkX7#cGg7%QN$;>av-p{!-D"
    "DVjLAdxwgy{GCJ`hq==oF&%y^^F!}+8mjF#yX?2zuD<=D!ojn>N#zGJ;@<M%ba{L7`NYMMIAJS>*D!v3BQ>?ff{D<m*7`U>K%}?BSV35Bu"
    "E7IKwOS@0ra?|lj7}Bxz0UFrnum%y_T?IQ<w#5BJfjfe?f^F#Lq4<93Gbmx*o(7}lE}OrRfq!IHtj?MRF{NwkV@%-rw9^)exX-Bz<rGe+k"
    "`w0~Y}Q#Zj!>l!>ppBZSqKtkUC<$5HIe(@VSi&6<q6ae;wgyj5DTUe{?w28*HK*jOhY+Hu30RZq1>-FVW{vo2V<`JfrM4S$#G;^d~EeDrm"
    "SFSsvg8ia$B#4_#C>KWYDSaB>F;kH`$W`CR&wH{4ft`burcC?73qhNV!sd*gXhs2K@FUO7DrL4beN97|g;HjBxq~@HK40X_fK9o-9ZMjre"
    "A=@90BTMJO*rJ38;lVZWFJ@t;bzjHV}?*|0KR9~fp;X^17$q?#yoRKFqd%lJi7JgV=I->RtM7we{T%QShib!ctA1x0F$f!EeyCK;<+*KTW"
    "=!E_TaM%Vb$pPB{BE@o}tMC+32J}|Q0T<!t^JU+8J3RJ)dK}TD%gour5*adcJsw(cZ??-{0iM3e>vs}XRu#SgfNKN^j0OWI4!6tzFS0Ry`"
    "uPe>%Eoa2SPjYCA+Na6vZnPt_lPB`~HIiqm$T7$0c_Prz@_jd#fVfZzq;(=8{^9CQs+3jUue`sS#3f5jAdE(DB>72D(d;pvaPDd+u!949T"
    "k6B!MjPi4E>M+#T5Sv?rBn!$<d)PC8FN*bW?3s{L%J>pn}nzne|R0-OJxdgP(i*ktpk4+<Wg2`9r*yUJ(iqcmk$y}p8nDSkAPKJpEI`ALo"
    "~k7UmVn?7q;?w*kS>Txj(yaY>kR&bZb{J$7vr3GebM#S#R`!8$VTc4)&y`GK~u$UMnW~!e4lpTT-a$VmdhS0n_3F|7*IebvF6ZBsEQ{=cT"
    "Ccn3&DN6ufDHgX#?CoFU34Xab_YjS59%U5OCZEK0r6qo<QwJc6x#3JfPm6K*-Fqb?Hm2r}0J=z8a?(y{WADTZYe8R=BFvDgMv!3GN>2QYg"
    "h@Lt!OP7;m_to1n#!T8OzmZROr`{ks^BDl4RPlS$4tOFoNSY7f{hn$lJw@NfOP82X-a?1;cLW(#q$NhJ3!7bSJ_#J0cTd>eRC;oB-74#6U"
    "Yd`v=<j5R0iE-lgNwL-6Ix^F#*&3RyPubKwzRUE;xnda}GnvELW`k{F2#h3EH$WnVw|sy(psWQEyoB(izjQzVyhm(YYyI>)?6LYeei_tKA"
    "_Uv9lME2ZeUp{(iEW(T#qEC3#MLz$yTt#&KVSK?ElAo&&M_(P*d#FVTH0E5i=1?CB}q$zY}VtOB%?gCxiJ|BIeB`AyV*|`3Y+m}M3Gc+Ro"
    "g`<5E%z*;xCGLWvm@bRETF9hTzpIywM4~YeT0Kcub7mws&YMtWkhL92&v!OCWK7?ldoEV=awq(%Z7h*FWW?d0jLlp^A*N5%#lkV%dJ-`QS"
    "!r&-M^@(`mUf&s-Hl-5^}M^5NBiG6<m1ce8F5v(UJ*#LNq^0H2OY!b^3a#nKcjfre&@`b$}!w^vg|BQa~*8m#~7R9v~Kb?M{R@X<bds8M("
    "a@H*j4>$RkAkXHgvC!`V9oP%Qg_*7X5p&zV`NhJlQ(zbzQ#NHiv(@Jd9e3gEb+Hf@ylLkLOd``l(EaSfaZKa9@A8E=quF!Xy3Se@=8%gxH"
    "$=ASumN(9FO}LSgch_!aL%`f#SEH1S4AINp1tWr%_rnF@vH<1$U&+iojtzsY3`it|<nDPjo%dfEtsz<N%19ijiPyVsv=lH+$c>3S5oHkf&"
    "0;wg-SZ|xjU7XuP}oJ3{ns2td6mi6A`Ci+lxTn>LV=V&Au9TuepVW9;S<~>a*pFHODP9TBrwTr-6E9;tJ7b9CqNhIh@IPiAGtwGDTAGZ*7"
    "wHRyVkDS;3xp0vFGLwjSX<?l!)tRpf?49>CY1$^p+Weo$@N}=R|c62%6`3oO{C}->eY3pjwn(b7-=XGpz|WBsc`bc4JXg23v<il%yg}<u8"
    "P#VAZ=>Ng63<AHYz$Qms?hOKT?_<|`@qOcO#<u2Vqd2*uc@s67Uk9S3i;u5Je^k*41uVnm%qC<?K^!(qmgJD*$|>TTlmMxpjPeZWQp{KyH"
    "tj6GJB$j}fS2e0bAB>BKjv68wV;YElYkiHuMmhmSx#mLLC6E0e_oM+)Co7E#0uYDASScIn~YR@^rHE}PF?pAp+b>G0E9}B>~GmrV-ZW4<Z"
    "g;tV-dk@+o+hSr)*kiRpH0KX=6=O6|CBz`dwyFW8<KKGna&Agz<{Z2rxB0*ZP(4jQXhMc2*W%vth>;VI5p)Q!6;ew1c!=j><rc>F5asOWk"
    "A(6{GLP&Q@smuvka@Gvc=fmyNV*~9oTmC`dbiqV?1-$DS))y7B31i}n;g7JoW4(T8Z`k#0zY<6FMjWejMywnS}>pF4H2n5kFlF7I+(fmE&"
    "3$hW?m#FpM8^Ox2{ClBUZ~mB~@$XZIZyOKlC)ag~doJB{53#1tpToiUkJkk<}Pv^PzALRVZsf;5wwizik;099WAU?&tP1FE|W5qq}Sg1CR"
    "LfG0&#-1J_-~7Z~$#2`nNwDirUHt1QLtpP^zB0MAq2Dgs$H91l~+HKl}~@E7-e-6Vu-%5FqlJA`Ijnl;^tD7p7H4M+F;F(;KV$Vga;YsS^"
    "8!a$+)O8?vMMi_)Z8?KgpM{;19dnNSkW??-jVYGwgJc6#bi3NO|b6G)#0LwXo&bxH2Jrr0g@}(w2cH-N0orWh$OVF%wx(<+o!jab~Kpfdc"
    "S21v(-GcrXzEYY!7$}Aeh{Ypx?X^TMenlsSrC~2Wx>X>L2+?-z{{N<s{8-FQemh20!i0sj!I+4FkqMLe9*B65A;67@isS_V2+d%Hc;gv|5"
    "yb&7)(808w2+j@UR6KW>RPd)!|{+cyMO};6_Osy^_9-teP+KCNC;rM%6veTE<CXrHwy^K{|eIR3rSuh!FkCKPmVAo796RjfBEY;mYo(r3X"
    "3Ga0)I%D7}MPToIO2xn|(bFXuoy#aSp$BD0x=Pml!ca%W4w}4PMhz&6q)LatjYsNt>L*YI{*?gOUl0?><jMbmft9Q^OQ~uprgJ{tyVa<p="
    ">cxzh4<EHSmJ=AzPe7#gVCMBUDx{g6=j5V*O7N83kTh^&Dr7~v|IK8>k`gQ_#yZ*Gfap5>C?UENtNQt#8_-u?#W{a(<EvK>(%ULtyoEzgf"
    "|5LTC7$gfSzKK=-D^n-;;+FyxqeD78Qg05X_J^OhM9VTF)ghV!;`WANGZqc>IbnmcNB_!!-+E~?VkMT>$2DyQIU{Et!GVY#E6OhqnW6Z<Z"
    "%TajG?r%Zo5bu3vYHX_LOYh<dq{wW2Fulta{y#9d4R!>i!w?!vkjG}ue45!AyqWaxZDb@HZOt1G`%99XGXFU!1*;8f{D-XRaHM;~ay!VaZ"
    "3)pND|9?&e`ln!jW$}T6>@RUIjOE0BU_eJp>fsjk6!cP)F|D(A4h$Ea<rPl4p_$c!!t9Tm?bIh&1_!zVI55suKTG`-iPz&j>BS^>5q-rRK"
    "z}^k0h1Cj}@#dp1-;IB3b}Wh^OG%ta8q%W+M{4+<2uvgyec}5Df1`Y|G|;gs%rM9vhVi>2Do$NHb_8;$y3q{Ls^F>n!Oj**)TzXo<i6Iu%"
    "<TF$}_zmH_3Duu3*FQx`s^1HVtrG>efBBvn_kLol|DBA*F}e5z2H_UqSQfBE{KdY_uGo}K<jQnqe@<T?NJR8VaRuR!~t)v{WJX}scw8zf<"
    "*veU~~u{5Q8K`b|M`1QY(U;oK)M5XZqIKrBg^(m9&4VP$7k3k9<*p>;B(^(*Ly|Q1>qfJuTy>q}11F;Xk{`u>l^B$+E|77bdC4wDb8h|ys"
    "6t{Qy;a`!}JoS4eKazXI?dCV6O;3xi;j>XrX|Kkce{Q%^y!@*Nht@88mrc23nU(&ceQ>2sBzWJsTVU?VJkx-;OpL_5GH#l{l_OI*5$8S-2"
    "V=T2Nzx&LZ_3Li4CS!jv&lZ)u8{D>@VAcm0B<1vQ#;R4w>rQ5rYWsp;8Ng4i_t_|A<yyv^&D0cCncBa-Y{!TZA5~!`J!oEcEmTuH7WcHQP"
    "2;~#8(kxipgPDN#Y1EYcqeQ!KAcfToWc`-J8?qS3`v%yjG+Jp)e1do7pQeD=g%JHDI<+q0Ip2+G(4`J>tDH6)f^s8KIOZD}cGJ<}I4^mR}"
    "ei4@(bscxFtwL=ECnja(H6nP{A5LepvbVR4(ghqy|K9`1t@d=Hb}RTJN2zk!be{v&T~(j&=})}-1IZK9v(jz5{LpNyJs>L>3uWM+42Q}{c"
    "kNJTb9$OqcQ*)I((pv%I<M-`zzF3o3CwPj1Ff?_|1&F6Q?n&F7{5FyiMF;<Pj4{SNOYSK-m7>8PNbkw(T=}GvW)c!^c{0znwLD6dr?3!LB"
    "w-3Mz`>4J!@lKLW{2<iqWiNG<y)DFsLLOBxzBB)7VLtCr=O7K23p@^Lzwo=#-UZ|=-4>Xck`R}4=?n2Cp)nd9-jem73Ytd&;wd4YxTO%60"
    "Ar@wS|m^*Igm2D4@3phwI(7&{#InBO7K%9F)@``f<+?=k9yoXwifyob`-(tg$uy8b%+>J-d?SJ!xen*C5xW$WbkNSv#~`z8N9Gk%NlK8yq"
    "ka!g*u~{uU=~DIX{_RD?D|y1fS^Zn~FOqrgx3bqX$gASYsttuzZdlSyO1oO@jZbISJoEQ>-LJ1`qaSM*MdUO`tRNvJBxasjIn*lgqI<9EV"
    "|Oduiq<<Go|BvSX3CeF@Ix5QmGnNx##gbqae8aaMvLhMk|c&jd#XY{NwdwNPmK>jk`Lte{>LE+|>NQ@gbzn18uD@s$9gidTO3CEIT@#FZ~"
    ")^Iuw1hI7Qh(Pc&N#0rmkT5z_Ljj`_#nT6_9BGr>P6O3MyckdlSCVeXa;%@}f8CvNDon9AkNRFGDWe8`c`G%+AU77E|(0pd3+Y1i=6zn(n"
    "EAnSt;TBC5Y-k^0lniRZOV3_H@6ZzxjhH|91hCRqb|J~=w06F!7%pqs-v;HX=E7d9WF|Tl&A?=s<T3XX`>vHwtYu=JNtrAZvD<ywol&>c!"
    "VLEuP<riRl>~mFREGL{r~L-gdp;hkhPyKXn>u`J+i2JSLu2wr1;R`3CnKIzNFXXgj5WH-7Jv)K9{9cV#X`VM=T1D=M3A*VyTPn@48#XUIE"
    "3b%JJt{Kgdn5>`;`Gx6+Z-u!XTgBN@6aE51Quh6LL3_M5(~))GH&Uh7S2y5C6tqwL3*+ypYW7&#oa3V*eA;Ee~T0;9Xx&7Djh9xG=jS%mK"
    "!tLs(Kk{m1@D;qjFTW7?qvaCjzup^NZhZNSd1j8Jg*nl0V^SnhV$m#w`lGu^b|M>yTq9=&zkPl9UCa48Bz)Le$dZHu8T4VO0X42}Zd`o`b"
    "u5t|c&wrCC);M|;qpqCshSe!nib-aW1<kI8|iSs4E+{F1OTythLT}q1!qYO-yEN2(XNds7}rHQPzdX>JWC}Q3*cWyt2H)=aWNQb<wBe^D7"
    "Uum$SpCALeK&C|#zwpqK*!<AcnQrYTft2SEYJ<j<e`qwr8HovB{|Uw1l2=`;2*|H2hIf8ICoWNAdyj&RLyLy99dC<fjiuD3G{$AK;aQx-b"
    "(^?HmoK|=4pG_(kzGHhdH$TnYTN*0xWH2rPc$?;lg~^Uw{-`=R7t=Pw8M!B6FTHBC@7HQRHm^R_YAQ_Xqy#x?T`k9qF({QUS>8fm_}zES}"
    "qnCu6!I-Tq5^DQ;Ph~PZ9i?MN1ri>L#-rOF>@QKQx&Qd?AU7;V`cUm`6*F>qV6ldY*-5=#9w2O6Cx|^P*{WPLzn#f}JakRPX|Sx4*gHl)q"
    "HispyjXd7h24fH7ZobcZv;z0muU5_Vt7^Gn62L<$m5m*fEJ2iZ_`3&TEG_*C8pb0MkUNmDb7knV)%SzZZN^?!{f^M(G|0uhI3<QS(P3s+^"
    "5yH!?Tqx<D5PDUHPs2SduT@d=1sJZUkad2?I;^Z0p+ebqE9csvPffmu}#Qp5AE-iNgQfx-LEUyP~qiKs5d4NsmoBNWZWYw7SJi=;g2VKoD"
    "+>+dr$=w5dITw<h;dj!SnjM;U2zdC09{DM7fyXr#t|Bif3cah$)hxU;cejPgywZ0}QiD6Vu3C~(Y|mT0<OfcpN;0;w6Vu2^QA-@QTD@ZS*"
    "zT)MMi<6V&$xuB)hx<fi!$;Bc_>+SYBg4)Mq%kBxDDg3-4w=)Vmd1oV)?w97j)AV|M`1AxCP#hQ5RmBKWc5erOSJtnmK#Is>~E<lt-LZas"
    "qkCnxQ~mIn;mLef3Srdcd)Zmsa}+WAu8R{n12Ri-%d%8)IGXL--*iZcYme%$?HSD{ovgnEp`~lDhCdbyhc1Lc>?KLful1!m6wU`tNQkh7O"
    "zP*-B#VF|**Kv3@!(IVOz+lH1-vY;H-)IBmQej@n?bB7wBw_141vIff-nFZ_?!4NJ5Ep;C|OUa@p20I!LJ9;EA;W<>L%rYZt6c%NRl`)b{"
    "S7g~w>v~(S}7JG;m71%k0GK*A6YzVCN+*A`(z#)n!82R<TAfrzVnn+!R36U!_Yt}!1LCZSq4Nw8Hzk00P6I|6kES{(EH|(R{w;f)XZ~;L@"
    "i9^*t!_EP-3AuEnR7v*YA#;Jy+{u4HOe67s3LtJ4W9J9mkdzyP`Sc}(rPNBjI2XayQx6Mwe`KC_>q`0`5xmD|uhvjJTY5O7E}gFRdb6J)Q"
    "7$0RxSjCxz^K|D4{RSP*P!QH67$$$0%%9nNOygdf%O;W3!Z*dY9$fAk(r54LI3bnxTzQwAH)2IqcWpwhNf3*+NpF+^;XvKmG1LO2^{kpe)"
    "uI^v+!M^GJYB>@N+hst=M2T6*G^9GcTorkpwQ8xG~!ae<K1qkz00>JOZdYBBmH$YC~AORGgoRb$S(=YB2e)iA=7`bDOW?{aWrysSM86$!x"
    ";&by<QTJcKWR$6R9Foor4qviYpuA+gQyxoum6s<m1>Uc$@+Q#$zg1Xu?Dc#8F?n`bo7ril<+FSnP&h**m4u!_54CMB4+djIaFmO)7GaY0}"
    "B-mEI`^rf+=ix#f$nu<epBVQEk9r0!oNah(q6+4T&KcH_&vZ^+bZw`nxbE0I%xbP?wvx(|FuRPid4h!kJI13ZiRRyKsQ23~JGBnzQXCa>T"
    "R14_ymj(EE=swpZcOPLS-eR-X>qq3%ci9-3^P-|porr}5onH7r88pNV93W_GY8N4lYqE6l+M%-}Xjn8OBlim|dmCVplnN2f=-cUXu%QR#8"
    ">HX0$vGI!cS7VbIXVN<6LV6erx7c;dk5q~KuB=x#EcOiK6j-lZSnxbJPf7hnvn`JgJuN_BPWRj{6g1W!GWPtpP2q4&W`wyqmKdjy>~PxXc"
    "S~i*D~VG<|uxZAPlrb^MLi-rFln!6_C$yRPsNxziPjx+`flbEh`~D2guVKmq>z(_hw%*T;pc3GS$ESpHVh&5Y{Ks*C!^6QCa?g-$bowE3N"
    "0tp42bSJq8q}wpB+>WO{0v(#Vfs834_f4N56<ym(a$wRHAQzZ#<-9<pMe_0FHamyPtAz6AvmwCG;^TTiapIMC+QGlSR6Ulv@POqkfwWjK+"
    "VV-VM}FurXgPPf7BF#DXv#$Y<+WHwtR={4Sgd}SWg+^gf-`s@f<2?!Bto!&RO)C`65`{mo0Z^Os8r7UOgBN72$i7?o)*YjSlD;`iXzmV8^"
    "#>VwVYvm^sH*{_+<v7#i2G4W2kB<%GgRC&cXMZqcHoAH5)ZqWat1LJ_&NEsLUDx`JIKNgaf?eFcM0{G11EX6gLYq63(%VF9F=JFGIPetd)"
    "zC+-9Vrmv<Ly^VmGiIHv{`ogho~4Lqm>`HRx)~IKO-2&pI?XITx-e9V7w+yb!oHDah2Mbr%$X7m2O7bO=kCX$6mP)*9k44&zKXU2rQSYqr"
    "_DTU~dSms`NoXuOA1ys1cF-Y$Z<^N!l?<)0qqL*8C%cj=b)u<I*JV2<qR}e5HPYsGegg&BGn~7=#$UE9qAdX7Ua$k*SAL*Uh+LI=9}d`kD"
    "*Xp^8OlYDfBJJ!^`d9{2m3CYBh&2dQrP)E6YFg6%P+^@UC7i&P&%nh=>iz)>P~!2wv{bk5ZIMKXu><qzqct%n~tM6R+zHA3k=9s3RQh}4|"
    "(pNY^j;<HE%m0Um30<KZ<3WnH7Qf-k3)7=z!kg(0cr1Iqs<TE?HJ~{`&?p+HWZu_jJ+D^87#@nWbP4L?K2#42QW479cUbkef_7hKN-p3wX"
    "63;zSyWUe~dA<}$VC($?9cb)Wi2WqUd5J665~tzj>xi0<=-HotMtK;PTNY`xi*XsJHUvF`<5p=Dv>a&D<i5+l{$J3lj=%oOtyoUYz2l}Ja"
    "9YL*?ne24$b@#z5RPzLN7l137wL8H-%B<aMhFH_v%N2}qD0XGT5Q-wrE8Dgu^g)cl_ExW^6ysfcbBBC69G+ViD*Jk|Mh>IZ=pTJ*I!FMFe"
    "0oL4g~UVi+^t%JCYc-i@3%cK!6mP%%{)1@tJGO>wY~z!YSe|NAu?PHji8`)s1~UqMt0+92Db-4^;J%UVu1idvJXlX#(R*++6xJIo=`~^TR"
    "5Y)^-suT8Br96NvV~v~-C5$jnCm-RdC79Me`4@Z~F#-C}bhY-XD2qtb>s$Z=En{G~OC$f><PIz``ZWQ&S99M?f5!OgbCm1pF^XT?033j|y"
    "kjV>J<B;F!C20d7;bnQs*-HQ9t_Es!*5E%TIKmG@d40FM|_q~%Mu|Vzt7QX(5LqR-)Ba?%9vgIvoiLQF)|KhmlRV%P|t>Kgu9$k%1M}S3-"
    ">r)u!CFO&C!=gA{HHoC?<g#({0hiKW`Y=5-dqEvCBDBzjoNWf;>nIn*)l~!7UWce<X7AblP|P%nc)O)%UzsWD1$qPT_L_yk_a`I>k0!W~1"
    "0-RVzBUA|NceE81q_6kc1!U?J07$5F1HF*&?Y8tv>*D<4RQ>=SoP^|clCyWR~gZ)g)`Av%h$>PmvdvMYN**>N3#4|&$Wad(&4|*ES<WU0z"
    "14Et+}+DE48Huj{Z#}97q0DzvOmT2kI{!GW%&m_kKqc@`E4644z(fXg?wDr4TDNs+iuvdI2WEDagLWs9x5=q*y`rXR&iZ@KtazY`5c_3A2"
    "Cw)3`B+e>kXUTbO(rCWxKzU;igAlhoU9a<;&;VhJfm8{Y=<8k(tjFmnn0nTT=C*GFPf=*j@PkCWPNOCSBWz3y%spakbE8L;jpmTFs}ofj*"
    "#=Z>SAuWgR53pT8(uaW0tAg<?bu~c%VEmLsV%g9=vJ0uMW(X_(%01x!B)VfL^06ZNxC=2ntbpGX!6K0xo2$pD#-0%fYd$NnYNPtdWaEY-Z"
    "t&qd7pSYb620Ha-Oy;3+DN^VkBGue1EEY=d#nKk(ugEM~_OjSo88*<Ec(6`;u^G_NPOPNDY31zQ*IRr^Ac?MK^boU9QU2h@g{|E3Un#d71"
    "a}f<2EMx^v>BR7f0>gKX<uB~i#FKqcCxQqc;&FkZv_^S_+~{;;<ye`JTt6jr?mR^o0q+d34Hbg*P!Nh87Qok!E<GQY3^;J18jF9R2WEVV2"
    "uQYVrL>$NFA{e*=&0}*SlF6-W$wP2SiAc+b#<WU$lgMM6(ni63Ga-t^Cxt><;*+3T2QF;UhS+DIeE>%=bypDY4-A%4sqvF?F0fje_+r_8n"
    "cxUT(jW+S8hQ#D8Cx*cO|)D8rMdTt_fuO!GXoogVBBhc*#n6Sg-1FqUDV$j)8Z3a18TH$s2X(5Zxp2{w3wMT;e8M#J*p(_IL;H03IC+-QA"
    "49EU%isMz7pgU`#{K{p6x3Ln{OSCOx!h7f6=q;+UUhF$}uug_EFwNa5gssFmtm_!iPUl$^#Hw*tyB-QB;#Pv+Vysx{7C77^4m#2Qb7vby~"
    "Owe2^4k|;n%(R!vNdfz4Ys0i~?zv$DX6gNhn3dAp)(@7+uHV#dZ01GlLkX5oIpuGQ<wF0S2;7Y0=1xJ>wYd``(#(gau!1*OG5oFVZ1qEw|"
    "AbX?HEi==9SAVu(sr^G{kl#Ba9gujb9?ayg?PF`xRqheSZ>3m@B32WC~}1ar2B9<-$j>~<@>B)QTx8Jh`L|-5b;ar@@HBoheJoV(=A_xPB"
    "y1zF-B@(CCx**v=Avs-rJbWOsf%{mPT!H>9$`1{L6O?ItfJllXkFx^?oCtVKx#<aYR0{1C3y@$_YbBh<Pj2EZzP)YeMRBzN)x(<PnEMX>!"
    "(1SLlkU@}9r&Sf2cBQv1dZM@}1lqAtV}KkD2z>_WpoyF1~P(T?qzbjWxrcDgMtek3Sd%b4p2#Ds;N4wU_1YEXv_XC-j^L}o0h#((PTTwu_"
    "Ltg57h5*Onnko3X3ICj2?s*bsU?Ir(LM?=S;`C+X}Hu9;%(!@=@)3(N6gKewNk@k@ysht-0T;D`Hoo(jr%`qR_o5w_LW2eZzdl<X$rd<;t"
    "7%tRgE@CKkuKdt-|7;9GB3XFJ6?|m(Dx~8khha|EwM|!htzu`r3Z}F=+<oKEpP3ma=7sQ(oy16sWCEcJLW|OZEs|P-s}$h|dWs@rr!9Fy="
    ")~r9uL~}E{{@jeb>#b?6M{lSNJh#Fj7Ybo%gq<KdScoPf`+q5d25lQ-5QoWeH%<ZTx*&L)hpFIZAR}CIfQ^(`$dVppNB};oemR4xCiTCH$"
    "WY}x#BMOeUyM`);Pxq`|Puu*slo(+rj>j5fyN)jN6R%-<)etL(N)dUZC!DVOr<~p#JZeg|M?3Nu0zIwHWev!03^ij`QaBHt?wgPB0bB&BI"
    ";gIrcCsBH_19L|JKzl-ae5-jWnOZx+EXztgeni$_;#<Vcd9MkG`=HtAztD|F^pc+heG?yOt*FBS{vr{Ud>npJ?RK!#{>{_;E6*(D$uOE=!"
    "jS}SsWGd=B;`uW-C%dWM6>(A&}bv$XyiACVW$W?48=ppd>7J%>zF^xsmTQ+tq)zFzjqJ?FjGZ9WIu{rwGpN+etWA{{R-LXNFM&Y^_Q_BW3"
    "sg4I;69kbL;(cWh-dqnyP!K8|^A%%K+E&{3-uH5*6^SCIqxrKb{_DTw?Uc!#?^7jqLWASoolcY7>v_Yf-<7>@Y<katF;CNde~NAyCcBqb+"
    "VRKV9U%B%nz_FZoGQ4!z|2zT7YctA72anw&*FD9lJ|&aY8;?vN@SlMi3K%m5E6Ky861;SvUy4vi(ts!^1K+?ew|Fo&Xf%au_?de-g?+)hf"
    "ra(1B3q)mc%M$f@p079SO}u5Ft8&^CXi>C6AoY%hVPE1%GIyg-5t$r{abL0*Ng#Y5{LjsL3f@v7of?y31cfeDVxYvSQZ|`wfetfQR2iFoS"
    "q>=dt6PwIZ5g5AsZf=c<@B8T2^1R~pcsRB~n0Z#qt|-DFAY&sZx#ol;lUO%VpaZ>9$ETA8gR=5?y(V(tx$zThiA6iJcvabLcyxI|KxbFEu"
    "{Hkc?0-xC8YeD=VbbzIA3Q6}LPI4gRq_v+=#SMgDs$}%!=ks#(KUJa9zhAGHj;f1<7lUhjMboSsC$vFe{{ZlqBTZGWxe=*$G)~eX-0Vch9"
    "-1{sAoWmWOSyR=>5H;YWTN3<!-HgYCGtVq+=2u+G1{o~1wokx?Eg&t^fd+7+iDpl|36_$9Ewt$XG1xEBG4rO4Y_FWxN#1O(Ja(9`6g3tSS"
    "Q%$nw5BbDGJ5l<U!<l$v~cJS?tgCFaoS6O7HP~!T72Q!F%_JmS2%W&DqooCO$m9UIs7Z!Gp;{L*NmWzS<$^R=+~y8|FHph#o{4S$9so-4X"
    "FPxZ89cZJLK<(+BQd~^tD+S%dv_iv5q;Te07$Eet^XHC0;Dn>uVhglvrsCMHeE0-#nfuGg>W{a|e`nUOwOL(kb)`q~)TF#t;s8Q8c)maQN"
    "<MkN^4)Lbn4nrU{JgYUO%|&0Ui*ZpLe@QnG1PYT#5$RhK^4m6VT)oQRM*QOr1(lC==H)35&wV93%<%Ok}#LCiCnMa-o7_^57{nXiY0^Ren"
    "JGuxCc_LGu%Nyw&d^^t}8^i(~2jH3o<2OHpswx8h^uW=P~0#X_bz$kvjYA?97Zwu(hqWC&jF%CtYfz6Xz;J-B@tWF!t9NS;AG7#399nqIh"
    "w#77xmQxaoU;iY5@k4lB(Qxtd>z{rxrPdDk*7-FNs78RB24tV?iucwOTW1;GRFD+l?dR3(>;GOPl87jUx4!?&ucX%(#k`-?z1+w+PSre&?"
    "kCN3x{~ZFY4uzt?Kd#ss<|b03pJ+U*CnPyEa1ajlHO2+kq7ALcC`ui5{7eKb?~ZLAfdybR)>%12WOnMn8bMPrjm)v8A|Skp6k>OjP+y1qT"
    ";6EDQrVq6b!rdkM=+QOQijR8Ivf_V><@@t%FkgB}a&EX=5vbjir~^=)<CkX;+pDd$CFIe$~oX+tqNvO9?bVsKYc<H{ot%Nl0;#AgY0lVOG"
    "2CJW#FnErq{Cz$a7CR$|zocxGmC4cP{so6v+t{??N%v-!b2G*w|&f74`^tvF{6u(m?xT5>}%y5#CxA!OXZxI%Dw7V0+aCbp8bB-7n>#}>y"
    "b(|Yf`*n6?N>qjB&#&|6SP%vcaw|Yrps8{$^RTt%`wfrhX50KVQ(mI%5e6tz$O#2#xp0oM}f$9*}T2Ce1`r+ypU^@8hrg08_N_w+<pN6j~"
    "vFpo?qKGhe*4l#ivY#!u3vbzkVMiGWCaE2(PDkDjZ0|tS7s}oxFD$X&#mrT~UhTahax~5^<X_1>qmm!~G(yp;o;HewqjQoW@l+jdd3?Ww)"
    "=v=thA$1GZa09~K8M<I+9De+eIXXKPLitrrL=70@)o`_%x*LU9LL@kpIkPj|5xZse5&0C9#{PqufMeU*MFWgxe0Hv?i<&5q=poddskMEZh"
    "~_sUa}-mZ+FfArKAbR5uBRwv0Wd7dLUO)?wN5zYlPomDGcuaV#3>Lj6F=GRT6X0zu)!Z_G(4zq+J8T!opJ3Fns_*3_`-zCBZtvnopiYN`4"
    "f6AV0`g0ZoXe9Vd-V5siPlp%$@P2`XLoE_6T!#u<7dM4nS{5ff0`%RS)YA${G*1uowfo`3n{KgyE%5^>z6j<nZPXKvXgU;Fnz)~bpa(h4q"
    "lBxee5V?XyUQP)C43Aq+~=B?eN!a?nL#``!Jd(&&YxEKuj-eY88rsQ_4oytBfnaXNYEmqgcqi={V@m8o{m)2st8~ayw{FR6N?!V)Pg*7}l"
    "KZJ#Ed*nyCdzkxx{N0Xi1TJ@gT6*vKs`sgSE+7py`LQGTUQEjb26Pf<&bY`(nMDHXB0f^E3iaV1ES8ZUrsn2>y>(hYPE4CV+ck*9Y?4Vfi"
    "vAU*s6eU?FMIqOC->HEW@z~`fHg@?W|hXm5godBiopq;wDKzUI0*%I+n?<{&*j1ANmd()%3k>~>t#^D`LB}*F|-(gWcWC4+RD{1l*8Fuw{"
    "5^DgX&(nujsU=y>yRh){CeMw2%1jhuLY+1eC$84o-^7&!0Av=uhu?GNgLBWC^fic#3*<u_3Y_=U>&KhTf_j5>2Wsfy&avC!{7i-#z^xW_f"
    "TMn=fA`tm;R<L)vR6!=!>#Kd_cj#Cf34A)L(>Q!Hv)p;e4irsDf=NJ2^<$@hpf;X=>gRva=HK4wkibG3Px)tLogslsiOD8N{xac@INyib?"
    "Z^HAe51ny7Eum3!2>=$uHa43z$m(}PlVtxs8cO@Mp2LuisH-VG5;Q$+AZ5RDoUmeTq@A0<|T4yO>k(HHte4#6D<S0pOlVh&ttJvrb+YkYm"
    "8xGPW7;JB?wlzCxP!8csn9=W1c!LxK81!bRy$IVm-N#$I^r@WY$!WK|{E(|Z1%+s@-6D1?>EiryPkv<HJH6LYM5GMfR$4KT`wY#H`)j3TZ"
    "649qUdI$E9)2#6hEH-$c*-VU9rOn_PO7t>^CUq8$t-9{a7-VHAGx_m5?DIC>v32IpD=O~HLpKLKY&4#aoZ=s8i!up*;B~VyKM4GdYBZ`>V"
    "cH7c^Y^aHi2tCS6OVuNvm7UZLI%3@m)ZKx+H9aHlgLlS?b-!jT-cgW#d3WXmXnH*>2oFZ1qzWw|j~Gioo?>*IY+h(qh9tF4gpxm8g7B1q<"
    "R{$4LsaDe<M3?-J7KOJ(UWtwWjuV3K#-p8JLyL_%u*zSn<;pM5T_b?=@;cDTv$0n8MNF7)pV_ZngnyHDP(n*njvjKBU0t-wsRdmHI#WtfQ"
    "+nwY5olPoM%D-;h%@LYhr?@*j%Ht(f|6NFyU#?6x$2|R0v=wr>ZpPM{em>>a0tNh+-2s4T}db2mC4~xN#<#`{seg=M=;N_iH#ndYZ{>dT%"
    "kL@C>meA{4JLA&j(t3vgC47UVgbZo2`wJhtx0foSaJiB&;7U*a?B8x(8MNWy#5@85i(8b$?N429s|ous(v6seTMZk{#YQu33E_U)J4ygdY"
    "9`<eYI?DQg%4J|()QjRXfbTYYywQk;*sDO8#I~q0naq(Fp8qIpcyYV@^rY&8yLl56W;oWbVS;1M`l&HP%<wGFxq=8?~y<_N)HZJ{;x2)gd"
    "pUa3M93pkn(f)y#G$y2xZ!0O+=|$fLKa)FZ9#Zj6v4irMP!mPoINqlVk5R%=M(InuNQj4lt+(&!nVeB;*c^c<O_4=;K2Me@V;;oMNJM$W`"
    "2V@khA@XW#N{K@-z-(8t4zL<$BQb__$|_ACUJyheK%O1+#Ex4Bs?jN}8;qcY7bXm^(q(-5z!RGsqj<t;1wcbVn3nm*2T?T`-LjLCIN`_5i"
    "Qil8TvZZ|-8+&VrFw>m1#T=Fv1mjH_;SJ#00r$OdAmhj2fe<|l;xI*#!J0FAf7BysYK!^P=%^eqtITNRhpSINEHh>;`3yji<Fn{YA#xele"
    "pZtlANenULQMkTMIj!b}u;)0vEpyd62_a4n=&(&t`o_fD>>I*|BsJK7sDJwR>lmk}-kk7ugYF_Eb@32p58WwH?Y{CIZ0-t>hR^*CFZhiRk"
    "1GIS(Y1-peMNTP;b3d$70-%tCI3^0q(03DuJshv{<i@nTxFzseEl_ivB=#aN*yCs+uQln?CGE00X-ajj4D7OC4u|mOy-7t20jJh;#LC*O?"
    "-{Ny=H$_*(?Mgg*K|P{w<pm$L2&Iz<Spb-rOa#`5M5ysksVfAXr;|{eM7VU;iZGeWqe-8bNDB@{xX;$7e%Pi?1%_A(F<(Oai9l;G^KW4Qb"
    "t|LOIE_leu57QLahlP2fC|;stl<#46t-8A&M2^F0)Q2)D>8=?blSmhTX~yViS#-dzkiCO~`c2gOaap{sDPHL|@?pwwh8yiZ$^{#f9H=Azv"
    "*hV~UK-v+?<a%Vd*#Q<hdn@h`+43f88Gc`)A?!66Ds+o{dAtW`tN$mk{^Bhc=aUCQA=n&w89*#s8m;hj@c@kbO(U*PFpV+cVK>NaUZ#(Gb"
    "3JoG*f*W$SQ!$CVCsp9mUua0*Ox;~1ldgN|x~cBMCeZ*24R8dC8`u?1qxVwySzFpkCKaVxKmCy3^h?5rBy!)COFMP8#Y%v`FzR<lCqHZuI"
    "71?%!q)NQxupS6p%_1;R#xX&kP@nKFazUqDY26J+m7GMYlcU3(LtS|DQ9itTtSOK=V`R0x)qPwK&px$EjCkU5cer+Dl_%ft{Bz^t@7I(mu"
    "2f!Q?+PTQ0z$4XGR{y@&;ZSF`j0fXN1)3p`CsGGXtCCjtI4waFYF2ul+j=T1RiMexx_~@`X*0Vx)~iZUZzsv&7JdX?_lax-t7HBTiAXM(C"
    "kHgU7>fV-H{J6ETt>G-U6`pfp@^jdW>&rk?gaDRR$26ax4&SP*9Z+)cJr)TKQOVG8)YKPv^74~j3+XPI?1Z;{~V2B2^tRgpXCGJ9ImeZOI"
    "z#pW%anzY{@GHPa~oC5?gTiNO!(4pUfS&?DDE$PIwz~8}0%t|%4)!5K~{3#(vZKZoegf6mzzO$-KuEFj8Hk$$KxkKYe>98GqHyGd2^^Vvo"
    "swG4G0OlS0To=JN%4()!OlC`FYd|`ofPYo+Y)chabO7ZF>qybj!7<KY*hoV_9PP*(-&jp7BRYm#%af3rN}Z<USMnZ+CXsj{+0Iw<RXtx+>"
    "5vvwJYFpeSNkl^y&u2f8GV;_Hb58YJ7i_6<)cGbQfCVGC&@&O6Woc#SCe1Am<CXWVSlUfpqxJ)muD@rM9MVzmQaO6P3$GDc-X<r)w*MO3F"
    "1Z)$s&7^fgbwMOdYp(m%1QvI*>i8`LYJFHp?akPx2jN|1;kVP0##hgo3<4Q&%Vt16|<``63gnV`&?jwh33C-r`m_A970~fek49d+_yNs<`"
    ";)#Pz&t<zpldwAW#n5Uv8&DHYT{_->;WSDYJJ-1R)&=s2VXa;7OM8;O9B+-sHcfu9ljmrcd03x|#hB<^jWdeLR?bIZ{yJGOZhxnkQmevEM"
    "Jic7dL4Fm$2%smep&~sJ`DX@c{p3^KLq>f6$b>zZ+_6mdVa2C?L_kQdI)e~0P60~#aion5W=T&G&Yae>BJxk@wLn(IzH-mPk4}&BsG8q<F"
    "1&6NPpsR=kWRdc*h;+wF*;!MTNKKm5wiY8uSfr1G?H{$fkc5Wc#?Nm@U5(~u$}LQg?c82FBKZ%NR&2VeLUo(NvdJVM;K~UU_+)36y;@c0<"
    "vmGqp?uD+_a*Z&D0MN3cIPW~1VT%aB^b&X$@RmVep1^xGYnRrl)Kol1214Ozu<lZg+yg#Ur<g9`<%|Tr!vGzPoU3ek5c*|E(`%3AIn9$=M"
    "UlK2zWH5>-}UFw3r!tsINHluLza0nCX!)Bk&FYmQ~`8IBK%I4ipp7Z+~3D<ZbhC?gLy>LeeUT_lYGUZr28Js^#V0TgjRi?S3Rp==Xl?Ix2"
    ")#UZhrMRNA7|Iw&g6PNb8cGBgQ8QHRR5L__fIONG+thDdosP#k`?#flY&Gc@?CYm;!zg_J1J7MMhJg?7hg!&K~c9T-l;{^DIoz(3EFR^WN"
    ">xM*+dr{BHMM{Nik_4&WDm~CDD$}XT_qXuHSBOWV&6B^UX$F<DPXOj0Ctw#Qf5dVeJGm@4pMs|Abj6fp-TH4P<2hcGpaG<32!o<1x_)4Ih"
    "|9xoZ`7M#0)mFRAWm)dS09~6F7Y{0j$O7J5KJ`gxx0#!!icwUDxj_QI&BM&~r=%8meXB2c?Sl`g_r-zW2}F2Fn4^}#tv_Lx)M#m@DU*)f2"
    "GG9n&T$hRcwV?Rp(Go&K&$F$v;k@hS2Ath*pRG53QpL(mt2~Q#;!{3mLmAXtM15lHom&7ht~%epgKE!Ff)-u8LXoj+#GQ?w?cT1OaqzJlA"
    "F?w>b-SKTK?AitAfQN`nR`sQdjLgOv2znf`$9#L>u3yl$UBRBQAeHN|Sk#o}LcWSjP1cDrNvf+DSp)zWgp!PwIy#hkL#~$^q(+N`9_1k{S"
    "SuN{+g07(cuXWj}CKet5R(PS`DUMQBUlpA<Z3PkYL?SHj!RG%;K0l*I~)J<MHIhszOP&QUfQzbc9!qNco<=`kP)a=qljM(7+Oi2C{S=gjR"
    "?U(#}BmB35i*~dQzFkw)_o}w|kNy^RM%SWR2)0FKaH|Cer@k5}DBWM#$R`8M{($afh{IHG*NUTNNiqC)FoEv@DbHo9mBG8HzSi_x!NpATX"
    "g}f4YrkLhp*qm>*=5MBmKeWf@w_wrWWj`B)CwU`kykAGDaX)X$CRSU(iPTY!!YK{*Z-^qph`*J}s#C7=?+-?el5KOGfFD}qFiCHOhN^#jT"
    "!utb|6QqN;)2l6+$_WSZ@Ho0H@`ILeJ(3xVu&O3uql1)Uh*Fu?0ap|7gUqvVI-s&9+#rdw0`<IYfHY+SLpiqWQ6@ql=~#yF6FzZWeal@T!"
    "VF%x3Uy<JbfZS>M5H`ZY(N4OG(SB_jf^82!@iX{`>geRi*8?*>$T>)Sx9TEGqO5mnSuB-At$K$ZZ`tWm0M+3lp7uwI*jEkVi)5x#@{3C9t"
    "ta0~iB7d--jHjyRq$N=fDAu4q{GoGTJZ;N-pKXt?wnnu5#r`{t&;J(mtS<?I4DxTb126#R>VUuVr^-lD{A^abJ0+J!EiGA!D}xinCVGY6A"
    "LD}5zo`wIoNs-Fx=3(c0f2iPw=sE&E6zfTgyB8*M4<*&Z}TGOYYF9b}9>JNU}dleQ3dd=5AmtQc`D9A9Tl@@`3%DBtO@&g1RrWv*iGz0uk"
    "C%N@Ad1r=7$VZrQkENlByS$Zs+RsVMm`WT0lgYe+<iS6lrR4-fz|o6|=hS`p=c|OL2l~q49dWj~FQav0C<)PhfU(+26x34y+0dGbZ_!a$2"
    "qu>+-=t}(<qLV5VKu3_O)tAgs*E*=e%1R}X*E_J_Vr(C#IWy|U;oT*d!m~|<HNZVf<!3rMXB8^+&Vpb)Di-^PBT|%bXya-MKE8AoenP^eV"
    "}{N$ZNdfHf$3g3U%phc$BvzUla6(Gb}PkZ-#jqk?LH!FhRTIPw{2&&O>n>W?-t$i;)4w0traE_Em6i5a|V_3ordc;4Uz4?2CSU?usq88yy"
    "g^L};uTn=-z163dGqyV{j4b~eaORi_3Q6M_e$B;?3lc2AgD6o%i(mLJWXlQ?Es4WIh3_ex5TarwnctycO&Pp6r@-V=Ord&?ed9U}U)_a?y"
    "NpGT5FR~17lCt|44Z=`{Um`e0L!{r<8fV20i139lOk;kN|!mfF>S&P;J(SAtR{L{}l=MpVB5+$xv58j8S2d43=r6U}ZdVEk!8;Q0)_I4Lk"
    "pP#sL>HUsa9M^=eA)$6FO5F`aH(H9%ymglw?{F)o_l@vLe1f+-9s`kZ)hVV``a<h*`zyhv*-~xNYMVxLr*P*sWM&PSt38A$d~1?9?<NbdL"
    "hTD^W!gFj9){LH|NX3K9A{$m{Qv&%|M|cE!~gML|KUIX<&Xb4)E*MCWJ3AXP%e(2?zk>7|089C_g-~y2Y=0B7T-9H`VfU?sNo~LtfnaiZT"
    "V*697P+Wy!o*-p+q*984A$e^<Id%S}E9<IoRsGVJ1$~I7W|3J?^TMLKM<oy0UPy(k$mIe|AVRg0m->NnMG<*k85=tKY+<r{(MXAT%zXWLl"
    "?n)Z{JF?87PK%ZOf<?iVywqHVYeT8$P@3U8{a9s%VsZEBxxw)bj-^)M7Zq-9Ceu~!?EhD3Mg2JJe|XGox>l9c||6Wm-)93(d?Cyw2M)_=+"
    "27I0XGv8|dW{d<!~PS79h`ygNYIhzP}3_|KvHx@xFWW+|nN=P%CXS#Q%R_)D!uX$s&kS$S>+6<fU78*`<PLh5lHr{8w>xZz?-=P|xES3@^"
    "HL!&4q<|n(&tsNwlFD0GE4$SXpRw;I+$ZSzL74cFDRWcAJ=%@*=eSpIO8;bO4otE&uAUz}KYJcKIfd9?J}LUPV)Jm6yP%Hl%uMQ*OYjU*c"
    "Ek)DF#B5Ti12;s$_=4Nqa)BP@-Gb19y@!|MyBu`91fYTpK8dB1f3sd_o0WlHYyFz_vX{ke(0&N`N*}qst6KQJZnAw+mRT-$Ii`Ju#U|<-D"
    "Xna7P%}W-f9~vy{&kg+yMQ83`5fp{u~C3N8F59t2&YzP8@sILm0i9H~$WU|2`53Af*rRJj;l_xDr1yL68{~Kl$6PrO0)=NgP8@CxO@(h|Y"
    "lw^_9`tS|DHiyS<lx`Qv}sdxihJ#($)~DBqYh5-8HW{`BjwUhxf)Py9J;GbqyoLhGVI;?<h6be7Tk#r+;DJEqoZye1-;Z5^m*lU?>4X7cL"
    "Jgh}((-<NOSz6}h+7H$!I2NEmb`Oz&ra%jvlHl{Yl=NHhLR=kZk4imFad(*brZ^zIC=cao`KvfN65_0n-E_~b1;+uy1y4j?UC7_WhS~uB6"
    "hUI_x<Fnq|XT7~=z1?TMH_v)I&wAU>das}LUOkf_+zsI5DqF^$N^;L`pqez>iQIE&i67e~%$9h`Rf%rO5*ojUQs7MqZ*w+b+4cZ)k@kWA9"
    "RgCh?TjLjAN(~Et1HGB_79yI_?4w6Equ>4>(ABi!v!XvxO{=Wu0|?Lb0Bn>``3?|dPtm4nx)rNUw0F{Ui3JO4F#43K5zr`p#=?c^o<%!jg"
    "~0gd%YP*Uzg_ITT)-EasEbPeC74O*d$q><JI8I1sLRXD2?8|i0>&`;-LIP8*?;{Q4~)%^6Qibp2b=;a-!6RGb|>uWv!d&J;%(8oyf))Tnm"
    "nouxJg|+e@1*9ORtzTDx#@5Hx4RW}7lu<kW<v$(J1Er6b^Of_iai7h-Pg9MEB%KveBg5OUx!q^0{XRY>Nt_u-)P#1~S)d#K;TrXVhMgEr#"
    "N#8T_qPWag?e5wnwMZR!NjPOF8_*0_b#X^cr`m?0+AQy6>O#PU&Hd~lN-Nmolnm1=5JwxJr*(_Nxc`8Leb?mVzT&9(6)Ikk=#g&g%AzN@S"
    "6z!*pm`O|d+g8t3hH9fF@-_J%y{N5ZaM?}{XZ0G^Yc3Bb9hz2&<KgwX%7Oe7KEU}_(!IwMi7K^eB};AMPEw^yymzFh%-JpS$t>ZjD9wY<G"
    "T)0mGLS^^NzLP8rDq?J?_;&4y-f~%odv%<!KOvheIn>6nMD={&}r38p(zwvc2V~oTO4`c1>586)KT#Q1PZZyiq)&=_mzXcRMUW#$Qgb|5O"
    "U#sf(d(^L-<9D*!JfrJ7ooE>VEbrV3}zPJZ6HwjZ-hVu({|F3HxlB4Esgw=%FFMyoOv;1n=1@H!`YeNu_j=#^sO9y-Rzm?sYm#jY!L#-ja"
    "$|lQ0?kcy;ES625SX261Ie6Tn7j?27jPLl%3D(moQx^Z8Re3!@`V;gZgrO!zqHm#<?VBk<RRs(VALt)TZ>ElB)ddIE+pi{caPWsQZwku@E"
    ")ShRToex&bdwA<!fw&ci>M$!bMovt(fw<V!4wEYrBFPO+77>{HRN#|lBnFk-|TgS~jQf@g}aa#ictY=V)sz9Ax{es=_jLpz$Jbc@4^~Cv<"
    "%`#MjvQZ)?;W64Jo$H&VE6Z(xQBl5}eEnz6H^_k*B%|4dVf})uc*0Vj``E$PzWm19A78%OX;bXU)a7hr8q;$8Wb@X1s@3PxmPkXkY`LKQI"
    "BQI@Wm5cd?YtTOb=y2aM>x`ZZ+nC1;FLbuhcWCEr^@}vj>1MrO0V&HcJQBVZ_2YhL>)%wkZQXrKud3e+_?qvdN-uo;=YGSEHT6+xT&TF0-"
    "#cQQM-Z*Ro%P)_dkC96W|Ye*uY|fwDk{k-(O^dOF6C;7xjFLQVYQ#9O_YN*#(}T;N%LaD`&BO_TKg;)6SXb-!X985B25;t--8(aXZC6AK="
    "SU&#|6Nt$EBr`n9HKjp}3=^D6kgLTI`C(9`sxH<lB{a(v!TgxcsS6R9?_@eIkm*IUEz7E4~TYqRuO3n!4g;b8I>srQSgj(F08A8^$aTf?("
    "`DU85>rSD&_a!Kr-uvV~dZb>s6<hBWydwh0fCwHz$z8|Y6dFuUgv68%q#E7u1B{VLZ<<g3Fn*LNT*>=l*CQ<gSZ)1b(c_tlk)r2}>2bfqC"
    "-EHlbVbV9_cqvsAK-zXxT#k_dS4oRWHostl7+>&suU+o`sYZThx!<`nt1xH#`%%R{^!sk#vZQJhPc7W&`{q7%7o#|Wm7F21`qM4?!xK;xQ"
    "X!~>HH_0tu^=CpXz?sA%yyR9Ug%JQq}WWdg&6;H`<2qhsp#6&89Wjn5jdJ#A7F%)L#E7iQ%XN(;$ioYDU7<qM{;|unxi=f>XYE=>!c<45a"
    "sP})RI>7=EvtFZNH1rs;~Q5OVYu&d{d$}8AMf57Yb7kai%8gp?CUjBhCBI719ESU;iv|YH-bI<%zxZeh~dJO803kLoI-Ng02lkT_RaOl?o"
    "$ied|NqQg)XDN)8na&YN^Ic5pb9f-2WkJ?7Wtz3W|m{omN2eQnTS5k);sd`esR`;Zk*PLx^=CQ6&3UD}CO6bZTgtg2nv2XDUK-T?985!2W"
    "<^eVF*E~W+V1(dP2dkhFolCF%LyJ%?R9uW#d5VVw~Jb1Nr5a#kHl7p3Ndgt^3LjXZih^&TVe*GV62VOD+G2U^y`^jRF&C0L8#<&^Y4IfN%"
    "dkgRB)1K6}fvK--7ozjEVG<a<%~&PE+Y^qjZ+WM-RmGRc`dirCYpL%NB5AfaDuSodT5k}a)Z{Fy)et6`9i6h?EHPO(r_*s~5WZbFkLppoE"
    "w@#{c9i7#ihx9VLfnEtIPaND`C2AG3ADMm)wC<m3fbGk!K0&^wy;EG$*g6$O@zdND7U)HeC$2z98zuqIq%+qxGm22Q#Y1!W+dN2tK=J(-)"
    "d%?{e56or1d<JNJ@^f8f0OwcngX*l%jd?N@L`1Y(C+hZLXD;ICYT?bb&BhZ&e9o8k8&W{;4EGKy2n-KgGjcX|tK|MXopuug$%Kk+=y&-p{"
    "$O%b8m-?&{~aVG=B&GqIR+&36{ucj>AuhQDs7TBbHB`IMEj$oWv`?bsH+TcH%%&~nKoq6icB;C9zGKuiG&b!Y;Tp4AIFmP0A_k{pVArH$*"
    "QK+?dJ8&TG=sWpTRYZft1n=?Zm!M_tr@$T((Zp2W8@YGpTYFSVWL8B(bQ^kU&-6J}%W2!xOZ2E&e*Z!f&O7+I?Y%;`k>R5s-x$uX-0v<qk"
    "wr4PEvmUx=3iuGR`1lU4qGeEN<$Y2+-;>ukavV`aq&f*zBlfsI327l?&e0w{AmV@Q8?$ddp_i>|Aky1&iue}z%(;RU-W-NJ5>V0@m7hqc4"
    "SSHlFZZGFKm2TeL#X#l_8ul3+qs03diQoZ8rneo>6OiI)0#p24$T+Nko;t49Cw!f)FG+a?bJPN1u4C==C}wMGbdawx%!?@dGy@7XbRckIE"
    "uU>0;b)}rpWZ?Q&jbr;$7So=cK^ghbWAl4F(~$pbs6JkQ9v(c@@7$5h&avUq!kQVH@3BX*oXvd$mvIpuuKq&TmJWrHJv_Tze2c_#szWEiH"
    "aj)C1nMkN9o5g0jiI?o9C00w8nz`|rYDVlVBC3F3!HT4jbJ1~A&yTu5~v6_e3*l%p(rdplujI$$N#X=KxT{IsAE9ZLF&&H^%?3MKVqt0uN"
    "|Qd3!;Po=QV+}jm-7=c0}$j@E^hJgAV-^1=s){6@UaJoOKgxbbOD9hfOF=h_tC@yP*QYn*A0d+5Fha&%aj`Ns#2w5$5QpOb%>n9s#xzsOh"
    "V-k#BF*?<fvVqK^PA9e^MbuhWfLDhmyjU?SV>y)7ahe}>eS2ss+S8eh7PFm=u!)o&e>U}P9)nJ*mX*+VNkLZH*lERfQM{!lqe+JabVMU0_"
    "e6|yQp`jGniFR1&6liy`0kH932>;cIG}kem|q4c5~Ty$*j`GQaE`*zdQ2XsoI4q$A9PA&koUIPr^F004Zhr2bLXyUi=Mk@Wh3^GNmGVtxa"
    "2O)gy}V@kKt0d<|5-J@{a%6k`ljXMrKI@UUXnP_<O{9ivlpoMh!13f`|~)B8$%<0w!Kf%QJ=x6h&zPJYPtsse>He3j!F^OhDHe;-!$Ir*Y"
    "AKo=&Bd-}}&OH<?$d_NTGOD;C(yvB5$Jx)sw^q*`?EG``9r^qAagy6VZ)s>K#PKp+W`<18q8tJgUYM19o$q$3e1*2{hj;-cs9B}XSL3SpE"
    "|mJp{?lbT@vT<zltpMA5TCgBI|50jb;-bg*df%Y)(*R&L06heir2?sEkNX{B^fkW&F>hKqc*BcnAuXAOV!P@v{O|MiougPnktG;O)S9f0S"
    "{OFH=Q@k2qC6b@?z+B}gN4nY~yeY?-Pl;ih3H^CcPoB$v{Z(D)|0#oQJ2SZ!!Q9i<1{cy;Boq>~OL#DS9Za65Z<VFXAjrm2ePHiR%Y<hH("
    "}v9FH|v2NBNxs%Z4b#M=UCE9t-hM;Qp}_}iGL%GPw<`K4nAF+h9xWOInfJh$VzalSNVDeK2hn7uQ&r=cBZO6a8J_h0E1$)BKYmtQ)sk@^I"
    "of@er$^nt?D|toPWPC@MTxA;=+%FHR$EG!=AwA|JjwHEfEpz5pn#46lt4IbGj4Tfe)5kw49{Vg8%RvuL-*h_+t*9|K6f<QS7fPjfN%Kq+b"
    "y3TcoesG7)PV>PncQ-*+iQy+R)R%*L(lb7`8oj@zt1p3>KvdGCaF#ynea#DKI8a>%Ts|DSNFz?+0n0&u~KRP27DT>+DA9j1h&JxbEbCvhH"
    "h^4sr!?&5dPRq6ALI1%@_McXzTZq)MXFn>??$eQVx?LV9%0KMN^=-zY{PY=;TiP&rN88#XT&qh?ZX79ZDE^nrk(0_{j{fWzcP9K(<Q2*4{"
    "v3>T4?!o2nVX3^Ci?MystmtKaALee}EXL*mp+8ZO3!JSv+-(*MD&l^cBVR>gp~+_a&GjWXmL@%*!%lhWkRMBU!ZmlkquaUT<R`lOH0;TKR"
    "dal+`SJw`5<G(>jNkQswxx>^%x^YjmvH^RGpmf$RFV6(@d%86((d;p$zgue?MZOm)J-G~q}ZS|E#cRnNY_Hmk}1+C5mq}yK;Fc0RQJVQ-H"
    "fAr7)f){Ev|o3NT$6<(cSHKg|bd5GZ;;r?>{H4?QTpNcB(|LkM36JLYK(IZ(HIyIQy_c$@v`Aaki3ra)Elkv(+18x)<CY4KZ^&VWNoTavy"
    "ESQ2O9AY?l{2`3QA-o_@Hve@_Y+Z)|Hyv`_Uuvi@UjTZEw_U$HUM$X8mSFeg$m40$_I0J57%O8#6qqOSW8%!BnYdA)VMb!oYl*0HOf38;D"
    "sNtwCGOA#uYp*|0qw$9T!y}peYO4VpKXc;bJn^YExET3jbr;!GzCy79miarO0W#00WdqP`v(c`F9CK2x)+wEG8h$1W}X}$A>Xt}s&=zzJ$"
    "?GnI|fM01Byy({Cf6-g3I6@TR{KW+8(P^1A7DBO_OHgUMYWD2`iR=39CYIv&u9`Q79Wwr02u?&GZtnsi6g+j=BED^FOPsn!;+VNp`eGbLL"
    "28xeGnbfkY6pykUirmI{LEoM9yR5yZzerKWFqn2QkujObSt=ovA^ilWMi=bUo0V8ZRXE(tu4^b8_vJf2JFe}t5Op(^TIo?XBoceZOSk7Nk"
    "jD6wF_2@&>#^v)6jP@-~^8$C!k}Umey-48+zU_OI@pu>EFJijEaWD6pJDrV6Zy4gP$~E<!LMJ0}DYapW{{xF(_Tu|29d;=P0Pw9F|hxpaQ"
    "aaw)Te~%Z&0klZN(#(%Xb%VNhPyL{%bKg}@~CbTTZ8Yd>8{R;Yg?l8axQwk0#YpPRf1)X;*S8cna~9=FNr09I1G;|yN6Y^E&;aW=KT?2|4"
    "a9;1FO#>}t*&dt)~3stCL`B3Z2?gotx;3F%%T+A1mQ@_&i<}mH3AwK~p0}kU7zvXzvEV|~M?<W@#gq%0opZJ<NP<}UGt~Y=A<Fg-s{1Mu8"
    "W+qx{L4?mZtYugDYq;v5DeC}T0mKv%gmwfP$|Qcu=5y~5Ee`KZn9^>~o-|w0bEXYZt|D_q8BiSegCEZxw!w20kT!RWW-kd|;Le9l9v|Egr"
    "-WBe!{!kQM{00ZTdhdYw!ZClqmPeSE6c*BU$<Cmb2td6$b(X|@2D9QpZDIY-L_?i{YsT2nui9tyb?)|!C2t!lS!=lzKvCL=OH7S0VBGPos"
    "^dnJ$_ly6f9j}FrAq0A&Ds~9=f3~wXmDu{vmPfU<}^f6uvz$)AV&7v3p>tV{Xarx*e!b*f*Gt*II~aJ1N}p)GRCZ^(6?C`?m<o?7jB9Tb)"
    "wqhsP0&$-JfJh_rnCVKcc)ma$`7h{*wxkz7@e2u&@33~nqvS`cr&@BM-Nai6t*8V+6{gesqv*&@B$jh*tw)_#5*5~y7U<2sG9;_I(4loE-"
    "fX{_@F<q$8Jcy7m0ZfPP4H`?%bQ8PW^(Q_vTef9vR{vix|kkT7LB|+f}7goO;5;C%r($-bX9kg@rlK_e$>~e=*PIsiMXVNHB>s4x#%tXj~"
    "s!J<C>~>QD%)O7Y+wCaok_2QTTM)PiB*~Z@$sa{9D*4sSBo_h(2ShsXE0PEgN-4LeDhNDy8=0uv|9@pyvfQ>2M1O^+ROKMWt~d!GA5x;Ih"
    "1#r$a$NCkxJZNrVrUSMiu$=6@?+`O-P1FGXjgJkNgxE0v-I@x`n?~5T3Q@8=<p5D2q2D2ZNA;8sQkuJKyY5~OKd>%SeqjS1Te!T<7vB-83"
    "=jqvXhqnt(SQp-;+ZQ*eSP10Uv>&Uy`UC8Hahypk-Aq_(^=C-+)j@blUmFUNKpydO4^Gz}@V7IGr)g%5zcLn@Mr0t+nj$>U$*?#f$XpJF-"
    "%D^d06*i5;ISkbIL}xmNc)V_i{lqBmTn{*w+NRDc)ZMca7dlj2lx_EBgw*kG-dW4QCT-ZZhgre``Tc8tlZp4(gOaC_0mtfbJK?6jx#!eZt"
    "#T*4xWgOFZG#)~;JXYEu(5CiBQP4}lhP9x`yHuXP$&p66s-&IP32p7mAuIwZ0a?>O)4_jf+8G&k{9$eH;@;i43l7|BSIM7xlZRI>82YoX*"
    "E;gZ?C;LBv`$uHq3qXL8cZIU)hc8~_4{eUV9SjY(B7DG*vg^eR&3l^JVa=innV%`!$HT8~YEML7SeA?rp*GpK#eEYZ+8PT|3gLkkL<M$64"
    "x*VCt`fd-wwh03HThy#G7VWlC#UhAIVh*08wTSK&u;EgLd;i}!p^$68p--AW)0F@fs-K&cQ=q7H(>tZRwq@);7$v6Zv&8Jj@ELc*vyiY$t"
    "2J#C@YD+eo=3wX!4oXkjiDeqbHQ8?N{#s#hAGot%UEDKC7_7V5fk7JTSEZj;%8%3fzb)(yBqW%f~wr42N{@S{5SPg$8^3YtRI~OeUkB#2>"
    "bc%0YvYTTLYuin#>0)@|sjg^<(!r~N}c+Qofp!83>SSrd0B`O}<T0-h5`is<YxRTb>UmAL<*4wZ>Jh59LM^X!q!dGuQi*T~gtyBbz8eGzG"
    "}A=hB0MG8H!rI3jGg9DRwOF>F31s*A&X}CR0Pek73)k`7V5d4c?K6Rxdi#hn^%^OCmt88W_!cQppqYHL)J~-a{EPYVPnhX8R&}pGfG!<~^"
    "U5!Ph%_sK$X~9Y5KT#~0$5nS+ZC%J&uR`FEy)LjYv;Z_cgNw??FW6U9)Lx*_Iv93!nmPvj8|&wW_Cu4HOIm9ngup5oChWnNpmHkh^L{L$*"
    "1%NWw2H5e6l{G2*4-JmZM()w3t1YaOM;S-eX(4dX<|o!cfw`c+Vbps(;P4wEl#pW(n2*Rh4-(drpwShMYlfg&-VwVQZh4dr@1{@zhZafk<"
    "Vw&1!ijqH+3TPk=xE00CF7zn2dFYmtOd&7;SmqzPunouxgb@G}{qPOJTiU(+1;De*Ex|oZ(N4Qu6)fl-$FOHA{9bM&THKhprnoZ0&j9&*k"
    "2ULNs~k+h{xSAGd|^&Ira8x^z`c?#G+--<Y{t=qtCPM6g=LeQ(hiJuGerI@91OCrrDkagq$6+@k+*7>EWXkO>gbj!LxbsApOsOe|5D)Cal"
    "C3>u#-BCm=}P9p;IYg%yI?;FDLMqn5Q8w%%NBve7<{Fm3=op&Q?$rgT98ok`|c?|e9{j^{{^qw6FHRINUkvNQIi0-~0-yWZRm>er)-Y+!|"
    "o9`%f)B8NyN0DNH;1xFvA6^AyW!?);VNR?fW%%73y6*Gh!CM<>=TE(5=owhL30+&D&{{I9s@}i?8}iy7z1s;AhK8g{(2Y=k@VJ%MFhea6X"
    "0qzjAib`)GCk}mO7CLrZ#<7cP~;Lq1S4zEQNKoGTX%s5!3mY~mTy#5+yhZ?xWO9^5o55oIWybVTS3PPC<@i49`|0p1HLMRgW+X!{YRdGUF"
    "9PEu$nOzqjk4ft>eq&7SCr4kcyOdsEc2FI>>(ycbzgpB7Il?s8ky9&#($GE8}sP9o~Nmyi<!5`mwRLTQsR`H7o!=RN%_a)@p=n?ukpu!+K"
    "(wUy}gAxf{}7{VO&LQ&4Pir3=U2G+>GF{mFDTmM#$%KrS34Q<Nl(M_6Rd;vs=wu<}toE#^YCE<|WfW9y`mJny;VM%^-LtIfi;^eb8l$0q5"
    "Zm!RR=5T>#*&sTIaqHU=b%cx_0>z-xhP>ixHY|{Q?j}GWZL#sJtNH|Xs#GUsn^$YA*+=9Kv?jxl9X5CvlsB0k`GR+0;nVrR*^3Cw*bV)14"
    "%LpA91QTflkti<K6bh`<&y|RED;T?@-py~<t*xPeFRla~`l+3ch=-7)NKp`J-hy{KqO&XKPy@W8Xbv&yWWkGX^o2Z#OQ;Xn{M<6sfOQwkg"
    "7(8&so}2J=twhQQQBfoF&@3v^!!^gl&p{NX=yF1`Rk6}5jhU%+IR>7IF>*QrA<U4KPQBydEco{=}>dyBgWwPN7IL(0Ick8YeRP?e*|i}N)"
    "q0snTp9`&3zw^L1Pu4*|H*6M%l*VT;LR9L9`(q983QsOo`}%#%8}M>|=s4d5fgLQ_;L=qlwVtwb62()9*mTwgqPnPD<|@>DF(2uk@AoQr_"
    ")qo!X|+R+LOWEHxRIjD+y{pL#*yqIaI6fm`1`Bo@5(g5(Pu(nR9<WA?Cc3LsQZ^=<a{oxR;ok_>SNd&`)o1z&F~z5p!|zZP}}h;_utOyqH"
    "*LPTPG0;T#-G}<1G%YU>G20`68t(oj4*|0k<$G?yDPnO{&kJ%ShVnu21N?Q%X|28dC_Ka6+)<_M5U%YT-urN7By3p51V;7;v0fb&Hbel&~"
    "-TZZT=9!A>@HoIn9D^(1+7)FWNTuQ9{9Ot`#m$}*J=gF;J~1xA7E9R(3PwR6T5UU8Iv>509b|y#etR%@{er>h^IZ=22nVUM)2Un{nj4+vl"
    "JkIHyQIZ*@0Kdh2?Txu?$SH6H<@Z~q4PYBOa0{7tr?a^fS3RHFZ_2flK"
)


@lru_cache(maxsize=1)
def songguesser_bundled_grid_year_index() -> tuple[dict[tuple[str, str], str], dict[str, str]]:
    from zlib import decompress
    snapshot = decompress(base64.b85decode(SONGGUESSER_GRID_YEAR_SNAPSHOT)).decode("utf-8")
    return songguesser_index_grid_year_lines(snapshot.splitlines())



def songguesser_grid_year(artist: Any, album: Any, album_artist: Any = None) -> str:
    """Look up the earliest Grid album date, with an offline snapshot fallback.

    Use the deployed grid.txt when possible. If it is absent, stale, or does
    not contain an album, use the full user-provided Grid index bundled with
    this code. Spotify's year remains the fallback when neither source matches.
    """
    album_text = str(album or "").strip()
    if not album_text:
        return ""

    variants: list[str] = []

    def add_variant(value: str) -> None:
        key = songguesser_grid_normalize_album(value)
        if key and key not in variants:
            variants.append(key)

    add_variant(album_text)
    # Spotify sometimes reverses the two exact subtitle clauses of a release.
    # Example: "More Blood, More Tracks: The Bootleg Series, Vol. 14
    # (Sampler)" vs. Grid "The Bootleg Series Vol. 14: More Blood,
    # More Tracks". Match only the *entire* reversed title, never its
    # fragments (particularly not "Blood On The Tracks").
    def add_reversed_clauses(value: str) -> None:
        clauses = value.split(":", 1)
        if len(clauses) == 2 and all(part.strip() for part in clauses):
            add_variant(clauses[1].strip() + ": " + clauses[0].strip())

    add_reversed_clauses(album_text)
    remaining = album_text
    for _ in range(3):
        stripped = re.sub(r"\s*[\[(][^\]()\[\]]+[\])]\s*$", "", remaining).strip()
        if not stripped or stripped == remaining:
            break
        add_variant(stripped)
        add_reversed_clauses(stripped)
        remaining = stripped

    # Preserve artist/album identity while dropping release-specific suffixes.
    stripped = re.sub(
        r"\s*[-–\u2014:]\s*(?:original\s+album|bonus\s+tracks?|\d{4}\s+"
        r"(?:remaster(?:ed)?|edition|mix)|reissue|deluxe|expanded)\b.*$",
        "", album_text, flags=re.IGNORECASE,
    ).strip()
    if stripped != album_text:
        add_variant(stripped)

    names: list[str] = []
    if isinstance(album_artist, str):
        names.append(album_artist)
    elif isinstance(album_artist, list):
        names.extend(
            item.get("name", "") if isinstance(item, dict) else str(item)
            for item in album_artist
        )
    if artist:
        names.append(str(artist))
        names.extend(re.split(r",\s*|\s+feat(?:uring)?\.?\s+", str(artist), flags=re.IGNORECASE))

    artist_keys: list[str] = []
    for name in names:
        norm = songguesser_grid_normalize_artist(name)
        if norm and norm not in {"unknownartist", "variousartists"} and norm not in artist_keys:
            artist_keys.append(norm)

    def lookup(indexes: tuple[dict[tuple[str, str], str], dict[str, str]]) -> str:
        by_pair, unique_titles = indexes
        for artist_key in artist_keys:
            for album_key in variants:
                year = by_pair.get((artist_key, album_key))
                if year:
                    return year
        # Allow sufficiently distinctive uniquely indexed albums to match
        # alternate Spotify credits (Bob Marley & The Wailers / Bob Marley).
        for album_key in variants:
            if len(album_key) >= 9 and unique_titles.get(album_key):
                return unique_titles[album_key]
        if not artist_keys and variants:
            return unique_titles.get(variants[0], "")
        return ""

    try:
        stat = GRID_FILE.stat()
        live_index = songguesser_grid_release_year_index(
            str(GRID_FILE), stat.st_mtime_ns, stat.st_size
        )
    except (OSError, UnicodeError) as error:
        # Keep the game playable on deployments where grid.txt wasn't included.
        live_index = None
        append_log(f"[songguesser year hint: grid.txt unavailable ({error}); trying bundled Grid year index]")

    if live_index is not None:
        live_year = lookup(live_index)
        if live_year:
            return live_year

    bundled_year = lookup(songguesser_bundled_grid_year_index())
    if bundled_year:
        append_log(
            f"[songguesser year hint: bundled Grid supplied {bundled_year} for "
            f"artist={artist!r}, album={album_text!r}; "
            f"deployed grid.txt missing or has no matching entry]"
        )
    return bundled_year


def songguesser_apply_grid_release_year(answer: dict[str, Any], prepared: dict[str, Any]) -> None:
    album_artist = prepared.get("grid_album_artist")
    track = prepared.get("track") if isinstance(prepared.get("track"), dict) else {}
    track_album = track.get("album") if isinstance(track.get("album"), dict) else {}
    if not album_artist:
        album_artist = track_album.get("artists")
    year = songguesser_grid_year(answer.get("artist"), answer.get("album"), album_artist)
    if year:
        answer["releaseYear"] = year
    # Release decade must ALWAYS follow the final corrected year, including
    # when a cached answer or Spotify enrichment supplied the year.
    answer["releaseDecade"] = songguesser_release_decade_from_year(
        str(answer.get("releaseYear") or "")
    )


def songguesser_track_identity_keys(track: dict[str, Any], fallback: str = "") -> set[str]:
    """Match both Spotify URIs and song identities across playlist/album sources."""
    configure_sampler_tools()
    keys: set[str] = set()
    uri = str(track.get("uri") or "").strip()
    if uri:
        keys.add(f"uri::{uri}")

    title = str(sampler_tools.format_track_name(track) or "").strip()
    artist = str(sampler_tools.format_track_artist(track) or "").strip()
    is_placeholder = (
        title.lower().startswith("public playlist item at position")
        or title.lower().startswith("local file at playlist position")
        or title.lower() == "unknown track"
        or artist.lower() == "unknown artist"
    )
    if title and artist and not is_placeholder:
        def norm(value: str, is_artist: bool = False) -> str:
            # Ignore dots/hyphens/spaces: "L.A. Blues" and "LA Blues"
            # are the same title for no-repeat matching.
            ascii_text = unicodedata.normalize("NFKD", value).encode("ascii", "ignore").decode("ascii").lower()
            if is_artist:
                ascii_text = re.sub(r"^the\s+", "", ascii_text)
            return "".join(re.findall(r"[a-z0-9]+", ascii_text))
        artist_id, title_id = norm(artist, True), norm(title)
        if artist_id and title_id:
            keys.add(f"song::{artist_id}::{title_id}")
    if not keys and fallback:
        keys.add(f"position::{fallback}")
    return keys


def songguesser_candidate_identity_keys(candidate: dict[str, Any]) -> set[str]:
    prepared = candidate.get("prepared") or {}
    fallback = ""
    if prepared.get("kind") == "playlist_context":
        fallback = f"{prepared.get('playlist_id')}::{prepared.get('playlist_position')}"
    return songguesser_track_identity_keys(prepared.get("track") or {}, fallback)


def songguesser_get_page_history(page_id: str) -> dict[str, Any]:
    """Keep an in-memory no-repeat history until this shuffle.html tab reloads."""
    now = time.time()
    # Limit stale histories and memory consumption, independent of Topster caches.
    for key, history in list(songguesser_page_histories.items()):
        if now - float(history.get("updated_at", 0)) > 24 * 60 * 60:
            songguesser_page_histories.pop(key, None)
    if len(songguesser_page_histories) > 512 and page_id not in songguesser_page_histories:
        oldest = min(songguesser_page_histories, key=lambda key: songguesser_page_histories[key].get("updated_at", 0))
        songguesser_page_histories.pop(oldest, None)

    history = songguesser_page_histories.setdefault(page_id, {"keys": set(), "updated_at": now})
    history["updated_at"] = now
    return history


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

    answer = {
        "artist": artist,
        "album": album_name,
        "song": song,
        "releaseYear": release_year,
        "releaseDecade": release_decade,
        "coverUrl": cover_url,
    }
    songguesser_apply_grid_release_year(answer, prepared)
    return answer


def songguesser_tracklist_entry(track: dict[str, Any], position: int) -> dict[str, Any]:
    """A display-only row preserving an album/playlist's original order."""
    configure_sampler_tools()
    track = track if isinstance(track, dict) else {}
    album = track.get("album") if isinstance(track.get("album"), dict) else {}
    uri = str(track.get("uri") or "")
    local_parts = sampler_tools.parse_local_uri_parts(uri) if uri.startswith("spotify:local:") else {}
    return {
        "position": int(position),
        "name": sampler_tools.format_track_name(track),
        "artist": sampler_tools.format_track_artist(track),
        "uri": uri,
        "album": album.get("name") or local_parts.get("album") or "",
        "albumId": str(album.get("id") or ""),
        "isLocal": bool(track.get("is_local") or uri.startswith("spotify:local:")),
    }


def songguesser_public_tracklist(game: dict[str, Any], candidate: dict[str, Any]) -> dict[str, Any]:
    """File playlists show the entire playlist; single-link playlists only
    show the songs from the current song's album *within* that playlist.
    Album links show the whole album in both input modes.
    """
    source_rows = candidate.get("source_tracklist") or []
    prepared = candidate.get("prepared") or {}
    active_track = prepared.get("track") or {}
    active_album = active_track.get("album") if isinstance(active_track.get("album"), dict) else {}
    active_uri = str(active_track.get("uri") or "")
    answer = candidate.get("answer") or {}
    chosen_name = str(answer.get("song") or "")
    chosen_artist = str(answer.get("artist") or "")
    active_album_name = str(active_album.get("name") or answer.get("album") or "")
    active_album_id = str(active_album.get("id") or "")
    rows = source_rows
    if candidate.get("source_kind") == "playlist" and game.get("source_mode") == "playlist":
        # Single Spotify playlist URL: show only matching album entries,
        # keeping their original playlist positions and order.
        album_key = songguesser_grid_normalize_album(active_album_name)
        rows = [row for row in source_rows if (
            bool(active_album_id and row.get("albumId") and row["albumId"] == active_album_id)
            or bool(album_key and songguesser_grid_normalize_album(row.get("album")) == album_key
                    and not (active_album_id and row.get("albumId") and row["albumId"] != active_album_id))
        )]
    # Track identity is Unicode-aware. The Grid normalizer intentionally
    # strips non-ASCII text for album lookup, but using that for track titles
    # makes distinct Japanese / Korean / Chinese titles all match as "".
    def track_key(value: Any) -> str:
        normalized = unicodedata.normalize("NFKC", str(value or "")).casefold()
        return "".join(char for char in normalized if char.isalnum())

    chosen_title_key = track_key(chosen_name)
    chosen_artist_key = track_key(chosen_artist)

    def text_match(row: dict[str, Any]) -> bool:
        return bool(
            chosen_title_key and chosen_artist_key
            and track_key(row.get("name")) == chosen_title_key
            and track_key(row.get("artist")) == chosen_artist_key
        )

    selected_position = prepared.get("playlist_position") if candidate.get("source_kind") == "playlist" else None

    def at_prepared_position(row: dict[str, Any]) -> bool:
        if selected_position is None:
            return False
        try:
            return int(row.get("position")) - 1 == int(selected_position)
        except (ValueError, TypeError):
            return False

    # The actual Spotify URI is stronger than text, including local-file URIs.
    # Prefer the original position only among URI-matching entries. If Spotify
    # skipped that position, search the entire list for the actual track.
    uri_matches = [i for i, row in enumerate(rows) if active_uri and row.get("uri") == active_uri]
    name_matches = [i for i, row in enumerate(rows) if text_match(row)]
    candidates = uri_matches if uri_matches else name_matches
    matched_index = next((i for i in candidates if at_prepared_position(rows[i])), None)
    if matched_index is None and candidates:
        matched_index = candidates[0]

    output = [{
        "position": row.get("position"), "name": row.get("name"),
        "artist": row.get("artist"), "isLocal": row.get("isLocal", False),
        "current": index == matched_index,
    } for index, row in enumerate(rows)]
    return {
        "kind": candidate.get("source_kind") or "album",
        "scope": ("album_in_playlist" if candidate.get("source_kind") == "playlist"
                  and game.get("source_mode") == "playlist" else "full_source"),
        "rows": output,
        "available": bool(output) and not candidate.get("source_tracklist_unavailable"),
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
    prepared["grid_album_artist"] = album.get("artists") or []

    return {"prepared": prepared, "answer": songguesser_track_answer(prepared), "source_kind": "album"}


def songguesser_candidate_from_playlist_item(
    playlist_bundle: dict[str, Any],
    item: dict[str, Any],
    cache: dict[str, Any] | None = None,
    use_lastfm_local_cover: bool = False,
) -> dict[str, Any]:
    configure_sampler_tools()

    prepared = sampler_tools.prepare_playlist_item_clip(
        playlist_bundle=playlist_bundle,
        item=item,
        clip_seconds=SONGGUESSER_CLIP_SECONDS,
        random_start=True,
        assumed_duration_seconds=SONGGUESSER_ASSUMED_DURATION_SECONDS,
        cache=cache,
        use_lastfm_local_cover=use_lastfm_local_cover,
    )

    # Save the playlist thumbnail separately. If Spotify skips a local file and
    # starts a different item, the fallback artwork must not belong to the
    # originally selected local file.
    prepared["playlist_cover_url"] = playlist_bundle.get("cover_url")
    item_track = item.get("track") or {}
    item_album = item_track.get("album") if isinstance(item_track.get("album"), dict) else {}
    prepared["grid_album_artist"] = item_album.get("artists") or []

    return {"prepared": prepared, "answer": songguesser_track_answer(prepared), "source_kind": "playlist"}



def songguesser_answer_has_unknown_album(answer: dict[str, Any]) -> bool:
    album = str(answer.get("album") or "").strip().lower()
    return not album or album in {"unknown album", "none", "null"}


def songguesser_should_lookup_answer(answer: dict[str, Any], hints_enabled: dict[str, Any]) -> bool:
    # Manual cover overrides are keyed by artist + album, so resolve a missing
    # album even when the user did not enable album/year hints.
    if songguesser_answer_has_unknown_album(answer):
        return True

    if not any(hints_enabled.get(key) for key in ("releaseYear", "releaseDecade", "album")):
        return False

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

        if songguesser_should_lookup_answer(answer, hints_enabled):
            looked_up = songguesser_search_track_metadata(sp, answer)
            if looked_up:
                for key in ("artist", "album", "song", "releaseYear", "releaseDecade", "coverUrl"):
                    value = looked_up.get(key)
                    if value and (key not in answer or not answer.get(key) or (key == "album" and songguesser_answer_has_unknown_album(answer))):
                        answer[key] = value

        # Spotify enrichment can fill a previously unknown album. Reapply the
        # grid override afterward so Spotify's reissue year never wins.
        songguesser_apply_grid_release_year(answer, candidate.get("prepared") or {})


def songguesser_summary_payload(game: dict[str, Any]) -> list[dict[str, Any]]:
    summary = []

    for index, candidate in enumerate(game.get("queue") or [], start=1):
        answer = songguesser_answer_with_saved_cover(candidate.get("answer") or {})
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
    excluded_keys: set[str] | None = None,
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
        identity_keys = songguesser_track_identity_keys(track)
        if track_key in used_keys or (excluded_keys is not None and not identity_keys.isdisjoint(excluded_keys)):
            continue
        used_keys.add(track_key)
        if excluded_keys is not None:
            excluded_keys.update(identity_keys)
        candidate = songguesser_candidate_from_album_track(album, track)
        candidate["source_tracklist"] = [
            songguesser_tracklist_entry(album_track, index)
            for index, album_track in enumerate(tracks, start=1)
        ]
        candidates.append(candidate)
        if len(candidates) >= maximum:
            break

    return candidates


def songguesser_build_playlist_candidates(
    sp: Any,
    cache: dict[str, Any],
    playlist_link: str,
    used_by_source: dict[str, set[str]],
    maximum: int,
    use_lastfm_local_cover: bool = False,
    excluded_keys: set[str] | None = None,
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
        identity_keys = songguesser_track_identity_keys(
            item.get("track") or {},
            f"{playlist_id}::{item.get('playlist_position')}",
        )
        if item_key in used_keys or (excluded_keys is not None and not identity_keys.isdisjoint(excluded_keys)):
            continue
        used_keys.add(item_key)
        if excluded_keys is not None:
            excluded_keys.update(identity_keys)
        candidate = songguesser_candidate_from_playlist_item(
            playlist_bundle=playlist_bundle,
            item=item,
            cache=cache,
            use_lastfm_local_cover=use_lastfm_local_cover,
        )
        candidate["source_tracklist_unavailable"] = bool(playlist_bundle.get("public_items_inaccessible"))
        candidate["source_tracklist"] = [
            songguesser_tracklist_entry(playlist_item.get("track") or {},
                                        int(playlist_item.get("playlist_position", 0)) + 1)
            for playlist_item in (playlist_bundle.get("items") or [])
        ] if not candidate["source_tracklist_unavailable"] else []
        candidates.append(candidate)
        if len(candidates) >= maximum:
            break

    return candidates


def songguesser_build_candidates_from_file(
    sp: Any, cache: dict[str, Any], albums_file: Path, excluded_keys: set[str] | None = None,
) -> list[dict[str, Any]]:
    configure_sampler_tools()

    lines = sampler_tools.load_album_lines(str(albums_file))
    if not lines:
        raise RuntimeError("No album or playlist links were found in the uploaded text file.")

    used_by_source: dict[str, set[str]] = {}
    candidates: list[dict[str, Any]] = []
    reserved_keys = set(excluded_keys or set())

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
                    candidates.extend(songguesser_build_playlist_candidates(
                        sp, cache, line, used_by_source, 1, excluded_keys=reserved_keys,
                    ))
                else:
                    candidates.extend(songguesser_build_album_candidates(
                        sp, cache, line, used_by_source, 1, excluded_keys=reserved_keys,
                    ))
            except Exception as error:
                append_log(f"[songguesser warning: skipped source {line!r}: {error}]")

        if len(candidates) >= SONGGUESSER_SONG_COUNT:
            break
        if len(candidates) == progress_before:
            break

    if len(candidates) < SONGGUESSER_SONG_COUNT:
        raise RuntimeError(
            f"Songguesser needs five tracks that have not played since the last page refresh, "
            f"but only {len(candidates)} are available in the uploaded text file. "
            "Choose more sources or refresh shuffle.html to reset the no-repeat history."
        )

    return candidates[:SONGGUESSER_SONG_COUNT]


def songguesser_build_candidates_from_single_link(
    sp: Any, cache: dict[str, Any], link: str, excluded_keys: set[str] | None = None,
) -> list[dict[str, Any]]:
    configure_sampler_tools()

    used_by_source: dict[str, set[str]] = {}
    reserved_keys = set(excluded_keys or set())

    if sampler_tools.extract_spotify_album_id(link):
        candidates = songguesser_build_album_candidates(
            sp=sp,
            cache=cache,
            album_line=link,
            used_by_source=used_by_source,
            maximum=SONGGUESSER_SONG_COUNT,
            excluded_keys=reserved_keys,
        )
    elif sampler_tools.extract_spotify_playlist_id(link):
        candidates = songguesser_build_playlist_candidates(
            sp=sp,
            cache=cache,
            playlist_link=link,
            used_by_source=used_by_source,
            maximum=SONGGUESSER_SONG_COUNT,
            use_lastfm_local_cover=True,
            excluded_keys=reserved_keys,
        )
    else:
        raise RuntimeError("Invalid Spotify album or playlist link/URI.")

    if len(candidates) < SONGGUESSER_SONG_COUNT:
        raise RuntimeError(
            f"Songguesser needs five tracks that have not played since the last page refresh, "
            f"but only {len(candidates)} remain available in that album/playlist. "
            "Choose a larger source or refresh shuffle.html to reset the no-repeat history."
        )

    return candidates[:SONGGUESSER_SONG_COUNT]


def songguesser_answer_with_saved_cover(answer: dict[str, Any]) -> dict[str, Any]:
    public_answer = dict(answer or {})
    default_cover_url = str(public_answer.get("coverUrl") or "").strip()
    public_answer["defaultCoverUrl"] = default_cover_url
    override = read_lyrics_album_cover_override(
        public_answer.get("artist") or "",
        public_answer.get("album") or "",
    )
    if override and override.get("imageUrl"):
        public_answer["coverUrl"] = override["imageUrl"]
        public_answer["manualCoverOverride"] = override
    else:
        public_answer["manualCoverOverride"] = None
    return public_answer


def songguesser_hint_cover_url(game: dict[str, Any], candidate: dict[str, Any], public_answer: dict[str, Any]) -> str | None:
    prepared = candidate.get("prepared") or {}

    if game.get("source_mode") == "file" and candidate.get("source_kind") == "playlist":
        playlist_cover = str(prepared.get("playlist_cover_url") or "").strip()
        if playlist_cover:
            return playlist_cover

    cover_url = str(
        public_answer.get("coverUrl")
        or public_answer.get("defaultCoverUrl")
        or ""
    ).strip()
    return cover_url or None


def songguesser_public_payload(game: dict[str, Any], candidate: dict[str, Any], position_ms: int) -> dict[str, Any]:
    answer = candidate.get("answer") or {}
    # The hint must reflect the ACTUAL reconciled track, not an earlier
    # Spotify-search reissue date or a previous playlist candidate.
    songguesser_apply_grid_release_year(answer, candidate.get("prepared") or {})
    public_answer = songguesser_answer_with_saved_cover(answer)
    hints_enabled = game.get("hints") or {}
    release_year = answer.get("releaseYear") or ""
    release_decade = answer.get("releaseDecade") or ""

    hints = {
        "releaseYear": release_year if hints_enabled.get("releaseYear") and release_year else None,
        "releaseDecade": release_decade if hints_enabled.get("releaseDecade") and release_decade else None,
        "artist": answer.get("artist") if hints_enabled.get("artist") else None,
        "album": answer.get("album") if hints_enabled.get("album") else None,
        "albumCover": songguesser_hint_cover_url(game, candidate, public_answer) if hints_enabled.get("albumCover") else None,
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
        "answer": public_answer,
        "tracklist": songguesser_public_tracklist(game, candidate),
        "hints": hints,
        "paused": bool(game.get("paused")),
    }


def songguesser_current_spotify_playback(sp: Any) -> dict[str, Any] | None:
    """Read the live Spotify Connect track, not the cached playlist item."""
    try:
        try:
            playback = sp.current_playback(additional_types="track")
        except TypeError:
            playback = sp.current_playback()
    except Exception:
        return None
    return playback if isinstance(playback, dict) else None


def songguesser_confirm_playlist_playback(
    sp: Any,
    prepared: dict[str, Any],
    previous_playback: dict[str, Any] | None,
    direct_track_uri: str = "",
    timeout_seconds: float = 5.0,
) -> dict[str, Any]:
    """Confirm the *actual* Spotify track rather than trusting playlist offsets.

    The Spotify API may skip unavailable/local playlist entries. Conversely, the
    playback context can be omitted in the status response. Exact URI matches
    are reliable without a context; other tracks are accepted only when their
    live playback is confirmed inside the requested playlist context.
    """
    previous = previous_playback or {}
    previous_item = previous.get("item") if isinstance(previous.get("item"), dict) else {}
    previous_uri = str(previous_item.get("uri") or "")
    previous_progress = previous.get("progress_ms")
    previous_context = previous.get("context") if isinstance(previous.get("context"), dict) else {}
    expected_context_uri = f"spotify:playlist:{prepared['playlist_id']}"
    expected_uri = str((prepared.get("track") or {}).get("uri") or "")
    expected_position = int(prepared.get("position_ms") or 0)
    deadline = time.monotonic() + max(0.2, timeout_seconds)
    stable_uri = ""
    stable_count = 0

    while time.monotonic() < deadline:
        time.sleep(0.3)
        playback = songguesser_current_spotify_playback(sp)
        if not playback or not playback.get("is_playing"):
            continue

        item = playback.get("item")
        if not isinstance(item, dict) or item.get("type", "track") != "track":
            continue
        uri = str(item.get("uri") or "")
        if not uri:
            continue

        # Direct-URI fallback is verified only by that exact Spotify track.
        if direct_track_uri:
            if uri == direct_track_uri:
                return playback
            continue

        # An exact match is safe even when Spotify omits playlist context.
        if expected_uri and uri == expected_uri:
            return playback

        context = playback.get("context") if isinstance(playback.get("context"), dict) else {}
        if str(context.get("uri") or "") != expected_context_uri:
            continue

        # Spotify may skip a playlist entry. Require proof this is a new start
        # before adopting an otherwise unexpected song as the correct answer.
        if uri != stable_uri:
            stable_uri, stable_count = uri, 1
        else:
            stable_count += 1

        progress = playback.get("progress_ms")
        near_start = isinstance(progress, (int, float)) and abs(progress - expected_position) <= 12000
        progress_changed = (
            isinstance(previous_progress, (int, float))
            and isinstance(progress, (int, float))
            and abs(previous_progress - progress) > 4500
        )
        different_track = bool(uri != previous_uri)
        different_context = not previous or str(previous_context.get("uri") or "") != expected_context_uri
        if stable_count >= 2 and (
            different_track or (different_context and near_start)
            or (progress_changed and near_start)
        ):
            return playback

    raise RuntimeError(
        "Spotify did not report a new playing track for the requested playlist. "
        "Songguesser cannot safely determine an answer for this round."
    )


def songguesser_confirm_album_playback(
    sp: Any,
    prepared: dict[str, Any],
    timeout_seconds: float = 7.5,
) -> dict[str, Any]:
    """Wait for the requested Spotify track to actually play.

    Spotify Connect may acknowledge start_playback() while the player remains
    paused. The regular sampler intentionally tolerates this; Songguesser must
    not start a *graded* round with no verified playing song. Poll only: sending
    start_playback() again could audibly restart a successfully playing clip.
    """
    expected_uri = str((prepared.get("track") or {}).get("uri") or "")
    if not expected_uri.startswith("spotify:track:"):
        raise RuntimeError("Songguesser cannot identify the requested album track.")
    deadline = time.monotonic() + timeout_seconds
    last_observed = ""
    while time.monotonic() < deadline:
        time.sleep(0.35)
        playback = songguesser_current_spotify_playback(sp)
        if not playback:
            continue
        item = playback.get("item") if isinstance(playback.get("item"), dict) else {}
        linked_from = item.get("linked_from") if isinstance(item.get("linked_from"), dict) else {}
        actual_uris = {str(item.get("uri") or ""), str(linked_from.get("uri") or "")}
        if playback.get("is_playing") and expected_uri in actual_uris:
            return playback
        last_observed = (
            f"status={'playing' if playback.get('is_playing') else 'paused'}, "
            f"track={str(item.get('uri') or 'unknown')}"
        )
    append_log(
        "[songguesser warning: album playback unconfirmed; "
        f"requested={expected_uri}; observed={last_observed or 'no Spotify status'}; "
        f"source={prepared.get('source_text') or 'unknown'}]"
    )
    raise RuntimeError(
        "Spotify accepted Songguesser's playback command but never confirmed "
        "that the selected album track began playing. No round was started. "
        "Check that Spotify Connect is active on the intended device, then retry."
    )


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
    selected_device_id = spotify_selected_device_id_for_account(sp)
    device_id = sampler_tools.get_device_id(sp, None, selected_device_id)
    if selected_device_id:
        append_log(f"[songguesser: using manually selected Spotify device {device_id}]")
    candidate = queue[current_index]
    prepared = candidate["prepared"]
    # Preserve the original playlist position identity even if Spotify skips
    # this entry and we replace prepared.track with the real playing item.
    initial_candidate_keys = songguesser_candidate_identity_keys(candidate)
    is_playlist = prepared.get("kind") == "playlist_context"
    before = songguesser_current_spotify_playback(sp) if is_playlist else None
    track = prepared.get("track") or {}
    track_uri = str(track.get("uri") or "")

    # Restore the Spotify playlist-context start that worked before the last
    # patch. The *answer* is reconciled to the actual Spotify playback, so
    # skipped/unavailable entries cannot create an incorrect Songguesser answer.
    playback_prepared = dict(prepared) if is_playlist else prepared
    if is_playlist and prepared.get("blind_public_playlist"):
        # Do not adopt a stale previous playback item in sampler.py; the
        # synchronization check below decides which track actually began.
        playback_prepared["blind_public_playlist"] = False

    append_log(
        "[songguesser playback request: "
        f"source={prepared.get('source_text') or prepared.get('album_name') or 'unknown'}; "
        f"kind={prepared.get('kind')}; "
        f"uri={track_uri or 'unavailable'}; "
        f"device={device_id}]"
    )
    position_ms = sampler_tools.start_prepared_clip(
        sp=sp,
        device_id=device_id,
        prepared=playback_prepared,
        local_seek_delay_seconds=SONGGUESSER_LOCAL_SEEK_DELAY_SECONDS,
        verify_playback=False,
    )

    # Album-link items use direct track URIs. Confirm that Spotify actually
    # starts the track before revealing a timed/graded round. Unlike the old
    # verifier, this never restarts an already-audible segment.
    if not is_playlist:
        songguesser_confirm_album_playback(sp, prepared)

    used_exact_uri_fallback = False
    if is_playlist:
        try:
            observed = songguesser_confirm_playlist_playback(
                sp=sp,
                prepared=prepared,
                previous_playback=before,
            )
        except RuntimeError as first_error:
            # Spotify can acknowledge a context start yet remain idle. A direct
            # catalog-track start is a recovery *only*, not the default, and
            # does not depend on playlist offsets to determine its identity.
            if track_uri.startswith("spotify:track:") and not prepared.get("is_local") and not prepared.get("blind_public_playlist"):
                append_log("[songguesser: playlist context did not start; trying exact Spotify track URI]")
                recovery = dict(prepared)
                recovery["kind"] = "track_uri"
                position_ms = sampler_tools.start_prepared_clip(
                    sp=sp,
                    device_id=device_id,
                    prepared=recovery,
                    local_seek_delay_seconds=SONGGUESSER_LOCAL_SEEK_DELAY_SECONDS,
                    verify_playback=False,
                )
                used_exact_uri_fallback = True
                try:
                    observed = songguesser_confirm_playlist_playback(
                        sp=sp,
                        prepared=prepared,
                        previous_playback=before,
                        direct_track_uri=track_uri,
                    )
                except RuntimeError as second_error:
                    raise RuntimeError(
                        "Spotify did not start the selected Songguesser track using "
                        "either playlist-context or direct-track playback. Make sure "
                        "the intended Spotify Connect device is active and the track "
                        "is playable on that device. No answer was graded."
                    ) from second_error
            else:
                # Local files and inaccessible public-playlist positions cannot
                # safely be started by a regular track URI. Try reactivating
                # the selected Connect device, then the playlist context again.
                live = songguesser_current_spotify_playback(sp)
                if live and live.get("is_playing"):
                    raise first_error
                append_log("[songguesser: no live playlist playback; reactivating Spotify Connect device]")
                try:
                    sp.transfer_playback(device_id=device_id, force_play=True)
                    time.sleep(0.5)
                except Exception as error:
                    append_log(f"[songguesser warning: device reactivation unsuccessful: {error}]")
                position_ms = sampler_tools.start_prepared_clip(
                    sp=sp,
                    device_id=device_id,
                    prepared=playback_prepared,
                    local_seek_delay_seconds=SONGGUESSER_LOCAL_SEEK_DELAY_SECONDS,
                    verify_playback=False,
                )
                observed = songguesser_confirm_playlist_playback(
                    sp=sp,
                    prepared=prepared,
                    previous_playback=before,
                )

        if not used_exact_uri_fallback:
            # Playlist-context playback may have skipped the selected position.
            # Adopt the actual track metadata, never the cached position's song.
            observed_item = observed["item"]
            observed_track = sampler_tools.simplify_track(observed_item)
            observed_album = observed_item.get("album") if isinstance(observed_item.get("album"), dict) else {}
            prepared["grid_album_artist"] = observed_album.get("artists") or []
            if not observed_track.get("uri") and not observed_track.get("name"):
                raise RuntimeError("Spotify did not expose the actual track for this Songguesser round.")
            old_uri = track_uri
            prepared["track"] = observed_track
            prepared["is_local"] = bool(observed_track.get("is_local"))
            prepared["track_text"] = (
                f"{sampler_tools.format_track_name(observed_track)} - "
                f"{sampler_tools.format_track_artist(observed_track)}"
            )
            album = observed_track.get("album") or {}
            prepared["album_name"] = album.get("name") or "Unknown album"
            if album.get("release_date"):
                prepared["release_date"] = album["release_date"]
            cover = album.get("cover_url") or sampler_tools.best_image_url(album.get("images"))
            if prepared.get("is_local") and game.get("source_mode") == "playlist":
                cover = sampler_tools.apply_lastfm_local_cover(observed_track) or cover
            if old_uri == observed_track.get("uri") and prepared.get("cover_url"):
                cover = cover or prepared["cover_url"]
            prepared["cover_url"] = cover or prepared.get("playlist_cover_url")
        sampler_tools.save_sampler_state(prepared, position_ms)

    # Record the track Spotify actually played, not merely its queued offset.
    # This prevents a skipped playlist entry from repeating a previously heard
    # track and ensures restarts on this page do not reuse it.
    history = game.get("page_history")
    if isinstance(history, dict):
        actual_keys = songguesser_candidate_identity_keys(candidate)
        if actual_keys and not actual_keys.isdisjoint(history["keys"]):
            try:
                sp.pause_playback()
            except Exception:
                pass
            raise RuntimeError(
                "Spotify played a track already heard on this page. The duplicate "
                "was not accepted as a Songguesser round. Choose another source "
                "or refresh shuffle.html to reset the no-repeat history."
            )
        history["keys"].update(actual_keys | initial_candidate_keys)
        history["updated_at"] = time.time()

    candidate["answer"] = songguesser_track_answer(prepared)
    try:
        songguesser_enrich_queue_answers(
            sp=sp,
            queue=[candidate],
            hints_enabled=game.get("hints") or {},
        )
    except Exception as error:
        append_log(f"[songguesser warning: could not enrich current track: {error}]")

    game["started_at"] = time.time()
    game["position_ms"] = position_ms
    game["paused"] = False
    game["playback_retry_pending"] = False
    return songguesser_public_payload(game, candidate, position_ms)


def songguesser_retryable_playback_error(game: dict[str, Any], error: Exception):
    """Keep the same candidate/index after Spotify fails to start a round.

    Never expose the answer or advance the game from this response. The client
    must explicitly request a retry of exactly this numbered round.
    """
    game["playback_retry_pending"] = True
    STATE_FILE.unlink(missing_ok=True)
    current_index = int(game.get("current_index", 0))
    append_log(
        f"[songguesser round {current_index + 1} playback failed; awaiting user retry: {error}]"
    )
    return jsonify({
        "ok": False,
        "retryable": True,
        "progress": current_index + 1,
        "total": len(game.get("queue") or []),
        "error": str(error),
    }), 502


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
        page_id = str(data.get("pageSessionId") or "").strip()
        if not re.fullmatch(r"[A-Za-z0-9_-]{16,100}", page_id):
            # Legacy clients receive a fresh history per game; the updated
            # shuffle.js always supplies a fresh token once per page load.
            page_id = secrets.token_urlsafe(24)
        if source_mode not in {"file", "playlist"}:
            return jsonify({"ok": False, "error": "Invalid source mode."}), 400

        hints = {
            "releaseYear": form_bool(data.get("hintReleaseYear"), False),
            "releaseDecade": form_bool(data.get("hintReleaseDecade"), False),
            "artist": form_bool(data.get("hintArtist"), False),
            "album": form_bool(data.get("hintAlbum"), False),
            "albumCover": form_bool(data.get("hintAlbumCover"), False),
        }

        try:
            sp = get_spotify_client()
        except RuntimeError:
            return jsonify({"ok": False, "error": "Press Login with Spotify before starting Songguesser."}), 401
        except Exception as error:
            return jsonify({"ok": False, "error": f"Could not connect to Spotify: {error}"}), 500

        configure_sampler_tools()
        cache = sampler_tools.load_cache()
        history = songguesser_get_page_history(page_id)
        # Mirror browser-held history: if Render restarted without a page
        # refresh, the frontend still knows which songs were already heard.
        try:
            client_seen = json.loads(str(data.get("previousTracks") or "[]")[:150000])
            if isinstance(client_seen, list):
                for key in client_seen[:5000]:
                    if isinstance(key, str) and len(key) <= 256 and re.fullmatch(r"song::[a-z0-9]+::[a-z0-9]+", key):
                        history["keys"].add(key)
        except (TypeError, ValueError, json.JSONDecodeError):
            pass
        excluded_keys = set(history["keys"])

        try:
            if source_mode == "playlist":
                link = str(data.get("playlistLink", "")).strip()
                if not link:
                    return jsonify({"ok": False, "error": "Enter a Spotify album or playlist link first."}), 400
                queue = songguesser_build_candidates_from_single_link(sp, cache, link, excluded_keys)
            else:
                uploaded_albums_file = save_uploaded_albums_file()
                if uploaded_albums_file is None:
                    return jsonify({"ok": False, "error": "Upload a .txt file containing album or playlist links."}), 400
                queue = songguesser_build_candidates_from_file(sp, cache, uploaded_albums_file, excluded_keys)
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
            "source_mode": source_mode,
            "page_history": history,
            "created_at": time.time(),
        }
        songguesser_games[game_id] = game
        session["songguesser_game_id"] = game_id
        append_log("[starting Songguesser]")

        try:
            return jsonify(songguesser_start_current(game))
        except Exception as error:
            # Preserve the exact queued first track. Destroying the game here
            # prevented any retry without generating a different five-song queue.
            return songguesser_retryable_playback_error(game, error)


@app.route("/api/songguesser/next", methods=["POST"])
def songguesser_next():
    game = get_current_songguesser_game()
    if game is None:
        return jsonify({"ok": False, "error": "No active Songguesser game."}), 404
    if game.get("playback_retry_pending"):
        return songguesser_retryable_playback_error(
            game, RuntimeError("This round is waiting for the Retry Round button.")
        )

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
        return songguesser_retryable_playback_error(game, error)


@app.route("/api/songguesser/retry", methods=["POST"])
def songguesser_retry():
    with sampler_lock:
        game = get_current_songguesser_game()
        if game is None:
            return jsonify({"ok": False, "error": "No active Songguesser game."}), 404
        if process_is_running():
            return jsonify({"ok": False, "error": "Stop the regular sampler before retrying Songguesser."}), 409
        if not game.get("playback_retry_pending"):
            return jsonify({"ok": False, "error": "This round is not waiting for a playback retry."}), 409
        data = request.get_json(silent=True) or {}
        try:
            requested_round = int(data.get("progress", 0))
        except (ValueError, TypeError):
            requested_round = 0
        current_round = int(game.get("current_index", 0)) + 1
        if requested_round != current_round:
            return jsonify({"ok": False, "error": "The retry request does not match the pending round."}), 409
        # Do not change current_index, shuffle the queue, or mark another song
        # as heard. The regular start routine verifies actual Spotify playback.
        try:
            return jsonify(songguesser_start_current(game))
        except Exception as error:
            return songguesser_retryable_playback_error(game, error)


@app.route("/api/songguesser/pause", methods=["POST"])
def songguesser_pause():
    game = get_current_songguesser_game()
    if game is None:
        return jsonify({"ok": False, "error": "No active Songguesser game."}), 404
    pause_spotify()
    game["paused"] = True
    return jsonify({"ok": True, "paused": True})


@app.route("/api/songguesser/play", methods=["POST"])
def songguesser_play():
    game = get_current_songguesser_game()
    if game is None:
        return jsonify({"ok": False, "error": "No active Songguesser game."}), 404
    try:
        sp = get_spotify_client()
        sp.start_playback()
        append_log("[Spotify Songguesser playback resumed]")
    except Exception as error:
        return jsonify({"ok": False, "error": f"Could not resume Songguesser playback: {error}"}), 502
    game["paused"] = False
    return jsonify({"ok": True, "paused": False})


@app.route("/api/songguesser/stop", methods=["POST"])
def songguesser_stop():
    # A user may toggle from Sampler to Songguesser before clicking Stop.
    # Legacy clients call this endpoint according to the checkbox state; do
    # not leave the regular sampler running invisibly.
    if process_is_running():
        return stop_sampler()
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

        try:
            selected_device_id = spotify_selected_device_id_for_account(get_spotify_client())
        except Exception as error:
            return jsonify({"ok": False, "error": str(error)}), 409

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

        if selected_device_id:
            cmd.extend(["--device-id", selected_device_id])

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
        # A completed or terminated child must never block a new Songguesser
        # round. poll() is the authoritative check; clear the dead reference.
        if sampler_process is not None and sampler_process.poll() is not None:
            sampler_process = None
        running = process_is_running()

    # Do not hold the process lock during a potentially slow Spotify API pause.
    pause_spotify()
    return jsonify({"ok": True, "running": running, "wasRunning": was_running})



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
        result = dict(cover_art)
        default_url = str(result.get("url") or "").strip()
        result["defaultUrl"] = default_url
        override = read_lyrics_album_cover_override(
            result.get("artist") or "",
            result.get("album") or "",
        )
        if override and override.get("imageUrl"):
            result["url"] = override["imageUrl"]
            result["manualCoverOverride"] = override
        else:
            result["manualCoverOverride"] = None
        return result

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
    if is_topster_admin_protected_page(filename) and not is_topster_admin():
        if topster_admin_password_is_configured():
            return redirect("/topster-admin-login")
        return "Topster editor access is restricted to the host computer.", 403

    target = BASE_DIR / filename
    if target.is_file():
        return send_from_directory(BASE_DIR, filename)
    return send_from_directory(BASE_DIR, "index.html")


if __name__ == "__main__":
    app.run(host="127.0.0.1", port=5000, debug=True)
