from __future__ import annotations

import argparse
from concurrent.futures import Future, ThreadPoolExecutor
import json
import os
import random
import re
import time
from pathlib import Path
from urllib.parse import unquote_plus

import spotipy
from dotenv import load_dotenv
from spotipy.oauth2 import SpotifyOAuth


ALBUMS_FILE = "albums.txt"
CACHE_FILE = "album_cache.json"
STATE_FILE = "sampler_state.json"
ACTIVE_DEVICE_ID_OVERRIDE: str | None = None

SCOPE = (
    "user-read-playback-state "
    "user-modify-playback-state "
    "user-read-private "
    "playlist-read-private "
    "playlist-read-collaborative"
)


def load_spotify_client(
    token_cache_path: str = ".spotify_token_cache",
    open_browser: bool = True,
) -> spotipy.Spotify:
    load_dotenv()

    required = [
        "SPOTIPY_CLIENT_ID",
        "SPOTIPY_CLIENT_SECRET",
        "SPOTIPY_REDIRECT_URI",
    ]

    missing = [key for key in required if not os.getenv(key)]
    if missing:
        raise RuntimeError(f"Missing environment variables in .env: {', '.join(missing)}")

    return spotipy.Spotify(
        auth_manager=SpotifyOAuth(
            client_id=os.getenv("SPOTIPY_CLIENT_ID"),
            client_secret=os.getenv("SPOTIPY_CLIENT_SECRET"),
            redirect_uri=os.getenv("SPOTIPY_REDIRECT_URI"),
            scope=SCOPE,
            cache_path=token_cache_path,
            open_browser=open_browser,
        )
    )


def load_album_lines(path: str) -> list[str]:
    lines = []

    with open(path, "r", encoding="utf-8") as file:
        for raw_line in file:
            line = raw_line.strip()
            if not line or line.startswith("#"):
                continue
            lines.append(line)

    if not lines:
        raise RuntimeError(f"No albums or playlists found in {path}")

    return lines


def load_cache() -> dict:
    """
    Loads album_cache.json safely.

    If the cache file is empty, malformed, or not a JSON object, ignore it and
    start with a fresh cache. This prevents a corrupted cache from stopping the
    sampler before playback starts.
    """

    path = Path(CACHE_FILE)
    if not path.exists():
        return {}

    try:
        raw_text = path.read_text(encoding="utf-8")
    except OSError as error:
        print(f"WARNING: Could not read {CACHE_FILE}; starting with an empty cache. Error: {error}")
        return {}

    if not raw_text.strip():
        print(f"WARNING: {CACHE_FILE} is empty; starting with an empty cache.")
        return {}

    try:
        cache = json.loads(raw_text)
    except json.JSONDecodeError as error:
        backup_path = Path(f"{CACHE_FILE}.corrupt_{time.strftime('%Y%m%d_%H%M%S')}")
        try:
            path.replace(backup_path)
            print(
                f"WARNING: {CACHE_FILE} was not valid JSON and was moved to "
                f"{backup_path.name}. Starting with an empty cache. Error: {error}"
            )
        except OSError:
            print(
                f"WARNING: {CACHE_FILE} was not valid JSON. Starting with an empty "
                f"cache. Error: {error}"
            )
        return {}

    if not isinstance(cache, dict):
        print(f"WARNING: {CACHE_FILE} did not contain a JSON object; starting with an empty cache.")
        return {}

    return cache


def save_cache(cache: dict) -> None:
    """
    Saves the cache atomically to reduce the chance of leaving an empty/corrupt
    album_cache.json if the script is interrupted while writing.
    """

    path = Path(CACHE_FILE)
    temp_path = Path(f"{CACHE_FILE}.tmp")

    with open(temp_path, "w", encoding="utf-8") as file:
        json.dump(cache, file, indent=2, ensure_ascii=False)

    temp_path.replace(path)


def best_image_url(images: list[dict] | None) -> str | None:
    if not images:
        return None

    valid_images = [image for image in images if isinstance(image, dict) and image.get("url")]
    if not valid_images:
        return None

    best = max(valid_images, key=lambda image: int(image.get("width") or 0))
    return best.get("url")


def simplify_artists(artists: list | None) -> list[dict]:
    simplified = []

    for artist in artists or []:
        if isinstance(artist, str):
            name = artist
        elif isinstance(artist, dict):
            name = artist.get("name")
        else:
            name = None

        if name:
            simplified.append({"name": name})

    return simplified


def simplify_album(album: dict) -> dict:
    images = album.get("images") or []
    external_urls = album.get("external_urls") or {}
    tracks_page = album.get("tracks") or {}
    track_items = tracks_page.get("items") or []

    simplified = {
        "id": album["id"],
        "uri": album.get("uri") or f"spotify:album:{album['id']}",
        "name": album.get("name") or "Unknown album",
        "artists": [artist["name"] for artist in simplify_artists(album.get("artists"))],
        "external_url": external_urls.get("spotify"),
        "release_date": album.get("release_date"),
        "release_date_precision": album.get("release_date_precision"),
        "images": images,
        "cover_url": best_image_url(images),
        "tracks_first_page": [],
        "tracks_complete": False,
    }

    if track_items:
        simplified_tracks = [
            simplify_track(track, album_context=simplified)
            for track in track_items
            if isinstance(track, dict)
        ]
        simplified["tracks_first_page"] = simplified_tracks
        simplified["tracks_complete"] = tracks_page.get("next") is None

    return simplified


def simplify_track(track: dict, album_context: dict | None = None) -> dict:
    album = track.get("album") if isinstance(track.get("album"), dict) else {}

    if album_context:
        album_name = album.get("name") or album_context.get("name")
        album_images = album.get("images") or album_context.get("images") or []
    else:
        album_name = album.get("name")
        album_images = album.get("images") or []

    track_id = track.get("id")
    uri = track.get("uri") or (f"spotify:track:{track_id}" if track_id else None)

    return {
        "id": track_id,
        "uri": uri,
        "name": track.get("name") or "Unknown track",
        "duration_ms": track.get("duration_ms"),
        "type": track.get("type") or "track",
        "is_local": bool(track.get("is_local")),
        "artists": simplify_artists(track.get("artists")),
        "album": {
            "name": album_name,
            "release_date": album.get("release_date") or (album_context or {}).get("release_date"),
            "release_date_precision": album.get("release_date_precision") or (album_context or {}).get("release_date_precision"),
            "images": album_images,
            "cover_url": best_image_url(album_images),
        },
    }


def cache_album(cache: dict, album_line: str | None, album: dict) -> dict:
    simplified = simplify_album(album)
    album_id_key = f"album_id::{simplified['id']}"

    cache[album_id_key] = simplified

    if album_line:
        cache[f"album::{album_line}"] = simplified

    if simplified.get("tracks_complete") and simplified.get("tracks_first_page"):
        cache[f"album_tracks::{simplified['id']}"] = {
            "complete": True,
            "tracks": simplified["tracks_first_page"],
        }

    return simplified



def album_cache_entry_is_hydrated(album: dict | None) -> bool:
    """
    Old album_cache.json entries did not store images/cover_url/embedded tracks.
    Treat those as stale so the currently played album can be refreshed once.
    """

    if not isinstance(album, dict):
        return False

    if not album.get("id"):
        return False

    if not album.get("cover_url") and not album.get("images"):
        return False

    return True


def hydrate_album_cache_entry(
    sp: spotipy.Spotify,
    album_id: str,
    album_line: str | None,
    cache: dict,
    fallback: dict | None = None,
) -> dict:
    """
    Refreshes one album with the single-album endpoint.

    This is used only for the album actually being prepared when the persistent
    cache is missing cover art. It avoids the forbidden batched-albums endpoint
    while still restoring cover display.
    """

    try:
        album = sp.album(album_id)
        simplified = cache_album(cache, album_line, album)
        save_cache(cache)
        return simplified
    except Exception as error:
        if fallback:
            print(
                f"WARNING: Could not refresh album cover metadata for album ID "
                f"{album_id}: {error}"
            )
            return fallback

        raise


def track_has_cover(track: dict | None) -> bool:
    if not isinstance(track, dict):
        return False

    album = track.get("album")
    if not isinstance(album, dict):
        return False

    return bool(album.get("cover_url") or album.get("images"))


def enrich_tracks_with_album_context(tracks: list[dict], album: dict) -> list[dict]:
    """
    Adds album cover context to cached tracks created by older sampler.py builds.

    Spotify's album_tracks endpoint returns simplified track objects that do not
    reliably include album artwork. The album object carries the cover.
    """

    album_name = album.get("name")
    album_images = album.get("images") or []
    album_cover_url = album.get("cover_url") or best_image_url(album_images)

    if not album_name and not album_images and not album_cover_url:
        return tracks

    changed = False

    for track in tracks:
        if not isinstance(track, dict):
            continue

        track_album = track.get("album")
        if not isinstance(track_album, dict):
            track_album = {}
            track["album"] = track_album
            changed = True

        if album_name and not track_album.get("name"):
            track_album["name"] = album_name
            changed = True

        if album_images and not track_album.get("images"):
            track_album["images"] = album_images
            changed = True

        if album_cover_url and not track_album.get("cover_url"):
            track_album["cover_url"] = album_cover_url
            changed = True

    return tracks


def preload_album_cache(sp: spotipy.Spotify, lines: list[str], cache: dict) -> None:
    """
    Batch-load direct Spotify album links before playback.

    Spotify's Get Several Albums endpoint accepts up to 20 album IDs per request.
    For normal albums with 50 or fewer tracks, this single batched response also
    carries the first/only page of album tracks, so later playback does not need
    an album lookup plus an album-tracks lookup for every line.
    """

    ordered_ids = []
    seen_ids = set()

    for line in lines:
        if extract_spotify_playlist_id(line) is not None:
            continue

        album_id = extract_spotify_album_id(line)
        if not album_id:
            continue

        if album_id in seen_ids or f"album_id::{album_id}" in cache:
            continue

        ordered_ids.append(album_id)
        seen_ids.add(album_id)

    if not ordered_ids:
        return

    loaded = 0

    for start in range(0, len(ordered_ids), 20):
        batch_ids = ordered_ids[start:start + 20]

        try:
            response = sp.albums(batch_ids)
        except Exception as error:
            print(f"WARNING: Could not batch-load album metadata for {len(batch_ids)} albums: {error}")
            continue

        for album in response.get("albums", []) or []:
            if not isinstance(album, dict):
                continue
            cache_album(cache, None, album)
            loaded += 1

        save_cache(cache)

        # Avoid sending large bursts if the user uploads a very large file.
        time.sleep(0.05)

    if loaded:
        print(f"Preloaded {loaded} Spotify album links using batched album requests.")


def get_album_tracks_cached(sp: spotipy.Spotify, album: dict, cache: dict) -> list[dict]:
    album_id = album["id"]
    cache_key = f"album_tracks::{album_id}"

    cached = cache.get(cache_key)
    if isinstance(cached, dict) and cached.get("complete") and isinstance(cached.get("tracks"), list):
        tracks = enrich_tracks_with_album_context(cached["tracks"], album)
        cache[cache_key] = {"complete": True, "tracks": tracks}
        save_cache(cache)
        return tracks

    if album.get("tracks_complete") and album.get("tracks_first_page"):
        tracks = enrich_tracks_with_album_context(album["tracks_first_page"], album)
        cache[cache_key] = {"complete": True, "tracks": tracks}
        save_cache(cache)
        return tracks

    tracks = []
    offset = 0
    limit = 50

    while True:
        page = sp.album_tracks(album_id, limit=limit, offset=offset)
        tracks.extend(
            simplify_track(track, album_context=album)
            for track in page.get("items", [])
            if isinstance(track, dict)
        )

        if page.get("next") is None:
            break

        offset += limit

    tracks = enrich_tracks_with_album_context(tracks, album)
    cache[cache_key] = {"complete": True, "tracks": tracks}
    save_cache(cache)

    return tracks


def get_playlist_bundle_cached(sp: spotipy.Spotify, playlist_id: str, cache: dict) -> dict:
    cache_key = f"playlist::{playlist_id}"
    cached = cache.get(cache_key)

    # Prefer zero extra API calls once a playlist has already been hydrated.
    # If the playlist changes, delete album_cache.json to refresh this cache.
    if isinstance(cached, dict) and isinstance(cached.get("items"), list):
        return cached

    playlist = sp.playlist(
        playlist_id,
        fields="id,name,owner(display_name),external_urls,images,snapshot_id,tracks(total)",
    )

    public_items_inaccessible = False

    try:
        playlist_items = get_all_playlist_items(sp, playlist_id)
    except Exception as error:
        if not spotify_error_is_forbidden(error):
            raise

        total = ((playlist.get("tracks") or {}).get("total") or 0)
        if not total:
            raise RuntimeError(
                "Spotify returned 403 for this playlist's items and did not "
                "return a playlist track count, so this public playlist cannot "
                "be sampled through the Web API."
            ) from error

        playlist_items = make_public_playlist_placeholder_items(total)
        public_items_inaccessible = True
        print(
            "WARNING: Spotify returned 403 for this public playlist's items. "
            "Using playlist-context playback by offset and discovering track "
            "metadata after each item starts."
        )

    bundle = {
        "id": playlist_id,
        "name": playlist.get("name", "Unknown playlist"),
        "owner_name": playlist.get("owner", {}).get("display_name", "Unknown owner"),
        "external_url": (playlist.get("external_urls") or {}).get("spotify"),
        "images": playlist.get("images") or [],
        "cover_url": best_image_url(playlist.get("images") or []),
        "snapshot_id": playlist.get("snapshot_id"),
        "items": playlist_items,
        "public_items_inaccessible": public_items_inaccessible,
    }

    cache[cache_key] = bundle
    save_cache(cache)

    return bundle


def prepared_cover_url(prepared: dict) -> str | None:
    track = prepared.get("track") or {}
    album = track.get("album") if isinstance(track.get("album"), dict) else {}

    album_images = album.get("images")
    album_cover = album.get("cover_url") or best_image_url(album_images)

    return (
        album_cover
        or prepared.get("cover_url")
        or best_image_url(prepared.get("images"))
    )


def save_sampler_state(prepared: dict, position_ms: int) -> None:
    track = prepared.get("track") or {}
    track_name = format_track_name(track)
    artist_name = format_track_artist(track)
    album = track.get("album") if isinstance(track.get("album"), dict) else {}

    state = {
        "timestamp": time.time(),
        "coverArt": {
            "url": prepared_cover_url(prepared),
            "width": 300,
            "height": 300,
            "source": "sampler_state",
            "track": track_name,
            "artist": artist_name,
            "album": album.get("name") or prepared.get("album_name"),
            "positionMs": position_ms,
        },
    }

    path = Path(STATE_FILE)
    temp_path = Path(f"{STATE_FILE}.tmp")

    try:
        temp_path.write_text(json.dumps(state, indent=2, ensure_ascii=False), encoding="utf-8")
        temp_path.replace(path)
    except OSError:
        pass



def extract_spotify_album_id(text: str) -> str | None:
    url_match = re.search(r"open\.spotify\.com/album/([A-Za-z0-9]+)", text)
    if url_match:
        return url_match.group(1)

    uri_match = re.search(r"spotify:album:([A-Za-z0-9]+)", text)
    if uri_match:
        return uri_match.group(1)

    if re.fullmatch(r"[A-Za-z0-9]{20,24}", text):
        return text

    return None


def extract_spotify_playlist_id(text: str) -> str | None:
    url_match = re.search(r"open\.spotify\.com/playlist/([A-Za-z0-9]+)", text)
    if url_match:
        return url_match.group(1)

    uri_match = re.search(r"spotify:playlist:([A-Za-z0-9]+)", text)
    if uri_match:
        return uri_match.group(1)

    return None


def search_album(sp: spotipy.Spotify, album_line: str) -> dict:
    album_id = extract_spotify_album_id(album_line)
    if album_id:
        return sp.album(album_id)

    if " - " in album_line:
        album_name, artist_name = album_line.split(" - ", 1)
        query = f'album:"{album_name.strip()}" artist:"{artist_name.strip()}"'
    else:
        query = album_line

    results = sp.search(q=query, type="album", limit=5)
    items = results.get("albums", {}).get("items", [])

    if not items:
        raise RuntimeError(f"No Spotify album match found for: {album_line}")

    return sp.album(items[0]["id"])


def resolve_album(sp: spotipy.Spotify, album_line: str, cache: dict) -> dict:
    album_id = extract_spotify_album_id(album_line)
    cache_key = f"album::{album_line}"

    if album_id:
        album_id_key = f"album_id::{album_id}"
        cached = cache.get(album_id_key) or cache.get(cache_key)

        if album_cache_entry_is_hydrated(cached):
            cache[cache_key] = cached
            return cached

        return hydrate_album_cache_entry(
            sp=sp,
            album_id=album_id,
            album_line=album_line,
            cache=cache,
            fallback=cached if isinstance(cached, dict) else None,
        )

    cached = cache.get(cache_key)
    if album_cache_entry_is_hydrated(cached):
        return cached

    if isinstance(cached, dict) and cached.get("id"):
        return hydrate_album_cache_entry(
            sp=sp,
            album_id=cached["id"],
            album_line=album_line,
            cache=cache,
            fallback=cached,
        )

    album = search_album(sp, album_line)
    simplified = cache_album(cache, album_line, album)
    save_cache(cache)

    return simplified


def get_all_album_tracks(sp: spotipy.Spotify, album_id: str) -> list[dict]:
    """
    Backward-compatible fallback. New playback code should use
    get_album_tracks_cached() so tracks are not refetched every run.
    """

    tracks = []
    offset = 0
    limit = 50

    while True:
        page = sp.album_tracks(album_id, limit=limit, offset=offset)
        tracks.extend(page.get("items", []))

        if page.get("next") is None:
            break

        offset += limit

    return tracks


def get_playlist_entry_content(entry: dict) -> dict | None:
    """
    Spotify's current Get Playlist Items response uses entry["item"].

    Older/deprecated responses used entry["track"]. Keep both so the script works
    across API response variants.
    """

    content = entry.get("item")
    if isinstance(content, dict):
        return content

    old_track = entry.get("track")
    if isinstance(old_track, dict):
        return old_track

    return None


def is_local_track(entry: dict, content: dict | None) -> bool:
    uri = ""

    if isinstance(content, dict):
        uri = content.get("uri") or ""

    return bool(
        entry.get("is_local")
        or (isinstance(content, dict) and content.get("is_local"))
        or uri.startswith("spotify:local:")
    )


def parse_local_uri_parts(uri: str | None) -> dict:
    """
    Local file URI format, when Spotify exposes it:

    spotify:local:{artist}:{album_title}:{track_title}:{duration_in_seconds}
    """

    empty = {
        "artist": None,
        "album": None,
        "track": None,
        "duration_ms": None,
    }

    if not uri or not uri.startswith("spotify:local:"):
        return empty

    parts = uri.split(":")
    if len(parts) < 6:
        return empty

    duration_ms = None
    try:
        duration_seconds = int(parts[-1])
        if duration_seconds > 0:
            duration_ms = duration_seconds * 1000
    except ValueError:
        pass

    return {
        "artist": unquote_plus(parts[2]) or None,
        "album": unquote_plus(parts[3]) or None,
        "track": unquote_plus(parts[4]) or None,
        "duration_ms": duration_ms,
    }


def get_track_duration_ms(track: dict | None) -> int | None:
    if not isinstance(track, dict):
        return None

    duration_ms = track.get("duration_ms")

    if isinstance(duration_ms, int) and duration_ms > 0:
        return duration_ms

    local_parts = parse_local_uri_parts(track.get("uri"))
    return local_parts["duration_ms"]


def normalize_track_uri(track: dict | None) -> str | None:
    if not isinstance(track, dict):
        return None

    uri = track.get("uri")
    if uri:
        return uri

    track_id = track.get("id")
    if track_id:
        return f"spotify:track:{track_id}"

    return None


def make_placeholder_local_track(playlist_position: int) -> dict:
    """
    Some Spotify API responses expose only entry.is_local=True and no item/track
    object. We can still play the local file by playlist context + zero-based
    playlist position.
    """

    return {
        "id": None,
        "name": f"Local file at playlist position {playlist_position + 1}",
        "uri": None,
        "duration_ms": None,
        "type": "track",
        "is_local": True,
        "artists": [],
        "album": {"name": None},
    }



def make_public_playlist_placeholder_track(playlist_position: int) -> dict:
    """
    Placeholder used when Spotify forbids reading another user's public playlist
    items. Playback can still use playlist context + offset; track metadata is
    discovered after playback starts via current_playback().
    """

    return {
        "id": None,
        "uri": None,
        "name": f"Public playlist item at position {playlist_position + 1}",
        "duration_ms": None,
        "type": "track",
        "is_local": False,
        "artists": [{"name": "Unknown artist"}],
        "album": {
            "name": "Unknown album",
            "release_date": None,
            "release_date_precision": None,
            "images": [],
            "cover_url": None,
        },
    }


def make_public_playlist_placeholder_items(total: int) -> list[dict]:
    total = max(0, int(total or 0))
    return [
        {
            "track": make_public_playlist_placeholder_track(position),
            "playlist_position": position,
            "is_local": False,
            "duration_ms": None,
            "blind_public_playlist": True,
        }
        for position in range(total)
    ]


def spotify_error_is_forbidden(error: Exception) -> bool:
    status = getattr(error, "http_status", None)
    if status == 403:
        return True

    text = str(error).lower()
    return "403" in text and "forbidden" in text


def update_prepared_from_current_playback(
    sp: spotipy.Spotify,
    prepared: dict,
    position_ms: int,
) -> None:
    """
    For public playlists whose items cannot be fetched, discover the actual
    non-local track after playback starts. This is intentionally used only for
    blind public-playlist fallback items.
    """

    if not prepared.get("blind_public_playlist"):
        return

    for _attempt in range(8):
        time.sleep(0.25)

        try:
            playback = sp.current_playback()
        except Exception:
            continue

        if not isinstance(playback, dict):
            continue

        item = playback.get("item")
        if not isinstance(item, dict) or item.get("type") != "track":
            continue

        track = simplify_track(item)
        prepared["track"] = track
        prepared["track_text"] = f"{format_track_name(track)} - {format_track_artist(track)}"
        prepared["is_local"] = False

        album = track.get("album") if isinstance(track.get("album"), dict) else {}
        if album.get("cover_url") or album.get("images"):
            prepared["cover_url"] = album.get("cover_url") or best_image_url(album.get("images"))
        if album.get("name"):
            prepared["album_name"] = album.get("name")
        if album.get("release_date"):
            prepared["release_date"] = album.get("release_date")

        save_sampler_state(prepared, position_ms)
        return



def get_playlist_page(sp: spotipy.Spotify, playlist_id: str, limit: int, offset: int) -> dict:
    """
    Do not use a restrictive fields= filter here.

    Local files can contain null/empty fields. Requesting the default object is
    more reliable while preserving local-file entries and normal catalog tracks.
    """

    return sp.playlist_items(
        playlist_id,
        limit=limit,
        offset=offset,
        additional_types=("track",),
    )


def get_all_playlist_items(sp: spotipy.Spotify, playlist_id: str) -> list[dict]:
    """
    Returns playlist items while preserving the zero-based playlist position.

    Normal Spotify tracks can play by playlist context + offset position.
    Local files should also be played by playlist context + offset position.
    """

    playlist_items = []
    offset = 0
    limit = 100

    while True:
        page = get_playlist_page(sp, playlist_id, limit=limit, offset=offset)
        entries = page.get("items", [])

        for entry_index, entry in enumerate(entries):
            playlist_position = offset + entry_index
            content = get_playlist_entry_content(entry)
            local_file = is_local_track(entry, content)

            if isinstance(content, dict):
                track = content
            elif local_file:
                track = make_placeholder_local_track(playlist_position)
            else:
                continue

            uri = normalize_track_uri(track)
            if uri:
                track["uri"] = uri

            if not uri and not local_file:
                continue

            track_type = track.get("type")

            # Playlist items can include episodes. This sampler only supports tracks.
            if track_type not in (None, "track"):
                continue

            playlist_items.append(
                {
                    "track": track,
                    "playlist_position": playlist_position,
                    "is_local": local_file,
                    "duration_ms": get_track_duration_ms(track),
                    "raw_entry_is_local": entry.get("is_local"),
                    "raw_item_present": isinstance(entry.get("item"), dict),
                    "raw_track_present": isinstance(entry.get("track"), dict),
                    "raw_item_keys": sorted(list(entry.get("item", {}).keys()))
                    if isinstance(entry.get("item"), dict)
                    else [],
                    "raw_track_keys": sorted(list(entry.get("track", {}).keys()))
                    if isinstance(entry.get("track"), dict)
                    else [],
                }
            )

        if page.get("next") is None:
            break

        offset += limit

    return playlist_items


def choose_random_track(tracks: list[dict], clip_seconds: int) -> dict:
    playable_tracks = []

    for track in tracks:
        duration_ms = get_track_duration_ms(track)

        if not track.get("uri"):
            continue

        if duration_ms is None:
            continue

        if duration_ms >= clip_seconds * 1000:
            playable_tracks.append(track)

    if not playable_tracks:
        raise RuntimeError("No playable tracks long enough for the requested clip length.")

    return random.choice(playable_tracks)


def choose_random_playlist_item(playlist_items: list[dict], clip_seconds: int) -> dict:
    playable_items = []

    for item in playlist_items:
        track = item["track"]
        duration_ms = item.get("duration_ms")
        local_file = item.get("is_local", False)
        blind_public_playlist = bool(item.get("blind_public_playlist"))

        if blind_public_playlist:
            playable_items.append(item)
            continue

        if not track.get("uri") and not local_file:
            continue

        # If duration is missing, allow it. For random-start, assumed duration is
        # used later. This is required for local files where Spotify returns no
        # item/track object.
        if duration_ms is None:
            playable_items.append(item)
            continue

        if duration_ms >= clip_seconds * 1000:
            playable_items.append(item)

    if not playable_items:
        raise RuntimeError(
            "No usable playlist items were returned after parsing. "
            "Run with --debug-playlist --debug-playlist-raw and send the output."
        )

    return random.choice(playable_items)


def get_device_id(sp: spotipy.Spotify, preferred_device_name: str | None = None) -> str:
    devices_response = sp.devices()
    devices = devices_response.get("devices", [])

    if not devices:
        raise RuntimeError(
            "No Spotify devices found. Open Spotify on your computer/phone/browser, "
            "start any song briefly, then run the script again."
        )

    if preferred_device_name:
        for device in devices:
            if preferred_device_name.lower() in device["name"].lower():
                sp.transfer_playback(device_id=device["id"], force_play=True)
                time.sleep(1)
                return device["id"]

        available = ", ".join(device["name"] for device in devices)
        raise RuntimeError(
            f'Device "{preferred_device_name}" not found. Available devices: {available}'
        )

    for device in devices:
        if device.get("is_active"):
            return device["id"]

    first_device = devices[0]
    sp.transfer_playback(device_id=first_device["id"], force_play=True)
    time.sleep(1)
    return first_device["id"]


def assumed_duration_ms(
    actual_duration_ms: int | None,
    assumed_duration_seconds: int,
) -> int | None:
    if actual_duration_ms is not None:
        return actual_duration_ms

    if assumed_duration_seconds <= 0:
        return None

    return assumed_duration_seconds * 1000


def calculate_position_ms(
    duration_ms: int | None,
    clip_seconds: int,
    random_start: bool,
) -> int:
    if not random_start:
        return 0

    if duration_ms is None:
        return 0

    max_start_ms = max(0, duration_ms - (clip_seconds * 1000) - 3000)
    return random.randint(0, max_start_ms) if max_start_ms > 0 else 0


def sleep_then_pause(sp: spotipy.Spotify, device_id: str, clip_seconds: int) -> None:
    """
    Waits for the requested clip length but does NOT pause playback.

    This avoids a silent gap between clips. The next call to start_playback()
    interrupts the currently playing song. The script pauses only after the last
    album/playlist line has finished, or when the user presses Ctrl+C.
    """

    time.sleep(clip_seconds)


def play_track_uri_clip(
    sp: spotipy.Spotify,
    device_id: str,
    track: dict,
    clip_seconds: int,
    random_start: bool,
    assumed_duration_seconds: int,
) -> int:
    duration_ms = assumed_duration_ms(
        actual_duration_ms=get_track_duration_ms(track),
        assumed_duration_seconds=assumed_duration_seconds,
    )

    position_ms = calculate_position_ms(
        duration_ms=duration_ms,
        clip_seconds=clip_seconds,
        random_start=random_start,
    )

    sp.start_playback(
        device_id=device_id,
        uris=[track["uri"]],
        position_ms=position_ms,
    )

    sleep_then_pause(sp, device_id, clip_seconds)

    return position_ms


def play_playlist_context_clip(
    sp: spotipy.Spotify,
    device_id: str,
    playlist_id: str,
    playlist_position: int,
    track: dict,
    clip_seconds: int,
    random_start: bool,
    assumed_duration_seconds: int,
    local_seek_delay_seconds: float,
) -> int:
    """
    Plays a playlist item by playlist context and zero-based offset position.

    For local files with no item/track object, Spotify may ignore position_ms
    during start_playback. This function starts the playlist item, waits briefly,
    then uses seek_track() to jump to the randomized position.
    """

    is_local = bool(track.get("is_local")) or str(track.get("uri") or "").startswith("spotify:local:")

    duration_ms = assumed_duration_ms(
        actual_duration_ms=get_track_duration_ms(track),
        assumed_duration_seconds=assumed_duration_seconds,
    )

    position_ms = calculate_position_ms(
        duration_ms=duration_ms,
        clip_seconds=clip_seconds,
        random_start=random_start,
    )

    # Use playlist context for every playlist item. For local files, start at 0
    # first and seek after the client has loaded the file.
    start_position_ms = 0 if is_local else position_ms

    sp.start_playback(
        device_id=device_id,
        context_uri=f"spotify:playlist:{playlist_id}",
        offset={"position": playlist_position},
        position_ms=start_position_ms,
    )

    if is_local and position_ms > 0:
        time.sleep(local_seek_delay_seconds)

        try:
            sp.seek_track(position_ms=position_ms, device_id=device_id)
        except Exception as error:
            print(
                "WARNING: Spotify started the local file but rejected the seek request. "
                f"Falling back to 0:00 for this item. Error: {error}"
            )
            position_ms = 0

    sleep_then_pause(sp, device_id, clip_seconds)

    return position_ms


def format_track_artist(track: dict) -> str:
    artists = track.get("artists", [])

    if not artists:
        local_parts = parse_local_uri_parts(track.get("uri"))
        return local_parts["artist"] or "Unknown artist"

    artist_names = [
        artist.get("name", "Unknown artist")
        for artist in artists
        if artist.get("name")
    ]

    if not artist_names:
        return "Unknown artist"

    return ", ".join(artist_names)


def format_track_name(track: dict) -> str:
    name = track.get("name")
    if name:
        return name

    local_parts = parse_local_uri_parts(track.get("uri"))
    return local_parts["track"] or "Unknown track"


def debug_print_playlist_items(playlist_items: list[dict], max_items: int = 25) -> None:
    print("\nDEBUG: Usable playlist items after parsing:")

    if not playlist_items:
        print("  No usable playlist items after parsing.")
        print()

    for item in playlist_items[:max_items]:
        track = item["track"]
        duration_ms = item.get("duration_ms")
        duration_text = "unknown" if duration_ms is None else f"{duration_ms // 1000}s"

        print(
            f"  Position {item['playlist_position']}: "
            f"name={format_track_name(track)!r}, "
            f"artist={format_track_artist(track)!r}, "
            f"uri={track.get('uri')!r}, "
            f"type={track.get('type')!r}, "
            f"is_local={item.get('is_local')}, "
            f"raw_entry_is_local={item.get('raw_entry_is_local')}, "
            f"raw_item_present={item.get('raw_item_present')}, "
            f"raw_track_present={item.get('raw_track_present')}, "
            f"raw_item_keys={item.get('raw_item_keys')}, "
            f"raw_track_keys={item.get('raw_track_keys')}, "
            f"duration={duration_text}"
        )

    if len(playlist_items) > max_items:
        print(f"  ... {len(playlist_items) - max_items} more items not shown")

    print()


def debug_print_raw_playlist(
    sp: spotipy.Spotify,
    playlist_id: str,
    max_items: int = 10,
) -> None:
    print("\nDEBUG RAW: First raw playlist items returned by Spotify API:")

    page = get_playlist_page(sp, playlist_id, limit=max_items, offset=0)
    entries = page.get("items", [])

    print(f"  page.total={page.get('total')}")
    print(f"  page.items_returned={len(entries)}")
    print(f"  page.next={page.get('next')!r}")

    for index, entry in enumerate(entries):
        current_item = entry.get("item")
        old_track = entry.get("track")

        print(f"\n  Raw playlist entry {index}:")
        print(f"    entry.is_local={entry.get('is_local')!r}")
        print(f"    entry.keys={sorted(list(entry.keys()))}")

        if isinstance(current_item, dict):
            print("    item_present=True")
            print(f"    item.keys={sorted(list(current_item.keys()))}")
            print(f"    item.name={current_item.get('name')!r}")
            print(f"    item.id={current_item.get('id')!r}")
            print(f"    item.uri={current_item.get('uri')!r}")
            print(f"    item.type={current_item.get('type')!r}")
            print(f"    item.is_local={current_item.get('is_local')!r}")
            print(f"    item.duration_ms={current_item.get('duration_ms')!r}")
        else:
            print("    item_present=False")
            print(f"    item={current_item!r}")

        if isinstance(old_track, dict):
            print("    deprecated_track_present=True")
            print(f"    deprecated_track.name={old_track.get('name')!r}")
            print(f"    deprecated_track.uri={old_track.get('uri')!r}")
            print(f"    deprecated_track.type={old_track.get('type')!r}")
            print(f"    deprecated_track.is_local={old_track.get('is_local')!r}")
            print(f"    deprecated_track.duration_ms={old_track.get('duration_ms')!r}")
        else:
            print("    deprecated_track_present=False")
            print(f"    deprecated_track={old_track!r}")

    print()


def process_playlist_line(
    sp: spotipy.Spotify,
    device_id: str,
    line: str,
    clip_seconds: int,
    random_start: bool,
    debug_playlist: bool,
    debug_playlist_raw: bool,
    assumed_duration_seconds: int,
    local_seek_delay_seconds: float,
) -> tuple[str, str, int]:
    playlist_id = extract_spotify_playlist_id(line)

    if not playlist_id:
        raise RuntimeError("Invalid playlist link or URI.")

    if debug_playlist_raw:
        debug_print_raw_playlist(sp, playlist_id)

    playlist_bundle = get_playlist_bundle_cached(sp, playlist_id, cache={})
    playlist_items = playlist_bundle["items"]

    if debug_playlist:
        debug_print_playlist_items(playlist_items)

    chosen_item = choose_random_playlist_item(playlist_items, clip_seconds)

    track = chosen_item["track"]
    playlist_position = chosen_item["playlist_position"]
    is_local = chosen_item["is_local"]

    position_ms = play_playlist_context_clip(
        sp=sp,
        device_id=device_id,
        playlist_id=playlist_id,
        playlist_position=playlist_position,
        track=track,
        clip_seconds=clip_seconds,
        random_start=random_start,
        assumed_duration_seconds=assumed_duration_seconds,
        local_seek_delay_seconds=local_seek_delay_seconds,
    )

    playlist_name = playlist_bundle.get("name", "Unknown playlist")
    owner_name = playlist_bundle.get("owner_name", "Unknown owner")
    track_artist = format_track_artist(track)
    position_seconds = position_ms // 1000

    source_text = f"Playlist: {playlist_name} - {owner_name}"

    if is_local:
        track_text = f"{format_track_name(track)} - {track_artist} [local file]"
    else:
        track_text = f"{format_track_name(track)} - {track_artist}"

    return source_text, track_text, position_seconds


def process_album_line(
    sp: spotipy.Spotify,
    device_id: str,
    line: str,
    cache: dict,
    clip_seconds: int,
    random_start: bool,
    assumed_duration_seconds: int,
) -> tuple[str, str, int]:
    album = resolve_album(sp, line, cache)
    tracks = get_album_tracks_cached(sp, album, cache)
    track = choose_random_track(tracks, clip_seconds)

    position_ms = play_track_uri_clip(
        sp=sp,
        device_id=device_id,
        track=track,
        clip_seconds=clip_seconds,
        random_start=random_start,
        assumed_duration_seconds=assumed_duration_seconds,
    )

    album_artist = ", ".join(album["artists"])
    track_artist = format_track_artist(track)
    position_seconds = position_ms // 1000

    source_text = f"Album: {album['name']} - {album_artist}"
    track_text = f"{format_track_name(track)} - {track_artist}"

    return source_text, track_text, position_seconds



def prepare_album_clip(
    sp: spotipy.Spotify,
    line: str,
    cache: dict,
    clip_seconds: int,
    random_start: bool,
    assumed_duration_seconds: int,
) -> dict:
    """
    Resolves one album line and chooses the random track before playback starts.

    This is intentionally separated from playback so the next album can be
    prepared in the background while the current clip is still audible.
    """

    album = resolve_album(sp, line, cache)
    tracks = get_album_tracks_cached(sp, album, cache)
    track = choose_random_track(tracks, clip_seconds)

    duration_ms = assumed_duration_ms(
        actual_duration_ms=get_track_duration_ms(track),
        assumed_duration_seconds=assumed_duration_seconds,
    )

    position_ms = calculate_position_ms(
        duration_ms=duration_ms,
        clip_seconds=clip_seconds,
        random_start=random_start,
    )

    album_artist = ", ".join(album["artists"])
    track_artist = format_track_artist(track)

    return {
        "kind": "track_uri",
        "source_text": f"Album: {album['name']} - {album_artist}",
        "track_text": f"{format_track_name(track)} - {track_artist}",
        "track": track,
        "position_ms": position_ms,
        "clip_seconds": clip_seconds,
        "cover_url": album.get("cover_url"),
        "album_name": album.get("name"),
        "is_local": False,
    }


def prepare_playlist_clip(
    sp: spotipy.Spotify,
    line: str,
    cache: dict,
    clip_seconds: int,
    random_start: bool,
    debug_playlist: bool,
    debug_playlist_raw: bool,
    assumed_duration_seconds: int,
) -> dict:
    """
    Resolves one playlist line and chooses the random playlist item before
    playback starts.

    This lets playlist API calls, playlist parsing, and random selection happen
    while the current clip is still playing.
    """

    playlist_id = extract_spotify_playlist_id(line)

    if not playlist_id:
        raise RuntimeError("Invalid playlist link or URI.")

    if debug_playlist_raw:
        debug_print_raw_playlist(sp, playlist_id)

    playlist_bundle = get_playlist_bundle_cached(sp, playlist_id, cache)
    playlist_items = playlist_bundle["items"]

    if debug_playlist:
        debug_print_playlist_items(playlist_items)

    chosen_item = choose_random_playlist_item(playlist_items, clip_seconds)

    track = chosen_item["track"]
    playlist_position = chosen_item["playlist_position"]
    is_local = chosen_item["is_local"]

    duration_ms = assumed_duration_ms(
        actual_duration_ms=get_track_duration_ms(track),
        assumed_duration_seconds=assumed_duration_seconds,
    )

    position_ms = calculate_position_ms(
        duration_ms=duration_ms,
        clip_seconds=clip_seconds,
        random_start=random_start,
    )

    playlist_name = playlist_bundle.get("name", "Unknown playlist")
    owner_name = playlist_bundle.get("owner_name", "Unknown owner")
    track_artist = format_track_artist(track)

    blind_public_playlist = bool(chosen_item.get("blind_public_playlist"))

    if blind_public_playlist:
        track_text = f"Public playlist position {playlist_position + 1}"
    elif is_local:
        track_text = f"{format_track_name(track)} - {track_artist} [local file]"
    else:
        track_text = f"{format_track_name(track)} - {track_artist}"

    return {
        "kind": "playlist_context",
        "source_text": f"Playlist: {playlist_name} - {owner_name}",
        "track_text": track_text,
        "playlist_id": playlist_id,
        "playlist_position": playlist_position,
        "track": track,
        "position_ms": position_ms,
        "clip_seconds": clip_seconds,
        "cover_url": playlist_bundle.get("cover_url"),
        "album_name": playlist_bundle.get("name"),
        "is_local": is_local,
        "blind_public_playlist": blind_public_playlist,
    }


def prepare_clip(
    sp: spotipy.Spotify,
    line: str,
    cache: dict,
    clip_seconds: int,
    random_start: bool,
    debug_playlist: bool,
    debug_playlist_raw: bool,
    assumed_duration_seconds: int,
) -> dict:
    """
    Prepares the next playable clip without starting playback.
    """

    if extract_spotify_playlist_id(line) is not None:
        return prepare_playlist_clip(
            sp=sp,
            line=line,
            cache=cache,
            clip_seconds=clip_seconds,
            random_start=random_start,
            debug_playlist=debug_playlist,
            debug_playlist_raw=debug_playlist_raw,
            assumed_duration_seconds=assumed_duration_seconds,
        )

    return prepare_album_clip(
        sp=sp,
        line=line,
        cache=cache,
        clip_seconds=clip_seconds,
        random_start=random_start,
        assumed_duration_seconds=assumed_duration_seconds,
    )



def spotify_playback_error_is_stale_device(error: Exception) -> bool:
    """
    Spotify Connect device IDs are session-like. The desktop app can still be
    open while the Web API rejects an older device_id with 404 Not found /
    Device not found.
    """

    status = getattr(error, "http_status", None)
    text = str(error).lower()

    if status == 404:
        return True

    return (
        "me/player/play" in text
        and "404" in text
        and ("not found" in text or "device not found" in text)
    )


def start_playback_with_device_retry(
    sp: spotipy.Spotify,
    device_id: str | None,
    playback_kwargs: dict,
) -> str | None:
    """
    Starts playback and refreshes the Spotify Connect device if Spotify rejects
    the cached device_id.

    The first attempt uses the known device ID. If Spotify returns 404/Device
    not found, it re-queries available devices and retries. If Spotify still
    rejects the explicit ID, it makes one final attempt without a device_id so
    Spotify can use the currently active device.
    """

    attempted_device_ids: set[str | None] = set()
    candidate_device_ids: list[str | None] = [device_id]
    last_error: Exception | None = None

    while candidate_device_ids:
        current_device_id = candidate_device_ids.pop(0)

        if current_device_id in attempted_device_ids:
            continue

        attempted_device_ids.add(current_device_id)

        try:
            sp.start_playback(device_id=current_device_id, **playback_kwargs)
            return current_device_id
        except Exception as error:
            if not spotify_playback_error_is_stale_device(error):
                raise

            last_error = error
            print(
                "WARNING: Spotify rejected the current playback device "
                f"({current_device_id or 'active device'}) as unavailable. "
                "Refreshing Spotify Connect devices and retrying."
            )

            try:
                refreshed_device_id = get_device_id(sp, None)
                if refreshed_device_id not in attempted_device_ids:
                    candidate_device_ids.append(refreshed_device_id)
            except Exception as refresh_error:
                print(f"WARNING: Could not refresh Spotify device list: {refresh_error}")

            # Final fallback: let Spotify target the active player, if one exists.
            if None not in attempted_device_ids:
                candidate_device_ids.append(None)

    if last_error is not None:
        raise last_error

    raise RuntimeError("Spotify playback failed before any playback attempt was made.")



def start_prepared_clip(
    sp: spotipy.Spotify,
    device_id: str,
    prepared: dict,
    local_seek_delay_seconds: float,
) -> int:
    """
    Starts an already prepared clip immediately.

    If Spotify rejects the previously cached Spotify Connect device ID, this
    refreshes the device and retries instead of letting every later clip fail
    with Device not found.
    """

    global ACTIVE_DEVICE_ID_OVERRIDE

    position_ms = int(prepared.get("position_ms") or 0)
    effective_device_id = ACTIVE_DEVICE_ID_OVERRIDE or device_id

    save_sampler_state(prepared, position_ms)

    if prepared["kind"] == "track_uri":
        track = prepared["track"]
        used_device_id = start_playback_with_device_retry(
            sp=sp,
            device_id=effective_device_id,
            playback_kwargs={
                "uris": [track["uri"]],
                "position_ms": position_ms,
            },
        )

        if used_device_id:
            ACTIVE_DEVICE_ID_OVERRIDE = used_device_id

        return position_ms

    if prepared["kind"] == "playlist_context":
        track = prepared["track"]
        is_local = bool(prepared.get("is_local")) or str(track.get("uri") or "").startswith("spotify:local:")

        start_position_ms = 0 if is_local else position_ms

        used_device_id = start_playback_with_device_retry(
            sp=sp,
            device_id=effective_device_id,
            playback_kwargs={
                "context_uri": f"spotify:playlist:{prepared['playlist_id']}",
                "offset": {"position": prepared["playlist_position"]},
                "position_ms": start_position_ms,
            },
        )

        if used_device_id:
            ACTIVE_DEVICE_ID_OVERRIDE = used_device_id

        if prepared.get("blind_public_playlist"):
            update_prepared_from_current_playback(sp, prepared, position_ms)

        if is_local and position_ms > 0:
            time.sleep(local_seek_delay_seconds)

            try:
                sp.seek_track(position_ms=position_ms, device_id=ACTIVE_DEVICE_ID_OVERRIDE or used_device_id or effective_device_id)
            except Exception as error:
                print(
                    "WARNING: Spotify started the local file but rejected the seek request. "
                    f"Falling back to 0:00 for this item. Error: {error}"
                )
                position_ms = 0

        return position_ms

    raise RuntimeError(f"Unknown prepared clip kind: {prepared.get('kind')!r}")


def wait_for_clip_or_stop(clip_seconds: int) -> None:
    """
    Keeps timing simple. The previous clip is not paused; the next call to
    start_playback() interrupts it.
    """

    time.sleep(clip_seconds)




def choose_effective_clip_seconds(args: argparse.Namespace) -> int:
    """
    Returns either the fixed clip length or a random clip length inside the
    user-selected inclusive bounds.
    """

    if args.clip_min_seconds is None and args.clip_max_seconds is None:
        return args.clip_seconds

    if args.clip_min_seconds is None or args.clip_max_seconds is None:
        raise RuntimeError(
            "--clip-min-seconds and --clip-max-seconds must be provided together."
        )

    return random.randint(args.clip_min_seconds, args.clip_max_seconds)


def describe_clip_mode(args: argparse.Namespace) -> str:
    if args.clip_min_seconds is None and args.clip_max_seconds is None:
        return f"Clip length: {args.clip_seconds} seconds"

    return (
        "Clip length: random "
        f"{args.clip_min_seconds}-{args.clip_max_seconds} seconds"
    )



def max_required_clip_seconds(args: argparse.Namespace) -> int:
    if args.clip_max_seconds is not None:
        return args.clip_max_seconds
    return args.clip_seconds


def playlist_item_is_playable(item: dict, required_clip_seconds: int) -> bool:
    track = item.get("track") or {}
    duration_ms = item.get("duration_ms")
    local_file = bool(item.get("is_local", False))

    if item.get("blind_public_playlist"):
        return True

    if not track.get("uri") and not local_file:
        return False

    if duration_ms is None:
        return True

    return duration_ms >= required_clip_seconds * 1000


def playlist_item_dedupe_key(item: dict) -> str:
    if item.get("blind_public_playlist"):
        return f"public_playlist_position::{item.get('playlist_position')}"

    track = item.get("track") or {}
    uri = track.get("uri")

    if uri:
        return f"uri::{uri}"

    name = format_track_name(track).strip().lower()
    artist = format_track_artist(track).strip().lower()
    duration_ms = item.get("duration_ms")

    # For local-file entries where Spotify exposes no track object, the playlist
    # position is the only reliable identity available from the Web API.
    if name.startswith("local file at playlist position"):
        return f"playlist_position::{item.get('playlist_position')}"

    return f"text::{artist}|{name}|{duration_ms}"


def get_unique_playable_playlist_items(
    playlist_items: list[dict],
    required_clip_seconds: int,
) -> list[dict]:
    playable_items = []
    seen_keys = set()

    for item in playlist_items:
        if not playlist_item_is_playable(item, required_clip_seconds):
            continue

        key = playlist_item_dedupe_key(item)
        if key in seen_keys:
            continue

        seen_keys.add(key)
        playable_items.append(item)

    return playable_items


def prepare_playlist_item_clip(
    playlist_bundle: dict,
    item: dict,
    clip_seconds: int,
    random_start: bool,
    assumed_duration_seconds: int,
) -> dict:
    track = item["track"]
    playlist_position = item["playlist_position"]
    is_local = item.get("is_local", False)

    duration_ms = assumed_duration_ms(
        actual_duration_ms=get_track_duration_ms(track),
        assumed_duration_seconds=assumed_duration_seconds,
    )

    position_ms = calculate_position_ms(
        duration_ms=duration_ms,
        clip_seconds=clip_seconds,
        random_start=random_start,
    )

    playlist_name = playlist_bundle.get("name", "Unknown playlist")
    owner_name = playlist_bundle.get("owner_name", "Unknown owner")
    track_artist = format_track_artist(track)
    blind_public_playlist = bool(item.get("blind_public_playlist"))

    if blind_public_playlist:
        track_text = f"Public playlist position {playlist_position + 1}"
    elif is_local:
        track_text = f"{format_track_name(track)} - {track_artist} [local file]"
    else:
        track_text = f"{format_track_name(track)} - {track_artist}"

    return {
        "kind": "playlist_context",
        "source_text": f"Playlist: {playlist_name} - {owner_name}",
        "track_text": track_text,
        "playlist_id": playlist_bundle["id"],
        "playlist_position": playlist_position,
        "track": track,
        "position_ms": position_ms,
        "clip_seconds": clip_seconds,
        "cover_url": playlist_bundle.get("cover_url"),
        "album_name": playlist_bundle.get("name"),
        "is_local": is_local,
        "blind_public_playlist": blind_public_playlist,
    }



def track_dedupe_key(track: dict) -> str:
    uri = track.get("uri")
    if uri:
        return f"uri::{uri}"

    name = format_track_name(track).strip().lower()
    artist = format_track_artist(track).strip().lower()
    duration_ms = get_track_duration_ms(track)

    return f"text::{artist}|{name}|{duration_ms}"


def get_unique_playable_album_tracks(
    tracks: list[dict],
    required_clip_seconds: int,
) -> list[dict]:
    playable_tracks = []
    seen_keys = set()

    for track in tracks:
        duration_ms = get_track_duration_ms(track)

        if not track.get("uri"):
            continue

        if duration_ms is not None and duration_ms < required_clip_seconds * 1000:
            continue

        key = track_dedupe_key(track)
        if key in seen_keys:
            continue

        seen_keys.add(key)
        playable_tracks.append(track)

    return playable_tracks


def prepare_album_track_clip(
    album: dict,
    track: dict,
    clip_seconds: int,
    random_start: bool,
    assumed_duration_seconds: int,
) -> dict:
    duration_ms = assumed_duration_ms(
        actual_duration_ms=get_track_duration_ms(track),
        assumed_duration_seconds=assumed_duration_seconds,
    )

    position_ms = calculate_position_ms(
        duration_ms=duration_ms,
        clip_seconds=clip_seconds,
        random_start=random_start,
    )

    album_artist = ", ".join(album.get("artists") or ["Unknown artist"])
    track_artist = format_track_artist(track)

    return {
        "kind": "track_uri",
        "source_text": f"Album: {album.get('name', 'Unknown album')} - {album_artist}",
        "track_text": f"{format_track_name(track)} - {track_artist}",
        "track": track,
        "position_ms": position_ms,
        "clip_seconds": clip_seconds,
        "cover_url": album.get("cover_url"),
        "album_name": album.get("name"),
        "is_local": False,
    }


def play_prepared_items_no_repeat(
    args: argparse.Namespace,
    sp: spotipy.Spotify,
    device_id: str,
    prepared_items: list[dict],
    completion_label: str,
) -> None:
    stopped_by_user = False

    for index, prepared in enumerate(prepared_items, start=1):
        try:
            position_ms = start_prepared_clip(
                sp=sp,
                device_id=device_id,
                prepared=prepared,
                local_seek_delay_seconds=args.local_seek_delay_seconds,
            )

            position_seconds = position_ms // 1000

            print(
                f"[{index}/{len(prepared_items)}] "
                f"{prepared['source_text']} | "
                f"Track: {prepared['track_text']} | "
                f"Start: {position_seconds}s"
            )

            wait_for_clip_or_stop(int(prepared.get("clip_seconds") or args.clip_seconds))

            if args.delay_seconds > 0:
                time.sleep(args.delay_seconds)

        except KeyboardInterrupt:
            stopped_by_user = True
            print("\nStopped by user.")

            try:
                sp.pause_playback(device_id=device_id)
            except Exception:
                pass

            break

        except Exception as error:
            print(f"[{index}/{len(prepared_items)}] ERROR: {error}")

            if args.delay_seconds > 0:
                time.sleep(args.delay_seconds)

    if not stopped_by_user:
        print(f"{completion_label}: played all {len(prepared_items)} possible songs without repeats.")
        try:
            sp.pause_playback(device_id=device_id)
        except Exception:
            pass


def run_single_album_mode(
    args: argparse.Namespace,
    sp: spotipy.Spotify,
    cache: dict,
    album_link: str,
) -> None:
    album = resolve_album(sp, album_link, cache)
    tracks = get_album_tracks_cached(sp, album, cache)
    required_clip_seconds = max_required_clip_seconds(args)
    playable_tracks = get_unique_playable_album_tracks(
        tracks=tracks,
        required_clip_seconds=required_clip_seconds,
    )

    if not playable_tracks:
        raise RuntimeError(
            "No playable album songs were long enough for the selected clip length."
        )

    if args.single_link_order == "random":
        random.shuffle(playable_tracks)

    device_id = get_device_id(sp, args.device_name)
    album_artist = ", ".join(album.get("artists") or ["Unknown artist"])

    print(f"Loaded album: {album.get('name', 'Unknown album')} - {album_artist}")
    print(f"Usable unique songs: {len(playable_tracks)}")
    print(describe_clip_mode(args))
    print(f"Single-link mode: {'random' if args.single_link_order == 'random' else 'ordered'} no-repeat album playback.")
    print("Press Ctrl+C to stop.\n")

    prepared_items = [
        prepare_album_track_clip(
            album=album,
            track=track,
            clip_seconds=choose_effective_clip_seconds(args),
            random_start=args.random_start,
            assumed_duration_seconds=args.assumed_duration_seconds,
        )
        for track in playable_tracks
    ]

    play_prepared_items_no_repeat(
        args=args,
        sp=sp,
        device_id=device_id,
        prepared_items=prepared_items,
        completion_label="Album complete",
    )


def run_single_link_mode(
    args: argparse.Namespace,
    sp: spotipy.Spotify,
    cache: dict,
) -> None:
    single_link = args.single_link or args.playlist_link or ""

    if extract_spotify_album_id(single_link):
        run_single_album_mode(args=args, sp=sp, cache=cache, album_link=single_link)
        return

    if extract_spotify_playlist_id(single_link):
        run_single_playlist_mode(args=args, sp=sp, cache=cache)
        return

    raise RuntimeError("Invalid Spotify album or playlist link/URI.")


def run_single_playlist_mode(
    args: argparse.Namespace,
    sp: spotipy.Spotify,
    cache: dict,
) -> None:
    playlist_id = extract_spotify_playlist_id(args.single_link or args.playlist_link or "")

    if not playlist_id:
        raise RuntimeError("Invalid Spotify playlist link or URI.")

    if args.debug_playlist_raw:
        debug_print_raw_playlist(sp, playlist_id)

    playlist_bundle = get_playlist_bundle_cached(sp, playlist_id, cache)
    playlist_items = playlist_bundle["items"]

    if args.debug_playlist:
        debug_print_playlist_items(playlist_items)

    required_clip_seconds = max_required_clip_seconds(args)
    playable_items = get_unique_playable_playlist_items(
        playlist_items=playlist_items,
        required_clip_seconds=required_clip_seconds,
    )

    if not playable_items:
        raise RuntimeError(
            "No playable playlist songs were long enough for the selected clip length."
        )

    if args.single_link_order == "random":
        random.shuffle(playable_items)

    device_id = get_device_id(sp, args.device_name)

    playlist_name = playlist_bundle.get("name", "Unknown playlist")
    owner_name = playlist_bundle.get("owner_name", "Unknown owner")

    print(f"Loaded playlist: {playlist_name} - {owner_name}")
    print(f"Usable unique songs: {len(playable_items)}")
    print(describe_clip_mode(args))
    print(f"Playlist mode: {'random' if args.single_link_order == 'random' else 'ordered'} no-repeat playback.")
    print("Press Ctrl+C to stop.\n")

    prepared_items = [
        prepare_playlist_item_clip(
            playlist_bundle=playlist_bundle,
            item=item,
            clip_seconds=choose_effective_clip_seconds(args),
            random_start=args.random_start,
            assumed_duration_seconds=args.assumed_duration_seconds,
        )
        for item in playable_items
    ]

    play_prepared_items_no_repeat(
        args=args,
        sp=sp,
        device_id=device_id,
        prepared_items=prepared_items,
        completion_label="Playlist complete",
    )


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Play a short random track sample from each album or playlist "
            "listed in albums.txt."
        )
    )

    parser.add_argument(
        "--spotify-token-cache",
        type=str,
        default=".spotify_token_cache",
        help=(
            "Spotipy token cache path. The hosted Flask backend passes a "
            "temporary cache file here so sampler.py does not try to open a browser."
        ),
    )

    parser.add_argument(
        "--albums-file",
        type=str,
        default=ALBUMS_FILE,
        help=(
            "Path to the album/playlist list file. Default: albums.txt. "
            "Blank lines and lines starting with # are ignored."
        ),
    )

    parser.add_argument(
        "--playlist-link",
        type=str,
        default=None,
        help=(
            "Backward-compatible alias for --single-link when the link is a "
            "Spotify playlist."
        ),
    )

    parser.add_argument(
        "--single-link",
        type=str,
        default=None,
        help=(
            "Play one Spotify album or playlist in no-repeat mode. "
            "The sampler plays each usable item once, then stops."
        ),
    )

    parser.add_argument(
        "--single-link-order",
        choices=["random", "ordered"],
        default="random",
        help=(
            "Song order for --single-link / --playlist-link. "
            "Use random for randomized no-repeat playback, or ordered to follow "
            "the album/playlist order. Default: random."
        ),
    )

    parser.add_argument(
        "--clip-seconds",
        type=int,
        default=15,
        help=(
            "Fixed number of seconds to play from each album or playlist. "
            "Default: 15. Ignored when --clip-min-seconds and "
            "--clip-max-seconds are provided."
        ),
    )

    parser.add_argument(
        "--clip-min-seconds",
        type=int,
        default=None,
        help=(
            "Minimum clip length, seconds, for random clip-length mode. "
            "Must be used with --clip-max-seconds."
        ),
    )

    parser.add_argument(
        "--clip-max-seconds",
        type=int,
        default=None,
        help=(
            "Maximum clip length, seconds, for random clip-length mode. "
            "Must be used with --clip-min-seconds."
        ),
    )

    parser.add_argument(
        "--delay-seconds",
        type=float,
        default=0.0,
        help=(
            "Optional extra delay before moving to the next album/playlist. "
            "Default: 0. Use 0 for the fastest transition."
        ),
    )

    parser.add_argument(
        "--shuffle-albums",
        action="store_true",
        help="Shuffle the line order before playing.",
    )

    parser.add_argument(
        "--start-index",
        type=int,
        default=1,
        help=(
            "1-based index of the usable line in albums.txt to start from. "
            "Blank lines and lines starting with # are ignored. Default: 1."
        ),
    )

    parser.add_argument(
        "--random-start",
        action="store_true",
        help="Start at a random point in the chosen track instead of 0:00.",
    )

    parser.add_argument(
        "--device-name",
        type=str,
        default=None,
        help='Optional Spotify device name, for example "DESKTOP" or "iPhone".',
    )

    parser.add_argument(
        "--debug-playlist",
        action="store_true",
        help="Print parsed playlist item data.",
    )

    parser.add_argument(
        "--debug-playlist-raw",
        action="store_true",
        help="Print the raw first page of playlist item data returned by Spotify.",
    )

    parser.add_argument(
        "--assumed-duration-seconds",
        type=int,
        default=180,
        help=(
            "Assumed duration when Spotify's Web API returns no duration. "
            "Used only for random-start. Default: 180."
        ),
    )

    parser.add_argument(
        "--preload-albums",
        action="store_true",
        help=(
            "Optional: batch-preload direct Spotify album links. Disabled by "
            "default because some Spotify apps/accounts receive 403 Forbidden "
            "from the batched albums endpoint."
        ),
    )

    parser.add_argument(
        "--local-seek-delay-seconds",
        type=float,
        default=0.0,
        help=(
            "For local files, wait this long after starting the playlist item "
            "before sending seek_track(). Increase only if seek happens too early. "
            "Default: 0.0."
        ),
    )

    args = parser.parse_args()

    if args.clip_seconds <= 0:
        raise RuntimeError("--clip-seconds must be greater than 0.")

    if args.clip_min_seconds is not None and args.clip_min_seconds <= 0:
        raise RuntimeError("--clip-min-seconds must be greater than 0.")

    if args.clip_max_seconds is not None and args.clip_max_seconds <= 0:
        raise RuntimeError("--clip-max-seconds must be greater than 0.")

    if (args.clip_min_seconds is None) != (args.clip_max_seconds is None):
        raise RuntimeError(
            "--clip-min-seconds and --clip-max-seconds must be provided together."
        )

    if (
        args.clip_min_seconds is not None
        and args.clip_max_seconds is not None
        and args.clip_min_seconds > args.clip_max_seconds
    ):
        raise RuntimeError("--clip-min-seconds cannot be greater than --clip-max-seconds.")

    if args.delay_seconds < 0:
        raise RuntimeError("--delay-seconds cannot be negative.")

    if args.start_index < 1:
        raise RuntimeError("--start-index must be 1 or greater.")

    if args.assumed_duration_seconds < 0:
        raise RuntimeError("--assumed-duration-seconds cannot be negative.")

    if args.local_seek_delay_seconds < 0:
        raise RuntimeError("--local-seek-delay-seconds cannot be negative.")

    sp = load_spotify_client(
        token_cache_path=args.spotify_token_cache,
        open_browser=args.spotify_token_cache == ".spotify_token_cache",
    )
    cache = load_cache()

    if args.single_link or args.playlist_link:
        run_single_link_mode(args=args, sp=sp, cache=cache)
        return

    all_lines = load_album_lines(args.albums_file)

    if args.start_index > len(all_lines):
        raise RuntimeError(
            f"--start-index {args.start_index} is beyond the number of usable "
            f"album/playlist lines in {args.albums_file}: {len(all_lines)}."
        )

    start_offset = args.start_index - 1
    lines = all_lines[start_offset:]

    if args.shuffle_albums:
        random.shuffle(lines)

    if args.preload_albums:
        preload_album_cache(sp, lines, cache)

    device_id = get_device_id(sp, args.device_name)

    print(f"Loaded {len(all_lines)} total album/playlist lines.")
    print(f"Starting at usable line index: {args.start_index}")
    print(f"Remaining lines to process: {len(lines)}")
    print(describe_clip_mode(args))
    print("Transition mode: prefetch next item while current clip plays.")
    print("Press Ctrl+C to stop.\n")

    stopped_by_user = False

    def submit_prepare(executor: ThreadPoolExecutor, line: str, clip_seconds: int) -> Future:
        return executor.submit(
            prepare_clip,
            sp,
            line,
            cache,
            clip_seconds,
            args.random_start,
            args.debug_playlist,
            args.debug_playlist_raw,
            args.assumed_duration_seconds,
        )

    with ThreadPoolExecutor(max_workers=1) as executor:
        prepared_future: Future | None = (
            submit_prepare(executor, lines[0], choose_effective_clip_seconds(args))
            if lines
            else None
        )

        for index, line in enumerate(lines, start=1):
            next_future: Future | None = None

            try:
                if prepared_future is None:
                    break

                prepared = prepared_future.result()

                position_ms = start_prepared_clip(
                    sp=sp,
                    device_id=device_id,
                    prepared=prepared,
                    local_seek_delay_seconds=args.local_seek_delay_seconds,
                )

                if index < len(lines):
                    next_future = submit_prepare(
                        executor,
                        lines[index],
                        choose_effective_clip_seconds(args),
                    )

                original_index = start_offset + index
                position_seconds = position_ms // 1000

                print(
                    f"[{original_index}/{len(all_lines)}] "
                    f"{prepared['source_text']} | "
                    f"Track: {prepared['track_text']} | "
                    f"Start: {position_seconds}s"
                )

                wait_for_clip_or_stop(int(prepared.get("clip_seconds") or args.clip_seconds))

                if args.delay_seconds > 0:
                    time.sleep(args.delay_seconds)

                prepared_future = next_future

            except KeyboardInterrupt:
                stopped_by_user = True
                print("\nStopped by user.")

                try:
                    sp.pause_playback(device_id=device_id)
                except Exception:
                    pass

                break

            except Exception as error:
                original_index = start_offset + index
                print(f"[{original_index}/{len(all_lines)}] ERROR for '{line}': {error}")

                if index < len(lines):
                    prepared_future = submit_prepare(
                        executor,
                        lines[index],
                        choose_effective_clip_seconds(args),
                    )
                else:
                    prepared_future = None

                if args.delay_seconds > 0:
                    time.sleep(args.delay_seconds)

    if not stopped_by_user:
        try:
            sp.pause_playback(device_id=device_id)
        except Exception:
            pass


if __name__ == "__main__":
    main()
