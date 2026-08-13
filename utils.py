#!/usr/bin/env python3
"""
utils.py

Shared infrastructure used across unprotbot.py, check_unprotected.py, and
publish_to_wiki.py: the MediaWiki API session/retry logic (GET and POST
alike), JSON disk caching, CSV reading/schema validation, the
indefinite-semi/ECP-protected page list fetch, and the small set of
filenames/formats/config values (DATA_DIR, AUDIT_CSV_FILE, contact-string
User-Agent, previous-protections date format, OLD_PROT_CUTOFF_YEARS) that
more than one script needs to agree on.
"""

import argparse
import csv
import json
import os
import re
import sys
import time
from datetime import datetime, timedelta, timezone
from typing import Any, Callable, Dict, List, Optional, Set, Tuple

import requests

JSONDict = Dict[str, Any]

WIKI_HOST = "https://en.wikipedia.org"
API_URL = f"{WIKI_HOST}/w/api.php"

SLEEP_BETWEEN_REQUESTS = 0.15

# How many years ago is "old enough" to consider for unprotection.
OLD_PROT_CUTOFF_YEARS = 7

# Shared between unprotbot.py (permanent pre-filter cache -- see
# too_many_protections_cache) and publish_to_wiki.py (drops these rows from
# the main "kept" table) so the two thresholds can't drift apart.
MAX_PROTECTION_COUNT = 4

DATA_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data")
os.makedirs(DATA_DIR, exist_ok=True)

PROTECTED_PAGES_CACHE_FILE = os.path.join(DATA_DIR, "protected_pages_cache.json")
AUDIT_CSV_FILE = os.path.join(DATA_DIR, "audit.csv")
UNPROTECTED_CSV_FILE = os.path.join(DATA_DIR, "unprotected.csv")

# The exact date pattern used at the start of one "previous protections"
# history line, e.g. "2019-05-17 by JBW: ...". unprotbot.py's
# format_previous_protections is the only writer (via format_prev_prot_entry
# below); publish_to_wiki.py's PREV_PROT_LINE_RE/PREV_PROT_SPLIT_RE are the
# only readers. Sharing the pattern means a format change on the writing
# side can't silently stop matching on the parsing side.
PREV_PROT_DATE_PATTERN = r"\d{4}-\d{2}-\d{2}"

SESSION = requests.Session()
SESSION.headers.update({"User-Agent": "ProtectionAuditBot/1.0"})


def set_contact(contact: str) -> None:
    """Sets SESSION's User-Agent per Wikimedia's UA policy -- called once by each script's main()."""
    SESSION.headers["User-Agent"] = f"ProtectionAuditBot/1.0 (contact: {contact})"


def format_prev_prot_entry(date: str, admin: str, comment: str) -> str:
    return f"{date} by {admin}: {comment}"


# Placeholder admin values written when no real username is known:
# "(unknown)" (resolve_original_protection, an unresolvable log trace) and
# "?" (format_previous_protections, e.get("user", "?") on a malformed entry).
# Checked in unprotbot.py (is_admin_active, is_still_admin) and
# publish_to_wiki.py (wikilink_admin) before treating a value as a real
# username.
UNRESOLVED_ADMIN_VALUES = ("(unknown)", "?")


def is_unresolved_admin(admin: Optional[str]) -> bool:
    return not admin or admin in UNRESOLVED_ADMIN_VALUES


def years_ago_cutoff(years: float) -> datetime:
    return datetime.now(timezone.utc) - timedelta(days=365 * years)


def retry_after_seconds(resp: requests.Response, attempt: int, base: float = 2) -> float:
    """Seconds to wait before retrying a 429: the Retry-After header if present, else exponential backoff."""
    try:
        return float(resp.headers.get("Retry-After", ""))
    except ValueError:
        return min(base * (attempt + 1), 20)


def request_with_retries(send: Callable[[], requests.Response], url: str, max_attempts: int = 5) -> JSONDict:
    """
    Shared retry loop behind every MediaWiki API call in this codebase --
    `send` is a zero-arg callable that issues the actual GET/POST (so this
    doesn't care which). Handles HTTP 429 (Retry-After header, or
    exponential backoff if that header is absent) and maxlag the same way
    for all of them.

    Raises RuntimeError if every attempt fails (including maxlag exhaustion,
    which isn't an HTTP error and wouldn't otherwise be caught) -- callers
    must not treat a failed fetch the same as a genuinely empty response.
    """
    last_error = "unknown error"
    for attempt in range(max_attempts):
        try:
            resp = send()
        except requests.exceptions.RequestException as exc:
            last_error = f"{type(exc).__name__}: {exc}"
            print(
                f"  ! API request to {url} failed ({last_error}), "
                f"retrying (attempt {attempt + 1}/{max_attempts})",
                file=sys.stderr,
            )
            time.sleep(2 * (attempt + 1))
            continue
        if resp.status_code == 429:
            wait = retry_after_seconds(resp, attempt)
            last_error = "HTTP 429"
            print(
                f"  ! API request to {url} rate-limited (429), "
                f"waiting {wait:.1f}s before retry {attempt + 1}/{max_attempts}",
                file=sys.stderr,
            )
            time.sleep(wait)
            continue
        if resp.status_code == 200:
            data = resp.json()
            if "error" in data and data["error"].get("code") == "maxlag":
                last_error = f"maxlag: {data['error']}"
                time.sleep(5 * (attempt + 1))
                continue
            time.sleep(SLEEP_BETWEEN_REQUESTS)
            return data
        last_error = f"HTTP {resp.status_code}"
        time.sleep(2 * (attempt + 1))
    raise RuntimeError(f"API request to {url} failed after {max_attempts} attempts: {last_error}")


def api_get(params: JSONDict, url: str = API_URL, max_attempts: int = 5) -> JSONDict:
    """GET against the MediaWiki API with maxlag handling/retries -- see request_with_retries."""
    params = dict(params)
    params.setdefault("format", "json")
    params.setdefault("maxlag", "5")
    return request_with_retries(lambda: SESSION.get(url, params=params, timeout=30), url, max_attempts)


def load_json_cache(
    cache_file: Optional[str],
    refresh_cache: bool = False,
    default: Any = None,
    max_age_seconds: Optional[float] = None,
) -> Any:
    """
    Load JSON from cache_file if it exists and refresh_cache isn't set, else
    return `default`.

    If `max_age_seconds` is given, a cache file older than that (by mtime --
    one cheap stat() call, no need to open/parse it) is treated the same as
    a missing one, so callers get a fresh fetch instead of silently trusting
    a snapshot that's aged past usefulness.
    """
    if cache_file and not refresh_cache and os.path.exists(cache_file):
        if max_age_seconds is not None and time.time() - os.path.getmtime(cache_file) > max_age_seconds:
            return default
        with open(cache_file, "r", encoding="utf-8") as f:
            return json.load(f)
    return default


def save_json_cache(cache_file: Optional[str], data: Any) -> None:
    if not cache_file:
        return
    with open(cache_file, "w", encoding="utf-8") as f:
        json.dump(data, f)


def check_csv_schema(
    path: str,
    expected_fieldnames: List[str],
    parser: argparse.ArgumentParser,
    context: str,
) -> Optional[List[str]]:
    """
    If `path` exists and has a non-empty header, calls `parser.error(...)`
    (which prints a message and exits) when its columns don't match
    `expected_fieldnames` -- appending under a mismatched header would
    silently produce a CSV whose header and data rows don't line up.
    Returns the file's existing fieldnames, or None if the file doesn't
    exist or is empty (i.e. a header still needs to be written).
    """
    if not os.path.exists(path) or os.path.getsize(path) == 0:
        return None
    with open(path, newline="", encoding="utf-8") as f:
        existing = csv.DictReader(f).fieldnames
    if existing is not None and list(existing) != expected_fieldnames:
        parser.error(
            f"{context}: {path} has columns {list(existing)}, which don't match the "
            f"current columns {expected_fieldnames}. Appending would produce a CSV "
            "with mismatched rows -- rename/move the old file or pick a fresh path."
        )
    return existing


def read_csv_rows(path: str) -> Tuple[Optional[List[str]], List[Dict[str, str]]]:
    """(fieldnames, rows) read from a CSV in one pass -- fieldnames is None if the file is empty."""
    with open(path, newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        return reader.fieldnames, list(reader)


def count_csv_rows(path: str) -> int:
    """Row count excluding the header, without building a dict per row like read_csv_rows does."""
    with open(path, newline="", encoding="utf-8") as f:
        return max(sum(1 for _ in csv.reader(f)) - 1, 0)


def mw_paginated(
    base_params: JSONDict,
    continue_key: str,
    extract_items: Callable[[JSONDict], List[JSONDict]],
) -> List[JSONDict]:
    """
    Repeatedly call api_get, following `continue_key`-based continuation
    (e.g. 'gapcontinue', 'cmcontinue'), collecting extract_items(data) from
    each page until there's no more continuation value.
    """
    results: List[JSONDict] = []
    cont = None
    while True:
        params = dict(base_params)
        if cont:
            params[continue_key] = cont
        data = api_get(params)
        results.extend(extract_items(data))
        cont = data.get("continue", {}).get(continue_key)
        if not cont:
            break
    return results


def _extract_protected_pages(data: JSONDict) -> List[JSONDict]:
    out: List[JSONDict] = []
    for page in data.get("query", {}).get("pages", {}).values():
        title = page.get("title")
        if not title:
            continue
        level = None
        for prot in page.get("protection", []):
            if prot.get("type") == "edit":
                level = prot.get("level")
                break
        out.append({"title": title, "level": level})
    return out


def fetch_protected_list(
    cache_file: Optional[str] = None,
    refresh_cache: bool = False,
    max_age_seconds: Optional[float] = None,
) -> List[JSONDict]:
    """
    Use list=allpages' protection filters to find namespace-0, non-redirect
    pages with an indefinite edit-protection at 'autoconfirmed' (semi) or
    'extendedconfirmed' (ECP) level.

    If cache_file is given and exists, its contents are used instead of
    hitting the API -- unless refresh_cache is set, or the cache has aged
    past max_age_seconds, in which case the API is queried fresh and
    cache_file is overwritten with the result.

    Returns a list of dicts: {"title": str, "level": str}
    """
    cached = load_json_cache(cache_file, refresh_cache, max_age_seconds=max_age_seconds)
    if cached is not None:
        return cached

    results = mw_paginated(
        {
            "action": "query",
            "generator": "allpages",
            "gapnamespace": "0",
            "gapfilterredir": "nonredirects",
            "gapprtype": "edit",
            "gapprlevel": "autoconfirmed|extendedconfirmed",
            "gapprexpiry": "indefinite",
            "gaplimit": "500",
            "prop": "info",
            "inprop": "protection",
        },
        "gapcontinue",
        _extract_protected_pages,
    )

    save_json_cache(cache_file, results)
    return results


def get_page_content(title: str, url: str = API_URL) -> Optional[str]:
    """Current live wikitext of `title`, or None if the page doesn't exist."""
    data = api_get(
        {"action": "query", "titles": title, "prop": "revisions", "rvprop": "content", "rvslots": "main"},
        url=url,
    )
    for page in data.get("query", {}).get("pages", {}).values():
        if "missing" in page:
            return None
        revisions = page.get("revisions", [])
        if revisions:
            return revisions[0].get("slots", {}).get("main", {}).get("*", "")
    return None


CHECKED_CANDIDATES_PAGE = "User:Rusalkii/Checked candidates for unprotection"

# One bulleted item is "* [[Title]]", optionally followed by more text on
# the same line (a note, a second wikilink, a signature) that's ignored --
# only the first wikilink's target counts, matching that page's own stated
# format ("Must be formatted as a bulleted item immediately followed by a
# link to the page; it will ignore all text on each line after the first
# wikilink"). [^\]|#] stops at "|" too, so a piped display-text link like
# "[[Title|note]]" still resolves to the real target, and at "#" so a
# section link like "[[Title#Section]]" resolves to the plain title that
# audit.csv/publish_to_wiki.py actually compare against.
EXCLUDED_BULLET_RE = re.compile(r"^\*+\s*\[\[([^\]|#]+)", re.MULTILINE)


def fetch_excluded_titles() -> Set[str]:
    """
    Titles manually marked "checked" on CHECKED_CANDIDATES_PAGE. Used both
    by unprotbot.py (pre-filter, before any per-page audit work) and
    publish_to_wiki.py (a safety net at publish time for rows that were
    already audited before being added to that page).
    """
    content = get_page_content(CHECKED_CANDIDATES_PAGE)
    if content is None:
        return set()
    return set(EXCLUDED_BULLET_RE.findall(content))
