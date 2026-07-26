#!/usr/bin/env python3
"""
unprotbot.py

Audits indefinitely semi-protected / extended-confirmed-protected articles
(namespace 0, non-redirects) on en.wikipedia.org, and for every page whose
*original* protection was placed more than X years ago and which is NOT under
an extended-confirmed contentious-topic (CT)restriction , produces a table with:

  - date of (original) protection
  - protecting admin
  - protecting edit summary
  - list of previous protections
  - total number of times protected (edit-protection only, any level/time)
  - page views
  - type of protection (current level)

Handles page moves: MediaWiki's protection log records an entry like
"moved protection settings from [[Old Title]] to [[New Title]]" (action
'move_prot') when protection is carried over during a page move. This
script walks backward through such entries to find where the protection
was *originally* applied, falling back to the move-log timestamp if the
original page/log entry can no longer be resolved. Log entries that only
touch move-protection (not edit-protection) are ignored, per the "ignore
changes to just move protection" instruction.

REQUIREMENTS
------------
    pip install requests

USAGE
-----
    python unprotbot.py --out data/audit.csv --contact you@example.com --limit 200

    Resume an interrupted run (skips titles already in --out, appends to it):
        python unprotbot.py --out data/audit.csv --contact you@example.com --resume

    Force a fresh candidate list instead of using the on-disk caches:
        python unprotbot.py --out data/audit.csv --contact you@example.com --refresh-cache

"""

import argparse
import csv
import os
import re
import sys
import time
from datetime import datetime, timedelta, timezone
from typing import Any, Dict, Iterator, List, Optional, Set, Tuple
from urllib.parse import quote

import requests

from utils import (
    AUDIT_CSV_FILE,
    DATA_DIR,
    JSONDict,
    OLD_PROT_CUTOFF_YEARS,
    PROTECTED_PAGES_CACHE_FILE,
    SESSION,
    SLEEP_BETWEEN_REQUESTS,
    api_get,
    check_csv_schema,
    fetch_protected_list,
    format_prev_prot_entry,
    load_json_cache,
    mw_paginated,
    read_csv_rows,
    save_json_cache,
    set_contact,
    retry_after_seconds
)

# A single MediaWiki protection-log event, as returned by list=logevents.
LogEntry = JSONDict

# --------------------------------------------------------------------------
# Configuration
# --------------------------------------------------------------------------

PAGEVIEWS_URL = (
    "https://wikimedia.org/api/rest_v1/metrics/pageviews/per-article/"
    "en.wikipedia/all-access/{agent}/{title}/daily/{start}/{end}"
)

OLD_PROT_CUTOFF = datetime.now(timezone.utc) - timedelta(days=365 * OLD_PROT_CUTOFF_YEARS)

FIELDNAMES: List[str] = [
    "title",
    "protection_date",
    "protecting_admin",
    "edit_summary",
    "protection_count",
    "previous_protections",
    "pageviews_last_30d",
    "protection_type",
    "resolved_via",
    "admin_active",
]


# --------------------------------------------------------------------------
# Step 2: Protection log analysis
# --------------------------------------------------------------------------

# Heuristic fallback (only used for old log entries without structured
# params.details): does the description mention edit-protection, or is it
# purely about move-protection?
EDIT_PROT_RE = re.compile(r"\[edit=", re.I)
MOVE_TAG_RE = re.compile(r"\[move=", re.I)

# Before the 'move_prot' action existed as a distinct log action type,
# protection carried over during a page move was sometimes logged as a
# plain 'protect' entry whose auto-generated comment just describes the
# move (e.g. "moved [[Old Title]] to [[New Title]]"), with no [edit=...]
# or [move=...] tag of its own.
MOVE_ONLY_COMMENT_RE = re.compile(r"^moved\s+\[\[", re.I)


def is_move_only_entry(entry: LogEntry) -> bool:
    """
    True if this log entry is purely a page-move record -- either the
    modern 'move_prot' action, or an old-style 'protect' entry whose
    comment is just a move description with no protection-setting tags.
    Such entries don't represent a deliberate protection action, so they
    shouldn't count toward protection_count or appear in the previous-
    protections list.
    """
    if entry.get("action") == "move_prot":
        return True
    if entry.get("params", {}).get("details"):
        return False  # structured data present -- trust it, not a move-only record
    desc = log_entry_description(entry)
    return bool(MOVE_ONLY_COMMENT_RE.match(desc.strip())) and not EDIT_PROT_RE.search(desc) and not MOVE_TAG_RE.search(desc)


def is_protection_entry(entry: LogEntry) -> bool:
    """True for a deliberate protect/modify action -- excludes move_prot carry-over and unprotect."""
    return entry.get("action") in ("protect", "modify") and not is_move_only_entry(entry)


def get_protection_log(title: str) -> List[LogEntry]:
    """Full protect-log for a title, oldest first."""
    data = api_get(
        {
            "action": "query",
            "list": "logevents",
            "letype": "protect",
            "letitle": title,
            "lelimit": "500",
            "ledir": "newer",
        }
    )
    return data.get("query", {}).get("logevents", [])


def log_entry_description(entry: LogEntry) -> str:
    """
    Human-readable protection description for a log entry, used only as a
    fallback for older entries that lack structured params.details.
    """
    params = entry.get("params", {})
    return params.get("description", "") or entry.get("comment", "")


def find_edit_detail(details: List[Dict[str, Any]]) -> Optional[Dict[str, Any]]:
    """The structured params.details entry for edit-protection, or None."""
    return next((d for d in details if d.get("type") == "edit"), None)


def touches_edit_protection(entry: LogEntry) -> bool:
    """
    Returns True if this log entry represents a change to *edit*
    protection, as opposed tojust move-protection.
    """
    action = entry.get("action", "")
    if action == "move_prot":
        # Moving protection settings during a page move carries over
        # whatever restrictions existed, including edit-protection --
        # treat as relevant so we can trace history through it.
        return True
    if action == "unprotect":
        return True

    # Modern log entries (~2014+) carry a structured list of the
    # protections actually set/changed by this entry -- prefer that over
    # regexing the human-readable description.
    details = entry.get("params", {}).get("details")
    if details:
        return find_edit_detail(details) is not None

    desc = log_entry_description(entry)
    if not desc:
        # No description available -- can't tell; be inclusive rather
        # than silently dropping potentially-relevant history.
        return True
    if EDIT_PROT_RE.search(desc):
        return True
    if MOVE_TAG_RE.search(desc):
        return False
    return True


def extract_old_title_from_move_prot(entry: LogEntry) -> Optional[str]:
    """
    For a 'move_prot' log entry, try to recover the source title, e.g.
    from entry['params']['oldtitle_title'] (modern API) or by parsing
    entry['comment'] text like:
      "moved protection settings from [[Old Title]] to [[New Title]]"
    """
    params = entry.get("params", {})
    for key in ("oldtitle_title", "oldtitle", "old_title"):
        if params.get(key):
            return params[key]

    comment = entry.get("comment", "") or ""
    m = re.search(r"from \[\[:?([^\]|]+)\]\]", comment)
    if m:
        return m.group(1).strip()
    return None


def parse_ts(ts: str) -> datetime:
    return datetime.strptime(ts, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)


# Sentinel returned by edit_expiry/edit_protection_signature when an entry's
# format doesn't let us positively read its edit-protection state -- kept
# distinct from any real value (a datetime, None for confirmed-indefinite,
# or a concrete signature) so an ambiguous old-format entry is never mistaken
# for proof of anything, in either direction.
UNKNOWN = object()

# Protect-log actions that represent a deliberate application (or removal)
# of protection settings, as opposed to a move-carried-over record
# (move_prot) with no protection decision of its own.
PROTECTION_ACTIONS = ("protect", "modify", "unprotect")


def parse_expiry_value(expiry_str: Optional[str]) -> Any:
    """Parse a protection-detail expiry string into a datetime, None if indefinite, or UNKNOWN if malformed."""
    if not expiry_str or expiry_str.lower() in ("infinite", "infinity", "indefinite"):
        return None
    try:
        return parse_ts(expiry_str)
    except ValueError:
        return UNKNOWN


EXPIRES_DESC_RE = re.compile(r"\[edit=[^\]]*\]\s*\(expires ([0-9]{1,2}:[0-9]{2}, [0-9]{1,2} \w+ [0-9]{4}) \(UTC\)\)", re.I)
INDEFINITE_DESC_RE = re.compile(r"\[edit=[^\]]*\]\s*\(indefinite\)", re.I)


def edit_expiry(entry: LogEntry) -> Any:
    """
    The edit-protection expiry set by a 'protect'/'modify' log entry: a
    datetime if temporary, None if confirmed indefinite, or UNKNOWN if the
    entry's format doesn't let us tell either way (e.g. an old free-text
    comment with no recognizable expiry tag) -- callers that need positive
    proof of indefinite protection should check `is None` exactly, not just
    falsiness.
    """
    details = entry.get("params", {}).get("details")
    if details:
        d = find_edit_detail(details)
        return parse_expiry_value(d.get("expiry")) if d else UNKNOWN

    desc = log_entry_description(entry)
    if INDEFINITE_DESC_RE.search(desc):
        return None
    m = EXPIRES_DESC_RE.search(desc)
    if m:
        try:
            return datetime.strptime(m.group(1), "%H:%M, %d %B %Y").replace(tzinfo=timezone.utc)
        except ValueError:
            return UNKNOWN
    return UNKNOWN


EDIT_BRACKET_RE = re.compile(r"\[edit=([^\]]*)\]\s*(\([^)]*\))?", re.I)


def edit_protection_signature(entry: LogEntry) -> Any:
    """
    A comparable value describing this entry's *edit*-protection state
    immediately after it was applied.

    MediaWiki's protection log always records the *full current state* of
    every restriction type on the page, not a diff of what a given action
    actually changed -- so a 'modify' entry that only touched, say,
    move-protection still shows edit-protection in its snapshot, identical
    to the entry before it. Comparing consecutive signatures is the only
    reliable way to tell "this entry set edit-protection" from "edit-
    protection just carried over unchanged while something else was
    touched" (see resolve_original_protection).

    Returns a hashable tuple for a concrete edit-protection state,
    "unprotected" if this entry leaves no edit-protection active, or
    UNKNOWN if the entry's format doesn't say either way.
    """
    if entry.get("action") == "unprotect":
        return "unprotected"

    details = entry.get("params", {}).get("details")
    if details:
        d = find_edit_detail(details)
        return ("edit", d.get("level"), d.get("expiry")) if d else "unprotected"

    desc = log_entry_description(entry)
    m = EDIT_BRACKET_RE.search(desc)
    if m:
        return ("edit", m.group(1), m.group(2))
    if not desc:
        return UNKNOWN
    # A snapshot with no [edit=...] tag at all -- e.g. one only listing
    # [move=...] -- genuinely doesn't have edit-protection active.
    return "unprotected" if MOVE_TAG_RE.search(desc) else UNKNOWN


def entries_with_new_edit_protection(history: List[LogEntry]) -> List[LogEntry]:
    """
    The subset of `history` (in the same oldest-first order) whose *edit*-
    protection signature actually differs from the entry immediately
    preceding it chronologically -- filtering out entries that only
    touched some other restriction (e.g. move-protection) and merely
    carried edit-protection forward unchanged in their snapshot.
    Move_prot entries are transparent here: they don't have their own
    edit-protection snapshot, so they're skipped without resetting the
    comparison (the entries before/after one are still compared directly).
    An unreadable signature is always kept, never used to suppress a
    later entry, and never suppressed itself -- we only omit an entry
    when we can positively confirm nothing changed.
    """
    out = []
    last_sig = None
    for e in history:
        if e.get("action") not in PROTECTION_ACTIONS:
            continue
        sig = edit_protection_signature(e)
        if sig is UNKNOWN or sig != last_sig:
            out.append(e)
        if sig is not UNKNOWN:
            last_sig = sig
    return out


def build_full_history(
    title: str, _seen: Optional[Set[str]] = None, _before: Optional[str] = None
) -> List[LogEntry]:
    """
    Recursively walk move_prot entries to build the complete, flattened
    list of edit-protection-relevant log entries for a title, oldest
    first, spanning every title in its move chain.

    A move_prot entry can occur anywhere in a title's log, not just as the
    earliest entry -- e.g. a page that already had its own protection
    history can later be moved on top of a differently-named article,
    inheriting *that* article's protection history from before the move.
    So every move_prot entry found is chased back to its old title, not
    just one sitting at position 0.
    """
    _seen = _seen or set()
    if title in _seen:
        return []
    # A new set per level (not a shared mutation) scopes the guard to the
    # current root-to-leaf path, not the whole tree -- a page that's been
    # moved back onto an earlier title of its own (e.g. swapped between two
    # capitalizations several times) legitimately revisits that title twice,
    # each time for a disjoint time window, and both visits must go through.
    _seen = _seen | {title}

    log = get_protection_log(title)
    relevant = [e for e in log if touches_edit_protection(e)]
    if _before is not None:
        # Only entries from strictly before the move belong to the page
        # that moved -- the old title now names a different page (typically
        # a leftover redirect), so anything logged against that title at or
        # after the move happened to that page, not to this one.
        relevant = [e for e in relevant if e.get("timestamp", "") < _before]

    out = []
    for e in relevant:
        if e.get("action") == "move_prot":
            old_title = extract_old_title_from_move_prot(e)
            if old_title:
                # Always carried forward, never discarded. An earlier
                # version of this pruned `out` whenever the ancestor title
                # had protection activity of its own, on the theory that a
                # busy ancestor meant a genuinely different, unrelated page
                # had lived there. In practice, on real article histories,
                # an ancestor with real activity is usually the SAME subject
                # bouncing between two titles it has held more than once
                # (e.g. a primary-topic dispute round-robin) -- pruning
                # there silently discarded the very entry that explains the
                # page's current indefinite protection. That false-positive
                # was worse than the rarer genuine-unrelated-occupant case
                # this was meant to guard against, and nothing here can
                # reliably tell the two apart (pageid differs in both
                # cases), so no pruning is attempted at all.
                ancestor_history = build_full_history(old_title, _seen, e.get("timestamp", ""))
                out.extend(ancestor_history)
        out.append(e)

    # Sibling move_prot branches can legitimately re-walk overlapping
    # ancestor time windows now that nothing is pruned (e.g. two different
    # moves both tracing back through the same earlier stint at a title)
    # -- dedup by logid, keeping first occurrence, so a merged entry isn't
    # double-counted in protection_count or shown twice in the history.
    seen_logids: Set[Any] = set()
    deduped = []
    for e in out:
        logid = e.get("logid")
        if logid is not None and logid in seen_logids:
            continue
        seen_logids.add(logid)
        deduped.append(e)
    return deduped


def resolve_original_protection(title: str) -> Optional[Dict[str, Any]]:
    """
    Find the most recent log entry where an admin deliberately applied
    *indefinite* edit-protection to this page or an ancestor title it was
    moved from.

    Returns a dict:
      {
        "date": <ISO8601 str, or "" if resolved_via is "unknown">,
        "admin": <str>,
        "summary": <str>,
        "resolved_via": "direct" | "move-traced" | "unconfirmed" | "unknown",
        "protection_count": <int, total 'protect'/'modify' edit-protection
                             entries across the whole move chain, any
                             level/time -- not counting move_prot carry-
                             over or unprotect entries>,
        "history": [every other relevant log entry across the move
                     chain, oldest first, excluding the one described
                     above],
      }
    or None if no relevant log entry was found at all (e.g. protection
    predates the log, or page/log unavailable).

    "unconfirmed" means the best candidate is an old-format entry whose
    expiry text we can't parse either way -- not proven indefinite, but not
    proven temporary either. "unknown" means every protect/modify entry
    found is *confirmed temporary* (e.g. carries an explicit "expires ..."
    tag), so nothing in the log actually explains the page's current
    indefinite protection -- picking one of those as "the" protection would
    misrepresent an expired temporary protection as the real thing, so
    "date" is left blank instead of guessing.
    """
    history = build_full_history(title)
    if not history:
        return None

    protection_count = sum(1 for e in history if is_protection_entry(e))

    # Only entries that actually changed edit-protection (not just carried
    # it forward unchanged while some other restriction was touched) are
    # eligible to be "the" protection -- see entries_with_new_edit_protection.
    eligible = [e for e in entries_with_new_edit_protection(history) if is_protection_entry(e)]

    indefinite = []
    unconfirmed = []
    for e in eligible:
        expiry = edit_expiry(e)
        if expiry is None:
            indefinite.append(e)
        elif expiry is UNKNOWN:
            unconfirmed.append(e)

    if indefinite:
        chosen = indefinite[-1]  # most recent deliberate indefinite application
        resolved_via = "direct" if chosen.get("title") == title else "move-traced"
    elif unconfirmed:
        chosen = unconfirmed[-1]  # most recent entry that isn't provably temporary
        resolved_via = "unconfirmed"
    else:
        chosen = None
        resolved_via = "unknown"

    if chosen is None:
        date, admin, summary = "", "(unknown)", "(no confirmed indefinite protection found in log)"
        remaining_history = history
    else:
        date = chosen.get("timestamp", "")
        admin = chosen.get("user", "(unknown)")
        summary = with_source_title_note(chosen.get("comment", ""), chosen.get("title"), title)
        remaining_history = [e for e in history if e is not chosen]

    return {
        "date": date,
        "admin": admin,
        "summary": summary,
        "resolved_via": resolved_via,
        "protection_count": protection_count,
        "history": remaining_history,
    }


def with_source_title_note(comment: str, entry_title: Optional[str], current_title: str) -> str:
    """
    Append '(on [[Entry Title]])' to a log entry's comment when the entry
    was logged under an earlier, pre-move title -- so a protection traced
    back through the move chain still shows which title it was actually
    placed on, rather than silently attributing it to the page's current
    name.
    """
    comment = (comment or "").strip()
    if entry_title and entry_title != current_title:
        note = f"(on [[{entry_title}]])"
        return f"{comment} {note}" if comment else note
    return comment


def format_previous_protections(history: List[LogEntry], current_title: str) -> List[str]:
    """
    Human-readable list of protection log entries other than the one
    already reported in the date/admin/summary columns, formatted as
    'YYYY-MM-DD by Admin: summary'. Spans the full move chain, so history
    from before a page move is included -- entries logged under an earlier
    title get a '(on [[Old Title]])' note appended so that's clear. Move-
    only entries (automatic carry-over during a page move -- not a
    deliberate protection action -- whether logged as 'move_prot' or as an
    old-style plain 'protect' entry with a move-description comment) are
    excluded. Explicitly sorted reverse chronological (newest first) by
    timestamp.
    """
    out = []
    relevant = [e for e in history if not is_move_only_entry(e)]
    for e in sorted(relevant, key=lambda e: e.get("timestamp", ""), reverse=True):
        ts = e.get("timestamp", "")[:10]
        comment = with_source_title_note(e.get("comment", ""), e.get("title"), current_title)
        out.append(format_prev_prot_entry(ts, e.get("user", "?"), comment))
    return out


# --------------------------------------------------------------------------
# Step 3: Filter out ECP/recently protected pages
# --------------------------------------------------------------------------

# The protecting summary itself often names the
# arbitration-enforcement basis for an ECP restriction (e.g.
# "[[WP:30/500|Arbitration enforcement]]" or a direct WP:ARBPIA3#500/30
# reference). NOTE: this only recognizes the Israel-Palestine (ARBPIA)
# citation shorthand plus the generic phrase "Arbitration enforcement" --
# it is not a general detector for every contentious-topic area's ECP
# restriction. This catches some pages not in the category.
ECP_SUMMARY_RE = re.compile(r"WP:30/500|WP:ARBPIA3#500/30|WP:A/I/PIA|Arbitration enforcement|ARBPIA3", re.I)


def is_ecp_by_summary(summary: Optional[str]) -> bool:
    """Does the protecting edit summary cite the ARBPIA arbitration-enforcement basis for ECP?"""
    return bool(ECP_SUMMARY_RE.search(summary or ""))


# Auto-maintained by the {{Contentious topics/talk notice}} template family:
# a talk page lands here when it carries that notice (without
# section=yes/relatedcontent=yes/nocat=yes) AND its associated article is
# extended-confirmed protected.
PROTECTED_LIST_CACHE_TTL_DAYS = 1
ECP_CAT_CACHE_TTL_DAYS = 30

ECP_CATEGORY = "Category:Wikipedia pages subject to the extended confirmed restriction"


def fetch_ecp_talk_titles(
    cache_file: Optional[str] = None,
    refresh_cache: bool = False,
    max_age_seconds: Optional[float] = None,
) -> Set[str]:
    """
    Fetch every Talk: page in ECP_CATEGORY.

    If cache_file is given and exists, its contents are used instead of
    hitting the API -- unless refresh_cache is set, or the cache has aged
    past max_age_seconds, in which case the API is queried fresh and
    cache_file is overwritten with the result.

    Returns a set of "Talk:Title" strings.
    """
    cached = load_json_cache(cache_file, refresh_cache, max_age_seconds=max_age_seconds)
    if cached is not None:
        return set(cached)

    titles = mw_paginated(
        {
            "action": "query",
            "list": "categorymembers",
            "cmtitle": ECP_CATEGORY,
            "cmnamespace": "1",  # Talk: only
            "cmlimit": "500",
        },
        "cmcontinue",
        lambda data: [m["title"] for m in data.get("query", {}).get("categorymembers", [])],
    )

    save_json_cache(cache_file, titles)
    return set(titles)


def is_ecp_contentious_topic(title: str, ecp_talk_titles: Set[str]) -> bool:
    """Is this article's talk page in the extended-confirmed-restriction category?"""
    return f"Talk:{title}" in ecp_talk_titles


# Unlike the ECP cache above, this one isn't fetched from Wikipedia -- it's
# built up by this script itself across runs. A page's resolved protection
# date (see resolve_original_protection) can only ever get *more recent*
# over time (a reprotection replaces it with a later date; nothing makes it
# earlier), so a cached date that's still within OLD_PROT_CUTOFF as of
# *this* run means the page is still definitely too young and the log walk
# can be skipped entirely. Once real time carries the cutoff past a cached
# date, that guarantee no longer holds -- the page might now be old enough,
# or might have been reprotected more recently since we last checked -- so
# it falls through to a real recheck rather than being trusted.

def check_too_young_cache(cache: Dict[str, str], title: str, cutoff: datetime) -> Tuple[bool, bool]:
    """
    Returns (still_valid, evicted).

    still_valid=True is a known-good fast-path skip: title's cached date is
    still within cutoff. evicted=True means a stale or malformed entry was
    just removed from cache -- the caller should treat this as a real
    recheck (and mark its cache dirty) rather than trusting outdated
    information.
    """
    cached_date = cache.get(title)
    if cached_date is None:
        return False, False
    try:
        if parse_ts(cached_date) > cutoff:
            return True, False
    except ValueError:
        pass
    del cache[title]
    return False, True


# --------------------------------------------------------------------------
# Step 4: Page views
# --------------------------------------------------------------------------


def _fetch_pageviews(title: str, agent: str, start: str, end: str, max_attempts: int = 5) -> Optional[int]:
    """
    Try to fetch pageviews summed over [start, end] for one `agent`
    classification ('user' or 'all-agents'). Returns the sum, or None on
    any failure -- a plain 404 is treated as "try a different agent
    classification" and doesn't print anything (that's the routine,
    expected case get_pageviews falls back on), but rate-limiting/network
    failures still get logged since those indicate a real problem.
    """
    safe_title = quote(title.replace(" ", "_"), safe="")
    url = PAGEVIEWS_URL.format(agent=agent, title=safe_title, start=start, end=end)

    for attempt in range(max_attempts):
        try:
            resp = SESSION.get(url, timeout=30)
            if resp.status_code == 429:
                wait = retry_after_seconds(resp, attempt)
                print(
                    f"  ! pageviews fetch for {title!r} ({agent}) rate-limited (429), "
                    f"waiting {wait:.1f}s before retry {attempt + 1}/{max_attempts}",
                    file=sys.stderr,
                )
                time.sleep(wait)
                continue
            if resp.status_code == 404:
                return None
            if resp.status_code != 200:
                print(f"  ! pageviews fetch for {title!r} ({agent}) returned HTTP {resp.status_code}", file=sys.stderr)
                return None
            items = resp.json().get("items", [])
            return sum(item.get("views", 0) for item in items)
        except (requests.RequestException, ValueError) as exc:
            print(f"  ! pageviews fetch for {title!r} ({agent}) failed: {exc}", file=sys.stderr)
            return None
        finally:
            time.sleep(SLEEP_BETWEEN_REQUESTS)

    print(f"  ! pageviews fetch for {title!r} ({agent}) still rate-limited after {max_attempts} attempts, giving up", file=sys.stderr)
    return None


def get_pageviews(title: str, days: int = 30, end_lag_days: int = 2, max_attempts: int = 5) -> Optional[int]:
    """
    Sum of daily pageviews over a trailing N-day window ending
    `end_lag_days` days before today.

    Wikimedia's pageviews data for very recent days isn't reliably
    processed yet -- including "today" (or sometimes yesterday) in the
    request range can 404 the *entire* request for lower-traffic articles,
    even though the article has real, non-zero traffic on every other day
    in range. Ending the window a couple of days back avoids that.

    Tries human-only traffic ('user' agent, the preferred metric) first.
    Even with the lag fix above, Wikimedia's backend still 404s the whole
    request under 'user'-only classification for a substantial fraction of
    lower-traffic articles despite real traffic existing -- confirmed this
    isn't transient (retries don't help) but that broadening to 'all-agents'
    (human + bot/spider) usually does resolve it, so a 404 falls back to
    that once rather than reporting a page as having no data.
    """
    end_date = datetime.now(timezone.utc) - timedelta(days=end_lag_days)
    end = end_date.strftime("%Y%m%d")
    # The pageviews API's start/end are both inclusive, so subtracting
    # `days - 1` (not `days`) from the end date makes the inclusive range
    # span exactly `days` calendar days.
    start = (end_date - timedelta(days=days - 1)).strftime("%Y%m%d")

    result = _fetch_pageviews(title, "user", start, end, max_attempts)
    if result is not None:
        return result

    result = _fetch_pageviews(title, "all-agents", start, end, max_attempts)
    if result is None:
        print(f"  ! pageviews fetch for {title!r} found no data under 'user' or 'all-agents'", file=sys.stderr)
    return result


# --------------------------------------------------------------------------
# Step 5: Protecting admin activity
# --------------------------------------------------------------------------

ADMIN_INACTIVE_AFTER_DAYS = 365 // 2  # 6 months
ADMIN_ACTIVITY_CACHE_TTL_DAYS = 7
ADMIN_ACTIVE_LABEL = {True: "active", False: "inactive", None: "unknown"}


def is_admin_active(admin: str, cache: Dict[str, list]) -> Optional[bool]:
    """
    Has `admin` made any edit in the last ADMIN_INACTIVE_AFTER_DAYS days?

    Reuses a cached result from `cache` (mutated in place) if it's less than
    ADMIN_ACTIVITY_CACHE_TTL_DAYS old.
    """
    if not admin or admin in ("(unknown)", "?"):
        return None

    cached = cache.get(admin)
    if cached is not None:
        status, checked_at = cached
        try:
            fresh = parse_ts(checked_at) >= datetime.now(timezone.utc) - timedelta(days=ADMIN_ACTIVITY_CACHE_TTL_DAYS)
        except ValueError:
            fresh = False
        if fresh:
            return status

    status = _fetch_admin_active(admin)
    cache[admin] = [status, datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")]
    return status


def _fetch_admin_active(admin: str) -> Optional[bool]:
    """Live usercontribs lookup backing is_admin_active -- not cached itself."""
    try:
        data = api_get(
            {
                "action": "query",
                "list": "usercontribs",
                "ucuser": admin,
                "uclimit": "1",
                "ucdir": "older",
                "ucprop": "timestamp",
            }
        )
    except Exception as exc:  # noqa: BLE001
        print(f"  ! error checking activity for admin {admin!r}: {exc}", file=sys.stderr)
        return None

    contribs = data.get("query", {}).get("usercontribs", [])
    if not contribs:
        return False

    try:
        last_edit = parse_ts(contribs[0]["timestamp"])
    except (KeyError, ValueError):
        return None

    return last_edit >= datetime.now(timezone.utc) - timedelta(days=ADMIN_INACTIVE_AFTER_DAYS)


# --------------------------------------------------------------------------
# Main pipeline
# --------------------------------------------------------------------------


def log_progress(i: int, total: int, title: str, reason: Optional[str] = None) -> None:
    print(f"[{i}/{total}] {title}", file=sys.stderr)
    if reason:
        print(reason, file=sys.stderr)


def iter_audit_rows(
    limit: Optional[int] = None,
    cache_file: Optional[str] = None,
    ct_cache_file: Optional[str] = None,
    too_young_cache_file: Optional[str] = None,
    admin_cache_file: Optional[str] = None,
    ecp_summary_cache_file: Optional[str] = None,
    refresh_cache: bool = False,
    skip_titles: Optional[Set[str]] = None,
) -> Iterator[Dict[str, Any]]:
    """
    Yields audit row dicts one at a time, as they're found.
    """
    skip_titles = skip_titles or set()
    candidates = fetch_protected_list(
        cache_file=cache_file,
        refresh_cache=refresh_cache,
        max_age_seconds=PROTECTED_LIST_CACHE_TTL_DAYS * 86400,
    )
    print(f"[info] {len(candidates)} indefinite semi/ECP-protected pages found", file=sys.stderr)

    seen_titles = set()
    unique = []
    for c in candidates:
        if c["title"] not in seen_titles:
            seen_titles.add(c["title"])
            unique.append(c)

    if limit is not None:
        unique = unique[:limit]

    # Pre-filter the candidate pool against the ECP contentious-topics
    # category once, up front
    ecp_talk_titles = fetch_ecp_talk_titles(
        cache_file=ct_cache_file,
        refresh_cache=refresh_cache,
        max_age_seconds=ECP_CAT_CACHE_TTL_DAYS * 86400,
    )
    ecp_summary_cache = set(load_json_cache(ecp_summary_cache_file, refresh_cache, default=[]))
    ecp_restricted_titles = {c["title"] for c in unique if is_ecp_contentious_topic(c["title"], ecp_talk_titles)}
    ecp_restricted_titles |= ecp_summary_cache
    print(
        f"[info] {len(ecp_restricted_titles)} candidates are ECP contentious-topic restricted "
        "(category or cached protection-summary match)",
        file=sys.stderr,
    )

    too_young_cache = load_json_cache(too_young_cache_file, refresh_cache, default={})
    too_young_cache_dirty = 0
    too_young_count = 0

    admin_activity_cache = load_json_cache(admin_cache_file, refresh_cache, default={})

    try:
        for i, entry in enumerate(unique, 1):
            title = entry["title"]
            if title in skip_titles:
                continue

            if title in ecp_restricted_titles:
                # Already known from the category pre-filter -- skip before
                # doing any per-page work at all (no log fetch, no printing).
                continue

            still_valid, evicted = check_too_young_cache(too_young_cache, title, OLD_PROT_CUTOFF)
            if still_valid:
                too_young_count += 1
                continue
            if evicted:
                # A stale entry was just evicted -- recheck for real, in case
                # the page was reprotected more recently since we last looked.
                too_young_cache_dirty += 1

            try:
                original = resolve_original_protection(title)
            except Exception as exc:  # noqa: BLE001
                log_progress(i, len(unique), title, f"  ! error resolving protection log: {exc}")
                continue

            if original is None:
                log_progress(i, len(unique), title, "  -> skipped: no relevant protection log entries found")
                continue

            # "unknown" means every protect/modify entry found in the log is
            # confirmed temporary -- nothing explains WHEN/WHO/WHY the page
            # became indefinitely protected. But the page only got here by
            # passing fetch_protected_list's own indefinite-protection
            # filter, so it unquestionably *is* indefinitely protected right
            # now regardless of what the log trace could pin down -- dropping
            # it from the audit entirely would hide a real candidate just
            # because its history is hard to read. Log it with the fields we
            # can't confidently fill left blank, instead of skipping.
            unknown_resolution = original["resolved_via"] == "unknown"

            if unknown_resolution:
                orig_date = None
            else:
                try:
                    orig_date = parse_ts(original["date"])
                except (KeyError, ValueError):
                    log_progress(i, len(unique), title, f"  -> skipped: unparseable protection date {original.get('date')!r}")
                    continue

                if orig_date > OLD_PROT_CUTOFF:
                    # Most candidates land here -- too common to log per-item, so
                    # skip silently and just report a total count at the end.
                    too_young_count += 1
                    too_young_cache[title] = original["date"]
                    too_young_cache_dirty += 1
                    if too_young_cache_dirty >= 100:
                        save_json_cache(too_young_cache_file, too_young_cache)
                        too_young_cache_dirty = 0
                    continue

            log_progress(i, len(unique), title)
            if unknown_resolution:
                print(
                    "  ! warning: currently indefinitely protected but every protection log "
                    "entry found is confirmed temporary -- logging with protection_date/"
                    "protecting_admin/edit_summary blank instead of skipping",
                    file=sys.stderr,
                )

            # Check every summary in this page's protection history
            all_summaries = ([] if unknown_resolution else [original["summary"]]) + [
                e.get("comment", "") for e in original["history"]
            ]
            if any(is_ecp_by_summary(s) for s in all_summaries):
                print("  -> skipped: a protection summary in this page's history cites ECP arbitration enforcement", file=sys.stderr)
                ecp_summary_cache.add(title)
                continue

            views = get_pageviews(title)
            prev = format_previous_protections(original["history"], title)

            admin = None if unknown_resolution else original["admin"]

            yield {
                "title": title,
                "protection_date": orig_date.strftime("%Y-%m-%d") if orig_date is not None else None,
                "protecting_admin": admin,
                "edit_summary": None if unknown_resolution else original["summary"],
                "protection_count": original["protection_count"],
                "previous_protections": " | ".join(prev) if prev else "(none)",
                "pageviews_last_30d": views if views is not None else "N/A",
                "protection_type": entry["level"] or "unknown",
                "resolved_via": original["resolved_via"],
                "admin_active": ADMIN_ACTIVE_LABEL[is_admin_active(admin, admin_activity_cache)],
            }
    finally:
        # Runs on normal completion AND on early abandonment (the caller
        # breaks out of its for-loop, e.g. after Ctrl+C, which closes this
        # generator) -- without a finally here, everything accumulated in
        # these caches during a partial run is silently lost instead of
        # persisted for next time.
        if too_young_cache_dirty:
            save_json_cache(too_young_cache_file, too_young_cache)
        save_json_cache(admin_cache_file, admin_activity_cache)
        save_json_cache(ecp_summary_cache_file, sorted(ecp_summary_cache))

    if too_young_count:
        print(f"[info] skipped {too_young_count} pages: not old enough (cutoff {OLD_PROT_CUTOFF.strftime('%m/%d/%Y')})", file=sys.stderr)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", default=AUDIT_CSV_FILE, help="Output CSV path")
    parser.add_argument("--limit", type=int, default=None, help="Limit number of candidate pages (for testing)")
    parser.add_argument("--contact", help="Email or userpage for the User-Agent, per Wikimedia's UA policy")
    parser.add_argument(
        "--resume",
        action="store_true",
        help="Skip titles already present in --out and append to it, instead of overwriting",
    )
    parser.add_argument(
        "--refresh-cache",
        action="store_true",
        help=(
            f"Ignore any existing {DATA_DIR}/protected_pages_cache.json / {DATA_DIR}/ecp_talk_titles_cache.json / "
            f"{DATA_DIR}/too_young_cache.json / {DATA_DIR}/admin_activity_cache.json / "
            f"{DATA_DIR}/ecp_summary_cache.json and re-fetch/re-derive all of them from scratch"
        ),
    )
    args = parser.parse_args()

    set_contact(args.contact)

    done_titles = set()
    file_mode = "w"
    write_header = True
    if args.resume and os.path.exists(args.out):
        check_csv_schema(args.out, FIELDNAMES, parser, "--resume")
        _, resume_rows = read_csv_rows(args.out)
        done_titles = {row["title"] for row in resume_rows}
        file_mode = "a"
        write_header = False
        print(f"[info] resuming: {len(done_titles)} titles already in {args.out}", file=sys.stderr)

    count = 0
    with open(args.out, file_mode, newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=FIELDNAMES)
        if write_header:
            writer.writeheader()
        for row in iter_audit_rows(
            limit=args.limit,
            cache_file=PROTECTED_PAGES_CACHE_FILE,
            ct_cache_file=os.path.join(DATA_DIR, "ecp_talk_titles_cache.json"),
            too_young_cache_file=os.path.join(DATA_DIR, "too_young_cache.json"),
            admin_cache_file=os.path.join(DATA_DIR, "admin_activity_cache.json"),
            ecp_summary_cache_file=os.path.join(DATA_DIR, "ecp_summary_cache.json"),
            refresh_cache=args.refresh_cache,
            skip_titles=done_titles,
        ):
            writer.writerow(row)
            f.flush()
            count += 1

    print(f"Wrote {count} rows to {args.out}")


if __name__ == "__main__":
    main()
