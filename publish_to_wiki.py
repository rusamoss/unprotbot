#!/usr/bin/env python3
"""
publish_to_wiki.py

Keeps the two live "candidates for unprotection" pages on en.wikipedia.org
in sync with unprotbot's audit:
  - User:Rusalkii/Candidates for unprotection
  - User:Rusalkii/Candidates for unprotection with high page views

Two modes:
  --mode check_unprotected   Runs check_unprotected.py to drop rows that are
                               no longer indefinitely protected, then
                               republishes both pages from the pruned
                               audit.csv. Meant to run frequently (e.g.
                               hourly).
  --mode full_run             Runs a full, non-resumed unprotbot.py audit
                               (still respecting the existing caches' own
                               TTLs -- not a hard --refresh-cache) into a
                               fresh audit.csv, then republishes. Meant to
                               run rarely (e.g. weekly) -- a full pass over
                               every candidate can take hours under
                               Wikipedia's rate limits.

A lockfile (publish.lock) makes a check_unprotected run skip instead of
racing a full_run that's still in progress.

USAGE
-----
    python publish_to_wiki.py --mode check_unprotected
    python publish_to_wiki.py --mode full_run

    Generate the page text locally without touching Wikipedia:
        python publish_to_wiki.py --mode check_unprotected --dry-run

    Preview wikitext from an arbitrary CSV, without running --mode's
    pipeline or touching the live protected-pages list at all:
        python publish_to_wiki.py --mode check_unprotected --dry-run --in old_audit.csv
"""

import argparse
import operator
import os
import re
import subprocess
import sys
from datetime import datetime, timedelta, timezone
from typing import Callable, Dict, List, Optional, Tuple
from urllib.parse import quote

from utils import (
    API_URL,
    AUDIT_CSV_FILE,
    DATA_DIR,
    JSONDict,
    MAX_PROTECTION_COUNT,
    OLD_PROT_CUTOFF_YEARS,
    PREV_PROT_DATE_PATTERN,
    SESSION,
    UNPROTECTED_CSV_FILE,
    WIKI_HOST,
    api_get,
    read_csv_rows,
    request_with_retries,
    set_contact,
)
from wiki_credentials import CONTACT, WIKI_BOT_PASSWORD, WIKI_BOT_USERNAME

# This script's own directory -- subprocess argv (unlike Python's imports)
# is resolved relative to the child process's cwd, not this script's
# location, so a bare "check_unprotected.py" would only work when invoked
# with cwd already set to this directory. Anchoring here keeps it working
# under cron/systemd, where that isn't guaranteed.
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))

AUDIT_CSV = AUDIT_CSV_FILE
UNPROTECTED_CSV = UNPROTECTED_CSV_FILE
LOCK_FILE = os.path.join(DATA_DIR, "publish.lock")

DRY_RUN_MAIN_FILE = os.path.join(DATA_DIR, "dry_run_main.txt")
DRY_RUN_HIGH_PAGEVIEWS_FILE = os.path.join(DATA_DIR, "dry_run_high_pageviews.txt")
DRY_RUN_ALL_FILE = os.path.join(DATA_DIR, "dry_run_all.txt")

LOW_PAGEVIEWS_PAGE = "User:Rusalkii/Candidates for unprotection"
HIGH_PAGEVIEWS_PAGE = "User:Rusalkii/Candidates for unprotection with high page views"

EDIT_SUMMARY = "Updating unprotection candidates"

MAX_PAGEVIEWS = (
    20000  # drop rows with more than this many pageviews/30d from the main table
)
# Only the main table filters on this -- high-pageviews has no age
# requirement. Distinctly named from utils.OLD_PROT_CUTOFF_YEARS (both get
# passed as a "years" kwarg to the two page-intro templates below, which
# made them easy to swap by accident when this was still called YEAR_CUTOFF).
MAIN_TABLE_MIN_AGE_YEARS = 10

# Separate table: pages with heavy traffic but only lightly protected --
# candidates worth a second look since they haven't needed reprotection much
# despite being high-visibility. Same pageviews cutoff as MAX_PAGEVIEWS, just
# selecting the pages on the other side of it (more than, not at-or-under).
HIGH_PAGEVIEWS_THRESHOLD = MAX_PAGEVIEWS
LOW_PROTECTION_COUNT_MAX = 3

COLUMNS: List[Tuple[str, str]] = [
    ("title", "Page"),
    ("protection_date", "Protection date"),
    ("protecting_admin", "Protecting admin"),
    ("edit_summary", "Edit summary"),
    ("protection_count", "Times protected"),
    ("previous_protections", "Previous protections"),
    ("pageviews_last_30d", "Page views (30d)"),
    ("protection_type", "Protection type"),
]

# Matches a previous-protections line as written by unprotbot.py's
# format_previous_protections: "YYYY-MM-DD by Admin: summary".
PREV_PROT_LINE_RE = re.compile(rf"^({PREV_PROT_DATE_PATTERN} by )([^:]+):(.*)$")

# Splits on " | " only when it's immediately followed by another entry's
# date prefix -- a literal " | " occurring inside a single entry's own
# free-text admin comment (real Wikipedia protection-log comments are
# unrestricted) isn't a boundary and must not be split on.
PREV_PROT_SPLIT_RE = re.compile(rf" \| (?={PREV_PROT_DATE_PATTERN} by )")

# Matches one non-nested {{...}} template invocation. Protection-log
# comments/summaries are free text written by many different admins over
# many years -- if one happens to contain literal template syntax, MediaWiki
# would try to transclude it when this text lands in published wikitext.
TEMPLATE_RE = re.compile(r"\{\{[^{}]*\}\}")


def escape_templates(text: str) -> str:
    """Wrap any {{template}} invocations in <nowiki> so publishing never transcludes them."""
    return TEMPLATE_RE.sub(lambda m: f"<nowiki>{m.group(0)}</nowiki>", text)


def wikilink_admin(admin: Optional[str], active: Optional[str] = None, is_sysop: Optional[str] = None) -> str:
    """
    [[User:Name]], or the raw text unchanged if there's no real username to
    link. Appends " (inactive)" if `active` is "inactive", and " (-admin)"
    if `is_sysop` is "no" (confirmed no longer an administrator) -- both
    can apply at once.
    """
    if not admin or admin in ("(unknown)", "?"):
        return admin or ""
    link = f"[[User:{admin}]]"
    if active == "inactive":
        link += " (inactive)"
    if is_sysop == "no":
        link += " (-admin)"
    return link


def format_previous_protections(raw: Optional[str]) -> str:
    """Each ' | '-joined log entry from the CSV on its own line, admin wikilinked."""
    if not raw or raw == "(none)":
        return "(none)"
    items = []
    for item in PREV_PROT_SPLIT_RE.split(raw):
        item = item.strip()
        m = PREV_PROT_LINE_RE.match(item)
        if m:
            prefix, admin, rest = m.groups()
            item = f"{prefix}{wikilink_admin(admin.strip())}:{escape_templates(rest)}"
        else:
            item = escape_templates(item)
        items.append(item)
    return "<br>\n".join(items)


def format_pageviews(raw: Optional[str]) -> str:
    try:
        return f"{int(raw):,}"
    except (TypeError, ValueError):
        return raw or ""


PROTECTION_TYPE_LABELS = {"autoconfirmed": "semi", "extendedconfirmed": "extended"}


def format_protection_type(raw: Optional[str]) -> str:
    return PROTECTION_TYPE_LABELS.get(raw, raw or "")


def compare_threshold(
    raw: Optional[str], value: int, op: Callable[[int, int], bool]
) -> bool:
    try:
        return op(int(raw), value)
    except (TypeError, ValueError):
        return False


def is_old_enough(protection_date: Optional[str], cutoff: datetime) -> bool:
    """
    True if `protection_date` ("YYYY-MM-DD") is at or before `cutoff`. A
    blank/unparseable date (e.g. the "unknown" resolution case, where
    protection_date is left empty) can't be confirmed to meet the bar, so
    it's excluded rather than assumed to pass.
    """
    if not protection_date:
        return False
    try:
        date = datetime.strptime(protection_date, "%Y-%m-%d").replace(tzinfo=timezone.utc)
    except ValueError:
        return False
    return date <= cutoff


def row_sort_key(row: Dict[str, str]) -> Tuple[float, str]:
    """Default table order: fewest protections first, then oldest protection date first."""
    try:
        count = int(row.get("protection_count"))
    except (TypeError, ValueError):
        count = float("inf")
    # "YYYY-MM-DD" sorts correctly as a plain string; a blank/unparseable
    # date (e.g. the "unknown" resolution case) sorts last within its
    # protection_count group rather than misleadingly first.
    date = row.get("protection_date") or "9999-99-99"
    return count, date


def row_to_wikitext(row: Dict[str, str]) -> str:
    title = row.get("title", "")
    protection_date = row.get("protection_date", "")
    log_url = f"{WIKI_HOST}/w/index.php?title=Special:Log&page={quote(title, safe='')}&type=protect"
    cells = {
        "title": f"[[{title}]]",
        "protection_date": f"[{log_url} {protection_date}]",
        "protecting_admin": wikilink_admin(
            row.get("protecting_admin", ""), row.get("admin_active"), row.get("admin_is_sysop")
        ),
        "edit_summary": escape_templates(row.get("edit_summary") or ""),
        "protection_count": row.get("protection_count", ""),
        "previous_protections": format_previous_protections(
            row.get("previous_protections", "")
        ),
        "pageviews_last_30d": format_pageviews(row.get("pageviews_last_30d", "")),
        "protection_type": format_protection_type(row.get("protection_type", "")),
    }
    lines = ["|-"]
    for key, _ in COLUMNS:
        lines.append(f"| {cells[key]}")
    return "\n".join(lines)


def assemble_table(blocks: List[str]) -> str:
    out = [
        '{| class="wikitable sortable"',
        "! " + " !! ".join(label for _, label in COLUMNS),
    ]
    out.extend(blocks)
    out.append("|}")
    return "\n".join(out)


MAIN_PAGE_INTRO = (
    "This is a list of pages which were (as of the {date} bot run) indefinitely "
    "semi- or extended-confirmed protected more than {years} years ago, have fewer "
    "than {max_pageviews:,} page views a month, and no more than {max_prot_count} "
    "entries in the protection log. This ignores redirects and pages which are only "
    "move protected, and filters out pages under [[Wikipedia:ECR|extended-confirmed "
    "restrictions]] due to general sanctions, or where the protection summary mentioned ArbCom sanctions. These pages are probably good "
    "candidates for a [[WP:TRYUNPROT]] trial.\n\n"
    "If unprotecting, make sure to check the protection log manually. The bot-read history can be wonky in cases with page moves, though all major bugs should be cleared up at this point.\n\n"
    f"See also [[{HIGH_PAGEVIEWS_PAGE}]].\n\n"
)

HIGH_PAGEVIEWS_PAGE_INTRO = (
    "This is a list of pages which were (as of the {date} bot run) indefinitely "
    "semi- or extended-confirmed protected more than {years} years ago, have "
    "greater than {threshold:,} page views a month, and no more than "
    "{low_prot_count} entries in the protection log. This ignores redirects and "
    "pages which are only move protected, and filters out pages under "
    "[[WP:ECR|extended-confirmed restrictions]] due to general sanctions, or where the protection summary mentioned ArbCom sanctions.\n\n"
    "If unprotecting, make sure to check the protection log manually. The bot-read history can be wonky in cases with page moves, though all major bugs should be cleared up at this point.\n\n"
    f"See also [[{LOW_PAGEVIEWS_PAGE}]].\n\n"
)


# Matches the "as of the July 25, 2026 bot run" stamp embedded in both
# page intros -- stripped out before comparing generated text against the
# live page, so a run that would only bump this date (nothing else in
# either table actually changed) is correctly recognized as a no-op rather
# than triggering a content-free edit.
BOT_RUN_DATE_RE = re.compile(r"as of the \w+ \d{1,2}, \d{4} bot run")


def normalize_for_diff(text: str) -> str:
    return BOT_RUN_DATE_RE.sub("as of the [DATE] bot run", text)


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


def wiki_login(username: str, password: str, url: str = API_URL) -> None:
    """
    Log SESSION into the wiki using a bot password from
    Special:BotPasswords (username like "User@botname") -- not a full
    account password, and not usable to log into the web UI.
    """
    login_token = api_get(
        {"action": "query", "meta": "tokens", "type": "login"}, url=url
    )["query"]["tokens"]["logintoken"]

    post_data = {
        "action": "login",
        "lgname": username,
        "lgpassword": password,
        "lgtoken": login_token,
        "format": "json",
    }
    result = request_with_retries(
        lambda: SESSION.post(url, data=post_data, timeout=30), url
    ).get("login", {})
    if result.get("result") != "Success":
        raise RuntimeError(f"Wiki login failed: {result}")


def get_csrf_token(url: str = API_URL) -> str:
    """Requires a prior wiki_login() call on the same SESSION."""
    return api_get({"action": "query", "meta": "tokens"}, url=url)["query"]["tokens"][
        "csrftoken"
    ]


def edit_page(
    title: str,
    text: str,
    summary: str,
    token: str,
    bot: bool = True,
    url: str = API_URL,
) -> JSONDict:
    """
    Replace `title`'s content with `text` via action=edit. Requires a prior
    wiki_login() + get_csrf_token() call -- `token` is that csrftoken, not
    a login token.
    """
    post_data = {
        "action": "edit",
        "title": title,
        "text": text,
        "summary": summary,
        "bot": "1" if bot else "0",
        "token": token,
        "format": "json",
    }
    data = request_with_retries(
        lambda: SESSION.post(url, data=post_data, timeout=30), url
    )
    if "error" in data:
        raise RuntimeError(f"Wiki edit of {title!r} failed: {data['error']}")
    edit_result = data.get("edit", {})
    if edit_result.get("result") != "Success":
        raise RuntimeError(f"Wiki edit of {title!r} did not succeed: {data}")
    return edit_result


def format_bot_run_date(dt: datetime) -> str:
    return f"{dt:%B} {dt.day}, {dt:%Y}"


def try_acquire_lock(mode: str) -> bool:
    try:
        fd = os.open(LOCK_FILE, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
    except FileExistsError:
        return False
    with os.fdopen(fd, "w") as f:
        f.write(
            f"pid={os.getpid()} mode={mode} started={datetime.now(timezone.utc).isoformat()}\n"
        )
    return True


def release_lock() -> None:
    if os.path.exists(LOCK_FILE):
        os.remove(LOCK_FILE)


def run_subprocess(args: List[str]) -> None:
    print(f"$ {' '.join(args)}", file=sys.stderr)
    subprocess.run(args, check=True)


def run_check_unprotected() -> bool:
    """
    Runs check_unprotected.py and returns whether it actually pruned
    anything. check_unprotected.py only rewrites audit.csv when something
    changed (see its own atomic_write_csv call), so comparing its mtime
    before/after is a free, reliable signal -- no stdout parsing needed.
    """
    mtime_before = os.path.getmtime(AUDIT_CSV) if os.path.exists(AUDIT_CSV) else None
    run_subprocess(
        [
            sys.executable,
            os.path.join(SCRIPT_DIR, "check_unprotected.py"),
            "--in",
            AUDIT_CSV,
            "--unprotected-out",
            UNPROTECTED_CSV,
        ]
    )
    mtime_after = os.path.getmtime(AUDIT_CSV) if os.path.exists(AUDIT_CSV) else None
    return mtime_before != mtime_after


def run_full_run() -> None:
    # Write to a temp path and only replace audit.csv on full success -- a
    # crash partway through a multi-hour run must not leave the live file
    # (which the next check_unprotected run reads) truncated.
    tmp_out = AUDIT_CSV + ".new"
    run_subprocess(
        [
            sys.executable,
            os.path.join(SCRIPT_DIR, "unprotbot.py"),
            "--out",
            tmp_out,
        ]
    )
    os.replace(tmp_out, AUDIT_CSV)


def build_wikitext(
    infile: str, include_all: bool
) -> Tuple[str, str, Optional[str], str]:
    """Returns (main_text, high_pageviews_text, all_text, stats_message). all_text is None unless include_all is set."""
    _, all_rows = read_csv_rows(infile)
    all_rows.sort(key=row_sort_key)

    all_blocks = [row_to_wikitext(r) for r in all_rows]

    # Computed once rather than inside is_old_enough per row.
    min_age_cutoff = datetime.now(timezone.utc) - timedelta(days=365 * MAIN_TABLE_MIN_AGE_YEARS)

    kept_blocks = [
        block
        for row, block in zip(all_rows, all_blocks)
        if compare_threshold(row.get("pageviews_last_30d"), MAX_PAGEVIEWS, operator.le)
        and compare_threshold(
            row.get("protection_count"), MAX_PROTECTION_COUNT, operator.le
        )
        and is_old_enough(row.get("protection_date"), min_age_cutoff)
    ]
    high_pageviews_blocks = [
        block
        for row, block in zip(all_rows, all_blocks)
        if compare_threshold(
            row.get("pageviews_last_30d"), HIGH_PAGEVIEWS_THRESHOLD, operator.gt
        )
        and compare_threshold(
            row.get("protection_count"), LOW_PROTECTION_COUNT_MAX, operator.lt
        )
    ]

    date_str = format_bot_run_date(datetime.now(timezone.utc))

    main_text = (
        MAIN_PAGE_INTRO.format(
            date=date_str,
            years=MAIN_TABLE_MIN_AGE_YEARS,
            max_pageviews=MAX_PAGEVIEWS,
            max_prot_count=MAX_PROTECTION_COUNT,
        )
        + assemble_table(kept_blocks)
        + "\n"
    )
    high_pageviews_text = (
        HIGH_PAGEVIEWS_PAGE_INTRO.format(
            date=date_str,
            years=OLD_PROT_CUTOFF_YEARS,
            threshold=HIGH_PAGEVIEWS_THRESHOLD,
            low_prot_count=LOW_PROTECTION_COUNT_MAX,
        )
        + assemble_table(high_pageviews_blocks)
        + "\n"
    )
    # Only assembled when actually needed -- on a real (non-dry-run)
    # publish, nothing ever reads all_text, so building it would be a
    # wasted full render of every row on every hourly/weekly run.
    all_text = assemble_table(all_blocks) + "\n" if include_all else None

    dropped = len(all_rows) - len(kept_blocks)
    stats = (
        f"{len(kept_blocks)} kept for {LOW_PAGEVIEWS_PAGE!r} ({dropped} dropped: "
        f">{MAX_PAGEVIEWS:,} pageviews/30d, >{MAX_PROTECTION_COUNT} times protected, "
        f"or protected less than {MAIN_TABLE_MIN_AGE_YEARS} years ago); "
        f"{len(high_pageviews_blocks)} kept for {HIGH_PAGEVIEWS_PAGE!r} "
        f"(pageviews > {HIGH_PAGEVIEWS_THRESHOLD:,}/30d and protection count < {LOW_PROTECTION_COUNT_MAX}); "
        f"{len(all_rows)} rows total"
    )
    return main_text, high_pageviews_text, all_text, stats


def publish_or_preview(infile: str, dry_run: bool) -> None:
    main_text, high_pageviews_text, all_text, stats = build_wikitext(
        infile, include_all=dry_run
    )
    print(f"[info] {stats}", file=sys.stderr)

    if dry_run:
        for path, text in [
            (DRY_RUN_MAIN_FILE, main_text),
            (DRY_RUN_HIGH_PAGEVIEWS_FILE, high_pageviews_text),
            (DRY_RUN_ALL_FILE, all_text),
        ]:
            with open(path, "w", encoding="utf-8") as f:
                f.write(text)
        print(
            f"[dry-run] wrote {DRY_RUN_MAIN_FILE} / {DRY_RUN_HIGH_PAGEVIEWS_FILE} / {DRY_RUN_ALL_FILE} instead of publishing",
            file=sys.stderr,
        )
    else:
        wiki_login(WIKI_BOT_USERNAME, WIKI_BOT_PASSWORD)
        token = get_csrf_token()
        for page_title, text in [(LOW_PAGEVIEWS_PAGE, main_text), (HIGH_PAGEVIEWS_PAGE, high_pageviews_text)]:
            current = get_page_content(page_title)
            # Compared with the date stamp stripped out -- the mode-level
            # "did check_unprotected prune anything" check upstream isn't
            # enough on its own, since a pruned row might not have been in
            # THIS page's table anyway, leaving this page's real content
            # unchanged even though something changed elsewhere.
            if current is not None and normalize_for_diff(current) == normalize_for_diff(text):
                print(f"[info] {page_title!r} unchanged except the date stamp -- skipping edit", file=sys.stderr)
                continue
            edit_page(page_title, text, EDIT_SUMMARY, token)
            print(f"[info] published to {page_title!r}", file=sys.stderr)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--mode", choices=["check_unprotected", "full_run"], required=True
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Write the generated page text locally instead of publishing to Wikipedia",
    )
    parser.add_argument(
        "--in",
        dest="infile",
        default=None,
        help=(
            "Render wikitext from this CSV instead of running --mode's pipeline first -- "
            "only valid together with --dry-run, for previewing formatting against an "
            "existing audit CSV without touching the live protected-pages list at all"
        ),
    )
    args = parser.parse_args()

    if args.infile and not args.dry_run:
        parser.error("--in is only valid together with --dry-run")

    set_contact(CONTACT)

    if args.infile:
        # Pure CSV -> wikitext preview -- no pipeline run, so no need for
        # the lock either (nothing shared is touched).
        publish_or_preview(args.infile, dry_run=True)
        return

    if not try_acquire_lock(args.mode):
        print(
            f"[info] {LOCK_FILE} exists -- another publish run is in progress, skipping this run",
            file=sys.stderr,
        )
        return

    try:
        if args.mode == "check_unprotected":
            changed = run_check_unprotected()
        else:
            run_full_run()
            changed = True  # a full run always rewrites audit.csv from scratch

        if changed or args.dry_run:
            publish_or_preview(AUDIT_CSV, dry_run=args.dry_run)
        else:
            print(
                "[info] no pages were unprotected -- nothing to publish, skipping wiki edit",
                file=sys.stderr,
            )
    finally:
        release_lock()


if __name__ == "__main__":
    main()
