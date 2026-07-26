#!/usr/bin/env python3
"""
check_unprotected.py

Refreshes the cache of indefinite semi/ECP-protected pages, then
checks audit.csv against it: pages that are no longer indefinitely
semi/ECP-protected are removed from audit.csv and added to
unprotected.csv instead.

USAGE
-----
    python check_unprotected.py --in data/audit.csv --unprotected-out data/unprotected.csv --contact you@example.com
"""

import argparse
import csv
import os
from typing import Dict, List

from utils import (
    AUDIT_CSV_FILE,
    PROTECTED_PAGES_CACHE_FILE,
    UNPROTECTED_CSV_FILE,
    check_csv_schema,
    fetch_protected_list,
    read_csv_rows,
    set_contact,
)


def atomic_write_csv(path: str, fieldnames: List[str], rows: List[Dict[str, str]]) -> None:
    tmp_path = f"{path}.tmp"
    with open(tmp_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)
    os.replace(tmp_path, path)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--in", dest="infile", default=AUDIT_CSV_FILE, help="Audit CSV to check and prune in place")
    parser.add_argument(
        "--unprotected-out",
        dest="unprotected_out",
        default=UNPROTECTED_CSV_FILE,
        help="CSV to append no-longer-protected rows to",
    )
    parser.add_argument("--contact", help="Email or userpage for the User-Agent, per Wikimedia's UA policy")
    args = parser.parse_args()

    set_contact(args.contact)

    print("Refreshing current indefinite semi/ECP-protected page list...")
    candidates = fetch_protected_list(cache_file=PROTECTED_PAGES_CACHE_FILE, refresh_cache=True)
    still_protected_titles = {c["title"] for c in candidates}
    print(f"{len(still_protected_titles)} pages currently indefinitely semi/ECP-protected")

    fieldnames, rows = read_csv_rows(args.infile)

    still_protected = [row for row in rows if row["title"] in still_protected_titles]
    unprotected = [row for row in rows if row["title"] not in still_protected_titles]

    if unprotected:
        write_header = check_csv_schema(args.unprotected_out, fieldnames, parser, "--unprotected-out") is None
        with open(args.unprotected_out, "a", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            if write_header:
                writer.writeheader()
            writer.writerows(unprotected)

        # Only rewrite audit.csv when something actually changed -- the
        # common case (nothing pruned) would otherwise be a full rewrite of
        # a multi-MB file, every run, for a no-op.
        atomic_write_csv(args.infile, fieldnames, still_protected)

    print(
        f"Checked {len(rows)} rows: {len(still_protected)} still indefinitely protected (kept in {args.infile}), "
        f"{len(unprotected)} no longer indefinitely protected (moved to {args.unprotected_out})"
    )


if __name__ == "__main__":
    main()
