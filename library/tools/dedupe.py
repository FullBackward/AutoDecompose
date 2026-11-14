"""Find duplicate or near-duplicate entries.

  py.sh dedupe.py [--write]

Keys (survey I §4.5): location (source, commit, path, lines); content (hash of
the site excerpts with comments and whitespace removed: the entry's
content_key); statement (the parent's statement, normalised the same way);
move plus goal shape. Prints clusters of size > 1 and, with --write, saves
reports/dedupe.json. Keys: location, content, statement, move+shape, and
problem+move (the competition problem named in a path, with the move). Merging is a reviewer's decision: the best verified
member keeps the entry and lists the others under known_uses.
"""
from __future__ import annotations

import argparse
import re
from collections import defaultdict

from common import ENTRIES, REPORTS, load_entries, normalised_hash, read_json, write_json


PROBLEM = re.compile(r"(?i)(imo|usamo|usa|egmo|apmo|putnam|uk)[\W_]*((?:19|20)\d\d)[\W_]*"
                     r"(?:r\d+[\W_]*)?(?:problem|p|q)?[\W_]*([ab]?\d{1,2})(?!\d)")


def problem_of(e: dict) -> str | None:
    """Competition problem identity from a site path, parent first: 'IMO2026/Q4/solution.lean',
    'Imo1964P1.lean', 'imo2026_q4' -> 'imo2026-q4'; 'putnam_2025_a6.lean' -> 'putnam2025-a6'.
    Repositories made by different agents differ at the character level in every other key
    (fixes brief 2026-11-14, item 5)."""
    sites = sorted(e["sites"], key=lambda s: s.get("role") != "parent")
    for s in sites:
        m = PROBLEM.search(s["path"])
        if m:
            label = m[3].lower()
            return f"{m[1].lower()}{m[2]}-{'q' + label if label.isdigit() else label}"
    return None


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true")
    a = ap.parse_args()
    keys = defaultdict(lambda: defaultdict(list))
    entries, bad = load_entries()
    if bad:
        print(f"# not read (entry.json does not parse): {', '.join(bad)}")
    for e in entries:
        for s in e["sites"]:
            keys["location"][(e["source"]["url"], s["path"], tuple(s["lines"]))].append(e["id"])
        keys["content"][e["content_key"]].append(e["id"])
        par = e.get("parent") or {}
        if par.get("statement") and par["statement"] != "TODO":
            keys["statement"][normalised_hash(par["statement"], e["language"])].append(e["id"])
        prob = problem_of(e)
        if prob:
            keys["problem+move"][(prob, e["move"])].append(e["id"])
        shape = (e.get("applicability") or {}).get("goal_shape", "")
        if shape and shape != "TODO":
            keys["move+shape"][(e["move"], " ".join(shape.split()).lower())].append(e["id"])
    report = {}
    for kind, groups in keys.items():
        clusters = [sorted(set(v)) for v in groups.values() if len(set(v)) > 1]
        report[kind] = clusters
        for c in clusters:
            print(f"{kind}: {', '.join(c)}")
    if not any(report.values()):
        print("no duplicates found")
    if a.write:
        write_json(REPORTS / "dedupe.json", report)


if __name__ == "__main__":
    main()
