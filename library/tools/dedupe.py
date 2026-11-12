"""Find duplicate or near-duplicate entries.

  py.sh dedupe.py [--write]

Keys (survey I §4.5): location (source, commit, path, lines); content (hash of
the site excerpts with comments and whitespace removed: the entry's
content_key); statement (the parent's statement, normalised the same way);
move plus goal shape. Prints clusters of size > 1 and, with --write, saves
reports/dedupe.json. Merging is a reviewer's decision: the best verified
member keeps the entry and lists the others under known_uses.
"""
from __future__ import annotations

import argparse
from collections import defaultdict

from common import ENTRIES, REPORTS, normalised_hash, read_json, write_json


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true")
    a = ap.parse_args()
    keys = defaultdict(lambda: defaultdict(list))
    for d in sorted(p for p in ENTRIES.iterdir() if p.is_dir()):
        e = read_json(d / "entry.json")
        for s in e["sites"]:
            keys["location"][(e["source"]["url"], s["path"], tuple(s["lines"]))].append(e["id"])
        keys["content"][e["content_key"]].append(e["id"])
        par = e.get("parent") or {}
        if par.get("statement") and par["statement"] != "TODO":
            keys["statement"][normalised_hash(par["statement"], e["language"])].append(e["id"])
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
