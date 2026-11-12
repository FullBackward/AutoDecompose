"""Append a record to an append-only ledger, checking its required fields.

  py.sh ledger.py queries   --json '{"query": "...", "engine": "...", "hits": 12, "by": "discoverer-a"}'
  py.sh ledger.py screening --json '{"source_id": "...", "decision": "include", "criterion": "I1-I3", "by": "screener-1"}'
  py.sh ledger.py sites     --json '{"source_id": "...", "path": "...", "lines": [10, 42], "move": "induction", "signal": "induction ... generalizing", "by": "site-finder"}'
  py.sh ledger.py candidates --json '{"url": "https://github.com/o/r", "language": "lean", "why": "...", "found_by": "query:12 | snowball:<source>:<direction>", "by": "discoverer-b"}'
  py.sh ledger.py LEDGER            (no --json: print the number of records)

Records get a timestamp. Existing lines are never rewritten; a correction is
a new record with "supersedes": <line number>.
"""
from __future__ import annotations

import argparse
import json

from common import LEDGER, MOVES, append_jsonl, die, now, read_jsonl

REQUIRED = {
    "queries": ["query", "engine", "hits", "by"],
    "screening": ["source_id", "decision", "criterion", "by"],
    "sites": ["source_id", "path", "lines", "move", "signal", "by"],
    "candidates": ["url", "language", "why", "found_by", "by"],
}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("ledger")
    ap.add_argument("--json")
    a = ap.parse_args()
    if a.json is None:
        if a.ledger in REQUIRED:
            print(len(read_jsonl(LEDGER / f"{a.ledger}.jsonl")))
            return
        die("give --json")
    if a.ledger not in REQUIRED:
        die(f"ledger must be one of {list(REQUIRED)}")
    rec = json.loads(a.json)
    missing = [k for k in REQUIRED[a.ledger] if k not in rec]
    if missing:
        die(f"missing fields {missing}")
    if a.ledger == "screening" and rec["decision"] not in ("include", "exclude", "unsure"):
        die("decision must be include, exclude or unsure")
    if a.ledger == "sites" and rec["move"] not in MOVES:
        die(f"move must be one of {MOVES}")
    rec["at"] = now()
    append_jsonl(LEDGER / f"{a.ledger}.jsonl", rec)
    print(f"appended to {a.ledger}")


if __name__ == "__main__":
    main()
