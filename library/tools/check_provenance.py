"""Re-fetch every copied file of an entry at its pinned commit and compare bytes.

  py.sh check_provenance.py ENTRY_ID [--checker NAME]

Records the result as the entry's 'provenance' check in library/checks/<id>.json
and in ledger/verdicts.jsonl. Exit status 1 on any mismatch.
"""
from __future__ import annotations

import argparse
import sys

from common import ENTRIES, fetch_at_commit, load_source, read_json, sha256_bytes
from record_verdict import record


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("entry")
    ap.add_argument("--checker", default="check_provenance.py")
    a = ap.parse_args()
    e = read_json(ENTRIES / a.entry / "entry.json")
    src = dict(load_source(e["source"]["source_id"]))
    src["commit"] = e["source"]["commit"]          # the entry's commit governs
    problems = []
    for f in e["files"]:
        local = (ENTRIES / a.entry / "code" / f["path"]).read_bytes()
        try:
            remote = fetch_at_commit(src, f["path"])
        except FileNotFoundError:
            problems.append(f"{f['path']}: not found upstream at {src['commit'][:12]}")
            continue
        if remote != local:
            problems.append(f"{f['path']}: local copy differs from upstream")
        elif sha256_bytes(local) != f["sha256"]:
            problems.append(f"{f['path']}: recorded hash differs")
    status = "fail" if problems else "pass"
    evidence = "; ".join(problems) or f"{len(e['files'])} file(s) byte-identical at {src['commit']}"
    record(a.entry, check="provenance", status=status, evidence=evidence, by=a.checker)
    print(f"{status} {a.entry}: {evidence}")
    sys.exit(1 if problems else 0)


if __name__ == "__main__":
    main()
