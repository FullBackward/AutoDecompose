"""Record a check result, a claim verdict or a review decision for an entry.

  py.sh record_verdict.py ENTRY_ID --check build|fidelity|sufficiency|children \
        --status pass|fail|not-run|ci-record --evidence TEXT --by ROLE
  py.sh record_verdict.py ENTRY_ID --claim N --verdict verified|refuted|unverifiable \
        --evidence TEXT --by ROLE
  py.sh record_verdict.py ENTRY_ID --review correctness|generality|provenance-licence \
        --decision accept|object --evidence TEXT --by ROLE

Verifiers and reviewers never edit an entry; they call this tool. Records are
appended to library/checks/<id>.json (latest record of each key wins) and to
ledger/verdicts.jsonl. Nothing is ever deleted.
"""
from __future__ import annotations

import argparse

from common import (CHECK_STATUSES, ENTRIES, LEDGER, LIB, VERDICTS, append_jsonl,
                    die, now, read_json, write_json)

CHECKS_DIR = LIB / "checks"
CHECK_NAMES = ["provenance", "build", "fidelity", "sufficiency", "children"]
LENSES = ["correctness", "generality", "provenance-licence"]


def record(eid: str, *, check=None, status=None, claim=None, verdict=None,
           review=None, decision=None, evidence="", by="") -> None:
    if not (ENTRIES / eid / "entry.json").exists():
        die(f"no entry {eid}")
    p = CHECKS_DIR / f"{eid}.json"
    data = read_json(p) if p.exists() else {"entry": eid, "records": []}
    if check:
        if check not in CHECK_NAMES or status not in CHECK_STATUSES:
            die(f"--check in {CHECK_NAMES}, --status in {CHECK_STATUSES}")
        rec = {"type": "check", "key": check, "value": status}
    elif claim is not None:
        if verdict not in VERDICTS:
            die(f"--verdict in {VERDICTS}")
        ns = [c["n"] for c in read_json(ENTRIES / eid / "entry.json")["claims"]]
        if claim not in ns:
            die(f"entry has no claim {claim} (claims: {ns})")
        rec = {"type": "claim", "key": str(claim), "value": verdict}
    elif review:
        if review not in LENSES or decision not in ("accept", "object"):
            die(f"--review in {LENSES}, --decision accept|object")
        rec = {"type": "review", "key": review, "value": decision}
    else:
        die("give --check, --claim or --review")
    if not evidence:
        die("--evidence is required: say what was checked and how")
    rec.update({"evidence": evidence, "by": by or "unknown", "at": now()})
    data["records"].append(rec)
    write_json(p, data)
    append_jsonl(LEDGER / "verdicts.jsonl", {"entry": eid, **rec})


def latest(eid: str) -> dict:
    """Latest value per (type, key)."""
    p = CHECKS_DIR / f"{eid}.json"
    out = {}
    if p.exists():
        for r in read_json(p)["records"]:
            out[(r["type"], r["key"])] = r
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("entry")
    ap.add_argument("--check"); ap.add_argument("--status")
    ap.add_argument("--claim", type=int); ap.add_argument("--verdict")
    ap.add_argument("--review"); ap.add_argument("--decision")
    ap.add_argument("--evidence", default="")
    ap.add_argument("--by", default="")
    a = ap.parse_args()
    record(a.entry, check=a.check, status=a.status, claim=a.claim, verdict=a.verdict,
           review=a.review, decision=a.decision, evidence=a.evidence, by=a.by)
    print("recorded")


if __name__ == "__main__":
    main()
