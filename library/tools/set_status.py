"""Promote, flag or deprecate an entry, enforcing the library's gates.

  py.sh set_status.py ENTRY_ID verified|accepted
  py.sh set_status.py ENTRY_ID flagged|deprecated --reason TEXT

verified  needs: strict validation; provenance pass; build pass or ci-record;
          a verdict on every claim, and no claim refuted (remove refuted claims
          first, so the specification is rewritten from verified facts).
accepted  needs: verified; at least one verified claim with evidence kind
          'check' and one verified claim of another kind; an 'accept' from
          every review lens and no standing objection.
The tool also writes the Verification section of README.md from the records.
"""
from __future__ import annotations

import argparse
import re

from common import ENTRIES, LEDGER, REPORTS, append_jsonl, die, now, read_json, write_json
from record_verdict import LENSES, latest
from statements import PROVER


def dedupe_clash(eid: str, e: dict) -> list[str]:
    """Other non-deprecated members of a dedupe cluster that this entry does not list
    in known_uses (fixes brief 2026-11-14, item 5)."""
    p = REPORTS / "dedupe.json"
    if not p.exists():
        return []
    known = " ".join(str(k) for k in e.get("known_uses") or [])
    out = set()
    for clusters in read_json(p).values():
        for ids in (clusters if isinstance(clusters, list) else []):
            ids = ids.get("entries", []) if isinstance(ids, dict) else ids
            if eid in ids:
                for o in ids:
                    if o != eid and o not in known and (ENTRIES / o / "entry.json").exists()                             and read_json(ENTRIES / o / "entry.json")["status"] != "deprecated":
                        out.add(o)
    return sorted(out)
from validate_entry import check as validate


def render(eid: str, e: dict, recs: dict) -> None:
    lines = [f"Status: **{e['status']}**" + (f" ({e.get('status_reason')})" if e.get("status_reason") else ""), ""]
    lines += ["| Check | Result | Evidence | By | Date |", "|---|---|---|---|---|"]
    for (t, k), r in sorted(recs.items()):
        if t == "check":
            lines.append(f"| {k} | {r['value']} | {r['evidence']} | {r['by']} | {r['at'][:10]} |")
    claims = [(int(k), r) for (t, k), r in recs.items() if t == "claim"]
    if claims:
        lines += ["", "| Claim | Verdict | Evidence | By |", "|---|---|---|---|"]
        for n, r in sorted(claims):
            lines.append(f"| {n} | {r['value']} | {r['evidence']} | {r['by']} |")
    revs = [(k, r) for (t, k), r in recs.items() if t == "review"]
    if revs:
        lines += ["", "| Review lens | Decision | Reason | By |", "|---|---|---|---|"]
        for k, r in sorted(revs):
            lines.append(f"| {k} | {r['value']} | {r['evidence']} | {r['by']} |")
    rp = ENTRIES / eid / "README.md"
    text = rp.read_text(encoding="utf-8")
    text = re.sub(r"(<!-- verification:start -->\n).*?(\n<!-- verification:end -->)",
                  lambda m: m[1] + "\n".join(lines) + m[2], text, flags=re.S)
    text = re.sub(r"\| Status \| [a-z]+ \|", f"| Status | {e['status']} |", text, count=1)
    rp.write_text(text, encoding="utf-8")


def gate_errors(eid: str, e: dict, status: str) -> list[str]:
    """Why ENTRY cannot become STATUS (verified or accepted); empty if it can."""
    recs = latest(eid)
    v = lambda t, k: recs.get((t, k), {}).get("value")
    errs = validate(eid, strict=True)
    if v("check", "provenance") != "pass":
        errs.append("provenance check has not passed")
    if v("check", "build") not in ("pass", "ci-record"):
        errs.append("build is neither pass nor ci-record")
    if e["kind"] == "instance" and e["language"] in PROVER and e.get("children") \
            and v("check", "glue-cites-children") != "pass":
        errs.append("glue-cites-children has not passed (validate_entry.py --record-glue)")
    if v("check", "sorry-scan") is None:
        errs.append("sorry-scan has not been recorded (sorry_scan.py)")
    elif v("check", "sorry-scan") == "fail":
        errs.append("sorry-scan found a sorry, admit or axiom inside a parent or child site")
    clash = dedupe_clash(eid, e)
    if clash:
        errs.append(f"duplicate of non-deprecated {', '.join(clash)} (reports/dedupe.json) "
                    f"not listed in known_uses: merge first")
    for c in e["claims"]:
        verdict = v("claim", str(c["n"]))
        if verdict in (None, "unverified"):
            errs.append(f"claim {c['n']} has no verdict")
        elif verdict == "refuted":
            errs.append(f"claim {c['n']} is refuted: remove or rewrite it")
    if status == "accepted":
        ok = [c for c in e["claims"] if v("claim", str(c["n"])) == "verified"]
        if not any(c["evidence_kind"] == "check" for c in ok):
            errs.append("no verified claim backed by a check")
        if not any(c["evidence_kind"] != "check" for c in ok):
            errs.append("no verified claim of a second kind of evidence")
        for lens in LENSES:
            if v("review", lens) != "accept":
                errs.append(f"review lens '{lens}' has not accepted")
    return errs


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("entry")
    ap.add_argument("status", choices=["verified", "accepted", "flagged", "deprecated"])
    ap.add_argument("--reason", default="")
    ap.add_argument("--dry-run", action="store_true", help="only say whether the gates allow it")
    a = ap.parse_args()
    p = ENTRIES / a.entry / "entry.json"
    e = read_json(p)
    recs = latest(a.entry)
    v = lambda t, k: recs.get((t, k), {}).get("value")
    if a.status in ("verified", "accepted"):
        errs = gate_errors(a.entry, e, a.status)
        if a.dry_run:
            print(("ok " if not errs else "NO ") + f" {a.entry} -> {a.status}")
            for x in errs:
                print(f"  - {x}")
            raise SystemExit(1 if errs else 0)
        if errs:
            print(f"refused: {a.entry} cannot become {a.status}")
            for x in errs:
                print(f"  - {x}")
            raise SystemExit(1)
    elif not a.reason:
        die("--reason is required for flagged and deprecated")
    e["status"] = a.status
    e["status_reason"] = a.reason
    e["status_at"] = now()
    write_json(p, e)
    render(a.entry, e, recs)
    append_jsonl(LEDGER / "verdicts.jsonl", {"entry": a.entry, "type": "status",
                                              "value": a.status, "reason": a.reason, "at": now()})
    print(f"{a.entry} -> {a.status}")


if __name__ == "__main__":
    main()
