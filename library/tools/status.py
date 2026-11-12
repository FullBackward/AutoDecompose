"""Show the progress of a harvest run. Read-only; safe to run while the run is going.

  python library/tools/status.py [RUN]        (default: the most recent run)
  python library/tools/status.py RUN --watch  (refresh every 30 s; Ctrl-C to stop)
"""
from __future__ import annotations

import argparse
import json
import time
from collections import Counter

from common import ENTRIES, LEDGER, LIB, read_jsonl


def show(run: str) -> None:
    d = LIB / "reports" / run
    if not d.is_dir():
        print(f"run {run}: not started (library/reports/{run}/ does not exist)")
        return
    calls = read_jsonl(d / "calls.jsonl")
    if not calls and not (d / "summary.json").exists():
        print(f"run {run}: running, no call finished yet (calls are logged when they finish; "
              "the ledger counts below grow before that)")
    cfg_p = LIB / "runs" / f"{run}.json"
    cap = json.loads(cfg_p.read_text(encoding="utf-8")).get("maxCostCNY") if cfg_p.exists() else None
    cost = sum(c.get("cost_cny") or 0 for c in calls)
    tok = sum(c.get("tokens") or 0 for c in calls)
    by_role = Counter(c["role"] for c in calls)
    bad = [c for c in calls if c.get("exit") not in (0, None) or c.get("is_error")]
    print(f"run {run}: {len(calls)} calls finished, {tok:,} tokens, {cost:.2f} CNY"
          + (f" of {cap} CNY cap ({100 * cost / cap:.0f}%)" if cap else ""))
    print("  by role: " + ", ".join(f"{k} {v}" for k, v in sorted(by_role.items())))
    if calls:
        print(f"  first call {calls[0]['at']}, last finished {calls[-1]['at']}")
    if bad:
        print(f"  {len(bad)} failed or errored calls, e.g. {bad[-1]['label']}: exit {bad[-1].get('exit')}")
    entries = [json.loads((p / 'entry.json').read_text(encoding='utf-8'))
               for p in ENTRIES.iterdir() if (p / 'entry.json').exists()]
    st = Counter(e["status"] for e in entries)
    print(f"  entries in library: {len(entries)} (" + ", ".join(f"{k} {v}" for k, v in st.items()) + ")")
    print("  ledgers: " + ", ".join(f"{n} {len(read_jsonl(LEDGER / f'{n}.jsonl'))}"
                                    for n in ("candidates", "screening", "sites", "verdicts")))
    print("  last 5 calls:")
    for c in calls[-5:]:
        print(f"    {c['at'][11:19]} {c['role']:8} {c['label'][:52]:52} exit {c.get('exit')} "
              f"{c.get('cost_cny', 0):.2f} CNY {c.get('seconds', '?')}s")
    s = d / "summary.json"
    if s.exists():
        print("  FINISHED: see " + s.relative_to(LIB.parent).as_posix())


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("run", nargs="?")
    ap.add_argument("--watch", action="store_true")
    a = ap.parse_args()
    runs = sorted((p for p in (LIB / "reports").iterdir() if p.is_dir()), key=lambda p: p.stat().st_mtime)
    run = a.run or (runs[-1].name if runs else None)
    if not run:
        print("no runs yet (library/reports/<run>/ does not exist)")
        return
    while True:
        show(run)
        if not a.watch:
            break
        time.sleep(30)
        print()


if __name__ == "__main__":
    main()
