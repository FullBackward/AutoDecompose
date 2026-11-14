"""Exclusion E3 as a recorded check: no sorry, admit, Admitted or axiom closes a goal in an entry.

  py.sh sorry_scan.py ENTRY_ID|all [--dry-run]

Scans every copied prover file under the entry's code/ (Lean, Rocq, Isabelle)
for the tokens that close a goal without a proof: `sorry` (Lean, Isabelle),
`admit` (Lean, Rocq), `Admitted` (Rocq), `axiom` (Lean) and `Axiom` (Rocq).
Isabelle's `oops` abandons a proof rather than closing it: it is listed, never
failed. Comments are blanked first (Lean `--` and `/- -/`, Rocq and Isabelle
`(* *)`), as well as a regex can, keeping line numbers.

A hit inside a parent, child or skeleton site fails the check; a hit elsewhere
in a copied file is listed in the evidence and does not fail, since files are
copied whole and other theorems in them may be unfinished. An entry with no
prover file (a markdown skill, a LaTeX blueprint node) records not-run.
Records `sorry-scan` with record_verdict.py, by sorry_scan.py, and re-renders
the README's Verification section. It never changes a status.
"""
from __future__ import annotations

import argparse
import re

from common import ENTRIES, die, language_of, read_json

TOKENS = {
    "lean": ["sorry", "admit", "axiom"],
    "rocq": ["admit", "Admitted", "Axiom", "axiom"],
    "isabelle": ["sorry"],
}
LISTED_ONLY = {"isabelle": ["oops"]}


def blank(m: re.Match) -> str:
    return re.sub(r"[^\n]", " ", m[0])


def strip_comments(text: str, lang: str) -> str:
    if lang == "lean":
        text = re.sub(r"/-.*?-/", blank, text, flags=re.S)
        text = re.sub(r"--[^\n]*", blank, text)
    else:
        for _ in range(3):  # nested (* (* *) *), innermost first
            text = re.sub(r"\(\*(?:(?!\(\*).)*?\*\)", blank, text, flags=re.S)
    return text


def scan(eid: str) -> tuple[str, str, list, list]:
    e = read_json(ENTRIES / eid / "entry.json")
    sites = [s for s in e["sites"] if s.get("role") in ("parent", "child", "skeleton")]
    inside, outside, listed, prover_files = [], [], [], 0
    for f in e["files"]:
        lang = language_of(f["path"])
        if lang not in TOKENS:
            continue
        prover_files += 1
        p = ENTRIES / eid / "code" / f["path"]
        text = strip_comments(p.read_bytes().decode("utf-8", "replace").replace("\r\n", "\n"), lang)
        for kind, toks in (("close", TOKENS[lang]), ("listed", LISTED_ONLY.get(lang, []))):
            for tok in toks:
                for m in re.finditer(rf"(?<![\w'.]){re.escape(tok)}(?![\w'])", text):
                    line = text.count("\n", 0, m.start()) + 1
                    hit = f"{f['path']}:{line} ({tok})"
                    if kind == "listed":
                        listed.append(hit)
                    elif any(s["path"] == f["path"] and s["lines"][0] <= line <= s["lines"][1] for s in sites):
                        inside.append(hit)
                    else:
                        outside.append(hit)
    if not prover_files:
        return "not-run", "no Lean, Rocq or Isabelle file among the copied files", [], []
    show = lambda xs: (", ".join(xs[:12]) + (f", ... ({len(xs)} in all)" if len(xs) > 12 else "")) or "none"
    ev = (f"inside parent/child/skeleton sites: {show(inside)}; elsewhere in the copied files "
          f"(not failed): {show(outside)}" + (f"; oops (listed, not failed): {show(listed)}" if listed else ""))
    return ("fail" if inside else "pass"), ev, inside, outside


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("entry", help="entry id, or 'all'")
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()
    ids = sorted(p.name for p in ENTRIES.iterdir() if (p / "entry.json").exists()) \
        if a.entry == "all" else [a.entry]
    if a.entry != "all" and not (ENTRIES / a.entry / "entry.json").exists():
        die(f"no entry {a.entry}")
    from record_verdict import latest, record
    from set_status import render
    for eid in ids:
        st, ev, inside, outside = scan(eid)
        print(f"{st:7} {eid}  inside {len(inside)}, elsewhere {len(outside)}")
        if not a.dry_run:
            record(eid, check="sorry-scan", status=st, evidence=ev, by="sorry_scan.py")
            render(eid, read_json(ENTRIES / eid / "entry.json"), latest(eid))


if __name__ == "__main__":
    main()
