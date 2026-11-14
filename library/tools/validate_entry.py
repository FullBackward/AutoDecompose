"""Check one entry, or all, against the library's rules. No network.

  py.sh validate_entry.py ENTRY_ID|--all [--strict] [--record-glue]

Checks: required fields and vocabularies; every listed file exists under
code/ with the recorded size and SHA-256; every site lies inside its file and
its excerpt hash matches; README.md has the required sections; every prover
code block in README.md appears verbatim in a copied file (so no code was
retyped or invented); claims are well formed. With --strict (required before
a status above draft) no TODO may remain outside the rendered Verification
section, and, for an instance in a prover language (lean, rocq, isabelle):
every parent and child statement is verbatim from a copied file or null with a
note; the glue (parent and skeleton sites) cites every child that is not a
subgoal; a theorem-scale shape matches the site lengths. Deprecated entries are
kept for the record and skip the strict content checks. --record-glue records
the glue-cites-children check for every prover instance. Exit status 1 if any
entry fails.
"""
from __future__ import annotations

import argparse
import re
import sys

import statements as S

from common import (CHECK_STATUSES, ENTRIES, EVIDENCE_KINDS, KINDS, MOVES,
                    STATUSES, read_json, sha256_bytes)

REQUIRED = ["id", "kind", "status", "title", "intent", "move", "language", "source",
            "files", "sites", "applicability", "claims", "rule", "content_key"]
SECTIONS = ["## Intent", "## The decomposition", "## Why it is good",
            "## When to use it, and when not", "## Consequences", "## Verification",
            "## Source and licence"]
PROVER_FENCES = {"lean", "coq", "isabelle", "sml"}


def norm(t: str) -> str:
    return t.replace("\r\n", "\n").replace("\r", "\n")


def statement_errors(e: dict, texts: dict[str, str]) -> list[str]:
    """Statements verbatim from the code (fields.md; brief 2026-11-14 item 1). Skills and
    entries in markdown, latex or python are exempt: their statements are prose or node labels."""
    corpus, errs = S.corpus_of(texts), []
    items = [("parent", e.get("parent") or {})] + [(c.get("name") or "?", c) for c in e.get("children") or []]
    for name, c in items:
        st = c.get("statement")
        if st is None:
            if not (c.get("note") or "").strip():
                errs.append(f"statement of {name} is null without a note saying why")
        elif not S.verbatim(st, corpus):
            errs.append(f"statement of {name} is not verbatim from a copied file; copy it with "
                        f"statements.py (skills and markdown/latex/python entries are exempt)")
    return errs


def glue_check(e: dict, texts: dict[str, str]) -> tuple[str, str, list[str]]:
    """Does the glue cite each child? Returns (status, evidence, names missing).
    Subgoals made by a tactic have no name to cite and are counted, not checked."""
    sites = [s for s in e["sites"] if s.get("role") in ("parent", "skeleton")]
    cited, missing, sub = [], [], 0
    for c in e.get("children") or []:
        if c.get("subgoal"):
            sub += 1
            continue
        name = c.get("name") or ""
        where = None
        for s in sites:
            for k, line in enumerate(S.site_text(texts, s).splitlines()):
                if S.cites(name, line):
                    where = f"{s['path']}:{s['lines'][0] + k}"
                    break
            if where:
                break
        (cited.append(f"{name}@{where}") if where else missing.append(name))
    ev = (f"cited: {', '.join(cited) or 'none'}; subgoals (no name to cite): {sub}"
          + (f"; NOT cited: {', '.join(missing)}" if missing else ""))
    return ("fail" if missing else "pass"), ev, missing


def shape_errors(e: dict) -> list[str]:
    """Theorem-scale shape numbers are the lengths of the sites, declaration included
    (brief 2026-11-14 item 3)."""
    sh = e.get("shape") or {}
    if sh.get("scale") != "theorem":
        return []
    span = lambda s: s["lines"][1] - s["lines"][0] + 1
    par = [s for s in e["sites"] if s.get("role") == "parent"]
    kids = [span(s) for s in e["sites"] if s.get("role") == "child"]
    errs = []
    if par and sh.get("glue_lines") != span(par[0]):
        errs.append(f"shape.glue_lines is {sh.get('glue_lines')}; the parent site has {span(par[0])} lines")
    if sh.get("child_lines") != kids:
        errs.append(f"shape.child_lines is {sh.get('child_lines')}; the child sites have {kids} lines")
    return errs


def check(eid: str, strict: bool) -> list[str]:
    d = ENTRIES / eid
    errs = []
    try:
        e = read_json(d / "entry.json")
    except Exception as x:
        return [f"entry.json unreadable: {x}"]
    for k in REQUIRED:
        if k not in e:
            errs.append(f"missing field '{k}'")
    if errs:
        return errs
    if e["id"] != eid:
        errs.append(f"id '{e['id']}' does not match directory")
    stray = sorted(p.name for p in d.iterdir() if p.name not in ("README.md", "entry.json", "code"))
    if stray:
        errs.append(f"files other than README.md, entry.json and code/: {', '.join(stray)} (remove them)")
    if e["kind"] not in KINDS: errs.append(f"bad kind {e['kind']}")
    if e["status"] not in STATUSES: errs.append(f"bad status {e['status']}")
    if e["move"] not in MOVES: errs.append(f"bad move {e['move']}")
    sh = e.get("shape")
    if sh is not None:
        if not isinstance(sh, dict) or sh.get("scale") not in ("theorem", "tactic"):
            errs.append("shape.scale must be 'theorem' or 'tactic'")
        elif sh["scale"] == "theorem":
            for k in ("direct_lemmas", "depth", "glue_lines", "child_lines"):
                if k not in sh:
                    errs.append(f"shape.{k} missing")
            if not isinstance(sh.get("direct_lemmas"), int) or sh["direct_lemmas"] < 2:
                errs.append("a theorem-scale entry needs shape.direct_lemmas >= 2")
            if sum(1 for s in e["sites"] if s.get("role") == "child") < 2:
                errs.append("a theorem-scale entry needs at least 2 child sites")
    if not re.fullmatch(r"[0-9a-f]{40}", e["source"].get("commit", "")):
        errs.append("source.commit is not a full 40-hex commit hash")

    texts = {}
    for f in e["files"]:
        p = d / "code" / f["path"]
        if not p.exists():
            errs.append(f"file missing: code/{f['path']}"); continue
        b = p.read_bytes()
        if len(b) != f["bytes"] or sha256_bytes(b) != f["sha256"]:
            errs.append(f"file changed since copy: code/{f['path']}")
        texts[f["path"]] = norm(b.decode("utf-8", "replace"))
    for s in e["sites"]:
        t = texts.get(s["path"])
        if t is None:
            errs.append(f"site file not among files: {s['path']}"); continue
        lines = t.split("\n")
        a, b = s["lines"]
        if b > len(lines):
            errs.append(f"site {s['path']}:{a}-{b} outside file"); continue
        ex = "\n".join(lines[a - 1:b])
        if sha256_bytes(ex.encode("utf-8")) != s.get("excerpt_sha256"):
            errs.append(f"site excerpt hash mismatch {s['path']}:{a}-{b}")

    for c in e["claims"]:
        for k in ("n", "claim", "evidence_kind", "evidence"):
            if k not in c:
                errs.append(f"claim {c.get('n', '?')} lacks '{k}'")
        if c.get("evidence_kind") not in EVIDENCE_KINDS:
            errs.append(f"claim {c.get('n', '?')}: evidence_kind not in {EVIDENCE_KINDS}")
    for k, v in (e.get("checks") or {}).items():
        if isinstance(v, dict) and v.get("status") not in CHECK_STATUSES:
            errs.append(f"check {k}: status not in {CHECK_STATUSES}")

    rp = d / "README.md"
    if not rp.exists():
        errs.append("README.md missing")
    else:
        r = norm(rp.read_text(encoding="utf-8"))
        for sec in SECTIONS:
            if sec not in r:
                errs.append(f"README.md lacks section '{sec}'")
        corpus = "\n".join(texts.values())
        for m in re.finditer(r"^(`{3,})([a-z]*)\n(.*?)\n\1$", r, flags=re.S | re.M):
            if m[2] in PROVER_FENCES and m[3] not in corpus:
                errs.append(f"README code block ({m[2]}) is not verbatim from a copied file: "
                            f"{m[3][:60]!r}...")
    if strict and e["status"] != "deprecated":
        r_plain = re.sub(r"<!-- verification:start -->.*?<!-- verification:end -->", "",
                         norm(rp.read_text(encoding="utf-8")), flags=re.S) if rp.exists() else ""
        if "TODO" in r_plain:
            errs.append("README.md still contains TODO")
        if e["kind"] == "instance" and e["language"] in S.PROVER:
            errs += statement_errors(e, texts)
            _, _, missing = glue_check(e, texts)
            for m in missing:
                errs.append(f"child '{m}' is not cited by any parent or skeleton site (widen the parent "
                            f"site, add a skeleton site with new_entry.py --add-to, mark it a subgoal, or remove it)")
        errs += shape_errors(e)
        flat = __import__("json").dumps(e)
        if "TODO" in flat:
            errs.append("entry.json still contains TODO")
        if not e["claims"]:
            errs.append("no claims")
        if e["kind"] != "skill" and not e.get("parent"):
            errs.append("instance or anti-pattern without a parent")
    return errs


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("entry", nargs="?")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--strict", action="store_true")
    ap.add_argument("--record-glue", action="store_true",
                    help="record the glue-cites-children check of every prover instance")
    a = ap.parse_args()
    ids = sorted(p.name for p in ENTRIES.iterdir() if p.is_dir()) if a.all else [a.entry]
    if a.record_glue:
        return record_glue(ids)
    bad = 0
    for eid in ids:
        errs = check(eid, a.strict)
        print(f"{'FAIL' if errs else 'ok  '} {eid}")
        for x in errs:
            print(f"     - {x}")
        bad += bool(errs)
    sys.exit(1 if bad else 0)


def record_glue(ids: list[str]) -> None:
    from record_verdict import latest, record
    from set_status import render
    for eid in ids:
        e = read_json(ENTRIES / eid / "entry.json")
        if e["kind"] != "instance" or e["language"] not in S.PROVER or not e.get("children"):
            continue
        st, ev, _ = glue_check(e, S.load_texts(eid, e))
        record(eid, check="glue-cites-children", status=st, evidence=ev, by="validate_entry.py")
        render(eid, read_json(ENTRIES / eid / "entry.json"), latest(eid))
        print(f"{st:4} {eid}")


if __name__ == "__main__":
    main()
