"""Check one entry, or all, against the library's rules. No network.

  py.sh validate_entry.py ENTRY_ID|--all [--strict]

Checks: required fields and vocabularies; every listed file exists under
code/ with the recorded size and SHA-256; every site lies inside its file and
its excerpt hash matches; README.md has the required sections; every prover
code block in README.md appears verbatim in a copied file (so no code was
retyped or invented); claims are well formed. With --strict (required before
a status above draft) no TODO may remain. Exit status 1 if any entry fails.
"""
from __future__ import annotations

import argparse
import re
import sys

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
    if e["kind"] not in KINDS: errs.append(f"bad kind {e['kind']}")
    if e["status"] not in STATUSES: errs.append(f"bad status {e['status']}")
    if e["move"] not in MOVES: errs.append(f"bad move {e['move']}")
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
        if strict and "TODO" in r:
            errs.append("README.md still contains TODO")
    if strict:
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
    a = ap.parse_args()
    ids = sorted(p.name for p in ENTRIES.iterdir() if p.is_dir()) if a.all else [a.entry]
    bad = 0
    for eid in ids:
        errs = check(eid, a.strict)
        print(f"{'FAIL' if errs else 'ok  '} {eid}")
        for x in errs:
            print(f"     - {x}")
        bad += bool(errs)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
