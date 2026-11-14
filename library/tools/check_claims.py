"""Decide machine-checkable claims without a model (protocol section 7, amended 2026-11-14).

  py.sh check_claims.py ENTRY_ID|all [--dry-run]

A claim of kind `check` may carry a "form" in one of five shapes; this tool
evaluates it against the entry's copied files under code/ and records the
verdict with record_verdict.py, by check_claims.py:

  declared(NAME, PATH, A-B)    a declaration named NAME starts in lines A-B of PATH
  cites(SITE, NAME)            NAME occurs, as a whole identifier, in the lines of SITE
  no_sorry(PATH, A-B)          no sorry/admit/Admitted/axiom (comments ignored) in the range
  count(NAME, N, PATH_GLOB)    NAME occurs N times, as a whole identifier, in the matching files
  lines(SITE, N)               the site is N lines long

SITE is a site's name, its role ("parent", "skeleton": all such sites), or
PATH:A-B. PATH is relative to code/. A claim without a form, or whose form
does not parse or names a missing file or site, is left for the model
verifier and reported here. A form decides only what it states: the claim's
prose must say no more than its form.
"""
from __future__ import annotations

import argparse
import fnmatch
import re

import statements as S
from common import ENTRIES, die, language_of, read_json
from sorry_scan import TOKENS, strip_comments

FORM = re.compile(r"^\s*(declared|cites|no_sorry|count|lines)\s*\((.*)\)\s*$", re.S)
ARITY = {"declared": 3, "cites": 2, "no_sorry": 2, "count": 3, "lines": 2}


class Unusable(Exception):
    pass


def span(arg: str) -> tuple[int, int]:
    m = re.fullmatch(r"\s*L?(\d+)\s*(?:-\s*L?(\d+))?\s*", arg)
    if not m:
        raise Unusable(f"bad line range {arg!r}")
    a = int(m[1]); b = int(m[2] or m[1])
    return a, b


def file_text(texts: dict, path: str) -> str:
    path = path.strip().strip("`'\"")
    if path not in texts:
        raise Unusable(f"no copied file {path!r}")
    return texts[path]


def site_texts(e: dict, texts: dict, ref: str) -> list[tuple[str, int, int, str]]:
    ref = ref.strip().strip("`'\"")
    m = re.fullmatch(r"(.+):(\d+)-(\d+)", ref)
    if m:
        t = file_text(texts, m[1])
        a, b = int(m[2]), int(m[3])
        return [(m[1], a, b, "\n".join(t.split("\n")[a - 1:b]))]
    hits = [s for s in e["sites"] if s.get("name") == ref] or \
           [s for s in e["sites"] if s.get("role") == ref]
    if not hits:
        raise Unusable(f"no site named or with role {ref!r}")
    return [(s["path"], *s["lines"], S.site_text(texts, s)) for s in hits]


def decide(e: dict, texts: dict, form: str) -> tuple[str, str]:
    m = FORM.match(form or "")
    if not m:
        raise Unusable("no form, or not one of declared/cites/no_sorry/count/lines")
    kind, args = m[1], [x.strip() for x in m[2].split(",")]
    if len(args) != ARITY[kind]:
        raise Unusable(f"{kind} takes {ARITY[kind]} arguments, got {len(args)}")
    if kind == "declared":
        name, path, rng = args
        t = file_text(texts, path); a, b = span(rng)
        lang = language_of(path)
        if lang not in S.DECL:
            raise Unusable(f"no declaration syntax for {lang}")
        pat = re.compile(rf"{S.DECL[lang]}\s+{re.escape(name.strip('`'))}(?![\w'])")
        lines = t.split("\n")
        for k in range(a, min(b, len(lines)) + 1):
            if pat.search(lines[k - 1]):
                return "verified", f"{kind}: {name} is declared at {path}:{k}"
        return "refuted", f"{kind}: no declaration of {name} in {path}:{a}-{b}"
    if kind == "cites":
        ref, name = args
        for path, a, b, txt in site_texts(e, texts, ref):
            for k, line in enumerate(txt.split("\n")):
                if S.cites(name.strip("`"), line):
                    return "verified", f"{kind}: {name} occurs at {path}:{a + k}"
        return "refuted", f"{kind}: {name} does not occur in site {ref}"
    if kind == "no_sorry":
        path, rng = args
        lang = language_of(path.strip("`"))
        if lang not in TOKENS:
            raise Unusable(f"no closing tokens defined for {lang}")
        a, b = span(rng)
        body = "\n".join(strip_comments(file_text(texts, path), lang).split("\n")[a - 1:b])
        found = [tok for tok in TOKENS[lang] if re.search(rf"(?<![\w'.]){re.escape(tok)}(?![\w'])", body)]
        return (("refuted", f"{kind}: {', '.join(found)} in {path}:{a}-{b}") if found
                else ("verified", f"{kind}: none of {', '.join(TOKENS[lang])} in {path}:{a}-{b}"))
    if kind == "count":
        name, n, glob = args
        if not n.isdigit():
            raise Unusable(f"count needs an integer, got {n!r}")
        files = [p for p in texts if fnmatch.fnmatch(p, glob.strip("`'\""))]
        if not files:
            raise Unusable(f"no copied file matches {glob!r}")
        c = sum(len(re.findall(rf"(?<![\w']){re.escape(name.strip('`'))}(?![\w'])", texts[p])) for p in files)
        return ("verified" if c == int(n) else "refuted"), f"{kind}: {name} occurs {c} times in {len(files)} file(s) matching {glob}"
    ref, n = args
    if not n.isdigit():
        raise Unusable(f"lines needs an integer, got {n!r}")
    sites = site_texts(e, texts, ref)
    got = [b - a + 1 for _, a, b, _ in sites]
    ok = int(n) in got
    return ("verified" if ok else "refuted"), f"{kind}: site {ref} has {', '.join(map(str, got))} lines"


def run(eid: str, dry: bool) -> list[str]:
    e = read_json(ENTRIES / eid / "entry.json")
    texts = S.load_texts(eid, e)
    out = []
    from record_verdict import latest, record
    have = latest(eid)
    for c in e["claims"]:
        if c.get("evidence_kind") != "check" or not c.get("form"):
            continue
        if have.get(("claim", str(c["n"])), {}).get("by") == "check_claims.py":
            continue
        try:
            verdict, ev = decide(e, texts, c["form"])
        except Unusable as x:
            out.append(f"claim {c['n']}: left for the verifier ({x})")
            continue
        out.append(f"claim {c['n']}: {verdict} ({ev})")
        if not dry:
            record(eid, claim=c["n"], verdict=verdict, evidence=f"{c['form']} -> {ev}", by="check_claims.py")
    if out and not dry:
        from set_status import render
        render(eid, read_json(ENTRIES / eid / "entry.json"), latest(eid))
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("entry", help="entry id, or 'all'")
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()
    ids = sorted(p.name for p in ENTRIES.iterdir() if (p / "entry.json").exists()) \
        if a.entry == "all" else [a.entry]
    if a.entry != "all" and not (ENTRIES / a.entry / "entry.json").exists():
        die(f"no entry {a.entry}")
    for eid in ids:
        for line in run(eid, a.dry_run):
            print(f"{eid}: {line}")


if __name__ == "__main__":
    main()
