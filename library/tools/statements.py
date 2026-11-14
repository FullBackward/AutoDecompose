"""Copy parent and child statements from the code, never retype them (fixes brief 2026-11-14, item 1).

  py.sh statements.py ENTRY_ID|all            show what would change
  py.sh statements.py ENTRY_ID|all --write    apply, and log it in provenance_log

For an instance in a prover language (lean, rocq, isabelle), every
parent.statement and children[].statement must occur, whitespace-normalised,
in one of the entry's copied files (validate_entry.py --strict). For each one
that does not, this tool:

  1. strips a gloss from the child's name ("h11 (witness existence)" -> "h11")
     and keeps the gloss in the child's "note";
  2. finds the declaration of that name in the copied files (theorem, lemma,
     def, have, Lemma, Definition, ...; the named site first) and copies its
     text up to where the proof starts (Lean ":=", Rocq ".", Isabelle
     "proof"/"by"/"using");
  3. if no declaration exists but the name is cited in a parent or skeleton
     site, the child is a lemma declared outside the copied files: statement
     null, with a note;
  4. otherwise the child is a subgoal made by a tactic inside the parent's
     proof (a case of mod_cases, a direction of an iff, a link of a calc):
     statement null, "subgoal": true, and the analyst's description kept in
     the note.

The functions here are also used by validate_entry.py.
"""
from __future__ import annotations

import argparse
import re

from common import ENTRIES, die, now, read_json, write_json

PROVER = ("lean", "rocq", "isabelle")
RUN = "fixes-2026-11-14"

DECL = {
    "lean": r"(?:theorem|lemma|def|abbrev|instance|example|structure|inductive|have|suffices|let)",
    "rocq": r"(?:Theorem|Lemma|Corollary|Proposition|Fact|Remark|Definition|Fixpoint|Example|Instance|assert)",
    "isabelle": r"(?:theorem|lemma|corollary|proposition|definition|fun|function|primrec|have|show|obtain)",
}
IDENT = r"[^\s()\[\]{}:,⟨⟩]+"


def norm_ws(s: str) -> str:
    return " ".join(s.split())


def corpus_of(texts: dict[str, str]) -> str:
    return " ".join(norm_ws(t) for t in texts.values())


def verbatim(stmt: str, corpus: str) -> bool:
    return norm_ws(stmt) in corpus


def strip_gloss(name: str) -> tuple[str, str]:
    """'h11 (witness existence)' -> ('h11', '(witness existence)'); a description stays whole."""
    m = re.fullmatch(rf"\s*({IDENT})\s*(\(.*\))?\s*", name or "")
    if m and m[2]:
        return m[1], m[2].strip()
    return (name or "").strip(), ""


def is_ident(name: str) -> bool:
    return bool(re.fullmatch(IDENT, name or ""))


def cites(name: str, text: str) -> bool:
    """NAME (its last dotted component) occurs as a whole identifier in TEXT."""
    n = name.split(".")[-1]
    return bool(n) and re.search(rf"(?<![\w']){re.escape(n)}(?![\w'])", text) is not None


def header_from(text: str, start: int, lang: str) -> str:
    rest = text[start:start + 6000]
    if lang == "lean":
        # the first ':=' at bracket depth 0 that does not belong to a 'let' line; this
        # skips auto-parameters '(h : P := by decide)' and 'let d := ...' in a statement
        ends, depth, i = [], 0, 0
        while i < len(rest) and not ends:
            ch = rest[i]
            if ch in "([{⟨":
                depth += 1
            elif ch in ")]}⟩":
                depth -= 1
            elif rest.startswith(":=", i) and depth <= 0:
                seg = rest[max(rest.rfind("\n", 0, i), rest.rfind(";", 0, i)) + 1:i]
                if not re.match(r"\s*(?:let|letI|haveI)\s", seg):
                    ends.append(i)
            elif rest.startswith("where", i) and depth <= 0 and re.match(r"(?<![\w'])where\b", rest[i:]) \
                    and (i == 0 or not (rest[i - 1].isalnum() or rest[i - 1] in "_'")):
                ends.append(i)
            i += 1
    elif lang == "rocq":
        ends = [m.start() + 1 for m in re.finditer(r"\.(?=\s)", rest)]
    else:
        ends = [m.start() for m in re.finditer(
            r"(?m)^\s*(?:proof|by|using|apply|unfolding|including|supply|sorry|oops)\b"
            r"|[ \t](?:by|using|unfolding)\s+[(\w]", rest)]
        ends = [e for e in ends if e > 0]
    return rest[:min(ends)].rstrip() if ends else ""


def find_declaration(name: str, lang: str, texts: dict[str, str], prefer: list[tuple[str, int, int]]):
    """Header text of NAME's declaration, searching the preferred site ranges first."""
    if not is_ident(name) or lang not in DECL:
        return None
    pat = re.compile(rf"{DECL[lang]}\s+{re.escape(name)}(?![\w'])")
    for path, a, b in prefer:
        t = texts.get(path)
        if t is None:
            continue
        lines = t.split("\n")
        off = len("\n".join(lines[:a - 1])) + (1 if a > 1 else 0)
        seg = "\n".join(lines[a - 1:b])
        m = pat.search(seg)
        if m:
            h = header_from(t, off + m.start(), lang)
            if h:
                return h
    for t in texts.values():
        m = pat.search(t)
        if m:
            h = header_from(t, m.start(), lang)
            if h:
                return h
    return None


def load_texts(eid: str, e: dict) -> dict[str, str]:
    out = {}
    for f in e["files"]:
        p = ENTRIES / eid / "code" / f["path"]
        if p.exists():
            out[f["path"]] = p.read_bytes().decode("utf-8", "replace").replace("\r\n", "\n")
    return out


def site_text(texts: dict[str, str], s: dict) -> str:
    t = texts.get(s["path"])
    if t is None:
        return ""
    a, b = s["lines"]
    return "\n".join(t.split("\n")[a - 1:b])


def glue_text(texts: dict[str, str], e: dict) -> str:
    return "\n".join(site_text(texts, s) for s in e["sites"] if s.get("role") in ("parent", "skeleton"))


def add_note(c: dict, text: str) -> None:
    c["note"] = (c["note"] + " " if c.get("note") else "") + text


def repair(eid: str, write: bool) -> list[str]:
    e = read_json(ENTRIES / eid / "entry.json")
    if e["kind"] != "instance" or e["language"] not in PROVER or e["status"] == "deprecated":
        return []
    texts = load_texts(eid, e)
    corpus, glue, lang = corpus_of(texts), glue_text(texts, e), e["language"]
    changes = []
    par = e.get("parent") or {}
    if par.get("statement") and not verbatim(par["statement"], corpus):
        sites = [(s["path"], *s["lines"]) for s in e["sites"] if s.get("role") == "parent"]
        h = find_declaration(par.get("name", ""), lang, texts, sites)
        if h:
            changes.append(f"parent {par.get('name')}: statement re-copied from code")
            par["statement"] = h
        elif par["statement"].strip() != "TODO":
            changes.append(f"parent {par.get('name')}: a goal inside a declaration, not a declaration")
            add_note(par, "The parent is a goal inside a larger proof (its site shows where), not a "
                          f"declaration; the analyst described it as: {par['statement']}")
            par["statement"] = None
        else:
            changes.append(f"parent {par.get('name')}: TODO left by an abandoned extraction (see item 5)")
    for c in e.get("children") or []:
        st = c.get("statement")
        old_name = c.get("name") or ""
        name, gloss = strip_gloss(old_name)
        if st is not None and verbatim(st, corpus):
            if not is_ident(name) and not c.get("subgoal"):
                changes.append(f"child {old_name!r}: named by a description, so a subgoal (statement kept)")
                c["subgoal"] = True
                add_note(c, "Subgoal made by a tactic inside the parent's proof; its name is a description, "
                            "not an identifier the glue could cite.")
            elif gloss and is_ident(name) and cites(name, glue) and not cites(old_name, glue):
                changes.append(f"child {old_name!r}: gloss moved from the name to the note")
                c["name"] = name
                add_note(c, f"Gloss moved from the name: {gloss}.")
            continue
        if st is None:
            continue
        child_sites = [(s["path"], *s["lines"]) for s in e["sites"]
                       if s.get("role") == "child" and s.get("name") in (name, old_name)]
        h = find_declaration(name, lang, texts, child_sites +
                             [(s["path"], *s["lines"]) for s in e["sites"] if s.get("role") in ("parent", "skeleton")])
        if h:
            changes.append(f"child {old_name!r}: statement re-copied from the declaration of {name}")
            if name != old_name:
                c["name"] = name
                add_note(c, f"Gloss moved from the name: {gloss}.")
            add_note(c, f"Analyst's paraphrase, replaced by the declaration's text: {st}")
            c["statement"] = h
        elif is_ident(name) and not gloss and cites(name, glue):
            changes.append(f"child {old_name!r}: cited by the glue but declared outside the copied files")
            if name != old_name:
                c["name"] = name
                add_note(c, f"Gloss moved from the name: {gloss}.")
            add_note(c, f"Declared outside the copied files (a project or library lemma); "
                        f"the analyst gave its statement as: {st}")
            c["statement"] = None
        else:
            changes.append(f"child {old_name!r}: a subgoal made inside the parent's proof")
            add_note(c, f"Subgoal made by a tactic inside the parent's proof, not a declaration; "
                        f"the analyst described it as: {st}")
            c["statement"] = None
            c["subgoal"] = True
    if changes and write:
        e.setdefault("provenance_log", []).append(
            {"field": "parent.statement,children", "agent_role": "fixer", "model": "statements.py",
             "run": RUN, "at": now(), "note": "; ".join(changes)})
        write_json(ENTRIES / eid / "entry.json", e)
    return changes


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("entry", help="entry id, or 'all'")
    ap.add_argument("--write", action="store_true")
    a = ap.parse_args()
    ids = sorted(p.name for p in ENTRIES.iterdir() if (p / "entry.json").exists()) \
        if a.entry == "all" else [a.entry]
    if a.entry != "all" and not (ENTRIES / a.entry / "entry.json").exists():
        die(f"no entry {a.entry}")
    for eid in ids:
        for ch in repair(eid, a.write):
            print(f"{eid}: {ch}")


if __name__ == "__main__":
    main()
