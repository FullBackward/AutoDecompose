"""Measures on a fixed sample of accepted proof files of Formalpedia.

  python -I -X utf8 sample_proofs.py SAMPLE_JSONL DIR_WITH_FILES [--out sample-measures.json]

SAMPLE_JSONL is `sample.jsonl` in this folder: one line per sampled proof, with the path of the file in the
Formalpedia repository and the theorem cards that the arrows give as its children. The sample is the first
accepted proof of every 1022-nd proved theorem in name order (300 proofs). DIR_WITH_FILES holds the files as
000.lean, 001.lean, ... in the order of the lines.

The arrows of Formalpedia show which cards a proof file imports. They do not show two things, which this
script measures on the text of the files:
  1. the helper lemmas that a proof file states for itself, before its final `theorem solution`;
  2. whether the proof text names each theorem card that it imports.

A name counts as named when its last dotted component occurs as a whole component of some identifier in the
text after the import lines. This can count a local name by accident, so "not named" is a lower bound.
Python 3.13 standard library only; no clock, no network, no randomness.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

DECL = re.compile(r"^[ \t]*(?:@\[[^\]\n]*\][ \t\n]*)*(?:(?:private|protected|noncomputable|nonrec|unsafe)[ \t]+)*"
                  r"(theorem|lemma)[ \t]+([^\s:({\[]+)", re.M)
DEFN = re.compile(r"^[ \t]*(?:@\[[^\]\n]*\][ \t\n]*)*(?:(?:private|protected|noncomputable|nonrec|unsafe)[ \t]+)*"
                  r"(def|abbrev|structure|class|inductive|instance)\b", re.M)
IDENT = re.compile(r"[A-Za-z_À-￿][A-Za-z0-9_'À-￿!?.]*")
IMPORT = re.compile(r"^import[ \t]+(\S+)", re.M)


def quantiles(xs: list) -> dict | None:
    xs = sorted(xs)
    if not xs:
        return None
    q = lambda p: xs[min(len(xs) - 1, int(round(p * (len(xs) - 1))))]
    return {"n": len(xs), "min": xs[0], "q1": q(.25), "median": q(.5), "q3": q(.75), "p90": q(.9), "max": xs[-1],
            "mean": round(sum(xs) / len(xs), 3)}


def is_final(name: str) -> bool:
    """The final declaration is written `solution`, `_root_.solution` or `solution.{u}`."""
    name = name.removeprefix("_root_.")
    return name == "solution" or name.startswith("solution.{")


def strip_comments(t: str) -> str:
    t = re.sub(r"/-.*?-/", " ", t, flags=re.S)
    return re.sub(r"--[^\n]*", "", t)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("sample", type=Path)
    ap.add_argument("files", type=Path)
    ap.add_argument("--out", type=Path)
    a = ap.parse_args()
    rows = [json.loads(line) for line in open(a.sample, encoding="utf-8")]
    per, missing = [], 0
    for i, r in enumerate(rows):
        p = a.files / f"{i:03d}.lean"
        if not p.exists():
            missing += 1
            continue
        raw = p.read_text(encoding="utf-8", errors="replace")
        text = strip_comments(raw)
        imports = IMPORT.findall(text)
        body = IMPORT.sub("", text)
        found = list(DECL.finditer(body))
        decls = [m.group(2) for m in found]
        local = [d for d in decls if not is_final(d)]
        comps = set()
        for tok in IDENT.findall(body):
            comps.update(tok.split("."))
        kids = r["children"]
        named = [k for k in kids if k.split(".")[-1] in comps]
        # the text of each declaration runs to the start of the next one; a declaration can name earlier ones
        last = [d.removeprefix("_root_.").split(".{")[0].split(".")[-1] for d in decls]
        height, direct_local, direct_card = [0] * len(found), None, None
        for j, m in enumerate(found):
            span = body[m.end(): found[j + 1].start() if j + 1 < len(found) else len(body)]
            cs = set()
            for tok in IDENT.findall(span):
                cs.update(tok.split("."))
            deps = [i for i in range(j) if not is_final(decls[i]) and last[i] in cs]
            height[j] = 1 + max(height[i] for i in deps) if deps else 0
            if is_final(decls[j]):
                direct_local = len(deps)
                direct_card = sum(1 for k in kids if k.split(".")[-1] in cs)
        fin = [j for j in range(len(found)) if is_final(decls[j])]
        per.append({
            "direct_local": direct_local, "direct_card": direct_card,
            "height_in_file": height[fin[-1]] if fin else None,
            "lines": raw.count("\n") + 1,
            "local_lemmas": len(local),
            "local_definitions": len(DEFN.findall(body)),
            "have": len(re.findall(r"(?<![A-Za-z0-9_'.])have\b", body)),
            "card_children": len(kids),
            "card_children_named": len(named),
            "imports_theorem_cards": sum(1 for x in imports if x.startswith("Theorems.")),
            "imports_definition_cards": sum(1 for x in imports if x.startswith("Definitions.")),
            "imports_all_of_mathlib": any(x == "Mathlib" for x in imports),
            "has_solution_decl": any(is_final(d) for d in decls),
            "source_kind": r.get("source_kind"),
        })
    n = len(per)
    with_local = [x for x in per if x["local_lemmas"] > 0]
    no_card = [x for x in per if x["card_children"] == 0]
    with_card = [x for x in per if x["card_children"] > 0]
    kids_total = sum(x["card_children"] for x in per)
    kids_named = sum(x["card_children_named"] for x in per)
    out = {
        "proof_files": n, "files_not_found": missing,
        "files_with_a_solution_declaration": sum(1 for x in per if x["has_solution_decl"]),
        "lines": quantiles([x["lines"] for x in per]),
        "local_helper_lemmas": quantiles([x["local_lemmas"] for x in per]),
        "files_with_a_local_helper_lemma": len(with_local),
        "local_helper_lemmas_in_those_files": quantiles([x["local_lemmas"] for x in with_local]),
        "local_definitions": quantiles([x["local_definitions"] for x in per]),
        "have_steps": quantiles([x["have"] for x in per]),
        "card_children": quantiles([x["card_children"] for x in per]),
        "lemmas_in_total (local helper lemmas + card children)": quantiles([x["local_lemmas"] + x["card_children"] for x in per]),
        "files_with_no_card_child": len(no_card),
        "of_these_with_a_local_helper_lemma": sum(1 for x in no_card if x["local_lemmas"] > 0),
        "files_with_a_card_child": len(with_card),
        "of_these_with_a_local_helper_lemma_too": sum(1 for x in with_card if x["local_lemmas"] > 0),
        "files_with_neither": sum(1 for x in per if x["local_lemmas"] == 0 and x["card_children"] == 0),
        "lines_of_files_with_neither": quantiles([x["lines"] for x in per if x["local_lemmas"] == 0 and x["card_children"] == 0]),
        "card_children_in_all_files": kids_total,
        "card_children_that_the_text_names": kids_named,
        "card_children_that_the_text_does_not_name": kids_total - kids_named,
        "files_with_a_card_child_that_the_text_does_not_name": sum(1 for x in per if x["card_children_named"] < x["card_children"]),
        "final_proof: local helper lemmas that its own text names": quantiles([x["direct_local"] for x in per if x["direct_local"] is not None]),
        "final_proof: card children that its own text names": quantiles([x["direct_card"] for x in per if x["direct_card"] is not None]),
        "final_proof: lemmas that its own text names (local + card)": quantiles(
            [x["direct_local"] + x["direct_card"] for x in per if x["direct_local"] is not None]),
        "final_proof: the same, for files with one or more such lemmas": quantiles(
            [x["direct_local"] + x["direct_card"] for x in per if x["direct_local"] is not None and x["direct_local"] + x["direct_card"] > 0]),
        "height of the final proof above the local helper lemmas": quantiles([x["height_in_file"] for x in per if x["height_in_file"] is not None]),
        "the same, for files with a local helper lemma": quantiles(
            [x["height_in_file"] for x in per if x["height_in_file"] is not None and x["local_lemmas"] > 0]),
        "arrow_count_equals_import_count_in_files": sum(1 for x in per if x["card_children"] == x["imports_theorem_cards"]),
        "files_that_import_all_of_mathlib": sum(1 for x in per if x["imports_all_of_mathlib"]),
    }
    text = json.dumps(out, ensure_ascii=False, indent=1)
    if a.out:
        a.out.write_text(text + "\n", encoding="utf-8", newline="\n")
    sys.stdout.write(text + "\n")


if __name__ == "__main__":
    main()
