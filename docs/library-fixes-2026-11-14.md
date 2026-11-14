# Library fixes: a brief for the agent that applies them

AutoDecompose, 2026-11-14. Written by the harness author after reading
`library/` as it stood at commit `7618b40` (91 entries, pilots 1 and 2 of
2026-11-12). This brief lists the defects found, the evidence for each, the
change that fixes it and how to show it is fixed. Everything here runs with
the Python standard library and the copied files already in the repository:
*no model call, no prover, no network fetch is needed for any item*, and none
may be made without the owner's go-ahead (README convention).

Read first: `library/README.md` (layout, tools, statuses),
`library/protocol.md` §3, §6, §7 (moves, gates, evidence kinds),
`.claude/skills/harvest-decompositions/references/fields.md` (every field of
`entry.json`). Run every tool as `library/tools/py.sh library/tools/<tool>.py`
from the repository root.

## 0. Rules for this task

1. Never edit anything under `library/entries/<id>/code/`; those files are
   byte-identical copies of upstream and `check_provenance.py` compares them.
2. Never retype code into an entry. Where a statement must be corrected, copy
   it from the file under `code/` with a tool, not by hand.
3. The ledgers (`library/ledger/*.jsonl`) and `library/checks/<id>.json` are
   append-only; record changes with `ledger.py` and `record_verdict.py`,
   never by rewriting a line.
4. `library/protocol.md` changes only by a dated amendment at its end.
5. One logical change per commit, full message, with the co-author trailer
   `Co-Authored-By: <your model name> <noreply@anthropic.com>`; the owner
   pushes.
6. Rebuild the index after any change to an entry's status or fields:
   `build_index.py`. Validate every touched entry with
   `validate_entry.py <id> --strict`.
7. Items 1 to 5 are the deliverable. Items 6 and 7 are plans for the next
   harvest run and need only text changes; do not run a harvest.

## 1. Statements must be verbatim (fields.md says so; 100 of 433 are not)

**Defect.** `fields.md` requires `parent.statement` and each
`children[].statement` "verbatim from the code". The validator
(`validate_entry.py`) checks that README code blocks are verbatim from a
copied file but never checks these two fields. Analysts paraphrased: 100 of
433 statements across the 91 entries are not substrings of the entry's copied
files after whitespace normalisation. Examples:

- `isabelle-calc-chain-afp-4d3178de`, child `fact_ge_power`: the statement
  carries a gloss `(from "fact n0 >= c ^ n0", "c <= n0 + 1", "n >= n0")`.
- `isabelle-extract-have-munkres-isabelle-8aac79ad`, children
  `Lemma_40_1_step2`, `Lemma_40_1_step3`: `(under the same hReg/hBasis/hCLF)`.
- The two `latex-blueprint-node-*` entries: statements are English
  paraphrases of LaTeX nodes.

**How it was measured** (reproduce before and after):

```python
import json, glob, os
bad = tot = 0
for f in sorted(glob.glob("library/entries/*/entry.json")):
    e = json.load(open(f)); d = f.rsplit("/", 1)[0]
    corpus = " ".join(" ".join(open(p, errors="replace").read().split())
                      for p in glob.glob(d + "/code/**/*", recursive=True) if not os.path.isdir(p))
    sts = [e["parent"]["statement"]] if e.get("parent") and e["parent"].get("statement") else []
    sts += [c["statement"] for c in e.get("children", []) if c.get("statement")]
    for s in sts:
        tot += 1
        if " ".join(s.split()) not in corpus:
            bad += 1; print(os.path.basename(d), s[:120])
print(bad, "/", tot)
```

**Fix.**

1. Add the test to `validate_entry.py`: in `--strict` mode, every
   `parent.statement` and `children[].statement` of an `instance` entry whose
   `language` is `lean`, `rocq` or `isabelle` must occur, whitespace-normalised,
   in one of the entry's copied files. Report the offending name. Entries of
   kind `skill`, and entries whose language is `markdown`, `python` or `latex`,
   are exempt (their "statements" are prose or node labels); say so in the
   error text and in `fields.md`.
2. Repair the failing entries: replace each paraphrased statement by the
   declaration's text copied from the file under `code/` (the site's line
   range tells you where). Move any gloss the analyst added into
   `intent` or `consequences`, where prose is allowed. Where a child is not
   declared in any copied file (a lemma from the project's library the
   analyst named as a child), keep the name, set the statement to the text
   found in the file if present, otherwise mark the child
   `"statement": null` and add a `"note"` saying where it is declared; the
   validator accepts `null` with a note.
3. Each repaired entry keeps its status only if its claims still hold as
   written; if a claim quoted the paraphrase, rewrite the claim and record
   a fresh verdict with `record_verdict.py ... --by fixer-2026-11-14`.

**Done when** the script above prints `0 / N` for the non-exempt entries and
`validate_entry.py --strict` passes on all 91.

## 2. The glue must cite its children (50 of 322 do not)

**Defect.** For an instance, the parent's site lines (the glue) should name
each child; otherwise the decomposition described is not the one the code
performs. 50 of 322 children are not named in the parent's site range. Part
of that is legitimate: the `latex-blueprint-node-*` entries have a LaTeX
parent whose `\uses{}` list names nodes, not lemma names, and some Rocq
children are reached through `apply` chains in a different range. The rest
are either a wrong site range (the parent range stops before the `exact`
lines) or a child that is not a child.

**How it was measured:**

```python
import json, glob, os
miss = tot = 0
for f in sorted(glob.glob("library/entries/*/entry.json")):
    e = json.load(open(f)); d = f.rsplit("/", 1)[0]
    ps = [s for s in e["sites"] if s.get("role") == "parent"]
    if not ps or not e.get("children") or e["language"] not in ("lean", "rocq", "isabelle"):
        continue
    s = ps[0]; a, b = s["lines"]
    glue = "\n".join(open(f"{d}/code/{s['path']}", errors="replace").read().split("\n")[a-1:b])
    for c in e["children"]:
        tot += 1
        if c.get("name") and c["name"].split(".")[-1] not in glue:
            miss += 1; print(os.path.basename(d), c["name"], a, b)
print(miss, "/", tot)
```

**Fix.**

1. Add a strict-mode check to `validate_entry.py` for prover-language
   instances: each child's name (its last dotted component) must occur in the
   text of a site with role `parent` or `skeleton`. For a child that the glue
   reaches only through another site, the entry may list that site with role
   `skeleton`; the check then passes.
2. Repair each failing entry by one of: widening the parent site to the
   lines that cite the child (add a site through the same `new_entry.py`
   excerpt mechanism, never by editing the hash by hand; if `new_entry.py`
   cannot add a site to an existing entry, add that ability to it); adding
   a `skeleton` site; or removing the child and the claims that depended on
   it. Record what you did in the entry's `provenance_log`.
3. Record the outcome as the entry's first real tool-established check:
   `record_verdict.py <id> --check glue-cites-children --status pass|fail --evidence "<names and lines>" --by validate_entry.py`.
   Add `glue-cites-children` to the check keys the README's status table and
   `set_status.py` know about; `verified` should require it to pass for
   prover-language instances.

**Done when** the script prints `0 / N` for prover-language instances, or
every remaining miss is covered by a `skeleton` site.

## 3. Shape numbers derived from the sites, not typed

**Defect.** `shape.glue_lines` and `shape.child_lines` are typed by the
analyst. The PFR correctness reviewer already found one off-by-four
(`closed_by` says a 102-line proof, the range is 98). Nothing recomputes them.

**Fix.** In `validate_entry.py` (strict), for a theorem-scale entry compute
`glue_lines` as the length of the parent site's range and `child_lines` as
the lengths of the child sites' ranges in order, and refuse a mismatch with
the typed values. Then run it over the 54 theorem-scale entries and correct
the typed numbers to the computed ones (this is a field edit, not a code
edit). If an analyst's `child_lines` list counted proof lines rather than
the site range, prefer the site range and say so in `fields.md`: "the lines
of the site, declaration included".

**Done when** all 54 pass and `fields.md` says how the numbers are counted.

## 4. The sorry scan as a recorded check

**Defect.** Exclusion E3 (no `sorry`, `admit`, `Admitted`, `axiom` added to
close a goal in the dependency cone) is applied by the analyst's eye and
appears only as a claim in some entries. It is a text search over the copied
files and can be a tool check.

**Fix.** Add `library/tools/sorry_scan.py <id>`: scan every file under
`code/` for the tokens (`sorry` in Lean and Isabelle, `admit`, `Admitted`,
`axiom` in Rocq and Lean; `oops` in Isabelle is a non-closing abort and is
listed, not failed), ignoring line comments and `--`/`(* *)` comment blocks
as best a regex can, and record
`record_verdict.py <id> --check sorry-scan --status pass|fail --evidence "<file:line list or 'none'>" --by sorry_scan.py`.
A hit inside the parent or a child site range fails; a hit elsewhere in a
copied file is reported in the evidence and does not fail (the files are
copied whole, and other theorems in them may be unfinished). Run it over all
91 entries; promote nothing on its own account, but add the key to the
status table and make `verified` require `sorry-scan` to be recorded.

**Done when** every `checks/<id>.json` has a `sorry-scan` record.

## 5. Duplicates merged before promotion

**Defect.** `reports/dedupe.json` already clusters
`lean-case-split-flt-anthropic-22d1c0d8` with `-f782b482`,
`lean-statement-object-flt-anthropic-afa74779` with `-b51da0fb`, and
`lean-suffices-or-strengthen-numina-putnam2025-3fe390a3` with `-687e778f`.
The three IMO 2026 Q4 iff-split entries
(`lean-iff-split-axiom-imo2026-5ffbca5d`, `lean-iff-split-dirac-imo2026-ff8df4eb`,
`lean-iff-split-mechmath-imo2026-75bedf39`) are the same decomposition of the
same statement from three agent-made repositories and are not clustered,
because the dedupe keys are location, content hash, normalised parent
statement and move+goal-shape, and the three repositories differ in all four
at the character level.

**Fix.**

1. In each listed cluster keep the entry with the highest status (then the
   more complete one), list the others under its `known_uses` with their
   ids, and deprecate them with
   `set_status.py <id> deprecated --reason "duplicate of <kept id>"`.
   For the IMO 2026 Q4 trio, keep one and list the other two as known uses:
   three independent repositories reaching the same split is itself a
   `known-use` claim worth adding to the kept entry.
2. Make `set_status.py` refuse `verified` or `accepted` for an entry that
   appears in a cluster of `reports/dedupe.json` with another non-deprecated
   entry, unless the other is listed in its `known_uses`.
3. Add to `dedupe.py` a fifth key: the problem identity for competition
   sources, taken from the path (`Imo2026/Q4`, `IMO2026/Q4`, `imo2026_q4`
   normalised to `imo2026-q4`) joined with the move; report those clusters
   under `"problem+move"`.

**Done when** `dedupe.py` reports no cluster containing two non-deprecated
entries that do not reference each other, and `INDEX.md` lists the
deprecated ones last.

## 6. Cheaper verification: checkable `check` claims (plan only)

**Finding.** In pilot-2 the verifier role cost 90 of 179 CNY over 238 calls
(`reports/pilot-2/calls.jsonl`, field `role`), reading whole files on the
pro model to judge claims that are line-number lookups. 171 of the 390 claims
in the library are of kind `check`.

**Change to make in text, for the next run.** Amend `protocol.md` §7 and
`fields.md` so that a claim of kind `check` is written in one of a few
machine-checkable forms, each with its evidence as a locator:

- `declared(NAME, PATH, A-B)`: a declaration named NAME starts in lines A-B;
- `cites(PARENT_SITE, NAME)`: NAME occurs in the parent's site lines;
- `no_sorry(PATH, A-B)`: no closing-by-sorry token in the range;
- `count(NAME, N, PATH_GLOB)`: NAME occurs N times in the matching files;
- `lines(SITE, N)`: the site is N lines long.

Add `library/tools/check_claims.py <id>` that evaluates these forms against
`code/` and records a verdict with `--by check_claims.py`. Then the model
verifier is briefed only with the `author-statement`, `measurement` and
`known-use` claims, and the workflow (`.claude/workflows/harvest-library.js`,
`library/tools/run_harvest.py`) passes it excerpts, not whole files. Do not
rewrite the 171 existing claims in this task; the new form applies from the
next run, and the old claims keep their recorded verdicts.

## 7. Recall: site finding from published structure (plan only)

**Finding.** Gold recall was 7/30 in pilot-1 and 12/24 in pilot-2
(`reports/*/summary.json`, `gold_recall`). The flow report shows 0 queries
and 0 candidates, so discovery (protocol §5, strategies A and B) never ran;
the cap of three sites per shard left the AFP with one entry over eight
shards and missed a strongpnt blueprint node and the Mathlib AbelRuffini
witness, both reachable from the project's own structure.

**Change to make in text, for the next run.** Amend protocol §6 phase 2b and
the site-finder brief in `references/briefs.md`:

- for a source with a blueprint, list sites from the `\uses{}` graph first
  (every node with two or more `\uses` targets is a theorem-scale candidate),
  then grep;
- for Mathlib `Archive/` and compfiles, one theorem per file: the file's
  main theorem is the candidate, its named lemmas the children;
- for the AFP and `l4v`, shard by session (`ROOT`) and by file, with a site
  budget per shard scaled by file count (say one site per 400 lines, minimum
  3, maximum 15) instead of a flat cap;
- the critic's `next_batch` list in `reports/pilot-2/summary.json` is the
  work order for the gold-missed sources.

Record both amendments under `protocol.md` "Amendments" with today's date.

## 8. Shape statistics in the index (small, do it)

Over the 54 theorem-scale entries, `child_lines` has quartiles 3, 10 and 29
(maximum 521), `glue_lines` 8, 14 and 30, `direct_lemmas` 2, 4 and 6, `depth`
2, 3 and 4. These are the first empirical sizes of a student task for
AutoDecompose. Add a "Shape of theorem-scale entries" table to
`reports/flow.md` in `build_index.py`: per language and overall, the count
and the quartiles of each of the four numbers, computed from the (now
derived, item 3) shape fields, accepted entries and all entries separately.

## 9. One stale critic item, for the record

The pilot-2 critic lists six entries "still carrying a refuted claim". Their
claim numbering has gaps (for example `lean-calc-chain-strongpnt-570bdcdb`
has claims 1, 2, 3, 4, 6), so the refuted claims were removed as the protocol
asks and `set_status.py` found no refuted verdict on a remaining claim. No
action; if you touch the critic's prompt, have it check the entry's current
claim list against the latest verdict per claim, not the ledger history.

## 10. Order of work and what to report

1. Items 1 and 2 (validator checks, then repairs), one commit for the tool
   change and one for the repaired entries.
2. Item 3, then 4, then 5, each one tool commit and one data commit.
3. Item 8, with the index rebuilt.
4. Items 6 and 7 as protocol amendments and brief edits.

Report, in `library/reports/fixes-2026-11-14.md`: the before and after
counts for items 1, 2 and 3; the number of entries whose status changed and
why; the clusters merged; the shape table; anything from this brief you
judged wrong, with the evidence. Do not change an entry's claims to make a
check pass; if a check fails and the claim is wrong, the claim goes, not the
check.
