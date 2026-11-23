# Features of the library's entries

Features of each entry of `library/entries/`, computed by code from the entry's own files. No model
takes part, so a rerun gives the same bytes. Two tools write them:

| Tool | Writes | Unit | Documented in |
|---|---|---|---|
| `tools/features/feature_graph.py` | `graphs.jsonl` (nodes and edges), `graph-features.jsonl` (94 flat features) | declarations of the copied files, and which mentions which | [graph.md](graph.md) |
| `tools/features/feature_terms.py` | `term-features.jsonl` (statement skeletons, parent-to-child relations, proof steps, move detectors, 138 flat features) | the inside of a statement and of a proof | [terms.md](terms.md) |

Every file has one line per entry, all 229 entries, sorted by id. The two tools share no code.

## Reproducing

```
library/tools/py.sh library/tools/features/feature_graph.py --all      # writes the two graph files
library/tools/py.sh library/tools/features/feature_terms.py --all      # writes term-features.jsonl
library/tools/py.sh library/tools/features/feature_graph.py --check    # recompute, exit 1 on any difference
library/tools/py.sh library/tools/features/feature_terms.py --check
```

Both use the Python standard library only and read nothing but `library/entries/`. Each takes about
15 seconds. `--self-test` runs the built-in cases of each lexer and detector. Each record carries
the versions of the code that wrote it and an `input_digest`: SHA-256 over `entry.json` (CRLF read
as LF) and the recorded hashes of the entry's files. The two tools compute the same digest, so a
row of one joins to the row of the other on `id` and `input_digest`, and a row whose digest no
longer matches its entry is stale. The three `.jsonl` files are marked `-text` in `.gitattributes`
so that their bytes do not depend on the checkout.

Whoever changes an extractor raises its version, reruns `--all` and, for `feature_terms.py`,
`--write-report`, and commits code and output together.

## Looking at the graphs

```
library/tools/py.sh library/tools/features/graph_viewer.py      # writes features/graph-viewer.html
```

The page opens in a browser without a server. The left rail lists the 199 entries that have a
graph; the right pane draws the chosen one from left to right, the parent first, with an arrow
from each declaration to those its text names. Above the drawing the page gives the entry's
intent and its claims, each with the kind of evidence and the latest verdict from
`checks/<id>.json`: that is the entry's record of why it is a good decomposition. The page is
generated from `graphs.jsonl`, `graph-features.jsonl`, the entries and the checks, so it is
git-ignored; rebuild it after any of them changes. Its layout and script are in
`tools/features/graph_viewer_template.html`.

## What a feature is evidence of

Each feature is documented with a tier and a class.

- **Tier.** T0 is read from `entry.json`. T1 is computed from the copied source text by a lexer. T2
  would come from the prover: elaborated terms and real dependencies. Nothing here is T2, because
  no prover toolchain was available; both documents end with a T2 design whose statements about
  tools are unverified. A T1 edge is a token that names a declaration, and a T1 "head" or
  "detector" is a token pattern. Neither is a semantic fact.
- **Class.** A *goal* feature can be computed from the parent statement and its context before any
  decomposition exists; these are the predictors. A *decomposition* feature needs the children or
  the proof; these are outcomes. *Meta* features describe the record.

Entries in LaTeX, Markdown and Python (30 of 229) have T0 features only; the code-derived ones are
null with a reason code.

## Where the two tools and the validator count differently

"How many children does the glue cite" has three definitions in the library.

| Counter | Reads | Counts a child when |
|---|---|---|
| `glue_check` in `validate_entry.py` | the whole text of the parent and skeleton sites | its name occurs on any line |
| `d_glue_children_cited` (`feature_terms.py`) | identifiers in the proof bodies of those sites | its name is a dotted component of one |
| `fanout_cited`, `fanout_cited_with_skeleton` (`feature_graph.py`) | tokens of the parent declaration, outside the child's own declaration | a token resolves to the child |

They agree on all but a few entries, and each disagreement is a difference of definition:
`lean-interface-lemma-carleson-50fa619f` (the parent site is the list of the eleven lemmas
themselves), `rocq-per-callee-lemma-coq-library-undecidability-683e3c0c` (the children are named by
a `Hint Resolve` line and used by `eauto`), and two entries whose child is a `have` step that no
later line mentions (`lean-key-invariant-compfiles-f9a0ece2`, `lean-key-invariant-seed-prover-ccd41e1d`).
The validator's count is the most lenient, the graph's the strictest.

## What has been checked, and what has not

The review of 2026-11-15 (`docs/features-and-literature-review-2026-11-15.md`) reran both tools
under several hash seeds, recomputed the detector table from the output, and compared a sample
with the source by hand. Two cautions follow from it.

1. The detector lists, the head-class table and the statement parser were written against this
   corpus and corrected on the audited samples. Their agreement with the move labels is therefore
   an in-sample figure. A source harvested later is the first fair test.
2. The features with the strongest precedent in the literature are not here yet: abstracted
   subterm patterns and walks in the term tree (survey K §6, rows 2, 3, 15 and 19), the recursion
   argument of the functions in a goal (survey J §10, candidate 2), and a generality relation
   between a parent and a child statement by anti-unification (survey J §10, candidate 3). The
   statement parser stops at the connectives and relations; what lies below is one leaf.

On 2026-11-21 the Lean graph was compared with dependency data from the Lean compiler for all of
Mathlib: `gold-lean.md` gives the method and the results, `tools/features/feature_gold.py` runs it. This
is the first check of the graph against a prover. It led to lexer 1.1.0, which changes Lean
entries only. The Rocq and Isabelle graphs have no such check yet.
