# The Lean graph against the Lean compiler

`feature_graph.py` reads source text. An arrow `A uses B` in its graph says that the text of A
contains a name that the resolver matches to B. This file reports how these arrows agree with the
dependencies that the Lean compiler records. `tools/features/feature_gold.py` makes the comparison. No
prover is necessary, because the compiler data is public.

Important statements in this file use Simplified Technical English.

## 1. The data

| Item | Value |
|---|---|
| Compiler data | The dataset MathlibGraph, https://huggingface.co/datasets/MathNetwork/MathlibGraph , revision `8c706461fe266802197b62af324de12a3f1aa7fb`, licence Apache 2.0 |
| Paper of the dataset | "The Network Structure of Mathlib", arXiv 2604.24797; the note is in `papers/network-structure-of-mathlib-2604.24797/` |
| How the dataset was made | With the tool `lean-training-data`, on Lean v4.28.0-rc1 |
| `v2/declaration/metrics.csv` | 57,521,366 bytes; SHA-256 `0c88b5044db57d48ba150fbe0a3550d47684739ca9b97dbb141564c5ce7a5658` |
| `mathlib_edges.csv` | 584,463,744 bytes; SHA-256 `5e1426b2304a97924cca1e48fa22d76620e1cb7bbb496a1bd9dd742cc6906922` |
| Source text | Mathlib at commit `534cf0b8f5267c3f20bf52f932ad5f9834187c35` (2 February 2026): https://codeload.github.com/leanprover-community/mathlib4/tar.gz/534cf0b8f5267c3f20bf52f932ad5f9834187c35 ; SHA-256 of the archive `3131e528db6ae57257e77c9306c98bc78f76b35d67d347027ed3818f0ee5148c` |

The files are not in this repository, because of their size (approximately 760 MB).

**What a row of the compiler data says.** `source,target,is_explicit` says that the checked
statement or proof of `source` contains the constant `target`. `is_explicit` is true when a person
wrote the constant in the source. The other rows come from the elaborator: instances, coercions,
numerals, and the lemmas that a tactic found.

## 2. The method

1. For each Mathlib file, the tool builds the graph that a library entry gets when the entry
   copies exactly that one file.
2. The tool keeps the compiler rows in which the source and the target are in that file.
3. The tool maps each compiler name to a row of the declaration table. A field or a constructor
   maps to the row of its type. A constant that the compiler made (`foo._proof_1`, `foo.match_1`)
   maps to the row of `foo`. A private name loses its `_private.<module>.0.` prefix.
4. The tool compares the two sets of arrows between rows.

The terms:

- **Precision** is the share of our arrows that the compiler also has.
- **Recall of explicit arrows** is the share of the compiler's explicit arrows that our tool
  gives.
- A **missed explicit arrow** is in one of two classes. In the class "name in the text", the last
  part of the target's name is a token in the text of the source declaration, so a better resolver
  can find the arrow. In the class "no token", the text has no such token (a notation, for
  example), so a tool that reads text cannot find the arrow.

To run the comparison:

```
library/tools/py.sh library/tools/features/feature_gold.py --nodes <metrics.csv> --edges <mathlib_edges.csv> \
    --src <the directory that holds Mathlib/> --out library/features/gold-lean-<lexer version>.json
```

The run on all files needs approximately 4 minutes. `--step N` reads each N-th file.

## 3. Results on all of Mathlib

7,189 files, 2,021,796 lines. The lexer failed on no file. The two result files are
`gold-lean-1.0.0.json` and `gold-lean-1.1.0.json`.

| Measure | Lexer 1.0.0 | Lexer 1.1.0 |
|---|---|---|
| Compiler declarations that a person wrote (by the pattern of the name) | 245,539 | 245,539 |
| Of these, with a row of the same name | 216,205 (88.1 %) | 222,871 (90.8 %) |
| Our rows that the compiler also has | 98.8 % | 98.8 % |
| Our arrows | 336,381 | 340,809 |
| Compiler arrows inside one file that the comparison can use, explicit | 210,462 | 221,923 |
| Compiler arrows that the comparison cannot use, because one end has no row | 220,724 | 155,296 |
| **Precision** | **88.8 %** | **89.6 %** |
| **Recall of explicit arrows** | **85.1 %** | **84.8 %** |
| Explicit arrows found | 178,998 | 188,164 |
| Recall of all compiler arrows inside one file | 69.6 % | 70.2 % |
| Missed explicit arrows, name in the text | 7,565 | 9,321 |
| Missed explicit arrows, no token | 23,899 | 24,438 |
| Precision in the median file | 96.2 % | 96.5 % |
| Recall of explicit arrows in the median file | 95.5 % | 95.0 % |

Precision by the way the resolver matched the name (lexer 1.1.0):

| Level of the match | Arrows | Precision |
|---|---|---|
| `scoped`: the name is in the namespace of the declaration that uses it | 179,481 | 91.8 % |
| `field`: field notation such as `x.f` | 80,808 | 80.1 % |
| `exact`: the full name | 73,742 | 94.8 % |
| `opened`: the name through an `open` | 6,778 | 85.6 % |

Precision by the kind of the declaration that uses the name (lexer 1.1.0):

| Source | Arrows | Precision | Recall of explicit arrows |
|---|---|---|---|
| Theorem or lemma | 273,834 | 91.6 % | 84.0 % |
| Definition, instance, structure and other | 66,975 | 81.1 % | 88.3 % |

## 4. How to read the results

1. **The declaration table is reliable.** 98.8 % of our rows are compiler declarations.
2. **An arrow is correct in approximately 9 of 10 cases.** The value for theorems, 91.6 %, is the
   better estimate. The compiler data has no row for a constant such as `foo._proof_1`: it
   contains 0 such names. When a definition or an instance contains a proof, the compiler moves
   that proof into such a constant, and its dependencies are then absent from the data. Thus a
   correct arrow from a definition can count as wrong.
3. **Our tool finds approximately 85 % of the arrows that a person wrote.** Of the 33,759 missed
   arrows, 24,438 leave no token in the text. A tool that reads text cannot find them.
4. **Field notation is the weak level.** 1 arrow in 5 is wrong there, and this level gives 24 %
   of all arrows.
5. **One file shows a small part of the dependencies.** Only 14.3 % of the explicit compiler
   arrows of a Mathlib declaration stay inside its file. For a library entry this is not a
   defect, because an entry copies the files that hold the parent and its children.
6. **These values are for Mathlib.** Mathlib is one project by persons, with much notation. The
   values for a different project can be different. Section 6 gives one check on text from
   agents.

## 5. What changed from lexer 1.0.0 to 1.1.0

All four changes are for Lean only. The Rocq and Isabelle graphs of the library are identical.

1. **Fields and constructors have names.** The table now records the fields of a `structure` or
   `class`, the parent projections after `extends`, and the constructors of an `inductive`. A use
   such as `x.f` or `T.c` then points at the row of the type. Effect: 6,666 more compiler
   declarations have a row, and 65,428 more compiler arrows enter the comparison.
2. **A parent in notation gives no projection.** `extends A ≃ B` names no parent type.
3. **A word is a tactic only after `by`.** Before the first `by` of a body, a word at the start of
   a line is a term. Example: `ext fun _ => rfl` as a term uses the lemma `ext`.
4. **The written type of the receiver can remove an arrow.** For `x.f`, when the header gives `x`
   a named type and no candidate is in the namespace of that type, the tool gives no arrow.
   Before, the tool gave an arrow to each candidate. On each 5th file this rule removed 1,064
   arrows: 668 were wrong and 396 were correct. Thus the rule increases precision and decreases
   recall. The switch `FIELD_TYPE_RULES` in `feature_graph_lex.py` turns the rule off.

In the library, 24 of the 117 Lean entries change. The totals go from 4,316 to 4,360 nodes and
from 10,511 to 10,738 arrows. The number of children that a parent cites does not change in any
entry.

## 6. One check on text that agents wrote

The lexer also read 300 accepted proof files of the Prove2Me corpus (143,575 lines), which it
never saw before. The details are in `papers/formalpedia-and-library-splits-2026-11-21.md`.

- The lexer failed on no file.
- It found 8,681 theorem and lemma declarations. An independent scan of the text found the same
  number in each of the 300 files.
- It found one blind spot. A command outside a declaration can register a lemma for an automatic
  tactic, for example `attribute [local fun_prop] Name`. The graph has no arrow for such a
  command. In the sample this is the only mention for 633 of 1,476 imported lemmas.

## 7. What is not measured

- **Rocq and Isabelle.** No public compiler data was found for them. A measurement needs a prover:
  `coq-dpdgraph` for Rocq, `thm_deps` for Isabelle.
- **Arrows between two files.** The comparison uses one file at a time.
- **The library's own entries.** The comparison uses Mathlib, not the 117 Lean entries. That
  needs a Lean installation and a build of each source.
- **The split of an arrow into statement and proof.** The compiler data does not have it.

## 8. The next repairs, in order of measured size

1. Field notation: 80,808 arrows at 80.1 % precision.
2. Registration commands (`attribute` in Lean, `Hint` in Rocq, `declare` and `lemmas` in
   Isabelle) as their own type of arrow.
3. The 9,321 missed arrows whose name is in the text.
