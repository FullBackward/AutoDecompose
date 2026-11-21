# OpenAI mathematics release of 6 October 2026 (`openai/math`)

| Field | Value |
|---|---|
| Authors, organisation | OpenAI. No person is named |
| Date and version read | Repository at commit 4eaee87 (29 October 2026, the newest on 21 November 2026). Four earlier commits compared: adc7f12 (6 Oct), 3014888 (7 Oct), 1581d4c (12 Oct), 42907c9 (26 Oct) |
| Source | Not a paper. https://github.com/openai/math (README, `history.md`, `CONTENTS.md`, `lean/README.md`, `lean/formalization.yaml`, `lean/docs/`, `lean/ComparatorChallenges/`, `lean/lakefile.lean`). Announcement: https://openai.com/index/sharing-ai-progress-in-mathematics/ . Related: https://openai.com/index/navier-stokes-solution/ |
| Licence of the source | Apache-2.0 (`LICENSE`; `formalization.yaml`, field `project.license`) |
| Files in this folder | `source.pdf` (the README, printed from GitHub), `note.md` |
| What was read | README, history and Lean README in full. Catalogue parsed in full. 4 of 245 scope notes read; all 245 parsed by script. The Lean tree was counted with `git grep` on a local clone; no Lean file was built. The openai.com pages were read only as extracts from a fetch tool |
| Read on | 21 November 2026 |

Confidence tags: **[P]** the writer of this note read the statement in the primary source, and the
place is given. **[S]** the statement comes from a secondary source, which is named. **[U]** the
statement is not verified. A number without a tag is not permitted. "Reader's count" marks a count
that the writer made on the repository files; the scripts and outputs are in the scratch folder.
**[P-x]** marks a quotation from openai.com as a fetch tool returned it; the raw page was not seen.

## 1. What the work is

The release is a repository of mathematical manuscripts that an unnamed internal OpenAI model
wrote [P, README]. It holds 721 manuscripts in 373 families [P, README]. A family is a group of
related papers: a principal result, companions, consequences, or other proofs [P, README]. OpenAI
calls the manuscripts "raw research data" [P, README]. A Lean library gives formal proofs for part
of the results. The repository states the scope of each formal proof, but it does not describe how
the Lean proofs were made.

## 2. How it works

The model received about 4,000 problems [P, README]. Each result used three hours of "ChatGPT Pro
thinking compute" on average [P, README, "How the results were produced"]. Two results are exceptions to
this procedure: a zero-free region for the zeta function, and the Hodge conjecture for CM abelian
varieties [P, README].

For the Lean side the repository gives three facts only. The catalogue says `automation: methods:
- method: agent` and `review: status: unchecked` [P, `formalization.yaml`, last lines]. The README
says that OpenAI adds formalisations "as we obtain them" [P, README]. The announcement adds no
method [P-x]. For the September Navier-Stokes result OpenAI says more [P-x, Navier-Stokes page].
The proof used about 10,000 concurrent agents, 2.7 million messages, about 130 billion output
tokens and about 88 hours. The Lean formalisation took "an additional 17 hours via GPT-6 Astra".
No source says that this system made the October library [U].

## 3. How it splits a proof

OpenAI describes no decomposition method. The repository shows only the result of one.

- **Unit.** The library is one Lake package, `OAI`, with one sub-library for each subject
  [P, `lakefile.lean`]. Below a subject, each result has a project directory. There are 668
  project directories in 26 subjects (reader's count). The counts below use 686 groups: the 668
  directories and 18 groups of files that sit outside a project directory.
- **Shape.** A project has many small files. The median file has 89 lines and 3 theorems or
  lemmas. The mean is 12.58 lines for each theorem or lemma (reader's count).
- **Shared code.** 344,735 import lines point inside the same project, 24,645 point to another
  project, and 68,592 point to Mathlib. 314 of the 686 groups are imported by another group
  (reader's count). The library is therefore not "one file per manuscript", and it is not a set of
  independent proofs.
- **Check of the top statement.** Each formal result has a Comparator challenge. A Comparator
  challenge is a Lean file that holds only the statement, with `sorry` as its proof. A JSON file
  beside it names the solution module and the permitted axioms
  [P, `ComparatorChallenges/QuasiRiemannHypothesis.json`]. There are 419 JSON files with 546
  theorem names (reader's count). No check of intermediate splits is published.

## 4. What it says about scale

OpenAI states three things only [P, `lean/README.md`]. The library is "a single large library".
OpenAI recommends compiling "only small portions at a time". A full build can fail on the Linux
limit `vm.max_map_count`. All other figures are reader's counts at commit 4eaee87:

| Measure | Value |
|---|---|
| Lean files below `lean/OAI` | 162,417 |
| Lines | 29,694,161 |
| Bytes | 1,778,091,847 |
| `theorem` or `lemma` declarations (pattern at line start) | 2,361,301 |
| Lines in the largest project (`Analysis/MutuallyUnbiased`, 3,386 files) | 2,835,023 |
| Median group (686 groups) | 42 files, 10,338 lines |
| Files that contain `decide +kernel` | 5,848, with 1,311,448 occurrences |
| `sorry` as a proof term | 0 (7 occurrences of the word, all in comments) |
| Lake dependencies | 30, with 23 compatibility patches |

The update of 26 October added 39,959 Lean files in one commit; 23,389 of them are in
`AlgebraicGeometry` (reader's count). OpenAI gives no figure for agents, cost, time, rebuilds or
merge conflicts. The only build figure is from outside: one pass over 162,170 of 163,096 files
took 31.5 hours on 24 cores [S, survey E, Section 1.6, from eunomia.dev]. That source counts
1,354,379 `decide +kernel` calls in the same 5,848 files; the reader's pattern finds fewer.

## 5. Evidence

**How many results have a Lean proof.** The secondary figures count different units.

| Figure | What it counts | Source |
|---|---|---|
| 162 | Papers listed under `sources` in `formalization.yaml` at the first commit, 6 October | reader's count; the same file has 173 on 7 October and 176 now |
| 24 % | 173 of 719, or 176 of 721: catalogue papers over manuscripts | reader's computation |
| 300 of 719, about 42 % | "top-line results formalized", OpenAI's own figure of 7 October | [P, `history.md`; README] |
| 36 % | Not found in any commit. 137 of 372 families (36.8 %) had no Lean note on 6 October; this can be the origin | reader's inference [U] |

Other units at the newest commit (reader's counts): 245 of 373 families have a Lean scope note;
344 manuscripts are linked from a scope note; the catalogue lists 208 main results. OpenAI does
not define the numerator 300, and no file in the repository reproduces it. Turing Agent reports
that 22 of the 121 theoretical computer science problems lacked full Lean verification
[S, Turing Agent, Figure 3 caption].

**How a partial formalisation is marked.** A family with a Lean proof has a link "(Lean)" in
`CONTENTS.md`. The link opens a scope note with a section "Scope" and a table of Comparator
statements [P, `lean/docs/003.md`, `087.md`]. The note says in prose what is left out, for example
"The nonsymmetric Mahler conjecture and the functional inequalities are not included"
[P, `lean/docs/087.md`]. 47 of 245 notes contain such a phrase (reader's count with a word
pattern; a lower bound). The catalogue as a whole has `status: scope: "Partial progress."` [P].

**Withdrawals.** On 7 October OpenAI withdrew three manuscripts after a sign error in one of them
broke two dependent papers. It revised 14 others and updated 13 more to cite the revised papers
[P, `history.md`]. The count went from 722 to 719, and to 721 on 26 October (reader's count).

There is no ablation and no baseline. OpenAI reports no full build of the library.

## 6. Limits

Stated by OpenAI: "Some of the unformalized results could have issues" [P, README]; the review
status is "unchecked" [P, catalogue].

Found by the reader:

- The method for the Lean proofs is not documented.
- The unit "top-line result" is not defined.
- Scope limits are prose, so a script cannot list the unproved parts.
- The reader's declaration counts use a text pattern and not the Lean elaborator.

## 7. Relation to the two anchors

**Turing Agent (arXiv 2611.21299)** is later. It takes three problems of this release that had no
complete Lean proof and finishes them. It cites the release and the Navier-Stokes page (checked in
`refs_2611.21299.json`). Turing Agent checks each split in Lean before work on the children. The
release publishes a check for the top statement only.

**MathEye (arXiv 2611.22103)** is later and does not cite the release. A MathEye "angelic proof"
keeps `sorry` for open obligations and records them. The library below `lean/OAI` contains no
`sorry`, and the release writes its open parts in prose.

## 8. What this repository can use

- **A scope note for each entry.** A short prose section that says what the formal statement
  covers and what it leaves out is cheap. A machine-readable list of omitted parts is better,
  because 47 notes here can be found only by a word pattern.
- **Comparator-style statement files.** A statement file with `sorry` and a list of permitted
  axioms separates "which statement" from "which proof". The library can store a split in the same
  way: parent statement, child statements, and a proof of the parent from the children.
- **A corpus for the feature graphs.** The library holds 668 projects with 24,645 cross-project
  imports. It is a large sample of machine-made decompositions with short lemmas, for comparison
  with the 229 human entries.

## 9. Open points and things not read

- The meaning of "300 / 719". How the Lean proofs were made, and by which system.
- `overview.pdf`, the preprints and the reasoning summaries were not read. No Lean file was built.
- The 11 dependencies from the GitHub organisation `lana-agents` were not examined [P, catalogue,
  `related_formalizations`].
- The openai.com pages need a reading of the raw text.
