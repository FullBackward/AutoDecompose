# Machine splits and human splits: the Prove2Me corpus against the library

Written on 21 November 2026. This is step 1 of Section 11 of `survey-M-results-2026-11-21.md`.

The question: how do the splits in the public Prove2Me corpus (Formalpedia) differ from the 198
human splits in the library of this repository? The work used no language model and no prover.

Important statements use Simplified Technical English. "Reader's" marks an inference of the
writer. All figures come from `prove2me-2608.28433/formalpedia/measures.json` and
`sample-measures.json`, and the folder `prove2me-2608.28433/formalpedia/` says how to compute
them again.

## 1. The data and the terms

**The data.** The Formalpedia snapshot of 21 November 2026, environment Lean v4.33.1: 476,697
cards and 3,632,901 arrows. These counts are equal to the counts in the manifest of the snapshot.

**The terms.**

- A **card** is one theorem statement or one definition. Each card is one Lean file.
- A **proof file** is a Lean file that proves the statement of one card. The platform accepted it.
- An **arrow** says that one card imports a different card. An arrow has the label `solution` when
  the import is in a proof file, and the label `statement` when it is in the statement.
- A **card child** of a theorem is a theorem card that a proof file of the theorem imports.
- A **local helper lemma** is a lemma that a proof file states for itself. It is not a card, and
  no arrow shows it.
- A **split at the level of cards** is a theorem with one or more card children.
- The **fan-out** is the number of children. The **height** is the longest chain of children
  below a theorem.

## 2. The main results

1. **Most of a split is not in the arrows.** A proof file has a mean of 27.9 local helper lemmas
   and 4.9 card children. Thus the arrows show approximately 15 % of the lemmas of a proof
   (reader's division). Section 4 has the details.
2. **In the middle of the distribution, the machine splits and the human splits have the same
   size.** The median fan-out is 3 in the two sets, and the median height is 5 in the two sets.
   Section 5 says how much this agreement can mean.
3. **The difference is in the tail.** The largest human split has 19 children. The largest
   machine split has 550 children, and 1 % of the machine splits have 153 or more.
4. **More children do not go with a shorter proof.** The median length of a proof increases from
   75 lines with no card child to 202 lines with 16 or more.
5. **The origin of a card decides its structure.** 70.3 % of the theorems that come from a code
   repository have a split at the level of cards. For theorems that come from a paper or a book,
   the proportion is 28.5 %.
6. **An imported card is almost always named in the file, but frequently not in a proof.** The
   text of a file names 97.4 % of the cards that it imports. For 43 % of the cards, the only
   mention is a command that registers the lemma for an automatic tactic. Section 9 has the
   details.
7. **The arrows contain cycles.** 2,593 cards are in 87 groups in which each card rests on each
   other card. The platform does not accept a circular pair as proved.
8. **The reach of a change is very uneven.** A change to the statement of a median card reaches
   7 cards. One card in a sample of 601 reaches 13,115.

## 3. The corpus

| Item | Count |
|---|---|
| Definition cards | 116,369 |
| Theorem cards | 360,328: 307,972 proved, 51,208 open, 1,148 disproved |
| Accepted proof files | 320,553. Of these, 5,492 are sketches: proofs that import an open theorem |
| Theorems with 2 or more accepted proofs | 7,224 (2.0 %) |
| Arrows with the label `solution` only | 1,965,083 |
| Arrows with the two labels | 1,013,694 |
| Arrows with the label `statement` only | 654,124 |
| Arrows from a proof file to a theorem card | 1,764,868 |
| Arrows from a proof file to a definition card | 1,213,909 |
| Authors of statements, authors of proofs | 242 and 270 |
| Theorems whose first proof has a different author from the statement | 14.2 % |

Four facts about the corpus change how a reader must use it.

- **The corpus is new.** 471,773 of the 476,697 cards (99.0 %) have a creation date in September,
  October or November 2026.
- **A small number of authors made half of it.** The five most active authors of statements have
  50.8 % of the cards.
- **Many cards are an existing project cut into cards.** The source field of 159,357 theorems
  (44.2 %) points to a file in a code repository. The source field of 129,212 theorems (35.9 %)
  refers to a paper or a book. The script assigns these classes by text patterns, so the
  proportions are approximate.
- **Some cards occur twice.** 2,090 theorem names are equal to a different theorem name with one
  more part at the start.

## 4. Where the split is: in the proof file

The arrows cannot show a lemma that a proof file states for itself. To measure this, the script
`sample_proofs.py` read a fixed sample of 300 accepted proof files: the first proof of each
1,022nd proved theorem in the order of the names.

| Measure in one proof file | Median | Upper quartile | 90th percentile | Maximum | Mean |
|---|---|---|---|---|---|
| Lines | 107 | 395 | 1,367 | 9,607 | 479.6 |
| Local helper lemmas | 2 | 19 | 69 | 871 | 27.9 |
| Card children | 1 | 4 | 8 | 239 | 4.9 |
| Local helper lemmas and card children together | 5 | 32 | 81 | 878 | 32.9 |
| `have` steps | 6 | 37 | 129 | 1,135 | 54.2 |

- 170 of the 300 files have one or more local helper lemmas. In these 170 files the median is 15.
- 133 files have no card child. 83 of these 133 have local helper lemmas. Thus "no arrow" does
  not mean "no split".
- 50 of the 300 files have no local helper lemma and no card child. These proofs are short: the
  median is 27 lines.
- The last declaration of a file is frequently a thin wrapper. Its own text names a median of 1
  lemma. The real parent is then a local lemma above the helpers.
- 146 of the 300 files import all of Mathlib.

**Result.** The arrows of Formalpedia show the lemmas that agents publish for other agents. They
do not show how one proof is split. A study that reads only the arrows measures the interface
between agents.

## 5. The comparison with the library

The library has 198 entries with a graph (117 Lean, 54 Rocq, 27 Isabelle). Each entry is one split
that a person wrote and that the library accepted as an example.

| Measure | Library, 198 human splits | Formalpedia, level of cards | Formalpedia, in one proof file |
|---|---|---|---|
| Theorems that the proof of the parent uses | median 3; quartiles 2 and 6; 90th percentile 11; maximum 19 | median 3; quartiles 1 and 6; 90th percentile 22; 99th percentile 153; maximum 550 (176,192 splits) | not measured as a direct count; see Section 4 |
| Height below the parent, through theorems | median 5; quartiles 3 and 8; 90th percentile 11; maximum 22 | median 5; quartiles 2 and 12; 90th percentile 32; maximum 210 | median 4; quartiles 2 and 7; 90th percentile 11; maximum 26 (167 files with a local helper lemma) |
| Definitions that the statement of the parent names | median 1; quartiles 0 and 2; 90th percentile 4 | median 1; quartiles 1 and 3; 90th percentile 5 | the same statement |
| Lines of the proof of the parent | median 17; quartiles 7 and 33; 90th percentile 60; maximum 607 | does not apply | median 93 for the full file; quartiles 31 and 388; 90th percentile 1,246; maximum 23,833 |
| Splits with a child that a different theorem uses | 85 of 175 entries (48.6 %) | 149,055 of 176,192 splits (84.6 %) | not measured |

**What the comparison shows.**

- The medians agree: 3 children, height 5, 1 definition in the statement. The agreement is in
  each of the three assistants of the library (medians 3, 3 and 4 for the fan-out; 5, 5 and 6 for
  the height).
- The lower three quarters of the machine splits are in the range of the human splits. The upper
  tenth is not: a fan-out of 22 or more, a height of 32 or more.
- A machine proof file is much longer than a human proof of a parent. The two units are not the
  same, because a machine file contains its helper lemmas.

**What the comparison does not show.** These limits are large.

- **Selection.** The library holds splits that were selected as good examples. Formalpedia holds
  all public cards. Equal medians do not show that the machine splits are equally good.
- **Reach of the graph.** A library graph covers only the files that the entry copied. A height
  in the library is thus a lower bound.
- **Method of the graph.** The library graph comes from the text of the code. The Formalpedia
  arrows come from import lines.
- **One snapshot.** The corpus increases by approximately 200,000 cards each month.

## 6. Does a split go with less work?

| Card children of the theorem | Theorems | Median lines of the first proof | Median seconds from statement to first proof |
|---|---|---|---|
| 0 | 134,107 | 75 | 1,512 |
| 1 | 44,354 | 55 | 897 |
| 2 to 3 | 59,258 | 74 | 824 |
| 4 to 7 | 35,433 | 128 | 3,038 |
| 8 to 15 | 16,375 | 206 | 2,449 for 8 or more |
| 16 or more | 20,772 | 202 | |

- **The length of a proof increases with the number of children.** This is not a cause and an
  effect. A hard theorem has a long proof and many children.
- **25,250 of the 134,107 proofs with no card child have 1,000 or more lines** (18.8 %).
- **The time is not a measure of difficulty.** For most cards the same author posts the statement
  and the proof, and the median time between them is 24 minutes. The time shows the work
  procedure of the author.
- **Result.** The corpus has no measure of the work for one lemma. The trace files of Turing
  Agent, with the failures for each of 135 lemmas, stay the only public data of that type that
  this survey found.

## 7. Open cards, sketches and cycles

- **Sketches are rare.** 5,492 of 320,553 accepted proofs import an open theorem (1.7 %).
- **Most open theorems block nothing.** Of 51,208 open theorems, a proof imports only 4,715
  (9.2 %). 3,609 splits have an open child.
- **Cycles.** A cycle is a group of cards in which each card rests on each other card through
  proof imports. The arrows have 87 such groups with 2,593 cards. The largest group has 2,084
  cards of one project.
  - In 79 of the 87 groups, one or more cards have two proofs. An arrow does not say which proof
    has the import. Thus such a cycle can come from two different proofs, and it does not show
    circular reasoning.
  - In the other 8 groups, with 19 cards, each card has one proof. These are pairs or triples of
    sketches that rest on each other. 17 of the 19 cards have the status "open". Thus the
    platform does not accept such a group as proved.
- **A status that the data does not explain.** 6 theorems have the status "proved", one proof
  that is a sketch, and an open child. A possible cause is a proof that the export omits for
  licence reasons. This is not verified.

**Result.** A store that accepts a proof against statements only can receive a circular group of
proofs. The store must find cycles before it marks a theorem as proved.

## 8. The reach of a change

The sample is each 794th card in the order of the names: 601 cards.

| Measure | Median | Upper quartile | 90th percentile | 99th percentile | Maximum |
|---|---|---|---|---|---|
| Cards that the card rests on | 12 | 74 | 258 | 3,439 | 3,494 |
| Cards that a change to its statement reaches | 7 | 32 | 149 | 2,525 | 13,115 |

- 25.3 % of the cards in the sample have no card above them.
- One theorem card in the corpus has 18,450 direct users. It is an intermediate lemma of a
  library from OpenAI.
- 108,419 theorem cards (30.1 %) have no user. 183,163 (50.8 %) have exactly one user. Of the
  251,909 cards that a proof imports, 68,746 (27.3 %) have two or more users.

**Result.** In a project of files, most changes to a statement are cheap, and a small number are
very expensive. The reach of a statement is a quantity with a long tail. On Prove2Me a statement
cannot change, so this cost does not occur there.

## 9. Imports that the proof does not use

In the sample, the proof files import 1,476 theorem cards. The text of the files names 1,438 of
them (97.4 %). 13 of the 167 files with a card child have an import that the text does not name.
The test looks for the last part of the name, so the 38 cases are a lower bound.

**A second look with the lexer of the library changes this result.** The lexer assigns each name
to the declaration that contains it. For the same 1,476 imported cards:

| How the file names the card | Cards |
|---|---|
| The name is in the file, but in no declaration | 633 |
| A declaration names the card (full name, or the last parts of it) | 816 |
| The file does not name the card | 27 |

The 633 cards are in commands of the form `attribute [local fun_prop] Name`. Such a command
registers a lemma for an automatic tactic. Then a later proof can use the lemma, and the text of
that proof does not show it. Thus the text cannot say if the proof uses these 633 cards. The
cases are concentrated: 5 of the 300 files have 407 of the 660 cards that no declaration names.

In the Turing Agent run with 109 claims, the proofs name 157 of 227 declared dependencies (69 %).
In this sample, a declaration names 816 of 1,476 imported cards (55 %), and the file names 1,449
(98 %). The two sources are thus not as different as the first count showed.

## 10. Consequences for this repository

1. **The unit of the library is the correct unit.** The library records lemmas inside a
   development. The card graph of a platform under-counts splits by a large factor.
2. **The next comparison must use the same tool on the two sides.** The feature tools of the
   library read Lean files. They can read a sample of Formalpedia proof files and give the same
   features as for the library entries: fan-out, height, the share of lines in the parent. This
   needs no model and no prover.
3. **The tail is the place to look for bad splits.** A fan-out above 19 and a proof of 1,000
   lines with no shared lemma do not occur in the library. They are candidates for a detector.
4. **Declared children must be checked for use, and text is not sufficient for the check.** A
   lemma that a command registers for an automatic tactic leaves no name in the proof that uses
   it. The feature tools of the library do not record such commands at this time.
5. **A store of splits must reject cycles.**
6. **Lines and time are not labels of difficulty.** A study of difficulty needs counts of
   failures, as in the Turing Agent trace files.

## 11. Limits of this work

- The sample of proof files has 300 files of 320,553. It is fixed and not random.
- The count of local helper lemmas reads the text with patterns. It does not use Lean.
- The hash of each fetched file is different from the hash in the index. The exported file has a
  header that the verified file does not have (reader's inference). Thus the script cannot
  confirm the bytes against the index.
- The classes of the source field come from text patterns.
