# M2F: Automated Formalization of Mathematical Literature at Scale

| Field | Value |
|---|---|
| Authors, organisation | Zichen Wang, Wanli Ma, Kun Yuan, Zaiwen Wen (Peking University); Zhenyu Ming, Gong Zhang (Huawei Technologies) |
| Date and version read | Version 1, 19 Feb 2026 (the only version) |
| Source | arXiv 2602.17016, https://arxiv.org/abs/2602.17016 ; https://github.com/optsuite/M2F ; generated Lean code https://github.com/optsuite/ReasBook |
| Licence of the source | CC BY 4.0 |
| Files in this folder | `paper.pdf`, `note.md` |
| What was read | Main text in full (Sections 1 to 7). Appendices A.1, A.2.5, A.2.6, C.1 to C.4, C.6 to C.8, D.1 to D.3 in full; Appendix B.1 in part. Figures not viewed. The two repositories were not read |
| Read on | 2026-11-21 |

Confidence tags: **[P]** the writer of this note read the statement in the primary source, and the
place is given (section, table, figure or page). **[S]** the statement comes from a secondary source,
which is named. **[U]** the statement is not verified. A number without a tag is not permitted.

No earlier survey in `docs/research/` describes this work. Survey B names it one time, as a user of the Lean LSP server.

## 1. What the work is

M2F is a pipeline that converts a textbook or a paper into a Lean 4 project that builds [P] (Section 1). It has two stages: first all statements, then all proofs [P] (Section 3.2). The pipeline accepts an edit only when the Lean checker reports a strict improvement [P] (Section 4.2). The authors report 153,853 lines of Lean from 479 pages, with all 875 audited proof holes closed [P] (Table 2). They also report 96 % on the FATE-H benchmark, against 80 % for Seed-Prover 1.5 [P] (Table 5).

## 2. How it works

**The accept rule.** A verifier call is one check of one file with `lake env lean` [P] (Appendix C.1). The pipeline takes a snapshot of the file, applies one patch inside a bounded range, and makes one verifier call. Stage 1 keeps the patch only when the errors of the file fall, or stay equal while the errors in the edited range fall. Stage 2 keeps the patch only when the errors fall, or stay equal while the number of `sorry` falls [P] (Section 4.2). The authors name this rule VeriRefine.

**Stage 1, statement compilation.** A preprocessor cuts the source into atomic blocks, which are ordered JSON items with one definition or statement each [P] (Sections 3.1, 4.4). For each block, a model writes a declaration skeleton with `sorry` as the proof. At most 3 repair attempts follow for each block [P] (Section 6.2).

**The dependency schedule.** The abstract says that the system "orders them via inferred dependencies". The body gives less. Both stages process the items "in increasing JSON index order" [P] (Sections 4.2, 4.5; Appendix A.2.5). Each item has a `dependencies` field of "lightweight dependency labels used as optional local context" [P] (Appendix B.1, Table 7). The paper gives no ordering algorithm. When an item needs a name before its body is stable, Stage 1 inserts a typed stub. A typed stub is the constant with its intended type and `sorry` as the body [P] (Section 4.5). The stub is the mechanism for forward references and cycles.

**Stage 2, freeze the signatures, then close the holes.** Statement signatures are fixed. Edits can change proofs and can add "local helpers that do not change existing signatures" [P] (Section 3.2). For each hole, a planner writes a proof plan and an executor proposes patches, with at most 10 attempts for each plan and at most 21 plans [P] (Section 6.3). A human expert compares each statement with its source span before the Stage 2 evaluation [P] (Section 6.1).

**File splitting.** When a file passes a line-count threshold, a splitter cuts it into `_partK` files with a linear import chain. One section module stays as the stable import target [P] (Section 4.3; Appendix A.2.5; D.2).

## 3. How it splits a proof

- Unit: the atomic block in Stage 1 and the proof hole in Stage 2. The edit scope is the declaration range and the file header [P] (Section 4.1).
- Who chooses: the preprocessor chooses the blocks from the source. The planner model chooses helper lemmas inside Stage 2.
- Check before work on the children: Stage 1 must end with a project that elaborates with every proof open [P] (Section 3.1).
- Record: none for the helper lemmas. The item list is flat.
- Failed child: the pipeline reverts the patch and plans again [P] (Algorithm 2).

Reader's inference: the Stage 2 rule accepts a patch only when the count of `sorry` falls. A patch that replaces one hole with two smaller open holes is thus rejected. The system cannot keep an open decomposition; it must close a hole and its helpers in one accepted step.

## 4. What it says about scale

| Quantity | Value | Place |
|---|---|---|
| Sources | 312 + 140 + 27 pages; 1,043 blocks | Tables 1, 2 |
| Output | 241 files, 4,116 declarations, 153,853 lines | Table 2 |
| Duration | "approximately three weeks" | abstract only |
| Hardware | one machine, 16 cores, 128 GiB | Section 6.1 |
| Verifier calls, Stage 1 | 592, 605, 81 (three corpora) | Table 9 |
| Verifier calls, Stage 2 | 628, 1,065, 77; 1.85 to 2.13 for each solved hole | Table 9 |
| Model calls, Stage 2 | 1,263, 2,001, 148 | Table 10 |
| Tokens, Stage 2 | 140,040,564; 307,966,089; 16,362,141 | Table 11 |
| Largest split of one section | 23 parts | Table 13 |
| Repair rounds for each block, Stage 1 | 0.42, 0.08, 0.20 | Table 3 |

All rows are [P]. Computed by the reader from Table 11: 516,094,497 tokens for the three corpora in both stages, about 3,354 tokens for each line. The paper describes no parallel agents; the pipelines "iterate deterministically" over the items [P] (Appendix A.2.5). Tool queries through the Lean language server are outside all counts [P] (Appendix C.6).

No figures given: wall-clock time for each stage, time of one verifier call, time of the final `lake build`, money, the line-count threshold.

## 5. Evidence

| Result | Value | Place |
|---|---|---|
| Stage 1 blocks that compile | 100 % on three corpora | Table 3 |
| Stage 2 holes closed | 875 of 875 | Table 2 |
| FATE-H | 96 %; 97 % with a 31-entry lemma map; Seed-Prover 1.5: 80 % | Table 5 |
| Ablation, Paper slice | one-shot 46.15 %; diagnostics only 13.85 %; no replanning 46.97 %; full 100 % | Table 4 |

The ablation removes parts of the Stage 2 loop. No ablation tests the two-stage split, the frozen signatures or the order of the items.

## 6. Limits

Authors: one FATE-H statement is inconsistent; two problems stay unsolved [P] (Section 6.4). Some Stage 1 counts are reconstructed from retry counters [P] (Appendix C.3).

Reader:

- The work addresses reason (i) by design. It checks one file after each edit and does not rebuild the project [P] (Appendix A.2.5). Frozen signatures and split files keep each check local. It reports calls, not time, so the saving is not measured.
- The work does not meet reason (ii), because it runs one item at a time.
- Gloeckle et al. note that both textbooks overlap with Mathlib [S] (arXiv 2604.03071, Section 5).

## 7. Relation to the two anchors

- Turing Agent: both write statements first and proofs second. Turing Agent keeps open child obligations in a graph and gives them to parallel agents. M2F keeps no open children and runs in sequence. M2F is earlier (February 2026). Turing Agent does not cite it [S] (Semantic Scholar reference list).
- MathEye: the result of Stage 1 is a whole project in which every proof is `sorry`, the same idea as an angelic proof at project size. MathEye selects which open obligations matter. M2F closes all of them in file order. MathEye does not cite it [S] (Semantic Scholar reference list).
- M2F cites ProofFlow and Aria for dependency graphs [P] (Section 2). It does not cite Draft-Sketch-Prove [P] (reference list searched).

## 8. What this repository can use

- The prompt rules in Appendix A.1 are decomposition rules from a group with industrial authors [P] (Appendix A.1). Move a proof inside a term to a named helper lemma. Separate an object from its properties. Treat a long chain of `have` steps as a sign that the statement has the wrong shape.
- The typed stub gives a way to schedule items that refer to each other.
- The frozen-signature stage defines independence: under fixed signatures, two holes in different declarations do not affect each other (reader's inference). The proposed algorithm can use this to run children in parallel.
- A stable section module in front of split files keeps the import target fixed when a file grows.

## 9. Open points and things not read

- Does the `dependencies` field change the order of the items? The paper does not say.
- Appendices A.2.1 to A.2.4, A.3, A.4, B.2 to B.7, C.5 and D.4 were not read.
