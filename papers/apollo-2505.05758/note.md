# APOLLO: Automated LLM and Lean Collaboration for Advanced Formal Reasoning

| Field | Value |
|---|---|
| Authors, organisation | Azim Ospanov, Farzan Farnia, Roozbeh Yousefzadeh; Huawei Hong Kong Research Center and The Chinese University of Hong Kong |
| Date and version read | v5, 4 November 2025 (v1: 9 May 2025). NeurIPS 2025 [S, Survey A of this repository; the arXiv page does not say so] |
| Source | arXiv 2505.05758, https://arxiv.org/abs/2505.05758. Code: https://github.com/aziksh-ospanov/APOLLO (not opened) |
| Licence of the source | CC BY 4.0 (arXiv abstract page) |
| Files in this folder | `paper.pdf`, `note.md` |
| What was read | Full main text and Appendices A to G from the arXiv HTML. The figures (code listings) were not viewed. |
| Read on | 21 November 2026 |

Confidence tags: **[P]** the writer of this note read the statement in the primary source, and the
place is given (section, table, figure or page). **[S]** the statement comes from a secondary source,
which is named. **[U]** the statement is not verified. A number without a tag is not permitted.

Surveys A (Section 4.1), B (Section C1) and F (Section 3.1) of this repository give the pipeline, the solver list and the ablation table. This note keeps to what bears on MathEye.

## 1. What the work is

APOLLO is a repair pipeline for Lean 4 proofs that a model wrote. It replaces each failing part of the proof with `sorry`. It tries automation on each hole. It sends each remaining hole back to the model as a new lemma. It calls the module for the first step the "Sorrifier". On miniF2F-test it raises five base models, for example o4-mini from 7.0% to 46.7% [P, Table 2].

## 2. How it works

1. A *Syntax Refiner* applies regular-expression rules to the text [P, A.1].
2. The *Sorrifier* parses the proof "into a tree of nested proof-blocks". It sends the proof to the Lean REPL and reads the errors and their locations [P, Section 3.2].
3. The *Auto Solver* tries `hint` and then a list of tactics on each hole [P, A.3].
4. Each hole that remains becomes a lemma with its local context, and the whole pipeline runs on it [P, Section 3.4].
5. The *Proof Assembler* puts the parts together and checks that no `sorry` or `admit` remains [P, Section 3.5].

## 3. How it splits a proof

- **Unit replaced by `sorry`.** One proof block of the tree, where sub-lemmas are child blocks. Three repairs exist: remove one line; remove a whole malformed block; insert `sorry` when a block compiles and leaves goals open [P, Section 3.2].
- **How the failing part is located.** By the error list of the REPL. The cycle of compile and patch repeats until no error remains [P, A.2].
- **The extracted sub-goal.** APOLLO asks the REPL for "the exact goal statements" [P, A.3]. It sets ten pretty-printer options so that every type is explicit [P, A.2]. No model rewrites the statement.
- **Check of the split.** The proof with `sorry` compiles. A malformed theorem statement causes a new generation [P, A.2].
- **Record.** A tree of blocks. No dependency graph.
- **Order of open goals.** The source order of the holes, `i = 1 .. n` [P, Algorithm 1]. No cost model. Every hole must be closed.
- **Rounds.** Recursion depth `r`; beyond `r` the hole stays `sorry` [P, Algorithm 1]. Tested values are 0 to 6 [P, Section 4.4]. Each sub-lemma gets 32 samples [P, Section 4].

## 4. What it says about scale

- Mean samples for each problem: 362 (Goedel-SFT), 307 (Kimina-7B), 63 (Goedel-V2-8B), 15 (o4-mini) [P, Table 2].
- A Lean check takes 6 to 200 seconds; the timeout is 5 minutes. One problem at 32 samples takes 700 to 2,000 seconds on one A5000 GPU [P, Appendix D].
- One theorem at a time, one file. No figures on rebuilds or on agents that work in parallel.

## 5. Evidence

| Result | Value | Place |
|---|---|---|
| Goedel-Prover-SFT, miniF2F-test | 64.7% at 25,600 samples; 65.6% with APOLLO at 362 samples | [P, Table 2] |
| Kimina-Prover-Preview-Distill-7B | 70.8% at 1,024 samples; 75.0% with APOLLO at 307 | [P, Table 2] |
| Goedel-V2-8B | 84.9% at 128 samples; 84.9% with APOLLO at 63 | [P, Table 2] |
| o3-mini with REPL feedback only | 25.4% at 10 samples; APOLLO 40.2% at 8 | [P, Table 8] |
| Model re-invoked on holes, alone | Kimina 63.1% to 69.3%; o4-mini 7.0% to 8.2% | [P, Table 4] |
| All three modules | Kimina 75.0%; o4-mini 46.7% | [P, Table 4] |
| PutnamBench, Kimina-7B | 10/658 at 192 samples; 11/658 with APOLLO at 108 | [P, Table 3] |

The Sorrifier is not ablated; the authors say it "cannot be ablated" [P, Section 4.5]. Repaired proofs are at least two times longer than unrepaired proofs on average [P, Section 4.3].

## 6. Limits

The authors state: no test with tree-search provers, and the result depends on a coherent first sketch [P, Section 5].

Reader's limits. Baseline numbers come from other papers [P, Section 4]. Table 5 gives for Kimina-7B a mean token budget (1.6M) above the maximum (1.3M). No measure says how often a removed line or block changed the intended argument.

## 7. Relation to the two anchors

**MathEye.** APOLLO did the `sorry` replacement first: v1 is dated 9 May 2025, eighteen months before MathEye. Both parse the script into a tree, compile, replace the failing block, and repeat until Lean accepts. MathEye adds an explicit rule: climb to the parent node when the error stays. APOLLO states block removal for a malformed sub-proof and no climb rule (reader's reading). After the replacement the two differ. APOLLO proves every hole by automation and by a model, in source order. MathEye builds a hypergraph, selects obligations with a MaxSAT solver, and asks a person. MathEye names the same limit, dependence on the first sketch. The text and the reference list of MathEye do not contain APOLLO (searched in the full text and in `refs_2611.22103.json`). MechMath cites APOLLO for the term "sorrifying" [P, MechMath Section 3.1].

**Turing Agent.** No shared mechanism beyond recursion on sub-goals. The text of the Turing Agent does not contain APOLLO (searched).

APOLLO cites Draft, Sketch, and Prove and Baldur. It cites no work on angelic execution or abduction, the lineage that MathEye names (searched).

## 8. What this repository can use

- **Explicit types for extracted goals.** A `subgoal` node of `graphs.jsonl` has no statement. A future extraction with a prover must print goals with the options of APOLLO, because a goal without explicit types can be ambiguous or trivial.
- **Three repair classes as labels.** "Line removed", "block removed" and "hole left open" are different outcomes for a `local` (`have`) node. Record the class when a failed step is logged.
- **Automation first.** In the worked example the Auto Solver closes four of six holes [P, Appendix F]. Mark a child whose proof is one automation tactic; it is glue, not a lemma worth a library entry.
- **Scale.** Each hole is an independent job with a fixed sample budget. That part runs in parallel with no shared state (reader's inference). The assembly step is serial.

## 9. Open points and things not read

- How often does the Sorrifier remove a line that the argument needed?
- Not read: the code repository; the code listings in Figures 2 and 6 to 16.
