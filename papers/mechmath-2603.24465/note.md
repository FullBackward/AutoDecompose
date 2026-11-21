# MechMath: Sorrifier-Driven Formal Decomposition Workflow for Automated Theorem Proving

| Field | Value |
|---|---|
| Authors, organisation | Ruichen Qiu, Yichuan Cao, Junqi Liu, Dakai Guo, Xiao-Shan Gao, Lihong Zhi, Ruyong Feng; Academy of Mathematics and Systems Science, Chinese Academy of Sciences, and UCAS, Beijing |
| Date and version read | v2, 16 August 2026 (v1: 25 March 2026). The arXiv page says "Published as a conference paper at COLM 2026". |
| Source | arXiv 2603.24465, https://arxiv.org/abs/2603.24465. Code: https://github.com/MechMath/MechMath-v1 (not opened) |
| Licence of the source | CC BY 4.0 (arXiv abstract page) |
| Files in this folder | `paper.pdf`, `note.md`, `figures/fig4-tree-depth-imo-p4.png` |
| What was read | Full main text; Appendices B, C.1 to C.3, D and E in full; Figure 4 rendered and viewed. The prompts in Appendix C.4 were not read. |
| Read on | 21 November 2026 |

Confidence tags: **[P]** the writer of this note read the statement in the primary source, and the
place is given (section, table, figure or page). **[S]** the statement comes from a secondary source,
which is named. **[U]** the statement is not verified. A number without a tag is not permitted.

Surveys C (Section 3) and F (Section 3.2) of this repository give the algorithm and the ablation. This note adds what bears on the anchors, on the graph and on scale.

## 1. What the work is

MechMath is a Lean 4 proving agent. Its central tool is the *Sorrifier*: a procedure that replaces each failing block of a proof with `sorry` until the proof compiles. Each `sorry` then becomes a separate lemma, and the same pipeline proves it. The work claims lower cost and time than four other agents on four benchmarks [P, Tables 1, 2, 8]. It takes the word "sorrifying" from APOLLO and cites APOLLO [P, Section 3.1].

## 2. How it works

1. A Reasoner model writes an informal proof. A Verifier model judges it three times. There are up to 16 refinement rounds [P, C.1].
2. A Prover model writes the Lean proof. It gets up to 4 repair rounds with compiler feedback [P, C.1].
3. If the proof still fails, the Sorrifier runs (Section 3 below).
4. For each `sorry`, the Reasoner reads the goal state and keeps the hypotheses that it judges relevant. It writes a lemma. Lean checks the syntax. The Verifier checks "extraction correctness" and "logical soundness" [P, Section 3.2.3].
5. A proved lemma returns to the parent as one `apply` line [P, Fig. 3].

The work names three classes of failure [P, E.3]. F1 is a failed leaf step; the Sorrifier repairs it. F2 is a false intermediate claim; the Verifier raises `LOGIC_ERROR`, and the parent proof is corrected. F3 is a wrong skeleton, for example a wrong induction hypothesis; only a new global proof repairs it.

## 3. How it splits a proof

- **Unit replaced by `sorry`.** The proof body of the shortest `have` or `replace` block that contains the line of the primary error. A `calc` or `choose` block is replaced whole. With no enclosing block, the line is cut at the error and `sorry` is appended [P, Algorithm 1].
- **How the failing part is located.** By the line and column of one compiler error. Lean compiles again after each single replacement, so that errors caused by the first error disappear [P, Section 3.1].
- **Who chooses.** A rule chooses the place. A model chooses the statement of the child.
- **Check before work on the children.** The proof with `sorry` compiles, so the holes together suffice for the parent. Only a model checks the extracted lemma. The final `apply` is the formal check.
- **Record.** A tree. A node is a lemma; an edge says that the parent proof applies the child. There is no dependency graph and no shared child.
- **Order of open goals.** No rule. Every hole must be closed. The work says that holes at one level "can be parallelized" [P, Section 4.1]. It does not say that the implementation does so.
- **Failed child.** The child goes through the whole pipeline again. A nested subgoal identical to its parent counts as no progress. After a threshold the run stops [P, Section 3.2.4]. The threshold and the iteration limit `N` have no stated value.

## 4. What it says about scale

| Quantity (MechMath-Hard) | Putnam 2025 | IMO 2025 | Place |
|---|---|---|---|
| LLM calls for each problem, mean | 91.3 | 643.5 | [P, Tables 5, 6] |
| Tokens, mean | 1,088 K | 7.99 M | [P, Tables 5, 6] |
| Sorrifier runs, mean | 12.6 | 98.0 | [P, Tables 5, 6] |
| Cost, mean | $18.5 | $82 | [P, Tables 1, 2] |
| Lemmas, mean | 14 | not given | [P, Table 1] |
| Lean lines, mean | 656 | not given | [P, Table 7] |

For IMO 2025 P4 the MechMath tree ends at depth 5 and has about 48 nodes at depth 2. The trees of Aristotle and Seed reach depths 11 and 12. These values are read from the plot [P, Fig. 4; `figures/fig4-tree-depth-imo-p4.png`]. There are no figures for rebuild time or for conflicts between agents. Each run treats one problem; there is no shared library.

## 5. Evidence

| Result | Value | Place |
|---|---|---|
| Putnam 2025 solved | Easy 9 of 12; Hard 11 of 12; Hilbert with the same model 1 of 12 | [P, Table 1] |
| miniF2F | 242/244 with at most 512 LLM calls; Hilbert 99.2% with 11.3K calls | [P, Table 8(a)] |
| ProverBench number theory | 24 of 40; Hilbert 16 of 40 | [P, D.3] |
| Ablation at 128 calls, Putnam A1 to A4 | discard and retry 0/4; iterative repair 3/4; MechMath 4/4 | [P, Table 3(d)] |
| Share of skeleton lines kept after a Sorrifier run | 74.5% (104 runs, miniF2F); 71.1% (135 runs, ProverBench); range 5% to 98% | [P, E.1] |
| Subgoals with a logic error | 1.22% Putnam; 1.49% IMO; 1.23% miniF2F; 7.05% ProverBench | [P, Table 12] |
| Subgoals with an extraction error | 3.05%; 4.85%; 0.00%; 1.92% | [P, Table 12] |

The ablation in Table 3(d) isolates the split. It covers four problems, and the work reports no repeated runs. No measure of the tree is tested against success.

## 6. Limits

The authors state that the pipeline is fixed and cannot skip or repeat a stage by context [P, Section 5].

Reader's limits.

- The figures of the other agents come from their own reports, with other budgets.
- The caption of Table 3 says that part (d) uses Hard mode. The costs in (d) are 1.53, 4.89, 11.60 and 19.90, which are the Easy-mode costs of Table 1.
- No model-free check confirms that an extracted lemma equals the hole.

## 7. Relation to the two anchors

**MathEye.** The first step is the same: replace failing fragments with `sorry` until Lean accepts the script. APOLLO did this in May 2025 and MechMath in March 2026. MathEye is dated 17 November 2026, so MathEye did not do it first. The text and the reference list of MathEye do not contain APOLLO, MechMath or ProofFlow (searched in the full text and in `refs_2611.22103.json`).

The differences are these.

- *Location.* MathEye starts at the failing tactic and climbs to the parent syntax node when the error stays. MechMath takes the shortest enclosing block. Algorithm 1 has no climb step (reader's reading).
- *After the replacement.* MechMath proves every hole with a model. MathEye builds a hypergraph, lets a MaxSAT solver choose a cheapest sufficient set of obligations, and asks a person.
- *Choice.* MathEye can ask about one interior claim in place of several leaves. MechMath cannot.

**Turing Agent.** In both, Lean accepts the parent with the open children assumed before work starts on the children. In MechMath the extracted lemma can differ from the hole, and only a model checks that difference. The Turing Agent keeps a graph; MechMath keeps a tree. The Turing Agent cites a later paper of the same group ("MechMath Agent Team", arXiv 2607.04394), not this one (checked in the anchor text).

MechMath cites Hilbert and Numina-Lean-Agent, which the Turing Agent also cites. It cites no work on angelic execution or abduction, the lineage that MathEye names (searched).

## 8. What this repository can use

- **Width profile.** Add the number of nodes at each depth to `graph-features.jsonl`; `graphs.jsonl` already stores `depth`. Then test whether human decompositions are wide and shallow, the shape that MechMath calls efficient.
- **Hypotheses kept.** For each `local` (`have`) node, count the names in scope and the names that the step mentions. This is the "relevant hypotheses" choice of MechMath, and a lexer can count it.
- **Name the anonymous holes.** The `subgoal` nodes of the graph have no statement. The extraction step of MechMath shows the target form: a lemma with a name and the kept hypotheses.
- **F3 marks where the library helps.** The case study repairs a failed induction by a generalised statement, "for all m ≤ n" [P, E.3]. No local repair finds this. It is the library move "generalise".
- **Scale.** Each hole becomes a new lemma, and the parent changes by one `apply` line. Parallel agents then do not edit the same lines (reader's inference). The parent must still compile again at each assembly.

## 9. Open points and things not read

- Does the implementation run sibling subgoals in parallel?
- IMO 2025 P6 is not reported; P2 is excluded as geometry [P, C.1].
- Not read: the prompts (C.4) and the code repository.
