# Beyond the Library: An Agentic Framework for Autoformalizing Research Mathematics (Theo)

| Field | Value |
|---|---|
| Authors, organisation | Arshia Soltani Moakhar, Iman Gholami, Max Springer, Mahdi JafariRaviz, MohammadTaghi Hajiaghayi. The paper gives e-mail domains only: umd.edu and princeton.edu |
| Date and version read | Version 3, 5 August 2026 (version 1: 30 June 2026) |
| Source | arXiv 2606.31134, https://arxiv.org/abs/2606.31134 ; formalisations at https://beyondthelibrary.github.io/formal_arxiv/ (not opened) |
| Licence of the source | CC BY 4.0 (arXiv page) |
| Files in this folder | `paper.pdf`, `note.md`, `figures/fig5a-pham-dag.png`, `figures/fig6-gravin-jia-dag.png`, `figures/fig7b-kalai-dag.png` |
| What was read | Full main text (Sections 1 to 5) and Appendices A to D from the arXiv HTML. Appendix E searched. Figures 5(a), 6 and 7(b) viewed. Figures 1 to 4, 5(b) and 7(a) not viewed |
| Read on | 21 November 2026 |

Confidence tags: **[P]** read in the primary source at the place given. **[S]** from a secondary
source. **[U]** not verified. "Reader's sum" is a sum that the writer of this note made from the
labels in a figure.

## 1. What the work is

Theo is a set of agents inside one Claude Code session. It receives a research paper as LaTeX and
PDF. It writes the Lean 4 statement of the main theorem, and then a Lean proof that follows the
proof in the paper [P, Section 2]. The work claims proofs for 32 of 32 sampled PutnamBench
problems and for the main theorems of seven research papers [P, Section 3]. Two of the seven use
no axiom outside the Lean kernel [P, Table 2]. The evidence is these runs and a cost table.

## 2. How it works

- **Orchestrator.** The orchestrator is the Claude Code session that starts the other agents. It
  can go back to an earlier stage. It writes no proof text itself [P, Section 2.2].
- **Type-first statement step.** A "type" is a definition that Mathlib does not have. A planner
  lists the necessary types in dependency order. For each type, k agents write a Lean definition
  at the same time [P, Section 2.1].
- **Auxiliary lemma technique.** An auxiliary lemma is a well-known property of a new type. The
  system states several such lemmas and tries to prove them. A failure shows that the definition
  is wrong or hard to use. The authors compare this to unit tests [P, Section 1]. A selector then
  ranks the k candidates by the proportion of lemmas proved, by the judge, and by length
  [P, Section 2.1].
- **Faithfulness Judge.** Four checks compare the Lean statement with the informal statement:
  two after a back-translation and two direct, with two different models. A tool removes the
  comments from the Lean code first [P, Section 2.1.3].
- **Claim Check.** A tool accepts a proof only when the statement is the same "byte for byte".
  It rejects an import that makes a cycle [P, Section 2.2].
- **Axioms.** A result that the paper cites from earlier work becomes a Lean axiom, and the judge
  examines its statement [P, Section 2.2].

## 3. How it splits a proof

- **Unit.** A lemma statement with `sorry` as its body. Each lemma is a node in a tree, and the
  main theorem is the root [P, Section 2.2].
- **Who chooses.** Agents choose. One agent writes an informal proof and a critic agent asks
  questions about it. A second agent expands it into steps and named sub-lemmas. A third agent
  makes "a topologically ordered set of lemmas" [P, Section 2.2].
- **When to split.** The orchestrator gives each node a score from its depth, the length of its
  Lean statement, the nesting of its quantifiers, and words in the paper (for example a step that
  the paper calls immediate). A low score makes the node a leaf [P, Section 2.2].
- **Check before work.** Yes. "we always prove the node before its children": the prover proves
  the parent with each child statement as a `sorry` premise, and only then proves the children.
  The reason given: the parent proof shows whether a child statement is too weak, too strong, or
  wrong [P, Section 2.2].
- **Record.** A tree of proof nodes. The appendix shows dependency graphs of groups of files
  [P, Figures 5 to 7].
- **When a child fails.** The prover returns one of three diagnoses: a hypothesis is absent, a
  child is too weak or contradictory, or the goal does not move. The orchestrator then adds a
  lemma, writes the child again, or changes a leaf into a node with children [P, Section 2.2].

## 4. What it says about scale

- Sizes in the text: 14,831 lines for the unit-distance paper and 5,713 lines for the cycle
  double cover paper [P, Sections 3.2.6 and 3.2.7]; "more than a hundred supporting lemmas" for
  Gravin and Jia [P, Appendix C.4].
- Sizes from the figures (reader's sums): Pham 47 files, 4,960 lines, 131 declarations
  [P, Figure 5(a)]; Gravin and Jia 107 files, 16,552 lines, 199 declarations [P, Figure 6];
  Kalai et al. 114 files, 29,187 lines, 277 declarations [P, Figure 7(b)]. Reader's inference: a
  file holds about two declarations, so a change to one lemma touches a small file.
- Cost: the seven papers use 11.01M input tokens, 49.71M output tokens and 14.70B cached input
  tokens, which is $13,681.05 at list prices [P, Table 3]. The authors paid about $1,200 for six
  months of a $200 plan [P, Section 3.3].
- Time: 219.5 hours for the unit-distance run and 45.7 hours for the cycle double cover run,
  with 168 transcripts [P, Appendix B].
- People: experts examine each statement. One expert with little Lean knowledge works with the
  system on the Pham paper [P, Section 3.2.1]. The prompts tell the system to work alone for 23,
  20 and 10 hours [P, Appendix D]. No human hours are given.
- The work gives no number of agents, no value of k, and no rebuild time. It does not report
  unused lemmas. It says nothing about merge conflicts.

## 5. Evidence

| Result | Place |
|---|---|
| PutnamBench: 32 of 32 random problems, Claude Opus 4.7, one attempt; lower bound 91.3% at 95% confidence | Table 1 |
| Putnam cost: about $150 of the plan; about $939 at list prices, about $29 for each problem | Section 3.1 |
| Seven papers: 0, 0, 1, 2, 3, 2 and 3 axioms outside the kernel | Table 2 |
| Unit-distance: 14,831 lines against roughly 33,000 for Aleph Prover, same two axioms | Section 3.2.6 |
| A counterexample to Lemma 2.6 of Pham; the bound of Lemma 2.9 stays as an axiom | Section 3.2.1; Appendix C.2 |

No ablation. Nothing isolates the split, the parent-first order, or the auxiliary lemmas. No
baseline is a plain coding agent with the same model.

## 6. Limits

Authors: the algorithmic results of the papers are not formalised, and the model is closed
[P, Appendix A].

Reader: the Putnam sample has 32 problems. The seven papers have no comparison system except one
count of lines. The check that a proof follows the paper depends on people, and the work gives no
procedure for it. The paper does not say that the harness code is public.

## 7. Relation to the two anchors

- **Turing Agent** is later by more than four months and cites Theo [P, `refs_2611.21299.json`].
  Same: the parent is proved from the child statements before work on the children. Reader's
  conclusion: this check is not new in Turing Agent. Different: Theo adds a leaf-or-split score
  and a byte-for-byte statement check; Turing Agent adds the experience pool and work on
  independent children at the same time. Theo cites Hilbert, Aristotle, Numina-Lean-Agent and
  Zhou et al. (arXiv 2507.15225, on decomposition) [P, References].
- **MathEye** is later, and neither work cites the other. Same: a parent proof with `sorry`
  premises is a proof with open obligations. Different: Theo has no person at each obligation and
  no computation of a smallest set of obligations.

## 8. What this repository can use

- The four signals for leaf or split are features. The feature graphs can compute them for the
  229 entries and test if they predict where a person split.
- The three diagnoses map to three repairs of a split: add a child, restate a child, split a
  leaf. This is a small vocabulary for failure labels.
- Auxiliary lemmas test a definition before any theorem uses it. This fits entries where the
  move is a new definition or an interface lemma.
- The byte-for-byte check and the import-cycle check are mechanical guards for parallel agents.
- The figures give files, lines and declarations for each group, as comparison data.

## 9. Open points and things not read

- How often does the parent-first proof reject a child statement? The work gives no count.
- What are k and the number of agents that run at one time?
- Not read: Appendix E in full, the formalisation site, Figures 1 to 4, 5(b) and 7(a).
