# ProofFlow: A Dependency Graph Approach to Faithful Proof Autoformalization

| Field | Value |
|---|---|
| Authors, organisation | Rafael Cabral, Tuan Manh Do, Yu Xuejun, Wai Ming Tai, Zijin Feng, Xin Shen; Huawei Celia Team and Huawei Noah's Ark Lab |
| Date and version read | v1, 13 October 2025. ICLR 2026 [S, reference 14 of arXiv 2610.36776 and Survey K of this repository; the arXiv page does not say so] |
| Source | arXiv 2510.15981, https://arxiv.org/abs/2510.15981. Code and benchmark: https://github.com/Huawei-AI4Math/ProofFlow (not opened) |
| Licence of the source | CC BY 4.0 (arXiv abstract page) |
| Files in this folder | `paper.pdf`, `note.md` |
| What was read | Full main text and Appendix A.1 to A.6 from the arXiv HTML. The figures were not viewed. |
| Read on | 21 November 2026 |

Confidence tags: **[P]** the writer of this note read the statement in the primary source, and the
place is given (section, table, figure or page). **[S]** the statement comes from a secondary source,
which is named. **[U]** the statement is not verified. A number without a tag is not permitted.

Survey K (Section 1.2) of this repository gives the main ProofScore figures, the cost and the failure table. This note keeps to the graph and to what bears on MathEye.

## 1. What the work is

ProofFlow translates a natural-language proof into Lean 4. A model first writes the dependency graph of the proof steps. Each step then becomes one Lean lemma that has only its declared prerequisites as hypotheses. The work claims that this keeps the structure of the human proof. The evidence is a benchmark of 184 undergraduate proofs with step graphs that persons checked [P, Section 5].

## 2. How it works

1. **Graph Builder.** A model reads the theorem and the proof and writes a directed acyclic graph. A node is one of four kinds: theorem condition, definition, lemma, or theorem solution. An edge `(u, v)` says that `u` is a prerequisite for the proof of `v`. Each node has a self-contained statement in natural language [P, Section 3.1].
2. **Checks on the graph.** No forward reference, no cycle, and every node except a theorem solution has an outgoing edge. On failure the model writes the graph again [P, Section 3.1].
3. **Formalizer.** A model writes each node as a Lean lemma that ends in `by sorry` [P, Section 3.1].
4. **Tactic Completer.** A prover model replaces each `by sorry` with tactics [P, Section 3.1].
5. **Error source.** When the tactics fail, the system tries to prove the negation of the step. A proved negation puts the fault on the natural-language statement [P, Section 4.2].

The edges are plain arrows. The incoming edges of one node are used together as its hypotheses, so they act as one joint premise set (reader's reading). There are no alternative premise sets. The graph comes from the text of the informal proof, not from prover terms.

## 3. How it splits a proof

- Unit: one step of the written proof, as one lemma.
- Who chooses: a model, from the natural-language proof. For the benchmark, a model wrote the graphs and persons verified them [P, A.1].
- Check before work on the children: the three structural checks above. No check that the children imply the parent.
- Record: a directed acyclic graph with four node kinds. Mean size 8.4 nodes: 2 conditions, 0.6 definitions, 4.4 lemmas, 1.2 solutions [P, Section 5, A.3].
- Failed child: the system labels the fault (formalizer, tactics, or the statement). It does not split again.
- Order of open goals: no rule. Each lemma is independent when its prerequisites are assumed.
- Rounds: up to five retries with the error message at each stage (Pass@5) [P, Section 6.2].

The work does not replace failing parts with `sorry`. It starts from lemmas that all end in `sorry`.

## 4. What it says about scale

With the graph enforced and the stronger models: 31.8 minutes and 94.2 thousand output tokens for each problem [P, Table 1]. Proofs have about eight nodes. No figures for large developments, rebuilds or parallel agents.

## 5. Evidence

No measure such as depth or centrality is computed on the graph. The test is an ablation: "DAG" gives each lemma only its declared prerequisites; "noDAG" gives every earlier step [P, Section 6.1].

| Measure (Pass@5) | DAG | noDAG | Place |
|---|---|---|---|
| ProofScore, stronger models | 0.545 | 0.417 | [P, Table 1] |
| ProofScore, weaker models | 0.355 | 0.347 | [P, Table 1] |
| Step-level tactic accuracy, stronger models | 0.742 | 0.681 | [P, Table 1] |
| Step-level tactic accuracy, weaker models | 0.358 | 0.391 | [P, Table 1] |
| Whole proof with correct syntax, stronger models | 0.375 | 0.353 | [P, Table 1] |
| Steps with no error, stronger models | 53.3% of 1,737 | 42.8% of 1,755 | [P, Table 2] |
| Steps where the statement is at fault | 2.2% | 2.6% | [P, Table 2] |

Baselines: whole-proof formalisation 0.123 and step-by-step formalisation 0.072 in ProofScore [P, Table 1].

## 6. Limits

The authors state that the Formalizer is the main source of failure, 32% to 47% of the outcomes [P, Section 6.2].

Reader's limits.

- ProofScore gives the DAG variant full marks for structure by construction, and a model judges the noDAG variant [P, Section 4.1]. Part of the gap 0.545 against 0.417 is therefore definitional.
- The tactic accuracy is free of this effect. It shows a gain of 0.061 for the stronger prover and a loss of 0.033 for the weaker one (reader's subtraction).
- The commercial models are not named [P, Section 6.1].
- No Lean check confirms that the lemmas together give the theorem.

## 7. Relation to the two anchors

**MathEye.** Both works hold a graph of which step uses which earlier fact. ProofFlow fixes the graph before any Lean code exists, from the informal proof. MathEye reads the graph from a Lean script after `sorry` replacement, and adds edges by inference rules. ProofFlow is earlier by thirteen months. Two points bear on MathEye. First, ProofFlow tests an open step by a machine attempt on its negation; MathEye asks a person. A negation attempt before the question to the person is a cheaper first filter (reader's proposal). Second, ProofFlow attempts every node and has no cost model; MathEye selects a smallest sufficient set with a MaxSAT solver. The text and the reference list of MathEye do not contain ProofFlow (searched in the full text and in `refs_2611.22103.json`).

**Turing Agent.** The Turing Agent reports about 10% of proved lemmas that no proof uses. ProofFlow shows one cause: when a step can see all earlier steps, the prover bypasses some of them. In one example the final step ignores four proved lemmas [P, A.5.3]. A restricted premise set prevents this. The text of the Turing Agent does not contain ProofFlow (searched).

ProofFlow cites Draft, Sketch, and Prove and Goedel-Prover-V2. It cites no work on angelic execution, and it does not cite APOLLO (searched).

## 8. What this repository can use

- **Hypothesis nodes.** `graphs.jsonl` has no node for a hypothesis of the parent statement. ProofFlow and MathEye both have such nodes. Add one node for each named hypothesis of the parent, and a `uses` edge from each child that mentions it. Then the graph says which child needs which assumption.
- **Unused children.** Add a feature for named children that neither the parent nor another child uses. This is the "squandered" case of ProofFlow and the unused lemmas of the Turing Agent.
- **Declared against actual prerequisites.** For each child, compare the names in its statement with the names its proof uses. A child whose proof ignores a declared sibling is a structural fault in the split.
- **The three validity checks** (no forward reference, no cycle, every node has a user) as self-checks in `feature_graph.py`. The field `on_cycle` already covers one.
- **A source of human step graphs.** ProofFlowBench has 184 proofs with checked step graphs. Check its licence before any harvest.

## 9. Open points and things not read

- How often do two annotators draw the same step graph? The work allows several valid graphs and gives no agreement figure [P, Section 4.1].
- Not read: the repository, the prompts, the benchmark files, the figures.
