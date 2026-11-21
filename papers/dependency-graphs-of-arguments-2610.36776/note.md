# Dependency Graphs of Mathematical Arguments: Representation, Structural Measurement, and Proof Review

| Field | Value |
|---|---|
| Authors, organisation | Eunji Park, Graduate School of Data Science, Seoul National University |
| Date and version read | 27 October 2026, v1 |
| Source | arXiv 2610.36776, https://arxiv.org/abs/2610.36776. No code or project URL. |
| Licence of the source | CC BY 4.0 (arXiv abstract page) |
| Files in this folder | `paper.pdf`, `note.md` |
| What was read | Full main text (Sections 1 to 12) from the arXiv HTML; reference list; Appendix A (prompt PGPP 0.1) read once. Figure 1 is given as text in the HTML. |
| Read on | 21 November 2026 |

Confidence tags: **[P]** the writer of this note read the statement in the primary source, and the
place is given (section, table, figure or page). **[S]** the statement comes from a secondary source,
which is named. **[U]** the statement is not verified. A number without a tag is not permitted.

No earlier survey of this repository covers this work.

## 1. What the work is

The work is a proposal, not an experiment. It defines a data model for the dependency graph of one informal mathematical paper [P, Section 2]. It defines two measures on that graph, depth and bulk, and proves five elementary propositions about them [P, Sections 4, 5]. It gives a prompt (PGPP 0.1) that tells a language model how to extract the graph [P, Appendix A]. It reports no measurement: "No empirical values are asserted in this paper" [P, Table 3 caption]. The author states that GPT-6 Astra developed the mathematical details and the proofs [P, Disclosure of AI assistance].

## 2. How it works

- **Node.** A node is a *state*: one claim or expression in one context [P, Section 2.1]. One formula in two contexts gives two nodes. A printed item is a *source occurrence*; occurrences and states are related many-to-many.
- **Edge.** An edge `u -> v` says that the selected justification of `v` uses `u`. The arrow points from input to output [P, Section 2.2].
- **Hyperedge.** The stored unit is an *inference record*. It holds a set of joint inputs, one output, an operation type, the evidence, and a label of the proof alternative [P, Eq. 2.1]. Inputs in one record are joined by AND. Two records with one output are alternatives (OR). The measured graph is the projection of the selected records to plain arrows [P, Section 2.2].
- **Source of the graph.** A language model proposes the graph from the text of the paper. A person accepts or rejects each item. No prover takes part [P, Section 3.3].
- **Measurement contract.** The contract `C = (M, B, P, W, H)` fixes five things: manuscript, boundary inputs, granularity policy, proof selection, anchor nodes. Two measures are comparable only under one contract [P, Section 3.1].
- **Operation registry.** Nine step types define what one step is, for example APPLY, COMBINE and OPAQUE [P, Table 1]. An OPAQUE block has known inputs and output; its interior is not decomposed.
- **Algorithm.** Visit the nodes in topological order and take set unions of ancestor edges. A shared sub-argument then counts once [P, Prop. 4.2]. Depth costs `O(n+m)`; bulk costs at most `O(n+m+m^2)` [P, Section 8.2].

## 3. How it splits a proof

The work does not split proofs for a prover. It decomposes a written argument into steps for measurement.

- Unit: one registered operation [P, Table 1].
- Who chooses: a language model proposes, a reviewer accepts [P, Section 3.3].
- Check: structural only (unique identifiers, one generating record for each state, no cycle) [P, Section 8.1]. A cycle blocks the measurement; the protocol forbids the silent removal of an edge [P, Section 2.3].
- Record: a directed acyclic graph with AND/OR inference records behind it.
- Failed child: an unresolved step keeps a flag, and the flag propagates to every dependent state [P, Eq. 8.1].
- Order of open goals: none. The work proposes a ranked list of checks for a reviewer, and does not implement it [P, Section 7.4].

## 4. What it says about scale

No figures given. The work gives complexity bounds only [P, Section 8.2].

## 5. Evidence

Every measure, with its definition. None has a reported value on real data.

| Measure | Definition | What the author says it describes | Place |
|---|---|---|---|
| Depth `D(v)` | edges on the longest path that ends at `v` | "sequential dependence" | [P, Def. 4.1] |
| Bulk `S(v)` | distinct edges among all ancestors of `v` | amount of structure that supports `v` | [P, Def. 4.1] |
| `N(v)` | number of ancestors of `v`, with `v` | size of the prerequisite set | [P, Section 4.5] |
| `q(G)` | `|E| / |V|` | direct relations for each state; equal for a chain and a star | [P, Eq. 4.7] |
| `rho(v)`, `mu(v)` | `S/(N-1)`; `S-N+1`, the undirected cycle rank | branches that part and meet again | [P, Eq. 4.8] |
| `I(v)` | 1 if an ancestor of `v` has an unresolved flag | reach of declared gaps | [P, Eq. 8.1] |
| Macro skeleton | transitive reduction of the reachability between anchors | shape at a coarse level | [P, Def. 5.1] |
| Structural signature | height, nodes at each depth, largest antichain, components, terminal results, branch and merge counts | descriptors for comparison | [P, Section 5.2] |
| Co-use `C(t,t')` | number of proof units that use both theorems | a prompt for review | [P, Eq. 7.1] |
| `b_out(v)` | share of direct uses outside the cluster of `v` | bridges between fields | [P, Eq. 7.2] |

The author says that no measure is evidence of difficulty or importance [P, Abstract].

| Proved property | Example in the source | Place |
|---|---|---|
| Transitive reduction keeps depth and can change bulk | `a->b->c` plus `a->c`: `D(c)=2`, `S(c)` goes from two to three | [P, Prop. 4.3] |
| A refinement of steps changes depth and bulk | one edge becomes `k+1` edges: both go from one to `k+1` | [P, Prop. 4.4] |
| Added edges never lower depth or bulk | bounds for unresolved edges | [P, Prop. 4.5] |
| Anchor reachability fixes the macro skeleton | independent of the steps between anchors | [P, Prop. 5.2] |
| Reference case "shared prefix" | `D(t)=3`, `S(t)=5`; a sum of branches gives six | [P, Table 2] |

No measure is validated against proof success, repair success or human judgement. No baseline, no ablation, no implemented validator [P, Section 9.3].

## 6. Limits

The author states that the work reports no extraction accuracy and no demonstrated benefit [P, Section 11].

Reader's limits. The propositions are textbook facts about directed acyclic graphs, as the author says [P, Section 1.4]. The prompt has no test on a real paper. A language model wrote the proofs.

## 7. Relation to the two anchors

**MathEye.** Both works store an AND set of premises for one conclusion. MathEye builds its hypergraph from the syntax of a Lean script; this work builds it from prose. MathEye lets a MaxSAT solver choose among alternatives; this work fixes one alternative by a declared proof selection. The OPAQUE block and the flag `I(v)` correspond to a `sorry` and to the theorems that depend on it (reader's comparison). The work notes that a minimum of bulk for each target is not a minimum for the union of targets [P, Section 6.2]. That is a reason for a global solver (reader's inference).

**Turing Agent.** The macro skeleton over named results is the same kind of object as the lemma graph of the Turing Agent (reader's comparison). This work does not check a split with a prover.

This work is earlier than both anchors by about three weeks. The texts of both anchors do not contain its title or its arXiv number (searched). It cites ProofFlow, the Mathlib network study, Lean Blueprint and KnowTeX. It cites no `sorry`-repair system.

## 8. What this repository can use

- **Add bulk beside depth.** `graphs.jsonl` stores `depth` and `n_desc` for each node. Bulk is the number of `uses` edges among the descendants. Then `mu = S - N + 1` counts how often branches below a parent meet again. That is a number for reuse.
- **Mind the direction.** The repository edge goes from user to used; this work goes from input to output. Depth is the same number under both conventions (reader's check).
- **Do not reduce before counting.** Transitive reduction keeps depth and loses bulk (Proposition 4.3). Reduce only in the viewer.
- **Compare shapes by a macro skeleton.** Take the parent and the named children as anchors. The skeleton does not depend on the granularity of the steps between them (Proposition 5.2). Raw depth does (Proposition 4.4). Therefore compare `depth` only within one `scale`.
- **Group edges into AND records.** Each `uses` edge has a line number. The edges from one `have` line are one joint premise set (reader's proposal; a lexer can do this).
- **Use Table 2 as self-tests** for `feature_graph.py`: shared prefix, cycle witness, refinement between anchors.
- **For the scaling problem.** In the repository graph, the set of users of a lemma, taken transitively, is the set that a change forces to rebuild. Its size is a cost figure for a proposed split (reader's inference; the work does not discuss builds).

## 9. Open points and things not read

- Does a second model, with the same contract, return the same depth and bulk? The work names this as its central open question [P, Section 1.4].
- No corpus exists yet; the co-use statistics are a plan [P, Section 7.3].
- Not read in detail: the field-by-field JSON contract in Appendix A.
