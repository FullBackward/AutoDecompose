# The Network Structure of Mathlib

| Field | Value |
|---|---|
| Authors, organisation | Xinze Li, Nanyun Peng, Simone Severini, Patrick Shafto; University of Toronto, UCLA, University College London, Google, Rutgers University – Newark |
| Date and version read | v2, 4 May 2026 (v1: 26 April 2026) |
| Source | arXiv 2604.24797, https://arxiv.org/abs/2604.24797. Data: https://huggingface.co/datasets/MathNetwork/MathlibGraph. Code: https://github.com/MathNetwork/mathlib-network (neither opened) |
| Licence of the source | CC BY 4.0 (arXiv abstract page) |
| Files in this folder | `paper.pdf`, `note.md` |
| What was read | Sections 1 to 6 and Appendices B and C in full. The arXiv HTML stops inside Table 20; from there (C.2.6 to C.4.4, pages 49 to 66) the text of the PDF was read. Appendix A (standard definitions) was not read. No figure was viewed. |
| Read on | 21 November 2026 |

Confidence tags: **[P]** the writer of this note read the statement in the primary source, and the
place is given (section, table, figure or page). **[S]** the statement comes from a secondary source,
which is named. **[U]** the statement is not verified. A number without a tag is not permitted.

Survey K (Section 2.3) of this repository gives the sizes, the statement/proof split, the depths and the import utilisation. Survey K could not read the degree statistics. This note gives the full list of measures; rows marked (K) repeat Survey K.

## 1. What the work is

The work is a descriptive network study of Mathlib at one commit (534cf0b, 2 February 2026) [P, Section 1]. It builds three graphs: of files, of declarations and of namespaces. It applies standard network measures to each graph. It makes three claims [P, Section 2]. The file and name hierarchy differs from the logical dependency structure. Files import far more than they use. Centrality shows language infrastructure and not mathematical importance. The work tests no prover and no agent.

## 2. How it works

- **Declaration graph.** A node is a declaration: theorem, definition, abbreviation, constructor, inductive type, opaque, quotient or axiom. An edge `d1 -> d2` is a plain arrow. It says that `d2` is a named constant in the elaborated proof term of `d1` [P, Def. B.2.1]. The graph comes from the terms of the prover, not from the text. It has 308,129 nodes and 8,436,366 edges [P, Section 1]; Section 5 says 317,655 nodes.
- **Module graph.** A node is a file; an edge is an `import`. 7,563 nodes, 23,570 edges [P, Def. B.1.5].
- **Namespace graph.** A node is a name prefix cut at depth `k`. The weight of an edge is the number of declaration edges between the two prefixes [P, Def. B.3.1].
- **Synthesized edges.** A *synthesized edge* is an edge that the elaborator inserts for instances, coercions and numerals. The source text does not show it. 6,257,832 edges are synthesized and 2,178,534 are explicit [P, Def. B.2.4].
- **Statement and proof edges.** A second partition separates edges from the statement, from the proof, and from both [P, Def. B.2.2].
- **Tools.** importGraph, jixia, lean-training-data; NetworkX, python-louvain, powerlaw. An AI system ran the tools; persons chose the questions [P, Section 5].

## 3. How it splits a proof

The work does not split proofs. One observation bears on splits. A tactic proof in Mathlib has a median of 2 steps and a mean of 4.1. 39.2% have one step, and 9.4% have ten or more [P, C.2.9, PDF p. 53]. `have` is 7.4% of all tactic steps [P, Table 24].

## 4. What it says about scale

- The longest import chain has depth 153: 154 layers, 1,433 files that no file imports, median layer width 25 [P, C.1.3].
- The critical path has 161 modules. The "parallelism ratio" is 7,563/161, about 22.4 [P, Def. B.1.9]. The ratio counts modules; it uses no measured compile time (reader's observation).
- Transitive reduction removes 4,122 of 23,570 import edges (17.5%) [P, B.1.3].
- *Import utilisation* is the share of the declarations of an imported file that the importing file references. Median 1.6%, mean 5.1%; 37% of import edges have zero utilisation [P, C.4.2].
- Of the cross-file declaration dependencies, 92.2% go through a transitive import chain [P, Table 34].
- *Module cohesion* is the share of the edges at a file that stay inside the file. Mean 0.107, median 0.074 [P, Table 33].
- A file holds about 44 declarations. The authors note that an AI author can use finer files "optimized for compilation parallelism" [P, C.4.4].

No build times and no merge-conflict figures. A co-modification graph over pull requests is defined and not computed [P, B.4.1].

## 5. Evidence

Measures on the declaration graph:

| Measure | Value | What the authors say it shows | Place |
|---|---|---|---|
| In-degree | mean 27.38, median 1, sd 620.10, max 89,936 (`OfNat.ofNat`); 119,633 nodes with zero | reuse is open-ended; the hubs are infrastructure | [P, Table 16] |
| Out-degree | mean 27.38, median 19, sd 29.18, max 522; theorems: mean 30.8, median 21 | bounded by what one proof can hold | [P, Tables 12, 16] |
| Power-law fit | in: alpha 1.781, x_min 20, truncated power law fits better; out: lognormal fits better | the graph is not scale-free | [P, Table 17] |
| DAG depth (K) | 84 layers; module graph 153; namespace graph 8 after cycles are merged | file layering is deeper than the logic needs | [P, C.2.4, C.3.3] |
| PageRank; betweenness (500 samples) | no declaration is in all three top-10 lists; 11.2% of nodes have non-zero betweenness | in-degree: vocabulary; PageRank: foundations; betweenness: bridges | [P, Table 18] |
| Louvain communities | 22; modularity 0.4757; NMI with top namespace 0.3432, ARI 0.1817 | naming and logic agree only in part | [P, Tables 19, 21] |
| The same, module graph | 16 communities; modularity 0.6395; NMI 0.42 | files follow directories more | [P, Table 7] |
| Robustness | one node removed: at most 6 nodes cut off; 20% removed by PageRank: 0.461 remain; random: 0.799 | hub-dominated | [P, Table 22] |
| Theorems never cited | 109,088 of 243,725 (44.8%) | the outer surface of the library | [P, C.2.2] |
| Edge by boundary | same file 9.6%; other file, same namespace 9.6%; cross-namespace 50.9%; no file data 29.9% | names do not contain dependencies | [P, Table 14] |
| Containment | top directory 48.9%; namespace depth 1: 22.2%; depth 2: 14.2% | the name tree is informative for two levels only | [P, Table 27] |
| Statement / proof / both (K) | 8.1% / 43.9% / 48.0% | proofs shape the graph more than statements | [P, Table 2] |
| Synthesis ratio | 74.2% | most edges are tool-made | [P, Def. B.2.4] |
| Definitional height (K) | median 7, mean 10.1, max 60 | hidden coupling through unfolding | [P, C.2.9] |
| `theorem` against `lemma` keyword | mean in-degree 5.16 against 3.52 (1.47 times); never cited 37.2% against 39.4% | a human label of importance agrees weakly with position | [P, Table 23] |

The last row is the only validation against a human judgement. No measure is tested against proof success or repair success. There is no baseline library.

## 6. Limits

The authors state three limits [P, Section 6]. The study uses one commit. Louvain has a resolution limit. The "process" is inferred, not observed.

Reader's limits: numbers differ inside the paper.

- Nodes: 308,129 or 317,655 [P, Sections 1, 5].
- Import edges: 23,570, 23,235 or 30,793 [P, B.1.2, Table 34, C.4.2].
- `Eq.refl` is second by in-degree in Section 2 and "single most-cited" in B.2.1.
- C.4.4 gives "86.9%" containment at depth 3; Table 27 gives 12.6%.
- Table 14 gives 50.9% cross-namespace edges, with no file data for 29.9% of the edges. Table 27 gives 77.8% at namespace depth 1. The two figures use different groupings, and the paper does not define them in one place.

## 7. Relation to the two anchors

**MathEye.** MathEye builds its graph inside one proof script, from syntax. This work builds a graph between declarations, from elaborated terms. This work shows that degree and centrality measure infrastructure. MathEye prices an obligation by a model score and by the size of the proof state, not by graph position. This finding supports that choice (reader's inference).

**Turing Agent.** The Turing Agent holds obligations in a directed acyclic graph and reports about 10% of proved lemmas as unused. In Mathlib 44.8% of theorems have no citation; there a leaf theorem is part of the interface. The ratio of nodes to critical-path length can be computed on the graph of the Turing Agent as a bound on parallel speed-up (reader's proposal).

This work is earlier than both anchors by more than six months. The texts of both anchors do not contain its title or number (searched). It cites LeanArchitect, leanblueprint and LeanDojo. It cites no `sorry`-repair work.

## 8. What this repository can use

- **Read the lexer graph as the explicit layer.** `graphs.jsonl` holds token mentions. That is close to the 2,178,534 explicit edges. The authors call the explicit subgraph "a closer proxy for human-intended dependencies" [P, Section 6]. A later T2 run must tag each edge as explicit or synthesized, and must keep the T1 edge.
- **Check the `where` field.** The repository edge already carries `statement`, `body` or `both`. Compare its shares with 8.1 / 43.9 / 48.0 as a rough test of the lexer.
- **Do not rank by in-degree alone.** `n_users` counts reuse. The hubs here are `Eq.refl` and coercions. Restrict reuse counts to declarations of class `theorem` in the copied files.
- **Add cohesion and utilisation of a split.** Cohesion: the share of `uses` edges of a parent and its children that stay inside the group. Utilisation: the share of a child file that the parent uses. Low values mean that a child is in the wrong file.
- **Baseline for proof length.** A human proof of ten or more steps is in the top 9.4%. The library entries come from that tail; state this when the library is compared with agent output.
- **Scale.** A rebuild follows files. But 92.2% of the dependencies pass through transitive imports, and the median utilisation is 1.6%. Most forced rebuilds are therefore not logically necessary. With one lemma for each file, the rebuild cone equals the dependency cone, and agents share no file (reader's inference from C.4.4).

## 9. Open points and things not read

- Do the measures change over time? The temporal graphs are defined and not computed [P, B.4.2].
- Does any measure predict which declaration is hard to prove or to repair? Not tested.
- Not read: Appendix A; the data set; the figures.
