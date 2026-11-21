# Autonomous AI Agents Systematically Diverge From Human Preferences in Proof Formalization

| Field | Value |
|---|---|
| Authors, organisation | Bálint Gyevnár (Institute for Complex Social Dynamics, Carnegie Mellon University); Simon DeDeo (Carnegie Mellon University; Santa Fe Institute) |
| Date and version read | 4 November 2026, v1 |
| Source | arXiv 2611.06995, https://arxiv.org/abs/2611.06995. Data and code: https://github.com/gyevnarb/proof-divergence (not opened) |
| Licence of the source | CC BY 4.0 (arXiv abstract page) |
| Files in this folder | `paper.pdf`, `note.md` |
| What was read | Full main text; Appendices A, B and C with all tables; Figures 3 and 4 rendered and viewed. Reference list searched. |
| Read on | 21 November 2026 |

Confidence tags: **[P]** the writer of this note read the statement in the primary source, and the
place is given (section, table, figure or page). **[S]** the statement comes from a secondary source,
which is named. **[U]** the statement is not verified. A number without a tag is not permitted.

No earlier survey of this repository covers this work.

## 1. What the work is

The work is an observational study. It asks where a coding agent edits a Lean project when the agent is free to choose. It replays the commit histories of nine human formalisation projects. At each human commit, an agent gets the parent state and the request to "take the next step". The study compares the edit of the agent with the edit of the human. It finds that agents go to `sorry` markers, to short definitions, and to the top and bottom of the dependency graph. It measures the place of an edit. It does not measure whether an edit compiles or is correct.

## 2. How it works

1. **Data.** Nine repositories, among them `flt`, `pfr`, `sphere` and `apap`. Mean size 12,822.22 lines and 717.89 commits; 1 to 61 editors [P, Table 2]. Merge commits are removed [P, A.1].
2. **Simulated collaboration.** A *simulated collaboration* is one run in which an agent continues from a human parent commit and produces its own child commit. The agents are Claude Code (Opus 4.6), Codex (GPT-5.2) and Gemini CLI (Gemini 3.1 Pro). There is no stopping condition and no budget [P, A.1].
3. **Graph.** A node is one definition, that is, one declaration. An edge `A -> B` is a plain arrow: the signature or the body of `A` references `B`. References to Mathlib are excluded [P, A.3]. A lexical parser builds the graph from the text, because a build of each commit takes "minutes to hours" [P, Appendix B]. All commits together give more than 4.7 million nodes and 10.8 million edges [P, A.1].
4. **Features of a definition** [P, A.3].
   - *Max leaf*: the largest of the shortest distances to the leaves that the definition can reach. It says how far the definition is above the axioms.
   - *Root distance*: the undirected shortest distance to a main root. A greedy rule adds roots until the transitive closure grows by less than 5%.
   - *Distance to sorry*: the undirected distance to the nearest definition that holds a `sorry`.
   - *Surprise*: the mean negative log-probability of the tokens under a prover model.
5. **Model.** A mixed-effects logistic regression predicts whether an actor modifies a definition of the parent commit [P, A.4].

## 3. How it splits a proof

The work does not split proofs. The nearest observation is the number of new definitions [P, Table 1]:

| Actor | Definitions added | Share |
|---|---|---|
| Human | 10,618 | 0.90% |
| Claude | 4,640 | 0.39% |
| Gemini | 1,974 | 0.17% |
| Codex | 2,056 | 0.17% |

## 4. What it says about scale

- 4,711,972 definition observations in total [P, Table 1]. No cost, token or time figures for the agents.
- Between 82% and 99% of all references go to Mathlib or the core library [P, Appendix B].
- Agents make isolated edits. For Claude, Gemini and Codex, 77%, 69% and 82% of the edits connect to no other definition edited in the same commit [P, Section 2.2.1].
- For humans, 62% of the edits connect to another edited definition [P, Section 2.2.1].

## 5. Evidence

| Finding | Human | Claude / Gemini / Codex | Place |
|---|---|---|---|
| Share of modifications in definitions that hold a `sorry` (4.2% of all definitions hold one) | 19.4% | 92.4% / 79.9% / 59.1% | [P, Fig. 3] |
| Share of modifications at distance two from a `sorry` | 35.1% | 1.2% / 7.2% / 25.7% | [P, Fig. 3] |
| Definitions removed | 4,913 (0.41%) | 408 / 618 / 57 | [P, Table 1] |
| Median characters changed in a modification | 20 | 149.5 / 84 / 103 | [P, Table 1] |
| Median characters of an added definition | 133 | 171 / 193 / 135 | [P, Table 1] |
| Log-odds for `Has sorry` (agents: deviation from human) | 1.969 | +4.556 / +3.074 / +1.714 | [P, Table 6] |
| Log-odds for size (rank) | 2.207 | -1.579 / -1.766 / -2.562 | [P, Table 6] |
| Log-odds for surprise of the signature | 0.024 | -0.877 / -0.338 / -0.390 | [P, Table 6] |
| Change of body surprise after a modification (nats per token) | -0.062 | -1.081 / -0.813 / -0.605 | [P, Fig. 4] |
| AUC of the fixed effects | 0.742 | 0.968 / 0.905 / 0.802 | [P, Table 6] |

- **Position.** The edit probability of an agent is lowest one to three dependency steps above a leaf, and about three steps from a main root. Humans work more in the middle [P, Section 2.2.2].
- **Premature filling.** A `sorry` declaration that an agent chose for an edit later gets a new signature "between 25% (Codex) and 48% (Claude) of the time" [P, Section 3.1].
- **Parser against the Lean compiler.** Definitions: F1 0.999. Edges: precision 0.862, recall 0.614 [P, Table 3].
- **Why recall is low.** 24% of the kernel dependencies are never written by name. Among the named dependencies, recall is 0.84 [P, Appendix B].

There is no ablation and no test of proof success.

## 6. Limits

The authors state five limits [P, Limitations]. The graph is lexical. The repositories can be in the training data. "The human" is an average of up to 61 persons. Merge commits are excluded. The regression is correlational.

Reader's limits.

- The work reports edits. It does not report the number of lemmas in a finished proof, lemma reuse, naming or statement form.
- The parser recovers root distance poorly: rank correlation 0.32 to 0.65 in the four largest projects [P, Appendix B].
- The caption of Figure 4 says "definitions containing at least one sorry". Its values equal the pooled average of both rows of Table 5. Reader's calculation for the human row: `(1232 x -0.345 + 5129 x 0.006) / 6361 = -0.062`.

## 7. Relation to the two anchors

**MathEye.** MathEye computes which open obligation a person must judge. This work shows what agents do with no such rule. They fill the marked hole and ignore its neighbourhood. Humans work two steps away, where they restate lemmas. From 25% to 48% of the filled holes get a new statement later. That supports the MathEye step of a truth question before a proof attempt (reader's inference).

**Turing Agent.** The Turing Agent reports about 10% of proved lemmas that no proof uses. This work reports that agents almost never remove definitions. Both observations point to growth without clean-up (reader's inference).

This work is earlier than both anchors by about two weeks. The texts of both anchors do not contain its title or number (searched). It cites SorryDB, LeanArchitect and APE-Bench. It cites no `sorry`-repair prover and not the Mathlib network study.

## 8. What this repository can use

- **A measured error rate for a lexer graph.** `graphs.jsonl` is the same kind of graph. Its hand audit gives 96.4% recall against the visible text (`graph.md`, Validation). This work shows that 24% of the kernel dependencies have no name in the text. A further 2.6% occur only through notation [P, Appendix B]. State this bound in `graph.md` until a T2 run exists.
- **Three node features.** Add max leaf, root distance and distance to the nearest `sorry`, as ranks within one project. They predict where humans and agents edit.
- **The case for a human library.** Humans add more definitions, remove more, and edit connected groups in the middle of the graph. Agents do not reproduce these choices. The work does not show that the human choice gives a better proof; that test is open.
- **Overlap with the library.** By the names of the entry folders, 18 entries come from four of the nine projects: `flt-imperial` 6, `pfr` 6, `sphere-packing` 4, `apap` 2 (reader's count).
- **Harvest from commits.** A human commit that adds definitions and modifies a parent is a dated split. The released dataset marks added, modified and removed definitions at each commit.
- **A statement check before a fill.** Do not rank open goals by the `sorry` marker alone. First ask whether the statement is stable.
- **Scale.** Isolated edits collide less in a merge queue. A restructuring needs connected edits. Parallel `sorry`-filling therefore selects against restructuring (reader's inference).

## 9. Open points and things not read

- Do the edits of the agents compile? The work does not say.
- Does a prompt that names a target lemma remove the differences? The study tests one prompt [P, A.1].
- Not read: the code repository.
