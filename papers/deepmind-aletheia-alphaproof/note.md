# Google DeepMind: AlphaProof Nexus (with a short comparison to Aletheia)

| Field | Value |
|---|---|
| Authors, organisation | George Tsoukalas, Anton Kovsharov, Sergey Shirobokov, Anja Surina and 17 others (21 names, reader's count), among them Thomas Hubert, Pushmeet Kohli and Swarat Chaudhuri. Google DeepMind; one author at Aarhus University |
| Date and version read | "Advancing Mathematics Research with AI-Driven Formal Proof Search", version 2, 8 June 2026 (version 1: 21 May 2026). For comparison: "Semi-Autonomous Mathematics Discovery with Gemini", arXiv 2601.22401, version 3 |
| Source | arXiv 2605.22763, https://arxiv.org/abs/2605.22763 ; proofs at https://github.com/google-deepmind/alphaproof-nexus-results . Aletheia: https://arxiv.org/abs/2601.22401 |
| Licence of the source | CC BY-NC-ND 4.0 (arXiv pages of both papers) |
| Files in this folder | `paper.pdf` (arXiv 2605.22763), `note.md` |
| What was read | 2605.22763: main text (Sections 1 to 6), Appendix A.1 and Appendix B.1 to B.3 in full, from the arXiv HTML. Appendix B.4 (proofs) not read. No figure viewed; captions read. 2601.22401: abstract and Sections 1.1 to 1.3 only. The results repository was not opened |
| Read on | 21 November 2026 |

Confidence tags: **[P]** the writer of this note read the statement in the primary source, and the
place is given. **[S]** the statement comes from a secondary source, which is named. **[U]** the
statement is not verified. A number without a tag is not permitted. Places refer to arXiv
2605.22763 unless "Aletheia" is written.

## 1. What the work is

AlphaProof Nexus is a framework for agents that search for Lean proofs of open problems. It is the
newest primary source of 2026 from Google DeepMind on formal proof search. The earlier surveys do
not mention it (name search, 21 November 2026). The paper claims that its strongest agent proved 9
of 353 open Erdős problems and 44 of 492 conjectures from the OEIS [P, abstract]. It also reports
that a much simpler agent proved the same 9 Erdős problems, at a higher cost on the hardest ones
[P, abstract; Section 5]. The evidence is a comparison of four agent designs by cost.

## 2. How it works

The input is a *proof sketch*: a Lean file with the target theorem and `sorry` in place of the
proof [P, Section 2]. Markers in the file say which parts the agent can change. Inside an
`EVOLVE-BLOCK` the agent can add helper lemmas, definitions and proof steps [P, Section 2].

The paper builds four agents [P, Section 2].

- **Agent A, basic.** N prover subagents run in parallel and share no state. Each one loops over
  *episodes*. An episode is one multi-turn session of Gemini 3.1 Pro with a search-and-replace
  tool. Lean compiles the sketch after each edit. If `sorry` remains at the end, the subagent
  writes the lessons of the episode as a comment in the sketch. The next episode starts from that
  sketch [P, Section 2; Appendix A.1].
- **Agent B.** Agent A with AlphaProof as a tool. AlphaProof receives one goal and returns a
  proof, a disproof, or a failure message [P, Section 2].
- **Agent C.** Subagents share a database of sketches. Rater agents (Gemini 3.0 Flash) rank 7
  sketches at a time. The rankings become Elo scores, and the scores decide which sketch a
  subagent continues [P, Section 2; Appendix A.1]. The rating exists because a proof check gives
  only yes or no, and a search needs a graded signal.
- **Agent D, full.** B and C together.

## 3. How it splits a proof

- **Unit.** A helper lemma with `sorry`, inside the Lean file of the target.
- **Who chooses.** The prover subagent. The controller sometimes adds an instruction such as
  "decompose unsolved goals" to the prompt [P, Appendix A.1, step 2]. Figure 1 shows one case: the
  prover "decomposed that goal into three simpler lemmas" [P, Figure 1 caption].
- **The check before work on the children.** There are two. First, the sketch must compile with
  the `sorry` lemmas in place, and a sandbox check confirms that the target statement is unchanged
  [P, Appendix A.1, step 3]. A sketch that compiles is a proof of the parent from the children.
  Second, AlphaProof can return a *disproof* of a child, which goes into the prompt [P, Section 2].
- **Record.** No tree and no graph. The record is a population of whole sketches with scores, and
  a *global goal cache*. The cache stores each subgoal under a hash of its exact Lean context and
  target. A subgoal that any sketch proved or disproved is not attempted again [P, Appendix A.1,
  "Global Goal Caching"].
- **When a child fails.** AlphaProof stops after about 400 simulations. The failure text stays
  with that subgoal in later prompts [P, Appendix A.1, "AlphaProof Budget"].

Aletheia does not split proofs formally. It writes natural-language proofs and has a
natural-language verifier [P, Aletheia, Section 1.1].

## 4. What it says about scale

The work is at the scale of one theorem. It gives no count of lines or lemmas.

- Agents C and D use 10 subagents for one attempt. Agents A and B were run as 100 independent
  subagents [P, Section 5].
- The search stops after 3000 episodes for one problem [P, Section 3]. One episode has at most 5
  AlphaProof queries and 90 edits [P, Appendix A.1].
- Cost: "a few hundred dollars per problem" [P, Section 1]. AlphaProof adds about 27.5 TPU hours,
  $60, for each problem [P, Section 5, "Cost and Variance"].
- To handle large Lean files, the subagent sends edits as diffs and does not rewrite the file
  [P, Appendix A.1, step 3].
- The agent was used inside "a larger effort on the AI-driven formalization of the Stacks
  Project", after people fixed the definitions and statements. No size is given [P, Section 4].
- Nothing is said about rebuild time or about agents that edit shared files. Each subagent works
  on its own copy of one file.

Aletheia gives a scale fact of another kind [P, Aletheia, Section 1.1, Table 2]. Of 700 open
Erdős problems, 212 answers passed its verifier. People graded 200 answers: 137 were flawed, 63
were technically correct, and 13 answered the intended question.

## 5. Evidence

| Result | Place |
|---|---|
| Agent D: 9 of 353 Erdős problems from Formal Conjectures | Section 3, Table 1 |
| Agent D: 44 of 492 OEIS conjectures, statements made by Gemini | Section 3 |
| Agent A solves all 9 Erdős problems | Section 5 |
| Agent D costs 2x to 5x less than A and B on problems 138 and 125, and is about half as cost-efficient on the rest | Section 5 |
| Agent A with Gemini 3.0 Flash or 3.1 Flash-Lite: 0 of 9 | Section 5; Appendix B.3 |
| AlphaProof alone, about 64 TPU hours for each problem: 0 of 9 | Appendix B.3 |
| Codex with GPT-5.5: 7 of 9. Claude Code with Opus 4.7: 0 of 9 | Section 5; Appendix B.3 |

The comparison of A, B, C and D is an ablation of the harness at a fixed model. It does not
isolate the split: all four agents can add helper lemmas. It shows that shared state and the
AlphaProof tool pay only on the hardest problems.

The failure analysis bears on splitting [P, Section 3, "Failure Analysis"]. The agent "frequently
offloaded a problem's core difficulty into a single sorry within a helper lemma that reiterated
the target statement in a slightly different form". A prompt against this behaviour did not stop
it. Other top sketches used `sorry` lemmas that the agent called known results. A manual check
found that these results did not exist.

## 6. Limits

Stated by the authors [P, Section 6; Section 5, "Cost and Variance"]:

- Results are in areas where Mathlib is mature and "tasks often decompose into tractable
  subgoals".
- Most Erdős problems stay out of reach.
- The search has high variance.
- The reported cost leaves out the cost of finding which problems are tractable.

Found by the reader:

- The framework is not released. Only the proofs are public. The models are commercial, and
  AlphaProof is closed.
- The comparison uses only the 9 problems that Agent D had solved, so it favours D.
- The compile check accepts a split whose child restates the parent.

## 7. Relation to the two anchors

**Turing Agent (arXiv 2611.21299)** is later by six months. It cites the AlphaProof paper and the
Aletheia paper, and not this paper (checked in `refs_2611.21299.json`). The same: a sketch with
`sorry`, parallel workers, and lessons that survive a context reset (a comment here, an
"experience pool" there). Different: Turing Agent keeps a directed acyclic graph and checks each
split as a separate step. Nexus keeps whole sketches. Nexus has three mechanisms that Turing Agent
lacks. They are a disproof tool for children, a goal cache keyed by the exact Lean state, and a
score for unfinished sketches. Nexus also has the cost figures and the harness ablation that Turing Agent
lacks.

**MathEye (arXiv 2611.22103)** is later and does not cite this paper. A Nexus sketch is what
MathEye calls an angelic proof. MathEye chooses the cheapest sufficient set of open obligations
and asks a person. Nexus sends every open obligation to AlphaProof and ranks sketches by a model's
opinion. The Nexus failure, one `sorry` that restates the target, is the case that MathEye's cost
model must price as expensive.

## 8. What this repository can use

- **A test for a null split.** A child that is equivalent to its parent is a known failure of an
  agent. The proposed algorithm can reject a split when one child alone implies the parent and the
  parent implies that child.
- **Disprove before you prove.** A cheap disproof attempt on each child removes false children
  before agents work on them.
- **A goal cache keyed by the exact proof state.** It removes repeated work when parallel agents
  produce the same child. This is a small-scale answer to the interference problem.
- **Compare against a plain loop.** The basic agent matched the full agent on 9 of 9 problems. Any
  claim for a decomposition method needs this baseline at equal cost.

## 9. Open points and things not read

- Appendix B.4 and the results repository were not read. The lemma counts of the 9 proofs are not
  known to this note.
- Figures 3, 9, 10 and 11 hold the cost data; they were not viewed.
- "AI co-mathematician" (arXiv 2605.06651, Google DeepMind) was downloaded and not read.
- AlphaProof itself is described in the earlier surveys and is not repeated here.
