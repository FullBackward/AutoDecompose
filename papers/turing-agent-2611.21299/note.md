# Turing Agent: Agentic Formal Verification for Mathematical Research

| Field | Value |
|---|---|
| Authors, organisation | Yang Chen, Qianyi Wang, Ronghui Yang and 13 others; contact authors Shuyue Hu, Yang Chen and Qianyi Wang. Agent Center of the Shanghai Artificial Intelligence Laboratory, with the University of Electronic Science and Technology of China, the University of Hong Kong, and the Shanghai University of Finance and Economics |
| Date and version read | 16 November 2026, version 1 |
| Source | arXiv 2611.21299, https://arxiv.org/abs/2611.21299 ; project page https://wangqy031216-cloud.github.io/turing-agent |
| Licence of the source | CC BY 4.0 (arXiv page) |
| Files in this folder | `paper.pdf`, `note.md`, `figures/fig6-results.png`, `figures/fig7-hypergraph.png`, `figures/fig8-matrix-hitting.png`, `figures/fig9-3sat.png`, `traces/` (measures from the project page, with the scripts) |
| What was read | Full main text (Sections 1 to 6) from the arXiv HTML. Appendices A to C searched, not read in full. Figures 6, 7, 8 and 9 viewed. Figures 1 to 5 not viewed. The three trace files of the project page parsed in full; its harness and results pages read |
| Read on | 21 November 2026 |

Confidence tags: **[P]** read in the primary source at the place given. **[S]** from a secondary
source. **[U]** not verified. Counts marked "reader's count" were made by the writer of this note
from the figures.

## 1. What the work is

Turing Agent is a harness. A harness is the program that gives a language model its tools, its
instructions and its control loop. This harness formalises research mathematics in Lean. It
receives an informal theorem and an informal proof. It writes a Lean statement, and then it writes
a Lean proof that the Lean kernel accepts. The paper claims that the harness is better than plain
coding agents at the statement step, and that it completes three research problems that an earlier
system left incomplete [P, abstract]. The evidence is two benchmarks and three case studies.

## 2. How it works

The harness has two types of agent [P, Section 3].

- **The theorem formalisation agent (TF agent).** It searches Mathlib and CSLib for definitions,
  adds definitions that are absent, and writes the Lean statement. Lean examines the statement.
  Then the agent compares the statement with the original text: domains, assumptions, the order
  of quantifiers, and the conclusion. The statement of the main theorem does not change after
  this step [P, Section 3.1].
- **The proof formalisation agents (PF agents).** A PF agent follows the informal proof and
  writes the Lean proof. It splits a goal into intermediate claims when that is necessary
  [P, Section 3.2].

Three more mechanisms support the PF agents.

- **Selective semantic review.** A PF agent asks the TF agent to examine an intermediate claim
  only when the meaning of the claim is not certain. The paper gives the reason: a review of each
  claim uses many model calls [P, Section 3.2.2].
- **Experience pool.** When the history of an agent becomes too long, the harness compresses it.
  Before that, the agent saves short records: a library lemma that was useful, a side condition
  that was necessary, the cause of a failure. The harness gives the related records to the agent
  on its next attempt [P, Section 3.2.3].
- **Final verification.** An independent Lean kernel examines the complete proof. Then a review
  agent compares the proof with the informal argument [P, Section 3.3].

## 3. How it splits a proof

- **Unit.** The unit is an intermediate claim: a Lean statement of a lemma.
- **Who chooses.** A PF agent chooses the split. Its input is the informal proof. The paper gives
  no rule for when to split: the agent splits "when needed" [P, Section 3.2.1].
- **Check before work.** The agent must show in Lean that the child statements, used as
  assumptions, imply the parent. The harness accepts the split only after this check. The same
  procedure applies to each child [P, Section 3.2.1]. This check finds a wrong split before any
  work on the children.
- **Record.** A directed acyclic graph holds the claims and their dependencies. A directed acyclic
  graph is a set of nodes and arrows in which no path returns to its start.
- **When a child fails.** The agent revises the proof or splits the claim again. The harness
  examines each completed branch again before it uses the branch in the parent [P, Section 3.2.1].

## 4. What it says about scale

**The paper.**

- Two case studies have 27 and 108 auxiliary lemmas [P, Section 5.2; Section 5.3]. The paper
  gives no count for the first case study.
- Independent children go to PF agents that work at the same time [P, Section 3.2.1]. The paper
  gives no number of agents.
- The paper gives no figures for tokens, money, time, rebuild time or conflicts between agents.
- The paper does not refer to the scaling problem of Prove2Me, and it does not cite Prove2Me.

**The project page.** The page publishes one trace file for each case study. `traces/README.md`
describes the files and the scripts. All figures in this part are [P, project page trace files,
field `meta`], or the reader's computation from the field `nodes`.

| Measure | Matrix hitting | Hypergraph influence | Random 3-SAT |
|---|---|---|---|
| Model | DeepSeek-V4-Pro | DeepSeek-V4-Pro | DeepSeek-V4.1-Flash |
| Time from start to end | 9,412 s (2.6 h) | 312,128 s (86.7 h) | 169,417 s (47.1 h) |
| Active time | 8,362 s (2.3 h) | 245,668 s (68.2 h) | 63,349 s (17.6 h) |
| Tool calls | 544 | 9,827 | 2,302 |
| Lean probes | 60 | 1,143 | 625 |
| Failures | 27 | 691 | 242 |
| Compactions of the context | 23 | 595 | 129 |
| Lessons saved | 11 | 273 | 108 |
| Semantic reviews | 0 | 3 | 4 |
| Auxiliary lemmas proved | 0 | 27 | 108 |
| Planned claims dropped before a proof | 8 | 3 | 1 |
| Declared dependencies between proved claims (reader's count) | 0 | 40 | 227 |
| Longest chain below the main theorem (reader's count) | 0 | 7 | 17 |
| Direct dependencies of the main theorem | 0 | 9 | 12 |
| Auxiliary lemmas that two or more claims depend on (reader's count) | 0 | 9 of 27 | 69 of 108 |
| Total lines of proof bodies (reader's count) | 17 | 818 | 1,920 |

The trace files give four facts that the paper does not give.

1. **The first case study has no auxiliary lemma.** The agent planned 8 claims. The 8 claims
   stayed in the graph for 5,176 s of the 9,412 s run, and then the agent dropped all 8. It found
   that an existing theorem of the OpenAI library, `universal_hitting`, already contains the
   argument [P, trace 116, `meta.summary`; times `t_in` 2,283 and `t_out` 7,459]. The 7 boxes in Figure 8 are existing library results that the
   final proof refers to. They are not lemmas that the agent proved.
2. **The work is not even across the claims.** In the hypergraph run, 3 of 28 claims have 57 % of
   the failures, and one claim (`block_restriction_estimate`) has 220 failures. In the 3-SAT run,
   11 of 109 claims have 71 % of the failures, and 59 of 109 claims have no failure (reader's
   computation).
3. **The graph grows during the run.** In the 3-SAT run, 27 of 110 claims enter the graph in the
   first 10 % of the time, and only 32 in the first half. The agent does not plan the full split
   at the start (reader's computation from `t_in`).
4. **The top of the graph is a chain.** In the 3-SAT run the claims at each height above the
   leaves number 36, 18, 12, 5, 7, 7, 5, 3, 3, 2, 3, 2, and then 1 for six levels. Parallel work is
   possible at the bottom only (reader's computation).

Three runs with two models and three problems do not permit a comparison between the models.

## 5. Evidence

Pass@1 in percent, one final submission for each problem [P, Figure 6; Section 4.2]:

| Task, model | Model alone | Codex CLI | Claude Code | Turing Agent |
|---|---|---|---|---|
| RLMEval, 248 theorems, GLM-5.3 | 16.94 | 41.94 | 80.24 | 82.66 |
| RLMEval, 248 theorems, DeepSeek-V4-Pro | 18.95 | 74.60 | 86.69 | 82.66 |
| Formal TCS Bench, 143 statements, faithful, GLM-5.3 | 8.39 | 29.37 | 40.56 | 57.34 |
| Formal TCS Bench, 143 statements, faithful, DeepSeek-V4-Pro | 7.69 | 27.97 | 29.37 | 61.54 |
| Formal TCS Bench, statement compiles, GLM-5.3 | 10.49 | 69.23 | 83.22 | 97.20 |
| Formal TCS Bench, statement compiles, DeepSeek-V4-Pro | 13.29 | 40.56 | 76.22 | 99.30 |

Reader's counts from the proof graphs [P, Figures 7 to 9, reader's count], beside the flag `used`
of the trace files [P, project page]:

| Problem | Auxiliary lemmas proved | Drawn grey ("not referenced") in the figure | Flag `used` is false in the trace | Added by the agent (figure) | Sent to semantic review |
|---|---|---|---|---|---|
| Matrix hitting points | 0 | 0 | 0 | 0 | 0 in the trace; the figure marks the main theorem |
| Hypergraph influence bound | 27 | 2 | 0 | 9 | 3 |
| Random 3-SAT variance | 108 | 12 | 3 | 38 | 4 |

**"Used" has three meanings in this one project, and they give three numbers.** For the 3-SAT run:
the flag `used` is false for 3 lemmas; the figure draws 12 lemmas grey; and 15 lemmas cannot be
reached from the main theorem through names that occur in the proof bodies (reader's computation
with `traces/trace_deps.py`). All 12 grey lemmas are among the 15. The cause is visible in the
data: a claim declares 227 dependencies in total, and the proof bodies name only 157 of them. One
claim, `delay_uniform_bound`, declares 52 dependencies and names 16. The method of names does not
work on the hypergraph run, where the main theorem names only 2 of its 9 declared dependencies.

**No ablation isolates the split.** The paper does not run the harness without decomposition.
On proving, the full harness is 2.42 points above Claude Code with one model and 4.03 points
below it with the other [P, Section 4.2].

## 6. Limits

Stated by the authors:

- The agent proves lemmas that the final proof does not use. The authors name better planning of
  dependencies as future work [P, Section 1].
- Future work includes better semantic checks and better decomposition [P, Section 6].

Found by the reader:

- A language model (GPT-6.1 Sol) is the judge of "faithful" on Formal TCS Bench, not the
  benchmark's own metric [P, Section 4.1].
- RLMEval runs in "easy mode": the lemmas of the project are available to the prover
  [P, Section 4.1]. The set is two projects of RLMEval, not all of it.
- The authors selected the three case studies from 22 problems that had no complete Lean proof
  [P, Figure 3 caption]. The paper does not report the other 19.
- The proof graphs in the paper group the lemmas by topic and omit the arrows [P, Figure 7
  caption]. The arrows are in the trace files of the project page.
- The count of 38 depends on box borders at reduced size. It can be wrong by 1 or 2.
- **The check of a split proves that the children are sufficient. It does not prove that each
  child is necessary.** A parent passes the check when its proof uses only some of the declared
  children. The 70 declared dependencies that no proof body names are the evidence (3-SAT run).
  This is the reader's inference.
- The hypergraph run needed 86.7 hours and 595 compactions of the context for 27 lemmas. The paper
  does not report this cost.

## 7. Relation to MathEye and to earlier work

- **MathEye (arXiv 2611.22103), one day later.** The two works share the principle that the
  structure of a proof is kept while single obligations stay open. They differ in three ways.
  Turing Agent examines a split before work on the children; MathEye examines the sketch after it
  fails. Turing Agent has no procedure to select the level at which to work; MathEye selects it
  with a solver. In Turing Agent a model closes each obligation; in MathEye a person answers.
  Neither work cites the other.
- **Earlier work.** Hilbert (arXiv 2509.22819) splits difficult claims again when a prover fails;
  the paper cites it [P, Section 2.2]. Prove2Me (arXiv 2608.28433) states the same check at the
  level of a platform: a parent is verified exactly when its children are. The paper does not
  cite Prove2Me, Goedel-Architect or APOLLO (searched in the full text).

## 8. What this repository can use

- **The check "children imply parent" as a build step.** The library's `glue_check` reads text.
  The review of 15 November found it lenient. A check by the prover is the correct form.
- **A baseline for waste, with its definition.** Of 135 auxiliary lemmas that the agent proved,
  the figures draw 14 grey (10 %) and the flag `used` is false for 3 (2 %). The library has the
  same problem: its three definitions of "children that the parent's proof cites" give three
  numbers. A measure of waste must state its definition.
- **A check that each child is necessary.** After the prover accepts a split, find the child
  assumptions that the proof of the parent uses, and remove the others before work on them. In the
  3-SAT run this removes up to 70 of 227 declared dependencies.
- **Search the library before a split.** In the first case study a plan of 8 claims stayed in the
  graph for more than half of the run, and an existing theorem made the plan unnecessary.
- **Measured difficulty for each claim.** The trace files give failures and probes for 135 proved
  lemmas together with their statements. This is a small set of real difficulty labels. A first
  test is not encouraging: the rank correlation between the length of a statement and the number
  of failures is +0.69 in the hypergraph run (27 lemmas) and -0.01 in the 3-SAT run (108 lemmas).
  The length of a statement alone does not predict difficulty.
- **Bridge lemmas.** 47 of the 135 lemmas are not in the source paper. 28 of the 47 are in groups
  that the authors name as bridges between representations (5 in "Definition bridges", 23 in
  "Representation bridge" and "Distribution interfaces"). This is the reader's inference from the
  group names. A bridge lemma depends on one library, thus it is unlikely to carry to a
  different proof assistant. The library can label each child as mathematical or bridge.
- **A plain coding agent as baseline.** Each experiment in this repository must include one,
  because the full harness is level with Claude Code on proving.

## 9. Open points and things not read

- How the PF agent decides to split, and how frequently a split fails the check.
- The cost of a case study in tokens and money. The time is on the project page.
- What "not referenced" means in Figures 7 and 9, and what the flag `used` means in the traces.
- How many PF agents worked at the same time. The sum of the times of the claims is larger than
  the time of the run (252.6 h against 86.7 h in the hypergraph run), but a claim can wait in the
  graph before work starts on it.
- Appendices A to C were searched for numbers and not read in full. Figures 1 to 5 were not
  viewed. The field `timeline` of the trace files was not analysed.
