# Survey M: results

Anchors: Turing Agent (arXiv 2611.21299, 16 November 2026) and MathEye (arXiv 2611.22103,
17 November 2026). Written on 21 November 2026.

This file gives the results of the survey. Each work has its own folder with the source and an
analysis note. `README.md` in this folder is the index. A name in square brackets, for example
[theo], refers to the note in the folder that starts with that name. The note gives the exact place
of each figure in its source.

Important statements in this file use Simplified Technical English. A statement marked "reader's"
is the inference of the writer of this file, not a claim of a source.

## 1. Scope, method and limits

- **Scope.** 28 works: the 2 anchors, 6 agent harnesses, 6 works on dependency graphs and on
  repair with `sorry`, 6 items on scale, 7 items from companies or on company releases, and 1
  earlier paper from program verification.
- **Method.** The writer of this file read the two anchors and the earlier paper. Four agents read
  the other 25 works and wrote their notes. The writer then compared approximately 110 figures and
  quotations from those 25 notes with the saved sources. All of them agree with the sources.
- **Limit 1.** A check of 110 items is a sample. The notes contain more figures than that.
- **Limit 2.** Most works are preprints of 2026 without peer review. Several are company posts
  without measurements.
- **Limit 3.** All 28 works are about Lean, with two exceptions: the documentation of Rocq and
  Isabelle, and the 2012 paper, which is about C programs.

## 2. The main results

1. **The two central ideas of the anchors are older than the anchors.** Section 3 gives the
   earlier works.
2. **No work isolates the effect of the split.** No experiment changes only the choice of lemmas
   and then measures the proof rate. Section 5 lists what the works measure in its place.
3. **In three independent comparisons, a plain agent loop is level with a harness or better.**
   See [turing-agent], [deepmind-aletheia-alphaproof] and [numina-fuse]. The third comparison is
   not controlled.
4. **The check "the children imply the parent" is necessary, and it is not sufficient.** Five
   independent works show a split that passes this check and still has a fault. Section 6.4
   gives the faults and a mechanical test for each.
5. **Each proof assistant now has a mechanism against the first reason of the scaling problem.
   No source measures the effect.** See Section 6.2.
6. **One design removes the second reason by construction.** Frozen statements with one separate
   edit region for each agent gave zero merge conflicts in 135 pull requests [leanmarathon].
7. **Agents and humans work on different parts of a proof.** Agents fill holes. Humans change
   the structure near the holes [agents-diverge-from-human-preferences].
8. **Large public data on machine-made splits exists.** The Prove2Me corpus is public under
   Apache 2.0, with 3,632,901 dependency arrows [prove2me]. The Turing Agent project page gives
   the failures for each of 135 lemmas [turing-agent].
9. **The three open claims of this repository stay open.** No work selects a split from a
   representation that Lean, Rocq and Isabelle share. No work labels splits with moves. No work
   carries a split from one assistant to a different one.

## 3. The two anchors: what is new, and what is not

| Idea in the anchor | Earlier work with the same idea | What the anchor adds |
|---|---|---|
| Turing Agent: prove the parent from the child statements before work on the children | Theo, 30 June 2026: "we always prove the node before its children" [theo]. Prove2Me, August 2026: the verdict `SKETCH_ACCEPTED` [prove2me]. Axiom Math adopted the same rule after a stall on 13 October 2026 [axiom-math] | Parallel proof agents, and review of a claim only when its meaning is not certain |
| Turing Agent: a store of lessons that stays when the context is compressed | Archon, April 2026: summaries of sessions, status documents for each file, a list of failed approaches [archon-rethlas] | Records that are attached to one claim |
| MathEye: replace each failed part with `sorry` and keep the structure | APOLLO, May 2025 [apollo]. MechMath, March 2026, which cites APOLLO for the word "sorrifying" [mechmath] | A rule that goes up one level in the syntax tree when the error stays |
| MathEye: a dependency graph of one proof | ProofFlow, October 2025 [proofflow] | Edges that need several premises together, and edges that rules add |
| MathEye: select the cheapest sufficient set of questions for a person | Dillig, Dillig and Aiken, 2012 [abductive-error-diagnosis] | The application to Lean proofs |

Three points about this table.

- MathEye cites none of APOLLO, MechMath and ProofFlow. Turing Agent cites Theo, and does not
  cite Prove2Me.
- The 2012 paper adds the costs of the parts of a question. MathEye uses a mean, and this gives
  two defects [matheye, Section 6]. The 2012 paper also asks a second question that can show that
  the goal is false. It also reports the error of the persons: with the questions, 7.3 % of their
  decisions are still wrong. MathEye has neither.
- The paper on Turing Agent gives no cost. Its project page gives the cost: 86.7 hours, 9,827
  tool calls and 595 compressions of the context for a problem with 27 lemmas [turing-agent,
  Section 4].

## 4. How the works split a proof

"Check" in this table means: a check of the split by the prover before work starts on the
children.

| System | Unit of a split | Who chooses the split | Check | When a child fails |
|---|---|---|---|---|
| Turing Agent | Lemma statement | Agent, from the informal proof | Yes: children imply parent | Revise, or split again |
| Theo | Lemma with `sorry` | Agents; a score decides leaf or split | Yes: parent proved first | One of three diagnoses, each with a repair |
| Prove2Me | Theorem card | Agent; a person fixes the milestones | Partly: the server checks the sketch, but the children are posted first | Disproof, then a new card |
| Axiom Math | Milestone, then smaller theorem | Persons and agents | Yes, after 13 October | Review of added assumptions |
| AlphaProof Nexus | Helper lemma with `sorry` in one file | Agent | Yes: the sketch must compile | A disproof of the child can come back |
| LeanMarathon | Node of one blueprint file | Agent, with a written rubric | No; work goes from the leaves up | Local helper nodes |
| Archon | File and `sorry` signature | Two agents; one has a new context | Not stated | New plan |
| Numina Fuse | Blueprint declaration | Agent or person | No; two reviewer agents | Start again, or revise the statement |
| Lea | Lemma | A person | No | "Disproved" is a normal result |
| AIProver | One informal lemma, only as a fallback | The host agent | No | Split again after two failures |
| MIP* = RE formalisation | Issue | Agents | No at the start; scanners later | Gap note; a person decides |
| M2F | Block, then proof hole | Preprocessor | Stage 1 must compile with open proofs | Revert and plan again |
| MechMath, APOLLO | The failed block | The location of the error | No | Recursion on the hole |
| ProofFlow | Step of the informal proof | A model | No | Attempt on the negation |
| MathEye | Lemma or `have` step | The model that writes the sketch | No; a check after the failure | Question to a person |

Two results from this table.

- **Four of fifteen systems make the prover check a split before work on the children.** They
  are Turing Agent, Theo, Axiom Math and AlphaProof Nexus. All four are works of 2026, and Axiom
  Math adopted the check after a failure. Prove2Me makes the same check, but not before the work
  on the children.
- **Two systems use explicit signals to decide between leaf and split.** Theo uses depth, the
  length of the statement, the nesting of quantifiers, and words in the paper [theo].
  LeanMarathon uses a rubric file with ten conditions for a split and five against, and a
  quantity that it calls "repair radius": the number of declarations that must change if one
  declaration is wrong [leanmarathon]. No other work gives a rule.

## 5. What the works measure about a split

| Work | Comparison | Result | What it isolates |
|---|---|---|---|
| ProofFlow | Each step gets only its declared prerequisites, against all earlier steps | Tactic accuracy 0.742 against 0.681 with the stronger models; 0.358 against 0.391 with the weaker models | The premise set of a step. This is the only controlled test in the survey |
| MathEye | Ask about each leaf, against ask about the selected set | 416 questions against 187 | The selection of questions |
| AlphaProof Nexus | Basic loop (agent A) against the full agent (agent D) | Both prove the same 9 of 353 problems; D costs 2 to 5 times less on two problems | The harness, by cost |
| AIProver | First harness against the harness after automatic search, same model | 15.7 % against 22.6 % | The harness, not the split |
| Turing Agent | Full harness against Claude Code, same model | +2.42 points with one model, -4.03 with the other | The harness, not the split |
| Archon | With a human blueprint, against without | 2 h 12 min against 3 h 43 min, one run each | Nothing with confidence |
| LeanMarathon | Earlier version against current version | About 12 days with 26 `sorry` left, against about 3 days with none | Two changes at the same time |
| Numina Fuse | Fuse against plain Claude Code in parallel worktrees | About 10,000 lines each day against 25,000 | Not controlled: the model is newer |
| APOLLO | None | The authors say that the `sorry` step "cannot be ablated" | Nothing |

**Result.** The value of a good split is a belief in this literature. It is not a measurement.
The 41-author survey asks for "budget-matched ablations" [from-solvers-to-research]. No work in
this survey has one for the split.

## 6. The scaling problem

### 6.1 The problem

Prove2Me states it in two paragraphs [prove2me, Section 4.1]. Naive `sorry`-filling does not scale,
for two reasons.

- **Reason (i), rebuild.** A change to one lemma forces a new build of each file that depends on
  it.
- **Reason (ii), interference.** Agents that edit the same files disturb each other. Then one
  merge queue admits one change at a time.

Section 4.1 of Prove2Me contains no measurement. It gives three citations.

### 6.2 Reason (i): mechanisms and measurements

| Mechanism | What stops the rebuild | Measurement |
|---|---|---|
| Lean module system [lean-module-system] | An edit in a proof, a comment, a private declaration. A new public theorem or a changed statement still rebuilds the dependents | Two logs: one file in 1.2 s of 7,687 jobs, and one file in 13 s of 7,668 jobs. No study |
| Rocq `.vos` and `.vok` files [proof-change-isolation-rocq-isabelle] | The interface file omits each proof that ends with `Qed` | None. The manual calls the mode experimental |
| Isabelle [proof-change-isolation-rocq-isabelle] | Proofs are checked in parallel. The manuals name only the session as the unit of a rebuild | Speed-up of at most 3.5 on 4 cores and 6.5 on 8 cores |
| Prove2Me cards [prove2me] | The server compiles a proof against statement files only. No file imports a proof | None |
| Lea [lea] | A fingerprint of the statement decides which results are still valid | None |
| Axiom Math [axiom-math] | A distributed build cache, and finite computations as separate certificates | None. "agents produced proofs faster than Lean could recheck them" |

Three more facts.

- **The statement of Prove2Me about Lean is out of date.** It says that Lean rebuilds the
  dependents "even for a proof-only edit". This is no longer true for files with a `module`
  header.
- **A file is a coarse unit.** In Mathlib a file uses a median of 1.6 % of what it imports, and
  92.2 % of the dependencies between files go through indirect imports
  [network-structure-of-mathlib]. Thus a rebuild by file is much larger than the true dependency.
- **A shorter proof is not a faster build.** The removal of 12,515 lines by proof shortening
  increased one build from 21.83 to 23.01 minutes. Narrower imports decreased the memory of the
  largest process from 12.605 to 2.891 GiB [lean-pool].

### 6.3 Reason (ii): mechanisms and measurements

| System | Unit of independent work | Why two units do not collide | Measurement |
|---|---|---|---|
| Gloeckle et al. [automatic-textbook-formalization] | Pull request | Nothing; one merge queue tests each request | 30,046 agent runs. Aborted runs use 42,904 of 80,686 million input tokens (53.2 %, reader's division). 4,668 runs blocked. No queue time and no conflict rate |
| LeanMarathon [leanmarathon] | One edit region before a frozen statement | The regions are separate, so the patches can land in any order | 135 pull requests, a maximum of 16 in one round, zero conflicts |
| Archon repository [archon-rethlas] | One file | A job is accepted only if it changed only its file | None |
| Numina Fuse [numina-fuse] | Scratch copy or worktree | One lock; patches land one at a time | None |
| Prove2Me [prove2me] | Card | Statements cannot change, and proofs depend on statements only | None |
| MIP* = RE [mip-star-re-long-horizon] | Issue | An integration agent handles conflicts | 1,790 merged pull requests. No conflict count |

**Result.** Only one source measures the waste (Gloeckle et al.), and only one source measures
the absence of conflicts (LeanMarathon). The design of LeanMarathon and the design of Prove2Me
agree on one principle: freeze the statements, and let each agent write only new text.

### 6.4 A third reason that the works show: a split can pass the check and be wrong

This reason is not in the two paragraphs of Prove2Me. Five independent works report it. The name
"statement drift" is the reader's.

| Fault | Where reported | A mechanical test |
|---|---|---|
| A child has its own conclusion as a hypothesis | MIP* = RE: one `sorry` left while 114 of 283 targets were not complete; the first main theorem had the form H implies (Q implies Q) | Compare each hypothesis with the conclusion |
| An assumption that has no proof hides behind a name | MIP* = RE: a scanner for such names flagged 63 declarations on 6 May, and none from 11 May | Scan the declarations for names of open assumptions |
| A child says the same as the parent in different words | AlphaProof Nexus: the agent "frequently offloaded a problem's core difficulty into a single sorry"; prompts did not stop it | Try to prove the child from the parent |
| A parent is proved with an added assumption | Axiom Math: tens of thousands of lines deleted | Compare the proved statement with the planned statement, byte for byte [theo] |
| A lemma is replaced by a stronger false statement, or its hypotheses cannot hold | Numina Fuse | Search for a counterexample; prove that the hypotheses can hold |
| A child is declared and not necessary | Turing Agent: 227 declared dependencies, 157 named in the proofs | Find the assumptions that the proof of the parent uses |

**Result.** When agents do not collide on files, they collide on statements. Prove2Me reports the
same effect as statements that agents write twice in forms that do not fit together.

### 6.5 Size and cost of the developments

| Work | Size | Cost and time, as the source gives them |
|---|---|---|
| Turing Agent, 2 problems | 818 and 1,920 lines of proof | 86.7 h and 47.1 h; no money |
| LeanMarathon, 3 runs | 8,513, 3,988 and 14,592 lines | $257.17, $189.43 and $623.54 |
| Theo, unit-distance paper | 14,831 lines | $2,480.64 at list prices; 219.5 h |
| Archon | 19,448 lines in 42 files | About 80 agent hours |
| MIP* = RE | 126,367 lines in 337 files | 30.121 billion tokens; 110 calendar days |
| Gloeckle et al. | About 130,000 lines | About $100,000 (the authors' estimate); one week |
| M2F | 153,853 lines | "approximately three weeks" |
| Lean Pool | 3,228,485 lines in 211 projects | A clean build needs 60.28 minutes |
| Axiom Math | About 43.1 million and 16 million lines | 24 days for the first |
| OpenAI release | 29,694,161 lines in 162,417 files | Not stated |

The cost for each line differs by a factor of more than 15 between these sources (reader's
division: $0.03 to $0.05 for LeanMarathon, $0.17 for Theo, $0.77 for Gloeckle et al.). The
sources use different models and different price rules, so the figures do not permit a ranking.

## 7. What the companies add

- **Axiom Math** [axiom-math]. Size: approximately 43.1 million lines in 24 days, from a map of
  108 milestones and about 380 tasks. The team found the split check by necessity. It names the
  build as the limit, and it gives no numbers.
- **Google DeepMind** [deepmind-aletheia-alphaproof]. A cache of goals: each subgoal is stored
  under a hash of its exact context and target, so that parallel attempts do not repeat it. The
  prover can return a disproof of a child. The paper is open about one failure: a helper lemma
  that repeats the target.
- **OpenAI** [openai-math-release-2026-10]. The largest public body of Lean code from agents. The
  catalogue has two words on the method: `method: agent` and `review: status: unchecked`. The
  coverage figures in the press count different units: 176 of 721 papers have a Lean source entry
  (24 %), and OpenAI's own figure is "300 / 719 = ~42%" of top-line results, without a definition.
- **Math Inc** [mathinc-gauss]. A split by layers of abstraction with a refinement theorem between
  two layers, and a split at service boundaries. This is a split for verification of software.
  No source of 2026 says how Gauss splits a mathematical proof.
- **Numina** [numina-fuse]. The team removed parts of its own harness when the models improved.
  It now expects that a graph of Lean statements is better than a separate blueprint.
- **Harmonic.** No source of 2026 on splits or scale was found, so there is no folder.

## 8. Data that this repository can use

| Data | Size | Licence | What it permits |
|---|---|---|---|
| Formalpedia export of Prove2Me [prove2me] | 360,328 theorem statements, 320,553 proofs, 3,632,901 arrows; several proofs for one statement | Apache 2.0 | Shapes of machine-made splits; alternative splits of one statement; size of the rebuild cone |
| Turing Agent traces [turing-agent, `traces/`] | 135 proved lemmas with statement, proof, dependencies, failures and times | None stated | Real difficulty for each lemma; a test of the "necessary child" check |
| OpenAI `openai/math` [openai-math-release-2026-10] | 162,417 Lean files | Apache 2.0 | Developments made by agents |
| Lean Pool [lean-pool] | 211 projects: 70 human, 102 AI, 39 mixed | For each project | Human and AI projects in one build |
| Mathlib network data [network-structure-of-mathlib] | 308,129 declarations, 8.4 million arrows from the prover | See the note | The structure of a human library |
| LeanMarathon rubric file [leanmarathon] | Ten conditions for a split, five against | See the note | A comparison, rule by rule, with the 17 moves of the library |

All of this data is Lean. Thus it does not close the gap on Rocq and Isabelle.

One caution about our own graphs. They come from the text of the code. One study compared a
graph from text with the Lean compiler: 86.2 % of the arrows from text are real, and the text
finds only 61.4 % of the true arrows. 24 % of the true dependencies are never written by name
[agents-diverge-from-human-preferences].

## 9. Consequences for the method that this repository proposes

These are the reader's proposals. Each has its evidence. No test of the full method exists.

1. **Search the library before a split.** In one Turing Agent run, a plan of 8 claims stayed for
   more than half of the run, and one existing theorem made it unnecessary.
2. **Use the known mechanics for `sorry`.** APOLLO and MechMath are sufficient. This step is not
   a contribution.
3. **Check a split in four parts.** (a) The children are sufficient. (b) Each child is necessary.
   (c) No child has one of the faults of Section 6.4. (d) A search for a counterexample fails.
   Part (a) is common practice. Parts (b), (c) and (d) exist only as separate pieces in
   different works.
4. **Add the costs; do not use a mean.** With added costs and one derivation for each node, the
   best set of open goals is a minimum cut [matheye, Section 8].
5. **Select where to work, because the work is not even.** In the Turing Agent run with 109
   claims, 11 claims have 71 % of the failures.
6. **Do not estimate difficulty from the length of a statement.** The rank correlation with
   failures is +0.69 in one run (27 lemmas) and -0.01 in the other (108 lemmas).
7. **Give each child only its declared prerequisites.** This is the one measured effect
   (ProofFlow), and it holds for the stronger models only.
8. **Select the form of a child by its build cost.** A private helper in the file of the parent
   costs no rebuild in Lean. A public lemma costs the files that import it.
9. **Freeze statements, and give each agent one separate region or one card.**
10. **Compare with a plain agent loop at the same cost.** Three works show that the plain loop is
    level.
11. **Record each split with its move, and mark each child as mathematical or bridge.**

## 10. Corrections

**To earlier documents of this repository.**

- Surveys C and F quote costs for MechMath ($19.90, 88 calls, 114 minutes) as Hard mode. The
  source table shows that they are Easy-mode costs [mechmath].
- Survey E says that one work holds the model and changes the harness. AIProver is a second
  [aiprover].
- Survey E says that OpenAI does not document how its Lean code was made. The catalogue has two
  fields on this [openai-math-release-2026-10].
- Survey F describes the Numina blueprint. Numina now argues against a separate blueprint
  [numina-fuse].
- Survey K gives RLMEval results for small provers only. Turing Agent reports 82.66 % on a
  subset with agent harnesses.
- `docs/research-pipeline-2026-11-10.md`, Section 6, says that Isabelle supports the card layout
  directly. Two limits apply: `sorry` needs `quick_and_dirty` in a batch build, and the manuals
  name only the session as the unit of a rebuild [proof-change-isolation-rocq-isabelle].

**To statements made earlier in this survey.**

- The first Turing Agent problem has no auxiliary lemma, not 7.
- The proportion of unused lemmas depends on the definition: 14 of 135 in the figures, 3 of 135
  by the flag in the trace files.

**Contradictions inside the sources.** Each note lists them. Examples: the MIP* paper says "63
days" in the abstract and 110 calendar days in a table; M2F says in the abstract that it orders
items by dependencies, and in the body that it uses the order of the index.

## 11. Recommended next steps, in order of cost

1. **No model and no prover.** Measure the Formalpedia arrows: fan-out, depth, number of
   alternative splits. Compare them with the graphs of the library. This is the first
   comparison of human splits with machine splits. **Done on 21 November 2026:** see
   `formalpedia-and-library-splits-2026-11-21.md`. Its main result changes this plan: the arrows
   show approximately 15 % of the lemmas of a proof, because most lemmas are local to a proof
   file. The next comparison must read the proof files with the feature tools of the library.
2. **No model and no prover.** Add to the feature tools the three definitions of an unused child,
   and a scanner for a hypothesis that repeats the conclusion.
3. **A prover and no model.** On the 27 Isabelle entries: the four-part check of Section 9, and
   the size of the rebuild after a change in one proof.
4. **A small model cost, which needs the owner's approval.** The transfer of a split between two
   assistants, with a plain agent as baseline.

## 12. Not covered

- The repositories of code of most works were not opened.
- Tau Ceti, a library that OpenAI and Axiom Math both depend on, appears in no survey of this
  repository and was not read.
- The works on angelic execution that MathEye cites were not read, except the 2012 paper.
- The 41-author survey names approximately 40 systems and benchmarks that the surveys of this
  repository do not name [from-solvers-to-research, Section 9 of the note].
