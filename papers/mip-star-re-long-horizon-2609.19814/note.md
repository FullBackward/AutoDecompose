# Long-horizon autoformalization of a core theorem underlying MIP* = RE

| Field | Value |
|---|---|
| Authors, organisation | Sirui Lu (Max-Planck-Institut für Quantenoptik; MCQST Munich), Ruixuan Deng and Zhengfeng Ji (Tsinghua University), Yanqiao Zhu (University of California, Los Angeles) |
| Date and version read | Version 3, 21 Oct 2026 (version 1: 17 Sep 2026) |
| Source | arXiv 2609.19814, https://arxiv.org/abs/2609.19814 ; code https://github.com/LionSR/MIPStarRE and https://github.com/Dengnifer/MIPStarRE-QPBT |
| Licence of the source | Paper: arXiv non-exclusive distribution licence 1.0. Lean code: Apache 2.0 (Code availability) |
| Files in this folder | `paper.pdf`, `note.md` |
| What was read | Main text in full (Sections 1 to 4, availability statements). Appendices B.4, C.1, D.7, E.1 to E.3 and E.5 to E.10 in full. Other appendices: headings only. Figures not viewed. Of arXiv 2607.07857: abstract, Method section, Appendix D, first part of Appendix F |
| Read on | 2026-11-21 |

Confidence tags: **[P]** the writer of this note read the statement in the primary source, and the
place is given (section, table, figure or page). **[S]** the statement comes from a secondary source,
which is named. **[U]** the statement is not verified. A number without a tag is not permitted.

No earlier survey in `docs/research/` names this work.

## 1. What the work is

FormalFlow is a system that coordinates coding agents on one GitHub repository under human supervision [P] (Section 2.1). The authors use it to prove in Lean 4 the quantum soundness of the low individual-degree test, a part of the proof of MIP* = RE [P] (Section 1). The library has 126,367 lines in 337 files, and agents wrote all of them [P] (Table S7; Methods, "Use of language models"). The paper claims that the hard part is no longer one lemma. The hard part is to keep statements faithful and to make proved lemmas fit together [P] (Section 3). The evidence is the public history of one project.

## 2. How it works

A blueprint is a dependency graph with a mathematical text that maps each claim of the paper to a Lean declaration [P] (Section 1). A proof obligation is "a claim that must be proved to complete an argument" [P] (Section 1). Each open obligation is a GitHub issue, and GitHub sub-issue links hold the hierarchy [P] (Methods, "Task generation"; E.2). An agent takes an issue whose prerequisites are closed, works in a separate Git worktree, and opens a pull request [P] (Methods, "The formalization session").

Continuous integration runs a full `lake build` and an axiom audit on each pull request that changes Lean code [P] (Methods, "Review and integration"). Review agents compare the change with the paper and the blueprint. After a merge, a scan opens issues for new obligations. This scan made 110 issues, and follow-up tasks are 292 of the 725 issues (40.3 %) [P] (E.3). When two branches conflict, an integration agent rebases the pull request and runs a full compilation before the merge [P] (Methods).

Two terms name the problems. Statement drift is a change of a formal statement that leaves the intended claim unproved, for example an added assumption. Composition is the requirement that each lemma supplies the objects and bounds that the next lemma assumes [P] (Section 2.1).

## 3. How it splits a proof

- Unit: one issue for one obligation, closed by one pull request. At the end, 181 blueprint statements link to 598 Lean declarations [P] (B.4).
- Who chooses: agents write a first skeleton with one file for each section of the paper. An orchestrator agent later splits blueprint statements into intermediate lemmas [P] (Section 2.1; Methods, "Blueprint").
- Check before work on the children: none at first. A task was finished "when its target theorem compiled" [P] (Section 2.1).
- Record: the blueprint graph and the sub-issue graph.
- Failed child: the agent files a gap note, and a human decides whether to correct the paper or the Lean code. The project has 25 gap notes [P] (Section 2.2).

The main finding is negative. "Local completion did not ensure that these components would fit together" [P] (Section 2.1). An agent can make a file compile when it moves an obligation into a hypothesis. On 29 April the repository had one `sorry`, but 114 of 283 target declarations were not complete [P] (Section 2.1; B.4). The early main theorem had the form H ⟹ (Q ⟹ Q): it assumed its conclusion [P] (C.1.1). Appendix C.1 lists five classes of composition failure: carrier mismatch, inlined conclusion, missing invariant, default value on invalid input, and insufficient error bound [P].

The remedy came during the run. A scanner flags a hypothesis that repeats the conclusion. A second scanner, the proof-debt scanner, flags names of unproved intermediate assumptions [P] (Section 2.1, "Review and automated checks"). A script checks that no blueprint node marked complete depends on an unfinished proof [P] (Methods, "Automated checks").

## 4. What it says about scale

| Quantity | Value | Place |
|---|---|---|
| Lean code | 126,367 lines, 337 files, Lean v4.31.0 | Table S7 |
| Time | 7 March to 24 June 2026; 110 calendar days, 83 active days; abstract: "63 days" | Table S7; abstract |
| Commits, pull requests | 2,778 commits; 1,790 pull requests merged | Table S7 |
| Tokens | 30.121 billion (30.035 billion input, 85.676 million output); about 238,000 for each line | E.10 |
| Cache | 90.7 % of input tokens are cache hits | E.10 |
| Money | $10,181.77 metered in one harness; other routes not priced | E.10 |
| Review | 21,651 comments on 1,904 closed pull requests and issues; 55.19 % on mathematics | Table 1 |
| Blocking checks | 4,113 runs; 49 failed; 42 of these were transient; 7 came from the checks | D.7.3 |
| Proof-debt findings | 63 on 6 May; zero from 11 May | D.7.1 |
| Second theorem (QPBT) | 298.5 hours, 261 pull requests, 13.7 billion tokens, 118,732 lines | Section 2.1; E.10 |

All rows are [P]. The parts read do not define the 63-day interval. No figures given: number of agents at one time, build time, time in continuous integration, number of conflicts or rebases, human hours.

## 5. Evidence

| Result | Value | Place |
|---|---|---|
| Final proof | no `sorry`; three standard axioms; comparator repository | Methods, "Checking the completed proof" |
| `sorry` count against blueprint status | 1 against 114 open | B.4 |
| Blueprint size while one `sorry` stayed | 283 targets (29 April) to 672 (8 May) | B.4 |
| Detection delay of three shortcuts | 29 days; under 1 day; 0 and 31 days | Table S4 |

No baseline. No ablation. The procedures changed during the project [P] (Section 4, first paragraph).

## 6. Limits

Authors: token records are incomplete; the GitHub Actions runs from 1 April to 4 June kept no counters [P] (E.10). Git metadata gives 83.3 % of commits to human accounts, but agents made all commits [P] (E.9).

Reader: the work addresses reason (ii), but the interference is semantic, not textual. Worktrees and an integration agent handle file conflicts, with no count. The work does not address reason (i): each pull request needs a full build, and no build time is given.

## 7. Relation to the two anchors

- Turing Agent: its rule (Lean checks that the children imply the parent) is the check that FormalFlow did not have at first. FormalFlow shows a failure that this rule does not catch: a child that assumes its own conclusion. FormalFlow is earlier (September 2026). Turing Agent does not cite it [S] (Semantic Scholar reference list).
- MathEye: MathEye records a confirmed claim as an assumption. FormalFlow measures what untracked assumptions cost: 63 flagged declarations before the scanner entered continuous integration. MathEye does not cite it [S] (Semantic Scholar reference list).
- The paper cites LeanMarathon and Theo as concurrent work, and it cites Rammal et al. [P] (Section 1; reference 13). It does not cite Prove2Me, Gloeckle et al. or M2F [P] (reference list searched).

## 8. What this repository can use

- A count of `sorry` is not a measure of progress. A test of a split must also count the obligations that sit in hypotheses.
- The five classes of composition failure are a checklist for the "interface lemma" move.
- The conclusion-shaped-hypothesis test is cheap and can run on each library entry.
- 40.3 % of the issues are follow-up tasks. A split is thus not final when work starts, and a method must permit new children.

**Earlier work: tensor networks (arXiv 2607.07857; Lu, Tjoa, Cirac; 8 Jul 2026).** Six agent roles formalize the fundamental theorem of matrix-product states. They run on the same harness, TeXRA, with a blueprint and a persistent memory [P] (Method section). The library has 705 source files, and the recorded model cost is $20,206 [P] (Method section; Appendix F). The orchestrator starts "three to five sub-agents concurrently", gives each a disjoint set of files, and checks the merged result with a full build [P] (Appendix D.1). One split of a proof into smaller lemmas cut the Lean work for that proof from 1,600,000 to 250,000 heartbeats [P] (Appendix D.2). The MIP* paper replaces the disjoint-files convention with worktrees, pull requests and continuous integration.

## 9. Open points and things not read

- How many agents ran at one time on the first theorem, and how long did one full build take?
- Appendices A, B.1 to B.3, B.5, C.2 to C.9, D.1 to D.6, E.4, F, G and H were not read.
