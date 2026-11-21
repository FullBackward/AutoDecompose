# Numina Fuse: Interactive Autoformalization in Lean 4

| Field | Value |
|---|---|
| Authors, organisation | Justin Asher, Yichuan Cao, Ruichen Qiu, Pietro Pellegrino, Jia Li. Project Numina (the organisation that builds the system), University of Naples Federico II, Academy of Mathematics and Systems Science of the University of Chinese Academy of Sciences |
| Date and version read | 24 October 2026, version 1 |
| Source | arXiv 2610.33860, https://arxiv.org/abs/2610.33860 ; code https://github.com/project-numina/fuse-desktop ; Kakeya result https://github.com/project-numina/kakeya-3d (neither opened) |
| Licence of the source | CC BY 4.0 (arXiv page) |
| Files in this folder | `paper.pdf`, `note.md` |
| What was read | Full main text (Sections 1 to 9) and Appendix A from the arXiv HTML. The text of Figures 3, 4 and 5 was read from the HTML. No figure viewed as an image. Appendix B (screen pictures) not viewed |
| Read on | 21 November 2026 |

Confidence tags: **[P]** read in the primary source at the place given. **[S]** from a secondary
source. **[U]** not verified.

## 1. What the work is

Fuse is a hosted application in which a person supervises agents that formalise mathematics in
Lean 4. The paper is a system description and an experience report from March to September 2026
[P, Figure 1]. It reports a study of seven prover models, and the use of Fuse in a formalisation
of the Kakeya conjecture in dimension three [P, Section 6]. Its main claim is about design: the
parts that stay useful are the project state, the Lean tools and the verification, and the
orchestration must change with each model [P, Section 9].

## 2. How it works

- **What lasts and what changes.** The work is in the user's repository as a normal Lean and
  leanblueprint project. A blueprint is the informal mathematics, with a link from each entry to
  its Lean declaration. Derived state (parsed blueprint, dependency graph, build errors, agent
  notes) is in a database. Sessions run on the server and continue after the browser closes. The
  prompts, roles and dispatch rules are a separate layer, which "changed with nearly every model
  release" [P, Section 3.1].
- **Three kinds of status.** Recorded status is a marker that a person or agent sets. Checked
  status is what Lean confirms; the backend lowers a recorded status that Lean does not confirm.
  Reviewed faithfulness comes only from reviewer agents and people [P, Section 3.3].
- **Roles.** An orchestrator (Claude Opus) plans and cannot write proofs. Specialists write and
  review the blueprint and the Lean statements. An explorer finds library results to use again. A
  golfer makes proofs shorter. Provers use a low-cost model [P, Section 4].
- **Stages.** Explore, draft, formalize (Lean with `sorry`), prove, golf, style [P, Figure 4].

## 3. How it splits a proof

- **Unit.** One blueprint declaration, with one prover for each declaration [P, Section 4]. For
  delegation the unit is a "region" of the blueprint [P, Figure 5].
- **Who chooses.** A writer agent drafts the blueprint from the source paper, or the user gives
  one. People review the statements [P, Section 2].
- **Check before work.** Two reviewer agents. The blueprint reviewer looks for counterexamples
  and hypotheses that cannot hold. The formalizer reviewer compares each Lean statement with its
  blueprint entry [P, Section 4]. Lean does not check that the children imply the parent.
- **Record.** The blueprint document and its dependency graph.
- **When a child fails.** "relaunch, or revise the statement" [P, Figure 4]. The paper reports
  an agent that could not prove a lemma and put a stronger, false statement in its place
  [P, Section 2].
- **The authors' later view.** A separate blueprint "constrains how agents decompose the
  problem". They expect "a graph of Lean statements, as in Prove2Me" to be better, with a split
  that changes while agents write Lean [P, Section 8].

## 4. What it says about scale

- Size: the Kakeya release has about 1,100 Lean files and 650k lines [P, Section 6.2]. No count
  of lemmas. No report of unused lemmas, but agents proved lemmas again in place of reuse, and
  the explorer agent exists for this reason [P, Section 6.2].
- Parallel work: at most eight provers at one time, each in a scratch copy of its file, typically
  3 to 6 minutes. At most four child orchestrators (one by default), each in its own Git worktree
  [P, Section 4; Figure 5].
- Merge: the patches of the children "are applied one at a time under a lock". Conflicts in
  files that only list imports are resolved automatically. Other conflicts are kept as recovery
  bundles. A rejected push is rebased, and a small agent tries each conflict. A person merges the
  pull request [P, Sections 2, 4 and 5].
- Rebuilds: dependencies come from a shared cache as copy-on-write links. Build errors are
  stored by file hash. Each clone has one Lean language server. Each child checks its worktree
  with separate `lake env lean` runs [P, Section 5].
- Rate: the last 12 days ran outside Fuse, with one person and Claude Code with Claude Fable 5.1
  in parallel worktrees. They added at most 288k new lines, or 25k each day. Fuse sessions wrote
  roughly 10k each day [P, Section 6.2].
- Cost: $0.041 to $0.526 for each solved lemma [P, Table 2]. No total cost for Kakeya.
- Human time: no hours. "even an engineer reading ten thousand lines a day would need two
  months" to read a project of this size [P, Section 8].

## 5. Evidence

| Result | Place |
|---|---|
| Seven prover models solve 45 to 52 of 52 lemmas, one attempt each; total cost $1.91 to $25.80 for each model | Table 2; Table 4 |
| Kakeya in dimension three: proved from one explicit hypothesis, which a separate team's formalisation discharges | Section 6.2 |
| Golfer: one file from about 220M to 85M heartbeats | Section 6.2 |
| Plain Claude Code with parallel worktrees: two to five times more lines each day than Fuse | Section 6.2 |

No ablation. The authors state this: except for the prover study and the golfer, "none of these
design changes was measured" [P, Section 4]. The last row is the only comparison with a plain
coding agent. It is not controlled: the model is newer, about 35% of the lines are copies, and
the measure is lines, not correct statements (reader's judgement).

## 6. Limits

Authors: the 52 lemmas do not separate the models. People found all the statement errors, after
the fact. The checks are "deliberately light". A blueprint that is kept separately becomes out of
date [P, Sections 2, 3.3, 6.1 and 8].

Reader: the prover study uses lemmas from developments that are complete, and the agent shell
could read the original source [P, Section 6.1]. The paper gives no rate of merge conflicts.

## 7. Relation to the two anchors

- **Turing Agent** is later by about three weeks. Its reference list has the earlier
  Numina-Lean-Agent paper and not Fuse [P, `refs_2611.21299.json`]. Same: a dependency graph,
  parallel provers on separate declarations, and a statement reviewer that is separate from the
  provers. Different: Fuse has no Lean check of a split. Fuse also reports that its layers
  "compensated for agents that ... did not reliably finish long tasks", and that it removed them
  when models improved [P, Section 4]. Reader's conclusion: this agrees with the result that the
  Turing Agent harness is level with Claude Code on proving.
- **MathEye** is later, and neither work cites the other. Same: a person examines statements.
  Different: Fuse concludes that people must "set standards, not review every step"
  [P, Section 8]. MathEye asks a person about each open obligation.
- Fuse cites Prove2Me, LeanMarathon, Goedel-Architect and Hilbert [P, References].

## 8. What this repository can use

- Three failures to test for in a split: a child statement made stronger after a failed proof, a
  lemma proved twice, and a statement with hypotheses that cannot hold (a vacuous proof).
- The merge design names the place where conflicts collect: files that only list imports. A
  split method can generate such files and never give them to an agent.
- The cost of a leaf (cents) supports small leaves with low-cost models.
- The authors' move from a blueprint to a graph of Lean statements supports the feature graphs of
  this repository as the main record of a split.
- Each claim about the value of a split needs the model and the date, because the value changed
  inside six months.

## 9. Open points and things not read

- How many merge conflicts and recovery bundles occurred? The paper gives no number.
- The code, the Kakeya repository and the screen pictures were not opened.
