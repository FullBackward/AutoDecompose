# Prove2Me: An Open Collaborative Platform for Scaling Math Formalization

| Field | Value |
|---|---|
| Authors, organisation | Shuze Chen and Tianyi Peng (Columbia Business School); Kunal Marwaha (University of Chicago); Xiaoyang Lu (Purdue University); Henry Yuen (Columbia University) |
| Date and version read | Version 2, 31 Aug 2026. Version 1 is dated 28 Aug 2026 |
| Source | arXiv 2608.28433, https://arxiv.org/abs/2608.28433v2 ; https://prove2.me/about ; https://prove2.me/faq ; https://github.com/prove2me |
| Licence of the source | Paper: arXiv non-exclusive distribution licence 1.0. Public contributions on the platform: Apache 2.0 from 24 Sep 2026 (FAQ) |
| Files in this folder | `paper.pdf` (version 2), `note.md` |
| What was read | Full main text and appendix A of version 2. A text comparison of version 1 with version 2. The About and FAQ pages in full. `start.md`; `SKILL.md` (rules section); `references/lean-setup.md` (full) and `references/prove.md` (searched) of the workspace repository; the README and `MANIFEST.json` of the `formalpedia` repository. Figures not viewed |
| Read on | 2026-11-21 |

Confidence tags: **[P]** the writer of this note read the statement in the primary source, and the
place is given (section, table, figure or page). **[S]** the statement comes from a secondary source,
which is named. **[U]** the statement is not verified. A number without a tag is not permitted.

Survey E, Section 1.1, records the design of the platform. This note adds only what bears on scale.

## 1. What the work is

Prove2Me is a web platform for Lean 4. Persons and their coding agents post theorem statements and proofs on it [P] (Section 1). Each statement is one immutable file, and each proof is a separate file [P] (Section 3). The paper claims that this design removes two causes that stop naive `sorry`-filling at scale [P] (Section 4.1). The evidence is four case-study missions [P] (Table 1). The paper gives no measurement of rebuild time or of interference between agents [P] (Sections 4.1 and 5, read in full).

## 2. How it works

**The scaling problem, as stated.** Naive `sorry`-filling is the method in which agents fill the `sorry` placeholders of one large proof. All agents edit a shared set of files [P] (Section 4.1, paragraph 1). The paper gives two reasons why this method does not scale.

- Reason (i), cost: "whenever a downstream lemma changes, every upstream file that depends on it must be recompiled" [P] (Section 4.1). The only support is a citation of the Mathlib paper of 2020 for the slow build of Mathlib "from scratch".
- Reason (ii), interference: "the work is hard to atomize". Agents that edit the same file or directory make contributions that "interfere with one another" [P] (Section 4.1).
- A Git workflow reduces both, but a human or an orchestrating agent must review and merge each pull request [P] (Section 4.1, paragraph 2).
- Section 2 repeats reason (i): "Lean recompiles the entire downstream cone whenever a module changes, even for a proof-only edit". It calls the merge queue "the empirical bottleneck of large swarms" and cites Gloeckle and Rammal [P] (Section 2, "Reusability and cost").

Reader's remark: Section 4.1 uses "downstream" for a dependency, and Section 2 uses "downstream" for the dependents.

**The mechanism.** A theorem card is one file, `Theorems/Thm_<slug>.lean`, that holds the imports and one statement that ends in `:= by sorry` [P] (Section 3.1; `formalpedia` README, "Layout"). A proof-sketch is a proof file without `sorry` that imports the cards of other theorems, open or proved [P] (Section 4.2). The server compiles a proof against the cards only: the imported children have `sorry` bodies on the server [P] (`references/prove.md`, "Reductions"). "A prover only needs to compile its proof or sketch of the statement it is working on" [P] (About, "Proof-sketch"). A proof file is never imported, so a change of proof cannot start a rebuild (reader's inference from the layout). No agent edits a file of another agent. The verification queue of the server replaces the merge queue, and one account can hold at most 100 pending submissions [P] (`references/prove.md`, "/verify").

A statement never changes. To correct a statement, the submitter marks the card "deprecated" and posts a new card, and the captain links the milestone to the new card [P] (FAQ, "Contribute"). The platform has three environments, each pinned to one Lean and Mathlib version, and "cross-environment reuse is not supported" [P] (FAQ, "Contribute").

## 3. How it splits a proof

- Unit: the theorem card. Two cards are independent because each proof compiles against statements only, and statements are immutable [P] (Section 4.2, Property 1).
- Who chooses: an agent writes the sketch; a human captain chooses the milestone statements [P] (Sections 3.3, 4.4).
- Check of a split: the server compiles the sketch. The verdict is `SKETCH_ACCEPTED` when the file has no `sorry` and imports at least one open theorem [P] (`references/prove.md`, status table). The agent posts the child cards before the sketch, so the check does not come before work on a child can start [P] (`references/prove.md`, "Reductions", step 1).
- Record: a graph. One statement can have several sketches, and "only one needs to succeed" [P] (About). The graph is thus an AND-OR graph (reader's term).
- Failed child: an agent submits a disproof. In the one reported case, the first agent then posted a corrected statement, which closed the branch [P] (Section 4.5).

## 4. What it says about scale

- Table 1: four missions, 17K to 151K lines, 3 to 9 agents, $200 to $600, 7 to 16 days [P] (Table 1; copied in Survey E).
- The FAQ gives 4 agents for Bandit Algorithms; Table 1 gives 6 [P] (FAQ, "Getting started"; Table 1).
- Public export on 2026-11-21, Lean v4.33.1 environment: 360,328 theorems, 116,369 definitions, 320,553 solutions, 3,632,901 dependency edges. The two older environments hold 15,635 and 18,515 theorems [P] (`formalpedia` README, "Environments").
- No figures given: rebuild time, compile time for each submission, queue delay, duplicate statements, deprecated cards, the cost of one full recompile.

## 5. Evidence

| Claim | Evidence | Place |
|---|---|---|
| Naive `sorry`-filling does not scale | Argument and three citations; no measurement | Sections 4.1, 2 |
| The design scales with few agents | Four case studies; 151K lines by 6 agents | Table 1 |
| Model and harness effects | Not separated | Section 5, last paragraph |

No baseline runs on the platform. No ablation isolates the split.

## 6. Limits

Authors: Table 1 is "case studies, not a controlled experiment"; the two cost conventions are not comparable [P] (Section 5).

Reader:

- Section 2 says that Lean rebuilds the cone "even for a proof-only edit". For files with a `module` header this was no longer true after Mathlib moved to the module system on 19 Nov 2025 (note `lean-module-system`). The paper does not name the module system, and the card files in Figures 1 and 4 have no `module` header [P] (Figures 1, 4).
- Interference moves from files to statements. Agents write incompatible statements of one lemma, and milestones are the only remedy [P] (Section 4.4). No count is given.
- The paper and the skill file call the platform "open-source" [P] (Section 1; `SKILL.md`, title). The GitHub organisation holds four public repositories [P] (GitHub API list, 2026-11-21). `prove2me_workspace` holds skill files, the API reference and two Lean scripts, with no licence file. `formalpedia` is a daily export under Apache 2.0. `or-formalization-drive` is a subset under Apache 2.0. `prove2me_feedback` is for feedback and holds no files. None holds the server, the verifier, the search index or the export script. The API is documented and needs an account.
- Version 2 changes no number. It adds two sentences and one reference on Tau Ceti (Section 2). It changes "guarantees immutability" to "enforces immutability" (Section 4.2). It moves one paragraph and the caption of Figure 6 [P] (reader's text comparison of the two arXiv HTML versions).

## 7. Relation to the two anchors

- Turing Agent: the same check. Lean compiles the parent with the child statements as assumptions. Turing Agent makes the check a condition for work on the children; Prove2Me does not. Prove2Me is first (August against November 2026). Prove2Me adds immutable statements and many users. Turing Agent adds an experience pool. Turing Agent does not cite Prove2Me [S] (Semantic Scholar reference list, 30 entries).
- MathEye: an angelic proof keeps its `sorry` holes inside one proof. A proof-sketch moves each hole to a separate card. MathEye selects the cheapest set of open obligations; Prove2Me has no selection rule among sketches. MathEye does not cite Prove2Me [S] (Semantic Scholar reference list, 35 entries).
- The paper cites Gloeckle et al., Rammal et al., M2F and DeepSeek-Prover-V2. It does not cite Draft-Sketch-Prove or Hilbert [P] (reference list read).

## 8. What this repository can use

- The `formalpedia` export gives `graph-*.jsonl`, one line for each parent-child edge [P] (README, "Layout"). It is a large corpus of machine-made decompositions under Apache 2.0, and the 17 moves can be tested on it.
- The design can be rebuilt without the platform (reader's inference; the prover facts are in the note `proof-change-isolation-rocq-isabelle`).
  - Immutable statements: one file for each statement, fixed by a content hash. This part needs no prover feature.
  - Rocq: close an open statement with `Admitted`, which makes it an axiom. A parent that requires the children compiles against their `.vos` files, which leave out opaque proofs.
  - Isabelle: close an open statement with `sorry`, which needs the option `quick_and_dirty` in a batch build. The command `thm_oracles` shows the results that rest on `sorry`. The unit of rebuild is the session, so each card needs a small session or a warm server session.
  - Accept a parent when it builds with open children. Finish with one full build that permits no `Admitted` or `sorry`.
- Not rebuildable from public parts: the search index, the credit system, the moderators.

## 9. Open points and things not read

- How much rebuild time does the card layout save? Nobody has measured it.
- `references/mission_captain.md`, `references/contribute.md` and the Terms page were searched, not read. Figures 5 to 8 were not viewed.
