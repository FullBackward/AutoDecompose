# Automatic Textbook Formalization

| Field | Value |
|---|---|
| Authors, organisation | Fabian Gloeckle, Ahmad Rammal, Charles Arnal, Remi Munos, Vivien Cabannes, Gabriel Synnaeve, Amaury Hayat; FAIR at Meta, CERMICS (ENPC), Korea Institute for Advanced Study |
| Date and version read | Version 1, 3 Apr 2026 (the only version) |
| Source | arXiv 2604.03071, https://arxiv.org/abs/2604.03071 ; code https://github.com/facebookresearch/repoprover ; result https://github.com/facebookresearch/algebraic-combinatorics |
| Licence of the source | CC BY 4.0 |
| Files in this folder | `paper.pdf`, `note.md`, `figures/fig5-agent-outcomes-over-time.png` |
| What was read | Full main text and appendix A. Figure 5 viewed. Figures 1, 2, 4 and 6: captions only. README of `repoprover` searched. Reference list checked for the anchors' precursors |
| Read on | 2026-11-21 |

Confidence tags: **[P]** the writer of this note read the statement in the primary source, and the
place is given (section, table, figure or page). **[S]** the statement comes from a secondary source,
which is named. **[U]** the statement is not verified. A number without a tag is not permitted.

Survey E, Section 1.3, records the roles, the outcome table and the failure modes. This note adds the measurements on scale and the changes that the authors made during the run.

## 1. What the work is

The work is a case study of one run. A group of Claude 4.5 Opus agents formalizes a 500-page textbook on algebraic combinatorics in Lean [P] (abstract). The agents share one Git repository and merge through one queue [P] (Section 1, items B to D). The run proves all 340 targets in one week [P] (Section 3.3). The paper names the single merge queue as "a choke point for the system" [P] (Section 2.7). It reports token counts for each agent outcome, but no queue time and no conflict rate [P] (Tables 2 and 3).

## 2. How it works

A sketcher agent writes the definitions and statements of one chapter and closes each proof with `sorry` [P] (Section 2.4). A prover agent fills one proof. A maintainer agent takes one issue file. Each agent works in a Git worktree, which is a separate checkout of the repository on its own branch [P] (Section 2.4). All worktrees share one Mathlib installation, so a worktree holds only the files and build artifacts of the project [P] (Section 2.4).

A merge queue is a list of approved pull requests that the system builds and merges one at a time. The queue here is single-threaded and has no batching [P] (Sections 2.7, 4.2). A pull request merges when it has no conflict with the main branch, the repository builds, and two reviewer agents approve [P] (Section 2.4). When the main branch moves first, the pull request is "requeued after rebasing and fixing" [P] (Section 2.7). The paper does not use the term "rebase cycle". The nearest limit is 10 review cycles for each pull request [P] (Section 3.4).

## 3. How it splits a proof

- Unit: one pull request from one agent. A prover agent edits one Lean file by design; a maintainer agent edits up to 14 files [P] (Figure 6b, Section 3.6).
- Who chooses: a sketcher agent chooses the statements; a prompted model chooses the 340 targets [P] (Sections 2.4, 2.5).
- Check before work on the children: none by Lean. A mathematical reviewer agent compares the statements with the source [P] (Section 2.4).
- Record: the repository and a folder of issue files. No dependency graph exists [P] (Section 3.5, item 3).
- Failed child: the agent reports "blocked", and the system starts the task again later [P] (Section 3.5, item 3).
- Independence of two units: the system does not know it in advance. The merge tests it [P] (Section 2.7).

An earlier design, with one agent that writes all statements and starts one prover for each theorem, did not scale past "simple preprints or book chapters" [P] (Section 2.3).

## 4. What it says about scale

| Quantity | Value | Place |
|---|---|---|
| Agent runs | 30,046 (Table 2); 29,691 with an outcome (Table 3) | Tables 2, 3 |
| Machines | eight, with one shared network file system | Section 2.7 |
| Duration | one week; the time axis ends near 170 h | Section 3.3, Figure 5 |
| Lean code | about 130,000 lines, about 5,900 declarations, 52 files | Table 1 |
| Tokens | 83,176 M input, 561.2 M output, 1,645,274 turns | Table 2 |
| Cost | $430K without caching; about $100K estimated with caching; $14K for output | Section 3.5 |
| Merged agents | 3,490, with 16,477 M input tokens | Table 3 |
| Aborted agents | 6,120, with 42,904 M input tokens | Table 3 |
| Blocked agents (no pull request) | 4,668, with 8,012 M input tokens | Table 3 |
| Agents at the limit of 10 review cycles | 976, with 6,935 M input tokens | Table 3 |
| Size of a pull request | "around 100 lines"; the largest "a few hundred" | Figure 4, Section 3.3 |

All tags in the table are [P]. The reader computed three shares from Table 3. Aborted agents use 53.2 % of the input tokens and are 20.6 % of the runs. Merged agents are 11.8 % of the runs. Maintainer agents use 44,770 M input tokens, and prover agents use 25,012 M [P] (Table 2).

Figure 5 shows the change over time (reader's reading of the plot, approximate). Between about 45 h and 90 h, aborted agents take the largest share of tokens. After about 90 h, the aborted share falls and the blocked share grows to about a third. The merged share is above 60 % only in the last hours.

**File-system contention.** The network file system made worktree copies and `lake build` processes "time out and fail", mostly after a restart [P] (Section 2.7).

**What the authors changed during the run.**

- They added "delays and jitter" to restarts [P] (Section 2.7).
- They corrected interruption and resumption, duplicate work, tool definitions, timeouts and thrashing [P] (Section 3.5, item 1).
- They added the issue tracker and maintainer agents after a first design with provers only [P] (Section 3.6).
- They stopped the run "a few times" and started status agents by hand. These agents removed stale issues and analysed the dependencies between issues [P] (Sections 3.5, 4.3).
- A change of prompts started a clean-up phase [P] (Figure 1, caption).

They did not change the merge queue. They name batching with bisection, as in the Mathlib bors bot, as the known remedy [P] (Section 2.7).

No figures given: queue length, waiting time, number of requeues, conflict rate, build time, rebuild time after a merge, number of agents that ran at one time.

## 5. Evidence

| Result | Value | Place |
|---|---|---|
| Targets proved | 340 of 340 | Table 1 |
| Share of input tokens on aborted agents | "around half" | Section 3.5, item 1 |
| Projected saving | "3-10x", not measured | Section 3.5 |

No baseline. No ablation. The authors changed the system during the run, so the run is not one fixed method.

## 6. Limits

Authors: the logs hold no cache statistics, so the $100K figure is an estimate [P] (Appendix A). The statements had only a manual spot-check [P] (Section 3.3).

Reader:

- The paper addresses reason (ii), interference, with branches, small pull requests and one queue. It then reports that the queue is the bottleneck. The evidence is the authors' observation, not a measurement.
- The paper does not address reason (i), the rebuild cone. It gives no build time.
- Table 1 gives about 3,300 successful agents; Table 3 gives 3,490 merged.

## 7. Relation to the two anchors

- Turing Agent: both give independent proof tasks to parallel agents. Turing Agent holds a dependency graph and checks each split in Lean. This work has neither, and it names the missing graph as a cost [P] (Section 3.5, item 3). This work is earlier (April 2026). Turing Agent does not cite it [S] (Semantic Scholar reference list).
- MathEye: both start from statements closed with `sorry`. MathEye computes which open obligations the theorem needs. Here, agents proved cited theorems that no target needed [P] (Section 4.2). MathEye does not cite it [S] (Semantic Scholar reference list).
- The paper cites Draft-Sketch-Prove and DeepSeek-Prover-V2 for decomposition, and M2F as concurrent work [P] (Sections 2.3, 3.1, 5).

## 8. What this repository can use

- Table 3 gives a cost model for a flat task queue: tokens for each outcome class. A test of a decomposition method can report the same classes.
- The blocked class shows the price of a missing dependency order: 4,668 runs. A split that records its dependencies removes this class.
- The three copies of one definition [P] (Section 4.1) show that independence of proofs does not give independence of definitions. The library can mark the splits that add a shared definition.

## 9. Open points and things not read

- How long did a pull request wait, and how many times was it requeued? The paper does not say. Whether the public repositories hold logs that answer this is not verified [U].
- The code of `repoprover` was not read. Figures 1, 2, 4 and 6 were not viewed.
