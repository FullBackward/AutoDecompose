# Lean Pool: An AI-Maintained Archive of Formalized Mathematics

| Field | Value |
|---|---|
| Authors, organisation | Vasily Ilin, University of Washington. The acknowledgements name Justin Asher as co-creator. This is not a company paper. It is the reader's free choice for this group, because the archive holds OpenAI's Lean releases and measures what it costs to keep such code building. Axiom Math lists the author as a core contributor to its classification project [P, Axiom post of 26 October 2026] |
| Date and version read | Version 1, 21 September 2026 |
| Source | arXiv 2609.25199, https://arxiv.org/abs/2609.25199 ; index https://vilin97.github.io/lean-pool/ |
| Licence of the source | CC BY 4.0 (arXiv page) |
| Files in this folder | `paper.pdf`, `note.md` |
| What was read | Sections 1 to 11 in full from the arXiv HTML. Appendix A.2, Appendix B, the start of Appendix C, Appendix D, Appendix E and Appendix F in full. Appendices G, H and I not read. No figure viewed. The archive was not opened |
| Read on | 21 November 2026 |

Confidence tags: **[P]** the writer of this note read the statement in the primary source, and the
place is given. **[S]** the statement comes from a secondary source, which is named. **[U]** the
statement is not verified. A number without a tag is not permitted.

## 1. What the work is

Lean Pool is one repository that holds many finished Lean projects, each with its own authors.
AI agents add projects, repair them when Lean and Mathlib change, and shorten them
[P, Section 1]. The paper is an operations report. It gives measured build times, repair counts
for six version upgrades, and the effect of five accepted clean-up changes. The author states that
one page is written by a person and that the rest is "produced almost entirely by AI"
[P, disclaimer]. The earlier surveys do not mention the work (name search, 21 November 2026).

## 2. How it works

- **Admission.** A project must be complete. It must have no `sorry`, no new axiom, no
  `set_option`, and no linter waiver. It needs a *card*: a record of authors, source, proof
  provenance and main results with informal statements. The licence must be Apache-2.0 or MIT
  [P, Section 2, "Admission rules"; Appendix B].
- **Continuous integration.** The checks build the whole library, reject warnings, run Mathlib's
  linters, and apply limits on proof size and file size [P, Section 3; Table 15].
- **Daily jobs.** Agents search for new formalisations, inspect open pull requests, optimise one
  project, and announce accepted work [P, Appendix C, Table 16].
- **Upgrade job.** A workflow starts when a new Lean or Mathlib release appears. It builds each
  project and gives each failing project to a repair agent. Then it assembles the patches and
  builds the combined archive [P, Section 5; Appendix C].
- **Review.** A model reviews each submission for faithfulness of the statements, sources and code
  quality. Maintainers decide on merges [P, Section 7; Table 9].

## 3. How it splits a proof

The work does not split proofs. It splits a library. The unit is a project that is developed
independently and kept in one common environment. This choice bears on the interference problem:
a repair agent works on one project, and the combined build comes after the patches are assembled
[P, Appendix C]. A cold build in continuous integration can run in shards, one for each group of
projects [P, Appendix B].

The paper gives one measure of the shape of machine-made proofs. The archive's copy of OpenAI's
Navier-Stokes and Euler development has 48,626 declarations and 530,547 dependency links
[P, Table 7]. Over 203 projects there are 173,362 declarations, 124,412 theorems and lemmas, and
1,389,967 dependency links; 87,408 declarations are used by more than one other [P, Table 6].

## 4. What it says about scale

**Size** on 21 September 2026 [P, Table 1; Appendix A, Table 10]: 211 projects, 7,043 Lean files,
3,228,485 source lines, 193,862 declaration commands, 837 registered main results. Proof
authorship: 70 human, 102 AI, 39 mixed.

**Build** [P, Appendix A.2, Table 12; one clean build each, 16 threads, Azure virtual machine]:

| Library | Million lines | Build minutes | CPU hours | Peak RAM (GiB) |
|---|---|---|---|---|
| Lean Pool | 3.23 | 60.28 | 14.29 | 20.03 |
| Mathlib, matching release | 2.33 | 37.44 | 9.38 | 7.35 |
| Tau Ceti | 1.46 | 30.89 | 7.13 | 10.67 |

**Upgrades** [P, Table 2; Table 19]. The table gives the projects whose unchanged source fails to
compile under the new version.

| To Lean version | Projects | Fail | Files edited | Lines changed |
|---|---|---|---|---|
| 4.31.0-rc1 | 59 | 44 | 825 | 25,583 |
| 4.32.0-rc1 | 91 | 58 | 402 | 5,653 |
| 4.33.0-rc1 | 143 | 100 | 576 | 11,690 |
| 4.33.0-rc2 | 145 | 19 | 585 | 5,221 |
| 4.34.0-rc1 | 148 | 3 | 448 | 4,676 |
| 4.34.0 | 191 | 97 | 639 | 5,951 |

In the last upgrade 95 of 97 repair jobs ended with success, and further integration work was
needed after them [P, Appendix D, Table 18]. Money and human hours for upgrades "were not logged"
[P, Table 19 caption].

**Review cost** [P, Table 5]: 285 reports at $308.52 in total, median $0.20, from API estimates;
6 later reports at $752.38 in API-equivalent price, median $89.03.

## 5. Evidence

Whole-library clean builds before and after an accepted change [P, Table 3; Table 20]:

| Change | Lines removed | Build minutes, before to after |
|---|---|---|
| Library-wide compression | 45,217 | 16.11 to 15.59 |
| Contributor proof golfing | 12,515 | 21.83 to 23.01 |
| Certificate simplification | 513 | 30.22 to 29.13 |
| Elaboration-cost reduction | 54,965 | 28.46 to 26.82 |

Shorter proofs do not always build faster: the golfing change removed 12,515 lines and the build
became longer. A refactoring that added reusable interfaces to the Navier-Stokes project raised
its build time from 879.67 s to 887.78 s [P, Table 4]. A change to Lean modules and narrower
imports cut the largest process from 12.605 GiB to 2.891 GiB in one benchmark [P, Table 21].

Review agreement is low. Of 69 pairs of reports on the same pull request, 37 have the same verdict
[P, Appendix F, Table 22]. No pair reviews the same revision, so this is not a clean repeat test.
There is no baseline system and no ablation. Each timing is one run.

## 6. Limits

Stated in the paper: review accuracy "was not independently labeled" [P, Figure 3 caption]. A
successful upgrade build does not show that every declaration has the same type before and after
[P, Appendix D]. In the last upgrade the repairs strengthened hypotheses on measurability,
sigma-finiteness and maximality [P, Appendix D]. The review service was switched off before the
observation date [P, Appendix F]. Profiling is advisory and does not block a merge [P, Appendix B].

Found by the reader: most of the text is machine-written, and one person takes responsibility for
it. The author maintains the archive, so the report is not independent. A repair that strengthens
a hypothesis changes a statement, and no check of the main results against their cards after an
upgrade is reported.

## 7. Relation to the two anchors

The work is earlier than both anchors by eight weeks. Neither anchor cites it (checked in the two
reference files). It does not cite Prove2Me.

**Turing Agent (arXiv 2611.21299).** Turing Agent ends when Lean accepts one proof. Lean Pool
measures what comes after: 44 of 59 projects failed at the first upgrade. A proof of 108 lemmas
from Turing Agent would enter such an archive as one project and would need this upkeep. Both
systems give independent units to parallel agents. Turing Agent's unit is a lemma inside one
proof; Lean Pool's unit is a project inside one library.

**MathEye (arXiv 2611.22103).** MathEye keeps a dependence graph for one proof in order to choose
what to ask a person. Lean Pool exports a dependence graph for each project in order to show
readers what a result rests on. Neither uses the graph to limit rebuild cost.

## 8. What this repository can use

- **Rebuild figures for the scaling problem.** 3.23 million lines need 60.28 minutes on 16
  threads. The table compares a library that agents maintain with Mathlib on the same machine,
  which the build figures in survey E do not do.
- **Version drift as a cost of a decomposition.** A split into many small lemmas makes many
  statements that a new Mathlib can break. The upgrade table gives a rate to plan with.
- **Shorter is not faster.** The golfing result argues against "fewer lines" as the only measure
  of a good decomposition. An experiment must measure build time as well.
- **Narrow imports.** The module change cut memory by a factor of about 4 (reader's computation
  from Table 21). Import width is a feature that the feature graphs can record for each entry.
- **Project cards.** The card (authors, source, provenance, main results with informal statements)
  is close to the library's entry record and can guide its fields.

## 9. Open points and things not read

- Appendices G, H and I, and the figures, were not read. The archive itself was not inspected.
- The LeanEval audit that the paper cites for reuse was not read.
- Tau Ceti, a library written by AI under human roadmaps, has a required performance check before
  a merge [P, Table 15]. It is a candidate for a separate note; this note did not read its source.
- The cost of the agents that do the daily jobs is not reported.
