# Axiom Math: the classification of finite simple groups and the Stacks Project in Lean

| Field | Value |
|---|---|
| Authors, organisation | Axiom Math. The first post names 4 core contributors (Dean Cureton, Vasily Ilin, Bhavik Mehta, Niels Voss) and 27 other contributors |
| Date and version read | Blog post of 26 October 2026; blog post of 4 November 2026; blog post of 16 November 2026; two repository READMEs as they were on 21 November 2026 |
| Source | Not a paper. Company blog and repositories: https://axiommath.ai/research/the-enormous-theorem-formalized/ ; https://axiommath.ai/research/the-stacks-project-formalized/ ; https://axiommath.ai/research/beyond-the-classification-what-the-cfsg-corpus-unlocks/ ; https://github.com/AxiomMath/CFSG ; https://github.com/AxiomMath/Stacks |
| Licence of the source | Blog: "© 2026 Axiom Math". Both repositories: Apache-2.0 (README) |
| Files in this folder | `source.pdf` (the post of 26 October, printed), `note.md` |
| What was read | The post of 26 October in full. The section "Engineering coherent mathematics at scale" and the sections after it in the post of 4 November. The first sections of the post of 16 November. Both READMEs in full. No Lean file was opened and nothing was built. No technical report exists |
| Read on | 21 November 2026 |

Confidence tags: **[P]** the writer of this note read the statement in the primary source, and the
place is given. **[S]** the statement comes from a secondary source, which is named. **[U]** the
statement is not verified. A number without a tag is not permitted. Every [P] here is a company
blog post or a README. None of it is reviewed, and the writer of this note checked no Lean file.

## 1. What the work is

Axiom Math is a company. Its prover is AxiomProver. In October and November 2026 it released two
Lean developments. The first is a proof of the classification of finite simple groups (CFSG). It
has about 43.1 million lines. Engineers and mathematicians directed "swarms of dozens of AI
agents" for 24 days to make it [P, post of 26 October, paragraph 2]. The second is a formalisation of the Stacks
Project with about 16 million lines [P, post of 4 November, paragraph 2]. The posts describe the
organisation of the work in prose. They give no description of AxiomProver itself. Survey C found
no technical report on 10 November 2026, and the writer of this note found none on 21 November.

## 2. How it works

The CFSG project had five parts [P, post of 26 October, "Unleashing the swarm"].

1. **A proof map.** A proof map is a shared record of what must be proved and how the pieces
   depend on one another. Axiom built it from the literature and from earlier Lean work. It had
   108 milestones and about 380 smaller tasks.
2. **Claims.** An agent claims a milestone through a GitHub issue and reports in Slack. When a
   task needs mathematics that does not exist yet, the agent delegates it to other agents.
3. **Roles.** "Lead agents decomposed difficult arguments and reviewed the statements being
   formalized." Other agents search for existing results or write proofs. Other agents do
   integration: they trace the final theorem back through its prerequisites and find missing
   links [section "Keeping the proof connected"].
4. **A shared repository.** Results enter one repository, where other agents use them.
5. **People.** Mathematicians examine obstructions. Engineers keep the system running. People
   inspect the final statement and its definitions. Lean checks the proofs [section "From
   completed pieces to a completed proof"].

The Stacks post names a hierarchy of agents with special roles and strict coordination rules. It
gives no detail [P, post of 4 November, section "Engineering coherent mathematics at scale"].

## 3. How it splits a proof

- **Unit.** A milestone theorem, then a smaller theorem. In the Stacks library the unit is a tag
  of the source text; a declaration carries `@[stacks TAG]` [P, Stacks README].
- **Who chooses.** People and agents build the first proof map from the literature. Lead agents
  split further during the run.
- **The check before work on the children.** It appeared after a failure. On 13 October only one
  milestone closed. Engineers then started a replanning effort, and agents split unfinished
  milestones into smaller theorems. "Each proposed decomposition had to explain how those smaller
  theorems, together with existing results, would establish the original milestone through a
  short Lean proof" [P, post of 26 October, "Keeping the proof connected"]. This is a proof of
  the parent from the children, required with the split.
- **Record.** A dependency graph, public at cfsg.axiommath.ai/proof-map [P, "Learn more"].
- **When a child fails or drifts.** A recurring fault was a proof under an added assumption.
  Review had to compare the proved statement with the planned statement. It had to judge whether
  the added assumptions follow from the stated hypotheses [P, section "Unleashing the swarm"].
  Early milestones hid large prerequisites that agents had assumed and not proved. Axiom deleted
  tens of thousands of lines and restarted parts [P, same section].

## 4. What it says about scale

This is the most direct company statement on the scaling problem that Prove2Me names. All items
are [P, post of 26 October, section "Keeping the proof connected"].

- **Rebuild.** "build times became a bottleneck: agents produced proofs faster than Lean could
  recheck them". A change to a shared result could force Lean to recheck all its dependents. With
  agents on separate machines, the same work was repeated.
- **Remedy 1.** A system distributes cached build results to the workers. It runs independent
  checks in parallel. It reuses a result when the code and its dependencies are unchanged.
- **Remedy 2.** Axiom moved expensive finite calculations into certificates that are checked
  separately. The post claims a gain of orders of magnitude and gives no number.
- **Interference.** Several forms of one definition had to stay compatible, and agents had to
  reuse results in place of copies. The post gives no count of conflicts and does not describe a
  merge queue.

| Measure | CFSG | Stacks |
|---|---|---|
| Lines of Lean | about 43.1 million [P, post] | about 16 million [P, post] |
| Time | 24 days; first swarm on 2 October 2026 [P, post] | not given |
| Agents | dozens [P, post] | not given |
| Full build | under 24 hours, with changes to Lake that are not upstream yet [P, CFSG README] | no time given; about 64,000 modules [P, Stacks README] |
| Repository size | 12,563,059 KB [P, GitHub API, field `size`] | 250,511 KB [P, GitHub API] |
| Code taken from others | about 1.2 million lines from Qiuzhen-CFSG [P, post, acknowledgements] | none named; built on Mathlib [P, README] |
| Faults found in the source | 34 deviations that needed a resolution [P, post] | dozens of statements [P, post] |

The cone of one result is large. A typical one of 30 application theorems cites corpus theorems
whose proofs have about 880,000 lines, and it adds about 1,200 lines [P, post of 16 November,
section "What Axiom Prover formalized"]. No figure is given for cost, tokens or models.

## 5. Evidence

The evidence is two public repositories and three blog posts. The READMEs claim no `sorry`, no
`native_decide`, and only the three standard axioms [P, both READMEs]. The CFSG statement comes
from the TauCeti project [P, CFSG README]. There is no baseline and no ablation. No post measures
the effect of the replanning of 13 October, of the build cache, or of the certificates. No
independent full build was found in a primary source [U]. The release date differs between
sources. The post of 26 October says "Today". The post of 4 November says 27 October. The GitHub
API gives 27 October 2026 as the creation date of the repository.

## 6. Limits

Stated by Axiom: progress was "easy to overstate", because Lean accepts a result under an unproved
assumption [P, post of 26 October]. People must still read the final statement and definitions.
The Stacks library has two tiers: `StacksCore` is reviewed by people, and `StacksFrontier` is
written by agents and still needs review [P, Stacks README]. The Stacks Project asked that
AI-made pull requests stay out of its repository [P, post of 4 November].

Found by the reader: AxiomProver, the models and the coordination tools are closed. All process
facts are a narrative by the company. 43.1 million lines in 24 days is about 1.8 million lines a
day (reader's computation). The posts do not say how much of this is generated data, such as
certificates.

## 7. Relation to the two anchors

Both anchors are later, and neither cites Axiom (checked in the two reference files).

**Turing Agent (arXiv 2611.21299).** The same check exists in both: a split is accepted with a
Lean proof that the children give the parent. Turing Agent has it by design, for trees of at most
108 lemmas. Axiom added it eleven days after the first swarm, for 108 milestones in a proof of
43.1 million lines. Axiom adds two things that Turing Agent lacks: integration agents that work
from the final theorem backwards, and a review of added assumptions. Turing Agent reports that
about 10 % of its lemmas were proved and not used. Axiom reports a related waste: it deleted lines
that rested on unproved assumptions.

**MathEye (arXiv 2611.22103).** MathEye records a confirmed claim as an assumption. Axiom shows
the risk: a milestone under an assumption looks closed. MathEye's graph can show which assumptions
remain; Axiom did this by review.

## 8. What this repository can use

- **Require the parent proof with the split.** Axiom's rule supports the Turing Agent check from
  a second, larger case. The proposed algorithm can treat it as mandatory.
- **A move "certificate".** Moving a finite computation into a separately checked certificate is
  a split by interface that cuts rebuild cost. The library has no such move among its 17.
- **A field for added assumptions.** Each entry can record whether a child proves the planned
  statement or a weaker one.
- **Cone size as a feature.** "880,000 lines behind 1,200" is a measure of rebuild exposure. The
  feature graphs can compute it for each entry.

## 9. Open points and things not read

- The repositories were not cloned (12.6 GB). File counts, lemma sizes and import structure are
  not known to this note.
- The proof map, the errata list, the paper on the Unbalanced Group Theorem, and the posts on the
  Weil conjectures, Faltings' theorem and the minimal model program were not read.
- IEEE Spectrum reported on the project in November 2026 [S, link on axiommath.ai]; not read.
- How AxiomProver chooses a split, and what a lead agent sees, is not public.
