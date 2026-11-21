# LeanMarathon: Toward Reliable AI Co-Mathematicians through Long-Horizon Lean Autoformalization

| Field | Value |
|---|---|
| Authors, organisation | Yuanhe Zhang (University of Warwick, RIKEN), Yuekai Sun (University of Michigan), Taiji Suzuki (University of Tokyo, RIKEN), Jason D. Lee (University of California, Berkeley), Fanghui Liu (Shanghai Jiao Tong University, corresponding author) |
| Date and version read | 3 June 2026, version 1 |
| Source | arXiv 2606.05400, https://arxiv.org/abs/2606.05400 ; code https://github.com/YuanheZ/LeanMarathon |
| Licence of the source | CC BY 4.0 (arXiv page) |
| Files in this folder | `paper.pdf`, `note.md` |
| What was read | Full main text (Sections 1 to 5) and the text of Appendix A from the arXiv HTML. From the repository: `agents/Blueprinter/docs/references/decomposition.md` and `agents/Worker/docs/contracts/local-refinement.md`, read in full. No figure viewed as an image |
| Read on | 21 November 2026 |

Confidence tags: **[P]** read in the primary source at the place given. **[S]** from a secondary
source. **[U]** not verified. "Repository" is the code repository as it was on the day of reading.

## 1. What the work is

LeanMarathon is a harness with four agents that formalises a full research paper in Lean 4. It
receives the LaTeX source of the paper and a file of target statements. It claims seven target
theorems from two papers on four Erdős problems, with 258 proved lemmas and theorems and no
`sorry` [P, Section 4]. The evidence is three runs with cost figures, one comparison with an
earlier version of the harness, and one comparison with Aristotle.

## 2. How it works

- **Blueprint.** The blueprint is one Lean file. Each lemma or theorem is a node with a Lean
  type, a LaTeX statement and a LaTeX proof. A body is `sorry`, or `sorry_using [...]` with the
  intended dependencies, or a full proof. All shared state is in this file [P, Section 2.1].
- **Durability.** The authors define agent durability as the property that a system "stays
  coherent across a multi-hour run" and that one wrong decision does not damage the rest
  [P, Section 1]. The mechanism has four parts: a limited edit region for each agent, a
  deterministic CI gate, a stop hook that holds an agent until its pull request merges, and no
  memory outside the blueprint file and the GitHub issue stream [P, Section 3.3].
- **Four agents.** The Blueprinter writes the skeleton. The Target-Reviewer compares each target
  theorem with its Lean type and cannot edit. A Worker proves one node. The Refiner repairs
  defects that touch more than one node [P, Table 1].
- **CI gate.** Seven checks. Two matter here. Dependency parity: the references in the prose
  proof must be equal to the dependencies that the Lean elaborator reports. Lemma closeness:
  "every lemma must be cited by some later lemma or theorem" [P, Section 3.3].
- **Refiner rule.** A full proof that compiles after a repair stays byte-identical. A full proof
  that does not compile becomes a placeholder; no partial edit [P, Section 2.2.4].

## 3. How it splits a proof

- **Unit.** A lemma or theorem declaration in the blueprint file.
- **Who chooses.** The Blueprinter, from the source proof. Its aim is a small "repair radius":
  the expected number of declarations that must change if one declaration is wrong
  [P, Section 2.2.1]. A rubric file gives the rules. It names concept, interface and cleanup
  nodes, lists ten conditions to split (for example "when necessity and sufficiency use different
  ideas"), and five conditions not to split [P, repository, `decomposition.md`].
- **Later changes.** A Worker can add helper lemmas only in a region immediately before its
  target; the target is the one terminal node of this local graph [P, Section 2.2.3]. The Refiner
  splits a failed node into smaller nodes [P, Section 4.4].
- **Check before work.** All statements must elaborate with placeholder bodies [P, Section 3.1].
  Lean does not check that the children imply the parent. Work goes from the leaves up: a node
  gets a Worker only when its dependencies are proved [P, Section 3.2]. The Worker first asks if
  the statement gives what the later nodes need, and tries a numeric counterexample
  [P, Section 2.2.3].
- **Record.** A directed acyclic graph that the tool reads from the Lean elaborator.
- **When a child fails.** The Worker files an issue, and only for a concrete defect. The Refiner
  marks the smallest connected part of the graph that must change, and classifies the defect as
  drift of the blueprint or a gap in the source [P, Section 2.2.4].

## 4. What it says about scale

| Run | Lean lines | Proof nodes | Rounds | Workers | Critical path | Tokens | Cost |
|---|---|---|---|---|---|---|---|
| Erdős–Graham | 8,513 | 111 | 19 | 58 | 11:38:23 | 308M | $257.17 |
| #1196 | 3,988 | 44 | 17 | 33 | 11:32:40 | 245M | $189.43 |
| #164 and #1217 | 14,592 | 147 | 40 | 111 | 40:43:21 | 796M | $623.54 |

[P, Tables 2 and 3]. All agents use Codex with GPT-5.5 [P, Section 4.2].

- Interference: 135 Worker pull requests merged, at most 16 in one round, with no merge conflict.
  The reason is that the edit regions of Workers are disjoint, so the patches commute
  [P, Section 4.3].
- Merge queue: the orchestrator merges each pull request directly, because GitHub auto-merge
  "serialises across parallel PRs" [P, Section 3.2].
- Rebuilds: the paper gives no build time. The time in the stop hook and CI wait is 07:15:10,
  02:15:33 and 07:05:26 [P, Table 3]. Reader's note: the blueprint is one file, so each check
  compiles all of it. A changed parent statement caused 12 downgrades of full proofs in the
  largest run [P, Section 4.6].
- Unused lemmas: the lemma closeness check rejects a lemma that no later node cites.
- People: the runs have no human input. People change the harness between runs
  [P, Section 4.3]. No human hours.
- Expansion: about 62 lines of paper prose became roughly 84 nodes [P, Section 4.6].

## 5. Evidence

| Result | Place |
|---|---|
| Seven target theorems, 258 lemmas and theorems, no `sorry`, no axiom | Table 2; Section 4.3 |
| Earlier harness on the same paper: about 12 days, 137 issues, 26 `sorry` left. Current harness: about 3 days, 16 issues, 0 `sorry` | Table 5 |
| Aristotle on the same inputs: 0 targets on both papers after more than 40 and 24 hours | Table 6 |
| Largest run: 32 defect areas, 26 drift and 6 source gaps | Section 4.6 |
| Failure: for the unit-distance disproof the run modelled a number field as a dummy record; this passed CI and proved nothing | Section 4.9 |

The "ablation" compares two harness versions that differ in two choices at once: the Refiner
reads the source, and the Worker has no line budget [P, Section 4.7]. It does not isolate the
split. With a budget of lines, Workers gave size as the reason to stop in 14 issues
[P, Table 5]. No baseline is a single Codex agent with the same model.

## 6. Limits

Authors: the harness cannot supply theory that Mathlib does not have. The CI checks are
structural, not semantic [P, Sections 3.3 and 4.9].

Reader: three runs. The Target-Reviewer examines only target theorems; the statements between
depend on the Worker's own audit. Table 2 gives four targets for Erdős–Graham and Table 6 gives
three. The paper does not discuss compile time for a file of 14,592 lines.

## 7. Relation to the two anchors

- **Turing Agent** is later by five months. The reference list that Semantic Scholar gives for it
  does not have LeanMarathon [P, `refs_2611.21299.json`]. Same: a graph of obligations, a frozen
  statement during proof, parallel agents on independent nodes. Different: LeanMarathon works
  from the leaves up and has no Lean check of a split. Its CI rejects unused lemmas, where Turing
  Agent reports about 10 % of them. It reports cost and one comparison of harness versions.
- **MathEye** is later, and neither work cites the other. Same: `sorry_using [...]` is a
  placeholder with declared dependencies, and the parity check compares declared and real edges.
  Different: no person answers questions, and no solver selects obligations.
- The work cites Aristotle, LeanArchitect and Draft, Sketch, and Prove. It does not cite Hilbert
  or Archon [P, References].

## 8. What this repository can use

- The rubric is a written set of split rules. The 17 moves of the library can be compared with
  it, rule by rule.
- Repair radius is a number that the feature graphs can compute for each of the 229 entries.
- The frozen statement with one edit region before the target gives parallel work with no merge
  conflict. It is the clearest answer in this group to interference between agents.
- The lemma closeness check and the parity check are cheap graph tests for a proposed split.
- A stop rule that uses size is gamed. A stop rule must name a concrete defect.
- The count of 26 drift defects to 6 source gaps shows that most repairs correct the split, not
  the mathematics.

## 9. Open points and things not read

- How does the method work when the blueprint is too large for one file?
- How good is the first split? The paper gives the number of repairs and no measure of the
  first graph.
- Not read: the reference list in detail, the figure images, the other repository files.
