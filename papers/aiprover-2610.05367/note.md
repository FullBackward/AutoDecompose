# AIProver: Agentic Auto-Formalization of Mathematical Research via Certificate-Driven Evolving Harness

| Field | Value |
|---|---|
| Authors, organisation | Prithwish Jana and 11 others (last author Vijay Ganesh). Georgia Institute of Technology, University of Pennsylvania, Foothill College, Rutgers University, Simon Fraser University, University of Texas at Austin |
| Date and version read | 4 October 2026, version 1 |
| Source | arXiv 2610.05367, https://arxiv.org/abs/2610.05367 ; project page https://jprithwish.github.io/AIProver |
| Licence of the source | arXiv non-exclusive distribution licence 1.0 (arXiv page). This is not a Creative Commons licence: the owner must decide whether `paper.pdf` can stay in a public repository |
| Files in this folder | `paper.pdf`, `note.md` |
| What was read | Full main text (Sections 1 to 6) and Table 3 from the arXiv HTML. Appendices A, B, D and F.2 to F.4 read. Appendices C, E, F.1 and F.5 to F.7 searched only. No figure viewed as an image |
| Read on | 21 November 2026 |

Confidence tags: **[P]** read in the primary source at the place given. **[S]** from a secondary
source. **[U]** not verified. "Reader's" marks an inference of the writer of this note.

## 1. What the work is

AIProver is a system that translates one informal theorem with its informal proof into one Lean 4
file. The work trains an open-weight model (Leanstral-1.5, 119B parameters) and, in alternate
rounds, changes the program that controls the model [P, Section 4]. It also gives a benchmark,
LoCoBench, with a validation part of 771 instances [P, Section 5.1]. It claims 36.7% correct
complete formalisations as a single agent, and 79.8% as a tool of Claude Code [P, Table 3]. The
evidence is one benchmark table with 39 other systems.

## 2. How it works

- **Certificate.** A certificate is the text that a verifier returns together with its score. Four
  checks run in a fixed order: type-correctness (the Lean diagnostics), completeness (the position
  of a `sorry` or the bad axiom), semantic correctness (two directions of an equivalence test
  against a reference Lean statement), and length fidelity. The joined certificate puts the first
  failing check first [P, Section 4.2.1]. It tells the next step what to repair.
- **Reward ladder.** One number grades a run: 0.05 for an ill-typed file, 0.15 to 0.50 for an
  incomplete proof, 0.30 to 0.90 for a complete proof, more when the statement is also equivalent
  to the reference [P, Table 1]. Reinforcement learning uses this number [P, Section 4.2.3].
- **Evolving harness (HarnessEvolve).** A harness is the program around the model: prompt, tools,
  memory and control flow [P, Definition 3.1]. HarnessEvolve is a search over harness programs. A
  tree holds each harness that was tried, its score, its certificates, and the label accepted or
  rejected. In each round a coding agent (Claude Code with Claude Opus 5) rewrites one accepted
  harness, and the child runs on 300 training problems. The tree keeps rejected children also, so
  that later rewrites do not repeat them [P, Section 4.2.2; Appendix A.1].
- **What the search found.** The final harness adds four hooks. One hook withholds library search
  until the answer file holds a theorem. One hook compiles the file at stop, asks for a repair,
  and rejects a statement that a fixed tactic sequence closes [P, Appendix F.2, Listing 8].
- **Skill mode.** Claude Code or Codex is the host. The host plans, judges the statement, and
  splits. AIProver writes Lean and searches for proofs [P, Appendix B].

## 3. How it splits a proof

The single agent does not split proofs across agents. The skill mode splits, as a second step.

- **Unit.** A lemma or a theorem part, written as a Lean statement with `:= by sorry` in one
  "skeleton" file [P, Listing 12, step 4a].
- **Who chooses.** The host agent, from the lemmas of the informal proof. The rule is "One job per
  NL lemma is the natural grain. Split further only when a piece fails twice" [P, Listing 13,
  Section 3]. The host first sends the whole problem with 4 samples, and splits only if no sample
  passes [P, Appendix B].
- **Check before work.** The skeleton must compile, and the host must judge it against the
  informal text. Then the statements are frozen. Lean does not check that the children imply the
  parent before work starts. The parent is one more job. It receives the children as `sorry`
  statements and runs at the same time as the children [P, Listing 12, step 4b]. (Reader's
  reading of the listing.)
- **Record.** The skeleton file. No graph.
- **When a child fails.** The host sends it again with a one-line hint, and after a second
  failure splits it along the informal proof [P, Listing 12, step 4d]. The tool reports whether a
  returned file kept the frozen text: `fixed-code:kept` or `CHANGED` [P, Listing 12].

## 4. What it says about scale

- A task is one theorem, not a development of many files. The median validation proof has 708
  words [P, Appendix A.2.4]. The work gives no count of lemmas for each output and does not
  report unused lemmas.
- Each problem has its own new Lake project with a read-only prebuilt Mathlib [P, Listing 4].
  Agents share no files. The work says nothing about rebuilds or a merge queue.
- About 44 runs are active at one time; each Lean server uses about 2.3 GB, so memory limits the
  number [P, Appendix A.1].
- Cost for each attempt: $0.32 alone, $1.55 with Claude Code, $0.85 with Codex [P, Section 5.3].
  One AIProver session has a median of about 13 minutes [P, Listing 13, Section 1].
- No person takes part at inference. No cost is given for the training or the harness search.

## 5. Evidence

LoCoBench-Val, 771 instances, pass@4, statement correct and proof complete [P, Table 3].

| System | Result |
|---|---|
| Leanstral-1.5 with tools | 12.6% |
| + seed harness | 15.7% |
| + HarnessEvolve only | 22.6% |
| AIProver (training + evolved harness) | 36.7% |
| Codex (GPT-5.6-Sol) / Claude Code (Opus 5) | 34.1% / 41.9% |
| Numina-Lean-Agent + Codex / + Claude Code | 44.5% / 72.5% |
| AIProver + Codex / + Claude Code | 62.4% / 79.8% |

- The ablation adds the model and harness components one at a time [P, Section 5.3]. No ablation
  isolates the split. The work does not say how many instances used the split.
- A plain coding agent with the same model is a baseline. But this baseline has "no Lean verifier
  in the loop" and no prebuilt Mathlib [P, Appendix A.3], and it uses 1.8 turns for each attempt
  [P, Table 6]. Reader's conclusion: the step from 41.9% to 79.8% mixes Lean tools, more samples,
  the judge procedure and the split.
- One sample on 509 training problems: 205 solved, and 173 that compile completely but state a
  different theorem [P, Listing 13, Section 1].

## 6. Limits

Authors: the work has no limitations section. Proof faithfulness is not scored, because no
reliable check exists [P, Section 5.2]. The model "cannot reliably judge its own statement"
[P, Listing 12].

Reader: two language models judge semantic correctness on the validation set, not Lean
[P, Appendix A.4.1]. The turn limit differs between places: 90, 100 and 200 [P, Listing 8;
Listing 12; Appendix B]. The project page gave no code link on 21 November 2026 (reader's check).

## 7. Relation to the two anchors

- **Turing Agent** is later (16 November 2026) and cites AIProver [P, `refs_2611.21299.json`].
  Same: informal theorem and proof in, Lean out, with a statement check that is separate from the
  proof. Different: Turing Agent checks in Lean that the children imply the parent, and holds a
  graph; AIProver freezes a skeleton and has no such check. The "experience pool" keeps lessons
  inside one proof. The HarnessEvolve tree keeps lessons about harness designs between training
  rounds. AIProver cites Prove2Me, Hilbert and LeanMarathon [P, References].
- **MathEye** is later, and neither work cites the other. Same: both give value to a proof that
  compiles with `sorry`. Different: MathEye asks a person about each open obligation.

## 8. What this repository can use

- The frozen skeleton with the `kept` or `CHANGED` report is a cheap test that a child proof did
  not change a shared statement. It prevents interference without a merge queue.
- The grain rule (one job for each informal lemma, split again after two failures) is a policy
  that the 229 library entries can test.
- The triviality probe (`tauto; simp_all_arith!; noncomm_ring`) can reject a vacuous child lemma
  before work starts.
- The reward ladder can score a partial decomposition, because it separates a correct statement
  with `sorry` from a wrong statement with a full proof.

## 9. Open points and things not read

- How often does the host split, and what does the split add? The work gives no figure.
- Not read in full: Appendices C, E, F.1, F.5 to F.7. Figures 1, 3, 4 and 7 not viewed.
