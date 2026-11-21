# Lea: An Agent Backbone for Mathematician-Controlled Formalization in Lean

| Field | Value |
|---|---|
| Authors, organisation | Shaswat Patel and Daniel Aarao Reis Arturi (equal contribution), with 7 others (last author Chinmay Hegde). New York University, Fundação Getulio Vargas, Oklahoma State University |
| Date and version read | 6 November 2026, version 1 |
| Source | arXiv 2611.08849, https://arxiv.org/abs/2611.08849 ; code https://github.com/VIDA-NYU/Lea (not opened) |
| Licence of the source | CC BY 4.0 (arXiv page) |
| Files in this folder | `paper.pdf`, `note.md` |
| What was read | Full text from the arXiv HTML: Sections 1 to 5 and Appendices A to F. No figure viewed as an image; the captions were read |
| Read on | 21 November 2026 |

Confidence tags: **[P]** read in the primary source at the place given. **[S]** from a secondary
source. **[U]** not verified.

## 1. What the work is

Lea is a server program for Lean formalisation in which the mathematician controls the work while
an agent runs. The authors call it a "backbone": one program that holds the agent loop, the Lean
tools and the history, and that several user interfaces share [P, Section 2]. Two interfaces
exist: LeaChat (a web client) and LeaOverleaf (a browser extension for Overleaf documents)
[P, Section 3]. The evidence is the design and one case study [P, Section 5]. The work makes no
claim about a benchmark.

## 2. How it works

- **Project and blueprint.** A project is a workspace that stays between runs. It holds a
  blueprint. A blueprint is a list of lemmas and definitions with their dependencies. A node is
  "ready" when its dependencies are complete [P, Section 2].
- **Status from Lean only.** The system does not store the status of a node. It reads the status
  from the last Lean result. "Formalized" means that the file elaborates without `sorry`.
  "Verified" means that SafeVerify also accepts it: kernel replay, a type match for each
  declaration, and a list of permitted axioms [P, Section 2].
- **Typed events.** Each action and result is an event with a type: a proof edit, a Lean
  verdict, a sub-agent result. An interface reacts to events and holds no agent logic
  [P, Section 2].
- **Intervention during a run.** In LeaChat the mathematician can edit the proof, deny a tool
  call, rewrite a blueprint node, or change the strategy while the agent runs. The history
  records who made each change [P, Sections 2 and 3].
- **Fingerprint.** In LeaOverleaf each Lean result is bound to a fingerprint of the statement
  text, its kind, its dependencies and the guidance. A change to one of these marks the result
  "stale" [P, Section 3].
- **Audited.** A person sets this last status after review. It is bound to a hash of the
  annotation, the Lean file, and each project file that the Lean file imports. A change to one
  input removes it [P, Section 3].
- **Disproved.** A run can end with a machine-checked refutation of the statement. Example: "if
  d divides n then d ≤ n" fails for n = 0, and the author adds n ≥ 1 [P, Appendix D].

## 3. How it splits a proof

- **Unit.** A blueprint node. In LeaOverleaf a node is a definition or theorem in the LaTeX
  source with a comment such as `% lea: formalize label=divisor_le` and `% lea: uses={...}`
  [P, Appendix D].
- **Who chooses.** The mathematician. "the mathematician chooses the objects and decomposition,
  the agent produces and checks Lean" [P, Section 3]. In the case study the agent proposes
  definitions and proof approaches, and the mathematician confirms each one [P, Section 4].
- **Check before work.** None. Lean does not check that the children imply the parent. The order
  is from the leaves up: a node waits until its dependencies are complete, and "an unresolved
  dependency blocks the run" [P, Section 3].
- **Record.** A dependency graph that stays between runs. Each node records its dependencies and
  the sessions that worked on it [P, Section 2].
- **When a child fails.** The mathematician intervenes, or the run ends as "disproved". In the
  case study one sub-agent proves "a trivial restatement of an earlier lemma" in place of the
  target, and the mathematician corrects it [P, Section 4].

## 4. What it says about scale

- The case study has four core Lean files, three sessions, 38 sub-agent calls, 28 human messages
  and 24.7M tokens with GPT-5.5 [P, Section 4; Appendix E]. No count of lemmas or lines. No
  report of unused lemmas. No cost in money and no time.
- Rebuilds: a changed definition causes a rebuild of the dependents through the import graph, and
  the system reports which results stay valid. An edit inside the proof body of a theorem, with
  the declaration unchanged, "need not invalidate dependents" [P, Section 3].
- A Lean language server stays active and keeps its elaboration state between edits
  [P, Section 2].
- Sub-agents run at the same time. Each has its own scratch directory, turn limit and tool list
  [P, Section 2].
- Several mathematicians cannot work on one project at the same time. Conflict resolution is
  future work [P, Section 5; Appendix F].
- Human time: the review "did not take substantial time" [P, Figure 5 caption]. No hours.

## 5. Evidence

| Result | Place |
|---|---|
| Durfee square generating function proved from Mathlib alone, from an outline in chat messages | Section 4 |
| 28 human messages, most of them confirmations; one substantive correction | Section 4 |
| Survey by other authors: 81.7% want full or partial human control; 66.7% want to keep strategic control | Section 1, citing Collins et al. |

No ablation. No baseline. The authors write: "We do not yet offer a controlled comparison"
[P, Section 5].

## 6. Limits

Authors: one case study; no comparison; no test in other fields of mathematics; the output needs
refactoring before it meets the Mathlib standard; the status reports on faithfulness are
"self-assessments" [P, Sections 3 and 5].

Reader: the case is a known result of small size. The paper gives no measure of how much the
human choice of the split helps.

## 7. Relation to the two anchors

- **Turing Agent** is ten days later. The reference list that Semantic Scholar gives for it (30
  entries) does not have Lea [P, `refs_2611.21299.json`]. Same: a dependency graph of
  obligations and parallel sub-agents. Different: in Lea a person chooses the split and no Lean
  check of the split exists; Lea works from the leaves up, Turing Agent from the parent down.
- **MathEye** is eleven days later and does not cite Lea. Same: a person stays inside the loop.
  Different: MathEye computes which questions to ask and takes yes or no; Lea lets the person
  change any object at any time and computes nothing about the questions.
- Lea cites LeanMarathon, Numina-Lean-Agent and LeanArchitect. It does not cite Archon, Theo or
  AIProver [P, References].

## 8. What this repository can use

- The invalidation rule separates the statement from the proof body. A split that fixes
  statements first keeps rebuilds small, because later proof edits do not make dependents stale.
- The history records whether a person or the agent made each step. Such a history is a source
  of human splits with exact provenance for the library.
- The `uses={...}` comment is a small format for a split that a person chose. A harvest tool can
  read it.
- "Disproved" as a normal end state shows that a child statement can be tested by counterexample
  search before proof work.
- The three statuses (formalized, verified, audited) separate what Lean proves from what a
  person confirmed.

## 9. Open points and things not read

- Does the leaf-first order cause proved lemmas that the parent cannot use? The paper does not
  say.
- The repository and the figures were not opened. The paper says that more projects exist, and
  that it does not report them [P, Section 5].
