# Automated Conjecture Resolution with Formal Verification (Rethlas and Archon)

| Field | Value |
|---|---|
| Authors, organisation | Haocheng Ju, Guoxiong Gao, Jiedong Jiang, Bin Wu and 12 others; contact authors Bryan Dai and Bin Dong. Peking University and the company IQuest Research, with Westlake University, Tianjin University, Kyoto University and Stanford University (PDF, page 1) |
| Date and version read | Version 2, 30 May 2026 (version 1: 4 April 2026) |
| Source | arXiv 2604.03789, https://arxiv.org/abs/2604.03789 ; code https://github.com/frenzymath/Archon and https://github.com/frenzymath/Rethlas ; result https://github.com/frenzymath/Anderson-Conjecture |
| Licence of the source | CC BY 4.0 (arXiv page) |
| Files in this folder | `paper.pdf`, `note.md` |
| What was read | Sections 1 to 3, 4.3, 4.4, 5.2 and 6 in full from the arXiv HTML; Appendices 15 and 16 read; Sections 4.1, 4.2 and 5.1 (the mathematics and Rethlas cases) and Appendices 7 to 14 not read. Figure 6 viewed. The Archon repository `README.md` and `docs/MULTILANE.md` (version 0.3.3) searched |
| Read on | 21 November 2026 |

Confidence tags: **[P]** read in the primary source at the place given. **[S]** from a secondary
source. **[U]** not verified. "README" is the Archon repository as it was on the day of reading.
It is later than the paper, so it describes later software.

## 1. What the work is

The work has two agents. Rethlas writes an informal proof of a research problem. Archon translates
an informal proof into a Lean 4 project with many files [P, Section 3]. The work claims that the
pair solves an open problem of D. D. Anderson (2014) and verifies the proof in Lean with almost no
human work [P, abstract]. The evidence is this case, and two more formalisations from the
FirstProof benchmark [P, Section 5.2.1]. There is no benchmark table.

## 2. How it works (Archon)

- **Plan Agent and Lean Agent.** The Plan Agent starts with an empty context, splits the work
  into tasks and gives guidance. The Lean Agent writes Lean inside a limited scope. The reason:
  in a long session the record of failed attempts makes the agent stop trying [P, Section 3.2.1].
- **Three phases.** Scaffolding, proving, then verification and polish [P, Section 3.2.1].
- **Memory system.** Each agent writes a summary of its session. Global status documents hold
  the workflow stage, the proving status of each file, and records of each `sorry` that was
  removed. The memory keeps "failed approaches, and learned techniques" across context
  compression and restarts [P, Sections 3.2.1 and 3.2.2].
- **Review Agent.** It runs at the end of each session and reads the recent sessions together.
  It exists because a stall is visible only as a pattern across sessions [P, Section 3.2.2].
- **Ask Informal Agent.** The Lean Agent can ask a model, or Rethlas, for an informal sub-proof
  [P, Section 3.2.1].
- **Comparator.** A tool checks that the proved theorem is equal to a specification file of 30
  lines that a person examines, and that only standard axioms are used [P, Appendix 16].

## 3. How it splits a proof

- **Unit.** A file (module) and a theorem signature with `sorry` at each obligation
  [P, Section 3.2.1].
- **Who chooses.** The Lean Agent makes the first structure from the informal proof. The Plan
  Agent changes it later. "This decomposition is not fixed" [P, Section 3.2.1].
- **Check before work.** The paper states none. It does not say that Lean checks that the
  children imply the parent before the children are proved.
- **Record.** The file structure and the status documents. The paper has no graph. The later
  README adds a dependency graph command (`archon dag`) [P, README].
- **When a child fails.** The Lean Agent returns diagnostics. The Plan Agent examines the
  strategy again and sends a changed task [P, Section 3.2.1]. Example: the agent replaces a
  construction with Zorn's lemma by an explicit recursion, and changes dependent files in several
  sessions [P, Appendices 15.3 and 15.4].

## 4. What it says about scale

- Anderson: 19,448 lines in 42 files, about 80 hours of agent time [P, Section 4.4; Figure 6].
  The folder for one cited paper (Jensen) has 14,530 of these lines [P, Figure 6].
- Cost: three Claude Code Max plans ($200 each month), each at about 70% of its weekly quota for
  one week [P, Section 4.4]. FirstProof Problem 4: about 50 hours and about $1,200. Problem 6:
  30 hours and about $750, with Claude Opus 4.6 [P, Section 5.2.1].
- People: for Anderson, a person downloads PDF files and examines the 30-line statement
  [P, Section 4.4; Appendix 16]. For FirstProof, one mathematician reads reports for about
  twenty minutes in each 24 hours, and gives one hint of one sentence [P, Section 5.2.1].
- Parallel work: "multiple Lean Agents can operate in parallel" on independent obligations
  [P, Section 3.2.1]. The paper gives no number of agents.
- Rebuilds and merges: the paper says nothing. The README shows the later answer. A job is one
  model lane on one file. A job is accepted only if "only the assigned file changed". A merge
  agent for each file keeps the best proof of each declaration. Each lane works in an isolated
  worktree. A protection file can freeze a signature [P, README; `docs/MULTILANE.md`].
- The paper gives no count of lemmas and does not report unused lemmas.

## 5. Evidence

| Result | Place |
|---|---|
| Anderson's problem: full Lean proof, passes `lake build` and Comparator | Section 4.4 |
| FirstProof Problems 4 and 6 formalised; 2 of 10 problems selected | Section 5.2.1 |
| One comparison from the same state with three open obligations: with a human blueprint, 2 hours 12 minutes; without, 3 hours 43 minutes | Section 4.4 |

The authors call the last row a "controlled ablation". It has one run for each branch. In the
guided branch Archon does not follow the route of the blueprint [P, Section 4.4]. No ablation
isolates the split or the two-agent design. No baseline is a plain coding agent.

## 6. Limits

Authors: Archon delays hard obligations. Its proofs use many `have` steps, and one proof block
can have hundreds of lines. Its extracted lemmas are subgoals that are "not generalized". Names
do not follow Mathlib [P, Section 5.2.3].

Reader: three cases, all selected by the authors. The claim about context and persistence has
no number. People examine only the top statement and its definitions.

## 7. Relation to the two anchors

- **Turing Agent** is later by seven months and cites this work [P, `refs_2611.21299.json`].
  Same: Lean projects from informal proofs, parallel agents on independent obligations, and a
  memory that survives context compression. The Archon memory system has the same function as
  the "experience pool". Different: Archon has no Lean check of a split, and it adds the Review
  Agent and Comparator. Archon cites Aristotle and Numina-Lean-Agent, not Hilbert
  [P, References].
- **MathEye** is later, and neither work cites the other. Same: a scaffold with `sorry` at each
  obligation. Different: no graph analysis selects the obligations, and the person gives free
  text, not yes or no.

## 8. What this repository can use

- File ownership is a simple guard against interference: one agent, one file, and a rejected
  result if any other file changes.
- A frozen signature (the protection file) is the same object as an accepted split. The library
  can store a split as a set of frozen signatures.
- The authors say that the extracted lemmas are subgoals and not general lemmas. The library can
  measure this gap, because it labels the moves "generalise" and "interface lemma".
- A stall pattern across sessions is a trigger to split again.
- The README describes a union graph across projects that finds duplicated work. The feature
  graphs can use the same idea.

## 9. Open points and things not read

- How many Lean Agents ran for Anderson, and how often did the structure change?
- Not read: the mathematics (Sections 4.1, 4.2, 5.1), Appendices 7 to 14, and the code itself.
