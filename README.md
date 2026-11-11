# AutoDecompose

Rule-based decomposition of hard theorem-proving problems into Putnam-level
lemmas, each handed to a bounded "student" agent that closes its leaves with
sledgehammer and the Isabelle Pool Server's `fill_sorries`. The aim is a
small-scale, controlled scaling study: the model is held fixed and only the
harness varies, which is the experiment Prove2Me (arXiv 2608.28433) leaves open.

This repository is at the design stage. It holds the research note that
motivates the work and the three literature surveys behind it; the code layout
is not decided yet.

## The question

Does automation at the proof-closing step (the human habit of writing the
argument and calling sledgehammer at the end) save a model reasoning, and does
that saving survive when a problem is split into pieces and the pieces into
subagents? Two quantities are measured, not the solve count alone:

- **tokens per closed leaf**, model fixed, harness varied;
- **decomposition correctness**: whether the lemma statements a rule produces
  are true, well-typed in context and sufficient for the parent.

Putnam-level problems are the *unit* of a student task here, not a benchmark
to beat. The decomposition is to be driven by rules drawn from verification
practice, mathematics and skill files rather than by free generation, so that
it is less random and checkable before any proof effort is spent.

## Where this sits

Three repositories, each with one role:

| Repository | Role |
|---|---|
| `Isabelle-Pool-Server` (IPS) | The prover oracle: warm sessions, the staged `fill_sorries`, sledgehammer, nitpick, the Isabelle symbol table. Makes no model calls. |
| `nearAI_Isabelle` | The student: a minimal upstream-derived agent harness (arms `plain` and `skeleton_forced`), its verifier and run queue. The controlled comparison of per-goal sledgehammer against skeleton-plus-filler runs there. |
| `AutoDecompose` (this repo) | The orchestration above both: statement objects, decomposition rules, sketches that import open children, scheduling of students, the cost model. |

The rule for what goes where: anything that needs Isabelle becomes an IPS
endpoint; anything that needs a model lives here; the student stays the
nearAI_Isabelle harness, imported rather than copied.

## Documents

- `docs/research-pipeline-2026-11-10.md`: the research note. Sections 1-3
  distil what the literature has evidence for (twelve design rules);
  Section 4 proposes a pipeline (plan, blueprint, fill, leaf prover, revise,
  verify) and its cost model; Section 5 lists what would settle the open
  points; Section 6 records the owner's framing and reads Prove2Me's
  statement-object model against it.
- `docs/research/survey-A-systems-2026-11-10.md`: about 45 LLM theorem-proving
  systems, 2022-2026, with budgets and source URLs.
- `docs/research/survey-B-practice-2026-11-10.md`: Isabelle and Lean automation
  practice, agent-loop lessons, prompting evidence, 19 design rules with sources.
- `docs/research/survey-C-frontier-2026-11-10.md`: IMO 2025-26 results,
  PutnamBench state, authors' accounts of what solved the hardest problems,
  costs, Isabelle-specific work.

The experimental evidence the note cites (pass-1 analysis, rep-1 analysis, the
three-run comparison table) stays in `nearAI_Isabelle/docs/`.

## Conventions

- Anything that spends money (a model call on the owner's key) needs the
  owner's explicit go-ahead for that run.
- Never copy an Isabelle symbol table: Unicode and `\<name>` handling goes
  through the IPS translator and `GET /api/v1/symbols`.
- Commits carry a full message, one logical change each; the owner pushes.
