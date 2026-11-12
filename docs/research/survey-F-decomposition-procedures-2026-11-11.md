# F. Decomposition procedures of other harnesses: how they split, check and route subgoals (as of 2026-11-11)

Prepared 2026-11-11 for AutoDecompose, which will decompose hard Isabelle/HOL problems into
Putnam-level lemmas by rules rather than by free generation, and will measure tokens per closed
leaf and decomposition correctness: whether a generated lemma statement is (a) true, (b)
well-typed in context, (c) sufficient for its parent. Surveys A (systems), B (practice) and C
(frontier) report what these systems achieved; this survey reports *how they decompose*, at the
level of steps, prompts, formats and rules, so that rules can be extracted. Headline results are
cited as [A §x], [B §x], [C §x] and not repeated.

Method. (i) Read-only reading of six local repositories; paths are relative to the owner's GitHub
folder (e.g. `isabelle-humanize/flows/isabelle_rlcr/prompts/round0.md`). (ii) arXiv HTML of 25
papers and several project pages, read through a fetch tool that returns extracts; verbatim
quotations are limited to sentences the extract returned, and truncated appendices are named.
(iii) Two PDFs converted with `pdftotext` (Seed-Prover 1.0, arXiv 2507.23726v2, which has no HTML
version; Kaliszyk's SCML 2026 slides). (iv) Raw GitHub files (lean4-skills; the Munkres project's
`CLAUDE.md`). Tags as in [B]: **[P]** read in the primary source during this survey; **[S]**
secondary only, including claims carried over from A-C without re-reading; **[U]** unverified or
not found.

Could not be fetched or found: the AlphaProof Nature article (publisher login redirect; the open
supplement holds hyperparameters only), so AlphaProof's variant kinds rest on [A §2.5]; anything
under the name "LLMemma" (no source found); Delta-Prover's DSL grammar and prompts (figures only);
Seed-Prover 1.5's rubric texts (headings only); the verbatim lemma prompts of Prover Agent and
MechMath (appendices absent from the extracts).

Field key, used in every entry and in Tables 1-2: **(1)** trigger; **(2)** proposer; **(3)**
representation and extraction into a standalone unit; **(4)** granularity control; **(5)**
statement checks before proving (type, disproof, NL judge); **(6)** sufficiency check (parent
compiles with children as `sorry`); **(7)** depth/width limits and restart; **(8)** failure
routing; **(9)** reuse/caching; **(10)** parallelism; **(11)** measured ablation of the
decomposition component, with budget.

---

## 0. Findings in brief

1. **Three families of move, only one of them free.** *Mechanical* moves cut at the failure site
   (APOLLO, MechMath's Sorrifier, ProofAug's FindMCSP, HybridProver, Isabellm); *template/DSL*
   moves fix the shape of what an LLM may emit (Delta-Prover's DSL, Minilang's ten operations,
   Goedel-Architect's `sorry_using` blueprint, Hilbert's `have` sketch, LEAP's "sorry only in new
   lemma statements"); *free* moves turn an NL proof into lemmas (Aristotle, Seed-Prover, Numina,
   Aleph, Prover Agent). Every measured decomposition gain comes from the first two (§8) [P].
2. **Truth is rarely checked before proof effort is spent.** Hilbert, Goedel-Architect, MerLean
   and Seed-Prover 1.5 test a lemma's truth only after the prover fails on it (Hilbert states this
   ordering as a cost saving). The only pre-proof formal truth gates are Goedel-Code-Prover's
   quickcheck factor and Kimina's parallel negation filter; MechMath uses an NL verifier first (§9) [P].
3. **Sufficiency is checked by compilation wherever it is checked at all,** and cheaply: Hilbert
   compiles the sketch with subgoal theorems as `sorry`; Goedel-Code-Prover requires the parent to
   reconstruct from the children; Goedel-Architect, LEAP, Delta-Prover and Prove2Me make the
   compiled sketch the certificate [P]. In Isabelle: a build with children `sorry`.
4. **Granularity is controlled by words, with two exceptions.** Aristotle: lemmas that
   "individually have very short proofs"; Goedel-Architect: "(nearly) trivial once its parent nodes
   are taken as given" [P]. The measurable controls are Goedel-Code-Prover's operator-footprint
   reduction and Seed-Prover 1.5's RL reward (>=3 lemmas, NL score >=0.7) [P]; the local Isabelle
   loop counts connectives in goal text (`isabelle-humanize/flows/isabelle_rlcr/progress.py`) [P].
5. **Shallow beats deep; global replanning beats recursion on the failing node.** Hilbert 98.36 %
   at depth 2, 98.7 % at depth 3 (cap 5); Seed-Prover 1.5 depth 4 then restart; Prover Agent depth
   1; Goedel-Architect, MerLean and Aristotle revise the whole plan and keep proved nodes [P].
6. **Every system that names failure causes uses two labels:** statement wrong, or lemma too
   coarse/hard (Goedel-Architect `STATEMENT_WRONG`/`PROOF_TOO_HARD`; Aristotle; MerLean's math
   then decomposition check; Magenta `math_error`/`code_error`, default `code_error`) [P].
7. **Measured ablations of decomposition are few.** MechMath 4/4 vs 3/4 vs 0/4 at 128 calls;
   ProofEvolve 32/60 vs 11/60 without decomposition; Goedel-Code-Prover, one model, 20.1 % vs
   44.9 % (code verification); Hilbert's depth curve; LEAP DAG vs tree +10.0/+16.7 points; Magenta's
   statement judge, false certificates 45.5 % to 0 % [P]. Delta-Prover's 83 subproblems is one problem.
8. **The humanize lineage enforces no proof decomposition.** Its 72 gates check the form of
   artefacts, not content; the Isabelle port puts "decompose: prove a helper `lemma` above the
   target" last on a four-step ladder and forbids `sorry` in the file; its B5 solve was still
   driven by self-decomposition (iff split, then residue cases) [P].
9. **The no-enforced-decomposition control asks for decomposition.** h1's prompt: "break it into
   lemmas, sketch the structure with sorry to read the subgoals, prove the pieces, and iterate".
   h1 tests suggested versus enforced decomposition, not decomposition versus none [P].
10. **Inside a decomposition nobody checks more than truth and sufficiency.** Faithfulness is
    checked only for top-level statements (Magenta, Prove2Me read-back, Rocq-MCP's A3 loophole);
    extraction fidelity only by Hilbert's assembly compile and MechMath's NL verifier [P].

---

## 1. Local harnesses (read directly)

### 1.1 humanize (v1 plugin, humanize2 `hmz`, Humanfia paper)

*What it is.* humanize2 is a flow engine that drives agent CLIs; only three flows are builtin
(`chat`, `ralph_loop`, `stateful_ralph`; `humanize2/src/hmz/flows/builtin/`), the rest live in the
official flowverse (`humanize2/docs/flows/index.md`) [P]. A copy of the flowverse is at
`isabelle-humanize/.m0/flowverse-ref/`.

*How a task is split* [P, `.../flows/humanize1/_humanize1/prompts.py`]. `gen-plan` writes a plan
whose goal tracker has an IMMUTABLE Ultimate Goal and Acceptance Criteria ("define 3-7 specific,
testable criteria") and a task table where each task carries a routing tag, `coding` (builder
executes) or `analyze` ("a question rather than work", answered by the reviewer). Each round
opens with a contract: "One mainline objective", "Target ACs (1-2 ACs only)", blocking side issues
in scope, queued ones out. With agent teams the leader must "Break work into independent tasks
that can be worked on in parallel without file conflicts ... Aim for 5-6 tasks per teammate".
`parallel_flame_chase` has a coordinator plan three lanes once; lane 1 alone writes the source,
lanes 2-3 work in snapshots and publish hashed artefacts (`humanize2/docs/flows/parallel-flame-chase.md`).

*Gates and drift.* v1's Stop hook runs a 13-stage gate pipeline, cheapest first (state schema,
branch, plan integrity, clean tree, >2000-line files, summary and contract present, lesson
delta, 42-round cap) [S, `isabelle-humanize/humanize-analysis(temp).md`, an analysis of the v1
code]. The Humanfia paper (arXiv 2610.08900) counts 72 gates in ten categories: state integrity
12, plan and scope protection 11, round isolation 10, git hygiene 9, review protocol 7, session
hygiene 6, artefact presence 5, lesson memory 5, environment precondition 4, completion
discipline 3; by the paper's account the gates check the presence and form of artefacts, not
their content, which is left to the reviewer [P, https://arxiv.org/html/2610.08900]. Drift: the reviewer must print ADVANCED / STALLED / REGRESSED;
two stalls bring a replan prompt, three stop the loop; every fifth round is a full alignment
review [P].

*Proof decomposition.* None is enforced; for formal proofs "the Lean kernel and a
statement-preservation check run before the reviewer" [P]. No ablation exists: "no public study
runs the same builder with and without its reviewer"; on the PutnamBench rerun 86 of 98 problems
passed on the first turn [P].

### 1.2 isabelle-humanize (`flows/isabelle_rlcr`)

A port of the RLCR loop to Isabelle: builder and reviewer agents with the IsabelleGym MCP; the
arbiter (`isabelle build`, no `sorry`/`oops`, target present) is the only termination authority
(`isabelle-humanize/README.md`) [P].

*Decomposition rules in the prompts* [P, `flows/isabelle_rlcr/prompts/`]. `round0.md` rule 1:
"NEVER leave `sorry` or `oops` anywhere in the file. A round that contains one is rejected
outright". Rule 5, the escalation ladder "when a step fails twice on the same subgoal": (a)
`isabelle_goal` at the failing line; (b) sledgehammer, paste verbatim; (c) `multi_attempt` with
2-4 candidates; "(d) decompose: prove a helper `lemma` above the target and use it." Rule 6: "if
you have spent two edits on the same subgoal without closing it, the next action is sledgehammer".
Rule 8: on timeout, larger sledgehammer budget, simpler method, "or decompose the goal".
`drift_replan.md` (after two stalls) gives a menu: "decompose the failing goal into helper
`lemma`s above the target", `multi_attempt` with "genuinely different" candidates, sledgehammer,
"or restructure the proof (induction on a different variable, a different rule, a case split)".

*Mechanical progress signal* [P, `progress.py`]. A round is PROGRESS if the open-goal count falls,
or equal count with lower "connective weight" (count of `⋀ ⟹ ∧ ⟶ ∀ ∃ λ` in goal text), or new
discharged helper lemmas; STAGNATION if the goal set is identical; REGRESSION if goals increase.
Gates (`gates.py`): branch consistency, IMMUTABLE section hash, clean tree, 2000-line file cap.

*Results* [P, `runs/README.md`, DeepSeek-V4-Pro both seats]: Putnam 2023 A1 solved in 2 rounds
($3.28); B5 in 5 rounds ($14.72; one REGRESSED round, one replan); IMO 2026 P1 in round 0 ($5.15,
1 059 lines). The final theories contain 21 (A1, 311 lines), 76 (B5, 2 644 lines) and 25 (P1)
`lemma`/`theorem` declarations by grep, i.e. heavy self-decomposition. B5's retrospective:
"Decomposition was the engine: splitting the biconditional into a forward exclusion and a backward
construction, then into per-residue cases" (`runs/putnam_2023_b5-rlcr-deepseek/methodology-analysis.md`).
The rlcr-vs-solo ablation has been run only on three smoke problems (`STATUS.md`).

### 1.3 Builder/reviewer protocol (`Research/agent-loops/builder-reviewer`)

A software loop, not a prover, but two rules transfer [P, `README.md`, `LESSONS.md`,
`BUILDER_PROMPT.md`]: work is split into stage commits, "Split a stage into two commits only if one
of them would otherwise exceed about 600 changed lines"; and the reviewer re-runs every gate
itself, because "Pasted output is a claim, not evidence" (three real defects were found only that
way in 13 commits / 15 reviews). One objection round, then the builder decides; declining is
recorded, never silent.

### 1.4 Shipped skill files

- **PIDE MCP skills** (`isabelle-pide-mcp/.claude/skills/`, origin `kappelmann/isabelle-pide-mcp`,
  four skills) [P]; the public `kappelmann/isabelle-pide-ai` (formerly "PIDE MCP") lists three
  skills whose text was not read. `isabelle-formalization/SKILL.md`, "Incremental Proof
  Development": "1. Write the right statement with a `sorry` proof. 2. Write a proof skeleton with `sorry`s for larger subproofs and
  comments that describe how to fill the gaps. 3. Fill the gaps iteratively one-by-one ...";
  encouraged: "Add intermediate lemmas (possibly with `sorry`) rather than getting stuck inside a
  large proof"; anti-patterns: "Leaving large sorried proof blocks if you are not convinced you can
  fill in the details" and "Changing the statement to something weaker unless clearly justified.
  Generalizations are fine if they can actually be instantiated". `isabelle-proof-development`:
  `try0` first (<5 s), then sledgehammer (<30 s), "almost always cheaper than guessing";
  structured Isar when automation is brittle. `pide-mcp`: a `sorry` is reported as `bad`, not an
  error; "A clean theory has 0 bad commands AND 0 errors AND 0 failures."
- **Isabelle-MCP** (`xqyww123/Isabelle-MCP`): no decomposition guidance; its docs define tool
  semantics only (`docs/TECH_NOTE.md`: `sorry` surfaces only as `background_bad` decoration) [P].
- **AutoCorrode** [P]. `iq/iq_guidance.md`: "When you work on an Isar proof, work top-down: First,
  establish the rough structure, using `sorry` to temporarily axiomatize core steps. Then, fill in
  those `sorry``s one at a time; if they are complex, hoist them out as separate lemmas or state
  subproofs via `proof -`." `design-documents/05-agent-generated-isabelle-style.md` is the opposite
  pole, for text inserted for humans: "Avoid placeholders (`sorry`, `oops`) unless explicitly
  requested." `CLAUDE.md`: `QUICK_AND_DIRTY=1 make build` accepts `sorry` (`-o quick_and_dirty`),
  and heavy theories split into `Foo.thy` and `Foo_Lemmas.thy`.

---

## 2. Isabelle harnesses

### 2.1 Draft, Sketch, Prove (DSP, 2022) [A §1.2] [P, https://ar5iv.labs.arxiv.org/html/2210.12283]
1. An informal draft (human or LLM). 2. A declarative Isar sketch in which open conjectures are
marked `<⋯>` and segments of the draft are copied as `(* ... *)` comments before their formal
step (e.g. `have c5: "0 ≤ 28a^2 - 10a + (25/28)"` ... `show ?thesis using c5 <⋯>`). 3. Each gap:
eleven tactics at 10 s each, then Sledgehammer 120 s; one open gap fails the attempt. No
recursion, no repair; diversity by resampling (100 attempts). Ablations as in [B §C2]; the
authors' hypothesis that human proofs "leave gaps between conjectures that are too difficult for
automated provers" is the granularity problem in its first statement.

### 2.2 POETRY (2024) [A §1.7] [P, https://arxiv.org/html/2405.14414]
*Representation* is learned: `ExtractProofSketch` walks training proofs by proof level and, when
the next line is deeper, emits the step with `sorry` appended ("Replace the next level proof with
sorry"); the model learns to emit `have "..." sorry` jointly. *Search*: best-first per level; a
complete sketch pauses the level and recursion enters the last unproved `sorry`. Node states OPEN,
FAILED, PROVED, HALF-PROVED; a HALF-PROVED node reverts to OPEN if its sub-root fails. Budgets:
600 s global, 10 s per step, 120 s per non-first level, 32 samples, 128 expansions, depth 10.
*Ablation*: none isolates recursion; against the same model trained without `sorry`, +3.9 miniF2F
average, multi-level PISA 13.6 vs 11.1 %; sketches average 3.3 steps against 12.7.

### 2.3 ProofAug (2025) [A §1.9] [P, https://arxiv.org/html/2501.18310]
*MCSP*: a semi-proof is compatible with the proposal if "each sorry in y matches a proof…qed block
or a by clause" of it; the maximal one is unique. *FindMCSP*: run steps in order; a failed step in
`prove` mode becomes `sorry`; a failure in any other mode empties the innermost `proof…qed` block
and closes it with `sorry`; a failure outside every block returns Null. *Fail fine, retry coarse*:
at each `sorry` try `<ATP>` (eight built-in methods at 10 s, then Sledgehammer 120 s); on failure
"we can rule out the possibility that the final proof contains the innermost proof…qed block in
which this sorry lives and replace the block with sorry", until the proof closes or degrades to a
single `sorry` on the theorem. *ERP*: on an `<ATP>` failure the LLM gets the informal draft, the
verified prefix and the proof state, and must reach the expected next state. *Ablation*
(deepseek-math-7b, miniF2F-test): DSP 28.7/40.6/49.2 % against ProofAug 36.5/44.7/52.5 % at
budgets 1/10/100; ERP +1.6 points at a 500-query cap. FindMCSP and coarse retry are not separated.

### 2.4 HybridProver (2025) [A §1.10] [P, v1 and current HTML]
Trigger: none of n = 128 whole proofs checks. v1: "we substitute all proof tactics for each
subgoal with the keyword sorry", sketches that fail the check are discarded, each hole gets
tactic-model candidates plus Sledgehammer 30 s with eleven heuristics; tactic-only 34.8 %, plus
sketch refinement 56.1 %, full 59.4 % (https://arxiv.org/html/2505.15740v1). The current version
changes the rule: each subgoal is checked with the others `sorry`ed, "Correct subgoal proofs are
preserved, while failed ones are replaced with sorry"; backtracking over alternative tactics;
whole-proof 45.9 %, tactic + sketch refinement 71.3 %, full 73.8 %; three-shot prompting: "no
performance gain" (https://arxiv.org/html/2505.15740). [B §C2] quotes the v1 numbers.

### 2.5 Isabelle/Minilang (2025, OOPSLA 2026) [C §5] [P, https://arxiv.org/html/2507.18885]
A ten-operation proof language whose operations *are* a decomposition vocabulary:

| Operation | Obligations it creates |
|---|---|
| `HAVE props` | the props G1..Gn, then the goal with them as facts |
| `CONSIDER P1 \| … \| Pn` | exhaustiveness `P1 ∨ … ∨ Pn`, plus one goal per case (n+1) |
| `CONSIDER ∃x. P x` | existence, plus the goal with x bound (2) |
| `RULE fact` | the premises H1..Hn of `H1 ⟶ … ⟶ G` |
| `CHOOSE term` | `G(y)` for the witness y |
| `SIMPLIFY facts?` | one simplified goal |
| `CASE_SPLIT`, `INDUCT` | as Isabelle `cases`, `induct` |
| `END`, `NEXT` | none: close the goal by "Sledgehammer*" (`auto`, `clarsimp` fallback, `fastforce` in parallel, then Sledgehammer) |

`INTRO` is a "necessary technical command" for context, *not* one of the ten (C §5 lists it among
them; `CONSIDER` counts twice). A rule-based translator covers about 85 % of ~340 K Isar proofs;
Sledgehammer* adds "at least 6 percentage points"; pass@1 69.1 % on PISA.

### 2.6 Isabellm (2026) [A §1.12] [P, https://arxiv.org/html/2601.04653]
The planner samples whole Isar outlines; each maximal `sorry` span is a hole whose goal is read
from the printed state. Holes are filled by a shallow stepwise search; a fill that is only
`apply` steps is inserted followed by a new `sorry` and counts as partial progress.
`OpenMinimalSorries` re-sorries failing lines after a bad edit. Repair is a CEGIS ladder anchored
at the earliest failing line: stage 1 regenerates the enclosing `have/show/obtain` micro-block,
stage 2 a `case` block or `proof…qed` subproof, stage 3 the whole proof; c1 = 2 failures before
stage 2, c2 = 3 before stage 3; failed blocks are fingerprinted (SHA1) and banned. Quickcheck and
Nitpick supply only "counterexample-oriented hints". The author: repair stages "rarely succeed
beyond trivial cases"; most successes come from the first outline or the stepwise prover. No
numbers.

### 2.7 Munkres topology in Isabelle (2026) [A §1.11] [P, https://arxiv.org/html/2604.07455]
Kaliszyk's slides list the method as six steps: "1 Write the theorem statement and proof skeleton
2 Leave every nontrivial step as sorry 3 Build only for structural correctness 4 Run sledgehammer
in bulk 5 Replace placeholders with the fastest reconstructed proofs 6 Split stubborn goals into
smaller have steps" [P, SCML 2026 slides]. The paper adds: sledgehammer annotations at timeout 10
are collected in one `process_theories` pass (parallel execution is not stated; [A §1.11] says it
is); an "ABSOLUTE RULE" for sorry-first was added after repeated "tactic explosion"; new code may
contain no tactic at all ("not by fast, not by linarith, not by simp, not by (rule ...), not even
done"); tools `eval_at` (profiling) and `desorry`. The `CLAUDE.md` now on the repository's main
branch is an earlier "Rules for Working on the Isabelle/HOL Formalization (Top1)" without
sledgehammer rules; its decomposition lines: "Add intermediate lemmas with `sorry` rather than
getting stuck inside a large proof", "Replace one `sorry` at a time with real proofs, keeping the
build green", and on a build timeout "Replace the last automation step by `sorry`"
(https://raw.githubusercontent.com/JUrban/isa_top_autoform1/main/CLAUDE.md) [P]. Granularity is
observed, not prescribed: 611 helper lemmas for 195 Munkres results, lemmas of 2-5 `have` steps,
median direct proof ~25 lines; 4 of 129 human interventions were for "cherry-picking easy goals".

### 2.8 LLMemma [U]
Cited in [C §5] from ResearchGate (Isar skeleton, holes closed by Sledgehammer, fixed tactics, a
fact-closer or LLM decomposition). No source under this name was found on 2026-11-11.

---

## 3. Mechanical repair harnesses (Lean)

### 3.1 APOLLO (2025) [A §4.1] [P, https://arxiv.org/html/2505.05758]
1. Syntax Refiner: regex rules (e.g. "from by" to ":= by", Lean 3 blocks); full list unpublished.
2. Sorrifier: parse into a tree of nested blocks; compile; per failure apply line removal, block
removal, or "insert sorry" (block compiles but leaves goals); loop until the file compiles; a
malformed theorem statement discards the proof. 3. AutoSolver: `hint` (only full closures), then
`nlinarith`, `norm_num`, `norm_cast`, `ring_nf`, `simp`, `simp_all`, wrapped in `try`. 4. Each
remaining `sorry` becomes a lemma with its local context ("queries the REPL for the exact goal
statements"; `pp` options make types explicit) and re-enters the pipeline; "if r_current > r then
return sorry". 5. Assembler splices and rejects any `sorry`/`admit`. *Ablation*: o4-mini 7.0 %
alone, 46.7 % with all three components, no pair above 20.5 %; Goedel-Prover-SFT at r = 6 reaches
65.6 % (~179 K tokens) against 64.7 % at K = 25 600; Sorrifier and Assembler were not ablated.

### 3.2 MechMath Sorrifier (2026) [C §3] [P, https://arxiv.org/html/2603.24465]
Trigger: first attempt plus up to four compiler-feedback repairs fail. Algorithm 1: (a)
`CleanUpRedundantCode` removes statements after an existing `sorry`; (b) compile; (c)
`SelectPrimaryError` picks one error; (d) `FindShortestBlock` among `have`/`calc` blocks overlapping
its line; (e) no block: truncate at the line and append `sorry`; `calc`/`choose`: replace the whole
block; `have`/`replace`: replace only the proof body, keeping the statement; (f) unchanged code
returns failure; (g) recompile, which "instantly removes any downstream cascading errors".
*Extraction*: at each `sorry` the Reasoner keeps only relevant hypotheses (the example keeps
`(b c : Nat) (h2 : b = c)`, drops `a`, `h1`); Lean checks syntax; a Verifier checks "extraction
correctness" (does the subgoal reflect the intended step) and "logical soundness", "usually
checked by whether there are obvious counterexamples or essential hypotheses missing"; failures go
back for re-extraction. Each subgoal recurses through the whole pipeline; a proved one is spliced
in as `apply <lemma> ...`. *No-progress rule*: a nested subgoal identical to its parent reverts to
a formal attempt and, after a fixed number, stops. App. E.3: "Global regeneration is strictly
treated as a tactical fallback"; an unsound subgoal raises `LOGIC_ERROR` and "the agent is
explicitly prohibited from attempting futile local repairs". *Ablation* (128 calls, A1-A4):
discard-and-retry 0/4; iterative repair 3/4 (A4 126 calls, 518 min, $55.70); Sorrifier 4/4 (A4 88
calls, 114 min, $19.90). Without the informal stage A2 fails and A4 needs 44 nodes ($20.5) instead
of 10 ($10.5).

### 3.3 Delta-Prover (2025) [A §4.2] [P, https://arxiv.org/html/2507.15225]
Trigger: iterative repair (m rounds x n repairs) fails. The LLM writes a sketch in a DSL built as
"an additional monad layer ... built upon TacticM" (PlayM): `suppose` adds hypotheses of any type
without their values being given; `define` introduces an expression with inferred type;
`show ... by` (ShowBy) poses a subgoal and records the proof it gets; `conclude` assembles the
recorded subproofs via the delaborator into one proof of the original. Elaborating the sketch
yields either a kernel error (fed back) or the subproblem list; "illegal formal draft" otherwise.
Unsolved subproblems are returned and the sketch regenerated, up to l_max (value not given).
IMO 2019 P1: repair alone failed at 1 024 calls; 83 subproblems at ~4 calls each. Stated failure
mode: LLMs cannot estimate subproblem difficulty, so one subproblem becomes the bottleneck.

---

## 4. Trained provers with a decomposition stage

### 4.1 DeepSeek-Prover-V2 (2025) [A §3.5] [P, https://arxiv.org/html/2504.21801]
DeepSeek-V3 is asked to "generate only a high-level proof sketch with the details omitted",
ending in a Lean theorem of `have ... := by sorry` steps. Each subgoal becomes a lemma in one of two
forms: (a) the subgoal replaces the goal; (b) the preceding subgoals are added as premises (used
for recursion). A 7B prover solves subgoals; data are kept only when all are solved. Early RL adds
a consistency reward that "penalizes the structural misalignment" between the proof and the
decomposed `have`s. No ablation of either. Public prompt asks for "key ideas, intermediate lemmas,
and proof structures" before the code (GitHub README) [P].

### 4.2 Kimina-Prover TTRL search (2025) [A §3.4] [P, https://huggingface.co/blog/AI-MO/kimina-prover]
"whenever a theorem or lemma fails to find a proof after N = 128 attempts, new candidate
sublemmas are generated" (also continuously in parallel); a general LLM proposes in NL,
Kimina-Autoformalizer-7B formalises. *Negation filtering*: try to prove each lemma's negation; if
provable it is "immediately discarded". *Pool*: per-scope (the problem and each lemma, which gives
recursion); a lemma below utilisation 0.10 after 50 insertions is pruned; each iteration builds
K = 10 prompt variants per problem (60 % top lemmas, 40 % top plus 1-4 random). Utilisation settles
at 30-40 %; "a large portion of the current sampling is spent on proving unhelpful or redundant
lemmas". No component ablation.

### 4.3 Seed-Prover 1.0 (2025) [A §3.7] [P, pdftotext of arXiv 2507.23726v2]
*Lemma style*: "we first require the model to generate some useful lemmas--each introduced by the
keyword lemma--before generating the main proof"; lemmas "can be compiled independently, stored
independently, and combined freely". Per problem a lemma pool stores statements, names, proofs,
difficulties, dependencies. *Proposer*: input "an unsolved problem and, optionally, some already
proved lemmas", output "10-50 candidate conjectures about properties of the problem", explicitly
not a solution attempt (e.g. for functional equations: "injective, surjective, bijective,
monotonic, or periodic"). *Medium*: inner refinement on failed lemmas at 8 x 8; any proved lemma is
written back into the outer prompt. *Heavy*: 5 000 conjectures; each proved or disproved with the
light setting; proved ones join the pool; more conjectures are proposed from proved lemmas; lemmas
scored by proof rate ("lemmas with low proof rate are often crucial"), LLM-judged relevance and
proof length; "Unrelated lemmas or lemmas with short proof lengths are removed"; hundreds of the
top lemmas go to a medium run. No ablation of the pool.

### 4.4 Seed-Prover 1.5 (2025) [A §3.8] [P, https://arxiv.org/html/2512.17260]
NL prover writes a lemma-style proof; the sketch model emits a Lean sketch with lemmas as `sorry`
splitting the goal into N independent subgoals; each lemma gets the agentic prover at Pass@3 x 3
(64 K tokens, 28 tool calls per attempt) to prove *or disprove*; unproved lemmas recurse through
NL proof and sketch; "If a lemma is disproved, the system reverts to the Sketch Model to refine the
sketch." Depth 4; at the cap, proved lemmas are put in context and the search restarts (effective
depth 8). *Sketch reward* (RL): an NL prover checks each lemma and any invalid lemma scores -1
("using the natural language prover to disprove is cheaper than using a theorem prover"); an LLM
judge scores alignment with the NL proof, decomposition granularity, difficulty reduction and
"Lean junk value analysis"; R = +1 only if >=3 lemmas, Lean score >=0 and NL score >=0.7. Verified
lemmas are cached. No ablation isolates the sketch model.

### 4.5 AlphaProof test-time RL (2024-25) [A §2.5] [S]
For an unsolved target, a variant generator builds a curriculum of Lean-validated variants
(simplifications, generalisations, decompositions; up to 15 evolutionary iterations) and RL runs on
it; the tree search treats tactics producing several subgoals as AND nodes (value = min over
subgoals). The Methods text could not be read (paywall); variant kinds are as reported in [A].

### 4.6 Goedel-Code-Prover (2026; Lean code verification) [A §4.7] [P, https://arxiv.org/html/2603.19329]
One 8B policy proposes lemmas L1..Lk and a parent proof term invoking each. *Decomposition score*:
operator footprint d(G) = number of logical and domain operators in the goal's AST; validity
v = 1_proof(L1..Lk; G) · Π_i 1_qc(L_i) (the parent must reconstruct from the children; no child
may have a quickcheck counterexample); d̄ = T·log Σ_i exp(d(L_i)/T) (a soft max); reduction
r = max(1 − d̄/d(G), 0); S = r·v. S is the GRPO reward for decomposition. Inference picks the open
goal of largest footprint, decomposes it, and continues up to 128 iterations or 32 open lemmas;
completion runs 128 refinements per lemma. *Ablation* (Verina, pass@32): whole-proof 19.6 %;
GPT-5.2-Pro decomposer + Gemini completer 54.4 %; own decomposer + Gemini 58.2 %; own both 68.8 %;
GPT-OSS-120B whole-proof 20.1 % vs hierarchical 44.9 %.

---

## 5. Agentic plan, blueprint and sketch harnesses

### 5.1 Aristotle (2025) [A §4.5] [P, https://arxiv.org/html/2510.01346v1]
1. Informal proof. 2. Restructure it "as a sequence of lemmas which build on each other, and which
individually have very short proofs" (the wording in [B §C2] and our README, "each meant to have a
very short proof", is a paraphrase). 3. Formalise lemma statements; REPL errors returned for
correction. 4. Search replaces every `sorry` in the block, lemmas before the theorem; goals from an
explicit `sorry` may not contain metavariables. 5. On failure the list is annotated "proved or
unproved" and the model is asked to revise, "keeping the proved lemmas but complementing them with
a new collection of additional lemmas", told to consider both causes: "an unworkable strategy
which needs to be fundamentally altered" or not "broken down into sufficiently granular lemmas".
No ablation. The quantifier-error anecdote of [B §C2] is, in the text, a confusion of "strictly
decreasing", "weakly decreasing" and "decreasing at some point".

### 5.2 Hilbert (2025-26) [A §4.4] [P, https://arxiv.org/html/2509.22819]
1. Four direct prover attempts. 2. Retrieval: five queries, top-5 each. 3. Sketch (up to 4
attempts with compiler feedback): "Break complex reasoning into logical sub-goals using `have`
statements", "Use `sorry` for all subgoal proofs"; each subgoal is to be simpler than the problem
and provable with one key theorem or a few tactics (paraphrase of the prompt); no `sorry` in the
main body. 4. Extraction: "From this proof sketch, extract any
missing proofs (specified with `sorry`) as independent subgoals (theorems)", "Do NOT change the
conclusion", same names as the `have`s, context from earlier subgoals; the count of `have`s is
compared with extracted theorems and missing ones re-requested; each is syntax-checked. 5.
Assembly: "ALWAYS use the supplied theorems"; sketch plus theorems compiled with subgoal proofs
`sorry`, errors fed back. 6. Per subgoal: four prover attempts; then the correctness check, *only
after the prover fails*: "evaluate whether the given mathematical theorem statement is
mathematically correct" (YES/NO with a fix; "Do NOT flag general results or helper lemmas that are
true independent of the given premises"); a NO returns to sketch refinement; common faults are
missing hypotheses and natural-number truncation. Then a shallow solve (<=30-line proof, 6
correction passes, 6 informal passes), then recursion; D = 5. Unproved leftovers restart the
decomposition. Async pool with "First Failure" mode for correctness checks. *Ablation*
(miniF2F): D = 0 75 %, D = 2 98.36 %, D = 3 98.7 %; retrieval off 97.9 % and reasoner calls 548 to
862.

### 5.3 Prover Agent (2025-26) [A §4.3] [P, https://arxiv.org/html/2506.19923]
Trigger: 50 direct + 50 refinement samples fail. An 8B informal model writes three lemmas of four
kinds: subgoals, special cases (e.g. n = 3), potentially useful facts derived from the
assumptions, hypothesis-driven conjectures (the last named only in the contributions list). A formaliser writes statements only, regenerated until
they parse; no disproof check; unprovable lemmas are dropped; proved ones go into the final
synthesis context. Each lemma: 10 + 10 samples; depth 1; miniF2F total 260 samples. Effect:
Goedel-Prover-V2 85.7 % to 86.5 % (miniF2F), PutnamBench 20 to 25 / 659 (40 to 110 samples). Of
the lemmas in its case-study appendix: 41.7 % used as subgoals, 25 % special cases, 25 %
"technique-inducing", 8.3 % failed.

### 5.4 Goedel-Architect (2026) [A §4.7, C §3] [P, https://arxiv.org/html/2606.06468]
*Blueprint format* (App. C.1), one Lean file:
```lean
@[blueprint
  (statement := /-- closed, typed, standalone natural language proposition -/)
  (proof := /-- complete natural language sketch citing parent declarations by backticked name -/)]
lemma|theorem name (binders) : conclusion := by sorry_using [p1, p2, ...]
```
"Each Lemma should be (nearly) trivial once its parent nodes are taken as given", at most 1-2 new
logical ideas beyond its dependencies; `sorry_using []` for leaves. Checks before proving: parses,
every node well-typed, graph acyclic, all nodes reachable from the target, target signature
verbatim, no `axiom`, no dead nodes; up to 8 retries. *Proving*: each lemma in parallel, seeing only
itself and its declared parents (65 536 tokens, 4 retries per node); the prover may "register a
proof of the negated statement in lieu of the original". *Refinement* (C.3): `## Diagnosis` is
exactly `STATEMENT_WRONG` (false under its hypotheses: "Fix the statement", or drop if
"structurally unfixable") or `PROOF_TOO_HARD` (add parents from `## Suggested Fix`); "Leave
`-- PROVED` nodes untouched unless a downstream revision forces a signature change"; "Do NOT replace
any `sorry_using` with an actual proof". Up to 8 (miniF2F) or 16 (PutnamBench) iterations. Why
global: recursive approaches "can inefficiently loop on dead-end strategies". *Numbers*: initial
blueprint 200/672, refined 508 by iteration 16, 597 with NL seeding at pass@4; negations on 292/672
problems, 1-4 nodes each.

### 5.5 Aleph Prover (2025-26) [A §4.7] [P, https://logicalintelligence.com/blog/aleph-solves-putnambench]
Only the outline is published: "Breaking down the original problem statement into subproblems";
proving them in Lean; "Modifying the high-level proof plan, depending on which subproblems are
successfully proved"; "recursive and interactive state management system with highly parallel Lean
verification calls". On the 500-problem run, about 15 proved lemmas per solution (max 62), 1 841
Lean checks per problem (max 37 061), $23.39 average (https://logicalintelligence.com/aleph-prover.html).

### 5.6 Numina-Lean-Agent (2026) [A §4.7, C §3] [P, https://arxiv.org/html/2601.14027v1]
A blueprint is a "design-document-style artifact": definitions, curated lemmas, a final theorem
that mostly composes them, with `\uses{...}` edges giving a DAG and the proving order. Revised on
Lean feedback when a step proves incorrect, underspecified or at the wrong granularity (strengthen
assumptions, rephrase for Lean interfaces, insert missing lemmas); the agent sometimes split finer
than the blueprint. `discuss_partner` consults other LLMs at bottlenecks. A stuck lemma (A5) was
isolated in a subagent that received a GPT-5.2 informal hint; the stated reason is that "very long
contexts degrade instruction-following". No threshold, prompt or skill text is published.

### 5.7 LEAP (2026) [A §4.7] [P, https://arxiv.org/html/2606.03303]
"If direct proving fails, LEAP shifts to decomposition" (direct proving: up to 20 compiler-feedback
revisions). Informal blueprint, then a Lean sketch whose main body is sorry-free: "sorry
placeholders are permitted only in the newly proposed lemma statements". Accepted sketches are AND
nodes, lemmas OR nodes of a DAG; the writer checks acyclicity; anticipatory lemmas may be added.
An LLM reviewer judges whether subgoals are relevant, easier and offer "a plausible route" (no
truth check). Search: DFS with backtracking; shared lemmas memoised. *Ablation*: Lean-IMO-Bench
Basic/Advanced, naive tree 73.3/40.0 %, DAG 83.3/56.7 %; without the reviewer Putnam 2025 A5 fails
"even after eight rollout attempts", with it two; calls per Putnam problem 46 (B2) to 3.0 k (A5).

### 5.8 MerLean-Prover (2026) [A §4.7] [P, https://arxiv.org/html/2605.26959]
The plan, "the only global object shared across invocations", is a topologically sorted list of
nodes (informal statement, sketch, dependencies, status); the target is anchored as the original
declaration with `sorry`. A Lean agent writes one node per file importing its dependencies. A
read-only Check agent returns one boolean: math ("mathematically correct as stated"),
decomposition ("whether a stuck statement should be split") or faithfulness. Routing: stuck node →
math check; if sound → decomposition check; "no" retries the node, "yes" asks the Planning agent
for a plan diff; an accepted diff invalidates downstream nodes and the walk restarts. 4 h per
problem; ten FormalQualBench solves cost $1 183.45 ($118.35 and 1 h 59 min each). No ablation.

### 5.9 ProofEvolve (2026) [A §4.7] [P, https://arxiv.org/html/2608.26334]
Nodes are tactic states (Γ ⊢ g); a hyperedge is a Lean-elaborated constructor whose children must
all close (AND), alternatives are OR. Operators: Decompose (a checked closing term, or a
constructor with typed obligations whose holes must become explicit child states), Recombine (apply a library schema), Repair (only after a rejection).
A schema is a prenex lemma ∀x, A1 → … → Am → C with a kernel-checked proof, abstracted from a
closed sub-DAG; instantiation unifies C with the goal and turns unmet premises into child states.
An archive keeps one DAG per descriptor cell (binned depth, dominant tactic family, schema region).
Per-target 1x profile: 12 model calls, 60 Lean calls, 400 K tokens, 1 800 s. *Ablation*
(IMO-LeanProofBench, 60 problems): 32 full, 11 without decomposition, 14 without recombination, 9
without repair; growing vs reset library 19.8 vs 7.3 % (synthetic).

### 5.10 Magenta (2026) [A §4.7] [P, https://arxiv.org/html/2609.11319]
No lemma decomposition: the informal chain is the plan. Two judges matter here. The statement
judge "Judge whether the candidate Lean 4 theorem statement faithfully formalizes the supplied
question" (domains, hypotheses, quantifiers, constraints, answer) returns JSON verdict, rationale,
mismatch details; it sees only statements that elaborate. The error judge routes a failed proof:
`math_error` only when "the supplied mathematical reasoning or claimed answer is itself false or
insufficient", everything else `code_error` (local repair); "When evidence is ambiguous, return
code_error." Budgets: T = 32 reasoner attempts, M = 512 statements, K = 4 096 proofs. *Ablation*
(AIME 2026): statement judge on, verified-and-correct 63.3 % and false-certificate rate 0 %; off,
20.0 % and 45.5 %. The error judge's ablation is announced but not reported.

### 5.11 Rocq-MCP, Putnam 2025 (2026) [B §B3] [P, https://arxiv.org/html/2603.20405]
Claude Code orchestrated four teams of three problems; 141 subagents, strictly two levels, each
prompted with multi-paragraph proof strategies written by the orchestrator. Roles by
inferred prompt: Lemma Prover 55 (738 M tokens), Bug Fixer 36, General 21, Verifier 15, Proof
Completer 13. Skeletons with `Admitted` stubs; "compile-first, interactive-fallback". Statement
check only at the end (`rocq_verify` applies the module's theorem to the original; axiom
whitelist); A3 passed vacuously through a partial-function encoding and was fixed by a human.
B5 used 82+ subagents (46 h), B6 91 and failed; no early-termination rule.

### 5.12 Prove2Me (2026) [P, https://arxiv.org/html/2608.28433]
Statement objects (description, preamble, Lean statement that must "terminate in a := by sorry
placeholder") are immutable. "We call a proof that imports other theorems a proof-sketch"; Property
1: "Theorem 4.1 is verified if all imported child lemmas are verified." Milestones are
"lemma-level sub-targets curated by the mission's captain", usually transcribed from the source, so
"independent attempts converge on one canonical statement"; agents "reuse an existing theorem where
one exists". Disproof is a submission of type ¬(statement): a disproof of an imported lemma led to a
corrected `gotsman_linial_with_zero`. Read-back: an auditor agent sees the Lean but not the source
and writes LaTeX; a human compares the two.

---

## 6. Skill files, and the no-enforced-decomposition control

### 6.1 Trail of Bits, "Writing Lean proofs" [B §B3] [P, https://trailofbits.com/skills/writing-lean-proofs/]
"design top-down, prove bottom-up"; "State the target theorem and the lemmas it needs, all with
`:= sorry`, and make the file compile. Each `sorry` is now an independent work unit"; inside a
proof "lay out the `have`/`suffices`/`calc` skeleton with `sorry` justifications". The extraction
ladder: a repeated sub-argument becomes a local `have`; a standalone lemma when "The statement is
independently interesting, or extraction sheds hypotheses the sub-argument does not need"; split
when the proof reads "long and unwieldy" ("there is no line threshold"); "Resolve doubt by
attempting the extraction: if a fragment has a clean statement, it wanted to be a lemma". Rejected
rationalisation: "I'll restructure it into lemmas after it works".

### 6.2 cameronfreer/lean4-skills [B §B3] [P, `plugins/lean4/skills/lean4/references/sorry-filling.md`, `cycle-engine.md`, `plugins/lean4/commands/autoprove.md`]
*Blocked-goal triage*: make the blocker concrete from goal and diagnostics; classify it into one of
seven classes (definitional/simp, missing intro/cases, missing rewrite, arithmetic, missing library
lemma, coercion/elaboration, "too large", which needs a helper lemma); test at most three cheap
candidates with `lean_multi_attempt`; search before adding structure; if the same blocker repeats,
stop guessing. *Stuck* = "Same sorry failed 2-3 times with no new approach", same build error after
two repairs, no sorry-count decrease for 10+ min, or empty search twice; blocker signature
(file, line, error hash); "Stuck-triggered replan is mandatory". *Falsification*: "Preflight
falsification for decidable/finite goals (30-60s max)"; on a witness, create `T_counterexample` and a
weaker `T_salvaged`; "Avoid proving `¬ P` if original sorry exists". *Fences*: "Declaration headers
... are immutable"; statement changes "Not permitted — rollback + stuck"; per sorry "Max 3
candidates ... ≤80 lines diff"; autoprove stops at 3 stuck cycles, 20 cycles or 120 min.

### 6.3 h1 (Meta FAIR, 2026) [C §3] [P, https://arxiv.org/html/2610.35962]
The harness "imposes no decomposition, planning, or search structure", but its system prompt
(App. B.2) allows and recommends it: "you may add your own helper lemmas/definitions"; "break it
into lemmas, sketch the structure with sorry to read the subgoals, prove the pieces, and iterate";
"To DEFER a goal use plain sorry (it returns the goal state)"; the worked example uses induction
"leaving sorries to see what specific goals need to be proven". The reflection prompt keeps "the
lemmas and definitions the prover has already proved". No frequency of self-decomposition is
reported. Ablations: Putnam100 69 with all tools, 49 without REPL/LSP/search; turns per
reflection 1/10/200 give 50/72/60 (so the "69 to 60" of our research note mixes two ablations);
matched with Goedel-Architect 598 vs 597 PutnamBench at $1.08 vs $1.47.

---

## 7. Comparison on the eleven fields

Abbreviations: NL natural language; fill = cheap tactics and/or hammer; neg = proof of the
negation; cex = counterexample search; "—" none or not described.

**Table 1. Fields (1)-(6).**

| Harness | (1) Trigger | (2) Proposer | (3) Representation / extraction | (4) Granularity | (5) Checks before proving | (6) Sufficiency |
|---|---|---|---|---|---|---|
| DSP | always | LLM, sketch from NL draft | Isar `have` + `<⋯>` gaps, in place | gaps must fall to fill | parse | sketch checks with gaps |
| POETRY | always (learned) | trained model | `have … sorry` per level, in place | one level at a time | — | level proof checks |
| ProofAug | proposal fails | mechanical (FindMCSP) | `sorry` for failed step/block | fail fine, retry coarse | — | MCSP checks by construction |
| HybridProver | 128 whole proofs fail | mechanical | v1 all tactics, v2 failed subgoals → `sorry` | — | structurally invalid sketches dropped | sketch checks |
| Minilang | always | model in a 10-op DSL | op creates obligations | ops are atomic | — | by op semantics |
| Isabellm | always (outline) | LLM outline, mechanical re-sorry | maximal `sorry` spans | repair ladder by block size | — | outline checks |
| Munkres | always | LLM, rule-bound | `have` + `sorry`, in place | split until sledgehammer closes | build for structure | build |
| isabelle-humanize | 2 failures on a subgoal (ladder step d) | LLM free | helper `lemma` above target | — (connective weight as progress) | — | arbiter build, no `sorry` |
| Humanfia | — | — | tasks/ACs, not lemmas | 1 mainline objective per round | — | — |
| APOLLO | proof fails | mechanical (Sorrifier) | `sorry` → lemma with REPL goal | — | — | assembler |
| MechMath | 1 + 4 repairs fail | mechanical + LLM extraction | innermost `have`/`calc` → `sorry`; relevant hyps only | — | Lean syntax; NL verifier (extraction, soundness) | `apply lemma` splice |
| Delta-Prover | repair budget fails | LLM in DSL | `show … by` subproblems | — | DSL elaboration | `conclude` |
| DeepSeek-V2 | always (data gen) | LLM (V3) | `have … sorry`; forms (a)/(b) | "details omitted" | — | composition |
| Kimina | 128 failures | LLM NL + autoformaliser | lemma in scope pool | — | neg filter (parallel) | — |
| Seed 1.0 heavy | medium fails | proposer, property enumeration | `lemma` decls; pool | score: low proof rate, relevance, length | prove/disprove each | medium run integrates |
| Seed 1.5 | always (sketch) | sketch model, RL rubric | `lemma … sorry` | >=3 lemmas; judge "granularity" | NL check (training reward) | sketch compiles |
| AlphaProof TTRL | unsolved target | variant generator | variants as separate targets | curriculum | Lean validity [S] | — |
| Goedel-Code-Prover | always | trained policy | lemmas + parent term | footprint reduction r | quickcheck (in S) | proof reconstruction (in S) |
| Aristotle | always | LLM, lemma list | separate lemma decls | "individually have very short proofs" | REPL type errors | search on block |
| Hilbert | 4 direct fail | LLM `have` sketch | `have` → named theorem + context | one key theorem or a few tactics (prompt, paraphrased) | syntax per theorem | assembled sketch compiled, subgoals `sorry` |
| Prover Agent | 100 samples fail | small LLM, 4 lemma kinds | statements only | — | parse | — (lemmas as context) |
| Goedel-Architect | always | LLM blueprint | `sorry_using [parents]`, `@[blueprint]` | "(nearly) trivial" given parents | type, DAG, reachability | blueprint compiles |
| Aleph | always | LLM plan | subproblems | — | — | — |
| Numina | always | LLM blueprint `\uses{}` | DAG of lemmas | revised "at the wrong granularity" | — | — |
| LEAP | direct (20 revisions) fails | LLM blueprint → sketch | `sorry` only in new lemma statements | reviewer: "easier" | compile; LLM reviewer | compiled sketch |
| MerLean | always (plan) | Planning agent | node per file, imports deps | decomposition check (boolean) | — (math check on failure) | — |
| ProofEvolve | always | model + schemas | hyperedge to child states | — | Lean edge acceptance | edge closes when children close |
| Magenta | — | — | — | — | statement judge (top only) | completeness judge (IMO only) |
| Rocq-MCP | always | orchestrator LLM | `Admitted` stubs; subagents | — | — | final `rocq_verify` |
| Prove2Me | always (missions) | agents + human milestones | immutable statement objects | milestones | search before submit | Property 1 |
| Trail of Bits | always | author, rule-bound | `:= sorry` lemmas; `have/suffices/calc` | extraction ladder | file compiles | file compiles |
| lean4-skills | stuck | agent, triage classes | helper lemma / sub-sorries | <=80-line diff, 3 candidates | preflight falsification | headers frozen |
| PIDE MCP skills | non-trivial proof | agent | `sorry` skeleton, helper lemmas | "Prove easy pieces immediately" | — | — |
| h1 | — (suggested) | agent free | `sorry` to read goals | — | — | SafeVerify at end |

**Table 2. Fields (7)-(11).**

| Harness | (7) Depth / width / restart | (8) Failure routing | (9) Reuse | (10) Parallel | (11) Ablation of decomposition (budget) |
|---|---|---|---|---|---|
| DSP | depth 1; resample | resample | — | — | no-automation -9.8/-9.0 pts (100 attempts) |
| POETRY | depth 10 | FAILED propagates, resketch | — | — | vs no-`sorry` model +3.9 miniF2F avg |
| ProofAug | until single `sorry` | coarser block, then ERP | shared prefix | 12 PISA | +7.8 pts at 1 query; ERP +1.6 at 500 |
| HybridProver | 1 | backtrack tactics | — | 64 procs | v1 34.8→56.1; v2 union of models 49.6→71.3 % (n=128) |
| Minilang | — | — | — | — | Sledgehammer* +6 pts |
| Isabellm | c1=2, c2=3 | micro-block → block → whole | ban list | — | none (qualitative) |
| Munkres | — | split stubborn goals | heap of chapters | — | none |
| isabelle-humanize | 42 rounds | stall 2 → replan; 3 → stop | lessons file | — | smoke only |
| Humanfia | 42 rounds | drift machine | BitLesson | lanes | none |
| APOLLO | r (2-6) | recurse on `sorry` | — | — | all 3 parts 46.7 vs 7.0 % (o4-mini) |
| MechMath | no depth cap; identity guard | LOGIC_ERROR halts local repair | — | — | 4/4 vs 3/4 vs 0/4 (128 calls) |
| Delta-Prover | l_max | regenerate sketch | — | — | IMO 2019 P1: 83 subproblems, ~332 calls vs fail at 1 024 |
| DeepSeek-V2 | recursive (data) | drop sample | — | — | none |
| Kimina | recursive scopes | prune < 0.10 after 50 | pool | yes | none |
| Seed 1.0 | heavy: days | pool grows | pool, cross-trajectory | yes | none |
| Seed 1.5 | depth 4 → restart (8); Pass@3x3 | disproved → re-sketch | verified-lemma cache | width raised for contests | none |
| AlphaProof | 15 iterations [S] | TTRL | — | yes | TTRL +~15 pts [A] |
| Goedel-Code-Prover | 128 iters, ≤32 open | frontier model after m fails | curriculum | pass@k | same model 20.1 → 44.9 %; system 68.8 % (pass@32) |
| Aristotle | iterate | revise list, keep proved | proved lemmas | many instances | none |
| Hilbert | D=5; restart | NO → re-sketch; shallow; recurse | proved subgoals | async pool | D0 75 %, D2 98.36 %, D3 98.7 % |
| Prover Agent | D=1 | drop lemma | — | — | +0.8 pt miniF2F; +5 Putnam (110 samples) |
| Goedel-Architect | 8/16 global iterations | WRONG → fix; HARD → add parents | proved nodes frozen | per lemma | 200 → 508 → 597/672 |
| Aleph | recursive | refine plan | — | parallel Lean | none |
| Numina | — | subagent, hint | blueprint | — | 4/11/12 of 12 without informal / with / with subagent (table extraction uncertain) |
| LEAP | DFS + backtrack; 2 rollouts | backtrack | memoised DAG | — | DAG +10.0/+16.7 pts; reviewer A5 |
| MerLean | 4 h | plan diff, invalidate downstream | — | sequential | none |
| ProofEvolve | per-target caps | Repair after rejection | archive, schemas | parallel attempts | 32 vs 11 /60 without decomposition |
| Magenta | T, M, K | math → re-derive; code → repair | — | batches | judge: FCR 45.5 → 0 % |
| Rocq-MCP | 2 levels | role subagents | — | 4 teams | none |
| Prove2Me | — | disproof → corrected lemma | corpus | agents | case studies |
| Trail of Bits | — | — | — | — | none |
| lean4-skills | 3 stuck / 20 cycles / 120 min | salvage; replan | — | — | none |
| PIDE MCP skills | — | restructure | — | — | none |
| h1 | — | reflection | proved lemma names | — | tools 69 vs 49; turns 72 vs 60 |

---

## 8. Rule, template and mechanical moves versus free generation

A *mechanical* move is computed from the proof text or failure site; a *template* move is chosen
by an LLM but its shape and obligations are fixed; a *free* move is whatever the LLM writes.

| Move | Kind | Used by | Evidence |
|---|---|---|---|
| Sorrify the failing block (innermost enclosing block of the primary error) | mechanical | MechMath, APOLLO, ProofAug, Isabellm, HybridProver, Munkres "replace the last automation step by `sorry`" | MechMath 4/4 vs 3/4 vs 0/4 at 128 calls [P]; ProofAug +7.8/+4.1/+3.3 pts [P]; APOLLO components together +39.7 pts on o4-mini [P] |
| Fail fine, retry coarse (drop the enclosing block, hammer the coarser goal) | mechanical | ProofAug; Isabellm's stage ladder | inside ProofAug's total only |
| Keep correct subproofs, sorry the rest | mechanical | HybridProver v2, ProofAug MCSP | union of whole-proof and tactic models 49.6 % → with sketch refinement 71.3 % (v2) [P] |
| Extract `have`/`show` as standalone lemma with context | template | Hilbert, DeepSeek-V2 (a)/(b), MechMath (relevant hyps), Seed 1.5, Trail of Bits ladder; Goedel-Prover-V2 `extract_goal` [A §3.6] | Hilbert depth curve [P] |
| Split by proof level | mechanical (training) | POETRY | 3.3 vs 12.7 steps per sketch [P] |
| Case split with exhaustiveness obligation | template | Minilang `CONSIDER`, `CASE_SPLIT`; isabelle-humanize replan menu; B5 per-residue | none isolated |
| Induction, choice of induction variable | template | Minilang `INDUCT`; isabelle-humanize "induction on a different variable"; h1 worked example | none isolated |
| iff / two inclusions | template | B5 run; Prog_Prove patterns [B §A4]; Minilang `HAVE` | none isolated |
| Backward rule (premises as subgoals), `suffices` | template | Minilang `RULE`; Trail of Bits `suffices` | none |
| Witness: `obtain`/`CHOOSE`/`define` | template | Minilang `CHOOSE`, `CONSIDER ∃`; Delta `define`, `suppose` | none |
| Calculational chain | template | Trail of Bits `calc`; DSP sketches | none |
| Special cases | free, typed | Prover Agent; AlphaProof variants [S]; lean4-skills small enumeration | 25 % of Prover Agent's used lemmas were special cases [P] |
| Consequences of hypotheses / property enumeration | free, typed | Seed 1.0 proposer; Prover Agent | none isolated; Kimina: much sampling "unhelpful or redundant" [P] |
| Generalise / strengthen | free | AlphaProof variants [S]; Numina "strengthening assumptions"; PIDE skill: generalisation "fine if ... instantiated" | none |
| Counterexample → salvage (weaker or corrected statement) | template | lean4-skills `T_salvaged`; Goedel-Architect `STATEMENT_WRONG`; Prove2Me `_with_zero`; B5 positivity fix | 292/672 problems needed a negation [P] |
| Contrapositive / contradiction as named move | — | not found as a decomposition move in any harness; `ccontr` is a Prog_Prove pattern [B §A4] | none |
| Reusable schema instantiation | mechanical (kernel-abstracted) | ProofEvolve | 32 vs 14 without recombination [P] |
| NL proof → lemma list | free | Aristotle, Seed 1.5, Hilbert, Goedel-Architect, LEAP, Numina, Aleph, MerLean, Magenta | Goedel-Architect 9 hard problems 0 → 1-4 with NL [P]; MechMath A2 [P] |
| Re-plan globally, keep proved nodes | template (routing) | Goedel-Architect, MerLean, Aristotle, Seed 1.5 restart | 200 → 508/672 over 16 refinements [P] |

Reading the table: every harness that reports a decomposition ablation either cuts mechanically at
the failure site or constrains the LLM to a format whose obligations are computed (sketch with
holes, DSL, AND-edges, scored lemmas). The purely free moves (property enumeration, special cases,
NL lemma lists) have the weakest evidence and the clearest reports of waste (Kimina's utilisation of
30-40 %; Seed 1.0 discards "lemmas with short proof lengths"; Prover Agent +0.8 points at 2.6x the
samples). The mathematical templates (cases, induction, iff, witness, calc) are ubiquitous in the
proofs these systems produce but are nowhere ablated as moves; Minilang is the only harness that
makes them the whole proposal vocabulary, and its gain is measured against Isar, not against free
decomposition.

---

## 9. How decomposition correctness is checked

**(a) True.** Formal disproof: Kimina proves negations of new lemmas (parallel to proving);
Goedel-Architect lets the prover register a negation, after a failed proof; Seed 1.0 and 1.5 try
to prove *or disprove* each lemma; Prove2Me accepts ¬statement as a submission; lean4-skills runs
"preflight falsification" (`decide`, small enumeration) for decidable goals before filling. Random
testing: Goedel-Code-Prover's quickcheck factor rejects a whole decomposition *before* any child is
proved; it is the only pre-proof formal truth gate found. NL judgement: MechMath (before solving;
three independent passes in the informal loop), Seed 1.5 (in the training reward, "cheaper than
formal disproof"), Hilbert and MerLean (after the prover fails). LEAP's reviewer judges relevance
and ease, not truth.

**(b) Well-typed in context.** Universal and cheap: every Lean harness compiles statements before
proving (Hilbert per extracted theorem, Goedel-Architect with graph checks, Prover Agent until it
parses, APOLLO with explicit `pp` types). Two typing faults are named: missing hypotheses and
natural-number truncation (Hilbert), which in Isabelle are the same hazards (`nat` subtraction,
`int`/`real` coercions, a free variable that HOL silently generalises).

**(c) Sufficient for the parent.** By compilation of the parent with children as placeholders:
Hilbert (explicit assembly step), Goedel-Code-Prover (`1_proof` in the score), Goedel-Architect
(`sorry_using`), LEAP and Delta-Prover (compiled sketch), Prove2Me (Property 1); mechanical
sorrifiers are sufficient by construction. Free-lemma systems (Kimina, Seed 1.0 heavy, Prover
Agent) do not check sufficiency at all: lemmas are offered as context and may go unused.

**Missing in the field.**
1. A truth check *before* proof effort on every new lemma, as a routine stage. Only
   Goedel-Code-Prover (quickcheck) and Kimina (negation in parallel) do it formally; the others
   spend prover budget first.
2. A measured *rate* of decomposition errors by type. The nearest are Goedel-Architect's 292/672
   problems with a negated node, Prover Agent's lemma-use categories and Kimina's utilisation; no
   one reports, per generated lemma, false / ill-typed / insufficient / unused.
3. An extraction-fidelity check that is formal: when hypotheses are dropped (MechMath keeps only
   "relevant" ones), only Hilbert's assembly compile and MechMath's NL verifier check that the
   standalone lemma still closes the `have` it came from.
4. A granularity check before proving that is not an LLM judgement: only Goedel-Code-Prover's
   footprint reduction.
5. A no-progress check: MechMath's identical-subgoal rule is the only one; nothing rejects a child
   that is a trivial restatement of its parent up to renaming.
6. Faithfulness checks exist only for top-level statements (Magenta's judge, Prove2Me read-back,
   Rocq-MCP's module check), and Rocq-MCP's A3 shows a vacuous statement can pass a kernel.

---

## 10. Candidate decomposition rules for AutoDecompose

Each rule names its sources and how Isabelle implements it. Rules 1-4 are the checking pipeline;
5-12 are moves; 13-18 are control.

1. **Admit no statement without three cheap checks, in order: type, disproof, sufficiency.**
   Sources: Goedel-Code-Prover's validity factor (quickcheck and parent reconstruction before any
   child is proved); Hilbert's assembly compile; Goedel-Architect's graph checks; Kimina's negation
   filter; lean4-skills preflight falsification. *Isabelle*: (a) `lemma name: fixes … assumes …
   shows … sorry` in a scratch theory with the parent's imports, through the Pool Server; reject on
   error or on a new free variable; (b) `quickcheck` then `nitpick`: "genuine" rejects,
   "potentially spurious" is a flag only [B §A3]; (c) the parent sketch built with every child
   `sorry` (or `-o quick_and_dirty`, as AutoCorrode's `QUICK_AND_DIRTY=1` build does). Log each
   outcome per lemma: this *is* the decomposition-correctness metric.

2. **Sorrify the failing block mechanically.** Sources: MechMath Alg. 1; APOLLO; ProofAug
   FindMCSP; Isabellm `OpenMinimalSorries`. *Isabelle*: from the first PIDE error, find the
   innermost `proof … qed` or `have … by …` span containing it; replace its proof by `sorry`
   (keep the statement); with no enclosing block, truncate and close with `sorry`; recompile; stop
   on a no-op. Success test from the PIDE skill: 0 errors and `bad` count equal to the number of
   holes.

3. **Retry coarse before asking the model.** Source: ProofAug Alg. 2; Isabellm's ladder. *Isabelle*:
   when the filler fails on a hole, replace the enclosing block by `sorry` and run the filler on
   the coarser goal; one fill per level, up to the theorem.

4. **Extract a `have` into a standalone lemma only with a fidelity check.** Sources: Hilbert
   (extraction, then assembly with "ALWAYS use the supplied theorems"); DeepSeek-V2 form (b);
   MechMath (relevant hypotheses); Trail of Bits ("extraction sheds hypotheses"). *Isabelle*: read
   the goal at the hole (⋀-bound variables, premises, `using` facts) and emit `fixes` with
   explicit types and `assumes`; check fidelity by replacing the hole with `using name by blast`
   (or `by (rule name)`) and building; a dropped hypothesis must survive rule 1(b).

5. **Case split with an exhaustiveness obligation.** Sources: Minilang `CONSIDER` (n+1
   obligations), isabelle-humanize replan menu, B5 per-residue split. *Isabelle*: `consider (a)
   "P1" | (b) "P2"` with the disjunction as its own child; residue splits on `n mod k` close their
   exhaustiveness by `presburger`/`arith`.

6. **Induction, with the induction variable and the `arbitrary:` set as the rule's parameters.**
   Sources: Minilang `INDUCT`; isabelle-humanize ("induction on a different variable"); h1's
   worked example; Prog_Prove's warning on `arbitrary:` [B §A4]. *Isabelle*: `induction n
   arbitrary: m` yields a base lemma and a step lemma whose `assumes` is the IH; varying
   `arbitrary:` is the "strengthen the hypothesis" move; quickcheck the step lemma, since an IH
   that is too weak shows up as a counterexample to the step as stated.

7. **Bidirectional and extensional splits.** Sources: B5 ("forward exclusion and a backward
   construction"); Prog_Prove patterns [B §A4]. *Isabelle*: `iffI`, `set_eqI`/`subset_antisym`,
   `ext`, `antisym` for orders; each direction a child.

8. **Backward rule, `suffices`, and witnesses as templates.** Sources: Minilang `RULE`, `CHOOSE`,
   `CONSIDER ∃`; Trail of Bits `suffices`; Delta-Prover `define`/`suppose`. *Isabelle*: `proof
   (rule r)` makes r's premises children; for an ∃-goal, `define w where …` then a child about the
   named `w`, so children never contain an unfixed witness; `obtain x where …` turns an ∃-fact into
   context.

9. **Calculational chains, one child per link.** Sources: Trail of Bits `calc`; DSP sketches.
   *Isabelle*: `also … finally`; each step a child; transitivity is checked by the chain itself.
   Prefer `<`/`≤`/`=` chains (Isar's `also` does not compose `≥` by default [B §A4]).

10. **Special cases are probes, not children.** Sources: Prover Agent (25 % of used lemmas);
    lean4-skills small enumeration; AlphaProof variants [S]. *Isabelle*: evaluate `value`/`eval`
    and `quickcheck` on small instances; feed results to the planner as evidence; a special case
    enters the dependency graph only if the parent's sketch cites it.

11. **Hypothesis consequences go to a bounded, pruned pool.** Sources: Seed 1.0 proposer; Prover
    Agent "facts derived from the assumptions"; Kimina's utilisation pruning (0.10 after 50).
    *Isabelle*: candidates `assumes <problem hypotheses> shows <property>`, rule 1 first; drop any
    candidate not cited by an accepted sketch after k sketches; `solve_direct` against the pool
    before proposing a new lemma [B §A2]. Low priority: weakest evidence of all moves.

12. **On a genuine counterexample, salvage rather than discard.** Sources: lean4-skills
    `T_counterexample`/`T_salvaged`; Goedel-Architect "Fix the statement"; Prove2Me
    `gotsman_linial_with_zero`; B5's positivity condition. *Isabelle*: nitpick's model names the
    bad instance; propose the hypothesis that excludes it (boundary, positivity, non-emptiness,
    `finite`), rerun rule 1 on the repaired child, then re-check the parent's sufficiency (the
    stronger hypothesis must be discharged there).

13. **Require a measurable reduction; reject identity.** Sources: Goedel-Code-Prover
    r = max(1 − d̄/d(G), 0); MechMath's identical-subgoal rule; isabelle-humanize's connective
    weight. *Isabelle*: footprint = count of logical connectives, quantifiers and constants in the
    statement term (computed from the server's term output, not from copied symbol tables); reject
    a decomposition whose largest child is not smaller than the parent, or whose child is
    α-equivalent to it.

14. **Target "nearly trivial given parents", tested by the filler.** Sources: Goedel-Architect;
    Aristotle; Hilbert (one key theorem or a few tactics); Munkres step 6; the research note's
    pass-1 fill rates [research note §1]. *Isabelle*: a leaf is accepted when `try0` or one
    sledgehammer call closes it; otherwise it is split again or sent to the leaf prover; never a
    longer timeout [research note §2a].

15. **Shallow and wide: depth cap 2-3, then global replan keeping proved nodes.** Sources: Hilbert
    (D=2 98.36 %, D=3 98.7 %); Seed 1.5 (depth 4, restart with proved lemmas); Prover Agent
    (D=1); Goedel-Architect (global refinement; recursion "can inefficiently loop on dead-end
    strategies"); MerLean (plan diff invalidates downstream). *Isabelle*: proved lemmas are
    immutable statement objects in their own theory files (Prove2Me); a replan may add nodes or
    replace unproved ones only.

16. **Diagnose mechanically before any LLM judge.** Sources: Goedel-Architect's two labels;
    MerLean's math-then-decomposition check; Magenta ("When evidence is ambiguous, return
    code_error"); Hilbert (judge only after prover failure). *Isabelle*: after a failed leaf,
    nitpick genuine → STATEMENT_WRONG (rule 12); sledgehammer finds a proof whose reconstruction
    fails → a proof-method problem, not a decomposition problem [B §A1]; otherwise PROOF_TOO_HARD →
    split (rules 2-9). The NL judge is the last resort and its verdict is logged against the formal
    outcome.

17. **Memoise canonical statements across branches.** Sources: LEAP (DAG vs tree +10.0/+16.7
    points); Seed 1.5 lemma cache; Prove2Me search-before-submit and milestones; ProofEvolve
    schemas. *Isabelle*: canonical key = statement printed with types and normalised bound names;
    before proving a child, `solve_direct` against proved pool lemmas.

18. **Cheap-to-expensive order for the whole pipeline.** Sources: Hilbert's ordering; APOLLO's
    AutoSolver before the LLM; DSP's heuristics before the hammer; lean4-skills (3 candidates,
    then search, then structure). *Isabelle*: parse/type (ms) → quickcheck (s) → nitpick (≤30 s) →
    sufficiency build → `try0` → sledgehammer (30 s) → leaf LLM prover in a fresh context → NL
    judge. Log tokens at each stage so tokens per closed leaf can be attributed to rule versus
    model.

---

## 11. Unverified items and discrepancies with A-C

- **[U]** AlphaProof's variant kinds and AND-node value rule (paywalled; [A §2.5] only); LLMemma
  (no source); Delta-Prover's DSL grammar and prompts (figures only); Seed 1.5's rubric texts;
  Prover Agent's and MechMath's verbatim lemma prompts; Numina's system prompt or skills (none in
  the public repo); Aleph's procedure (outline only); how often h1's agents self-decomposed (not
  reported); the v1 humanize gate pipeline (from a local analysis note, not the v1 code).
- **Corrections to A-C and the research note**, each argued in place: HybridProver's 34.8 → 56.1 %
  in [B §C2, §E] is v1, whose procedure differs from the current one (§2.4); Aristotle's
  "each meant to have a very short proof" is a paraphrase, and its drafting slip was about
  strict/weak/eventual decrease rather than quantifiers (§5.1); h1's context-rot comparison is
  72 vs 60, not 69 vs 60 (§6.3); the Munkres sledgehammer pass is not stated to be parallel (§2.7);
  Minilang's ten operations exclude `INTRO` (§2.5); Goedel-Architect's "11 to 44" negated nodes
  and "pass@44" are rendering artefacts for 1-4 and pass@4 (§5.4).

## Source index

Local (relative to the owner's GitHub folder): `humanize2/README.md`, `humanize2/docs/flows/*.md`,
`humanize2/src/hmz/flows/builtin/`; `isabelle-humanize/README.md`, `STATUS.md`,
`humanize-analysis(temp).md`, `humanize2-explained(temp).md`, `flows/isabelle_rlcr/{gates.py,
progress.py, prompts/round0.md, prompts/next_round.md, prompts/drift_replan.md, prompts/review.md}`,
`.m0/flowverse-ref/flows/humanize1/_humanize1/prompts.py`, `runs/README.md`,
`runs/putnam_2023_b5-rlcr-deepseek/methodology-analysis.md`;
`Research/agent-loops/builder-reviewer/{README.md, LESSONS.md, BUILDER_PROMPT.md, REVIEWER_PROMPT.md}`;
`isabelle-pide-mcp/.claude/skills/{isabelle-formalization, isabelle-proof-development, pide-mcp}/SKILL.md`;
`Isabelle-MCP/docs/TECH_NOTE.md`; `AutoCorrode/CLAUDE.md`, `AutoCorrode/iq/iq_guidance.md`,
`AutoCorrode/design-documents/05-agent-generated-isabelle-style.md`.

Web: URLs are given inline at each entry (all fetched 2026-11-11), plus
https://github.com/cameronfreer/lean4-skills , https://github.com/kappelmann/isabelle-pide-ai ,
https://github.com/deepseek-ai/DeepSeek-Prover-V2 ,
https://github.com/ByteDance-Seed/Seed-Prover/tree/main/DeltaProver and
https://arxiv.org/pdf/2507.23726 (Seed-Prover 1.0; no HTML version). Not reachable: AlphaProof
https://www.nature.com/articles/s41586-025-09833-y (login redirect).
