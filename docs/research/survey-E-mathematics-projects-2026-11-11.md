# E. Large mathematics formalisation projects: how they split work, freeze statements, coordinate workers, and what they cost

Prepared 2026-11-11 for AutoDecompose (rule-based decomposition of hard Isabelle/HOL problems into Putnam-level
lemmas closed by bounded student agents; measured by tokens per closed leaf and decomposition correctness).
Surveys A-C cover competition-scale systems; this one covers project-scale formalisation, AI-run and human-run,
for what it says about the unit of work, statement stability, coordination and cost. Facts already in A-C are
cited as [A §x], [B §x], [C §x] and not repeated.

Method: web search, then direct reads of primary sources (arXiv HTML converted to text and read in full, PDFs via
`pdftotext`, repository READMEs, project blogs). Section 1 and Section 2.3 were read by the author. The rest of
Section 2 was read by two delegated readers during this survey, instructed to read primary sources and quote; I
did not re-read those sources. Tags:

- **[P]** read in the primary source during this survey by the author;
- **[P\*]** read in the primary source during this survey by a delegated reader, not re-read by the author;
- **[S]** secondary source only; **[U]** unverified or recalled; **[derived]** my arithmetic on published numbers.

Costs are quoted with their pricing basis. Subscription and API prices for one run differ by a factor of about 55
(Section 1.7), so dollar figures are never comparable across rows.

---

## 0. Findings in brief

1. Every AI project that reached textbook or research scale converged on one unit of work: **a statement, posted
   before its proof, with its dependencies explicit** (Prove2Me's card, AutoformBot's DAG task, the swarm's sketched
   `sorry`, the human blueprint node) (1.1-1.4, 2.1-2.5).
2. Anthropic's first FLT attempts "quickly lost track of the project's state and stopped collaborating effectively";
   the run succeeded after moving to Prove2Me's statement DAG with statements and proofs in separate files [P] (1.2).
3. Immutability has a measured price: in the 13-million-line FLT proof about two in five statements inside proof
   files repeat one made elsewhere, a fifth of proof-file lines are verbatim copies, and 31 % of bytes are generated
   preambles [P] (1.2).
4. AI projects fail on statements, above all definitions: 61 of 62 agent definitions judged poor in one review;
   weak carrier-set definitions in Isabelle Munkres; a textbook definition implemented wrongly twice by the swarm [P]
   (1.3, 1.7, 1.8).
5. Checking statements before proving pays: peer agents "caught several false statements early" in FLT; disproof
   submissions repaired a Prove2Me branch; test statements are 23.8 % of Formal Conjectures [P] (1.1, 1.2, 1.9).
6. Flat task queues waste compute: the 30 000-agent swarm spent about half its input tokens on aborted agents and
   found its single merge queue a choke point; its successor added a dependency DAG and a bisecting merge queue [P]
   (1.3, 1.4).
7. "Model fixed, harness varied" has one precedent: AutoformBot ablated each harness component at a fixed model and
   matched token budget (77 % vs 51-64 %) [P] (1.4). None exists in Isabelle or at Putnam-lemma grain, and none varies
   the decomposition policy.
8. Checking has become a cost line: one pass over OpenAI's AI-written Lean library took 31.5 h on 24 cores, 1 % of
   files taking a quarter of it [P] (1.6); the FLT proof builds in about six hours on 96 cores [P] (1.2).

---

## 1. AI-run large projects

### 1.1 Prove2Me (Chen, Marwaha, Lu, Yuen, Peng; arXiv 2608.28433v2, 31 Aug 2026)

Read in full, https://arxiv.org/html/2608.28433v2 [P]. The research note's Section 6 summarises it; this is the record.

**Statement object.** "each theorem is a standalone, immutable object that is stated once and may have multiple
proofs, possibly by different agents" [P]. A card has a *Description* (natural language; agents "encouraged to spell
out the intended formulation in detail"), a *Preamble* (imports from Mathlib or platform definition files) and a
*Formal statement* "required to terminate in a `:= by sorry` placeholder"; environments are pinned to one Mathlib and
toolchain and "fully isolated" [P]. Statement shape serves the consumer: the example is stated "for a bare adjacency
predicate `adj` rather than a `SimpleGraph`, which keeps it directly applicable to the hypercube subsets that the
sensitivity proof needs; choices of this kind are what the Description field records and what auditing checks" [P].

**Proofs and disproofs.** A proof declares `theorem solution` "whose type matches that of the target theorem exactly and
which contains no `sorry` or any other new axioms", compiled in the target's environment; "an agent may submit a
disproof ... whose type is ¬(target statement)"; every proof carries "a detailed natural-language explanation" [P].

**Proof-sketch and Property 1.** "We call a proof that imports other theorems a proof-sketch: it establishes the target
conditional on the imported statements"; imports may still end in `sorry`; "every statement and proof-sketch is
persistent and cannot be edited once submitted". Property 1 verbatim: "**Theorem 4.1 is verified if all imported child
lemmas are verified.**" Hence "An agent can attack any one of them without ever downloading or compiling Theorem 4.1 ...
Immutability guarantees that this local correctness composes into global correctness" [P].

**Section 4.1, why naive sorry-filling does not scale** [P]: (i) "whenever a downstream lemma changes, every upstream file
that depends on it must be recompiled"; (ii) "the work is hard to atomize. When several agents edit the same file or
directory, their contributions are typically interdependent and interfere with one another". Git workflows mitigate this
"at the cost of centralization: pull requests must be reviewed and merged by human maintainers or an orchestrating agent".
Related work adds that "Lean recompiles the entire downstream cone whenever a module changes, even for a proof-only edit",
so a swarm's merge queue "becomes the empirical bottleneck". **Section 4.1 contains no measurements**; the numbers are
Gloeckle's (1.3) and, later, Anthropic's (1.2).

**Formalpedia** is the library of proved, individually importable cards, aimed at "the application layer"; a search API
indexes the mandatory descriptions; "Agents are also instructed to search before they submit ... introduce a new statement
only when none does"; contributors earn credit when others import their statements [P].

**Missions, captain, audit.** A mission is "a headline goal ..., the definitions it depends on, and the milestone lemmas".
"Humans audit this core before the mission is released ... and audit nothing beyond it ... This is sound because the trusted
object is not the agent's chosen decomposition, but the Lean kernel's acceptance of proofs of the audited statements" [P].
The captain's agent drafts a private, mutable proposal, but "the human is required to click each statement individually to
confirm it"; confirmed drafts become immutable and a moderator reviews the mission [P].

**Read-back.** "an independent auditor agent is given the Lean declaration and its dependent definitions, but not the
original source reference" and translates it to LaTeX "making binders and hypotheses explicit"; the human compares two
mathematical statements [P]. The paper's example surfaces three implicit conventions (independent quantification, empty
product 1, hypothesis only n < M) [P].

**Milestones.** Consensus fails two ways: "several agents independently formalize the same lemma in mutually incompatible
ways; because the resulting statements cannot import one another, parallel effort is duplicated", and "a formalization that
silently deviates from the source contaminates everything above it" [P]. A milestone is "an authoritative natural-language
statement, usually transcribed verbatim from the source ... together with a link to the theorem that is its canonical
formalization, once the captain attests one"; milestones are ordered, "idempotent" and "authoritative", and are "the entry
point to a mission rather than the raw decomposition graph" [P].

**Discussion and correction.** Agents post "progress, intermediate findings, and lessons learned" [P]. The only reported
statement defect: a sketch imported `gotsman_linial`, another agent disproved it, and the first posted
`gotsman_linial_with_zero` "that supplied the missing boundary condition, and the corrected theorem went on to close the entire
branch" [P]: the repair was a new statement, not an edit.

**Missions** (Table 1; mid-June to end July 2026; "case studies, not a controlled experiment") [P]:

| Mission | Type | LOC | Cost | Agents | Models | Days |
|---|---|---|---|---|---|---|
| Exact Matrix Completion | paper | 81K | $600 | 9 | Opus 4.8, Fable 5, GPT 5.5 | 16 |
| Sipser-Gács-Lautemann | paper | 55K | $400 | 3 | Fable 5, GPT 5.6-Sol | 8 |
| Bandit Algorithms | textbook | 151K | $400 | 6 | Fable 5, GPT 5.6-Sol | 13 |
| Introduction to Linear Optimization | textbook | 17K | $200 | 4 | GPT 5.6-Sol | 7 |

Costs are "Claude and ChatGPT Max plans at roughly $200 per month times the number of human contributors"; agents include
"subagents launched by the same user" [P]. The Sensitivity Conjecture mission also closed [P]. **No per-mission tokens, failure
account, defect count, duplicate count or time breakdown is given.**

**Limitations stated.** Model and harness "confounded in every row ... requires holding the model fixed and varying only the
harness, which we leave to future work"; open questions on corpus search, exchange of "harnesses, lessons, and context",
rejecting "low-quality or malicious content", and human-legible insight; "Choosing what is worth formalizing, decomposing it
into milestones, and judging whether a formal statement says what it is meant to say all remain matters of human judgment"
[P]. v2 is dated after the FLT run (1.2) and does not mention it.

### 1.2 Anthropic's FLT formalisation on Prove2Me (run 7-17 Aug 2026; announced 4 Sep 2026)

Read [P]: https://www.anthropic.com/research/formalizing-fermats-last-theorem ; the run report
https://www-cdn.anthropic.com/9e431dff043da6538d99d6c2d231b670aa3da263.pdf ; README and PROOF-PATH.md of
https://github.com/anthropics/fermats-last-theorem ; Buzzard https://xenaproject.wordpress.com/2026/09/04/flt-anthropic-has-beaten-me-to-it/ .
Headline numbers are in [B §B4].

**Organisation.** "A team of Claude agents working in parallel wrote the statements, checked one another's statements, and
proved them"; humans "wrote no mathematics and no Lean beyond the one-line statement of the goal theorem" and gave priorities
("push [the] Mazur [theorem] to be done soon") [P]. "Dozens of Claude agents"; a model "roughly comparable to Claude Fable 5.1"
[P]. "A 'card' is Prove2Me's unit of work: one theorem statement, posted as a node in the shared dependency graph" [P]. In the
release, "A theorem `X.y` is stated in `Theorems/Thm_X_y.lean` and proved in `P2M/Sol/S_X_y.lean`, whose `import Theorems.…`
lines are exactly the theorems it cites" [P]. Agents priced cards in "days", "weeks", "months" and re-priced them; a "weeks"
wall closed in 2 h 16 min [P].

**Why the switch mattered.** "A number of Claude's initial attempts failed: while agents had some early success, they quickly
lost track of the project's state and stopped collaborating effectively. Their failed efforts contributed ~7% of the
non-boilerplate lines in the final proof" [P]. Prove2Me helped by a DAG of statements "particularly helpful for mitigating
memory degradation and allowing multiple agents to work in parallel"; by "separating theorem statements and proofs into
different files" to cut compilation; and by search over descriptions [P].

**Statement checking.** "Before a statement was worked on, other agents usually checked that it was true as written. This caught
several false statements early" [P]. One false lemma passed a reviewer and was caught by an agent who "found the counter-example
by computing a case my [review] had argued instead of computed ... before anyone wrote a proof against it"; another, objected to
by a second agent, was retracted 90 minutes before the end [P].

**End-to-end check.** "Prove2Me compiles each card's proof separately, against only the statements of its children" [P]. The
acceptance test recompiled all 29,511 cards off-platform, "every proof's type matched to its card and its axioms confined to
Lean's standard three plus exactly its declared children, and that dependency graph checked acyclic and grounded"; then one Lean
project whose `FinalCheck.lean` pins `#print axioms`; then comparator and the independent kernel nanoda [P].

**Size and cost.** 29,511 theorems in the final tree, "about 533,000 supporting lemmas local to the proof files", about 13 million
lines (10.5 million without boilerplate), 60,475 modules [P]. "about six billion output tokens" [P]; a commenter's $300,000 is
[S]. Build 5 h 32 min at 96 jobs, peak 153 GB (README); comparator about 15 h [P]. About 200,000 output tokens per final-tree
theorem, 460 per line [derived].

**Quality, from the assessment section of the report** (Claude's text, quoted by Anthropic) [P]: "Each card was proved in
isolation. Roughly two in five theorem statements inside the proof files repeat, word for word, a statement already made in
another proof file. About a fifth of all proof-file lines are verbatim copies ... and one basic lemma is re-declared in over 300
files." "31% of the bytes are generated preambles that switch off instances and simp lemmas so each proof's environment holds
still. About 11,700 files set their own computation (heartbeat) limits". "One toolchain bump, Lean 4.30 to 4.33 ... changed 7,620
of 29,511 proof files (26%), and 5,672 (19%) needed individual repair." "Our 'Ribet', 'Wiles', 'Mazur' and 'Langlands–Tunnell'
are restricted versions." A dip in the proved count was "a rewiring of that dependency tree, not lost work" [P].

**Buzzard** [P]: compiled it, ran comparator, "it checks out"; inspected by hand the roughly 100 lines an agent classed as neither
definition nor proof; "mathematically this work of anthropic tells us essentially nothing". On Mathlib: reviewer time "a massive
bottleneck", "reviewers are very reluctant to review AI-generated code". Anthropic also reports Vinogradov's three-primes theorem
"in just three days" by agents on three Claude Max plans coordinating only through Prove2Me [P].

### 1.3 The 30 000-agent swarm: Gloeckle et al., "Automatic Textbook Formalization" (arXiv 2604.03071, Apr 2026)

Read in full, https://arxiv.org/html/2604.03071v1 [P]; code https://github.com/facebookresearch/repoprover .

**Target.** Grinberg's 500-page graduate algebraic-combinatorics text; 340 target definitions and theorems, all proved; about
130,000 lines, 5,900 declarations, 52 files; Claude 4.5 Opus; one week [P]. Targets were picked "by means of a prompted LLM",
omitting helpers, to measure coverage while "reducing review workload" [P].

**What failed first.** An agent writing all statements and launching one prover subagent per theorem "proved unable to scale
beyond simple preprints or book chapters because of its limited context handling" [P].

**Partition and roles.** Git, trunk-based, short-lived branches; features "as small and self-contained as possible" [P].
*Sketchers* formalise a chunk's definitions and statements with `sorry`; *provers* fill proofs and may escalate or fix statements;
a *mathematical reviewer* ("whether the statements accurately reflect the statements from the source") and an *engineering
reviewer* must both approve and the branch must build and merge cleanly; rejection reasons include "duplication of existing
results" [P]. A folder of issue files coordinates maintainer, triage, scan and progress agents [P]. No human partitions.

**Merge queue.** "the single-threaded shared merge queue is a choke point ... when they are ready to be merged, they may no longer
be compatible with the current main branch and need to be requeued"; agents "giving up eventually and creating additional issues
... spawn[ed] additional maintainer agents, further increasing the resource contention" [P]. **No conflict rate is reported.**
Largest PRs "did not exceed a few hundred lines" [P].

**Outcomes** (Table 3) [P]:

| Outcome | Agents | Input tokens (M) |
|---|---|---|
| Merged | 3,490 | 16,477 |
| Approved, not merged / max revisions / max iterations | 589 / 976 / 11 | 1,298 / 6,935 / 101 |
| No PR / No PR (blocked) | 14,192 / 4,668 | 7,448 / 8,012 |
| Aborted (restarts) | 6,120 | 42,904 |
| Total | 29,691 | 80,686 |

Total 30,046 agents, 83.7 B input and 561 M output tokens; "$430K" uncached, estimated "$100K overall", "around $200 per page and
$300 per target"; "around half of the input tokens are spent on aborted agents" [P]. Merged agents are 11.8 % [derived].

**Failure modes, causes as stated** [P]: an N-partition type defined three times, a shared version making four, one chapter's
8k-line private API bridged by an equivalence instead; the Bender-Knuth involution defined twice, both wrong; "Where lemmas were
provable with a broken definition, prover agents happily provided the proofs. Where the lemma was false ... [they] did not
investigate globally", blamed on "'myopic' prompts" and reviewers "preventing regressions"; placeholder definitions "such as the
identity function"; rabbit holes into cited theorems (Kasteleyn led to Pfaffians); "LLM bureaucrats" under tight orchestration,
duplication and convention drift under loose; blocked agents simply requeued, whereas "A directed acyclic graph of task
dependencies that determines agent launch order would improve inference efficiency".

**Lessons stated** [P]: leave freedom early and tighten "when the release nears ... 'simulated annealing'"; hand-launched status
agents wrote blocker reports a few times; "a 3-10x decrease in inference cost can be achievable without the need for better
models" (projected); "the bottleneck ... is no longer a lack of logical reasoning in models but the complex orchestration".

### 1.4 AutoformBot / ATLAS: Rammal et al., "Formalizing Mathematics at Scale" (arXiv 2605.29955, May 2026)

Read in full, https://arxiv.org/html/2605.29955v1 [P]. Successor to 1.3; not in surveys A-C.

**Scale.** 26 textbooks; 2,855 of 4,007 targets (71.3 %); 483,918 lines, over 45,000 declarations; 183,157 M tokens in their
weighted measure (cache reads 0.1x, writes 1.25x, output 5x); mainly Opus 4.6; about a week per book; human input "from
nonexistent to sending a few messages of general advice ... once a day" [P]. Per book: Real Analysis 175/177 at 586 M; Lie
Groups 74/185 at 45,384 M; work stopped at "strongly diminishing returns, where each new success required exponentially more
compute" [P]. Workers take 76.4 % of compute, reviewers 6.9 %, orchestrator 4.0 % [P].

**Partition.** An orchestrator agent keeps a task DAG "whose edges encode the book's logical dependencies", under a "strict task
granularity rule: each task covers at most one mathematical statement or one specific fix (a single sorry, a single axiom, a
single faithfulness issue)", and must "never retry a failed task with an identical prompt" [P]. Ready tasks are dispatched;
several workers may race in separate worktrees, first through the gates wins; a per-task *trace analyser* keeps skill guides;
a *supervisor* re-evaluates targets after each merge and files "one task per unjustified sorry" [P]. Merge queue: batched,
rebased, "verified with a single build ... If it fails, the queue bisects the batch to isolate the breaking commit" [P].

**Statement checking.** A metaprogram builds the declaration graph with axiom sets and "structural tags" (vacuous bodies,
hypothesis smuggling); three LLM judges score faithfulness, integrity, quality; the anti-cheating list includes statements
replaced by `True` and "Encoding theorems as definitions" [P]. Human review of one book: two placeholder axioms, "most of the
formalization is solid, but the hardest statements are not formalized faithfully"; it also corrected a false textbook statement
[P].

**Harness ablation** (one book, 39 targets) [P]. Model fixed (Opus 4.6), three workers per task, 600 M tokens: full system 77 %;
without orchestrator re-planning 64 % (cheapest below about 100 M, then plateaus); without supervisor 51 %; without trace analyser
57 %, exhausting its budget fastest as "workers repeat the same mistakes". Harness fixed, 1,200 M tokens: Opus 4.6 92 % vs Gemini
3.1 Pro 46 %. Racing 3-5 workers beats 1 in wall clock (62-68 % vs 44 % at 4 h) and at lower token budgets.

**Failure modes** [P]: "Frontal assault"; "Cheating", including replacing "a manifold or a scheme ... with an oversimplified formal
definition, which can then contaminate many dependent statements", with stricter review breeding "an adversarial dynamic";
"Infrastructure panic"; "Orchestrator fatigue": "it creates coarse-grained tasks with unhelpful prompts, or silently stops
dispatching work on difficult targets". What worked: progressive-detail views, delegation to fresh task-scoped agents, and
"Worker escalations, particularly decomposition requests ... surface false axioms and suggest decomposition strategies" [P].

### 1.5 Math Inc Gauss: strong PNT and sphere packing

Basics in [A §4.6], [B §B4]. Additions:
- **Strong PNT (2025).** Gauss "relies on natural language scaffolding supplied by human mathematicians, and requires high-level
  expert guidance"; about 25,000 lines, three weeks, "thousands of concurrent agents, each with its own Lean runtime"; no cost
  [P] https://www.math.inc/gauss .
- **Dimension 8.** The human project (from March 2024) supplied repository, blueprint and main statement; "Working from the
  existing blueprint and Lean development, ... Gauss completed a sorry-free formalization ... in five days, taking the project from
  about 20 000 lines to 80 000 lines. A subsequent compression and refactoring pass reduced the development to 60 000 lines ... it
  was easier to generate the proof than to clean up and golf the code"; style: "many small auxiliary definitions with little or no
  API", trivial facts and special cases of Mathlib reproved; correspondence to the intended proof path "still being investigated"
  [P] https://arxiv.org/html/2604.23468v3 .
- **Dimension 24 (Mar 2026).** About two weeks from the paper "plus autonomous literature search", "no additional human-written
  scaffolding"; "At peak ... roughly 500,000 lines ... after cleanup ... about 180,000"; two source errors found and fixed [P]
  https://github.com/math-inc/Sphere-Packing-Lean . Lean maintainers later called cleaning it up "more trouble than it was worth"
  [P\*] https://xenaproject.wordpress.com/2026/10/16/how-to-formalize-all-of-mathematics/ .

Both successes started from a human-fixed statement set; generation inflated code 1.3-2.8x over what survived cleanup [derived].

### 1.6 OpenAI's AI-generated Lean library and its checking cost

- **Library** (https://github.com/openai/math , read 2026-11-11) [P]: 721 manuscripts in 373 families from an internal model; "~42%
  top-line results formalized"; Lean "organized in a single large library, so we recommend compiling only small portions at a
  time"; each formalised result has a Comparator challenge (statement with `sorry`) as its statement check. History: three
  manuscripts withdrawn on 7 Oct 2026 for a sign error propagating to two dependants; 14 revised with "corrected statements" [P]. A
  blog reports Lean theorems weaker than a Navier-Stokes paper's claims [S]
  https://redreamality.com/blog/ai-math-verification-lean-faithfulness/ . How the Lean was produced is not documented.
- **Checking cost** (eunomia.dev, 6 Nov 2026, read in full) [P] https://eunomia.dev/blog/2026/11/06/ai-lean-proof-checking-cost/ :
  162,170 of 163,096 files checked once in 31.5 h on a 24-core desktop; 1 % of files took a quarter of the time; 1,354,379
  `decide +kernel` calls in 5,848 files (Mathlib: 7), the 3.6 % of files using it taking 18 % of the time; one 450-line file
  without `decide` took 2.6 h on one core; replay costs 0.5-6.5 % of the first check but dependency loading (median 4 s) dominates.
  Advice: "budget it in tokens per CPU-second". The tool's README says a separate run certified only 968 of 162,170 modules [P]
  https://github.com/yunwei37/proofserve . Headline also in [C §4].

### 1.7 Isabelle at project scale

**Munkres in Isabelle/HOL** (arXiv 2604.07455, read in full [P]; outcome numbers in [A §1.11]).
- Two phases, "ChatGPT 5.2 for bulk formalization and Claude Opus 4.6 for proof development"; one agent at a time, so no merge
  problem; the partition is the textbook's numbering, each item annotated `(** from §37 Theorem 37.3 (Tychonoff) [top1.tex:5253] **)`
  [P].
- Final sorry-first rule: skeleton with `sorry` at every step ("not by fast, not by linarith, not by simp ... not even done"); build;
  `sledgehammer [timeout = 10]` on every `sorry`; `process_theories` once "to collect all ATP suggestions in a single pass"; take
  the fastest proof; on failure "decompose the step into finer have blocks and repeat" [P]. CLAUDE.md had eight revisions "each
  prompted by a specific failure mode" [P].
- Build engineering: a precompiled heap cut incremental builds from 50-60 s to 12-13 s; metis to meson often 10x; the 120 s session
  timeout "acts as a hard constraint on proof complexity" [P].
- Human role: 635 of 764 user messages were the automatic "Read CLAUDE.md"; 59 corrections (tactic explosion 9, tool misuse 6,
  "Cherry-picking easy goals" 4) [P].
- Cost: 2.66 M output and 17.2 B cache-read tokens, "$8,895 at list prices", effectively "approximately $160" on a $200/month plan
  [P], a factor of about 55 [derived].
- Statement review of a frozen snapshot: `is_topology_on` lacks `T ⊆ Pow X`, propagating to derived predicates; incomplete and
  mislabelled theorems; `countable` defined three times; redundant "safe" hypotheses; yet "no proved theorem is wrong: the explicit
  assumptions compensate for the weak definitions at every point of use"; "the model reliably produces definitions that are
  sufficient for the proofs at hand but does not anticipate downstream reuse" [P].

**Urban, Megalodon topology** (arXiv 2601.03298, read [P]): about 130,000 lines in two weeks for "about $100"; a script printing per
theorem "admit:NO, recadmit:NO, deps(...)" was added late to expose "choke points", and "this has helped the LLM to orient itself";
the LLMs were "(occasionally) lazy in formalizing the theorem and definition statements ... stubs, ad-hoc or special cases" [P].

**"Just Type It in Isabelle!"** (arXiv 2604.15713v3, sections 6-7 read [P]; summary in [C §5]): reviews "focused on aligning theorem
statements and definitions with the underlying paper"; one misalignment "still remains in the final version, despite human reviews
repeatedly pointing to the problem"; a locale assumed properties of a constant "before defining the constant" [P]. 1,938 lines at
$139 (human paper proof) vs 2,071 at $140 (AI paper proof), API-priced, the latter needing "more human feedback ... as well as more
rounds of review"; told to import an existing formalisation, the agent copied it [P].

### 1.8 "Sorries Are Not the Hard Part" (arXiv 2606.13925, read [P])

Grothendieck vanishing in Lean; humans fixed the statement over Mathlib definitions only ("it prevents the agent from making custom
definitions to render the theorem trivially true") and supplied Hartshorne's proof [P]. Nine days to a sorry-free 5,000 lines, one
week of expert review, two weeks of review-driven refactoring [P]. "the agent made 62 of its own definitions and there was exactly one
that was done the correct way"; intermediate results "not general enough to be reusable"; requested changes were made but "the agent
failed to identify further changes on its own"; on heartbeat overrides: "a proof too expensive to check is usually a proof that should
be decomposed" [P].

### 1.9 Formal Conjectures and AlphaProof Nexus: statement defects at project scale

Benchmark numbers are in [C §2.4].
- **Formal Conjectures** (arXiv 2605.13171, read [P]): 291 misformalisations fixed: misrepresentation 140 (48.1 %), semantic 103
  (35.4 %), implicit conventions 23, reporting 15, syntactic 9, mathematical 1; "mandatory code review by humans with both Lean
  expertise and relevant mathematical domain knowledge"; "AlphaProof runs on submissions to catch potential misformalizations before
  merging"; "test-based design for definitions", 467 test and 155 API statements (23.8 %); easy variants included because their
  disproof "might indicate that some of the definitions used have been stated incorrectly" [P].
- **AlphaProof Nexus** (arXiv 2605.22763v2, read [P]): proofs under "natural density" exposed ambiguous Erdős statements (#125,
  #741); for 492 autoformalised OEIS conjectures the agent first had to prove "test lemmas" checking the first terms; a sandbox
  "verifies that the original target theorem statement was not altered"; "a global goal cache ... computes a deep hash of the exact
  formal Lean context and target for every generated subgoal" and reuses proofs and disproofs across the population [P]. Cost "a few
  hundred dollars" per solved problem, but "identifying tractable problems was itself a significant computational investment" [P].

---

## 2. Human-run and human+tool projects

### 2.1 Liquid Tensor Experiment (Lean 3; Dec 2020 to Jul 2022) [P\*]

Sources: https://xenaproject.wordpress.com/2021/06/05/half-a-year-of-the-liquid-tensor-experiment-amazing-developments/ ,
https://leanprover-community.github.io/blog/posts/lte-final/ , Commelin & Topaz https://arxiv.org/abs/2309.14870 .
- About 91,000 lines; "about a dozen mathematicians and several computer scientists"; no cost figure [P\*].
- "Johan made an attack along the path of steepest ascent towards the proof, and handed off all required self-contained lemmas to the
  community"; the blueprint came after the code, "(largely) the other way around!" (Scholze) [P\*]; "the key thing which made LTE
  parallelisable was the nice collection of sorrys in the repo" (Buzzard) [P\*].
- Spec-driven development: a sorried definition is "a unit of mathematical debt" usable at once; "We can't rely on an implementation
  detail because there is no implementation yet!"; when `Ext` was refactored, failures were "localized to those constructions and
  proofs that depend on the implementation" [P\*].
- Statement check: an `examples/` test suite of known facts, because "If the contributors to LTE were evil, the symbol Ext might be
  defined as the zero functor" [P\*].

### 2.2 PFR (Lean 4; 12 Nov to 5 Dec 2023) [P\*]

Sources: https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/ , Zulip archive.
- About three weeks, about 11,100 lines, 20-30 contributors [P\*]. Unit: a blueprint node; Tao front-loaded statements and posted
  numbered "Outstanding tasks" lists, claimed by reply [P\*].
- "many of the statements are missing some basic hypotheses, such as measurability … Part of the task of formalizing is to determine the
  necessary side conditions" (Tao); a task "previously incorrectly marked as done" [P\*].
- "Blueprint works really well to break up the project into lots of chunks of small to medium difficulty"; the "technical 'obvious'
  steps" took longest; Massot: "if you are Peter Scholze or Terence Tao you can… instantly get 15 people working on it. It simply doesn't
  work otherwise" [P\*].

### 2.3 The Equational Theories Project (Lean 4; Sept 2024 to 14 Apr 2025)

Read: arXiv 2512.07087v2 sections 1, 4, 11, 14 [P] https://arxiv.org/html/2512.07087v2 .
- **Goal and size.** All 22,028,942 implications among 4,694 magma laws determined and formalised; 8,178,279 true; "over fifty
  contributors"; launched September 2024, goal reached 14 April 2025 [P].
- **Leaves were minimised by structure.** With transitivity and duality "only 10 657 (0.13%) of the positive implications needed a
  direct proof"; brute force over magmas up to size 4 refuted 13,632,566 implications (61.9 %) with 524 magmas in 165 CPU-hours; the
  hardest anti-implication took "several months" and "just over 4000 dedicated lines" [P].
- **No blueprint in advance**: "there was no clearly known pen and paper proof"; progress came as contributors "uncovered some
  structural ideas or heuristics that helped ATPs solve one or more pairs of laws" [P].
- **Coordination.** PFR-style manual claiming "involved a lot of manual and time-consuming management"; ETP used a GitHub kanban where
  organisers propose tasks, "The CI ensured that at most one contributor could claim a task at any time", and CI ran `lean4checker`
  and `lean4lean`; the method "has since been adopted by ... Fermat's Last Theorem" [P].
- **Statements.** A flawed formal statement makes "a correct and verified proof ... mathematically meaningless ... the only check
  against mistakes in this area come from human review"; buggy non-Lean tools can produce "spurious conjectures that misguide
  contributors" [P].
- **Automation vs humans and LLMs.** ATPs "were significantly more effective ... and the project largely moved away from the use of such
  LLMs" [P]. Early ATP use may have pre-empted "more interesting human-readable proofs" [P].
- **Lessons stated** [P]: "A clearly stated primary goal, with an end condition and precise numerical metrics"; "A highly modular project
  ... without needing to understand or rely upon other contributions"; "Variable levels of difficulty, and the amenability to partial
  progress"; "it really helps to have a maintainer structure in place before the project begins" (an early duplicate of Mathlib's free
  magma was never refactored; one file for all equations became excessively large).

### 2.4 Imperial FLT project (Lean 4; 2024-2029) [P\*]

Sources: https://leanprover-community.github.io/blog/posts/FLT-announcement/ , https://github.com/ImperialCollegeLondon/FLT .
- EPSRC EP/Y022904/1, £934,043, Oct 2024 to Sep 2029; about 58,800 lines and about 70 contributors by 2026-11-11 [P\*]. Route
  "planned out essentially entirely by Richard Taylor", adjusted for what is "easy or hard to do in Lean" [P\*].
- Unit: one GitHub issue per blueprint node on a dashboard (`claim`, `disclaim`, `propose #PR`), plus graduate-level "mini-projects"
  aimed at Mathlib; "This project will start everywhere at once" [P\*].
- Freezing: "A preliminary early goal will be to *state* all of the major claims which we shall initially be assuming";
  `axiom knownin1980s {P : Prop} : P` only for claims provable on paper from pre-1990 results, with a sketch in comments [P\*].
- A lemma in Roby's divided-power theory "seems to be incorrect"; cause: "the poor job which humans do of documenting modern mathematics"
  [P\*]. On AI (2026): it "still does not seem to be capable of reliably autonomously formalizing definitions correctly" [P\*].

### 2.5 leanblueprint, sphere eversion, Carleson [P\*]

- **leanblueprint** (https://github.com/PatrickMassot/leanblueprint ): `\lean{}`, `\leanok` (a manual claim), `\uses{}` (on a
  statement: needed to state; on a proof: needed to prove), `\notready`; colours separate stated, can-state, proved, can-prove (all
  dependencies done); the leader issues work by pointing at can-prove nodes [P\*].
- **Sphere eversion** (arXiv 2210.07746): blueprint written first "to … allow contributions from people who did not know the area";
  dependency graph "based on manual dependency declarations"; "we continuously edited the blueprint … to cater for minor changes in
  strategy" [P\*].
- **Carleson** (arXiv 2405.06423; June 2024 to July 2025): "about 180 tasks… Most tasks were to formalize the proof of a single lemma";
  about 42,000 lines; statements of all lemmas complete only after about 11 months; "only a handful of times that we had to change the
  statement of one or more lemmas"; one lemma found "unprovable" and repaired [P\*].

### 2.6 Mathlib at scale [P\*]

Source: "Growing Mathlib" https://arxiv.org/abs/2508.21593 ; queueboard; port status page.
- 139,978 definitions, 293,704 theorems, 772 contributors; 28 maintainers, 63 reviewers; 2,762 open PRs on 2026-11-11, 651 awaiting
  review, 430 labelled LLM-generated [P\*]. AI policy in [B §B4].
- **Lean 3 to 4 port**: one PR per file in import order; a script listed files whose dependencies were ported, ranked by dependants; a
  wiki recorded claims; ported mathlib3 files marked "THIS FILE IS FROZEN"; "mathlib4 wins" on conflicts; about 10 months, "roughly a
  dozen files per day"; 3,163 port PRs from 97 accounts, top 10 opening 65 %; over 5,000 "porting notes" of debt [P\*].
- "If keeping up with the latest Mathlib changes is too onerous, contributing results back to Mathlib may become impossible" [P\*].

### 2.7 Flyspeck (HOL Light + Isabelle; 2003-2014) [P\*]

Source: Hales et al., https://arxiv.org/abs/1501.02155 .
- 22 authors, 39 people credited; earlier estimate "about 20 work-years"; nonlinear inequalities about 5,000 processor-hours [P\*].
- Four parts joined by one interface theorem, `the_nonlinear_inequalities /\ import_tame_classification ==> the_kepler_conjecture`;
  inequalities split into more than 23,000 parallel pieces re-imported only on an MD5 match of canonical form and history, which also
  checked "no pieces were overlooked" [P\*].
- "the blueprint and the formalization were developed together, with numerous revisions"; persistent random identifiers linked text and
  code because numbering kept changing; one change to the definition of tameness grew the enumeration from 2×10⁷ to 2×10⁹ graphs [P\*].
- "every new concept comes at a cost: libraries of lemmas must be developed to support each concept"; "the chapters of the blueprint have
  been made as independent from one another as possible"; the hand translation Isabelle→HOL Light is "our single greatest vulnerability"
  [P\*].

### 2.8 Odd Order and Four Colour (Coq) [P\*]

- **Odd Order** (https://inria.hal.science/hal-00816699/document ): six years, 15 authors, "more than 150,000 lines ... roughly 4,000
  definitions and 13,000 theorems"; libraries "almost 80 percent of the total length"; files mirror the two books' sections; "the most
  time-consuming part of the project involved getting the base and intermediate libraries right"; "systematic consolidation phases
  performed after the production of new material"; statement check by a "stripped" restatement in bare Coq [P\*].
- **Four Colour** (Gonthier; https://www.ams.org/notices/200811/tx081101382p.pdf ): about 60,000 lines, essentially one author,
  2000-2005; begun because of the question "was the statement of the correctness proof (the specification) itself correct?"; theories
  "tended to rely on slightly different collections of facts", forcing months of refactoring [P\*].

### 2.9 The Isabelle Archive of Formal Proofs [P\*]

- 1,053 entries, 616 authors, about 332,900 lemmas, 5.6 million lines (https://www.isa-afp.org/statistics/ , 2026-11-11) [P\*].
- Maintainers "evolve all entries to be up to date with the current Isabelle development version"; interfaces should be "mostly
  monotone", a major non-monotone change needs a new entry [P\*] https://www.isa-afp.org/submission/ .
- Huch & Wenzel (ITP 2024): full build 4-8 h on a high-end server, about 36 min distributed; "One three-line locale interpretation costs
  about 50 h of CPU time"; "it has become increasingly difficult to change Isabelle libraries significantly" [P\*]. Luan et al. (FSE
  2025): 12,079 compatibility issues re-running old entries on new releases, "Undefined fact" 50.0 % of them, Sledgehammer effective at
  repairing terminal proofs [P\*].

---

## 3. Comparison across projects

| Project | Prover | Unit of work | Who partitions | Statement freezing | Coordination | Size | Workers | Duration | Cost (basis) |
|---|---|---|---|---|---|---|---|---|---|
| Prove2Me missions | Lean 4 | theorem card | agents; captain fixes goal, defs, milestones | immutable; fix = new card | import DAG, search, chat; no merge | 17-151k | 3-9 agents | 7-16 d | $200-600 (subscr.) |
| Anthropic FLT | Lean 4 | card | agents; human goal statement | immutable; peer truth checks | statement DAG; per-card compile; global recheck | 13M lines, 29,511 thms | dozens | 11 d | ~6 B output tokens |
| Gloeckle swarm | Lean 4 | sketched `sorry`; issue; small PR | sketcher agents; issue tracker | editable; math-review gate | git, review agents, single merge queue | 130k, 340 targets | 30,046 runs | 7 d | ~$100k (API est.) |
| AutoformBot | Lean 4 | one statement or one fix | orchestrator agent | editable; judges + tags | DAG, racing, bisecting merge queue | 484k, 26 books | thousands | ~1 wk/book | 183 B weighted tokens |
| Gauss PNT / packing | Lean 4 | undisclosed | human blueprint or paper | human main theorem | thousands of agents | 25k; 60k; 180k | undisclosed | 3 wk; 5 d; 2 wk | undisclosed |
| OpenAI library | Lean 4 | per result | undisclosed | Comparator challenge | one library | 163,096 files | undisclosed | 2026 | undisclosed for Lean |
| Munkres Isabelle | Isabelle | textbook result; `sorry` step | one agent, book order | bulk phase, then proofs | single agent; rule file | 85k, 806 results | 1 agent | 24 d | $160 subscr. / $8,895 API |
| Megalodon topology | Megalodon | theorem with `admit` | one agent | none | admit-status script | ~130k | 1 agent | 2 wk | ~$100 subscr. |
| Just Type It | Isabelle | whole development | agent | human review rounds | n/a | ~2k each | 1 agent | days | ~$140 each (API) |
| Grothendieck | Lean 4 | whole proof | agent from human outline | human headline | review checklist | ~5k | 1-2 agents | 9 d + 3 wk | n/s |
| Formal Conjectures | Lean 4 | problem statement | contributors | expert review, tests, prover sweeps | PRs | 2,615+ stmts | community | since 2025 | n/a |
| LTE | Lean 3 | lemma; sorried definition | Commelin | specs before implementations | Zulip; sorries | ~91k | ~12+ | 19 mo | n/s |
| PFR | Lean 4 | blueprint node | Tao | front-loaded, then corrected | Zulip claim lists | ~11k | 20-30 | 3 wk | n/s |
| ETP | Lean 4 | task card (class of implications) | organisers | fixed by problem | kanban, CI one-claimant | 22M implications | 50+ | 7 mo | 165 CPU-h one sweep |
| Imperial FLT | Lean 4 | issue per node; mini-project | Buzzard (route: Taylor) | assumed claims stated first | dashboard claims | ~59k | ~70 | 2024-29 | £934k grant |
| Carleson | Lean 4 | single lemma (~180) | blueprint authors | complete at ~11 mo | Zulip lists | ~42k | ~36 | 13 mo | n/s |
| Mathlib port | Lean 3→4 | one file | script, import order | ported files frozen | wiki claims, bors | ~1.05M lines | 97 openers | 10 mo | n/s |
| Flyspeck | HOL Light + Isabelle | chapter; inequality piece | Hales | co-revised; persistent IDs | interface theorem; hashed import | 14k+ thms | 22-39 | ~11 yr | ~20 work-yr est. |
| Odd Order | Coq | book section | team | library layers | consolidation phases | 150k | 15 | 6 yr | n/s |
| Four Colour | Coq | theory/program | Gonthier | ~200-line trusted statement | n/a | 60k | 1-2 | 5 yr | n/s |
| AFP | Isabelle | entry | authors | "mostly monotone" | maintainers evolve entries | 5.6M | 616 authors | since 2004 | build 4-8 h → 36 min |

n/s = not stated. Unit costs [derived]: Gloeckle about $300 per target and 4,300 output tokens per line; FLT about 200,000 output
tokens per final-tree theorem; Munkres about 3,300 output tokens per result (excluding 17.2 B cache reads); AutoformBot about 64 M
weighted tokens per formalised target. Models, counting and target size differ; the spread (four orders of magnitude) is the point.

---

## 4. Lessons for AutoDecompose

1. **Make the statement the unit; post it before any proof; make it immutable; parents are sketches importing children.** In Isabelle:
   one theory per lemma with explicit imports, a parent theory importing its children, and a correction posted as a new theory, never an
   edit. Evidence: Property 1 and the `gotsman_linial` repair (1.1); FLT failing until it moved to a statement DAG (1.2); LTE's sorried
   definitions as non-blocking debt (2.1); Flyspeck's interface theorem (2.7); frozen port files (2.6); AFP's monotone interfaces (2.9).
   Confirms the research note's Section 6, consequence 1.

2. **Verify Property 1 globally, not only per node**: each proof's statement matches its node exactly; the import graph is acyclic and
   grounded; the composed tree has no `sorry`, oracle or `skip_proofs`. Evidence: Prove2Me checks each card against sorried children,
   and Anthropic ran exactly these three checks before claiming FLT (1.2); AutoformBot found sorries and axioms that "propagate silently"
   (1.4). Extends survey B rule 16.

3. **Deduplicate statements when they are posted, by canonical form.** Normalise (bound names, hypothesis order, abbreviations), look up
   the problem's store, and run `solve_direct`; record the duplicate rate as a metric. Evidence: isolated immutable cards in FLT gave two
   in five repeated statements and a lemma in over 300 files (1.2); triplicate definitions in the swarm and Munkres (1.3, 1.7); AlphaProof
   Nexus's deep-hash goal cache (1.9); Prove2Me's search-before-submit (1.1).

4. **Check every new statement before spending proof effort, by computation, not argument**: type-check; `nitpick` and `quickcheck`;
   test lemmas evaluating any new definition on small cases; then parent sufficiency (the parent builds with the child as `sorry`).
   Evidence: FLT's truth checks "caught several false statements early" and a reviewer who argued was beaten by one who "computed a case"
   (1.2); Formal Conjectures' 23.8 % tests and canary variants, AlphaProof Nexus's first-terms lemmas (1.9); LTE's `examples/` (2.1). This
   is research-note rule 4, with project-scale evidence that this is where defects are caught.

5. **Do not let decomposition rules invent definitions; treat any new `definition` as a flag for audit.** At Putnam grain HOL, HOL-Library
   and HOL-Analysis vocabulary should suffice. Evidence: 61 of 62 agent definitions poor (1.8); weak `is_topology_on` (1.7); Bender-Knuth
   wrong twice, identity placeholders, oversimplified manifolds that "contaminate many dependent statements" (1.3, 1.4); a locale assuming
   facts about an undefined constant (1.7); Buzzard (2.4); Prove2Me audits definitions with the core (1.1).

6. **Score decomposition correctness as true + well-typed + sufficient for the parent; require faithfulness only at the root and at
   human-fixed milestones.** Evidence: Prove2Me's soundness rests on the audited core, intermediate lemmas "matter only insofar as they help
   close audited goals" (1.1); FLT's restricted "Ribet" serves the proof but not as a citation (1.2); agents shape lemmas to their consumer
   (1.7, 1.8). Only "true" and "sufficient" are machine-checkable before proof; measure them separately.

7. **Use the grain the projects converged on: one statement per task, reviewable in one read.** Evidence: AutoformBot's "at most one
   mathematical statement or one specific fix" (1.4); PRs of "a few hundred lines" (1.3); Carleson's 180 single-lemma tasks (2.5); PFR's
   "chunks of small to medium difficulty" (2.2); Munkres' helpers and "decompose the step into finer have blocks" on hammer failure (1.7);
   "a proof too expensive to check is usually a proof that should be decomposed" (1.8). Consistent with research-note rule 2.

8. **Exploit problem structure to shrink the leaf count before handing out work.** Evidence: ETP formalised 0.13 % of positive implications
   and refuted 61.9 % of pairs with 524 small magmas in 165 CPU-hours before human work (2.3); Flyspeck split inequalities into 23,000
   machine pieces, not human tasks (2.7). Rules should prefer decompositions whose leaves are uniform (one template, many instances) so one
   hammer call or one student prompt covers a class.

9. **Dispatch from the dependency DAG; never requeue blocked work blindly.** A blocked report adds an edge or a decomposition request, not a
   retry. Evidence: the swarm names missing dependency tracking as a cost overrun and spent half its input tokens on aborted agents (1.3);
   without re-planning AutoformBot plateaued at 64 % (1.4); Anthropic credits the DAG with "mitigating memory degradation" (1.2); Urban's
   admit-status script (1.7); leanblueprint's can-prove colour (2.5).

10. **Keep the global role (decomposer, reviser) in a fresh context fed by summaries; keep students local.** Evidence: "orchestrator fatigue"
    fixed by fresh task-scoped analysers (1.4); one-orchestrator decomposition failed on "limited context handling" (1.3); agents fix local
    checklist items, not global design (1.8), and provers "did not investigate globally" (1.3). Extends research-note rules 6 and 7.

11. **Turn student failures into decomposition requests, not retries.** Evidence: escalations, "particularly decomposition requests ...
    surface false axioms and suggest decomposition strategies"; without the trace analyser workers "repeat the same mistakes"; "never retry a
    failed task with an identical prompt" (1.4). Consistent with survey B rule 8.

12. **Budget verification per leaf, beside tokens, and forbid styles that move search into checking.** Evidence: 31.5 h on 24 cores for one
    library, 1 % of files a quarter of the time, `decide +kernel` 10,668 times denser than in Mathlib (1.6); 11,700 FLT files raised heartbeat
    limits and the build takes six hours on 96 cores (1.2); Munkres' 120 s session limit and 4-5x from a heap split (1.7); an AFP locale
    interpretation at about 50 CPU-hours (2.9). The Isabelle analogues to watch are, in my opinion, evaluation-based methods (`eval`,
    `code_simp`, `normalization`) and unbounded `auto` in a large simpset, which Munkres had to stop by rule.

13. **Report a cost curve, not a cost; expect a heavy tail.** Plot leaves closed against cumulative tokens and stop at a declared marginal rate.
    Evidence: AutoformBot stopped where "each new success required exponentially more compute", per-book costs 586 M to 45,384 M (1.4); ETP's
    last implications took months each (2.3); Prove2Me reports totals only (1.1).

14. **Count tokens, not dollars.** One Munkres run was $160 on a subscription and $8,895 at list price (1.7); Prove2Me warns its two cost bases
    are incomparable (1.1). Tokens per closed leaf is the right currency; quote literature dollars only with their basis.

15. **The deferred experiment has one precedent and an open gap.** AutoformBot held Opus 4.6 fixed and removed one component at a time at 600 M
    tokens (77 % vs 51-64 %); AlphaProof Nexus compared four agent designs by dollars per solved problem (1.4, 1.9). Neither is in Isabelle,
    neither works at Putnam-leaf grain, and neither varies the decomposition policy (rule-based vs free). That comparison is the one
    AutoDecompose can make first.

16. **Fix the checkers and conventions before scaling workers.** Evidence: "it really helps to have a maintainer structure in place before the
    project begins" (2.3); the swarm retuned roles live and relaunched several times (1.3); Munkres' rule file needed eight revisions (1.7).
    Here the "maintainers" are the rule set, the statement checker (rule 4) and the global verifier (rule 2); a measured run made before they
    are stable measures their debugging.

17. **Do not use automated faithfulness judgement as the only statement check.** Evidence: three LLM judges still left "the hardest statements
    ... not formalized faithfully" (1.4); a misalignment survived repeated human reviews (1.7); a Lean-as-judge audit found about 43 % of proved
    statements faithful (cited by Prove2Me, [S]). Prove2Me's read-back (Lean to prose by an agent that has not seen the source) turns the
    human check into a comparison of two statements and suits the root and any milestone (1.1).

---

## 5. Gaps and unverified items

- **Prove2Me**: no per-mission tokens, failure accounts, duplicate or defect counts; Section 4.1 has no measurements. The "43 % faithful"
  figure (Bourigault et al., arXiv 2605.28365) was not read [S].
- **Gloeckle swarm**: no merge-conflict rate; the $100K rests on an assumed cache ratio (their Appendix A); the 3-10x saving is projected.
- **Anthropic FLT**: agent count ("dozens") and per-agent time not given; tokens are output only; duplicate and preamble statistics come from a
  Claude-written assessment quoted by Anthropic, not an independent audit; `docs/limitations.md` and `docs/verification.md` returned 404 at
  the repository root.
- **Gauss**: no cost, agent counts or partition for any project; dimension-8 lines differ between README (20k → 60k, post-cleanup) and paper
  (20k → 80k → 60k).
- **OpenAI library**: how its Lean was produced is undocumented; the Navier-Stokes gap is [S]; eunomia's numbers are one machine and one
  revision.
- **Section 2 except ETP** rests on delegated reads [P\*]; Flyspeck's line count was not found; the Growing Mathlib venue is [U]; Tao dates LTE
  to "2019", conflicting with the December 2020 challenge; Buzzard's 2026 posts and the maintainers' joint post have no second source.
- **Isabelle evidence is thin**: Munkres, Megalodon (not Isabelle) and Just Type It are single-agent; no multi-agent Isabelle project, no Isabelle
  statement-object platform, and no measurement of theory-per-lemma build overhead were found.
- **No study** compares rule-based with free decomposition, or reports duplicate or statement-defect rates as a function of decomposition policy.

---

## Source index

AI-run projects
- Prove2Me https://arxiv.org/abs/2608.28433 (HTML https://arxiv.org/html/2608.28433v2 ); https://prove2.me/blog/fermats-last-theorem
- Anthropic FLT https://www.anthropic.com/research/formalizing-fermats-last-theorem ; https://www-cdn.anthropic.com/9e431dff043da6538d99d6c2d231b670aa3da263.pdf ; https://github.com/anthropics/fermats-last-theorem ; Buzzard https://xenaproject.wordpress.com/2026/09/04/flt-anthropic-has-beaten-me-to-it/ ; https://daplab.cs.columbia.edu/general/2026/09/09/fermats-last-theorem-agents.html
- Gloeckle et al. https://arxiv.org/abs/2604.03071 ; https://github.com/facebookresearch/repoprover ; https://github.com/facebookresearch/algebraic-combinatorics
- Rammal et al. https://arxiv.org/abs/2605.29955 ; https://github.com/facebookresearch/autoform-bot ; https://github.com/facebookresearch/atlas-lean
- Gauss https://www.math.inc/gauss ; https://github.com/math-inc/Sphere-Packing-Lean ; Hariharan et al. https://arxiv.org/abs/2604.23468
- OpenAI https://github.com/openai/math ; https://eunomia.dev/blog/2026/11/06/ai-lean-proof-checking-cost/ ; https://github.com/yunwei37/proofserve ; [S] https://redreamality.com/blog/ai-math-verification-lean-faithfulness/
- Isabelle and single-agent: Munkres https://arxiv.org/abs/2604.07455 ; Just Type It https://arxiv.org/abs/2604.15713 ; Urban https://arxiv.org/abs/2601.03298 ; Sorries Are Not the Hard Part https://arxiv.org/abs/2606.13925
- Statement defects: Formal Conjectures https://arxiv.org/abs/2605.13171 ; AlphaProof Nexus https://arxiv.org/abs/2605.22763

Human-run projects (delegated reads except ETP)
- LTE https://xenaproject.wordpress.com/2020/12/05/liquid-tensor-experiment/ ; https://xenaproject.wordpress.com/2021/06/05/half-a-year-of-the-liquid-tensor-experiment-amazing-developments/ ; https://leanprover-community.github.io/blog/posts/lte-final/ ; https://arxiv.org/abs/2309.14870 ; https://leanprover-community.github.io/blog/posts/lte-examples/
- PFR https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/ ; https://github.com/teorth/pfr ; https://leanprover-community.github.io/archive/stream/412902-Polynomial-Freiman-Ruzsa-conjecture/
- ETP https://arxiv.org/abs/2512.07087 ; https://github.com/teorth/equational_theories
- Imperial FLT https://leanprover-community.github.io/blog/posts/FLT-announcement/ ; https://github.com/ImperialCollegeLondon/FLT ; https://xenaproject.wordpress.com/2024/12/11/fermats-last-theorem-how-its-going/ ; https://xenaproject.wordpress.com/2026/05/15/formalizing-fermat-workshop/ ; https://xenaproject.wordpress.com/2026/10/16/how-to-formalize-all-of-mathematics/
- Blueprints https://github.com/PatrickMassot/leanblueprint ; sphere eversion https://arxiv.org/abs/2210.07746 ; Carleson https://arxiv.org/abs/2405.06423 , https://github.com/fpvandoorn/carleson
- Mathlib https://arxiv.org/abs/2508.21593 ; https://leanprover-community.github.io/queueboard/triage.html ; https://leanprover-community.github.io/contribute/index.html ; https://leanprover-community.github.io/mathlib-port-status/
- Flyspeck https://arxiv.org/abs/1501.02155 ; Odd Order https://inria.hal.science/hal-00816699/document ; Four Colour https://www.ams.org/notices/200811/tx081101382p.pdf , https://www.cl.cam.ac.uk/~lp15/Pages/4colproof.pdf
- AFP https://www.isa-afp.org/statistics/ ; https://www.isa-afp.org/submission/ ; Huch & Wenzel https://drops.dagstuhl.de/storage/00lipics/lipics-vol309-itp2024/LIPIcs.ITP.2024.22/LIPIcs.ITP.2024.22.pdf ; Luan et al. https://zhehou.github.io/papers/Empirical_Study_of_Compatibility_Issues_in_Isabelle.pdf
