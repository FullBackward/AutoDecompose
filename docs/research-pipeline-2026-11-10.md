# Two questions after pass 1: would a fixed hammer budget or a worked example help the forced arm, and what pipeline would the literature build?

Winston Ren's project, nearAI_Isabelle; this note by the harness author, 2026-11-10.
Moved to AutoDecompose on 2026-11-11 (it is the starting point of that repo); the
pass-1 and rep-1 analyses it cites stay in nearAI_Isabelle.
Evidence: pass 1 (`nearAI_Isabelle/docs/pass1-analysis-2026-11-10.md`) and three
literature surveys commissioned for this note, kept as appendices in `docs/research/`
(systems [A], practice [B], frontier results [C]), and three more added on
2026-11-11 for Section 7 (verification projects [D], mathematics projects [E],
decomposition procedures [F]); every borrowed claim below carries a bracketed
pointer into them, and from there to the primary source.

My conclusions, stated first and argued below. (i) A longer fixed sledgehammer
timeout will not make the forced arm solve more; this is more probable than not
from our own data and consistent with everything published. (ii) A worked
example in the prompt would buy syntax conformance and little else; I regard a
gain in proving power as not much better than a guess, and the literature holds
no measurement for a frontier model in Isabelle. (iii) Every system that proves
IMO or Putnam problems in 2025-26 has the shape our forced arm has, with three
parts we lack: a natural-language plan before the skeleton, an LLM prover (not
only a hammer) on each unfilled leaf in a fresh context, and a disproof check on
every new statement. The pipeline I propose in Section 4 adds those three, keeps
the Pool Server as the verifier, and is sized for the six IMO problems first.

Roadmap. Section 6 is an addendum on the owner's framing and Prove2Me; Section 7,
a second addendum, reads large proving projects and other harnesses' decomposition
procedures against the pipeline. Section 1 fixes terms and what the pass measured. Section 2 answers
question 1a and 1b. Section 3 distils the surveys into the design rules that
have evidence behind them. Section 4 proposes the pipeline and says what to
build first; Section 5 lists what would settle the open points. The surveys'
numbers are quoted with their budgets; anything self-reported or unverified is
marked so.

## 1. Terms and what pass 1 measured

A *leaf* is a terminal proof step (`by ...`, `.`, `..`, a `qed` with a method).
The *filler* is the server's `fill_sorries`: sledgehammer on every `sorry` of a
file, 30 s each, run inside one session. The *forced arm* lets the model write
only structure and `sorry`; the filler writes every leaf. The *plain arm* gives
the model a per-goal sledgehammer and no filler.

Pass 1 ran each IMO 2026 problem once per arm. Both arms solved P1, P4, P5 and
missed P2, P3, P6. The filler proved 1 011 of 1 393 sorries it tried (73 %);
the per-goal sledgehammer found 3 proofs in 67 calls and was not called at all
in the three plain solves. Two of the three plain misses were give-up loops
(the model stopped, the harness nudged, 489 and 425 times). One forced miss
overwrote its own file. These are harness facts, not facts about the arms, and
they are being fixed; the arguments below set them aside.

## 2. Question 1: two proposed improvements to the forced arm

### 2a. A fixed, longer sledgehammer timeout

*It would not help.* The evidence is of two kinds.

Our data. In the forced runs the model retried 35 sorries that had failed at
30 s with budgets of 60 to 300 s. One was proved (P3, at 180 s). Where a 60 s
round did prove many, 91 of 96 on P1, those were leaves the 30 s round had never
reached because its job cap expired, and they proved at the same rate (95 %)
the 30 s round achieved on its own leaves. Per problem, at 30 s the filler
proved 95 % (P1), 91 % (P4), 92 % (P5), 61 % (P6), 51 % (P3) and 37 % (P2) of
what it tried. The rate tracks the problem, not the budget.

The literature. Böhme and Nipkow's "Judgement Day" (IJCAR 2010) found that
three provers at 5 s equal the best single prover at 120 s, and that 240 s adds
0.4 points over 120 s [A §5]; Isabelle's 30 s default was set on that study
[B §A1]. The Sledgehammer manual's own diagnosis of a reconstruction that "runs
seemingly forever" is that the goal is too hard for metis, not that it needs
more time; its remedies are fewer facts, a simpler goal, or an Isar proof
[B §A1]. Every Isabelle LLM pipeline fixes its budget (10 s heuristics then
120 s in DSP and ProofAug; 30 s in HybridProver; 60 s in IsabeLLM) and none
reports a timeout ablation [B §D2]. Draft-Sketch-Prove's one hammer-side
ablation points the other way: running cheap tactics for 10 s *before*
sledgehammer doubled the hammer baseline, 10.4 to 20.9 % [A §5].

So the lever is not seconds but the goal. When a leaf survives one hammer
call, the published practice, and the practice that worked in our solved runs,
is to restate it: split it, add the facts it needs with `using`, or prove a
lemma above it. The forced P1 run did exactly this for its five survivors (0/5,
then 10/11, then 3/3). I would keep 30 s, and spend any extra prover time on
breadth: more sorries in parallel, and a cheap-tactics pass before the hammer
(Section 4, rule 5).

### 2b. A worked example in the prompt

*It would buy conformance, not proving power; the measurement that would
settle it does not exist.* Few-shot exemplars were found ineffective for GPT-4
proof generation (COPRA) and gave no gain for a model that already knows
Isabelle syntax (HybridProver: "the few-shot prompting provides no extra hints
to prove the theorem") [B §D1]. Random exemplars raised syntactic and lowered
semantic correctness in ProofBridge; models imitate the shape and hallucinate
the content [B §D1]. The one measured gain is from *retrieved similar proofs*
in the same development, IsabeLLM, 76 to 94 % on 16 lemmas [B §D1], which is
not our situation: an IMO proof has no near-identical neighbour. No frontier-
model agent of 2026 uses proof exemplars; they use rules, feedback and
retrieval (Numina, the minimal agent, Delta-Prover, the Trail of Bits and
lean4-skills skill files) [B §D1, §B3].

Our data agree on the cheap part. The leaf rule rejected one to five writes per
forced run, each a single turn, and the models complied at once; the rule's
cost is not where the forced arm lost. The forced arm lost time to scratch
tests of closers it could not write (29 min on P1), to a file used as a
scratchpad when the server's scratch runs timed out (P2), and to leaves no
hammer could close (P3, P6). An exemplar fixes none of these.

There is one thing an exemplar might teach that rules do not: *granularity*.
Aristotle restructures each informal proof into lemmas that "individually have
very short proofs" and, on failure, asks whether the proof was broken down into
"sufficiently granular lemmas" [F §5.1]; Delta-Prover solved IMO 2019 P1 as 83 subproblems of about four calls
each after 1 024 monolithic attempts failed [A §4.2]. Our forced misses have
exactly the coarse-leaf signature (P3's late rounds: 0/3, 0/4, 1/9, 1/6). A
skeleton exemplar of the right grain could move that; I put it at "it might
well be", and it is cheap to test (Section 5). It is also a change to the arm,
so it belongs in a new arm or a flagged variant, not in `skeleton_forced` as
run, and the owner's standing decision against prompt hints about goal binding
is untouched by it: granularity is a different matter from binding.

## 3. What the literature has evidence for

I list only rules with a measurement or an author's stated ablation behind
them; rules that are merely common are left out. The surveys' section numbers
follow each rule.

1. **Natural-language plan first, then a skeleton of `sorry` lemmas, then
   per-lemma proving with verifier feedback.** This is the shape of every
   2025-26 system at IMO or Putnam level: Seed-Prover 1.5, Aristotle, Hilbert,
   Goedel-Architect, MechMath, Aleph [C §3]. The cleanest ablation is
   Goedel-Architect on DeepSeek-V4-Flash, the model family we use: direct
   proving 6.5 %, a tool-using single prover 54.5 %, the blueprint 75.6 %, the
   blueprint seeded by a natural-language proof 88.8 % of PutnamBench [C §3].
   Draft-Sketch-Prove measured the Isabelle version in 2022: forcing the model
   to write complete proofs instead of leaving gaps cost 9 to 10 points [A §1.2].
2. **Lemmas with very short proofs; shallow and wide, not deep.** Aristotle and
   Delta-Prover as above; Hilbert's gain is almost all at depth two (75 to
   98.4 %) and Seed-Prover 1.5 caps depth at four for contests [A §6(2)].
3. **Repair with placeholders beats regeneration at equal budget.** MechMath on
   Putnam 2025 A1-A4 at 128 calls each: discard-and-retry 0/4, whole-proof
   repair 3/4, "sorrify" the failing block and solve the holes 4/4, at a third
   of the cost [C §3]. Delta-Prover: 95.9 % against 49.1 % for best-of-N at the
   same 16 384 calls [A §4.2]. Goedel-Prover-V2: the compiler's error text is
   the repair input whose removal hurts most [B §C1].
4. **Disproof as a first-class signal.** Goedel-Architect found a false
   sub-lemma on 292 of 672 problems; Seed-Prover 1.5 routes a disproved lemma
   back to sketch revision; Aristotle's formalisation step caught its informal
   draft confusing strictly, weakly and eventually decreasing [C §3; F §5.1]. In Isabelle this is `nitpick` and
   `quickcheck`, with "potentially spurious" treated as a hint [B §A3].
5. **A cheap-to-expensive automation ladder, and one hammer call per goal
   shape.** `try0`-class methods in seconds, heuristics at about 10 s, then one
   sledgehammer call; after that, change the goal [B §E rule 5, §D2; A §5].
6. **Refine the global blueprint, do not recurse on the failing lemma.**
   Goedel-Architect's stated reason: recursion "can inefficiently loop on
   dead-end strategies" [A §4.7].
7. **Fresh contexts and a cache of verified lemmas, not a growing
   transcript.** Seed-Prover 1.5 found 32 to 64 k-token trajectories net
   negative and re-injects proved lemmas on restart; Numina moved stuck lemmas
   into subagents because "very long contexts degrade instruction-following";
   h1 measured "context rot" (raising turns per reflection from 10 to 200
   drops Putnam100 from 72 to 60 [F §6.3]);
   the minimal agent's self-managed notes gave +7 % at -20 % cost [B §C4; C §4].
   Our plain P2 at 741 k tokens per call and the 1.3 GB P3 transcript are the
   same failure.
8. **Budget by LLM attempts adaptively, not by hammer seconds.** The only
   measured adaptive policy decides continue-versus-restart from the diversity
   of errors across failed attempts: 28.9 % less cost at equal accuracy
   [B §C5]. Stop a target when consecutive failures repeat the same error.
9. **Verify a frozen artifact cold; check statements, not only sorries.**
   Statement defects are now a first-class failure (Aleph's 15 counterexamples
   to PutnamBench statements; 398 certified benchmark defects in "Faults in Our
   Formal Benchmarking"; "Sorries Are Not the Hard Part") [C §2.3-2.4, §4].
   Our `verified.thy` plus cold rebuild already does the first half.
10. **Verifier throughput is engineering, not plumbing.** Kimina's import-keyed
    warm REPLs gave 1.94x; snapshotting removed the 60 s import per branch;
    Lean now checks slower than models write [C §4]. The Pool Server's warm
    sessions and `fill_sorries` are the Isabelle analogue; the pass showed the
    forced arm spending 60 to 70 % of its wall clock in them.
11. **Geometry needs a geometry engine.** Seed-Geometry and Yuclid solve in
    seconds what general provers spend hours on; Goedel-Architect calls IMO 2025
    P2 "out of reach for a general-purpose Lean prover" [C §3-4]. Our P2 imports
    HOL-Analysis and was the worst cell on both arms.
12. **No cross-problem lemma library.** LEGO-Prover's library showed no direct
    reuse and its gains vanish at equal compute; within-problem caching pays
    [B §C7].

Two findings bear on this project in particular. First, the counter-trend:
h1 (Meta FAIR, Oct 2026) matches or beats the enforced-decomposition systems
with a minimal harness, provided the verifier interface is tight (persistent
file, per-edit feedback, REPL, goal view, everything imported), and the
upstream of this repository reached 672/672 on PutnamBench with DeepSeek V4, a
bash tool and nudging, at $0.17 a problem [A §4.7; C §3]. A strong enough
model self-decomposes. The open question for DeepSeek on IMO problems is
whether it is strong enough, and pass 1 says: on P1, P4, P5 yes, on P2, P3,
P6 no, on either arm. Second, the Isabelle-specific gap: no published Isabelle
result exists on IMO 2025 or 2026, the per-goal sledgehammer has no competition
result above 3 of 640 on PutnamBench, and every Isabelle gain since 2022 has
come from sketches with hammers closing leaves [C §5]. Our plain arm is the
2022 shape; our forced arm is the 2025 shape minus its LLM prover.

That last clause is, in my opinion, the most useful thing the surveys say
about pass 1. In Seed-Prover, Hilbert and Goedel-Architect the thing that
closes a lemma is an LLM with tools, of which the hammer is one. In our forced
arm the only thing that may close a leaf is sledgehammer. The filler's
proof-rate profile (above 90 % on well-stated leaves, near zero on the leaves
that decided P2 and P3) is Draft-Sketch-Prove's 2022 observation that human
proofs "leave gaps too difficult for automated provers" [A §6(2)]. The
published fix is a prover below the filler, not a longer hammer.

## 4. A pipeline for hard problems in Isabelle, built on the Pool Server

Let me state the design as a sequence of stages, then the parallelism, then
the budgets, then the order in which to build it. The aim is a pipeline that
can be left running on the six IMO problems for a day and scaled to a Putnam
set by adding workers; everything is textual on the harness side, with the
prover untouched, as the owner requires.

**Stage 0, plan.** The model writes an informal proof as a numbered list of
lemmas, each stated so that it should have a short proof. No Isabelle yet.
(Rule 1; Goedel-Architect's 75.6 to 88.8 % is the gain from this stage alone.)

**Stage 1, blueprint.** The model turns the plan into a theory file: helper
lemma statements with `sorry`, the frozen targets with structured skeletons
whose leaves are `sorry`, dependencies implicit in order. The harness accepts
the write only if the file parses and every frozen statement is present (the
write-time check pass 1 showed we need). Every new statement is run through
`nitpick` and `quickcheck` in a scratch session; a genuine counterexample is
returned to the model as "this lemma is false", and the blueprint is revised
before any proof effort (rule 4).

**Stage 2, fill.** The filler runs once over all sorries, 30 s each, preceded
by a cheap-tactics pass (`try0`-class methods, a few seconds) so sledgehammer
is spent only on what they miss (rule 5). This is `fill_sorries` as it exists,
with the heuristics pass added on the server or in the harness. In pass 1 this
stage alone closed 90 % of leaves on the solved problems.

**Stage 3, prove the survivors, one per fresh context.** Each surviving
`sorry` becomes a self-contained lemma with its statement and the facts in
scope, handed to a *leaf prover*: a fresh model context with the scratch tools
(`isabelle_run_code`, `multi_attempt`, `find_theorems`, per-goal sledgehammer)
and a budget of, say, 20 turns, whose output is either a proof text that
passes in isolation or a decomposition into further `sorry` lemmas (rules 2, 3,
7). The leaf prover may write closers; the leaf rule applies to the blueprint
author, not to it. Depth is capped at three. Proofs that pass are written back
into the file; the main context never sees the leaf prover's transcript, only
its verdict and a one-line summary.

**Stage 4, revise the blueprint.** The main context receives the list of
proved and unproved lemmas with their error summaries, and revises the
blueprint globally: restate coarse lemmas, add helpers, drop a wrong strategy
(rule 6). Then Stages 2 to 4 repeat. Verified lemmas are kept verbatim across
revisions and re-injected after any context reset (rule 7).

**Stage 5, verify.** As now: `completed()` builds a frozen copy cold, checks
statements, sorries and escape hatches, and the result is `verified.thy`.
`disproved()` stays as the exit for a false formalisation.

*Parallelism.* Stage 3 is the fan-out: one leaf prover per surviving sorry,
each on its own scratch session, as many in flight as the server's session
pool allows (six today). Stage 2 already runs inside one session; a second
form of parallelism, several fill jobs on disjoint sorry sets, would need the
server to split a file, which I would defer. Across problems, one worker per
problem as now. The queue and driver stay as they are.

*Budgets and stopping.* Per problem: a wall clock and a token cap, with the
cap logged against outcome so the report gives cost per solve (rule 8, and the
surveys' $5.80 to $74 per Putnam problem as calibration [C §4]). Per leaf: 20
turns, then decomposition or surrender. Per attempt: three consecutive model
turns without a tool call end the attempt as `gave_up`; a blueprint revision
whose error summary repeats the previous one verbatim is a second trigger. The
nudge stays for a single stray stop, which upstream found valuable [A §4.7],
but it no longer runs to the wall.

*What to build, in order.* (i) The three defect fixes from pass 1: give-up
detection, write-time protection of frozen statements, the 90 s clamp and a
worded result on sledgehammer timeouts. Without these, nothing measured in the
next pass is clean. (ii) Stage 3, the leaf prover, as a harness-side
sub-attempt reusing the existing attempt machinery on a one-lemma theory. This
is the largest change and the one the literature backs most strongly. (iii)
Stage 0 as a required first turn, and Stage 1's `nitpick` check on new
statements. (iv) The cheap-tactics pass before the hammer, in the server's fill
job. (v) Context management: verified-lemma cache and reset. (vi) A geometry
path for P2 is beyond this project; I would record P2 as out of scope for a
general Isabelle pipeline, as Goedel-Architect did for its Lean counterpart.

*What this is not.* It is not a trained prover, a lemma pool across problems,
or test-time training; the surveys show those are what the IMO-grade systems
add on top, at 10 to 500 accelerator-days per problem [C §4], and nothing here
reaches for them. It is also not a bet against the minimal harness: if a
future model self-decomposes well enough, Stages 0, 1 and 4 collapse into the
model's own turns and the pipeline degrades to the plain arm with a leaf
prover. The design is chosen so that collapse costs nothing.

## 5. What would settle the open points

- **Timeout.** Already settled as far as our data can: 1 of 35 retries. A
  cheaper confirmation is to rerun the filler on the surviving sorries of the
  three forced misses at 30 s and 120 s from the final files; no model calls
  are needed.
- **Exemplar.** A controlled pair on the three solved problems and P3: the
  forced arm as run against the same arm with one worked skeleton of the right
  grain in the strategy text, three reps each; the outcome measures are fills
  proved on the first round and leaf-rule rejections. About 24 attempts.
- **Leaf prover.** Take the surviving sorries of P3 and P6 forced (five and
  six) as standalone lemmas and run a fresh-context prover on each with a
  20-turn budget. If none closes, Stage 3 is not where those problems are lost
  and the plan stage is; if several close, Stage 3 is the next build.
- **Give-up.** Reading the 490 stop turns of plain P3 would say whether an
  escalating nudge (new information, not repetition) could have restarted
  work; the MathArena result suggests error diversity, not count, is the
  signal to act on [B §C5].

## 6. Addendum (2026-11-10): the owner's framing, and Prove2Me

The owner's statement of the experiment, recorded here because it changes
what the arms are for. The question is what *automation at the proof-closing
step* buys a model: the human habit of writing the argument and calling
sledgehammer at the end, to save reasoning. The nearAI harness was chosen
because it is minimal, not because it is strong. Scaling is to be studied at
small scale, by decomposing a hard problem into Putnam-level pieces handed to
subagents ("students" with sledgehammer and the filler), with the
decomposition driven by rules drawn from verification practice, mathematics
and skill files rather than by free generation, so that it is less random and
more often correct. Putnam problems are the unit of the subagent task, not a
benchmark to beat. The three tasks: improve the filler; build and evaluate a
rule-based decomposition; formalise the scaling question.

Prove2Me (Chen, Marwaha, Lu, Yuen, Peng; arXiv 2608.28433, Aug 2026) is the
scaling reference the owner has in mind. What it says, read from the paper:

- *Naive sorry-filling does not scale* (their Section 4.1), for two reasons:
  every change to a lemma recompiles its downstream cone, and agents editing a
  shared file interfere, so the work cannot be atomised; centralised swarms
  pay for this with a serialised merge queue (Gloeckle et al.: about 30 000
  agents, $100 000, one textbook in a week).
- Their remedy is structural: a theorem is an immutable statement object
  (description, preamble, formal statement ending in `:= by sorry`); proofs
  are separate objects whose type must match; a *proof-sketch* is a proof that
  imports other, possibly still open, theorems, so the parent is verified
  exactly when its children are (their Property 1); a searchable corpus
  (Formalpedia); *milestones*, canonical lemma statements curated by a human
  captain, so that independent agents converge on one formulation instead of
  incompatible ones; disproof as a first-class submission; a discussion
  channel; a sub-agent "read-back" from Lean to prose for auditing.
- Their evidence is case studies, not a controlled experiment: four missions
  of 17 k to 151 k Lean lines by 3 to 9 agents on $200 to $600 of consumer
  subscriptions. They say plainly that model generation and harness are
  confounded in every row and that separating them "requires holding the model
  fixed and varying only the harness, which we leave to future work".

Three consequences for this project, in my opinion.

1. The statement-object model is the right unit for the subagent experiment,
   and Isabelle supports it directly: one theory file per lemma with its own
   imports, immutable once posted; a parent "sketch" theory that imports the
   children and proves the target from them; the glue check of Section 4
   becomes "the parent builds with every child `sorry`", and Property 1 holds
   because the final verifier refuses `sorry` anywhere in the cone. The Pool
   Server already gives one warm session per child.
2. Prove2Me's milestones are the social version of the rule-based
   decomposition the owner wants: canonical statements that stop agents
   diverging. Our templates would produce such statements mechanically, and
   their correctness is checkable before any proof is attempted. That is a
   claim Prove2Me cannot test and we can.
3. The controlled experiment Prove2Me leaves open, model fixed and harness
   varied, is exactly the shape of this project. At our scale the measurable
   quantities are the ones in Section 4's cost model: leaf closure by
   automation p, subagent success q, decomposition correctness r, and prover
   time per leaf; their swarm figures give the large-scale end of the curve.

## 7. Addendum (2026-11-11): what large projects and other harnesses say about decomposition

Surveys A to C studied systems that prove one competition problem at a time.
Two kinds of evidence were missing: projects that proved thousands of
statements with many workers, where decomposition, interfaces and cost have
been lived with for years, and the step-by-step procedures by which other
harnesses split a goal. Three further surveys supply them: large verification
projects [D] (seL4, AutoCorrode, CompCert, LLM work on verification
codebases), large mathematics formalisations [E] (Prove2Me and the FLT run on
it, the 30 000-agent swarm, AutoformBot, Munkres in Isabelle, LTE, PFR, the
Equational Theories Project, Flyspeck and others), and the decomposition
procedures of 33 published harnesses and six local ones [F]. Section 7.1 says
what the projects teach, 7.2 what the procedures teach, 7.3 what I would
change in Section 4, 7.4 what stays open, and 7.5 records corrections.

My conclusions, stated first. (i) The evidence supports rule-based
decomposition in a narrower form than the README's: *rules should produce
most child statements from the structure of the parent, and the model should
supply only the few statements that carry the idea.* Every large project that
worked divided the labour this way, and every measured gain from
decomposition in a harness came from a mechanical or template move, not from
free generation. (ii) Decomposition fails on statements, not proofs, so the
statement check of Stage 1 should become the centre of the pipeline and the
source of the correctness measurement r.

### 7.1 What the large projects teach

1. *At scale, most lemma statements are produced by rule.* In 2012 the seL4
   proofs held 22 000 lemmas stated by people and 95 000 once tool-generated
   ones were counted; `crunch` states one invariant-preservation lemma per
   callee and closes it with `wp` [D §1.1, §1.3]. AutoCorrode derives one
   weakest-precondition obligation per function contract and uses callee
   contracts as lemmas [D §2.2]; CompCert and CakeML fix one statement shape
   per compiler pass [D §4]. The analogue for a mathematical problem is the
   definitional and inductive structure of its statement: cases, induction
   steps, the unfolding of each defined constant.
2. *The expensive statement is the invariant, and it is fixed before the work
   fans out.* Invariants took 80 % of the effort of seL4's first refinement,
   and design-level work divided among people only "once the formulation of
   invariants had stabilized" [D §1.2, §1.6]. For a competition problem the
   invariant is the strengthened induction hypothesis or the key auxiliary
   statement: the part no rule can produce, and the part to check hardest.
3. *The unit of work has converged on one immutable statement, posted before
   its proof, with its imports explicit.* Prove2Me, AutoformBot, the swarm and
   the human blueprints all arrived at it [E §0, §3]. Anthropic's FLT run is
   the clearest case: its first attempts "quickly lost track of the project's
   state", and it succeeded after moving to Prove2Me's statement graph
   [E §1.2]. Immutability has a measured price there, since about two in five
   statements in the proof files repeat one made elsewhere [E §1.2];
   statements should be deduplicated when they are posted.
4. *Projects fail on statements, above all on definitions.* Of the 62
   definitions an agent made for the Grothendieck vanishing formalisation, its
   expert reviewers found one done correctly; the Isabelle Munkres has a
   topology predicate that is too weak; the swarm got one textbook definition
   wrong twice [E §1.3, §1.7, §1.8]. Extraction also creates false statements:
   23 of 241 seL4 lemmas that an LLM search failed to prove were false because
   the benchmark had dropped their assumptions when slicing them out of their
   files [D §1.9]. The projects that caught such errors early did it by
   computation, not argument (FLT's peer agents "caught several false
   statements early"; test and API statements are 23.8 % of Formal
   Conjectures) [E §1.2, §1.9].
5. *Leaves are short, and closing the short ones is easy to overvalue.* 41.5 %
   of 29 125 seL4 lemmas are one step and 86 % at most ten [D §1.4].
   Sledgehammer alone closes 40.3 % of seL4 theorems but 15.0 % of proof
   lines, and the best LLM system's 77.6 % of theorems is 36.2 % of lines
   [D §1.9, §5]. The bulk is closed by methods tied to the decomposition, not
   by the general hammer: about 21 800 `wp`-family calls in l4v, and
   AutoCorrode's Crush [D §2.3, §5].
6. *Statement size predicts proof size.* Matichuk et al. found proof size
   quadratic in the size of the formal statement, and Staples et al. found
   effort linear in proof size [D §1.5]. This gives a prediction we can test:
   tokens per closed leaf should grow roughly with the square of the leaf's
   statement size.
7. *Parallelism is bounded by the stability of interfaces, and checking is a
   cost.* Up to four people worked on one seL4 proof "without much conflict";
   more than five or six would have needed "a more serious effort in planning
   and synchronisation" [D §1.6]. The swarm spent about half its input tokens
   on agents later aborted, and its single merge queue choked [E §1.3]. One
   pass over OpenAI's AI-written Lean library took 31.5 hours on 24 cores
   [E §1.6].

### 7.2 What the other harnesses' procedures teach

[F] records the same eleven fields for every harness (trigger, proposer,
representation, granularity control, statement checks, sufficiency check,
limits, failure routing, reuse, parallelism, ablation). Six findings bear on
this project.

1. *Moves are of three kinds, and only two have evidence.* A mechanical move
   is computed from the proof text or the failure site (MechMath's Sorrifier,
   APOLLO, ProofAug); a template move is chosen by the model in a fixed shape
   whose obligations are computed (Delta-Prover's DSL, Minilang's ten
   operations, Goedel-Architect's blueprint, Hilbert's `have` sketch); a free
   move is whatever the model writes, typically an informal proof cut into
   lemmas. Every ablation of decomposition that [F] found measures a move of
   the first two kinds; the free moves have the weakest evidence and the
   clearest reports of waste [F §0, §8].
2. *The mathematical templates are everywhere and nowhere tested.* Case split,
   induction, both directions of an iff, a named witness and a calculational
   chain appear in every system's proofs, but no harness ablates them as moves.
   Minilang alone makes them its whole vocabulary, and it is measured against
   Isar, not against free decomposition [F §8]. This is the gap a rule-based
   decomposer can fill.
3. *Truth is checked late; sufficiency is checked cheaply.* Hilbert,
   Goedel-Architect, MerLean and Seed-Prover 1.5 test a lemma's truth only
   after the prover fails on it; the only formal checks before proof are
   Goedel-Code-Prover's quickcheck factor and Kimina's negation filter.
   Sufficiency, wherever it is checked, is checked by compiling the parent with
   the children as placeholders [F §9].
4. *Granularity is set by words.* "Individually have very short proofs"
   (Aristotle), "(nearly) trivial once its parent nodes are taken as given"
   (Goedel-Architect); the only measurable controls are Goedel-Code-Prover's
   operator-footprint reduction and Seed-Prover 1.5's reward [F §0].
5. *Shallow beats deep, global replanning beats recursion, and diagnosis has
   two labels.* Hilbert reaches 98.36 % at depth 2 and 98.7 % at depth 3;
   every harness that names a cause of failure uses "statement wrong" and "too
   hard or too coarse" [F §0, §5.2, §5.4].
6. *The usual control is not a null control.* h1's system prompt tells the
   model to "break it into lemmas, sketch the structure with sorry ... prove
   the pieces"; the humanize harness, and its Isabelle port, enforce no proof
   decomposition, and the port's Putnam 2023 B5 solve came from the model
   splitting the proof itself [F §1.1, §1.2, §6.3]. A comparison with either
   is a comparison of *suggested* with *enforced* decomposition.

### 7.3 Changes to Section 4

I would make five changes, each a consequence of the points above.

(i) *Split Stage 0 by who writes what.* The model writes the plan and the key
statements (the invariant of 7.1, point 2). Every other statement is produced
by rules: the templates of [F §10] rules 5-9 (a case split with its
exhaustiveness as a child, induction with its `arbitrary:` set as a parameter,
the two directions of an iff, `suffices` and named witnesses, one child per
link of a calculational chain) and the mechanical moves of rules 2-3 (sorrify
the innermost failing block; retry automation on the coarser goal before
asking the model). This also removes an inconsistency: Section 4 as written
has Stages 0 and 1 generated freely, while the README promises rule-driven
decomposition.

(ii) *A statement gate, in fixed order, before any proof effort:* parse and
type-check in the parent's context; `quickcheck`, then `nitpick` (a genuine
counterexample rejects, "potentially spurious" is logged only); extraction
fidelity (the hole the child came from closes by `using child by blast`);
sufficiency (the parent builds with every child `sorry`); deduplication by
canonical form and `solve_direct` against the problem's proved lemmas. The
gate's log is the measurement r, reported by cause: ill-typed, refuted,
unfaithful extraction, insufficient, duplicate, and, after the run, unused.
Before a proof exists "true" can only mean "not refuted", and r should say so.

(iii) *Each template carries its closing method, and rules define nothing.* An
induction template emits, say, `induct ...; auto simp: ...` for its routine
cases, and only the residue goes to the filler and the students [D §5 rule 7].
A rule may not introduce a `definition`; a new definition from any source is
flagged for audit [E §4 rule 5].

(iv) *Statement objects, dispatched from the graph.* One theory per lemma,
immutable once it passes the gate; a correction is a new theory. Students are
dispatched from the dependency graph, and only over frozen statements; Stage 4
replans globally and keeps proved nodes. The depth cap of three stands, though
Hilbert's curve suggests two would lose little.

(v) *Weigh what is closed, and time the checking.* Report tokens per closed
leaf beside the leaf's statement size, so that a harness closing only short
leaves does not look efficient [D §5 rule 13], and test the prediction of 7.1,
point 6. Log prover time per leaf beside tokens, and plot leaves closed against
cumulative tokens rather than quote one cost [E §4 rule 13].

These changes define the experiment that, in my opinion, the literature lacks:
with the model, the students and the filler fixed, compare three decomposition
policies, namely suggested (an h1-style prompt), free (an informal plan cut
into lemmas, as in Goedel-Architect) and rule-based (as above). The only
harness ablation at a fixed model I know of is AutoformBot's, 77 % for the full
system against 51 to 64 % with one component removed, and it does not vary the
decomposition policy [E §1.4].

### 7.4 What the surveys could not settle

- *The cost of a theory per lemma in Isabelle.* No multi-agent Isabelle
  project exists, and nobody has measured the build overhead of one theory per
  lemma [E §5]. It decides whether the statement-object model of Section 6 is
  affordable here, and it can be measured on the Pool Server without a model
  call: build a parent importing N child theories against the same lemmas in
  one file, for N from 10 to 200.
- *Decomposition errors by type.* No harness reports, per generated lemma, how
  many are false, ill-typed, insufficient or unused [F §9]. The gate of 7.3
  (ii) produces exactly this table.
- *Prove2Me's scaling argument.* Its Section 4.1, the case that naive
  sorry-filling does not scale, contains no measurements [E §1.1, §5]; Section
  6 above rests on that argument and on the swarm's experience, not on a
  number.
- *The value of the templates.* Whether rule-produced children close at a
  higher rate per token than free ones is untested anywhere [F] could find. I
  put a gain at "it might well be"; the three-policy comparison of 7.3 would
  settle it.

### 7.5 Corrections made on 2026-11-11

Survey F found three errors in this note, now corrected in place: Aristotle's
wording is "individually have very short proofs", not "each meant to have a
very short proof" (Section 2b); the slip Aristotle's formalisation caught was a
confusion of strictly, weakly and eventually decreasing (Section 3, rule 4);
and h1's context-rot figure is 72 to 60 as turns per reflection rise from 10 to
200, where the note had mixed two ablations into "69 to 60" (Section 3, rule
7). It found a fourth in survey B: the HybridProver figures 34.8 to 56.1 % come
from the paper's first version, whose procedure differs from the current one
[F §2.4]. Surveys A to C are left as written; [F §11] lists the discrepancies.

## Appendices

- `docs/research/survey-A-systems-2026-11-10.md`: about 45 systems, 2022-2026,
  with per-system fields, synthesis and source URLs.
- `docs/research/survey-B-practice-2026-11-10.md`: Isabelle and Lean
  automation practice, agent-loop lessons, prompting evidence, 19 design rules,
  each with its source; section F lists what could not be verified.
- `docs/research/survey-C-frontier-2026-11-10.md`: IMO 2025-26 results,
  PutnamBench state, the authors' own accounts of what solved the hardest
  problems, costs, Isabelle-specific work; section 6 lists unverified claims.
- `docs/research/survey-D-verification-projects-2026-11-11.md`: seL4 and its
  proof-engineering literature, AutoCorrode, LLM work on verification
  codebases, CompCert and others; 14 lessons in section 5.
- `docs/research/survey-E-mathematics-projects-2026-11-11.md`: Prove2Me, the
  FLT run on it, the 30 000-agent swarm, AutoformBot, Gauss, Munkres in
  Isabelle, and the human projects (LTE, PFR, ETP, Flyspeck, Odd Order, the
  AFP); a comparison table in section 3, 17 lessons in section 4.
- `docs/research/survey-F-decomposition-procedures-2026-11-11.md`: the
  decomposition procedure of 33 published and six local harnesses on eleven
  common fields; 18 candidate rules with their Isabelle form in section 10;
  discrepancies with A-C in section 11.
