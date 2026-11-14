# Sorry skeletons are the multi-agent protocol

| | |
|---|---|
| Kind | skill |
| Move | workflow |
| Language | markdown |
| Status | draft |
| Source | [trailofbits-skills](../../sources/trailofbits-skills/SOURCE.md) at `e4dd0bb5b155` |
| Licence | `CC-BY-SA-4.0` |
| Licence recorded | 2026-11-14T09:51:11Z |

## Intent

State the theorem-scale decomposition as an explicit multi-agent workflow:
one pass states the target and the lemmas written for it, together with their
API, as compiling `sorry` stubs; the statements are then frozen as interface,
and independent agents each discharge one stub with no shared context beyond
the file.

## The decomposition

### skill-text `sorry-skeletons`: [`plugins/writing-lean-proofs/skills/writing-lean-proofs/references/llm-techniques.md` lines 57-73](https://github.com/trailofbits/skills/blob/e4dd0bb5b15535f7c5a0834187dffba6ac37e4ff/plugins/writing-lean-proofs/skills/writing-lean-proofs/references/llm-techniques.md#L57-L73) ([local copy](code/plugins/writing-lean-proofs/skills/writing-lean-proofs/references/llm-techniques.md))

```markdown
## Sorry skeletons are the multi-agent protocol

The spec-driven decomposition described in the library-design reference is
directly an LLM
workflow: one agent (or one pass) states the target, its lemmas, and their
API as compiling `sorry` stubs; independent agents then discharge
individual sorries with no shared context beyond the file. This is exactly
how PFR ran ~20 human contributors in parallel — the proof assistant
verifies each contribution independently, so contributors need not
understand the whole. Rules:

- Every stub must compile before fan-out (`lake build` on the skeleton).
- A filled sorry must not change any statement — statements are frozen
  interface; if a statement is wrong, that is a design change, surfaced
  rather than silently patched.
- Prefer many small stubs over few large ones: the granularity criterion is
  "one agent can discharge one stub without global context".
```

How the parts fit. The workflow is a two-phase process. In the *statement*
phase one pass writes the target and its lemmas *together*, as `sorry` stubs
whose statements are the API — so the skeleton compiles before any proof
exists. In the *fan-out* phase independent agents discharge the individual
sorries, each reading no more than the file. Three rules hold the two phases
together: **compile-before-fan-out** (line 68) requires `lake build` on the
skeleton first, so no agent works against a statement that does not typecheck;
**frozen-statements** (lines 69-71) forbids a filled sorry from changing any
statement, so the interface the agents were handed is the interface that ships;
**many-small-stubs** (lines 72-73) sizes each stub by the criterion "one agent
can discharge one stub without global context", which is the skeleton with one
hole per bounded prover. None of the three rules names a concrete lemma: the
passage teaches the workflow, not one instance of it, so the child list is
empty of lemmas and the three rules stand in for the lemmas.

## Why it is good

1. The site is a single 17-line reference that states the whole protocol, so
   the reader sees the move in one sitting (lines 57-73).
2. The placeholder token is `sorry`: it occurs exactly twice in the file, once
   as the compiling stubs and once in the "filled sorry" rule, so the skeleton
   mechanism is the stub and nothing else.
3. The granularity criterion is the authors' own words — "one agent can
   discharge one stub without global context" (lines 72-73) — which is the
   sizing rule that turns a monolithic theorem into a skeleton of bounded
   holes.
4. The interface is frozen by rule, not by convention: "statements are frozen
   interface; if a statement is wrong, that is a design change, surfaced rather
   than silently patched" (lines 69-71).
5. The authors name a real precedent at the same shape: "This is exactly how
   PFR ran ~20 human contributors in parallel — the proof assistant verifies
   each contribution independently, so contributors need not understand the
   whole" (lines 63-66).

This workflow maps to survey F §10 rule 1 ("admit no statement without three
cheap checks"): the compile-before-fan-out rule is the sufficiency check of
building the parent sketch with every child `sorry`, and the frozen-statements
rule is the fidelity guard that pairs with it.

In my opinion the line worth copying is the frozen-statements rule, because it
converts the fragile part of parallel proof work — contributors drifting off
the interface — into a hard, surfaced event (a design change) rather than a
silent patch.

## When to use it, and when not

Use it when you are about to prove a main theorem from lemmas written for it
and want to parallelise the proofs across agents or contributors, when the
statements (the interface) can be settled before the proofs, and when the team
can compile the skeleton first. Avoid it when the statements are still in
flux — a change is then a design change to a frozen interface, surfaced rather
than patched; when the goal is a single small proof one agent closes directly
without decomposition; or when the skeleton cannot be made to compile first.

## Consequences

Freezing statements as interface makes any statement change an explicit design
change that must be surfaced rather than silently patched — the price of the
independence the workflow buys. The compile-before-fan-out gate means the
skeleton must build before any agent is dispatched, so a skeleton that does not
compile blocks the whole fan-out. The granularity criterion sizes every stub:
a stub that is too large reintroduces the shared-context problem the workflow
is meant to remove, while many trivial stubs add fan-out overhead. The
independence of each contribution rests on the frozen statements being
correct — the proof assistant verifies each stub against its own statement,
but a wrong frozen statement propagates to the assembled theorem undetected.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| sorry-scan | not-run | no Lean, Rocq or Isabelle file among the copied files | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(plugins/writing-lean-proofs/skills/writing-lean-proofs/references/llm-techniques.md:57-73, 17) -> lines: site plugins/writing-lean-proofs/skills/writing-lean-proofs/references/llm-techniques.md:57-73 has 17 lines | check_claims.py |
| 2 | verified | count(sorry, 2, plugins/writing-lean-proofs/skills/writing-lean-proofs/references/llm-techniques.md) -> count: sorry occurs 2 times in 1 file(s) matching plugins/writing-lean-proofs/skills/writing-lean-proofs/references/llm-techniques.md | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/trailofbits/skills at commit `e4dd0bb5b15535f7c5a0834187dffba6ac37e4ff`, under `CC-BY-SA-4.0`; see the [source note](../../sources/trailofbits-skills/SOURCE.md) for the licence text and attribution.
