# Plan-first inference prompt: name intermediate lemmas before Lean code

| | |
|---|---|
| Kind | skill |
| Move | workflow |
| Language | markdown |
| Status | draft |
| Source | [deepseek-prover-v2](../../sources/deepseek-prover-v2/SOURCE.md) at `e598a57ea328` |
| Licence | `LicenseRef-unknown` |

## Intent

The Quick Start's inference prompt makes the model state a proof plan — its
"key ideas, intermediate lemmas, and proof structures" — *before* writing any
Lean code. The generated proof therefore arrives as a decomposition into
named subgoals rather than a single monolith, mirroring the plan-first
cold-start pipeline the model was trained with.

## The decomposition

### skill-text `prompt`: [`README.md` lines 140-149](https://github.com/deepseek-ai/DeepSeek-Prover-V2/blob/e598a57ea3284997d4a2a168a069fdd5064afbc8/README.md#L140-L149) ([local copy](code/README.md))

````markdown
prompt = """
Complete the following Lean 4 code:

```lean4
{}
```

Before producing the Lean 4 code to formally prove the given theorem, provide a detailed proof plan outlining the main proof steps and strategies.
The plan should highlight key ideas, intermediate lemmas, and proof structures that will guide the construction of the final formal proof.
""".strip()
````

### context `formal_statement`: [`README.md` lines 127-138](https://github.com/deepseek-ai/DeepSeek-Prover-V2/blob/e598a57ea3284997d4a2a168a069fdd5064afbc8/README.md#L127-L138) ([local copy](code/README.md))

```markdown
formal_statement = """
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- What is the positive difference between $120\%$ of 30 and $130\%$ of 20? Show that it is 10.-/
theorem mathd_algebra_10 : abs ((120 : ℝ) / 100 * 30 - 130 / 100 * 20) = 10 := by
  sorry
""".strip()
```

How the parts fit. This is a two-part prompt, not a proof with children. The
`context` block is the *goal*: the MiniF2F statement `mathd_algebra_10` (a
percent-difference problem) whose proof body is `sorry`, so it is a hole to be
filled, not a closed development. The `skill-text` block is the *instruction*
wrapped around that goal: it opens with "Complete the following Lean 4 code"
and a `{}` hole into which `formal_statement` is substituted
(`prompt.format(formal_statement)`, line 152), then — before any code is
produced — it requires "a detailed proof plan" that names the "key ideas,
intermediate lemmas, and proof structures" that will guide the code. The two
parts fit as *plan-then-fill*: the prompt tells the model to first commit to a
decomposition (the named lemmas and structure), and only then to emit the Lean
code that realises it. There are no named children in the README itself: the
actual lemmas are whatever the model emits at inference time, and the matching
MiniF2F solution (`valid/mathd_algebra_10.lean`) is a member of the
`minif2f-solutions.zip` archive, not a repository path, so it cannot be read
here.

## Why it is good

1. The prompt makes the plan a mandatory step ordered before the code: "Before
   producing the Lean 4 code to formally prove the given theorem, provide a
   detailed proof plan outlining the main proof steps and strategies" (line
   147). Evidence: `check` of the copied `README.md` lines 140-149.
2. The plan is required to name decomposition structure, not just prose: it
   must "highlight key ideas, intermediate lemmas, and proof structures that
   will guide the construction of the final formal proof" (line 148).
   Evidence: `check` of the copied `README.md` lines 140-149.
3. The target the prompt wraps is the theorem `mathd_algebra_10` with proof
   body `sorry` (line 137), so the prompt is a fill-the-hole instruction whose
   plan precedes the code that replaces the hole. Evidence: `check` of the
   copied `README.md` lines 127-138.
4. The README describes this same plan-first workflow as the model's training
   procedure: DeepSeek-V3 is prompted "to decompose theorems into high-level
   proof sketches while simultaneously formalizing these proof steps in Lean 4,
   resulting in a sequence of subgoals" (line 56). Evidence: `author-statement`.
5. The reinforcement-learning stage reuses the same decomposition and composes
   the subgoal proofs: "By composing the proofs of all subgoals, we construct a
   complete formal proof for the original problem" (line 64). Evidence:
   `author-statement`.

In my opinion the detail worth copying is the *ordering*: the instruction
places the decomposition before the code, so the plan is a commitment the code
is then asked to follow, rather than a post-hoc explanation. The prompt itself
does no checking of that commitment — see Consequences.

## When to use it, and when not

Use it when the model was trained to plan before proving — DeepSeek-Prover-V2's
cold-start data pairs subgoal decompositions with their formal proofs (lines
56-58) — and you want the decomposition surfaced as an inspectable plan rather
than a single opaque proof. Avoid it when the model was not trained to plan
first, or when you need only the code and the plan would waste output tokens
(the example sets `max_new_tokens=8192`, line 160, to leave room for the
plan), or when the plan is never checked against the code, so a plan that names
lemmas the code does not use still passes.

## Consequences

The prompt lets the model spend output tokens on a plan the code may not
actually use: nothing in the Quick Start checks that the plan's named lemmas
appear in the Lean code, or that the returned code compiles — the plan is
trusted, not verified. The `sorry` in `mathd_algebra_10` (line 137) is the
input hole the model is asked to fill, not a closing hack, so this site does
not trip protocol §4 E3's "sorry in the dependency cone" exclusion; a reader
must substitute their own goal statement for `mathd_algebra_10`. Because the
plan is emitted before the code, the example sets `max_new_tokens=8192` (line
160) to leave room for it.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/deepseek-ai/DeepSeek-Prover-V2 at commit `e598a57ea3284997d4a2a168a069fdd5064afbc8`, under `LicenseRef-unknown`; see the [source note](../../sources/deepseek-prover-v2/SOURCE.md) for the licence text and attribution.
