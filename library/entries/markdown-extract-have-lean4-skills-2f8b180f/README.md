# Extract-have: lift the two inline haves of big_result into helper1 and helper2

| | |
|---|---|
| Kind | instance |
| Move | extract-have |
| Language | markdown |
| Status | draft |
| Source | [lean4-skills](../../sources/lean4-skills/SOURCE.md) at `3f913c66251b` |
| Licence | `MIT` |

## Intent

A monolithic proof of `big_result` whose body holds two inline `have` blocks
(30 and 40 lines of tactics) plus a 30-line remainder is refactored into two
named lemmas, `helper1` and `helper2`, each owning one intermediate goal. The
main proof then reduces to a one-line application per lemma plus the
remainder, so each intermediate step is stated once, testable on its own, and
reusable.

## The decomposition

### parent `big_result`: [`plugins/lean4/skills/lean4/references/proof-refactoring.md` lines 208-212](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/proof-refactoring.md#L208-L212) ([local copy](code/plugins/lean4/skills/lean4/references/proof-refactoring.md))

```lean
theorem big_result : Conclusion := by
  intro x hx
  have h1 := helper1 x hx
  have h2 := helper2 x h1
  [30 lines - much clearer now]
```

### child `helper1`: [`plugins/lean4/skills/lean4/references/proof-refactoring.md` lines 202-203](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/proof-refactoring.md#L202-L203) ([local copy](code/plugins/lean4/skills/lean4/references/proof-refactoring.md))

```lean
lemma helper1 (x : α) (hx : Property x) : IntermediateGoal1 := by
  [30 lines - extracted from h1]
```

### child `helper2`: [`plugins/lean4/skills/lean4/references/proof-refactoring.md` lines 205-206](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/proof-refactoring.md#L205-L206) ([local copy](code/plugins/lean4/skills/lean4/references/proof-refactoring.md))

```lean
lemma helper2 (x : α) (h1 : IntermediateGoal1) : IntermediateGoal2 := by
  [40 lines - extracted from h2]
```

### context `before-monolithic`: [`plugins/lean4/skills/lean4/references/proof-refactoring.md` lines 192-199](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/proof-refactoring.md#L192-L199) ([local copy](code/plugins/lean4/skills/lean4/references/proof-refactoring.md))

```lean
-- BEFORE: Monolithic proof
theorem big_result : Conclusion := by
  intro x hx
  have h1 : IntermediateGoal1 := by
    [30 lines of tactics...]
  have h2 : IntermediateGoal2 := by
    [40 lines of tactics...]
  [30 more lines...]
```

How the parts fit. `helper2` depends on `helper1`: its second parameter
`h1 : IntermediateGoal1` is exactly `helper1`'s conclusion, so the two leaves
form a two-link chain

```
big_result ── have h1 := helper1 x hx ──▶ helper1 : Property x → IntermediateGoal1
    └──────── have h2 := helper2 x h1 ──▶ helper2 : IntermediateGoal1 → IntermediateGoal2
```

`big_result` applies `helper1` first (binding `h1`), then `helper2`
(consuming `h1`), then the 30-line remainder. The BEFORE block shows the same
two goals as inline `have`s (`have h1 : IntermediateGoal1`,
`have h2 : IntermediateGoal2`), so the two one-line applications in the AFTER
proof are exactly the glue: nothing else in the parent refers to how either
goal is proved.

Why each leaf is good. `helper1` is a self-contained statement —
`(x : α) → Property x → IntermediateGoal1` — that closes on its own from the
extracted 30-line block and takes only the hypotheses it uses (`x`, `hx`).
`helper2` is self-contained given its named sibling:
`(x : α) → IntermediateGoal1 → IntermediateGoal2`, closing from the extracted
40-line block with `helper1`'s conclusion as its only extra input. Because
`helper2` states its dependence on `helper1` as an explicit parameter rather
than re-proving it, the two leaves are independently provable and the parent's
glue is just composition.

## Why it is good

1. The AFTER proof of `big_result` cites exactly two lemmas, `helper1` and
   `helper2`, one application each (`have h1 := helper1 x hx`,
   `have h2 := helper2 x h1`), and these correspond one-to-one to the two
   inline goals of the BEFORE block (check, lines 192-212).
2. The main proof drops from the 8-line BEFORE block, embedding 70 lines of
   elided tactic blocks, to 5 lines of glue; the two extracted bodies move out
   into the lemmas (measurement, lines 192-199 versus 208-212).
3. The file states the trigger for this exact move in its own words: refactor
   on "Large preliminary calculations (50+ line `have` statements)" (line 59),
   and Step 3 is its illustration.
4. The same move recurs in the file's "Real Refactoring Example": the inline
   `have hk_bound : ... := by ...` is extracted to `private lemma
   strictMono_all_lt_succ_last` and the main proof "now just calls helper"
   (known-use, lines 309-330).

In my opinion the detail worth copying is that `helper2` takes the previous
lemma's conclusion as an explicit parameter, which records the dependency in
the type instead of leaving it implicit in the surrounding proof.

## When to use it, and when not

Use it when the proof body is dominated by intermediate goals stated as inline
`have`s whose tactic blocks are long (the file's trigger is a 50+ line `have`
statement, line 59) and whose statements are clean and self-contained with
local dependencies only. The extracted helper should take exactly the
hypotheses it uses, so each leaf is provable and testable on its own. Avoid it
when the `have` is short and linear, when the helper would need 10+ parameters
or its context is too tangled to separate cleanly (the file's "Bad
breakpoints", lines 182-187), or when the intermediate result depends on later
bindings so it cannot be stated before the parent. Do not extract
definitionally sensitive fragments: the file's Pattern 3.4 warns that
measure-theory manipulations with `let` bindings should stay inline.

## Consequences

Each extracted `have` becomes a top-level lemma whose statement must be exactly
the type the parent's `have` expects, with every hypothesis the body uses:
`helper1` must conclude in `IntermediateGoal1` given `hx : Property x`, and
`helper2` must take `h1 : IntermediateGoal1` — the previous lemma's conclusion
— or the glue `have h2 := helper2 x h1` will not elaborate. The file's Step 4
(lines 215-232) turns this into a check: the goal at the old `have` line must
match the helper's conclusion. A dropped or mismatched hypothesis breaks
sufficiency silently. Sequential dependence is the other cost: `helper2`
depends on `helper1`, so the two leaves are not parallelisable as stated (to
parallelise, `helper2` would re-prove `IntermediateGoal1` or take it as an
assumption).

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/cameronfreer/lean4-skills at commit `3f913c66251b8712bb58e6ce83a453fa96e3f94f`, under `MIT`; see the [source note](../../sources/lean4-skills/SOURCE.md) for the licence text and attribution.
