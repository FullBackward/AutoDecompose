# Iff split for the comparison-encoding lemma gtFelt_eq_one_iff

| | |
|---|---|
| Kind | instance |
| Move | iff-split |
| Language | lean |
| Status | draft |
| Source | [trailofbits-skills](../../sources/trailofbits-skills/SOURCE.md) at `e4dd0bb5b155` |
| Licence | `CC-BY-SA-4.0` |

## Intent

Characterise the field-element encoding `gtFelt` (which maps a comparison on
canonical representatives to `1` or `0`) by proving the iff
`gtFelt a b = 1 ↔ a.val > b.val`. The proof splits the iff with `constructor`
so that each direction is discharged by a dedicated one-line lemma that
unfolds the definitional `if`.

## The decomposition

### parent `gtFelt_eq_one_iff`: [`plugins/writing-lean-proofs/evals/cases/03-normal-form/input/WordCmp.lean` lines 38-45](https://github.com/trailofbits/skills/blob/e4dd0bb5b15535f7c5a0834187dffba6ac37e4ff/plugins/writing-lean-proofs/evals/cases/03-normal-form/input/WordCmp.lean#L38-L45) ([local copy](code/plugins/writing-lean-proofs/evals/cases/03-normal-form/input/WordCmp.lean))

```lean
theorem gtFelt_eq_one_iff (a b : Felt) : gtFelt a b = 1 ↔ a.val > b.val := by
  constructor
  · intro h
    by_contra hab
    rw [gtFelt_of_not_gt a b hab] at h
    exact absurd h (by norm_num)
  · intro h
    exact gtFelt_of_gt a b h
```

### child `gtFelt_of_gt`: [`plugins/writing-lean-proofs/evals/cases/03-normal-form/input/WordCmp.lean` lines 26-27](https://github.com/trailofbits/skills/blob/e4dd0bb5b15535f7c5a0834187dffba6ac37e4ff/plugins/writing-lean-proofs/evals/cases/03-normal-form/input/WordCmp.lean#L26-L27) ([local copy](code/plugins/writing-lean-proofs/evals/cases/03-normal-form/input/WordCmp.lean))

```lean
theorem gtFelt_of_gt (a b : Felt) (h : a.val > b.val) : gtFelt a b = 1 := by
  simp [gtFelt, h]
```

### child `gtFelt_of_not_gt`: [`plugins/writing-lean-proofs/evals/cases/03-normal-form/input/WordCmp.lean` lines 29-30](https://github.com/trailofbits/skills/blob/e4dd0bb5b15535f7c5a0834187dffba6ac37e4ff/plugins/writing-lean-proofs/evals/cases/03-normal-form/input/WordCmp.lean#L29-L30) ([local copy](code/plugins/writing-lean-proofs/evals/cases/03-normal-form/input/WordCmp.lean))

```lean
theorem gtFelt_of_not_gt (a b : Felt) (h : ¬ a.val > b.val) : gtFelt a b = 0 := by
  simp [gtFelt, h]
```

How the parts fit. The lemma graph is a star of depth 1:

```
gtFelt_eq_one_iff (L38-45)
 ├── forward  : gtFelt a b = 1 → a.val > b.val   -- uses gtFelt_of_not_gt (L29-30)
 └── backward : a.val > b.val → gtFelt a b = 1   -- uses gtFelt_of_gt (L26-27)
```

`constructor` on the iff goal produces the two direction goals. The backward
direction is a direct application of `gtFelt_of_gt a b h` (line 45). The
forward direction proves the contrapositive structure by contradiction:
assume `¬ a.val > b.val` (that is, `hab`), rewrite the hypothesis
`h : gtFelt a b = 1` with `gtFelt_of_not_gt a b hab` to get `0 = 1`, and close
with `exact absurd h (by norm_num)` (lines 40-43).

Each child is a good leaf because its statement is self-contained — it only
mentions `gtFelt` and its own hypothesis — and its proof is a single `simp`
over the definition `gtFelt` with the hypothesis `h`, so it closes on its own
with no further project lemma. Neither child depends on the other, which is
what lets the parent's two directions be discharged independently.

## Why it is good

1. Each direction of the iff is closed by exactly one child lemma: the forward
   direction rewrites with `gtFelt_of_not_gt a b hab` (line 42) and the
   backward direction applies `gtFelt_of_gt a b h` (line 45), both under the
   `constructor` at line 39 ([file lines 38-45](https://github.com/trailofbits/skills/blob/e4dd0bb5b15535f7c5a0834187dffba6ac37e4ff/plugins/writing-lean-proofs/evals/cases/03-normal-form/input/WordCmp.lean#L38-L45)).
2. Both children close by `simp [gtFelt, h]` alone (lines 27 and 30), so each
   is a single tactic over the definition with no other lemma
   ([file lines 26-30](https://github.com/trailofbits/skills/blob/e4dd0bb5b15535f7c5a0834187dffba6ac37e4ff/plugins/writing-lean-proofs/evals/cases/03-normal-form/input/WordCmp.lean#L26-L30)).
3. The shape is small and flat: an 8-line glue assembled from 2 one-line child
   proofs, depth 1 below the theorem (read of the whole copied file; parent
   L38-L45, child proofs L27 and L30).
4. The parent is reused as a leaf by `ltFelt_eq_one_iff`, which reduces to it
   in one line, `simp only [ltFelt, gtFelt_eq_one_iff]` (line 48)
   ([file lines 47-48](https://github.com/trailofbits/skills/blob/e4dd0bb5b15535f7c5a0834187dffba6ac37e4ff/plugins/writing-lean-proofs/evals/cases/03-normal-form/input/WordCmp.lean#L47-L48)).
5. The module docstring states what these lemmas are for: "Field-element
   encodings of comparisons on canonical representatives, used to model the
   VM's `gt`/`lt` instructions."
   ([file lines 3-8](https://github.com/trailofbits/skills/blob/e4dd0bb5b15535f7c5a0834187dffba6ac37e4ff/plugins/writing-lean-proofs/evals/cases/03-normal-form/input/WordCmp.lean#L3-L8)).

In my opinion the forward direction is the interesting half: it is not a
direct application of the child but a rewrite-plus-contradiction, and it works
only because the encoding's two values `1` and `0` are distinct and `norm_num`
knows it.

## When to use it, and when not

Use it when a goal is an iff (or an order antisymmetry) between an encoding
taking a fixed value and the decidable condition the encoding represents, and
each direction can be stated as its own lemma whose proof is a single
`simp`/unfold over the definition. It fits here because `gtFelt a b` is
literally `if a.val > b.val then 1 else 0`, so both branches are one rewrite
away.

Avoid it when the forward direction needs a real argument rather than an
unfold-and-contradiction, when the encoding is not already in `simp`-normal
form, when the condition is not decidable, or when the two directions need
unrelated proofs. Also avoid it if the encoding's two output values are not
distinct constants, since then the contradiction step cannot close by
`norm_num`.

## Consequences

`constructor` on the iff creates two goals, one per direction. The backward
direction is free — a direct application of `gtFelt_of_gt`. The forward
direction carries the one real obligation: to exclude the `gtFelt a b = 0`
case it needs `by_contra`, a rewrite with `gtFelt_of_not_gt`, and a proof of
`absurd (0 = 1)` via `norm_num`. Failure mode: if the encoding returned the
same value on both branches, or if `norm_num` could not see `0 ≠ 1`, the
contradiction would need its own lemma and the "one line per direction" shape
would break.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/trailofbits/skills at commit `e4dd0bb5b15535f7c5a0834187dffba6ac37e4ff`, under `CC-BY-SA-4.0`; see the [source note](../../sources/trailofbits-skills/SOURCE.md) for the licence text and attribution.
