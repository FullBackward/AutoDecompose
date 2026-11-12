# Iff-split of IMO 1986 Q5: IsGood f iff f = fun x => 2 / (2 - x)

| | |
|---|---|
| Kind | instance |
| Move | iff-split |
| Language | lean |
| Status | accepted |
| Source | [mathlib4](../../sources/mathlib4/SOURCE.md) at `e1545ebed975` |
| Licence | `Apache-2.0` |

## Intent

Split the characterisation `IsGood f ↔ f = fun x ↦ 2 / (2 - x)` into its two
directions with `refine ⟨·, ·⟩`. The forward direction is extensionality
applied to the already-proved pointwise lemma `map_eq`; the reverse unfolds the
candidate function into the three fields of `IsGood` with `constructor`.

## The decomposition

### parent `isGood_iff`: [`Archive/Imo/Imo1986Q5.lean` lines 74-89](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Imo/Imo1986Q5.lean#L74-L89) ([local copy](code/Archive/Imo/Imo1986Q5.lean))

```lean
theorem isGood_iff {f : ℝ≥0 → ℝ≥0} : IsGood f ↔ f = fun x ↦ 2 / (2 - x) := by
  refine ⟨fun hf ↦ funext hf.map_eq, ?_⟩
  rintro rfl
  constructor
  case map_two => simp [tsub_self]
  case map_ne_zero => intro x hx; simpa [tsub_eq_zero_iff_le]
  case map_add_rev =>
    intro x y
    cases lt_or_ge y 2 with
    | inl hy =>
      have hy' : 2 - y ≠ 0 := (tsub_pos_of_lt hy).ne'
      rw [div_mul_div_comm, tsub_mul, mul_assoc, div_mul_cancel₀ _ hy', mul_comm x,
        ← mul_tsub, tsub_add_eq_tsub_tsub_swap, mul_div_mul_left _ _ two_ne_zero]
    | inr hy =>
      have : 2 ≤ x + y := le_add_left hy
      simp [tsub_eq_zero_of_le, *]
```

### context `map_eq`: [`Archive/Imo/Imo1986Q5.lean` lines 67-70](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Imo/Imo1986Q5.lean#L67-L70) ([local copy](code/Archive/Imo/Imo1986Q5.lean))

```lean
theorem map_eq (x : ℝ≥0) : f x = 2 / (2 - x) :=
  match lt_or_ge x 2 with
  | .inl hx => hf.map_of_lt_two hx
  | .inr hx => by rwa [tsub_eq_zero_of_le hx, div_zero, hf.map_eq_zero]
```

### context `IsGood`: [`Archive/Imo/Imo1986Q5.lean` lines 37-40](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Imo/Imo1986Q5.lean#L37-L40) ([local copy](code/Archive/Imo/Imo1986Q5.lean))

```lean
structure IsGood (f : ℝ≥0 → ℝ≥0) : Prop where
  map_add_rev x y : f (x * f y) * f y = f (x + y)
  map_two : f 2 = 0
  map_ne_zero : ∀ x < 2, f x ≠ 0
```

How the parts fit. `refine ⟨fun hf ↦ funext hf.map_eq, ?_⟩` (line 75) turns the
`↔` goal into exactly two children: the forward implication
`IsGood f → f = fun x ↦ 2 / (2 - x)` and the reverse, the `?_` hole
`f = fun x ↦ 2 / (2 - x) → IsGood f`.

The forward child closes immediately: `funext hf.map_eq` reduces the function
equality to a pointwise equality `f x = 2 / (2 - x)`, which is exactly the
already-proved lemma `map_eq` (lines 67-70), itself closed by a `match
lt_or_ge x 2` case split using `hf.map_of_lt_two` and `hf.map_eq_zero`. So the
forward direction carries no new pointwise argument.

The reverse child is the interesting half. `rintro rfl` substitutes the concrete
function into the goal, leaving `IsGood (fun x ↦ 2 / (2 - x))`. Then
`constructor` (line 77) splits this structure goal into its three fields, and
each is discharged as a named `case`:

- `case map_two` (line 78): `simp [tsub_self]` proves `2 / (2 - 2) = 0`.
- `case map_ne_zero` (line 79): `intro x hx; simpa [tsub_eq_zero_iff_le]` proves
  `2 / (2 - x) ≠ 0` when `x < 2` (the denominator is non-zero).
- `case map_add_rev` (lines 80-89): after `intro x y`, a further `cases
  lt_or_ge y 2` splits on whether `y < 2`. In the `inl hy` branch the hypothesis
  `hy' : 2 - y ≠ 0` is used to cancel the denominator in a `rw` chain (lines
  85-86); in the `inr hy` branch `2 ≤ x + y` makes both sides `0`, closed by
  `simp [tsub_eq_zero_of_le, *]` (line 89).

## Why it is good

1. The `↔` goal is split on line 75 by `refine ⟨fun hf ↦ funext hf.map_eq, ?_⟩`
   into exactly two directions, and both close: the forward by `funext
   hf.map_eq`, the reverse by the `?_` hole over lines 76-89. (`check`)
2. In the reverse direction, `constructor` (line 77) splits
   `IsGood (fun x ↦ 2 / (2 - x))` into the three fields of `IsGood`
   (lines 37-40), each discharged as a separate named `case`: `map_two` by
   `simp [tsub_self]`, `map_ne_zero` by `intro x hx; simpa [tsub_eq_zero_iff_le]`,
   and `map_add_rev` by `cases lt_or_ge y 2` with both branches closed. (`check`)
3. The forward direction introduces no new pointwise argument: `funext
   hf.map_eq` applies the pointwise lemma `map_eq` (lines 67-70), so the iff
   proof reuses the already-proved fact `f x = 2 / (2 - x)` rather than
   re-deriving it. (`check`)
4. The module docstring states the plan verbatim — "We formalize the assumptions
   on `f` in `Imo1986Q5.IsGood` predicate, then prove `Imo1986Q5.IsGood f ↔
   f = fun x ↦ 2 / (2 - x)`" (lines 20-21) — and the formal proof follows it.
   (`author-statement`)
5. The same iff-split by `refine ⟨·, ·⟩` is used in the same file at lines 50-53
   for `f x = 0 ↔ 2 ≤ x`, whose forward direction is `not_lt.1 fun hlt ↦
   hf.map_ne_zero x hlt hx₀` and reverse is closed by `rcases exists_add_of_le
   hle` plus a rewrite. (`known-use`)

In my opinion the detail worth copying is the asymmetry the split makes
visible: the forward direction is a one-line application of a lemma proved
earlier, while the reverse is where the real content lives, and `constructor`
lets that content be discharged field by field with a short `simp` per field.

## When to use it, and when not

Use `refine ⟨·, ·⟩` (or `constructor`) on a `↔` goal when the two directions
want different tools: here one direction is a pointwise equality proved by
extensionality of an existing lemma, and the other is showing a candidate
function satisfies each field of a structure, which `constructor` splits into
named cases. It is the natural shape for a "characterise the solutions" theorem:
one direction shows the candidate solutions work, the other shows nothing else
works.

Avoid it when one direction is definitional or symmetric (then the split adds a
trivial child), when both directions need the same rewriting (a single
`rw`/`calc` chain often proves both at once), or when the predicate side is not
a structure, so `constructor` cannot split it into named fields and you would
need a manual `refine ⟨field₁, field₂, …⟩` anyway.

## Consequences

`refine ⟨·, ·⟩` on an iff creates exactly two obligations — the forward and the
reverse implication — and each must be closed on its own. The reverse direction
here is not self-contained: `constructor` further splits it into the three
fields of `IsGood`, so the reverse child is far larger than the forward (14
lines versus 1). A subtle failure mode: the forward direction silently leans on
an earlier pointwise lemma (`map_eq`), so the iff itself looks near-trivial
while the real work happened earlier in the file; anyone reproducing the whole
argument must also carry the upstream lemmas (`map_of_lt_two`, `map_eq_zero`,
lines 50-70).

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml triggers on push to master (default branch) and delegates to .github/workflows/build_template.yml; 'build archive, counterexamples and wanted' step runs 'lake-build-with-retry.sh Archive Counterexamples Wanted' (line 252) and 'check that Archive built' runs 'lake build --no-build --wfail Archive' (line 297), building Archive/Imo/Imo1986Q5.lean. Pinned commit e1545ebed97594477bbd88b2fe948ffce56e5af2 is on master (GitHub compare master...e1545eb: status behind, ahead_by 0, behind_by 1). | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at e1545ebed97594477bbd88b2fe948ffce56e5af2 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | copied file (byte-identical at e1545ebed975): line 75 'refine ⟨fun hf ↦ funext hf.map_eq, ?_⟩' splits the ↔ into two directions; forward closes by 'funext hf.map_eq' (line 75); reverse closes via 'rintro rfl' + 'constructor' + three cases over lines 76-89. | verifier |
| 2 | verified | copied file: line 77 'constructor'; IsGood structure (lines 37-40) has exactly three fields map_add_rev, map_two, map_ne_zero; line 78 'case map_two => simp [tsub_self]', line 79 'case map_ne_zero => intro x hx; simpa [tsub_eq_zero_iff_le]', lines 80-89 'case map_add_rev => intro x y; cases lt_or_ge y 2 with | inl hy ... | inr hy ...' both branches closed. | verifier |
| 3 | verified | copied file: map_eq (lines 67-70) proves 'f x = 2 / (2 - x)'; line 75 forward uses 'funext hf.map_eq' which applies map_eq pointwise, introducing no new argument. | verifier |
| 4 | verified | copied file docstring lines 20-21: 'We formalize the assumptions on f in Imo1986Q5.IsGood predicate, then prove Imo1986Q5.IsGood f ↔ f = fun x ↦ 2 / (2 - x)'; the theorem isGood_iff at lines 74-89 proves exactly this statement. | verifier |
| 5 | verified | copied file lines 50-53: theorem map_eq_zero 'f x = 0 ↔ 2 ≤ x' uses 'refine ⟨fun hx₀ ↦ not_lt.1 fun hlt ↦ hf.map_ne_zero x hlt hx₀, fun hle ↦ ?_⟩' (forward not_lt.1...) and reverse 'rcases exists_add_of_le hle with ⟨x, rfl⟩; rw [add_comm, hf.map_add, hf.map_two, mul_zero]'. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Copied file (byte-identical at e1545ebed975) matches entry exactly. Line 75 'refine ⟨fun hf ↦ funext hf.map_eq, ?_⟩' splits the ↔ into exactly two children: forward closes in one line via funext hf.map_eq; reverse closes over lines 76-89 via rintro rfl; constructor; then three named cases. IsGood (lines 37-40) has exactly three fields map_add_rev/map_two/map_ne_zero, matching case map_two (l78), map_ne_zero (l79), map_add_rev (l80-89). Both children and all closing methods match the entry's parent/children fields and README; CI-recorded build passes Archive so the proof closes. | reviewer-correctness |
| generality | accept | Move is stated generally: 'use_when' reduces to 'the two directions want different tools' and frames it as the 'characterise the solutions' archetype (one direction shows candidates work, the other shows nothing else does), which generalises past IMO 1986; the avoid_when conditions (definitional/symmetric direction, both directions sharing one rw/calc chain, predicate side not a structure) are specific and honest heuristics. Consequences are honest and specific: exactly two obligations, the reverse child far larger (14 vs 1 lines, matching the copied code at lines 75 vs 76-89), and the failure mode that the forward direction silently leans on upstream lemmas map_eq/map_of_lt_two/map_eq_zero (lines 47-70) is accurate. Only mild generality weakness: the sole in-file known-use (lines 50-53) shares the same IsGood predicate, so cross-context generality rests on the related compfiles entry rather than this entry's own evidence; not a standing objection. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are all consistent and traceable: check_provenance.py reports the copied file byte-identical at pinned commit e1545ebed97594477bbd88b2fe948ffce56e5af2; that commit is recorded identically in entry.json, sources/mathlib4/source.json and SOURCE.md. Every permalink uses the same commit and its line ranges match the copied file (IsGood 37-40, map_eq 67-70, isGood_iff 74-89, map_eq_zero 50-53, docstring 20-21 verified against the local copy). Licence Apache-2.0 is recorded in entry.json/README/source.json/SOURCE.md, the file header declares Apache 2.0, and upstream-LICENSE is the Apache 2.0 text. bytes=2996 and file sha256 match the copied file; validate_entry.py --strict passes. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover-community/mathlib4 at commit `e1545ebed97594477bbd88b2fe948ffce56e5af2`, under `Apache-2.0`; see the [source note](../../sources/mathlib4/SOURCE.md) for the licence text and attribution.
