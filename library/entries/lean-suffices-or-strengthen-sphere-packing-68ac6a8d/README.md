# Prove the right limit of F/G at 0 through the atTop limit along 1/s

| | |
|---|---|
| Kind | instance |
| Move | suffices-or-strengthen |
| Language | lean |
| Status | accepted |
| Source | [sphere-packing](../../sources/sphere-packing/SOURCE.md) at `efe3bbbc1ece` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T09:08:56Z |

## Intent

A one-sided limit at `0`, `Tendsto FmodGReal (nhdsWithin 0 (Set.Ioi 0)) (nhds (18 π⁻²))`,
is not attacked in its own neighbourhood. Instead the proof first establishes the more
convenient statement — the limit of `FmodGReal (1 / s)` as `s → ∞`, where the real
functional equations of `F` and `G` turn the ratio into an explicit numerator over
denominator whose limits are known — and then pulls that limit back to `0` along
`tendsto_inv_nhdsGT_zero`.

## The decomposition

### parent `FmodG_rightLimitAt_zero`: [`SpherePacking/ModularForms/FG.lean` lines 519-527](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/ModularForms/FG.lean#L519-L527) ([local copy](code/SpherePacking/ModularForms/FG.lean))

```lean
theorem FmodG_rightLimitAt_zero :
    Tendsto FmodGReal (nhdsWithin 0 (Set.Ioi 0)) (nhds (18 * (π ^ (-2 : ℤ)))) := by
  have hlim : Tendsto (fun s : ℝ ↦ FmodGReal (1 / s)) atTop (nhds (18 * π ^ (-2 : ℤ))) := by
    rw [show (18 : ℝ) * π ^ (-2 : ℤ) = 36 * π ^ (-2 : ℤ) / 2 by ring]
    refine (FmodG_numerator_tendsto.div FmodG_denominator_tendsto two_ne_zero).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    rw [FmodGReal, F_functional_eq_real hs, G_functional_eq_real hs, mul_assoc (s ^ 10)]
    exact (mul_div_mul_left _ _ (pow_ne_zero 10 hs.ne')).symm
  exact (hlim.comp tendsto_inv_nhdsGT_zero).congr fun t ↦ by simp
```

### child `FmodG_numerator_tendsto`: [`SpherePacking/ModularForms/FG.lean` lines 483-488](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/ModularForms/FG.lean#L483-L488) ([local copy](code/SpherePacking/ModularForms/FG.lean))

```lean
lemma FmodG_numerator_tendsto :
  Tendsto (fun s ↦ s ^ 2 * FReal s
    - 12 * π ^ (-1 : ℤ) * (s * ((F₁ * E₄.toFun).resToImagAxis s).re)
    + 36 * π ^ (-2 : ℤ) * (E₄.toFun.resToImagAxis s).re ^ 2) atTop (nhds (36 * π ^ (-2 : ℤ))) := by
  tendsto_cont [sq_mul_FReal_tendsto_zero, mul_F₁E₄_re_tendsto_zero,
    tendsto_resToImagAxis_of_tendsto_atImInfty E₄_tendsto_one_atImInfty]
```

### child `FmodG_denominator_tendsto`: [`SpherePacking/ModularForms/FG.lean` lines 491-496](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/ModularForms/FG.lean#L491-L496) ([local copy](code/SpherePacking/ModularForms/FG.lean))

```lean
lemma FmodG_denominator_tendsto :
  Tendsto (fun s ↦ (H₄.resToImagAxis s).re ^ 3
    * (2 * (H₄.resToImagAxis s).re ^ 2 + 5 * (H₂.resToImagAxis s).re * (H₄.resToImagAxis s).re
    + 5 * (H₂.resToImagAxis s).re ^ 2)) atTop (nhds 2) := by
  tendsto_cont [tendsto_resToImagAxis_of_tendsto_atImInfty H₂_tendsto_atImInfty,
    tendsto_resToImagAxis_of_tendsto_atImInfty H₄_tendsto_atImInfty]
```

### child `F_functional_eq_real`: [`SpherePacking/ModularForms/FG.lean` lines 500-506](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/ModularForms/FG.lean#L500-L506) ([local copy](code/SpherePacking/ModularForms/FG.lean))

```lean
lemma F_functional_eq_real {s : ℝ} (hs : 0 < s) :
    FReal (1 / s) = s ^ 10 * (s ^ 2 * FReal s
      - 12 * π ^ (-1 : ℤ) * (s * ((F₁ * E₄.toFun).resToImagAxis s).re)
      + 36 * π ^ (-2 : ℤ) * (E₄.toFun.resToImagAxis s).re ^ 2) := by
  push_cast [← Complex.ofReal_inj, ← (F₁_imag_axis_real.mul E₄_imag_axis_real).eq_real_part s,
    ← E₄_imag_axis_real.eq_real_part s]
  linear_combination F_functional_equation' hs
```

### child `G_functional_eq_real`: [`SpherePacking/ModularForms/FG.lean` lines 510-516](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/ModularForms/FG.lean#L510-L516) ([local copy](code/SpherePacking/ModularForms/FG.lean))

```lean
lemma G_functional_eq_real {s : ℝ} (hs : 0 < s) :
    GReal (1 / s) = s ^ 10 * (H₄.resToImagAxis s).re ^ 3 *
      (2 * (H₄.resToImagAxis s).re ^ 2 + 5 * (H₂.resToImagAxis s).re * (H₄.resToImagAxis s).re
        + 5 * (H₂.resToImagAxis s).re ^ 2) := by
  push_cast [← Complex.ofReal_inj, ← H₂_imag_axis_real.eq_real_part s,
    ← H₄_imag_axis_real.eq_real_part s]
  linear_combination G_functional_equation' hs
```

### How the parts fit

The parent's proof is the glue. It does not reason about the neighbourhood of `0`
directly. Line 521 states the strengthened intermediate `hlim`, the limit of
`FmodGReal (1 / s)` at `atTop`; line 522 rewrites the target constant `18 π⁻²` as
`36 π⁻² / 2`; line 523 assembles the numerator and denominator children into a
limit of their quotient with `FmodG_numerator_tendsto.div FmodG_denominator_tendsto
two_ne_zero`; lines 525-526 rewrite the quotient pointwise, using the two
functional-equation children to unfold `FmodGReal (1 / s)` and then cancelling the
common `s ^ 10`; line 527 pulls the whole `atTop` limit back to the right limit at
`0` with `(hlim.comp tendsto_inv_nhdsGT_zero)`.

The lemma graph, in text (each `→` is "is used by", all in this one file):

```
FmodG_rightLimitAt_zero (L519-527)
├── FmodG_numerator_tendsto (L483-488)
│     ├── sq_mul_FReal_tendsto_zero (L473-474)
│     │     └── F_isBigO_exp_atImInfty (L464-465)
│     │           └── F₁_isBigO_exp_atImInfty (L457-461)
│     │                 └── E₂E₄_sub_E₆_div_q_tendsto (L299-313)
│     │                       └── qexp_tendsto_of_poly_bound (L286-291)
│     ├── mul_F₁E₄_re_tendsto_zero (L477-480)
│     │     └── F₁_mul_E₄_isBigO_exp_atImInfty (L468-470) → F₁_isBigO_exp_atImInfty
│     └── tendsto_resToImagAxis_of_tendsto_atImInfty E₄_tendsto_one_atImInfty (L488)
├── FmodG_denominator_tendsto (L491-496)
│     ├── tendsto_resToImagAxis_of_tendsto_atImInfty H₂_tendsto_atImInfty (L495)
│     └── tendsto_resToImagAxis_of_tendsto_atImInfty H₄_tendsto_atImInfty (L496)
├── F_functional_eq_real (L500-506)
│     └── F_functional_equation' (L423-430) → F_functional_equation (L414-420)
└── G_functional_eq_real (L510-516)
      └── G_functional_equation' (L440-446) → G_functional_equation (L433-437)
```

Each child is a good leaf because its statement is self-contained and its proof
closes on its own or from named siblings:

- `FmodG_numerator_tendsto` is exactly the numerator of `FmodGReal (1 / s)` after
  the `s ^ 10` is cancelled; it closes with one `tendsto_cont` call over three
  sibling decay/limit facts (`sq_mul_FReal_tendsto_zero`, `mul_F₁E₄_re_tendsto_zero`,
  and the `E₄ → 1` limit).
- `FmodG_denominator_tendsto` is the matching denominator; it closes with one
  `tendsto_cont` call over the two theta `H₂`/`H₄` at-infinity limits.
- `F_functional_eq_real` and `G_functional_eq_real` are pure algebraic identities
  (the real forms of the modular functional equations); each closes with one
  `linear_combination` call from the corresponding imaginary-axis equation
  (`F_functional_equation'` / `G_functional_equation'`).

The two tendsto children and the two functional-equation children are the only
lemmas the glue cites directly (lines 523 and 525); `two_ne_zero`,
`tendsto_inv_nhdsGT_zero` and `pow_ne_zero` are Mathlib facts, not project lemmas.

## Why it is good

1. The main theorem `FmodG_rightLimitAt_zero` is declared at
   [`FG.lean` lines 519-527](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/ModularForms/FG.lean#L519-L527)
   (check, form `declared`).
2. The proof has no `sorry`/`admit`/`axiom` token in lines 519-527 (check, form
   `no_sorry`); the file builds in the project's CI.
3. The parent's proof cites the child `FmodG_numerator_tendsto` at line 523 (check,
   form `cites`); the full glue-cites-children check covers all four children.
4. The glue closes the theorem in 9 lines from 4 direct lemmas whose proofs span
   6, 6, 7 and 7 lines, and the longest chain of project lemmas below the theorem
   is 6 (`FmodG_rightLimitAt_zero → FmodG_numerator_tendsto →
   sq_mul_FReal_tendsto_zero → F_isBigO_exp_atImInfty → F₁_isBigO_exp_atImInfty →
   E₂E₄_sub_E₆_div_q_tendsto → qexp_tendsto_of_poly_bound`), all in this one file
   (measurement).
5. The theorem's doc comment records its blueprint origin: "lim_{t → 0⁺}
   F(it) / G(it) = 18 π⁻² (blueprint Lemma 8.8)" (author-statement, line 518).

In my opinion the detail worth copying is the pairing of the move with its
bookkeeping: the strengthened `atTop` limit is chosen *because* the functional
equations are clean there, and the glue keeps the change of variable and the
pull-back as two separate named pieces (`hlim` and `.comp tendsto_inv_nhdsGT_zero`),
so a verifier can read off exactly where the convenient statement ends and the
pull-back begins.

## When to use it, and when not

Use it when a one-sided limit at a point (`nhdsWithin a (Set.Ioi a)`) is awkward in
its own neighbourhood but the function has an explicit functional equation in
another coordinate, so that `Tendsto (f ∘ g) atTop (nhds L)` can be assembled from
named tendsto lemmas and then pulled back by a standard inversion lemma
(`tendsto_inv_nhdsGT_zero` for `a = 0`). The functional equation must simplify the
ratio enough to leave a numerator and denominator that each tend to a known value.

Avoid it when the pull-back lemma does not match the filter (the change of variable
must be a homeomorphism onto the punctured neighbourhood and the limit must be one
of the standard inversion filters), or when the functional equation leaves a term
that does not decay at `atTop` — then the numerator/denominator children no longer
close on their own and the argument needs an extra decay lemma before the split.

## Consequences

The move creates one intermediate obligation, the `atTop` limit along `1 / s`. Its
proof must produce four halves — the numerator limit, the denominator limit, and the
two real functional equations — and must cancel the common factor `s ^ 10`. The
pull-back step depends on `tendsto_inv_nhdsGT_zero` matching the filter
`nhdsWithin 0 (Set.Ioi 0)`, so the change of variable has to be the reciprocal.
Failure mode: if the functional equation does not leave a vanishing tail, the
numerator child no longer closes on its own and the decomposition needs a further
decay lemma (as the numerator child itself already does, via
`sq_mul_FReal_tendsto_zero`).

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml; commit efe3bbbc1ece548f4672a772b94d8f621c10fdda is HEAD of main (default branch, compare main...efe3bbbc = identical); the workflow triggers on push to main and builds the whole Lean project via leanprover/lean-action (lake build), which includes SpherePacking/ModularForms/FG.lean | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: FmodG_numerator_tendsto@SpherePacking/ModularForms/FG.lean:523, FmodG_denominator_tendsto@SpherePacking/ModularForms/FG.lean:523, F_functional_eq_real@SpherePacking/ModularForms/FG.lean:525, G_functional_eq_real@SpherePacking/ModularForms/FG.lean:525; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at efe3bbbc1ece548f4672a772b94d8f621c10fdda | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(FmodG_rightLimitAt_zero, SpherePacking/ModularForms/FG.lean, 519-527) -> declared: FmodG_rightLimitAt_zero is declared at SpherePacking/ModularForms/FG.lean:519 | check_claims.py |
| 2 | verified | no_sorry(SpherePacking/ModularForms/FG.lean, 519-527) -> no_sorry: none of sorry, admit, axiom in SpherePacking/ModularForms/FG.lean:519-527 | check_claims.py |
| 3 | verified | cites(parent, FmodG_numerator_tendsto) -> cites: FmodG_numerator_tendsto occurs at SpherePacking/ModularForms/FG.lean:523 | check_claims.py |
| 4 | verified | Read code/FG.lean: parent spans L519-527 (9 lines); 4 children sites FmodG_numerator_tendsto L483-488 (6), FmodG_denominator_tendsto L491-496 (6), F_functional_eq_real L500-506 (7), G_functional_eq_real L510-516 (7); chain links all confirmed: FmodG_numerator_tendsto cites sq_mul_FReal_tendsto_zero (L487), which cites F_isBigO_exp_atImInfty (L474), which cites F₁_isBigO_exp_atImInfty (L465), which cites E₂E₄_sub_E₆_div_q_tendsto (L460), which cites qexp_tendsto_of_poly_bound (L313) | verifier |
| 5 | verified | Read code/FG.lean L518: doc comment is '/-- lim_{t → 0⁺} F(it) / G(it) = 18 π⁻² (blueprint Lemma 8.8). -/' directly above the theorem, recording exactly the stated limit and blueprint Lemma 8.8 | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent FmodG_rightLimitAt_zero (L519-527) and all four children (L483-488, L491-496, L500-506, L510-516) match the code verbatim; closed_by tactics match exactly (tendsto_cont/linear_combination). The proof closes with no sorry: hlim is assembled from FmodG_numerator_tendsto.div FmodG_denominator_tendsto then rewritten with F_functional_eq_real and G_functional_eq_real and pulled back via tendsto_inv_nhdsGT_zero. The four children are exactly the project lemmas the glue cites (L523, L525); two_ne_zero, tendsto_inv_nhdsGT_zero, pow_ne_zero are Mathlib facts, correctly excluded. Shape numbers correct: direct_lemmas=4, glue_lines=9, child_lines=[6,6,7,7] (verified line-by-line), depth=6 (chain parent -> numerator -> sq_mul_FReal_tendsto_zero -> F_isBigO_exp_atImInfty -> F1_isBigO_exp_atImInfty -> E2E4_sub_E6_div_q_tendsto -> qexp_tendsto_of_poly_bound, 6 project lemmas below the theorem). | reviewer-correctness |
| generality | accept | Move generalises beyond the example: applicability/goal_shape is 'Tendsto f (nhdsWithin a (Set.Ioi a)) L' with a functional equation clean under t -> a+1/s (1/s for a=0), not just F/G at 0. use_when/avoid_when name the two real preconditions honestly: a matching pull-back/inversion filter (tendsto_inv_nhdsGT_zero) and a functional equation that leaves decaying numerator/denominator terms; the failure mode is specific (need an extra decay lemma) and is exactly what the example itself requires via sq_mul_FReal_tendsto_zero. Consequences enumerate the intermediate atTop obligation, the four halves and the s^10 cancellation. Good leaves for a bounded prover are stated: self-contained statements, each closing with a single automated tactic (tendsto_cont / linear_combination) over named siblings - confirmed at FG.lean 483-516 (children) and 519-527 (parent, doc comment at 518). | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are all consistent and traceable: commit efe3bbbc1ece548f4672a772b94d8f621c10fdda matches across entry.json source.commit, files/site permalinks, README, SOURCE.md and source.json; check_provenance reports the file byte-identical at that commit; local code sha256 c99685... equals files[0].sha256; licence Apache-2.0 is recorded identically in entry.json/README/SOURCE.md/source.json and the upstream-LICENSE file is genuine Apache 2.0; every cited line range (parent 519-527, children 483-488/491-496/500-506/510-516, claim-5 doc comment at 518) matches the copied file verbatim. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean at commit `efe3bbbc1ece548f4672a772b94d8f621c10fdda`, under `Apache-2.0`; see the [source note](../../sources/sphere-packing/SOURCE.md) for the licence text and attribution.
