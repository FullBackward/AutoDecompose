# Exponent interpolation of the f- and g-side estimates for the forest operator bound

| | |
|---|---|
| Kind | instance |
| Move | other |
| Language | lean |
| Status | accepted |
| Source | [carleson](../../sources/carleson/SOURCE.md) at `d75f54374f7f` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T09:07:56Z |

## Intent

Bound the mixed norm `‖∫ x, conj (g x) * ∑ u, carlesonSum (𝔉 u) f x‖ₑ` for
every exponent `q ∈ (1, 2]` by proving two separate estimates and interpolating
between them: `forest_operator_g` carries the bound on `g` (sharp near `q = 2`),
`forest_operator_f` carries the bound on `f` (sharp near `q = 1`). Raising the
two to the complementary powers `2 - 2/q` and `2/q - 1` and multiplying gives
the desired `dens₂` exponent `q⁻¹ - 2⁻¹` in one step.

## The decomposition

### parent `forest_operator`: [`Carleson/ForestOperator/Forests.lean` lines 1024-1070](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/ForestOperator/Forests.lean#L1024-L1070) ([local copy](code/Carleson/ForestOperator/Forests.lean))

```lean
theorem forest_operator {n : ℕ} (𝔉 : Forest X n) {f g : X → ℂ}
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    (hg : Measurable g) (h2g : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    ‖∫ x, conj (g x) * ∑ u with u ∈ 𝔉, carlesonSum (𝔉 u) f x‖ₑ ≤
    C2_0_4 a q n * (dens₂ (⋃ u ∈ 𝔉, 𝔉 u)) ^ (q⁻¹ - 2⁻¹) *
    eLpNorm f 2 volume * eLpNorm g 2 volume := by
  have g_part := 𝔉.forest_operator_g hf h2f hg h2g -- ^ (2 - 2 / q)
  have f_part := 𝔉.forest_operator_f hf h2f hg h2g -- ^ (2 / q - 1)
  rcases (q_le_two X).eq_or_lt with rfl | hq
  · rw [sub_self, ENNReal.rpow_zero, mul_one, C2_0_4, C2_0_4_base]
    rw [Forest.G2_0_4] at g_part; convert g_part using 6; ring
  have egpos : 0 < 2 - 2 / q := by
    rw [sub_pos]; nth_rw 2 [show 2 = (2 : ℝ) / 1 by norm_num]
    exact div_lt_div_of_pos_left zero_lt_two zero_lt_one (one_lt_q X)
  have efpos : 0 < 2 / q - 1 := by rwa [sub_pos, one_lt_div (zero_lt_one.trans (one_lt_q X))]
  rw [← ENNReal.rpow_le_rpow_iff egpos] at g_part
  rw [← ENNReal.rpow_le_rpow_iff efpos] at f_part
  have key := mul_le_mul' g_part f_part
  have esum : 2 - 2 / q + (2 / q - 1) = 1 := by ring
  rw [← ENNReal.rpow_add_of_nonneg _ _ egpos.le efpos.le, esum, ENNReal.rpow_one, mul_assoc,
    mul_assoc _ (eLpNorm f 2 volume), ENNReal.mul_rpow_of_nonneg _ _ egpos.le,
    ENNReal.mul_rpow_of_nonneg _ _ efpos.le, mul_mul_mul_comm,
    ← ENNReal.rpow_add_of_nonneg _ _ egpos.le efpos.le, esum, ENNReal.rpow_one, ← mul_assoc,
    ENNReal.mul_rpow_of_nonneg _ _ efpos.le, ← mul_assoc, ← ENNReal.rpow_mul,
    show 2⁻¹ * (2 / q - 1) = q⁻¹ - 2⁻¹ by ring] at key
  apply key.trans; gcongr
  calc
    _ ≤ ((2 : ℝ≥0∞) ^ ((3 * 𝕔 + 15 + 5 * (𝕔 / 4)) * a ^ 3)) ^ (2 - 2 / q)
        * (2 ^ (-(n / 2 : ℝ))) ^ (2 - 2 / q) *
        (2 ^ ((3 * 𝕔 + 15 + 5 * (𝕔 / 4)) * a ^ 3)) ^ (2 / q - 1) := by
      rw [Forest.G2_0_4, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_rpow_of_ne_zero two_ne_zero,
        Forest.C2_0_4_aux]
      simp only [ENNReal.coe_ofNat]
      rw [ENNReal.mul_rpow_of_nonneg _ _ egpos.le]
      simp only [ENNReal.coe_pow, ENNReal.coe_ofNat]
      gcongr _ * (2 ^ ?_) ^ _
      · norm_num
      have : 𝕔 / 2 ≤ 2 * (𝕔 / 4) + 1 := by lia
      grw [this]
      ring_nf
      lia
    _ = _ := by
      rw [← mul_rotate, ← ENNReal.rpow_add_of_nonneg _ _ efpos.le egpos.le, add_comm (2/q - 1),
        esum, ENNReal.rpow_one, ← ENNReal.rpow_mul, C2_0_4, C2_0_4_base, ENNReal.coe_mul,
        ENNReal.coe_pow, ENNReal.coe_rpow_of_ne_zero two_ne_zero, neg_div,
        show -(n / 2) * (2 - 2 / q) = -(1 - 1 / q) * n by ring]
      congr; rw [sub_div, div_self (q_pos X).ne']
```

### child `forest_operator_g`: [`Carleson/ForestOperator/Forests.lean` lines 830-841](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/ForestOperator/Forests.lean#L830-L841) ([local copy](code/Carleson/ForestOperator/Forests.lean))

```lean
lemma forest_operator_g (t : Forest X n)
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    (hg : Measurable g) (h2g : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    ‖∫ x, conj (g x) * ∑ u with u ∈ t, carlesonSum (t u) f x‖ₑ ≤
    G2_0_4 a n * eLpNorm f 2 volume * eLpNorm g 2 volume := by
  calc
    _ ≤ _ := forest_operator_g_prelude hf h2f hg h2g
    _ ≤ _ := by
      rw [mul_comm _ (eLpNorm f 2 volume), mul_assoc]; gcongr
      rw [← ENNReal.rpow_le_rpow_iff (show (0 : ℝ) < (2 : ℕ) by norm_num),
        ENNReal.rpow_natCast, ENNReal.rpow_natCast]
      exact forest_operator_g_main hg h2g
```

### child `forest_operator_f`: [`Carleson/ForestOperator/Forests.lean` lines 997-1009](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/ForestOperator/Forests.lean#L997-L1009) ([local copy](code/Carleson/ForestOperator/Forests.lean))

```lean
lemma forest_operator_f (t : Forest X n)
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    (hg : Measurable g) (h2g : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    ‖∫ x, conj (g x) * ∑ u with u ∈ t, carlesonSum (t u) f x‖ₑ ≤
    C2_0_4_aux a * dens₂ (⋃ u ∈ t, t u) ^ (2 : ℝ)⁻¹ *
    eLpNorm f 2 volume * eLpNorm g 2 volume := by
  calc
    _ ≤ _ := forest_operator_f_prelude hf h2f hg h2g
    _ ≤ _ := by
      rw [← mul_rotate, mul_assoc]; gcongr
      rw [← ENNReal.rpow_le_rpow_iff (show (0 : ℝ) < (2 : ℕ) by norm_num),
        ENNReal.rpow_natCast, ENNReal.rpow_natCast]
      exact forest_operator_f_main hf h2f
```

How the parts fit. The parent `forest_operator` is the glue: it names the two
sides (`have g_part := 𝔉.forest_operator_g …`, `have f_part :=
𝔉.forest_operator_f …`), raises each to a complementary power (`2 - 2/q` for
the g-side, `2/q - 1` for the f-side) via `rpow_le_rpow_iff`, and multiplies
them (`mul_le_mul' g_part f_part`). A single rewrite uses `esum : 2 - 2/q +
(2/q - 1) = 1` to collapse the two `eLpNorm` tails, and a final `calc`
shows the product of the two constants equals the target `C2_0_4`. The endpoint
`q = 2` is split off first (`rcases (q_le_two X).eq_or_lt`), where `2 - 2/q` is
0 and only the g-side matters.

Lemma graph (text):

```
forest_operator (theorem, 1024-1070)   -- the glue
  ├── forest_operator_g (830-841)      -- g-side, exponent 2 - 2/q
  │     ├── forest_operator_g_prelude  (690-…)
  │     └── forest_operator_g_main     (759-…)
  └── forest_operator_f (997-1009)     -- f-side, exponent 2/q - 1
        ├── forest_operator_f_prelude  (852-…)
        └── forest_operator_f_main     (928-993)
              └── forest_operator_f_inner (880-921)
```

Each child is a good leaf because it is a self-contained statement — a bound on
the *same* integral with a *different* constant — whose proof closes on its own
two named siblings: `forest_operator_g` is a two-link `calc` that goes through
`forest_operator_g_prelude` (which moves the `g` norm out of the integral) and
`forest_operator_g_main` (the row/adjoint bound), and `forest_operator_f` is the
symmetric `calc` through `forest_operator_f_prelude` and `forest_operator_f_main`
(which in turn rests on `forest_operator_f_inner`). Neither child mentions `q`;
each is proved once at the two extreme regimes, and the parent does all the
`q`-dependent bookkeeping on top of them.

## Why it is good

1. The parent site — the theorem `forest_operator` with its proof — is 47 lines
   long (`check`; `lines(parent, 47)`, lines 1024-1070). This is
   `shape.glue_lines`, the measurement of the glue.
2. The parent's proof cites the g-side estimate `forest_operator_g` (`check`;
   `cites(parent, forest_operator_g)`, line 1030).
3. The parent's proof cites the f-side estimate `forest_operator_f` (`check`;
   `cites(parent, forest_operator_f)`, line 1031). Together with (2) these two
   citations are `shape.direct_lemmas = 2`.
4. `forest_operator_f` is declared in the copied file at lines 997-1009
   (`check`; `declared(forest_operator_f, Carleson/ForestOperator/Forests.lean,
   997-1009)`).
5. The authors state the two-sided structure in the doc comments: "The `f` side
   of Proposition 2.0.4." above `forest_operator_f` and "The `g` side of
   Proposition 2.0.4." above `forest_operator_g` (`author-statement`; lines 996
   and 829).

In my opinion the detail worth copying is that the two children are stated
*without* the parameter `q` they interpolate: each is a clean, reusable bound at
one extreme, and the entire `q`-dependence (the complementary powers, the
positivity facts `egpos`/`efpos`, and the constant bookkeeping) lives in the
glue, so the children are exactly the "one hole per bounded prover" shape a
decomposer should emit.

## When to use it, and when not

Use it when the goal is a bound on a bilinear quantity that must hold across an
interval of a parameter, and two estimates of the *same* quantity are available
with complementary strengths — here one that keeps `g` bounded (`forest_operator_g`,
good near `q = 2`) and one that keeps `f` bounded plus a `dens₂` factor
(`forest_operator_f`, good near `q = 1`). The tell is that the two bounds share
the same tail (`eLpNorm f 2 volume * eLpNorm g 2 volume`), so their product
collapses. The two exponents must be positive (here `egpos`, `efpos`), sum to 1
(`esum`), and the product of the two constants must be shown to equal the target
constant.

Avoid it when only one side has a useful estimate, when the two estimates do not
bound the same object (their product cannot be formed), or when the exponent
interval degenerates at an endpoint — `q = 2` makes `2 - 2/q = 0`, so the
interpolation must branch into a separate endpoint case. The constant bookkeeping
is real work (the final `calc` with `lia`/`ring`), so it is not free once the two
estimates are stated.

## Consequences

The move replaces one bound by two named estimates and creates three arithmetic
obligations the glue must discharge: the two powers are positive (`egpos`,
`efpos`, needed for `rpow_le_rpow_iff`), they sum to 1 (`esum`), and the product
of the two constants equals the target `C2_0_4` (the final `calc`). At the
endpoint `q = 2` the power `2 - 2/q` is 0, so the interpolation degenerates and
the theorem branches on `rcases (q_le_two X).eq_or_lt`, closing the endpoint by
`convert g_part using 6; ring`. If the two sides did not share the same
`eLpNorm f 2 * eLpNorm g 2` tail, their product would not simplify to the target
form.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push.yml (build_project job, lean-action build:true); Carleson.lean has 'public import Carleson.ForestOperator.Forests'; commit d75f54374f7f930e70a86b443f20d0e0935c275e is on default branch master | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: forest_operator_g@Carleson/ForestOperator/Forests.lean:1030, forest_operator_f@Carleson/ForestOperator/Forests.lean:1031; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at d75f54374f7f930e70a86b443f20d0e0935c275e | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(parent, 47) -> lines: site parent has 47 lines | check_claims.py |
| 2 | verified | cites(parent, forest_operator_g) -> cites: forest_operator_g occurs at Carleson/ForestOperator/Forests.lean:1030 | check_claims.py |
| 3 | verified | cites(parent, forest_operator_f) -> cites: forest_operator_f occurs at Carleson/ForestOperator/Forests.lean:1031 | check_claims.py |
| 4 | verified | declared(forest_operator_f, Carleson/ForestOperator/Forests.lean, 997-1009) -> declared: forest_operator_f is declared at Carleson/ForestOperator/Forests.lean:997 | check_claims.py |
| 5 | verified | copied Forests.lean line 829 reads '/-- The g side of Proposition 2.0.4. -/' above forest_operator_g (830), line 996 reads '/-- The f side of Proposition 2.0.4. -/' above forest_operator_f (997) | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Code at the cited ranges matches the entry. Parent forest_operator spans lines 1024-1070, 47 lines, matching glue_lines and claim 1 (lines parent 47). Children match their statements verbatim: forest_operator_g 830-841 (12 lines, matching child_lines[0]) closes via forest_operator_g_prelude then forest_operator_g_main (lines 836 and 841, matching closed_by); forest_operator_f 997-1009 (13 lines, matching child_lines[1]) closes via forest_operator_f_prelude then forest_operator_f_main (lines 1004 and 1009, matching closed_by). The parent cites exactly these two lemmas (line 1030 forest_operator_g, line 1031 forest_operator_f), so direct_lemmas is 2 and the children are exactly the lemmas the glue uses. No sorry in the site ranges. Depth 3 confirmed as the chain forest_operator -> forest_operator_f -> forest_operator_f_main (line 983 exact forest_operator_f_inner) -> forest_operator_f_inner (line 880). Doc comments The g side of Proposition 2.0.4 (line 829) and The f side of Proposition 2.0.4 (line 996) match claim 5. | reviewer-correctness |
| generality | accept | Move is stated generally as exponent interpolation of two complementary estimates of the same bilinear quantity, abstracted beyond the example (use_when gives the geometric-mean condition with exponents summing to 1). When-not-to-use and consequences are honest and specific, and each matches the cited code: the parent's egpos/efpos/esum obligations, the rcases endpoint branch at q=2, and the shared eLpNorm tail all appear verbatim at lines 1024-1070. The children (830-841, 997-1009) contain no q, confirming the good-leaf claim: each is a self-contained one-constant bound closing on two named siblings, exactly the one-hole-per-bounded-prover shape, which the README states explicitly. | reviewer-generality |
| provenance-licence | accept | check_provenance pass (1 file byte-identical at d75f54374f7f930e70a86b443f20d0e0935c275e); commit d75f54374f7f930e70a86b443f20d0e0935c275e agrees across entry.json, README, source.json and SOURCE.md; licence Apache-2.0 in all four plus upstream-LICENSE is Apache-2.0 text; permalinks use the pinned commit and cite line ranges that match the copied file (parent forest_operator 1024-1070, forest_operator_g 830-841, forest_operator_f 997-1009, doc comments at 996 and 829); SOURCE.md carries the LICENSE link and attribution. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/fpvandoorn/carleson at commit `d75f54374f7f930e70a86b443f20d0e0935c275e`, under `Apache-2.0`; see the [source note](../../sources/carleson/SOURCE.md) for the licence text and attribution.
