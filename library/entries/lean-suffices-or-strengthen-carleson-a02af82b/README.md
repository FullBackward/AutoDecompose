# Suffices to split the pointwise tree estimate into three terms, each bounded by a named lemma (Carleson Lemma 7.1.3)

| | |
|---|---|
| Kind | instance |
| Move | suffices-or-strengthen |
| Language | lean |
| Status | accepted |
| Source | [carleson](../../sources/carleson/SOURCE.md) at `d75f54374f7f` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T10:57:34Z |

## Intent

The pointwise tree estimate (Lemma 7.1.3) bounds the Carleson sum of a
phase-modulated function `f` by a linear combination of the maximal function,
the boundary operator and the nontangential maximal function of `f`'s
approximation. The proof does not attack the bound directly: it rewrites the
summed kernel into three terms and uses one `suffices` to assert that the sum
of the three integrals equals the integral of the sum, so each term is then
bounded by its own named same-file lemma (Lemmas 7.1.4, 7.1.5, 7.1.6), with
two further lemmas absorbing their constants into the single constant `C7_1_3`.

## The decomposition

### parent `pointwise_tree_estimate`: [`Carleson/ForestOperator/PointwiseEstimate.lean` lines 1092-1160](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/ForestOperator/PointwiseEstimate.lean#L1092-L1160) ([local copy](code/Carleson/ForestOperator/PointwiseEstimate.lean))

```lean
lemma pointwise_tree_estimate (hu : u ∈ t) (hL : L ∈ 𝓛 (t u)) (hx : x ∈ L) (hx' : x' ∈ L)
    (hf : BoundedCompactSupport f) :
    ‖carlesonSum (t u) (fun y ↦ exp (.I * - 𝒬 u y) * f y) x‖ₑ ≤
    C7_1_3 a * (maximalFunction volume 𝓑 c𝓑 r𝓑 1 (approxOnCube (𝓙 (t u)) (‖f ·‖)) x' +
    t.boundaryOperator u (approxOnCube (𝓙 (t u)) (‖f ·‖)) x') +
    nontangentialMaximalFunction (𝒬 u) (approxOnCube (𝓙 (t u)) f) x' := by
  set g := approxOnCube (𝓙 (t u)) f
  -- Convert the sum over `p` into a sum over `s`.
  unfold carlesonSum carlesonOn
  rw [p_sum_eq_s_sum fun s x ↦ ∫ (y : X), cexp (I * (Q x y - Q x x)) * Ks s x y *
        (fun y ↦ cexp (I * -𝒬 u y) * f y) y]
  -- Next introduce an extra factor of `‖cexp (I * 𝒬 u x)‖ₑ`, i.e., 1. Then simplify.
  have : 1 = ‖cexp (I * 𝒬 u x)‖ₑ := by simp
  rw [← one_mul ‖_‖ₑ, this, ← enorm_mul, Finset.mul_sum]
  have : ∑ i ∈ t.σ u x, cexp (I * 𝒬 u x) * ∫ (y : X), (cexp (I * (Q x y - Q x x)) * Ks i x y *
            (cexp (I * -𝒬 u y) * f y)) =
          ∑ i ∈ t.σ u x, ∫ (y : X),
            (f y * ((exp (I * (- 𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1) * Ks i x y) +
            (f y - g y) * Ks i x y + g y * Ks i x y) := by
    simp_rw [Ks, mul_sub, mul_add, sub_eq_add_neg, exp_add]
    apply Finset.sum_congr rfl
    intro _ _
    apply (integral_const_mul ..).symm.trans
    apply integral_congr_ae
    exact (funext fun y ↦ by ring).eventuallyEq
  rw [this]
  -- It suffices to show that the integral splits into the three terms bounded by Lemmas 7.1.4-6
  suffices ∑ i ∈ t.σ u x, ∫ (y : X),
             (f y * ((cexp (I * (-𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1) * Ks i x y)) +
             (f y - g y) * Ks i x y + g y * Ks i x y =
           ∑ i ∈ t.σ u x,
             ((∫ (y : X), f y * ((cexp (I * (-𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1) * Ks i x y)) +
             (∫ (y : X), (f y - g y) * Ks i x y) + (∫ (y : X), g y * Ks i x y)) by
    -- Separate the LHS into three pieces
    rw [this, Finset.sum_add_distrib, Finset.sum_add_distrib]
    apply le_trans <| ENNReal.coe_strictMono.monotone <| (nnnorm_add_le _ _).trans
      (add_le_add_left (nnnorm_add_le _ _) _)
    rw [ENNReal.coe_add, ENNReal.coe_add, mul_add]
    -- Apply Lemmas 7.1.4, 7.1.5, and 7.1.6
    simp_rw [← mul_comm (Ks _ x _)]
    refine add_le_add_three ?_ ?_ (second_tree_pointwise hu hL hx hx')
    · simp_rw [mul_comm (Ks _ x _), mul_comm (f _)]
      have h : C7_1_3 a ≥ C7_1_4 a := C7_1_4_le_C7_1_3 (four_le_a X)
      exact (first_tree_pointwise hu hL hx hx' hf).trans <| mul_left_mono (by exact_mod_cast h)
    · have h : C7_1_3 a ≥ C7_1_6 a := C7_1_6_le_C7_1_3
      exact (third_tree_pointwise hu hL hx hx' hf).trans <| mul_left_mono (by exact_mod_cast h)
  -- In order to split the integral, we will first need some trivial integrability results
  have h1 {i : ℤ} : Integrable (fun y ↦ approxOnCube (𝓙 (t.𝔗 u)) f y * Ks i x y) := by
    classical
    apply (integrable_Ks_x <| one_lt_realD (K := K)).bdd_mul
      (c := ∑ J with J ∈ 𝓙 (t u), ‖⨍ y in J, f y‖)
    · exact (stronglyMeasurable_approxOnCube _ _).aestronglyMeasurable
    · refine ae_of_all _ fun x ↦ (norm_sum_le _ _).trans <| Finset.sum_le_sum (fun J hJ ↦ ?_)
      by_cases h : x ∈ (J : Set X)
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_apply, ite_eq_right h, norm_zero]
        exact norm_nonneg _
  have : ∀ (y : X), ‖cexp (I * (-𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1‖ ≤ 2 := by
    refine fun y ↦ le_of_le_of_eq (norm_sub_le _ _) ?_
    norm_cast
    rw [mul_comm, norm_exp_ofReal_mul_I, one_add_one_eq_two]
  have h2 {i : ℤ} : Integrable
      (fun y ↦ f y * ((cexp (I * (-𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1) * Ks i x y)) :=
    hf.integrable_mul <| (integrable_Ks_x <| one_lt_realD (K := K)).bdd_mul (c := 2)
      (Measurable.aestronglyMeasurable (by fun_prop)) (ae_of_all _ this)
  have h3 {i : ℤ} : Integrable (fun y ↦ (f y - approxOnCube (𝓙 (t.𝔗 u)) f y) * Ks i x y) := by
    simp_rw [sub_mul]
    exact hf.integrable_mul (integrable_Ks_x <| one_lt_realD (K := K)) |>.sub h1
  exact Finset.fold_congr fun i _ ↦ (by rw [integral_add _ h1, integral_add h2 h3]; exact h2.add h3)
```

### child `first_tree_pointwise`: [`Carleson/ForestOperator/PointwiseEstimate.lean` lines 602-668](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/ForestOperator/PointwiseEstimate.lean#L602-L668) ([local copy](code/Carleson/ForestOperator/PointwiseEstimate.lean))

```lean
lemma first_tree_pointwise (hu : u ∈ t) (hL : L ∈ 𝓛 (t u)) (hx : x ∈ L) (hx' : x' ∈ L)
    (hf : BoundedCompactSupport f) :
    ‖∑ i ∈ t.σ u x, ∫ y, (exp (.I * (-𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1) * Ks i x y * f y‖ₑ ≤
    C7_1_4 a * maximalFunction volume 𝓑 c𝓑 r𝓑 1 (approxOnCube (𝓙 (t u)) (‖f ·‖)) x' := by
  let _ : MulPosReflectLE ℝ := inferInstance -- perf: https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/performance.20example.20with.20type-class.20inference
  let _ : PosMulReflectLE ℝ := inferInstance -- perf: https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/performance.20example.20with.20type-class.20inference
  set g := approxOnCube (𝓙 (t u)) (‖f ·‖)
  let q (y) := -𝒬 u y + Q x y + 𝒬 u x - Q x x
  rcases (t.σ u x).eq_empty_or_nonempty with hσ | hσ; · simp [hσ]
  have : ∀ s ∈ t.σ u x, ‖∫ y, (cexp (I * (q y)) - 1) * Ks s x y * f y‖ₑ ≤
      ∫⁻ y, ‖(exp (I * q y) - 1) * Ks s x y * f y‖ₑ := fun s hs ↦
    (enorm_integral_le_lintegral_enorm _).trans (by simp)
  conv_lhs =>
    enter [1, 2, s, 2, y]
    rw [← Complex.ofReal_neg, ← Complex.ofReal_add, ← Complex.ofReal_add, ← Complex.ofReal_sub]
  refine (enorm_sum_le _ _).trans <| ((t.σ u x).sum_le_sum this).trans ?_
  suffices ∀ s ∈ t.σ u x, ∫⁻ y, ‖(exp (I * q y) - 1) * Ks s x y * f y‖ₑ ≤
      (5 * 2 ^ ((𝕔 + 4) * a ^ 3) * maximalFunction volume 𝓑 c𝓑 r𝓑 1 g x')
      * 2 ^ (s - t.σMax u x hσ) by
    apply ((t.σ u x).sum_le_sum this).trans
    rw [← Finset.mul_sum]
    apply le_trans <| mul_le_mul_right (L7_1_4_sum hσ) _
    rw [mul_comm _ 2, ← mul_assoc, ← mul_assoc, C7_1_4]
    gcongr; norm_num
  intro s hs
  have eq1 : ∫⁻ y, ‖(exp (I * q y) - 1) * Ks s x y * f y‖ₑ =
      ∫⁻ y in ball x (D ^ s / 2), ‖(exp (I * q y) - 1) * Ks s x y * f y‖ₑ := by
    rw [← lintegral_indicator measurableSet_ball]; congr! 2 with y
    symm; rw [indicator_apply_eq_self]; intro my
    suffices Ks s x y = 0 by simp [this]
    contrapose! my; apply dist_mem_Ioo_of_Ks_ne_zero at my
    rw [mem_Ioo] at my; rw [mem_ball']; exact my.2
  have eq2 : ∫⁻ y in ball x (D ^ s / 2), ‖(exp (I * q y) - 1) * Ks s x y * f y‖ₑ ≤
      5 * 2 ^ (s - σMax t u x ⟨s, hs⟩) * (2 ^ ((𝕔 + 3) * a ^ 3) / volume (ball x (D ^ s))) *
      ∫⁻ y in ball x (D ^ s / 2), ‖f y‖ₑ := by
    convert! (lintegral_mono (L7_1_4_integrand_bound f hu hs)).trans ?_
    · norm_cast
    · rw [lintegral_const_mul'' _ hf.aestronglyMeasurable.enorm.restrict]
  apply le_of_eq_of_le eq1 ∘ eq2.trans
  rw [← mul_rotate _ (5 * 2 ^ ((𝕔 + 4) * a ^ 3)), ← mul_assoc, mul_comm _ 5]
  simp_rw [mul_assoc]; gcongr _ * (_ * ?_)
  rw [show (𝕔 + 4) * a ^ 3 = (𝕔 + 3) * a ^ 3 + a ^ 3 by ring, pow_add, mul_assoc,
    ENNReal.mul_comm_div]
  gcongr
  have ⟨pₛ, pₛu, xpₛ, hpₛ⟩ := t.exists_p_of_mem_σ u x hs
  have ball_subset : ball (𝔠 pₛ) (16 * D ^ s) ⊆ ball x ((2 ^ 5) * D ^ s) := by
    apply ball_subset_ball'
    calc
      _ ≤ (16 : ℝ) * D ^ s + 4 * D ^ 𝔰 pₛ :=
        add_le_add_right (mem_ball'.mp (Grid_subset_ball xpₛ.1)).le _
      _ = 16 * D ^ s + 4 * D ^ s := by nth_rw 3 [← hpₛ]
      _ ≤ _ := by linarith only [defaultD_pow_pos a s]
  calc
  _ ≤ 2 ^ (5 * a) * ((∫⁻ y in ball x (D ^ s / 2), ‖f y‖ₑ) / volume (ball (𝔠 pₛ) (16 * D ^ s))) := by
    rw [mul_comm, ENNReal.div_mul _ (.inr (by positivity)) (.inr (by finiteness))]; gcongr
    refine ENNReal.div_le_of_le_mul' ((measure_mono ball_subset).trans ?_)
    convert! measure_ball_two_le_same_iterate (μ := volume) x (D ^ s) 5 using 2
    simp [mul_comm 5 a, pow_mul]
  _ ≤ _ := by
    gcongr ?_ * ?_
    · apply pow_right_mono₀ one_le_two
      rw [pow_succ a 2, mul_le_mul_iff_left₀ (a_pos X)]
      nlinarith [four_le_a X]
    · refine le_trans ?_ (L7_1_4_laverage_le_MB hL hx hx' g pₛu xpₛ)
      rw [hpₛ]; gcongr ?_ / _
      rw [← hpₛ]; exact L7_1_4_integral_le_integral hu hf pₛu xpₛ

```

### child `second_tree_pointwise`: [`Carleson/ForestOperator/PointwiseEstimate.lean` lines 671-752](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/ForestOperator/PointwiseEstimate.lean#L671-L752) ([local copy](code/Carleson/ForestOperator/PointwiseEstimate.lean))

```lean
lemma second_tree_pointwise (hu : u ∈ t) (hL : L ∈ 𝓛 (t u)) (hx : x ∈ L) (hx' : x' ∈ L) :
    ‖∑ i ∈ t.σ u x, ∫ y, Ks i x y * approxOnCube (𝓙 (t u)) f y‖ₑ ≤
    nontangentialMaximalFunction (𝒬 u) (approxOnCube (𝓙 (t u)) f) x' := by
  rcases (t.σ u x).eq_empty_or_nonempty with hne | hne; · simp [hne]
  let s₁ := Finset.min' (t.σ u x) hne
  have ms₁ : s₁ ∈ t.σ u x := Finset.min'_mem ..
  simp_rw [σ, Finset.mem_image, Finset.mem_filter_univ] at ms₁
  obtain ⟨p, ⟨mp, xp, _, _⟩, sp⟩ := ms₁
  have Lle : L ≤ 𝓘 p := by
    rcases 𝓛_subset_𝓛₀ hL with hL | hL
    · exact le_of_mem_of_mem (hL.symm ▸ scale_mem_Icc.1) hx xp
    · exact (le_or_ge_of_mem_of_mem xp hx).resolve_left (hL.2 p mp)
  let s₂ := Finset.max' (t.σ u x) hne
  have ms₂ : s₂ ∈ t.σ u x := Finset.max'_mem ..
  simp_rw [σ, Finset.mem_image, Finset.mem_filter_univ] at ms₂
  obtain ⟨p', ⟨mp', xp', Qxp', _⟩, sp'⟩ := ms₂
  have s_ineq : 𝔰 p ≤ 𝔰 p' := by
    rw [sp, sp']; exact (t.σ u x).min'_le s₂ (Finset.max'_mem ..)
  have pinc : 𝓘 p ≤ 𝓘 p' := le_of_mem_of_mem s_ineq xp xp'
  have d5 : dist_(p') (𝒬 u) (Q x) < 5 := dist_lt_5 hu mp' Qxp'
  have d5' : dist_{x, D ^ s₂} (𝒬 u) (Q x) < 5 * defaultA a ^ 5 := by
    have i1 : dist x (𝔠 p) < 4 * D ^ 𝔰 p' :=
      (mem_ball.mp (Grid_subset_ball xp)).trans_le <| by
        gcongr; exacts [one_le_realD _, s_ineq]
    have i2 : dist (𝔠 p') (𝔠 p) < 4 * D ^ 𝔰 p' :=
      mem_ball'.mp (ball_subset_Grid.trans (Grid.le_def.mp pinc).1 |>.trans Grid_subset_ball <|
        mem_ball_self (by unfold defaultD; positivity))
    calc
      _ ≤ dist_{𝔠 p, 8 * D ^ 𝔰 p'} (𝒬 u) (Q x) := by
        refine cdist_mono (ball_subset_ball' ?_); rw [← sp']
        calc
          _ ≤ (D : ℝ) ^ 𝔰 p' + 4 * D ^ 𝔰 p' := add_le_add_right i1.le _
          _ = 5 * D ^ 𝔰 p' := by ring
          _ ≤ _ := by gcongr; norm_num
      _ ≤ defaultA a * dist_{𝔠 p', 4 * D ^ 𝔰 p'} (𝒬 u) (Q x) := by
        convert cdist_le (x₂ := 𝔠 p) _ using 1
        · exact cdist_congr rfl (by ring)
        · apply i2.trans_le; nth_rw 1 [← one_mul (4 * _)]; gcongr; exact one_le_two
      _ ≤ defaultA a ^ 5 * dist_(p') (𝒬 u) (Q x) := by
        rw [pow_succ', mul_assoc]; gcongr
        convert! cdist_le_iterate _ (𝒬 u) (Q x) 4 using 1
        · exact cdist_congr rfl (by ring)
        · unfold defaultD; positivity
      _ < _ := by rw [mul_comm]; gcongr
  have d1 : dist_{x, D ^ (s₂ - 1)} (𝒬 u) (Q x) < 1 := by
    calc
      _ ≤ dist_{x, D ^ s₂} (𝒬 u) (Q x) * 2 ^ (-𝕔 * a : ℤ) := by
        rw [neg_mul, zpow_neg, le_mul_inv_iff₀ (by positivity), mul_comm]
        convert! le_cdist_iterate _ (𝒬 u) (Q x) (𝕔 * a) using 1
        · apply cdist_congr rfl
          rw [Nat.cast_pow, ← pow_mul, show a * (𝕔 * a) = 𝕔 * a ^ 2 by ring, ← Nat.cast_pow]
          change _ = (D : ℝ) * _
          rw [← zpow_one_add₀ (realD_pos _).ne', add_sub_cancel]
        · unfold defaultD; positivity
      _ < 5 * defaultA a ^ 5 * 2 ^ (-𝕔 * a : ℤ) := by gcongr
      _ = 5 * (2 : ℝ) ^ (-(𝕔 - 5) * a : ℤ) := by
        rw [Nat.cast_pow, ← pow_mul, ← zpow_natCast, show (2 : ℕ) = (2 : ℝ) by rfl, mul_assoc,
          ← zpow_add₀ two_ne_zero]
        congr
        simp
        ring
      _ ≤ 5 * 2 ^ (-3 : ℤ) := by
        gcongr
        · exact one_le_two
        · simp only [neg_sub, sub_mul, Int.reduceNeg, tsub_le_iff_right, le_neg_add_iff_add_le]
          norm_cast
          calc
          3 + 5 * a
          _ ≤ a + 5 * a := by gcongr; linarith [four_le_a X]
          _ = 6 * a := by ring
          _ ≤ 𝕔 * a := by gcongr; linarith [seven_le_c]
      _ < _ := by norm_num
  have x'p : x' ∈ 𝓘 p := (Grid.le_def.mp Lle).1 hx'
  refine le_iSup₂_of_le (𝓘 p) x'p <| le_iSup₂_of_le x xp <|
    le_iSup₂_of_le (𝔰 p') ⟨s_ineq, scale_mem_Icc.2⟩ <| le_iSup_of_le ?_ ?_
  · apply le_upperRadius; convert! d1
  · convert le_rfl; change (Icc (𝔰 p) _).toFinset = _; rw [sp, sp']
    apply subset_antisymm
    · rw [← Finset.toFinset_coe (t.σ u x), toFinset_subset_toFinset]
      exact (convex_scales hu).out (Finset.min'_mem ..) (Finset.max'_mem ..)
    · intro z mz; rw [toFinset_Icc, Finset.mem_Icc]
      exact ⟨Finset.min'_le _ _ mz, Finset.le_max' _ _ mz⟩
```

### child `third_tree_pointwise`: [`Carleson/ForestOperator/PointwiseEstimate.lean` lines 974-1065](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/ForestOperator/PointwiseEstimate.lean#L974-L1065) ([local copy](code/Carleson/ForestOperator/PointwiseEstimate.lean))

```lean
lemma third_tree_pointwise (hu : u ∈ t) (hL : L ∈ 𝓛 (t u)) (hx : x ∈ L) (hx' : x' ∈ L)
    (hf : BoundedCompactSupport f) :
    ‖∑ i ∈ t.σ u x, ∫ y, Ks i x y * (f y - approxOnCube (𝓙 (t u)) f y)‖ₑ ≤
    C7_1_6 a * t.boundaryOperator u (approxOnCube (𝓙 (t u)) (‖f ·‖)) x' := by
  classical
  let I (i : ℤ) (x : X) := ‖∫ (y : X), Ks i x y * (f y - approxOnCube (𝓙 (t u)) f y)‖ₑ
  let Js (p : 𝔓 X) := Set.toFinset <| { J ∈ 𝓙 (t u) | ↑J ⊆ ball x (16 * D ^ 𝔰 p) ∧ s J ≤ 𝔰 p }
  let ps (I : Grid X) := Finset.univ.filter (fun p ↦ p ∈ t u ∧ 𝓘 p = I)
  let 𝔗_fin := Finset.univ.filter (· ∈ t u)
  have A5_pos : (defaultA a : ℝ) ^ 5 > 0 := pow_pos (by norm_num) 5
  calc
    _ ≤ ∑ i ∈ t.σ u x, ‖∫ y, Ks i x y * (f y - approxOnCube (𝓙 (t u)) f y)‖ₑ :=
      enorm_sum_le (t.σ u x) _
    _ = ∑ p ∈ 𝔗_fin, (E p).indicator 1 x * I (𝔰 p) x := by
      rw [← p_sum_eq_s_sum I]
      simp_rw [indicator_eq_indicator_one_mul _ (I _), 𝔗_fin]
    _ ≤ ∑ p ∈ 𝔗_fin, (E p).indicator 1 x *
          (D2_1_3 a / (volume (ball x (D ^ 𝔰 p))) * 2 ^ (3 / a : ℝ) *
          ∑ J ∈ 𝓙' t u (𝔠 p) (𝔰 p), D ^ ((s J - 𝔰 p) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ) := by
      refine Finset.sum_le_sum fun J hJ ↦ ?_
      by_cases xJ : x ∈ E J
      · rw [indicator_of_mem xJ, Pi.one_apply, one_mul, one_mul]
        exact L7_1_6_I_le hu hf (Finset.mem_filter.mp hJ).2 xJ
      · simp only [indicator_of_notMem xJ, zero_mul, le_refl]
    _ = ∑ I : Grid X, ∑ p ∈ ps I, (E p).indicator 1 x *
          (D2_1_3 a / (volume (ball x (D ^ s I))) * 2 ^ (3 / a : ℝ) *
          ∑ J ∈ 𝓙' t u (c I) (s I), D ^ ((s J - s I) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ) := by
      let summand := fun (y : X) (i : ℤ) ↦
          D2_1_3 a / volume (ball x (D ^ i)) * 2 ^ (3 / a : ℝ) *
          ∑ J ∈ 𝓙' t u y i, D ^ ((s J - (i : ℝ)) / a) * ∫⁻ y in J, ‖f y‖ₑ
      exact sum_p_eq_sum_I_sum_p t u x summand
    _ ≤ ∑ I : Grid X, ∑ p ∈ ps I, (E p).indicator 1 x *
          (D2_1_3 a / (volume (ball (c I) (16 * D ^ s I)) / defaultA a ^ 5) *
          2 ^ (3 / a : ℝ) *
          ∑ J ∈ 𝓙' t u (c I) (s I), D ^ ((s J - s I) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ) := by
      refine Finset.sum_le_sum fun I _ ↦ Finset.sum_le_sum fun p hp ↦ ?_
      by_cases xEp : x ∈ E p; swap
      · simp only [indicator_of_notMem xEp, zero_mul, le_refl]
      apply mul_le_mul_right
      gcongr; apply ENNReal.div_le_of_le_mul'
      calc
        _ ≤ volume (ball x (32 * D ^ s I)) := by
          refine measure_mono (ball_subset_ball' ?_)
          suffices dist (c I) x < 4 * D ^ (s I) by linarith [defaultD_pow_pos a (s I)]
          exact mem_ball'.mp <| (Finset.mem_filter.mp hp).2.2 ▸ Grid_subset_ball (E_subset_𝓘 xEp)
        _ ≤ _ := by
          rw [show (32 : ℝ) = 2 ^ 5 by norm_num]
          exact measure_ball_two_le_same_iterate x (D ^ s I) 5
    _ ≤ ∑ I : Grid X, ((I : Set X).indicator 1 x') *
          (D2_1_3 a / (volume (ball (c I) (16 * D ^ s I)) / defaultA a ^ 5) *
          2 ^ (3 / a : ℝ) *
          ∑ J ∈ 𝓙' t u (c I) (s I), D ^ ((s J - s I) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ) := by
      simp_rw [← Finset.sum_mul]
      gcongr with I hI
      by_cases! ex : ∃ p ∈ ps I, x ∈ E p
      · obtain ⟨p, hp, xEp⟩ := ex
        have L_subset_I : (L : Set X) ⊆ (I : Set X) := by
          simp only [ps, Finset.mem_filter] at hp
          exact hp.2.2 ▸ subset_of_mem_𝓛 hL hp.2.1 (not_disjoint_iff.mpr ⟨x, ⟨E_subset_𝓘 xEp, hx⟩⟩)
        simp only [L_subset_I hx', indicator_of_mem, Pi.one_apply]
        rw [Finset.sum_eq_single_of_mem p hp]
        · exact le_of_eq <| (indicator_eq_one_iff_mem _).mpr xEp
        · intro p' hp' p'_ne_p
          simp only [ps, Finset.mem_filter] at hp hp'
          exact (indicator_eq_zero_iff_notMem _).mpr fun xEp' ↦
            disjoint_left.mp (disjoint_Ω p'_ne_p (hp'.2.2.trans hp.2.2.symm)) xEp'.2.1 xEp.2.1
      · suffices ∑ p ∈ ps I, (E p).indicator (1 : X → ℝ≥0∞) x = 0 by rw [this]; exact zero_le
        exact Finset.sum_eq_zero (fun p hp ↦ indicator_of_notMem (ex p hp) _)
    _ = ∑ I : Grid X, ((I : Set X).indicator 1 x') *
          ((D2_1_3 a * defaultA a ^ 5 * 2 ^ (3 / a : ℝ)) /
          volume (ball (c I) (16 * D ^ s I)) *
          ∑ J ∈ 𝓙' t u (c I) (s I), D ^ ((s J - s I) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ) := by
      congr! 2 with I
      rw [← ENNReal.div_mul _ (.inr (by positivity)) (.inr (by finiteness)), mul_rotate (_ / _),
        ← mul_div_assoc]
      congr 2; ring
    _ ≤ ∑ I : Grid X, ((I : Set X).indicator 1 x') *
          (C7_1_6 a / volume (ball (c I) (16 * D ^ s I)) *
          ∑ J ∈ 𝓙' t u (c I) (s I), D ^ ((s J - s I) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ) := by
      gcongr; exact le_C7_1_6 (four_le_a X)
    _ = C7_1_6 a *
        ∑ I : Grid X, ((I : Set X).indicator 1 x') *
          (1 / volume (ball (c I) (16 * D ^ s I)) *
          ∑ J ∈ 𝓙' t u (c I) (s I), D ^ ((s J - s I) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ) := by
      rw [Finset.mul_sum]; congr! 1 with I
      simp_rw [← mul_assoc, ← mul_div_assoc, mul_one, mul_comm (C7_1_6 a : ℝ≥0∞)]
    _ = _ := by
      unfold boundaryOperator; congr! 2 with I
      simp_rw [← indicator_mul_const, Pi.one_apply, one_mul]; congr! 2
      rw [Finset.mul_sum]; congr! 2 with J hJ
      rw [← mul_assoc, mul_comm (_ / _), ← mul_div_assoc, mul_one, ijIntegral]; congr! 1
      exact lintegral_eq_lintegral_approxOnCube pairwiseDisjoint_𝓙 (mem_𝓙_of_mem_𝓙' hJ) hf
```

### child `C7_1_4_le_C7_1_3`: [`Carleson/ForestOperator/PointwiseEstimate.lean` lines 1077-1089](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/ForestOperator/PointwiseEstimate.lean#L1077-L1089) ([local copy](code/Carleson/ForestOperator/PointwiseEstimate.lean))

```lean
lemma C7_1_4_le_C7_1_3 {a : ℕ} (ha : 4 ≤ a) : C7_1_4 a ≤ C7_1_3 a := by
  have : (10 : ℝ≥0) ≤ 2 ^ 4 := by norm_num
  grw [C7_1_4_def, C7_1_3_def, this, ← pow_add]
  gcongr
  · norm_num
  suffices 4 ≤ (𝕔 / 4) * a ^ 3 by linarith
  have : 4 ≤ (4 / 4) * a ^ 3 := calc
    4 = 4 * 1 * 1 := by norm_num
    _ ≤ a * a * a := by gcongr <;> linarith
    _ = (4 / 4) * a ^ 3 := by ring
  apply this.trans
  gcongr
  linarith [seven_le_c]
```

### child `C7_1_6_le_C7_1_3`: [`Carleson/ForestOperator/PointwiseEstimate.lean` lines 1071-1075](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/ForestOperator/PointwiseEstimate.lean#L1071-L1075) ([local copy](code/Carleson/ForestOperator/PointwiseEstimate.lean))

```lean
lemma C7_1_6_le_C7_1_3 {a : ℕ} : C7_1_6 a ≤ C7_1_3 a := by
  rw [C7_1_6_def, C7_1_3_def]
  gcongr
  · norm_num
  · lia
```

How the parts fit. The glue (`pointwise_tree_estimate`) is a chain of rewrites
followed by one `suffices` and a little bookkeeping. Its shape, in text:

```
pointwise_tree_estimate (Lemma 7.1.3)
├── first_tree_pointwise (Lemma 7.1.4) — the oscillation term, → C7_1_4 · maximalFunction
│     └── L7_1_4_sum · L7_1_4_integrand_bound · L7_1_4_laverage_le_MB · L7_1_4_integral_le_integral
├── second_tree_pointwise (Lemma 7.1.5) — the main term, → nontangentialMaximalFunction
│     └── dist_lt_5 · le_cdist_iterate · cdist_le · convex_scales
├── third_tree_pointwise (Lemma 7.1.6) — the error term, → C7_1_6 · boundaryOperator
│     └── p_sum_eq_s_sum · L7_1_6_I_le · sum_p_eq_sum_I_sum_p · le_C7_1_6 · lintegral_eq_lintegral_approxOnCube
├── C7_1_4_le_C7_1_3 — folds C7_1_4 into C7_1_3 (needs 4 ≤ a)
└── C7_1_6_le_C7_1_3 — folds C7_1_6 into C7_1_3
```

Reading the glue top to bottom: after `set g := approxOnCube (𝓙 (t u)) f`, it
unfolds `carlesonSum`/`carlesonOn` and converts the sum over tiles `p` into the
sum over scales `s` (`p_sum_eq_s_sum`, line 1101); introduces a unit phase
`1 = ‖cexp (I * 𝒬 u x)‖ₑ`; and rewrites the summed kernel into the three terms
`f·((cexp(…) − 1)·Ks)`, `(f − g)·Ks` and `g·Ks`. Then the single `suffices`
(line 1119) replaces the goal by "the sum of the three integrals equals the
integral of the sum", which is discharged at the very end by
`Finset.fold_congr` once the three integrability facts `h1`, `h2`, `h3`
(lines 1139-1159) are proved. With that exchange in hand, the three terms are
combined by `add_le_add_three` and bounded by the three `*_tree_pointwise`
lemmas, each scaled up to `C7_1_3` by the constant lemmas
`C7_1_4_le_C7_1_3` and `C7_1_6_le_C7_1_3`.

Each child is a good leaf because its statement is self-contained and its
proof closes on its own or from named same-file siblings, never from the
parent:

- `first_tree_pointwise` closes with its own `suffices` (`∀ s ∈ t.σ u x, …`)
  followed by a `calc` chain, using only the four private siblings `L7_1_4_*`.
- `second_tree_pointwise` closes by building `iSup` witnesses from the
  scale-extremal points and the distance estimates `dist_lt_5`,
  `le_cdist_iterate`, `cdist_le`, `convex_scales`; unlike the other two
  tree-pointwise lemmas it needs no `hf` hypothesis.
- `third_tree_pointwise` closes with a `calc` chain from the σ-sum to the
  `boundaryOperator` sum, using the sum-conversion and integral lemmas.
- `C7_1_4_le_C7_1_3` and `C7_1_6_le_C7_1_3` are pure constant comparisons
  closed by `gcongr`/`norm_num`/`lia` (the first needs a one-line `suffices`
  for `4 ≤ (𝕔 / 4) · a³`).

In my opinion the detail worth copying is the division of labour: the glue
does only algebra, the triangle inequality and integrability; every analytic
estimate lives in a leaf whose statement is a bound on one of the three terms.

## Why it is good

1. The parent proof closes with no `sorry`, `admit` or `axiom` token
   (`check`, `no_sorry(Carleson/ForestOperator/PointwiseEstimate.lean,
   1092-1160)`; lines 1092-1160).
2. The parent `pointwise_tree_estimate` is a real declaration in
   `Carleson/ForestOperator/PointwiseEstimate.lean` at lines 1092-1160
   (`check`, `declared(pointwise_tree_estimate, …)`).
3. The glue cites the children: `first_tree_pointwise` occurs in the parent's
   lines (`check`, `cites(pointwise_tree_estimate, first_tree_pointwise)`),
   and the strict validator confirms all five are cited.
4. The theorem-scale shape is `direct_lemmas = 5`, `glue_lines = 69`,
   `child_lines = [67, 82, 92, 13, 5]`, `depth = 3`
   (`measurement`, counted from the copied file; the depth chain is
   pointwise_tree_estimate → first_tree_pointwise → L7_1_4_laverage_le_MB →
   subset_of_mem_𝓛).
5. The authors mark the move themselves: the comment "It suffices to show that
   the integral splits into the three terms bounded by Lemmas 7.1.4-6"
   (line 1118) and the docstring tags `/-- Lemma 7.1.3. -/`, `/-- Lemma 7.1.4
   -/`, `/-- Lemma 7.1.5 -/`, `/-- Lemma 7.1.6 -/` (lines 1091, 601, 670,
   973) (`author-statement`).

## When to use it, and when not

Use it when the target is a bound on a sum of integrals whose integrand
separates by plain algebra into a few terms, each term already bounded (or
easily bounded) by its own lemma, and the constants of those lemmas can be
folded into the parent's constant. The `suffices`-by-equality here is the
"prove a more convenient statement" move: instead of bounding the sum
directly, prove that the sum of the three integrals equals the integral of the
sum, then bound each piece separately.

Avoid it when the terms cannot be separated by the triangle inequality and
linearity (cross terms, or one term that dominates the others and needs joint
control), when the integrability side conditions are themselves the hard part
rather than a routine `Integrable` chase, or when there is no constant lemma
to absorb the per-term constants — otherwise the parent's conclusion is left
with a sum of distinct constants instead of the single `C7_1_3`.

## Consequences

The move trades one hard bound for three leaf lemmas plus two constant lemmas,
but it creates obligations of its own: each term needs its own bound lemma;
the constants need the two `C7_1_*_le_C7_1_3` lemmas; and, critically, the
`suffices` exchange needs the three integrability facts `h1`, `h2`, `h3`
before `Finset.fold_congr` will close it. If any term is not integrable, or
the terms interact, the exchange and the `add_le_add_three` combination both
break, and the `suffices` must be re-posed with a different split.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push.yml (build_project job, leanprover/lean-action build:true build-args 'Carleson Challenge Solution') runs on push to master; pinned commit d75f54374f7f930e70a86b443f20d0e0935c275e is an ancestor of master (api compare behind_by=0); PointwiseEstimate.lean is under Carleson/ForestOperator/, part of the Carleson build target | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: first_tree_pointwise@Carleson/ForestOperator/PointwiseEstimate.lean:1135, second_tree_pointwise@Carleson/ForestOperator/PointwiseEstimate.lean:1132, third_tree_pointwise@Carleson/ForestOperator/PointwiseEstimate.lean:1137, C7_1_4_le_C7_1_3@Carleson/ForestOperator/PointwiseEstimate.lean:1134, C7_1_6_le_C7_1_3@Carleson/ForestOperator/PointwiseEstimate.lean:1136; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at d75f54374f7f930e70a86b443f20d0e0935c275e | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | no_sorry(Carleson/ForestOperator/PointwiseEstimate.lean, 1092-1160) -> no_sorry: none of sorry, admit, axiom in Carleson/ForestOperator/PointwiseEstimate.lean:1092-1160 | check_claims.py |
| 2 | verified | declared(pointwise_tree_estimate, Carleson/ForestOperator/PointwiseEstimate.lean, 1092-1160) -> declared: pointwise_tree_estimate is declared at Carleson/ForestOperator/PointwiseEstimate.lean:1092 | check_claims.py |
| 3 | verified | cites(pointwise_tree_estimate, first_tree_pointwise) -> cites: first_tree_pointwise occurs at Carleson/ForestOperator/PointwiseEstimate.lean:1135 | check_claims.py |
| 4 | verified | counted from code/Carleson/ForestOperator/PointwiseEstimate.lean: 5 children; parent 1092-1160 (69 lines); children 602-668 (67), 671-752 (82), 974-1065 (92), 1077-1089 (13), 1071-1075 (5); depth chain: first_tree_pointwise at 1135, L7_1_4_laverage_le_MB at 665 (inside first_tree_pointwise), subset_of_mem_𝓛 at 593 (inside L7_1_4_laverage_le_MB, declared at 582) | verifier |
| 5 | verified | read lines of PointwiseEstimate.lean: comment '-- It suffices to show that the integral splits into the three terms bounded by Lemmas 7.1.4-6' at 1118; docstrings '/-- Lemma 7.1.3. -/' at 1091, '/-- Lemma 7.1.4 -/' at 601, '/-- Lemma 7.1.5 -/' at 670, '/-- Lemma 7.1.6 -/' at 973 | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent pointwise_tree_estimate is declared at 1091/statement 1092-1160 and matches entry.json; all five children are at their stated ranges with matching statements (first 602-668, second 671-752, third 974-1065, C7_1_4_le_C7_1_3 1077-1089, C7_1_6_le_C7_1_3 1071-1075). Closing methods match the code: first_tree_pointwise closes via its own suffices+calc+gcongr using L7_1_4_*; second via le_iSup witnesses with dist_lt_5/le_cdist_iterate/cdist_le/convex_scales; third via calc with p_sum_eq_s_sum/L7_1_6_I_le/sum_p_eq_sum_I_sum_p/le_C7_1_6/lintegral_eq_lintegral_approxOnCube; the two constant lemmas by gcongr/norm_num/lia(+suffices). The parent closes with 'exact Finset.fold_congr' at line 1160 and no sorry/admit/axiom occurs anywhere in the file. The glue cites exactly these five lemmas (1132,1134,1135,1136,1137), matching glue-cites-children. Shape numbers are right: direct_lemmas=5, glue_lines=69 (1092-1160), child_lines=[67,82,92,13,5], depth=3 (pointwise_tree_estimate -> first_tree_pointwise:1135 -> L7_1_4_laverage_le_MB:665 -> subset_of_mem_𝓛:593). | reviewer-correctness |
| generality | accept | Move generalises beyond the Carleson example: use_when/avoid_when abstract to 'a bound on a sum of integrals whose integrand separates by plain algebra into a few terms, each bounded by its own named lemma, with per-term constants folded into the parent constant'. 'Avoid when' is honest and specific, tracing to real mechanisms: cross/dominating terms that resist triangle-inequality+linearity split, integrability side conditions (h1/h2/h3, lines 1139-1157) as the hard part, and absence of constant lemmas (C7_1_4_le_C7_1_3, C7_1_6_le_C7_1_3). Consequences name the true obligations and failure modes (non-integrable term breaks the Finset.fold_congr exchange; interacting terms break add_le_add_three). Good-leaves question answered explicitly: 'each child is a good leaf because its statement is self-contained and its proof closes on its own or from named same-file siblings, never from the parent', with child_lines [67,82,92,13,5] quantifying boundedness. Line numbers in the prose verified against the local copy. | reviewer-generality |
| provenance-licence | accept | Provenance consistent and traceable. check_provenance.py: pass, 1 file byte-identical at d75f54374f7f930e70a86b443f20d0e0935c275e; copied-file sha256 (c28d96b7...) matches entry.json files[].sha256. Commit is identical across README, entry.json, source.json and sources/carleson/SOURCE.md (full hash d75f54374f7f930e70a86b443f20d0e0935c275e). Licence Apache-2.0 stated identically in entry.json, README, SOURCE.md, source.json and the copied upstream-LICENSE is the standard Apache-2.0 text. All permalinks use the same commit + file path; sed of the copied file confirms the cited line ranges match the declarations (parent 1092-1160, first 602-668, second 671-752, third 974-1065, C7_1_4 1077-1089, C7_1_6 1071-1075; docstrings at 1091/601/670/973, suffices comment at 1118), and line-count metrics match child_lines [67,82,92,13,5]. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/fpvandoorn/carleson at commit `d75f54374f7f930e70a86b443f20d0e0935c275e`, under `Apache-2.0`; see the [source note](../../sources/carleson/SOURCE.md) for the licence text and attribution.
