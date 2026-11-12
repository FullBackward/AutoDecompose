# Thirteen-link calc bounding f/Δ for polynomially-growing Fourier coefficients

| | |
|---|---|
| Kind | instance |
| Move | calc-chain |
| Language | lean |
| Status | accepted |
| Source | [sphere-packing](../../sources/sphere-packing/SOURCE.md) at `efe3bbbc1ece` |
| Licence | `Apache-2.0` |

## Intent

Prove the blueprint's Lemma 7.4 — an upper bound on the ratio of a function with
polynomially-growing Fourier coefficients to the modular discriminant Δ — as one
monotone `calc` chain, with one private `step_N` lemma per link. Each factor of
the product (the leading exponential, the sum of coefficient norms, the infinite
product) is then bounded by its own small lemma, so the main proof is nothing but
the sequence of lemma references.

## The decomposition

### parent `DivDiscBoundOfPolyFourierCoeff`: [`SpherePacking/MagicFunction/PolyFourierCoeffBound.lean` lines 457-487](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean#L457-L487) ([local copy](code/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean))

```lean
theorem DivDiscBoundOfPolyFourierCoeff : norm ((f z) / (Δ z)) ≤
  (DivDiscBound c n₀) * rexp (-π * (n₀ - 2) * z.im) := calc
  _ = norm ((∑' (n : ℕ), c (n + n₀) * cexp (π * I * (n + n₀) * z)) /
      (cexp (2 * π * I * z) * ∏' (n : ℕ+),
      (1 - cexp (2 * π * I * n * z)) ^ 24)) := step_1 z c n₀ f hf
  _ = norm ((cexp (π * I * n₀ * z) * ∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := step_2 z c n₀
  _ = norm ((cexp (π * I * n₀ * z) / cexp (2 * π * I * z)) *
      (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := step_3 z c n₀
  _ = norm ((cexp (π * I * (n₀ - 2) * z)) *
      (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)) := step_4 z c n₀
  _ = norm (cexp (π * I * (n₀ - 2) * z)) *
      norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      norm (∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24) := step_5 z c n₀
  _ = norm (cexp (π * I * (n₀ - 2) * z)) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      ∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24 := step_6 z c n₀
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
      (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := step_7 z c n₀
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * norm (cexp (π * I * n * z))) /
      (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := step_8 z c n₀ hcsum
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
      (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := step_9 z c n₀ hcsum
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
      (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := step_10 z c n₀
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
      (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := step_11 z hz c n₀ hcsum k hpoly
  _ ≤ rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
      (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24) := step_12 z hz c n₀
  _ = (DivDiscBound c n₀) * rexp (-π * (n₀ - 2) * z.im) := step_13 z c n₀
```

### child `step_1`: [`SpherePacking/MagicFunction/PolyFourierCoeffBound.lean` lines 192-197](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean#L192-L197) ([local copy](code/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean))

```lean
include hf in
private lemma step_1 :
    norm ((f z) / (Δ z)) = norm (
      (∑' (n : ℕ), c (n + n₀) * cexp (π * I * (n + n₀) * z)) /
      (cexp (2 * π * I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * I * n * z)) ^ 24)
    ) := by simp [DiscriminantProductFormula, hf, fouterm];
```

### child `step_7`: [`SpherePacking/MagicFunction/PolyFourierCoeffBound.lean` lines 247-255](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean#L247-L255) ([local copy](code/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean))

```lean
private lemma step_7 :
    norm (cexp (π * I * (n₀ - 2) * z)) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    ∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24 ≤
    rexp (-π * (n₀ - 2) * z.im) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  gcongr
  · exact aux_6 z
  · norm_cast
    exact aux_7 z (n₀ - 2)
```

### child `step_8`: [`SpherePacking/MagicFunction/PolyFourierCoeffBound.lean` lines 257-270](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean#L257-L270) ([local copy](code/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean))

```lean
include hcsum in
private lemma step_8 :
    rexp (-π * (n₀ - 2) * z.im) * norm (∑' (n : ℕ), c (n + n₀) * cexp (π * I * n * z)) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * norm (cexp (π * I * n * z))) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  gcongr
  · exact aux_6 z
  · calc
    _ ≤ ∑' (n : ℕ), norm ((c (n + n₀)) * (cexp (↑π * I * ↑n * z))) := by
      refine norm_tsum_le_tsum_norm ?_
      exact aux_3 z c n₀ hcsum
    _ = ∑' (n : ℕ), norm (c (n + n₀)) * norm (cexp (↑π * I * ↑n * z)) :=
      by simp only [norm_mul]
```

### child `step_9`: [`SpherePacking/MagicFunction/PolyFourierCoeffBound.lean` lines 272-283](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean#L272-L283) ([local copy](code/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean))

```lean
include hcsum in
private lemma step_9 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * norm (cexp (π * I * n * z))) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) := by
  gcongr
  · exact aux_6 z
  · exact (aux_4 z c n₀ hcsum)
  · exact aux_10 z c n₀ hcsum
  · rw [Complex.norm_exp]
    simp
```

### child `step_10`: [`SpherePacking/MagicFunction/PolyFourierCoeffBound.lean` lines 285-318](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean#L285-L318) ([local copy](code/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean))

```lean
private lemma step_10 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
    (∏' (n : ℕ+), norm (1 - cexp (2 * π * I * n * z)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
    (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) :=
by
  have hpow : ∀ {ι} (f : ι → ℝ), Multipliable f → ∀ n, Multipliable (fun i => f i ^ n) := by
    intro ι f hf n
    induction n with
    | zero => simp [(multipliable_one : Multipliable (fun _ : ι => (1 : ℝ)))]
    | succ n hn => simpa [pow_succ] using (hn.mul hf)
  gcongr
  · exact aux_8 z
  · apply tprod_le_of_nonneg_of_multipliable
    · intro n; simp
      have : (1 - rexp (-(2 * π * ↑↑n * z.im))) ^ 24 =
          ((1 - rexp (-(2 * π * ↑↑n * z.im))) ^ 12) ^ 2 := by ring_nf
      rw [this]; exact sq_nonneg _
    · intro n; simp only [neg_mul]; gcongr
      · simp only [sub_nonneg, exp_le_one_iff, Left.neg_nonpos_iff]; positivity
      · have hre : -(2 * π * n * z.im) = (2 * π * I * n * z).re := by simp
        rw [hre]; exact aux_2 (2 * π * I * n * z)
    · have h_base : Multipliable (fun b : ℕ+ => 1 - rexp (-2 * π * ↑↑b * z.im)) := by
        apply Real.multipliable_of_summable_log
        · intro i; simp [pi_pos, UpperHalfPlane.im_pos]
        · simp_rw [sub_eq_add_neg]
          apply Real.summable_log_one_add_of_summable
          apply Summable.neg
          conv => lhs; equals (fun (b : ℕ) => Real.exp (-2 * π * b * z.im)) ∘ (PNat.val) => rfl
          apply Summable.subtype
          simp_rw [mul_comm, mul_assoc, Real.summable_exp_nat_mul_iff]
          simp [pi_pos, UpperHalfPlane.im_pos]
      exact hpow _ h_base 24
    · exact hpow _ (MultipliableEtaProductExpansion_pnat z).norm 24
```

### child `step_11`: [`SpherePacking/MagicFunction/PolyFourierCoeffBound.lean` lines 320-352](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean#L320-L352) ([local copy](code/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean))

```lean
include hz hcsum hpoly in
private lemma step_11 :
  rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n * z.im)) /
  (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) ≤
  rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
  (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) := by
  gcongr
  · exact le_of_lt (aux_8 z)
  · exact aux_10 z c n₀ hcsum
  · simp only [div_eq_mul_inv]
    -- **This is where we use the fact that c is eventually polynomial in n.**
    have hnorm : ‖(rexp (-π * 2⁻¹) : ℂ)‖ < 1 := by
      rw [Complex.norm_real]
      simp; positivity
    have h₁ : ∀ (n : ℕ), rexp (-π * n * 2⁻¹) = (rexp (-π * 2⁻¹)) ^ n := by
      intro n; symm
      calc (rexp (-π * 2⁻¹)) ^ n
      _ = rexp ((-π * 2⁻¹) * n) := by
        have := (Real.exp_mul (-π * 2⁻¹) n).symm
        norm_cast at this
      _ = rexp (-π * ↑n * 2⁻¹) := by congr 1; ring
    have h₂ : ∀ (n : ℕ), ‖c (↑n + n₀)‖ * rexp (-π * 2⁻¹) ^ n =
        ‖c (↑n + n₀) * rexp (-π * 2⁻¹) ^ n‖ := fun n => by
      rw [norm_mul, neg_mul, norm_pow, Complex.norm_real]
      simp
    simp only [h₁, h₂]
    have := hpoly' c n₀ k hpoly
    norm_cast at this
    exact summable_real_norm_mul_geometric_of_norm_lt_one hnorm this
  · have : -π * ↑n / 2 = -π * ↑n * (1 / 2) := by rw [mul_one_div]
    rw [this]
    simp only [neg_mul]
    gcongr
```

### child `step_12`: [`SpherePacking/MagicFunction/PolyFourierCoeffBound.lean` lines 406-440](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean#L406-L440) ([local copy](code/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean))

```lean
include hz in
private lemma step_12 :
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
    (∏' (n : ℕ+), (1 - rexp (-2 * π * n * z.im)) ^ 24) ≤
    rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
    (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24) := by
  gcongr
  · -- This allows us to get rid of the numerators
    exact aux_11
  · apply tprod_le_of_nonneg_of_multipliable
    · intro n; simp
      have : (1 - rexp (-(π * ↑↑n))) ^ 24 = ((1 - rexp (-(π * ↑↑n))) ^ 12) ^ 2 := by ring
      rw [this]
      exact sq_nonneg ((1 - rexp (-(π * ↑↑n))) ^ 12)
    · intro n; simp
      suffices this : 1 - rexp (-(π * ↑↑n)) < 1 - rexp (-2 * π * ↑↑n * z.im) by
        apply le_of_lt
        have h₁ : 0 ≤ 1 - rexp (-(π * ↑↑n)) := by norm_num; positivity
        have h₂ : 0 ≤ 1 - rexp (-2 * π * ↑↑n * z.im) := by linarith
        have h₃ : 24 ≠ 0 := by positivity
        have h₄ : (1 - rexp (-(2 * π * ↑↑n * z.im))) ^ 24 = (1 - rexp (-2 * π * ↑↑n * z.im)) ^ 24 :=
          by ring_nf
        rw [h₄]
        exact (pow_lt_pow_iff_left₀ h₁ h₂ h₃).mpr this
      gcongr; simp; ring_nf
      calc π * ↑↑n
      _ ≤ π * ↑↑n * 1 := by rw [mul_one]
      _ < π * ↑↑n * z.im * 2 := by
        rw [mul_assoc (π * ↑↑n), mul_lt_mul_iff_right₀ (by positivity)]
        linarith
    · exact step_12a pi_pos
    · conv_lhs =>
        intro b
        rw [mul_assoc, mul_comm _ z.im, ←mul_assoc, neg_mul, neg_mul]
      apply step_12a (mul_pos two_pi_pos (UpperHalfPlane.im_pos z))
```

### child `step_13`: [`SpherePacking/MagicFunction/PolyFourierCoeffBound.lean` lines 442-446](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean#L442-L446) ([local copy](code/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean))

```lean
private lemma step_13 :
  rexp (-π * (n₀ - 2) * z.im) * (∑' (n : ℕ), norm (c (n + n₀)) * rexp (-π * n / 2)) /
  (∏' (n : ℕ+), (1 - rexp (-π * n)) ^ 24) =
  (DivDiscBound c n₀) * rexp (-π * (n₀ - 2) * z.im) := by
  rw [DivDiscBound, mul_div_assoc, mul_comm]
```

### How the parts fit

The parent `DivDiscBoundOfPolyFourierCoeff` is a single `calc` of 13 links. Each
link is a step of the form `_ = … := step_N z c n₀ …` (equality) or `_ ≤ … :=
step_N …` (inequality), so the chain itself checks transitivity and the only
obligation each child carries is that its left-hand side definitionally matches
the previous link's right-hand side. The 13 children run

```
step_1 → step_2 → step_3 → step_4 → step_5 → step_6 → step_7 → step_8
→ step_9 → step_10 → step_11 → step_12 → step_13
```

where `A → B` means the right-hand side of `A` is the left-hand side of `B`.
Eight of the thirteen are shown above as excerpts; the other five are pure
algebra that re-arranges the expression between the unfolding and the first
inequality, and are listed with permalinks below.

* **step_1** (shown) unfolds `f z` by `hf`/`fouterm` and `Δ` by
  `DiscriminantProductFormula`, turning the goal into a ratio of a Fourier sum
  over a `cexp`-product. Closes with one `simp`.
* **step_2** [L199-L210](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean#L199-L210) pulls the constant `cexp (π·I·n₀·z)` out of the `tsum` (`rw [← tsum_mul_left]` then `ring`).
* **step_3** [L212-L217](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean#L212-L217) folds that factor into the numerator as `cexp (π·I·n₀·z) / cexp (2·π·I·z)`, closed by `field_simp`.
* **step_4** [L219-L228](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean#L219-L228) simplifies the exponent quotient to `cexp (π·I·(n₀-2)·z)` (`Complex.exp_sub` + `ac_rfl`).
* **step_5** [L230-L237](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean#L230-L237) pushes `norm` through the product and division (`simp only [norm_div, norm_mul]`).
* **step_6** [L239-L245](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean#L239-L245) pushes `norm` through the infinite product via `aux_5`.
* **step_7** (shown) is the first inequality: `norm (cexp (π·I·(n₀-2)·z)) ≤ rexp (-π·(n₀-2)·z.im)`, by `gcongr` with `aux_6` (denominator nonnegative) and `aux_7`.
* **step_8** (shown) applies the triangle inequality to the infinite sum, `norm_tsum_le_tsum_norm`, using summability `aux_3`.
* **step_9** (shown) replaces `norm (cexp (π·I·n·z))` pointwise by `rexp (-π·n·z.im)`, via `aux_4`/`aux_10` and `Complex.norm_exp`.
* **step_10** (shown) bounds the product factor `norm (1 - cexp (2·π·I·n·z))` below by `1 - rexp (-2·π·n·z.im)`, using `tprod_le_of_nonneg_of_multipliable` and `aux_2`; its proof also establishes the two `Multipliable` side conditions (`aux_8`, `MultipliableEtaProductExpansion_pnat`).
* **step_11** (shown) is the crux: with `z.im > 1/2` and the polynomial growth `hpoly`, it replaces `rexp (-π·n·z.im)` by `rexp (-π·n/2)` in the numerator sum, via `summable_real_norm_mul_geometric_of_norm_lt_one` and `hpoly'`.
* **step_12** (shown) bounds the product `(1 - rexp (-2·π·n·z.im))^24 ≤ (1 - rexp (-π·n))^24` using `z.im > 1/2`, through `step_12a` (summability of the geometric product).
* **step_13** (shown) recognises the result as `(DivDiscBound c n₀) * rexp (-π·(n₀-2)·z.im)` by unfolding `DivDiscBound`.

Why each is a good leaf: every step is a self-contained statement whose proof
closes either by a single `simp`/`field_simp`/`rw` or from the named siblings
`aux_1…aux_11` (the file's `calc_aux` section), with only the summability
hypothesis `hcsum` and the polynomial-growth hypothesis `hpoly` threaded in
where genuinely needed (via `include … in`). The dependency graph is shallow:
the longest project-lemma chain below the theorem is `step_9 → aux_10 → aux_9 →
aux_ring` (depth 4); `step_12` also fans out through `step_12a →
natplus_summable_of_nat_summable`.

## Why it is good

1. *(check)* The proof is a single `calc` whose 13 links each cite exactly one
   private step lemma, with no other proof text
   ([lines 457-487](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean#L457-L487)).
2. *(check)* Every lemma the theorem depends on in its own file (`step_1…step_13`,
   `aux_1…aux_11`, `aux_ring`, `aux_misc`, `step_12a`,
   `natplus_summable_of_nat_summable`, `hpoly'`) is closed without `sorry`; the
   file's only `sorry`s are at lines 631 and 633, in the downstream corollary
   `norm_φ₀_le` that *uses* this theorem rather than feeding it.
3. *(measurement)* The glue is 29 lines (459-487) assembling 13 direct lemmas; the
   8 shown children have proof bodies of 1, 4, 8, 6, 29, 27, 29 and 1 lines, so the
   three estimate-heavy steps (step_10, step_11, step_12) carry 85 of the 105 shown
   proof lines.
4. *(author-statement)* The blueprint states this as `lemma:mod-div-disc-bound`
   with `\lean{MagicFunction.PolyFourierCoeffBound.DivDiscBoundOfPolyFourierCoeff}`
   marked `\leanok`, and gives a 5-line `=, ≤, ≤, ≤, =` chain that the Lean `calc`
   expands into 13 steps ([construct-a-b.tex L96 and L112-127](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/blueprint/src/subsections/construct-a-b.tex#L96));
   the in-proof comment at [line 330](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean#L330)
   marks the polynomial-growth step.

In my opinion the detail worth copying is the discipline of *one private lemma
per link* even for the five purely algebraic re-arrangements (step_2…step_6): it
keeps the main proof a pure skeleton and lets each algebraic identity be checked
in isolation, at the cost of thirteen one-use lemmas.

## When to use it, and when not

Use a one-lemma-per-link `calc` when the goal is a bound (or equality) that
factors into independent pieces — a leading exponential, a sum of norms, an
infinite product — so that each factor can be bounded by its own small lemma, and
the informal proof is already a displayed `= ≤ = ≤ =` chain. The pattern shines
when the links are real estimates (inequalities) rather than bookkeeping, and when
transitivity should be checked by the chain itself rather than by hand.

Avoid it when a link needs too much local context to state as a standalone lemma
(keep it inline as a `have`); when the chain is short enough that one `calc` with
`rw`/`gcongr` inline is clearer than many one-use lemmas; or when the children are
pure rewrites with no independent interest — as here step_2…step_6 arguably are,
which the authors' own file-header to-do list names as boilerplate to be replaced by
library lemmas (`tprod_le_tprod`, `summable_real_norm_mul_geometric_of_norm_lt_one`).

## Consequences

The move creates thirteen private lemmas, one per link, stated before the theorem
and referenced by name; `calc` checks transitivity itself, so each child's only
obligation is that its two endpoints definitionally match the adjacent links. It
also creates the side obligations the children would otherwise hide: summability
(`hcsum`, threaded into step_8, step_9 and step_11 via `include`) and the
`Multipliable` side conditions of `tprod_le_of_nonneg_of_multipliable` (established
inside step_10 and step_12). Failure modes: a child whose statement drifts from
the chain's endpoints will not elaborate; a one-use child that cannot be stated
cleanly is boilerplate; and dropping a needed hypothesis (e.g. `hcsum`) fails the
whole chain, not just one link.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml: 'Build the project' step runs leanprover/lean-action (lake build) on every push to main, building all SpherePacking modules including SpherePacking/MagicFunction/PolyFourierCoeffBound.lean; pinned commit efe3bbbc1ece548f4672a772b94d8f621c10fdda is on the default branch main | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 5 file(s) byte-identical at efe3bbbc1ece548f4672a772b94d8f621c10fdda | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read copied PolyFourierCoeffBound.lean lines 457-487: DivDiscBoundOfPolyFourierCoeff is a single calc with 13 links (lines 459-487), each link citing exactly one private step lemma (step_1 through step_13), and no other proof text in the calc body. | verifier |
| 2 | verified | grep sorry over copied PolyFourierCoeffBound.lean: only two sorry tactic tokens, at lines 631 and 633 inside the downstream corollary norm_phi0_le which uses (not feeds) the theorem; lines 31 and 33 mention sorry only inside a doc-comment. step_1..step_13, aux_1..aux_11, aux_ring, aux_misc, step_12a, natplus_summable_of_nat_summable, hpoly' all close without sorry. | verifier |
| 3 | verified | Counted proof-body lines in the copied file: glue = lines 459-487 = 29 lines. Shown children proof bodies: step_1 L197=1, step_7 L252-255=4, step_8 L263-270=8, step_9 L278-283=6, step_10 L290-318=29, step_11 L326-352=27, step_12 L412-440=29, step_13 L446=1; matches [1,4,8,6,29,27,29,1]; 29+27+29=85 of total 105. | verifier |
| 4 | verified | Read copied code/blueprint/src/subsections/construct-a-b.tex: L96 = \begin{lemma}\label{lemma:mod-div-disc-bound}\lean{MagicFunction.PolyFourierCoeffBound.DivDiscBoundOfPolyFourierCoeff}\leanok (exact); the proof's align env spans L115-119 = 5 display lines; file L330 comment is exactly 'This is where we use the fact that c is eventually polynomial in n.'. Minor note: the relation sequence is =,=,≤,≤,= (two equalities then two inequalities), not the claim's '=,≤,≤,≤,='; all locators and the 5-line count are correct. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Read the copied file code/SpherePacking/MagicFunction/PolyFourierCoeffBound.lean and the blueprint tex. Parent DivDiscBoundOfPolyFourierCoeff (L457-487) is a single calc with 13 links, each '_ = ... := step_N ...' or '_ ≤ ... := step_N ...', no other proof text; matches claim 1 and the README. The 13 children step_1..step_13 are exactly the lemmas the calc cites (no aux_* appears directly in the calc body), and each child's statement LHS/RHS matches the adjacent links so the chain closes on (DivDiscBound c n₀) * rexp (...). Closing tactics in entry.json match the code (e.g. step_1 'simp [DiscriminantProductFormula, hf, fouterm]', step_13 'rw [DivDiscBound, mul_div_assoc, mul_comm]'; step_2/step_8/step_9/step_10/step_11/step_12 are faithful paraphrases of the code). Only 'sorry' tokens are at L631 and L633, in the downstream corollary norm_φ₀_le that calls (not feeds) the theorem, so the theorem's own dependency cone (step_*, aux_1..aux_11, aux_ring, aux_misc, step_12a, natplus_summable_of_nat_summable, hpoly') is sorry-free. Shape numbers correct: direct_lemmas=13, glue_lines=29 (L459-487), child_lines=[1,4,8,6,29,27,29,1] match proof-body line counts of step_1,7,8,9,10,11,12,13, and depth=4 matches the longest chain step_9→aux_10→aux_9→aux_ring. Trivial non-blocking wording note: the blueprint align is '=,=,≤,≤,=' over 5 lines (L115-119), described in claim 4 as '=,≤,≤,='; does not affect the decomposition. | reviewer-correctness |
| generality | accept | Generality holds. (1) Move stated beyond the example: applicability.goal_shape + use_when/avoid_when abstract it to any monotone =/<= chain of a bound that factors into independent pieces, each bounded by one lemma with definitionally-matching endpoints; use_when even keys on the informal proof already being a displayed = <= = <= = chain. (2) 'when not to use' and consequences are honest and specific: avoid_when flags pure-rewrite children as boilerplate (admitting step_2..step_6 'arguably are'), consequences name concrete failure modes (endpoint drift fails elaboration; missing hcsum fails the whole chain; one-use children needing many section vars are boilerplate). (3) Good-leaf rationale present: README 'Why each is a good leaf' says self-contained statements closing by a single simp/field_simp/rw or named siblings aux_1..aux_11, shallow dependency depth (step_9 -> aux_10 -> aux_9 -> aux_ring, verified in code), and hypotheses threaded only where needed via include (hcsum/hpoly, confirmed by grep). Minor imprecision, not an objection: the avoid_when sentence attributes the authors' TODO-list 'boilerplate' naming to step_2..step_6, but the file header (lines 30-38) actually names step_10/step_11/step_12/aux_5 as needing library lemmas (tprod_le_tprod, summable_real_norm_mul_geometric_of_norm_lt_one); the substance (estimate-heavy vs pure-rewrite steps) is still correctly separated elsewhere. | reviewer-generality |
| provenance-licence | accept | check_provenance.py passes: 5 files byte-identical at commit efe3bbbc1ece548f4672a772b94d8f621c10fdda and recorded sha256 hashes match. entry.json source.url/commit/licence (thefundamentaltheor3m/Sphere-Packing-Lean, efe3bbbc..., Apache-2.0) match sources/sphere-packing/source.json and SOURCE.md exactly; upstream-LICENSE is Apache License 2.0 text. All permalinks (files and sites) use the pinned commit with correct repo and paths matching the copied code files. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean at commit `efe3bbbc1ece548f4672a772b94d8f621c10fdda`, under `Apache-2.0`; see the [source note](../../sources/sphere-packing/SOURCE.md) for the licence text and attribution.
