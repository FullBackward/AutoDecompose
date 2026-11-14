# Weighted-average key invariant closes Putnam 2025 B2 (centroid x₁ < x₂)

| | |
|---|---|
| Kind | instance |
| Move | key-invariant |
| Language | lean |
| Status | accepted |
| Source | [numina-putnam2025](../../sources/numina-putnam2025/SOURCE.md) at `60d33c8ba19a` |
| Licence | `MIT` |
| Licence recorded | 2026-11-14T09:42:16Z |

## Intent

Prove Putnam 2025 B2 — the centroid `x₁` of the region under a strictly
increasing, non-negative, continuous curve `f` on `[0,1]` lies to the left of
the centroid `x₂` of its solid of revolution — by carrying the whole proof on
one auxiliary inequality, `weighted_average_lt_of_strictMono`: the `f`-weighted
average of `x` is strictly less than the `f²`-weighted average. Two positivity
lemmas discharge the centroid formulas' hypotheses, the two centroid lemmas
identify `x₁` and `x₂` with the two sides of that inequality, and one rewrite
followed by `exact` closes.

## The decomposition

### parent `putnam_2025_b2`: [`NuminaPutnam2025/putnam_2025_b2.lean` lines 1044-1078](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_b2.lean#L1044-L1078) ([local copy](code/NuminaPutnam2025/putnam_2025_b2.lean))

```lean
theorem putnam_2025_b2 (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (hfm : StrictMono f)
  (hfc : Continuous f):
  let R : Set (ℝ × ℝ) := { x | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 }
  let x₁ : ℝ := ⨍ x in R, x.1
  let R' : Set (ℝ × ℝ × ℝ) := { x' | ∃ x ∈ R, ∃ θ : ℝ, x'.1 = x.1 ∧ x'.2.1 = x.2 * cos θ ∧ x'.2.2 = x.2 * sin θ }
  let x₂ : ℝ := ⨍ x' in R', x'.1
  x₁ < x₂ := by
  intro R x₁ R' x₂

  -- Positivity of integrals
  have hI1_pos : 0 < ∫ x in (0:ℝ)..1, f x := integral_f_pos f hf hfm hfc
  have hI2_pos : 0 < ∫ x in (0:ℝ)..1, f x ^ 2 := integral_f_sq_pos f hf hfm hfc

  -- The key mathematical insight (proved in weighted_average_lt_of_strictMono):
  -- For strictly increasing f ≥ 0 on [0,1]:
  --   (∫x·f)/(∫f) < (∫x·f²)/(∫f²)
  have hkey := weighted_average_lt_of_strictMono f hf hfm hfc

  -- The centroid x-coordinate of the 2D region R equals (∫x·f)/(∫f)
  -- This follows from the centroid_2d_formula lemma
  have hx1_eq : x₁ = (∫ x in (0:ℝ)..1, x * f x) / (∫ x in (0:ℝ)..1, f x) := by
    simp only [x₁, R]
    exact centroid_2d_formula f hf hfc hI1_pos

  -- The centroid x-coordinate of the 3D solid R' equals (∫x·f²)/(∫f²)
  -- This follows from the centroid_3d_formula lemma
  have hx2_eq : x₂ = (∫ x in (0:ℝ)..1, x * f x ^ 2) / (∫ x in (0:ℝ)..1, f x ^ 2) := by
    simp only [x₂, R', R]
    exact centroid_3d_formula f hf hfc hI2_pos

  -- Apply the key inequality
  rw [hx1_eq, hx2_eq]
  exact hkey
```

### child `integral_f_pos`: [`NuminaPutnam2025/putnam_2025_b2.lean` lines 24-39](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_b2.lean#L24-L39) ([local copy](code/NuminaPutnam2025/putnam_2025_b2.lean))

```lean
lemma integral_f_pos (f : ℝ → ℝ)
    (hf : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ f x)
    (hfm : StrictMono f)
    (hfc : Continuous f) :
    0 < ∫ x in (0:ℝ)..1, f x := by
  have h1 : f 1 > f 0 := hfm (by norm_num : (0:ℝ) < 1)
  have h2 : f 0 ≥ 0 := hf 0 (by simp)
  have h3 : f 1 > 0 := lt_of_le_of_lt h2 h1
  have h4 : ∀ x ∈ Ioo (0:ℝ) 1, f x > 0 := fun x hx => by
    have : f x > f 0 := hfm hx.1
    linarith
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact hfc.intervalIntegrable 0 1
  · intro x hx
    exact h4 x hx
  · norm_num
```

### child `integral_f_sq_pos`: [`NuminaPutnam2025/putnam_2025_b2.lean` lines 41-56](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_b2.lean#L41-L56) ([local copy](code/NuminaPutnam2025/putnam_2025_b2.lean))

```lean
lemma integral_f_sq_pos (f : ℝ → ℝ)
    (hf : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ f x)
    (hfm : StrictMono f)
    (hfc : Continuous f) :
    0 < ∫ x in (0:ℝ)..1, f x ^ 2 := by
  have h1 : f 1 > f 0 := hfm (by norm_num : (0:ℝ) < 1)
  have h2 : f 0 ≥ 0 := hf 0 (by simp)
  have h3 : f 1 > 0 := lt_of_le_of_lt h2 h1
  have h4 : ∀ x ∈ Ioo (0:ℝ) 1, f x > 0 := fun x hx => by
    have : f x > f 0 := hfm hx.1
    linarith
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact (hfc.pow 2).intervalIntegrable 0 1
  · intro x hx
    exact sq_pos_of_pos (h4 x hx)
  · norm_num
```

### child `weighted_average_lt_of_strictMono`: [`NuminaPutnam2025/putnam_2025_b2.lean` lines 431-441](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_b2.lean#L431-L441) ([local copy](code/NuminaPutnam2025/putnam_2025_b2.lean))

```lean
lemma weighted_average_lt_of_strictMono (f : ℝ → ℝ)
    (hf : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ f x)
    (hfm : StrictMono f)
    (hfc : Continuous f) :
    (∫ x in (0:ℝ)..1, x * f x) / (∫ x in (0:ℝ)..1, f x) <
    (∫ x in (0:ℝ)..1, x * f x ^ 2) / (∫ x in (0:ℝ)..1, f x ^ 2) := by
  have hI1_pos : 0 < ∫ x in (0:ℝ)..1, f x := integral_f_pos f hf hfm hfc
  have hIf2_pos : 0 < ∫ x in (0:ℝ)..1, f x ^ 2 := integral_f_sq_pos f hf hfm hfc
  have hkey := key_product_ineq f hf hfm hfc
  rw [div_lt_div_iff₀ hI1_pos hIf2_pos]
  linarith
```

### child `centroid_2d_formula`: [`NuminaPutnam2025/putnam_2025_b2.lean` lines 549-691](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_b2.lean#L549-L691) ([local copy](code/NuminaPutnam2025/putnam_2025_b2.lean))

```lean
lemma centroid_2d_formula (f : ℝ → ℝ) (hf : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ f x) (hfc : Continuous f)
    (hI_pos : 0 < ∫ x in (0:ℝ)..1, f x) :
    let R : Set (ℝ × ℝ) := { p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ f p.1 }
    ⨍ p in R, p.1 ∂(volume.prod volume) = (∫ x in (0:ℝ)..1, x * f x) / (∫ x in (0:ℝ)..1, f x) := by
  intro R
  -- The proof uses the definition of setAverage and Fubini's theorem.
  -- We need to show:
  -- 1. (volume.prod volume) R = ENNReal.ofReal (∫ x in (0:ℝ)..1, f x)
  -- 2. ∫ p in R, p.1 ∂(volume.prod volume) = ∫ x in (0:ℝ)..1, x * f x
  -- Then the result follows from the definition of setAverage.

  -- Define the region between 0 and f over [0,1]
  let R' := regionBetween (fun _ => 0) f (Icc (0:ℝ) 1)

  -- R and R' differ only on a null set (boundary)
  -- R' = {(x,y) : x ∈ [0,1], 0 < y < f(x)}
  -- R  = {(x,y) : x ∈ [0,1], 0 ≤ y ≤ f(x)}

  -- Key facts about measures
  have h_f_int : IntegrableOn f (Icc (0:ℝ) 1) volume := hfc.integrableOn_Icc
  have h_zero_int : IntegrableOn (fun _ => (0:ℝ)) (Icc (0:ℝ) 1) volume := by
    apply integrableOn_const
    · simp only [Real.volume_Icc, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true]
    · simp only [enorm_zero]; exact ENNReal.zero_ne_top

  -- The measure of the region R' equals ∫f(x)dx
  have h_vol_R' : volume.prod volume R' = ENNReal.ofReal (∫ x in Icc (0:ℝ) 1, f x) := by
    have := volume_regionBetween_eq_integral h_zero_int h_f_int measurableSet_Icc
      (fun x hx => hf x hx)
    simp only [Pi.sub_apply, sub_zero] at this
    exact this

  -- Convert to interval integral
  have h_set_to_interval : ∫ x in Icc (0:ℝ) 1, f x = ∫ x in (0:ℝ)..1, f x := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]

  -- The average formula requires showing R and R' have the same measure up to null sets
  -- and the integrals are equal

  -- For now, we use the direct calculation approach
  -- The setAverage is defined as (μ.real s)⁻¹ • ∫ x in s, f x ∂μ

  -- Due to the complexity of showing R and R' are ae-equal and computing the
  -- integral of p.1 over R using Fubini, we defer to the standard calculus result.
  -- The mathematical content is straightforward:
  -- - measure(R) = ∫₀¹ f(x) dx (by Fubini, integrating 1 over the region)
  -- - ∫_R x dA = ∫₀¹ x·f(x) dx (by Fubini, integrating x over the region)

  -- For a complete formal proof, one would need to:
  -- 1. Show R is measurable (it is, as it's a region defined by continuous functions)
  -- 2. Show R =ᵐ R' (they differ only on the graph of f and the x-axis, both null sets)
  -- 3. Apply Fubini to compute ∫_R p.1 = ∫₀¹ ∫₀^{f(x)} x dy dx = ∫₀¹ x·f(x) dx

  -- Using setAverage_eq: ⨍ x in s, f x ∂μ = (μ.real s)⁻¹ • ∫ x in s, f x ∂μ
  rw [MeasureTheory.setAverage_eq]

  -- We need to show:
  -- (volume.prod volume).real R)⁻¹ • ∫ p in R, p.1 ∂(volume.prod volume)
  -- = (∫ x in (0:ℝ)..1, x * f x) / (∫ x in (0:ℝ)..1, f x)

  -- Key step 1: Show R and R' have the same measure (they differ by a null set)
  -- R' = regionBetween 0 f [0,1] uses open interval Ioo
  -- R uses closed bounds, but the boundary has measure zero

  -- Key step 2: Compute the measure and integral using Fubini
  -- measure(R) = ∫₀¹ f(x) dx
  -- ∫_R p.1 dA = ∫₀¹ x·f(x) dx

  -- The technical proof requires:
  -- 1. Showing the graph of f and the x-axis segment have measure zero in the product space
  -- 2. Using ae-equality to transfer the measure computation from R' to R
  -- 3. Using Fubini's theorem to compute ∫_R p.1 as an iterated integral

  -- For the measure: (volume.prod volume).real R = ∫₀¹ f(x) dx
  -- This is a standard calculus fact: the area under a non-negative continuous curve
  -- equals the integral of that curve.
  -- The proof requires showing that R and regionBetween differ by a null set, then
  -- using volume_regionBetween_eq_integral to get the measure, and converting to real.
  have h_measure_R : (volume.prod volume).real R = ∫ x in (0:ℝ)..1, f x := by
    -- R = {(x,y) : x ∈ [0,1], y ∈ [0, f(x)]}
    -- R' = regionBetween 0 f [0,1] = {(x,y) : x ∈ [0,1], y ∈ (0, f(x))}
    -- We show they have the same measure (differ by null set)
    -- Then use volume_regionBetween_eq_integral
    have h_R_eq_R' : volume.prod volume R = volume.prod volume R' := by
      have hR_eq : R = {p : ℝ × ℝ | p.1 ∈ Icc 0 1 ∧ p.2 ∈ Icc 0 (f p.1)} := by
        ext p
        simp only [R, mem_setOf_eq, mem_Icc]
        tauto
      have hR'_eq : R' = {p : ℝ × ℝ | p.1 ∈ Icc 0 1 ∧ p.2 ∈ Ioo 0 (f p.1)} := by
        ext p; simp only [R', regionBetween, mem_setOf_eq, mem_Ioo]
      apply measure_congr
      rw [Filter.eventuallyEq_set]
      rw [Measure.ae_prod_iff_ae_ae]
      · filter_upwards with x
        by_cases hx : x ∈ Icc (0:ℝ) 1
        · have h_ae := Filter.eventuallyEq_set.mp (Ioo_ae_eq_Icc (a := 0) (b := f x) (μ := volume))
          filter_upwards [h_ae] with y hy
          simp only [hR_eq, hR'_eq, mem_setOf_eq, hx, true_and, hy]
        · filter_upwards with y
          simp only [hR_eq, hR'_eq, mem_setOf_eq, hx, false_and]
      · have h1 : MeasurableSet R := by rw [hR_eq]; exact measurableSet_region_between_cc measurable_const hfc.measurable measurableSet_Icc
        have h2 : MeasurableSet R' := by rw [hR'_eq]; exact measurableSet_regionBetween measurable_const hfc.measurable measurableSet_Icc
        have heq : {x : ℝ × ℝ | x ∈ R ↔ x ∈ R'} = (R ∩ R') ∪ (Rᶜ ∩ R'ᶜ) := by
          ext x
          simp only [mem_setOf_eq, mem_union, mem_inter_iff, mem_compl_iff]
          tauto
        rw [heq]
        exact (h1.inter h2).union (h1.compl.inter h2.compl)
    rw [Measure.real_def, h_R_eq_R', h_vol_R', h_set_to_interval, ENNReal.toReal_ofReal (le_of_lt hI_pos)]

  -- For the integral: ∫_R p.1 = ∫₀¹ x·f(x) dx by Fubini
  have h_integral_R : ∫ p in R, p.1 ∂(volume.prod volume) = ∫ x in (0:ℝ)..1, x * f x := by
    -- First show R =ᵐ R' (same as in measure proof)
    have hR_eq : R = {p : ℝ × ℝ | p.1 ∈ Icc 0 1 ∧ p.2 ∈ Icc 0 (f p.1)} := by
      ext p; simp only [R, mem_setOf_eq, mem_Icc]; tauto
    have hR'_eq : R' = {p : ℝ × ℝ | p.1 ∈ Icc 0 1 ∧ p.2 ∈ Ioo 0 (f p.1)} := by
      ext p; simp only [R', regionBetween, mem_setOf_eq, mem_Ioo]
    have h_ae_eq : R =ᵐ[volume.prod volume] R' := by
      rw [Filter.eventuallyEq_set, Measure.ae_prod_iff_ae_ae]
      · filter_upwards with x
        by_cases hx : x ∈ Icc (0:ℝ) 1
        · have h_ae := Filter.eventuallyEq_set.mp (Ioo_ae_eq_Icc (a := 0) (b := f x) (μ := volume))
          filter_upwards [h_ae] with y hy
          simp only [hR_eq, hR'_eq, mem_setOf_eq, hx, true_and, hy]
        · filter_upwards with y
          simp only [hR_eq, hR'_eq, mem_setOf_eq, hx, false_and]
      · have h1 : MeasurableSet R := by rw [hR_eq]; exact measurableSet_region_between_cc measurable_const hfc.measurable measurableSet_Icc
        have h2 : MeasurableSet R' := by rw [hR'_eq]; exact measurableSet_regionBetween measurable_const hfc.measurable measurableSet_Icc
        have heq : {x : ℝ × ℝ | x ∈ R ↔ x ∈ R'} = (R ∩ R') ∪ (Rᶜ ∩ R'ᶜ) := by
          ext x; simp only [mem_setOf_eq, mem_union, mem_inter_iff, mem_compl_iff]; tauto
        rw [heq]
        exact (h1.inter h2).union (h1.compl.inter h2.compl)
    rw [setIntegral_congr_set h_ae_eq]
    -- Now compute ∫ p in R', p.1 using Fubini
    -- By Fubini's theorem: ∫_R' p.1 dA = ∫₀¹ (∫₀^{f(x)} x dy) dx = ∫₀¹ x·f(x) dx
    -- The inner integral evaluates to x · (f(x) - 0) = x · f(x)
    exact setIntegral_fst_regionBetween f hf hfc

  -- Combine to get the result
  rw [h_measure_R, h_integral_R]
  -- Goal: (∫ x in 0..1, f x)⁻¹ • (∫ x in 0..1, x * f x) = (∫ x in 0..1, x * f x) / (∫ x in 0..1, f x)
  rw [smul_eq_mul, inv_mul_eq_div]
```

### child `centroid_3d_formula`: [`NuminaPutnam2025/putnam_2025_b2.lean` lines 702-1042](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_b2.lean#L702-L1042) ([local copy](code/NuminaPutnam2025/putnam_2025_b2.lean))

```lean
lemma centroid_3d_formula (f : ℝ → ℝ) (hf : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ f x) (hfc : Continuous f)
    (hI_pos : 0 < ∫ x in (0:ℝ)..1, f x ^ 2) :
    let R : Set (ℝ × ℝ) := { p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ f p.1 }
    let R' : Set (ℝ × ℝ × ℝ) := { p' | ∃ p ∈ R, ∃ θ : ℝ, p'.1 = p.1 ∧ p'.2.1 = p.2 * cos θ ∧ p'.2.2 = p.2 * sin θ }
    ⨍ p' in R', p'.1 ∂volume = (∫ x in (0:ℝ)..1, x * f x ^ 2) / (∫ x in (0:ℝ)..1, f x ^ 2) := by
  intro R R'
  -- R' is the solid of revolution obtained by rotating R about the x-axis.
  -- In cylindrical coordinates (x, r, θ), R' corresponds to:
  --   { (x, r, θ) | x ∈ [0,1], 0 ≤ r ≤ f(x), θ ∈ [0, 2π) }
  -- The Jacobian of the transformation (x, r, θ) → (x, r cos θ, r sin θ) is r.
  --
  -- Key computations:
  -- 1. volume(R') = ∫₀¹ ∫₀^{f(x)} ∫₀^{2π} r dθ dr dx
  --              = ∫₀¹ ∫₀^{f(x)} 2πr dr dx = ∫₀¹ π·f(x)² dx = π · ∫₀¹ f(x)² dx
  --
  -- 2. ∫_{R'} x dV = ∫₀¹ ∫₀^{f(x)} ∫₀^{2π} x·r dθ dr dx
  --               = ∫₀¹ x · π·f(x)² dx = π · ∫₀¹ x·f(x)² dx
  --
  -- 3. ⨍ p' in R', p'.1 = (∫_{R'} x dV) / volume(R')
  --                     = (π · ∫₀¹ x·f(x)² dx) / (π · ∫₀¹ f(x)² dx)
  --                     = (∫₀¹ x·f(x)² dx) / (∫₀¹ f(x)² dx)
  --
  -- The formal proof uses change of variables to cylindrical coordinates.
  -- The key is that the π factors cancel in the ratio.
  --
  -- We use setAverage_eq to express the average as integral / measure.
  rw [MeasureTheory.setAverage_eq]

  -- We need to show:
  -- (volume.real R')⁻¹ • ∫ p' in R', p'.1 ∂volume = (∫ x in 0..1, x * f x ^ 2) / (∫ x in 0..1, f x ^ 2)
  --
  -- This requires showing:
  -- 1. volume.real R' = π · ∫ x in 0..1, f x ^ 2
  -- 2. ∫ p' in R', p'.1 ∂volume = π · ∫ x in 0..1, x * f x ^ 2
  -- Then (volume.real R')⁻¹ • ∫ p' in R', p'.1 = (∫ x·f²) / (∫ f²) since π cancels

  -- For now, we establish the measure and integral using the cylindrical coordinate formula.
  -- The formal derivation requires change of variables, which is complex in Lean.
  -- We proceed by stating the key equalities and deriving the result.

  -- Volume of R' = π · ∫₀¹ f(x)² dx (disk method for solid of revolution)
  -- Mathematical derivation:
  -- R' ≃ { (x, y, z) | x ∈ [0,1], y² + z² ≤ f(x)² } (solid with circular cross-sections)
  -- By Fubini: volume(R') = ∫₀¹ (area of disk at x) dx = ∫₀¹ π·f(x)² dx = π · ∫₀¹ f(x)² dx
  --
  -- The formal proof would require:
  -- 1. Show R' equals the Cartesian form {(x,y,z) | x ∈ [0,1], y²+z² ≤ f(x)²}
  -- 2. Apply Fubini to express volume as ∫_x (∫_{y²+z² ≤ f(x)²} 1) dx
  -- 3. Use Complex.volume_closedBall (or equivalent for ℝ²) to get area = π·f(x)²
  -- 4. Evaluate the outer integral
  --
  -- This requires significant measure-theoretic machinery for relating ℝ² and ℂ measures
  -- and computing volumes of 2D disks via Fubini in the product space ℝ × ℝ × ℝ.
  -- First, let's show that R' equals the Cartesian form
  -- R' = {(x, y, z) | x ∈ [0,1], y² + z² ≤ f(x)²}
  -- This is because rotating (x, r) by angle θ gives (x, r·cos θ, r·sin θ)
  -- and as θ ranges over all reals and r over [0, f(x)], we cover the disk.

  -- Define the Cartesian form of the solid
  let R'_cart : Set (ℝ × ℝ × ℝ) := {p | p.1 ∈ Icc 0 1 ∧ p.2.1 ^ 2 + p.2.2 ^ 2 ≤ (f p.1) ^ 2}

  -- Key lemma: R' = R'_cart
  -- This is a standard result: rotating (x, r) by all angles θ covers the disk of radius r
  -- The forward direction uses cos^2 + sin^2 = 1
  -- The backward direction uses the complex argument function to find θ
  have hR'_eq : R' = R'_cart := by
    ext p
    simp only [R', R'_cart, mem_setOf_eq, mem_Icc]
    constructor
    · -- R' → R'_cart
      rintro ⟨q, hqR, θ, hx, hy, hz⟩
      simp only [R, mem_setOf_eq] at hqR
      constructor
      · constructor
        · rw [hx]; exact hqR.1
        · rw [hx]; exact hqR.2.1
      · rw [hy, hz, hx]
        have hq2_nn : 0 ≤ q.2 := hqR.2.2.1
        have hq2_le : q.2 ≤ f q.1 := hqR.2.2.2
        calc (q.2 * cos θ) ^ 2 + (q.2 * sin θ) ^ 2
            = q.2 ^ 2 * (cos θ ^ 2 + sin θ ^ 2) := by ring
          _ = q.2 ^ 2 * 1 := by rw [cos_sq_add_sin_sq]
          _ = q.2 ^ 2 := by ring
          _ ≤ (f q.1) ^ 2 := by
              apply sq_le_sq' _ hq2_le
              linarith [hf q.1 (And.intro hqR.1 hqR.2.1)]
    · -- R'_cart → R': given (x, y, z) with y² + z² ≤ f(x)², find (x, r) and θ
      intro ⟨hx, hdisk⟩
      let r := Real.sqrt (p.2.1 ^ 2 + p.2.2 ^ 2)
      have hr_nn : 0 ≤ r := Real.sqrt_nonneg _
      have hr_le : r ≤ f p.1 := by
        rw [← Real.sqrt_sq (hf p.1 hx)]
        exact Real.sqrt_le_sqrt hdisk
      use (p.1, r)
      constructor
      · simp only [R, mem_setOf_eq]
        exact ⟨hx.1, hx.2, hr_nn, hr_le⟩
      · -- Use complex argument to find the angle
        let z : ℂ := ⟨p.2.1, p.2.2⟩
        use Complex.arg z
        -- ‖z‖ = r since ‖z‖ = √(re² + im²) = √(p.2.1² + p.2.2²) = r
        have h_norm : ‖z‖ = r := by
          simp only [z, Complex.norm_def, Complex.normSq_mk]
          -- normSq_mk gives us x*x + y*y, need to convert to x^2 + y^2
          congr 1
          ring
        refine ⟨rfl, ?_, ?_⟩
        · -- p.2.1 = r * cos (arg z)
          -- Use Complex.norm_mul_cos_arg: ‖z‖ * cos(arg z) = z.re = p.2.1
          have := Complex.norm_mul_cos_arg z
          simp only [z] at this
          rw [h_norm] at this
          linarith
        · -- p.2.2 = r * sin (arg z)
          -- Use Complex.norm_mul_sin_arg: ‖z‖ * sin(arg z) = z.im = p.2.2
          have := Complex.norm_mul_sin_arg z
          simp only [z] at this
          rw [h_norm] at this
          linarith

  -- Helper lemmas for disk volume
  have complex_closedBall_iff : ∀ z : ℂ, ∀ r : ℝ, 0 ≤ r →
      (z ∈ Metric.closedBall (0 : ℂ) r ↔ z.re ^ 2 + z.im ^ 2 ≤ r ^ 2) := by
    intros z r hr
    rw [Metric.mem_closedBall, _root_.dist_zero_right]
    constructor
    · intro h
      have h1 : ‖z‖ ^ 2 ≤ r ^ 2 := sq_le_sq' (by linarith [norm_nonneg z]) h
      rw [← Complex.normSq_eq_norm_sq] at h1
      have : Complex.normSq z = z.re ^ 2 + z.im ^ 2 := by simp [Complex.normSq, sq]
      linarith
    · intro h
      have h2 : ‖z‖ ^ 2 ≤ r ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq]
        have : Complex.normSq z = z.re ^ 2 + z.im ^ 2 := by simp [Complex.normSq, sq]
        linarith
      have h3 : ‖z‖ ≤ r := by
        have hn := norm_nonneg z
        nlinarith [sq_nonneg ‖z‖, sq_nonneg r]
      exact h3

  have disk_eq_image : ∀ r : ℝ, 0 ≤ r →
      {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ r ^ 2} =
      Complex.measurableEquivRealProd '' (Metric.closedBall (0 : ℂ) r) := by
    intros r hr
    ext p
    simp only [mem_setOf_eq, mem_image]
    constructor
    · intro hp
      use ⟨p.1, p.2⟩
      constructor
      · exact (complex_closedBall_iff _ r hr).mpr hp
      · simp [Complex.measurableEquivRealProd_apply]
    · rintro ⟨z, hz, rfl⟩
      simp only [Complex.measurableEquivRealProd_apply]
      exact (complex_closedBall_iff z r hr).mp hz

  have ofReal_pow_mul_pi : ∀ r : ℝ, 0 ≤ r →
      ENNReal.ofReal r ^ 2 * ↑NNReal.pi = ENNReal.ofReal (Real.pi * r ^ 2) := by
    intros r hr
    have h1 : ENNReal.ofReal r ^ 2 = ENNReal.ofReal (r ^ 2) := by
      rw [← ENNReal.ofReal_pow hr]
    rw [h1]
    have h2 : (NNReal.pi : ENNReal) = ENNReal.ofReal Real.pi := by
      rw [← NNReal.coe_real_pi]
      exact ENNReal.coe_nnreal_eq NNReal.pi
    rw [h2]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ r ^ 2)]
    congr 1; ring

  have disk_volume : ∀ r : ℝ, 0 ≤ r →
      volume ({p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ r ^ 2}) = ENNReal.ofReal (Real.pi * r ^ 2) := by
    intros r hr
    rw [disk_eq_image r hr]
    have hmp := Complex.volume_preserving_equiv_real_prod
    rw [← hmp.measure_preimage_emb Complex.measurableEquivRealProd.measurableEmbedding]
    simp only [MeasurableEquiv.preimage_image]
    rw [Complex.volume_closedBall 0 r]
    exact ofReal_pow_mul_pi r hr

  have slice_preimage : ∀ x : ℝ, Prod.mk x ⁻¹' R'_cart =
      if x ∈ Icc (0:ℝ) 1 then {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ (f x) ^ 2} else ∅ := by
    intro x
    ext p
    simp only [R'_cart, mem_preimage, mem_setOf_eq, mem_Icc]
    split_ifs with hx
    · simp only [mem_setOf_eq, hx, true_and]
    · simp only [mem_empty_iff_false, iff_false, not_and]
      intro h; exact (hx h).elim

  have slice_measure : ∀ x : ℝ, volume (Prod.mk x ⁻¹' R'_cart) =
      (Icc (0:ℝ) 1).indicator (fun x => ENNReal.ofReal (Real.pi * (f x) ^ 2)) x := by
    intro x
    rw [slice_preimage]
    split_ifs with hx
    · simp only [indicator_of_mem hx]
      exact disk_volume (f x) (hf x hx)
    · simp only [measure_empty, indicator_of_notMem hx]

  have R'_cart_measurable : MeasurableSet R'_cart := by
    have h1 : MeasurableSet {p : ℝ × ℝ × ℝ | p.1 ∈ Icc (0:ℝ) 1} :=
      measurable_fst measurableSet_Icc
    have h2 : MeasurableSet {p : ℝ × ℝ × ℝ | p.2.1 ^ 2 + p.2.2 ^ 2 ≤ (f p.1) ^ 2} := by
      apply measurableSet_le
      · apply Measurable.add
        · exact ((measurable_fst.comp measurable_snd).pow_const 2)
        · exact ((measurable_snd.comp measurable_snd).pow_const 2)
      · exact ((hfc.comp continuous_fst).measurable.pow_const 2)
    exact h1.inter h2

  have h_vol : volume.real R' = Real.pi * ∫ x in (0:ℝ)..1, f x ^ 2 := by
    rw [hR'_eq]
    -- Use volume = volume.prod volume on ℝ × (ℝ × ℝ)
    have hvol : (volume : Measure (ℝ × ℝ × ℝ)) =
        Measure.prod (volume : Measure ℝ) (volume : Measure (ℝ × ℝ)) :=
      Measure.volume_eq_prod ℝ (ℝ × ℝ)
    rw [Measure.real_def, hvol]
    rw [Measure.prod_apply R'_cart_measurable]
    simp_rw [slice_measure]
    rw [lintegral_indicator measurableSet_Icc]
    -- Convert lintegral to integral
    have hint : IntegrableOn (fun x => Real.pi * (f x) ^ 2) (Icc 0 1) := by
      apply Continuous.integrableOn_Icc
      exact continuous_const.mul (hfc.pow 2)
    have hnn : ∀ᵐ x ∂volume.restrict (Icc (0:ℝ) 1), 0 ≤ Real.pi * (f x) ^ 2 := by
      apply ae_of_all
      intro x
      exact mul_nonneg (le_of_lt Real.pi_pos) (sq_nonneg _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    rw [ENNReal.toReal_ofReal]
    · rw [integral_const_mul]
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
      rw [integral_Icc_eq_integral_Ioc]
    · apply setIntegral_nonneg measurableSet_Icc
      intro x _
      exact mul_nonneg (le_of_lt Real.pi_pos) (sq_nonneg _)

  -- First moment ∫_{R'} x dV = π · ∫₀¹ x·f(x)² dx
  -- By Fubini: ∫_{R'} x dV = ∫₀¹ x · (area of disk at x) dx = ∫₀¹ x · π·f(x)² dx = π · ∫₀¹ x·f(x)² dx
  have h_int : ∫ p' in R', p'.1 ∂volume = Real.pi * ∫ x in (0:ℝ)..1, x * f x ^ 2 := by
    rw [hR'_eq]
    -- Use integral_prod with indicator function approach
    -- ∫ p' in R'_cart, p'.1 = ∫ p', indicator_{R'_cart} (·.1) p'
    rw [← integral_indicator R'_cart_measurable]
    -- Apply Fubini
    have hvol : (volume : Measure (ℝ × ℝ × ℝ)) =
        Measure.prod (volume : Measure ℝ) (volume : Measure (ℝ × ℝ)) :=
      Measure.volume_eq_prod ℝ (ℝ × ℝ)
    -- Need integrability for Fubini
    have h_int_on : IntegrableOn (fun p' : ℝ × ℝ × ℝ => p'.1) R'_cart volume := by
      apply ContinuousOn.integrableOn_compact
      · -- R'_cart is compact: it's a closed bounded set
        -- First get the bound M on f
        have hfc_bdd := IsCompact.exists_bound_of_continuousOn (isCompact_Icc (a := (0:ℝ)) (b := 1)) hfc.continuousOn
        obtain ⟨M, hM⟩ := hfc_bdd
        have hM_pos : 0 ≤ M := by
          have := hM 0 (by simp : (0:ℝ) ∈ Icc 0 1)
          exact le_trans (abs_nonneg _) this
        apply IsCompact.of_isClosed_subset (isCompact_Icc.prod (isCompact_closedBall (0 : ℝ × ℝ) M))
        · apply IsClosed.inter
          · exact isClosed_Icc.preimage continuous_fst
          · have hcont1 : Continuous (fun p : ℝ × ℝ × ℝ => p.2.1 ^ 2 + p.2.2 ^ 2) :=
              ((continuous_fst.comp continuous_snd).pow 2).add
                ((continuous_snd.comp continuous_snd).pow 2)
            have hcont2 : Continuous (fun p : ℝ × ℝ × ℝ => (f p.1) ^ 2) :=
              (hfc.comp continuous_fst).pow 2
            exact isClosed_le hcont1 hcont2
        · intro p hp
          simp only [R'_cart, mem_setOf_eq] at hp
          simp only [mem_prod, mem_Icc, Metric.mem_closedBall]
          constructor
          · exact hp.1
          · -- Need to show (p.2.1, p.2.2) is in closedBall 0 M
            have hfp := hM p.1 hp.1
            have hf_nn := hf p.1 hp.1
            rw [Real.norm_of_nonneg hf_nn] at hfp
            -- For ℝ × ℝ, the norm is max |x| |y|, so dist p.2 0 = max |p.2.1| |p.2.2|
            rw [_root_.dist_zero_right, Prod.norm_def]
            -- Need max |p.2.1| |p.2.2| ≤ M
            -- We have p.2.1² + p.2.2² ≤ f(p.1)² ≤ M², so |p.2.1|, |p.2.2| ≤ f(p.1) ≤ M
            have h1 : p.2.1 ^ 2 ≤ (f p.1) ^ 2 := by
              have := hp.2; have hp2 := sq_nonneg p.2.2; linarith
            have h2 : p.2.2 ^ 2 ≤ (f p.1) ^ 2 := by
              have := hp.2; have hp1 := sq_nonneg p.2.1; linarith
            have h1' : |p.2.1| ≤ f p.1 := by
              rw [← sq_abs p.2.1] at h1
              have hab := abs_nonneg p.2.1
              nlinarith [sq_nonneg |p.2.1|, sq_nonneg (f p.1)]
            have h2' : |p.2.2| ≤ f p.1 := by
              rw [← sq_abs p.2.2] at h2
              have hab := abs_nonneg p.2.2
              nlinarith [sq_nonneg |p.2.2|, sq_nonneg (f p.1)]
            simp only [Real.norm_eq_abs]
            exact max_le (h1'.trans hfp) (h2'.trans hfp)
      · exact continuous_fst.continuousOn
    have h_integrable : Integrable (R'_cart.indicator (fun p' : ℝ × ℝ × ℝ => p'.1)) volume :=
      h_int_on.integrable_indicator R'_cart_measurable
    rw [hvol, integral_prod _ h_integrable]
    -- Inner integral: for fixed x, ∫ yz, indicator_{R'_cart}(·.1) (x, yz)
    -- = ∫ yz ∈ slice(x), x = x · volume(slice(x)) = x · π·f(x)² if x ∈ [0,1]
    have inner_integral : ∀ x, ∫ yz : ℝ × ℝ, R'_cart.indicator (fun p' : ℝ × ℝ × ℝ => p'.1) (x, yz) =
        (Icc (0:ℝ) 1).indicator (fun x => x * Real.pi * (f x) ^ 2) x := by
      intro x
      have h_ind_eq : ∀ yz : ℝ × ℝ, R'_cart.indicator (fun p' : ℝ × ℝ × ℝ => p'.1) (x, yz) =
          (Prod.mk x ⁻¹' R'_cart).indicator (fun _ => x) yz := by
        intro yz
        by_cases h : (x, yz) ∈ R'_cart
        · have hyz : yz ∈ Prod.mk x ⁻¹' R'_cart := h
          simp only [indicator_of_mem h, indicator_of_mem hyz]
        · have hyz : yz ∉ Prod.mk x ⁻¹' R'_cart := h
          simp only [indicator_of_notMem h, indicator_of_notMem hyz]
      simp_rw [h_ind_eq, slice_preimage]
      split_ifs with hx
      · simp only [indicator_of_mem hx]
        rw [integral_indicator]
        · rw [setIntegral_const]
          -- volume.real {p | p.1² + p.2² ≤ f(x)²} = π · f(x)²
          have hdisk := disk_volume (f x) (hf x hx)
          simp only [Measure.real_def]
          rw [hdisk, ENNReal.toReal_ofReal]
          · rw [smul_eq_mul]; ring
          · exact mul_nonneg (le_of_lt Real.pi_pos) (sq_nonneg _)
        · -- measurability of disk
          apply measurableSet_le
          · exact (measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)
          · exact measurable_const
      · simp only [indicator_of_notMem hx]
        simp only [indicator_empty, integral_zero]
    simp_rw [inner_integral]
    rw [integral_indicator measurableSet_Icc, setIntegral_congr_fun measurableSet_Icc
        (fun x hx => by ring : ∀ x ∈ Icc (0:ℝ) 1, x * Real.pi * (f x) ^ 2 = Real.pi * (x * (f x) ^ 2))]
    rw [integral_const_mul]
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    rw [integral_Icc_eq_integral_Ioc]

  rw [h_vol, h_int]
  rw [smul_eq_mul, inv_mul_eq_div]
  -- Goal: (π * ∫ f²)⁻¹ * (π * ∫ x·f²) = (∫ x·f²) / (∫ f²)
  have hpi_ne_zero : Real.pi ≠ 0 := Real.pi_ne_zero
  have hI_ne_zero : ∫ x in (0:ℝ)..1, f x ^ 2 ≠ 0 := ne_of_gt hI_pos
  field_simp
```

How the parts fit. The glue (parent `putnam_2025_b2`) is 35 lines of
bookkeeping that reduce the whole problem to one inequality. It first proves
the two denominators are positive (`integral_f_pos`, `integral_f_sq_pos`),
obtains the key inequality `hkey := weighted_average_lt_of_strictMono f hf hfm
hfc`, identifies `x₁` with `(∫ x·f)/(∫ f)` via `centroid_2d_formula` and `x₂`
with `(∫ x·f²)/(∫ f²)` via `centroid_3d_formula`, then closes with `rw
[hx1_eq, hx2_eq]` and `exact hkey`. The lemma graph, with the line where each
project lemma is cited:

```
putnam_2025_b2
├── integral_f_pos                  (line 1056; leaf)
├── integral_f_sq_pos               (line 1057; leaf)
├── weighted_average_lt_of_strictMono  (line 1062)   ← the key invariant
│   ├── integral_f_pos              (line 437)
│   ├── integral_f_sq_pos           (line 438)
│   └── key_product_ineq            (line 439)
│       ├── integral_f_pos          (line 165)
│       ├── integral_f_sq_pos       (line 166)
│       ├── symm_product_nonneg     (line 186)
│       └── symm_product_pos        (line 205)
├── centroid_2d_formula             (line 1068)
│   └── setIntegral_fst_regionBetween (line 686)
└── centroid_3d_formula             (line 1074)
```

Three of the five direct children are good leaves for a bounded prover, where
the criterion is bounded size — a leaf the prover can be expected to close in
one sitting. `integral_f_pos` (16 lines) and `integral_f_sq_pos` (16 lines) are
short, self-contained statements whose proofs close on the hypotheses alone via
one library theorem, `intervalIntegral.intervalIntegral_pos_of_pos_on`.
`weighted_average_lt_of_strictMono` (11 lines) is the key invariant: its own
proof closes from two siblings (`integral_f_pos`, `integral_f_sq_pos`) plus the
project lemma `key_product_ineq`, which does the hard double-integral work — so
the main theorem only has to match its two sides. The other two children are
not bounded leaves: `centroid_2d_formula` (143 lines) and `centroid_3d_formula`
(341 lines) are large identification lemmas, the bulk of the file. Each closes
by `MeasureTheory.setAverage_eq` plus a Fubini computation
(`setIntegral_fst_regionBetween` for the 2D region; the internal disk-volume
slice computation for the 3D solid), and each is self-contained given its
hypotheses — the parent discharges their `hI_pos` hypotheses with the two
positivity lemmas — but a bounded prover could not be expected to produce them
from the theorem statement alone.

## Why it is good

1. The parent site `putnam_2025_b2` is 35 lines long — the whole competition
   theorem is a short bookkeeping proof assembled from five named lemmas
   (`check`, [lines 1044-1078](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_b2.lean#L1044-L1078)).
2. The parent cites `weighted_average_lt_of_strictMono`, the one lemma that
   carries the mathematical idea (`check`,
   [lines 1044-1078](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_b2.lean#L1044-L1078)).
3. The copied file contains no `sorry`, `admit` or `axiom`, so every lemma in
   the decomposition closes (`check`,
   [whole file](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_b2.lean)).
4. The decomposition has 5 direct lemmas, a 35-line glue, and depth 3
   (`putnam_2025_b2` → `weighted_average_lt_of_strictMono` →
   `key_product_ineq` → `integral_f_pos`), so the idea is isolated in a lemma
   two levels below the theorem (`measurement`, line refs
   [1062](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_b2.lean#L1062),
   [439](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_b2.lean#L439),
   [165](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_b2.lean#L165)).
5. The authors themselves label the key invariant in the glue: "The key
   mathematical insight (proved in `weighted_average_lt_of_strictMono`)"
   (`author-statement`,
   [lines 1059-1061](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_b2.lean#L1059-L1061)).

In my opinion the reusable detail is the *shape* rather than the inequality
itself: the author found the one statement whose two sides the problem's two
quantities already were, proved it once (expensively, in `key_product_ineq`),
and left the main theorem as a five-line citation. That is the "one key
theorem" pattern of survey F rule 14.

## When to use it, and when not

Use it when the goal's two sides can both be identified, by formula lemmas,
with the two sides of one auxiliary inequality that carries the whole idea
(here the `f`- vs `f²`-weighted average of `x` for strictly increasing
`f ≥ 0`), the auxiliary statement is self-contained enough to prove once and
cite, and the formulas' side conditions are discharged by short positivity
lemmas. The exemplar pays a real price for this shape: the two identification
lemmas (`centroid_2d_formula`, 143 lines, and `centroid_3d_formula`, 341 lines)
each need their own Fubini / measure-theoretic proof and are most of the file.
That is the cost of reducing the whole theorem to a 35-line glue, paid once and
walled off behind the two formula lemmas rather than spread through the main
proof. Avoid it when the auxiliary inequality does not isolate the monotonicity
hypothesis that makes the strict comparison true (a merely non-decreasing
weight would collapse the comparison); or when the denominators' positivity
cannot be separated into short lemmas.

## Consequences

The move obliges the writer to (i) prove the key inequality once
(`weighted_average_lt_of_strictMono`, which itself rests on the heavy
`key_product_ineq` double-integral argument); (ii) prove the two centroid
formulas that identify the goal's quantities with the two sides of the
inequality (`centroid_2d_formula`, `centroid_3d_formula`); and (iii) discharge
the positivity hypotheses those formulas need (`integral_f_pos`,
`integral_f_sq_pos`). Failure mode: the strict inequality `x₁ < x₂` holds only
because the weight `f` is strictly increasing; a merely non-decreasing `f`
would collapse the comparison, and a differently shaped region or solid would
no longer reduce to the same four single integrals, so the two centroid
formulas would not meet the key inequality.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/lean_action_ci.yml runs leanprover/lean-action@v1 (lake build) on push/PR; default branch main; pinned commit 60d33c8ba19af905bd731e938ebde1c5b8c76519 is HEAD of main; NuminaPutnam2025.lean line 8 imports NuminaPutnam2025.putnam_2025_b2 so lake build compiles the entry's file | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: integral_f_pos@NuminaPutnam2025/putnam_2025_b2.lean:1056, integral_f_sq_pos@NuminaPutnam2025/putnam_2025_b2.lean:1057, weighted_average_lt_of_strictMono@NuminaPutnam2025/putnam_2025_b2.lean:1059, centroid_2d_formula@NuminaPutnam2025/putnam_2025_b2.lean:1065, centroid_3d_formula@NuminaPutnam2025/putnam_2025_b2.lean:1071; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 60d33c8ba19af905bd731e938ebde1c5b8c76519 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(putnam_2025_b2, 35) -> lines: site putnam_2025_b2 has 35 lines | check_claims.py |
| 2 | verified | cites(putnam_2025_b2, weighted_average_lt_of_strictMono) -> cites: weighted_average_lt_of_strictMono occurs at NuminaPutnam2025/putnam_2025_b2.lean:1059 | check_claims.py |
| 3 | verified | no_sorry(NuminaPutnam2025/putnam_2025_b2.lean, 1-1080) -> no_sorry: none of sorry, admit, axiom in NuminaPutnam2025/putnam_2025_b2.lean:1-1080 | check_claims.py |
| 4 | verified | Counted in the copied code: 5 direct lemmas exist (integral_f_pos L24, integral_f_sq_pos L41, weighted_average_lt_of_strictMono L431, centroid_2d_formula L549, centroid_3d_formula L702); parent site 1044-1078 is 35 lines; depth chain confirmed: putnam_2025_b2 cites weighted_average_lt_of_strictMono at L1062 (have hkey := ...), which cites key_product_ineq at L439, which cites integral_f_pos at L165 (have hI1_pos := integral_f_pos ...). | verifier |
| 5 | verified | Author comment at L1059 reads '-- The key mathematical insight (proved in weighted_average_lt_of_strictMono):' (L1059-L1061), matching the quoted text verbatim. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Decomposition faithful: parent putnam_2025_b2 (L1044-1078, 35 lines) cites exactly the 5 named children integral_f_pos (L1056), integral_f_sq_pos (L1057), weighted_average_lt_of_strictMono (L1062), centroid_2d_formula (L1068), centroid_3d_formula (L1074) and closes via rw [hx1_eq,hx2_eq]; exact hkey. Each child's statement and closed_by match the copied code (verified at L24-39, 41-56, 431-441, 549-691, 702-1042). Shape numbers correct: direct_lemmas=5, glue_lines=35, child_lines=[16,16,11,143,341] (24-39,41-56,431-441,549-691,702-1042), depth=3 (b2->weighted_average_lt_of_strictMono L439 -> key_product_ineq L165 cites integral_f_pos). | reviewer-correctness |
| generality | accept | Move is stated beyond the example: use_when/avoid_when and the 'In my opinion' paragraph reduce it to a reusable shape (one auxiliary inequality whose two sides are the goal's two quantities, proved once and cited in a short glue), with avoid_when naming two specific honest conditions (monotonicity hypothesis not isolated; denominators' positivity not separable into short lemmas). Consequences are specific and honest about the strictMono crux and the non-reducibility of differently-shaped regions. The bounded-prover leaf criterion is now stated explicitly ('bounded size - a leaf the prover can be expected to close in one sitting'), and the revision restricts 'good leaf' to the three short children (integral_f_pos 16L, integral_f_sq_pos 16L, weighted_average_lt_of_strictMono 11L) while correctly marking centroid_2d_formula (143L) and centroid_3d_formula (341L) as large identification lemmas 'not bounded leaves'. The exemplar's cost is acknowledged as the price of the reusable shape ('paid once and walled off behind the two formula lemmas'), not a disqualifier. Verified in copied code: key_product_ineq (L106-~215+) is the heavy symmetrization double-integral argument; weighted_average_lt_of_strictMono L431-441 cites integral_f_pos/integral_f_sq_pos/key_product_ineq and closes with div_lt_div_iff0+linarith; line counts match shape.child_lines [16,16,11,143,341]. | reviewer-generality |
| provenance-licence | accept | Commit 60d33c8ba19af905bd731e938ebde1c5b8c76519 is consistent across entry.json source.commit, sources/numina-putnam2025/source.json, and SOURCE.md. Licence recorded as MIT in entry.json, README, source.json (licence_files=[LICENSE]) and SOURCE.md; upstream-LICENSE is a genuine MIT text (Copyright (c) 2025 Numina). Every permalink (file + 6 sites) uses the pinned commit hash with matching line ranges. Copied file code/NuminaPutnam2025/putnam_2025_b2.lean is 53575 bytes matching entry.json bytes, and check_provenance.py already passed (1 file byte-identical at the pinned commit). Source note SOURCE.md records repo URL, pinned commit, browse-at-commit link, licence, and attribution; README Source and licence section points to it. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/project-numina/Numina-Putnam2025 at commit `60d33c8ba19af905bd731e938ebde1c5b8c76519`, under `MIT`; see the [source note](../../sources/numina-putnam2025/SOURCE.md) for the licence text and attribution.
