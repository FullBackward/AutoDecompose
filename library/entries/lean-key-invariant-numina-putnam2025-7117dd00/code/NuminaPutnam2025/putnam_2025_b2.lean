import Mathlib
set_option pp.numericTypes true
set_option pp.funBinderTypes true
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat MeasureTheory Set Real

-- Helper lemmas for integrability
lemma continuous_mul_f_integrable (f : ℝ → ℝ) (hfc : Continuous f) :
    IntervalIntegrable (fun x => x * f x) volume 0 1 := by
  apply Continuous.intervalIntegrable
  exact continuous_id.mul hfc

lemma continuous_f_sq_integrable (f : ℝ → ℝ) (hfc : Continuous f) :
    IntervalIntegrable (fun x => f x ^ 2) volume 0 1 := by
  apply Continuous.intervalIntegrable
  exact hfc.pow 2

lemma continuous_mul_f_sq_integrable (f : ℝ → ℝ) (hfc : Continuous f) :
    IntervalIntegrable (fun x => x * f x ^ 2) volume 0 1 := by
  apply Continuous.intervalIntegrable
  exact continuous_id.mul (hfc.pow 2)

-- Positivity of integrals
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

/-- Symmetrization helper: (x-y)(f(x)-f(y)) ≥ 0 for strictly monotone f -/
lemma symm_product_nonneg (f : ℝ → ℝ) (hfm : StrictMono f) (x y : ℝ) :
    0 ≤ (x - y) * (f x - f y) := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · have h1 : x - y < 0 := sub_neg_of_lt hxy
    have h2 : f x - f y < 0 := sub_neg_of_lt (hfm hxy)
    exact mul_nonneg_of_nonpos_of_nonpos h1.le h2.le
  · simp
  · have h1 : x - y > 0 := sub_pos_of_lt hxy
    have h2 : f x - f y > 0 := sub_pos_of_lt (hfm hxy)
    exact mul_nonneg h1.le h2.le

/-- Symmetrization helper: (x-y)(f(x)-f(y)) > 0 for strictly monotone f when x ≠ y -/
lemma symm_product_pos (f : ℝ → ℝ) (hfm : StrictMono f) (x y : ℝ) (hne : x ≠ y) :
    0 < (x - y) * (f x - f y) := by
  rcases hne.lt_or_gt with hxy | hxy
  · have h1 : x - y < 0 := sub_neg_of_lt hxy
    have h2 : f x - f y < 0 := sub_neg_of_lt (hfm hxy)
    exact mul_pos_of_neg_of_neg h1 h2
  · have h1 : x - y > 0 := sub_pos_of_lt hxy
    have h2 : f x - f y > 0 := sub_pos_of_lt (hfm hxy)
    exact mul_pos h1 h2

/-- The key integrand for the symmetrization argument -/
def key_integrand (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (p.1 - p.2) * (f p.1) * (f p.2) * (f p.1 - f p.2)

/-- The key integrand is non-negative for strictly monotone f -/
lemma key_integrand_nonneg (f : ℝ → ℝ) (hfm : StrictMono f)
    (hf : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ f x) (p : ℝ × ℝ)
    (hp : p ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) :
    0 ≤ key_integrand f p := by
  unfold key_integrand
  have h1 : 0 ≤ f p.1 := hf p.1 hp.1
  have h2 : 0 ≤ f p.2 := hf p.2 hp.2
  have h3 : 0 ≤ (p.1 - p.2) * (f p.1 - f p.2) := symm_product_nonneg f hfm p.1 p.2
  calc 0 ≤ (p.1 - p.2) * (f p.1 - f p.2) * (f p.1 * f p.2) := by
         apply mul_nonneg h3
         exact mul_nonneg h1 h2
       _ = (p.1 - p.2) * f p.1 * f p.2 * (f p.1 - f p.2) := by ring

/-- The key inequality that drives the proof:
    For strictly increasing f ≥ 0 on [0,1],
    (∫xf(x)dx)(∫f(x)²dx) < (∫xf(x)²dx)(∫f(x)dx)

    This is equivalent to showing the double integral
    ∫∫ (x-y)f(x)f(y)(f(x)-f(y)) dxdy > 0
    which holds because (x-y)(f(x)-f(y)) ≥ 0 with equality only on the diagonal. -/
lemma key_product_ineq (f : ℝ → ℝ)
    (hf : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ f x)
    (hfm : StrictMono f)
    (hfc : Continuous f) :
    (∫ x in (0:ℝ)..1, x * f x) * (∫ x in (0:ℝ)..1, f x ^ 2) <
    (∫ x in (0:ℝ)..1, x * f x ^ 2) * (∫ x in (0:ℝ)..1, f x) := by
  -- The proof uses the symmetrization double integral argument.
  -- Key identity: After expanding using Fubini and symmetrizing:
  -- 2(RHS - LHS) = ∫∫_{[0,1]²} (x-y)·f(x)·f(y)·(f(x)-f(y)) dxdy > 0
  --
  -- This double integral is positive because:
  -- 1. The integrand (x-y)(f(x)-f(y))·f(x)·f(y) is non-negative everywhere
  --    (by symm_product_nonneg: (x-y) and (f(x)-f(y)) have the same sign, and f ≥ 0)
  -- 2. The integrand is strictly positive on a set of positive measure
  --    (whenever x ≠ y and both f(x), f(y) > 0)
  --
  -- Technical details: For strictly increasing f ≥ 0 on [0,1]:
  -- - f(t) > 0 for all t ∈ (0,1] since f(t) > f(0) ≥ 0
  -- - The set {(x,y) : x ≠ y, x,y ∈ (0,1)} has positive Lebesgue measure
  -- - The integrand is continuous
  -- - By integral_pos_of_integrable_nonneg_nonzero, the double integral is positive
  --
  -- Since the double integral equals 2(RHS - LHS), we conclude RHS - LHS > 0.
  --
  -- The formal proof requires setting up the product measure theory carefully:
  -- 1. Convert interval integrals to set integrals over Icc 0 1
  -- 2. Use MeasureTheory.integral_prod_mul to express products as double integrals
  -- 3. Apply symmetrization via integral_prod_symm
  -- 4. Show integrand positivity using key_integrand_nonneg and symm_product_pos
  -- 5. Apply integral_pos_of_integrable_nonneg_nonzero on the product space
  --
  -- This requires significant measure theory machinery.
  -- The mathematical argument is complete; formalization deferred.
  -- The proof follows the symmetrization argument via double integrals:
  --
  -- Let A = ∫xf(x)dx, B = ∫f(x)²dx, C = ∫xf(x)²dx, D = ∫f(x)dx
  -- We want: AB < CD
  --
  -- Key identity: CD - AB = ∫∫ x·f(x)·f(y)·(f(x) - f(y)) dxdy
  --
  -- By symmetry (swapping x,y): CD - AB = ∫∫ y·f(y)·f(x)·(f(y) - f(x)) dxdy
  --
  -- Adding these: 2(CD - AB) = ∫∫ (x-y)·f(x)·f(y)·(f(x)-f(y)) dxdy
  --
  -- The integrand (x-y)·f(x)·f(y)·(f(x)-f(y)) = f(x)·f(y)·(x-y)·(f(x)-f(y)) ≥ 0
  -- because (x-y) and (f(x)-f(y)) have the same sign for strictly monotone f,
  -- and f(x), f(y) ≥ 0.
  --
  -- The integrand is strictly positive when x ≠ y and both f(x), f(y) > 0,
  -- which occurs on (0,1] × (0,1] minus the diagonal (a set of positive measure).
  --
  -- Therefore ∫∫ ≥ 0 with strict positivity, so CD - AB > 0.

  -- The formal proof is a direct positivity argument using the product measure structure
  -- with the key observation that (x-y)(f(x)-f(y)) ≥ 0 for monotone f.

  -- For the formal proof, we establish the double integral positivity directly.
  -- This is a standard argument in real analysis.

  have hI1_pos : 0 < ∫ x in (0:ℝ)..1, f x := integral_f_pos f hf hfm hfc
  have hI2_pos : 0 < ∫ x in (0:ℝ)..1, f x ^ 2 := integral_f_sq_pos f hf hfm hfc

  -- The key claim is that the difference
  -- (∫xf²)(∫f) - (∫xf)(∫f²) > 0
  -- This follows from the double integral identity and positivity.

  -- Let μ be the volume restricted to Icc 0 1
  set μ := volume.restrict (Icc (0:ℝ) 1)

  -- The key double integral: ∫∫ (x-y)f(x)f(y)(f(x)-f(y)) dxdy > 0
  -- This equals 2 * ((∫xf²)(∫f) - (∫xf)(∫f²))

  -- Define the double integral integrand
  let Δ := fun p : ℝ × ℝ => (p.1 - p.2) * f p.1 * f p.2 * (f p.1 - f p.2)

  -- Δ is non-negative everywhere on [0,1]²
  have hΔ_nonneg : ∀ p ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, 0 ≤ Δ p := fun p hp => by
    simp only [Δ]
    have h1 : 0 ≤ f p.1 := hf p.1 hp.1
    have h2 : 0 ≤ f p.2 := hf p.2 hp.2
    have h3 : 0 ≤ (p.1 - p.2) * (f p.1 - f p.2) := symm_product_nonneg f hfm p.1 p.2
    have : 0 ≤ (p.1 - p.2) * (f p.1 - f p.2) * (f p.1 * f p.2) := mul_nonneg h3 (mul_nonneg h1 h2)
    linarith [this]

  -- Δ is strictly positive at (1/2, 1/4)  (or any pair with x ≠ y and x,y > 0)
  have hΔ_pos_example : 0 < Δ ((1/2 : ℝ), (1/4 : ℝ)) := by
    simp only [Δ]
    have hne : (1/2 : ℝ) ≠ 1/4 := by norm_num
    have h12_pos : (0:ℝ) < 1/2 := by norm_num
    have h14_pos : (0:ℝ) < 1/4 := by norm_num
    have hf12_pos : 0 < f (1/2) := by
      have : f (1/2) > f 0 := hfm h12_pos
      have : f 0 ≥ 0 := hf 0 (by norm_num)
      linarith
    have hf14_pos : 0 < f (1/4) := by
      have : f (1/4) > f 0 := hfm h14_pos
      have : f 0 ≥ 0 := hf 0 (by norm_num)
      linarith
    have hsym : 0 < ((1/2 : ℝ) - 1/4) * (f (1/2) - f (1/4)) := by
      apply symm_product_pos f hfm (1/2) (1/4) hne
    have hprod : 0 < f (1/2) * f (1/4) := mul_pos hf12_pos hf14_pos
    have : 0 < ((1/2 : ℝ) - 1/4) * (f (1/2) - f (1/4)) * (f (1/2) * f (1/4)) :=
      mul_pos hsym hprod
    linarith [this]

  -- Δ is continuous
  have hΔ_cont : Continuous Δ := by
    simp only [Δ]
    apply Continuous.mul
    apply Continuous.mul
    apply Continuous.mul
    · exact continuous_fst.sub continuous_snd
    · exact hfc.comp continuous_fst
    · exact hfc.comp continuous_snd
    · exact (hfc.comp continuous_fst).sub (hfc.comp continuous_snd)

  -- The double integral is positive
  -- Using the fact that Δ is continuous, nonneg on [0,1]², and positive at an interior point

  -- Key identity:
  -- ∫∫Δ dxdy over [0,1]² = 2 * ((∫xf²)(∫f) - (∫xf)(∫f²))
  -- where the integrals are over [0,1]

  -- The proof uses MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae

  -- Since μ = volume.restrict (Icc 0 1), the integral over μ.prod μ is the same
  -- as the integral over Icc 0 1 × Icc 0 1 with volume.prod volume

  -- Step 1: Integrability on the product space
  have hΔ_intOn : IntegrableOn Δ (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) (volume.prod volume) := by
    apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    exact hΔ_cont.continuousOn

  -- Step 2: Show the set integral is positive
  -- Using setIntegral_pos_iff_support_of_nonneg_ae
  have hΔ_int_pos : 0 < ∫ p in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, Δ p ∂(volume.prod volume) := by
    -- The integrand is non-negative a.e.
    have h_ae_nonneg : ∀ᵐ p ∂(volume.prod volume).restrict (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1), 0 ≤ Δ p := by
      apply Filter.eventually_of_mem
      · rw [MeasureTheory.mem_ae_iff]
        -- The set where Δ < 0 has measure zero
        -- Since Δ ≥ 0 on [0,1]², the set {Δ < 0} ∩ [0,1]² is empty
        have h_empty : {p : ℝ × ℝ | Δ p < 0} ∩ (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) = ∅ := by
          ext p
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
          intro hΔ_neg hp
          have := hΔ_nonneg p hp
          linarith
        have h_meas : MeasurableSet {x : ℝ × ℝ | ¬(0 ≤ Δ x)} := by
          apply MeasurableSet.compl
          exact hΔ_cont.measurable (measurableSet_Ici : MeasurableSet (Set.Ici (0 : ℝ)))
        calc ((volume.prod volume).restrict (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)) {x | ¬(0 ≤ Δ x)}
            = (volume.prod volume) ({x | ¬(0 ≤ Δ x)} ∩ (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)) := by
              rw [MeasureTheory.Measure.restrict_apply h_meas]
          _ = (volume.prod volume) ({x | Δ x < 0} ∩ (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)) := by
              congr 1
              ext p
              simp only [Set.mem_inter_iff, Set.mem_setOf_eq, not_le]
          _ = (volume.prod volume) ∅ := by rw [h_empty]
          _ = 0 := by simp
      · intro p hp
        exact hp
    rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae h_ae_nonneg hΔ_intOn]
    -- Need to show the support has positive measure
    -- The support contains an open set around (1/2, 1/4)
    have h_support_pos : 0 < (volume.prod volume) (Function.support Δ ∩ (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)) := by
      -- (1/2, 1/4) is in the support since Δ(1/2, 1/4) ≠ 0
      have h_in_support : ((1/2 : ℝ), (1/4 : ℝ)) ∈ Function.support Δ := by
        simp only [Function.mem_support]
        exact hΔ_pos_example.ne'
      -- The support is open (since Δ is continuous)
      have h_support_open : IsOpen (Function.support Δ) := hΔ_cont.isOpen_support
      -- The interior of [0,1]² is (0,1)²
      have h_in_interior : ((1/2 : ℝ), (1/4 : ℝ)) ∈ interior (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := by
        rw [interior_prod_eq]
        simp only [interior_Icc, Set.mem_prod, Set.mem_Ioo]
        norm_num
      -- Use IsOpen.measure_pos for the interior intersection
      calc 0 < (volume.prod volume) (Function.support Δ ∩ interior (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)) := by
             apply (h_support_open.inter isOpen_interior).measure_pos (volume.prod volume)
             use ((1/2 : ℝ), (1/4 : ℝ))
             exact ⟨h_in_support, h_in_interior⟩
           _ ≤ (volume.prod volume) (Function.support Δ ∩ (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)) := by
             apply MeasureTheory.measure_mono
             apply Set.inter_subset_inter_right
             exact interior_subset
    exact h_support_pos

  -- Step 3: Relate the set integral to interval integrals using Fubini
  -- The key algebraic identity links the double integral to the products

  -- Using the identity:
  -- ∫∫ Δ(x,y) dxdy = ∫∫ (x-y)f(x)f(y)(f(x)-f(y)) dxdy
  -- Expanding: = ∫∫ xf(x)²f(y) - xf(x)f(y)² - yf(x)²f(y) + yf(x)f(y)² dxdy
  -- Using product structure:
  -- = (∫xf²)(∫f) - (∫xf)(∫f²) - (∫f²)(∫yf) + (∫f)(∫yf²)
  -- = (∫xf²)(∫f) - (∫xf)(∫f²) - (∫f²)(∫xf) + (∫f)(∫xf²)  [since ∫yf = ∫xf]
  -- = 2 * ((∫xf²)(∫f) - (∫xf)(∫f²))

  -- So (∫xf²)(∫f) - (∫xf)(∫f²) = (1/2) * ∫∫Δ > 0

  -- The formal proof: Establish the algebraic identity using Fubini and product integral

  -- Abbreviations for the four single integrals (as set integrals over Icc 0 1)
  set A := ∫ x in Icc (0:ℝ) 1, x * f x  -- ∫xf
  set B := ∫ x in Icc (0:ℝ) 1, f x ^ 2  -- ∫f²
  set C := ∫ x in Icc (0:ℝ) 1, x * f x ^ 2  -- ∫xf²
  set D := ∫ x in Icc (0:ℝ) 1, f x  -- ∫f

  -- Key identity: ∫∫Δ = 2(CD - AB)
  have h_identity : ∫ p in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, Δ p ∂(volume.prod volume) = 2 * (C * D - A * B) := by
    -- Expand Δ(x,y) = (x-y)f(x)f(y)(f(x)-f(y))
    -- = xf(x)²f(y) - xf(x)f(y)² - yf(x)²f(y) + yf(x)f(y)²
    -- Then use linearity of integration and product structure
    -- This requires MeasureTheory.setIntegral_prod_mul

    -- First show the integrand expansion
    have h_expand : ∀ p : ℝ × ℝ, Δ p = (p.1 * (f p.1)^2 * f p.2) - (p.1 * f p.1 * (f p.2)^2)
        - (p.2 * (f p.1)^2 * f p.2) + (p.2 * f p.1 * (f p.2)^2) := by
      intro p
      simp only [Δ]
      ring

    -- Use setIntegral_prod_mul for each of the 4 product terms
    have h1 : ∫ p in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, p.1 * (f p.1)^2 * f p.2 ∂(volume.prod volume)
        = (∫ x in Icc (0:ℝ) 1, x * (f x)^2) * (∫ y in Icc (0:ℝ) 1, f y) := by
      have := MeasureTheory.setIntegral_prod_mul (μ := volume) (ν := volume)
        (fun x => x * (f x)^2) (fun y => f y) (Icc 0 1) (Icc 0 1)
      convert this using 2
    have h2 : ∫ p in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, p.1 * f p.1 * (f p.2)^2 ∂(volume.prod volume)
        = (∫ x in Icc (0:ℝ) 1, x * f x) * (∫ y in Icc (0:ℝ) 1, (f y)^2) := by
      have := MeasureTheory.setIntegral_prod_mul (μ := volume) (ν := volume)
        (fun x => x * f x) (fun y => (f y)^2) (Icc 0 1) (Icc 0 1)
      convert this using 2
    have h3 : ∫ p in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, p.2 * (f p.1)^2 * f p.2 ∂(volume.prod volume)
        = (∫ x in Icc (0:ℝ) 1, (f x)^2) * (∫ y in Icc (0:ℝ) 1, y * f y) := by
      have := MeasureTheory.setIntegral_prod_mul (μ := volume) (ν := volume)
        (fun x => (f x)^2) (fun y => y * f y) (Icc 0 1) (Icc 0 1)
      convert this using 2
      ext p; ring
    have h4 : ∫ p in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, p.2 * f p.1 * (f p.2)^2 ∂(volume.prod volume)
        = (∫ x in Icc (0:ℝ) 1, f x) * (∫ y in Icc (0:ℝ) 1, y * (f y)^2) := by
      have := MeasureTheory.setIntegral_prod_mul (μ := volume) (ν := volume)
        (fun x => f x) (fun y => y * (f y)^2) (Icc 0 1) (Icc 0 1)
      convert this using 2
      ext p; ring

    -- Integrability for each of the 4 terms
    have hint1 : IntegrableOn (fun p : ℝ × ℝ => p.1 * (f p.1)^2 * f p.2)
        (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) (volume.prod volume) := by
      apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      apply (continuous_fst.mul ((hfc.pow 2).comp continuous_fst)).mul (hfc.comp continuous_snd)
        |>.continuousOn
    have hint2 : IntegrableOn (fun p : ℝ × ℝ => p.1 * f p.1 * (f p.2)^2)
        (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) (volume.prod volume) := by
      apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      apply (continuous_fst.mul (hfc.comp continuous_fst)).mul ((hfc.pow 2).comp continuous_snd)
        |>.continuousOn
    have hint3 : IntegrableOn (fun p : ℝ × ℝ => p.2 * (f p.1)^2 * f p.2)
        (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) (volume.prod volume) := by
      apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      apply (continuous_snd.mul ((hfc.pow 2).comp continuous_fst)).mul (hfc.comp continuous_snd)
        |>.continuousOn
    have hint4 : IntegrableOn (fun p : ℝ × ℝ => p.2 * f p.1 * (f p.2)^2)
        (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) (volume.prod volume) := by
      apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      apply (continuous_snd.mul (hfc.comp continuous_fst)).mul ((hfc.pow 2).comp continuous_snd)
        |>.continuousOn

    -- Rewrite the integral using the expansion and split
    have hcongr : ∫ p in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, Δ p ∂(volume.prod volume) =
        ∫ p in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1,
          ((p.1 * (f p.1)^2 * f p.2) - (p.1 * f p.1 * (f p.2)^2)
           - (p.2 * (f p.1)^2 * f p.2) + (p.2 * f p.1 * (f p.2)^2)) ∂(volume.prod volume) := by
      apply MeasureTheory.setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
      intro p _; exact h_expand p

    rw [hcongr]
    -- Split the integral using linearity
    simp only [sub_eq_add_neg]
    rw [MeasureTheory.integral_add, MeasureTheory.integral_add, MeasureTheory.integral_add]
    · rw [MeasureTheory.integral_neg, MeasureTheory.integral_neg]
      rw [h1, h2, h3, h4]
      simp only [A, B, C, D]
      ring
    · exact hint1
    · exact hint2.neg
    · exact hint1.add hint2.neg
    · exact hint3.neg
    · exact (hint1.add hint2.neg).add hint3.neg
    · exact hint4

  -- From hΔ_int_pos and h_identity, we get CD - AB > 0
  have h_diff_pos : C * D - A * B > 0 := by
    have h1 : 2 * (C * D - A * B) > 0 := by
      calc 2 * (C * D - A * B) = ∫ p in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, Δ p ∂(volume.prod volume) := h_identity.symm
        _ > 0 := hΔ_int_pos
    linarith

  -- Convert from set integrals to interval integrals
  have eq_A : A = ∫ x in (0:ℝ)..1, x * f x := by
    simp only [A]
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc (μ := volume) (f := fun x => x * f x)]
  have eq_B : B = ∫ x in (0:ℝ)..1, f x ^ 2 := by
    simp only [B]
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc (μ := volume) (f := fun x => f x ^ 2)]
  have eq_C : C = ∫ x in (0:ℝ)..1, x * f x ^ 2 := by
    simp only [C]
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc (μ := volume) (f := fun x => x * f x ^ 2)]
  have eq_D : D = ∫ x in (0:ℝ)..1, f x := by
    simp only [D]
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc (μ := volume) (f := fun x => f x)]

  -- The goal in terms of interval integrals
  rw [← eq_A, ← eq_B, ← eq_C, ← eq_D]

  -- AB < CD follows from CD - AB > 0
  linarith

/-- Key lemma: For a strictly increasing non-negative function f on [0,1],
    the weighted average ∫x·f(x)dx/∫f(x)dx is less than ∫x·f(x)²dx/∫f(x)²dx. -/
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

/-- The integral of the first coordinate over regionBetween 0 f [0,1] equals
    ∫₀¹ x * f(x) dx. This is a Fubini-type result for non-rectangular regions.

    Mathematical proof:
    ∫∫_{R'} x dA = ∫₀¹ (∫₀^{f(x)} x dy) dx = ∫₀¹ x * f(x) dx

    The inner integral ∫₀^{f(x)} x dy = x * f(x) since x is constant w.r.t. y. -/
lemma setIntegral_fst_regionBetween (f : ℝ → ℝ) (hf : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ f x)
    (hfc : Continuous f) :
    ∫ p in regionBetween (fun _ => (0:ℝ)) f (Icc (0:ℝ) 1), p.1 ∂(volume.prod volume) =
    ∫ x in (0:ℝ)..1, x * f x := by
  -- Strategy: Use Fubini's theorem
  -- ∫_{R'} p.1 dA = ∫_x (∫_{0 < y < f(x)} x dy) dx = ∫_x x · f(x) dx
  --
  -- Express the set integral using indicator function, apply Fubini, compute inner integral

  -- First, convert the regionBetween set integral to a form we can use Fubini on
  -- regionBetween 0 f [0,1] = {(x,y) : x ∈ [0,1] ∧ y ∈ Ioo 0 (f x)}
  have hR_meas : MeasurableSet (regionBetween (fun _ => (0:ℝ)) f (Icc (0:ℝ) 1)) :=
    measurableSet_regionBetween measurable_const hfc.measurable measurableSet_Icc

  -- The integral over regionBetween can be computed via indicator function and Fubini
  rw [← integral_indicator hR_meas]

  -- We need integrability for Fubini
  have h_int : Integrable (fun p : ℝ × ℝ => (regionBetween (fun _ => (0:ℝ)) f (Icc 0 1)).indicator
      (fun p => p.1) p) (volume.prod volume) := by
    -- Show p.1 is integrable on regionBetween (a bounded region)
    -- The region is contained in [0,1] × [0, M] for some M
    have hfc_bdd : ∃ M, ∀ x ∈ Icc (0:ℝ) 1, |f x| ≤ M := by
      have := IsCompact.exists_bound_of_continuousOn (isCompact_Icc (a := (0:ℝ)) (b := 1)) hfc.continuousOn
      obtain ⟨M, hM⟩ := this
      exact ⟨M, hM⟩
    obtain ⟨M, hM⟩ := hfc_bdd
    -- regionBetween ⊆ [0,1] × [0, M]
    have h_subset : regionBetween (fun _ => (0:ℝ)) f (Icc 0 1) ⊆ Icc 0 1 ×ˢ Icc 0 M := by
      intro p hp
      simp only [regionBetween, mem_setOf_eq, mem_Ioo] at hp
      simp only [mem_prod, mem_Icc]
      constructor
      · exact hp.1
      · constructor
        · linarith [hp.2.1]
        · have hfp := hM p.1 hp.1
          have hf_nonneg := hf p.1 hp.1
          rw [abs_of_nonneg hf_nonneg] at hfp
          linarith [hp.2.2]
    have h_int_rect : IntegrableOn (fun p : ℝ × ℝ => p.1) (Icc 0 1 ×ˢ Icc 0 M) (volume.prod volume) := by
      apply ContinuousOn.integrableOn_compact' (isCompact_Icc.prod isCompact_Icc)
        (measurableSet_Icc.prod measurableSet_Icc)
      exact continuous_fst.continuousOn
    exact (h_int_rect.mono_set h_subset).integrable_indicator hR_meas

  -- Apply Fubini's theorem
  rw [integral_prod _ h_int]

  -- Now we have ∫ x, (∫ y, indicator_{R'} (x,y) · x dy) dx
  -- For fixed x, the inner integral is ∫ y, indicator_{Ioo 0 (f x)} y · x dy if x ∈ [0,1], else 0

  -- Convert inner integral
  have h_inner : ∀ x, ∫ y, (regionBetween (fun _ => (0:ℝ)) f (Icc 0 1)).indicator (fun p => p.1) (x, y) =
      (Icc (0:ℝ) 1).indicator (fun x => x * f x) x := by
    intro x
    by_cases hx : x ∈ Icc (0:ℝ) 1
    · -- x ∈ [0,1]: inner integral is ∫ y in Ioo 0 (f x), x dy = x * f(x)
      simp only [indicator_of_mem hx]
      have h_ind_eq : ∀ y, (regionBetween (fun _ => (0:ℝ)) f (Icc 0 1)).indicator (fun p => p.1) (x, y) =
          (Ioo (0:ℝ) (f x)).indicator (fun _ => x) y := by
        intro y
        by_cases hy : y ∈ Ioo (0:ℝ) (f x)
        · have hp_mem : (x, y) ∈ regionBetween (fun _ => (0:ℝ)) f (Icc 0 1) := by
            simp only [regionBetween, mem_setOf_eq, mem_Ioo, hx, true_and]
            exact hy
          simp only [indicator_of_mem hy, indicator_of_mem hp_mem]
        · have hp_nmem : (x, y) ∉ regionBetween (fun _ => (0:ℝ)) f (Icc 0 1) := by
            simp only [regionBetween, mem_setOf_eq, mem_Ioo, hx, true_and, not_and, not_lt] at hy ⊢
            exact hy
          simp only [indicator_of_notMem hy, indicator_of_notMem hp_nmem]
      simp_rw [h_ind_eq]
      rw [integral_indicator measurableSet_Ioo]
      rw [setIntegral_const]
      simp only [Real.volume_Ioo, measureReal_def, smul_eq_mul, mul_comm, sub_zero]
      rw [ENNReal.toReal_ofReal (hf x hx)]
    · -- x ∉ [0,1]: indicator is 0
      simp only [indicator_of_notMem hx]
      have h_zero : ∀ y, (regionBetween (fun _ => (0:ℝ)) f (Icc 0 1)).indicator (fun p => p.1) (x, y) = 0 := by
        intro y
        apply indicator_of_notMem
        simp only [regionBetween, mem_setOf_eq, hx, false_and, not_false_eq_true]
      simp only [h_zero, integral_zero]

  simp_rw [h_inner]
  rw [integral_indicator measurableSet_Icc]
  -- Now we have ∫ x in Icc 0 1, x * f x = ∫ x in 0..1, x * f x
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- The centroid formula for the region under a curve.
    For R = {(x,y) : 0 ≤ x ≤ 1, 0 ≤ y ≤ f(x)}, where f is continuous and non-negative,
    the centroid x-coordinate is ⨍ p in R, p.1 = (∫₀¹ x·f(x) dx) / (∫₀¹ f(x) dx).

    This follows from:
    1. measure(R) = ∫∫_R 1 dA = ∫₀¹ f(x) dx  (by Fubini)
    2. ∫∫_R x dA = ∫₀¹ ∫₀^{f(x)} x dy dx = ∫₀¹ x·f(x) dx  (by Fubini)
    3. ⨍ p in R, p.1 = (∫∫_R x dA) / measure(R)
-/
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

/-- The centroid formula for a solid of revolution.
    For R' generated by rotating R about the x-axis, where f is continuous and non-negative,
    the centroid x-coordinate is ⨍ p' in R', p'.1 = (∫₀¹ x·f(x)² dx) / (∫₀¹ f(x)² dx).

    This follows from the disk method:
    1. measure(R') = π · ∫₀¹ f(x)² dx  (volume of solid of revolution)
    2. ∫∫∫_{R'} x dV = π · ∫₀¹ x·f(x)² dx  (first moment)
    3. The π factors cancel in the ratio
-/
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

#print axioms putnam_2025_b2
