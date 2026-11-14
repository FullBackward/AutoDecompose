/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DifferentialPrincipalSymbol
public import AtiyahSinger.Analysis.EllipticParametrix

/-!
# Parametrices for the original elliptic differential operator

Public module ID: M0435.

D03/A04: connect the polynomial principal symbol of SG III.1.2-1.3 to the
punctured homogeneous model used in III.4.6. Regularizing a smooth full symbol
changes it by a symbol of every order. Thus its principal class is unchanged,
including in differential order zero. The final parametrix acts on the original
differential section map. General inverse-bound ellipticity remains separate.
The native principal symbol's punctured smoothness, homogeneity and exact
ellipticity comparison are proved. Regularization preserves the original principal
class, and the actual parametrix existence theorem retains this same differential map.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold MeasureTheory Set
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 15

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

include hM hT2 hSC hE hF

/-- Full-symbol smoothness restricts to the complement of the zero section. -/
theorem IsGlobalSymbol.isSmoothOffZeroGlobalSymbol {m : ℝ}
    {a : GlobalSymbolFunction (n := n) E F}
    (ha : IsGlobalSymbol (n := n) (r := r) (q := q) E F m a) :
    IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a := by
  /- In every valid chart and frame, take the smoothness part of ha. Restrict
  its domain from the full frequency space to the nonzero frequencies. No
  compactness, homogeneity, ellipticity, or density is needed for restriction. -/
  have _baseSmooth := hM
  have _baseHausdorff := hT2
  have _baseSecondCountable := hSC
  have _sourceSmooth := hE
  have _targetSmooth := hF
  intro c hc e f _ _
  exact (ha c hc e f).1.mono (Set.prod_mono le_rfl (Set.subset_univ _))

set_option maxHeartbeats 800000 in
-- The extended limit accommodates the all-order estimates for the high-frequency regularization
-- error.
/-- A high-frequency regularization of an already smooth symbol changes it by every order. -/
theorem QuantizationPresentation.isGlobalSymbol_regularizedSymbolFunction_sub
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    {m : ℝ} (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m) (l : ℝ) :
    IsGlobalSymbol (n := n) (r := r) (q := q) E F l
      (A.regularizedSymbolFunction p.val - p.val) := by
  /- Stage 1: each cutoff summand is smooth across zero since p itself is smooth
  there. Compact spatial support makes extension across each chart edge smooth.
  Stage 2: enlarge each compact coordinate set to a compact neighborhood inside
  the chart overlap. High-frequency recovery gives equality on its interior for
  all sufficiently large frequencies, hence equality of all derivatives there.
  Stage 3: the remaining frequencies lie in a bounded ball. Bound every derivative
  on the compact product. Every real-order symbol weight is bounded away from zero
  on this product, giving order l. Homogeneity of p is not required. -/
  classical
  have _baseSecondCountable := hSC
  intro c hc e f _ _
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let V := symbolChartDomain E F c e f
  let p₀ := globalSymbolInChart E F p.val c e f
  let T (d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (z η : EuclideanSpace ℝ (Fin n)) :=
    covectorInChart d (c.symm z) (covectorFromChart c (c.symm z) η)
  have hV : IsOpen V := isOpen_symbolChartDomain E F c e f
  have htransition (d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (z η : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target)
      (hdz : c.symm z ∈ d.source) :
      ContDiffAt ℝ ∞ (Function.uncurry (T d)) (z, η) := by
    have hcM := subset_maximalAtlas (I := I) (n := ∞) hc
    have hdM := subset_maximalAtlas (I := I) (n := ∞) hd
    have hforward : ContDiffAt ℝ ∞ (d ∘ c.symm) z := by
      exact ((contMDiffAt_of_mem_maximalAtlas hdM hdz).comp z
        (contMDiffAt_symm_of_mem_maximalAtlas hcM hz)).contDiffAt
    have hinverse : ContDiffAt ℝ ∞ (c ∘ d.symm) (d (c.symm z)) := by
      have hbase : d.symm (d (c.symm z)) ∈ c.source := by
        rw [d.left_inv hdz]
        exact c.map_target hz
      exact ((contMDiffAt_of_mem_maximalAtlas hcM hbase).comp (d (c.symm z))
        (contMDiffAt_symm_of_mem_maximalAtlas hdM (d.map_source hdz))).contDiffAt
    have hderiv := (hinverse.fderiv_right (m := ∞) (by simp)).comp (z, η)
      (hforward.comp (z, η) contDiffAt_fst)
    apply contDiffAt_piLp'
    intro j
    have heval := hderiv.clm_apply (contDiffAt_const (c := EuclideanSpace.single j 1))
    have hscalar := contDiffAt_snd.inner ℝ heval
    apply hscalar.congr_of_eventuallyEq
    have hopen : IsOpen (c.target ∩ c.symm ⁻¹' d.source) :=
      c.continuousOn_symm.isOpen_inter_preimage c.open_target d.open_source
    filter_upwards [hopen.prod isOpen_univ |>.mem_nhds
      (show (z, η) ∈ (c.target ∩ c.symm ⁻¹' d.source) ×ˢ univ from ⟨⟨hz, hdz⟩, trivial⟩)]
      with p hp
    have hsource := hp.1.2
    have hcomp := mfderiv_comp (I := I) (I' := I) (I'' := I) (d (c.symm p.1))
      (by
        simpa only [d.left_inv hsource] using
          (contMDiffAt_of_mem_maximalAtlas hcM (c.map_target hp.1.1)).mdifferentiableAt
            (by simp))
      ((contMDiffAt_symm_of_mem_maximalAtlas hdM (d.map_source hsource)).mdifferentiableAt
        (by simp))
    rw [mfderiv_eq_fderiv] at hcomp
    dsimp [NormedSpace.fromTangentSpace, tangentSpaceCastModel] at hcomp
    rw [d.left_inv hsource] at hcomp
    change inner ℝ p.2 ((mfderiv I I c (c.symm p.1))
        ((mfderiv I I d.symm (d (c.symm p.1))) (EuclideanSpace.single j 1))) =
      inner ℝ p.2
        ((fderiv ℝ (c ∘ d.symm) (d (c.symm p.1))) (EuclideanSpace.single j 1))
    change fderiv ℝ (c ∘ d.symm) (d (c.symm p.1)) =
      (mfderiv I I c (c.symm p.1)).comp (mfderiv I I d.symm (d (c.symm p.1))) at hcomp
    rw [hcomp]
    rfl
  let P (j : Fin A.size) := (A.patch j).chart.symm '' tsupport (A.patch j).input.cutoff
  have hP (j : Fin A.size) : IsCompact (P j) :=
    (A.patch j).input.compact_support.image_of_continuousOn
      ((A.patch j).chart.continuousOn_symm.mono
        (fun y hy ↦ ((A.patch j).input.support_subset hy).1))
  have hPsource (j : Fin A.size) : P j ⊆ (A.patch j).chart.source := by
    rintro x ⟨y, hy, rfl⟩
    exact (A.patch j).chart.map_target (((A.patch j).input.support_subset hy).1)
  have hweight (j : Fin A.size) (x : M) (hx : (A.patch j).weight x ≠ 0) : x ∈ P j := by
    have hsource : x ∈ (A.patch j).chart.source := by
      by_contra hout
      exact hx (by simp [QuantizationPatch.weight, hout])
    have hcut : (A.patch j).input.cutoff ((A.patch j).chart x) ≠ 0 := by
      simpa only [QuantizationPatch.weight, ite_eq_left hsource] using hx
    exact ⟨(A.patch j).chart x, subset_tsupport _ hcut,
      (A.patch j).chart.left_inv hsource⟩
  have hcoord : globalSymbolInChart E F (A.regularizedSymbolFunction p.val) c e f =
      fun z η ↦ ∑ j, (((A.patch j).weight (c.symm z) *
        highFrequencyCutoff n (T (A.patch j).chart z η) : ℝ) : ℂ) • p₀ z η := by
    ext z η v
    simp [globalSymbolInChart, regularizedSymbolFunction, p₀, T]
  -- Prove actual smoothness in every original chart, including its zero covectors.
  have hreg : ContDiffOn ℝ ∞
      (Function.uncurry (globalSymbolInChart E F (A.regularizedSymbolFunction p.val) c e f))
      (V ×ˢ univ) := by
    rw [hcoord]
    intro w hw
    have hbasecont : ContinuousAt (fun y : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin n) ↦ c.symm y.1) w :=
      (c.continuousOn_symm.continuousAt (c.open_target.mem_nhds hw.1.1.1)).comp
        continuousAt_fst
    have hterm (j : Fin A.size) :
        ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
          (((A.patch j).weight (c.symm y.1) *
            highFrequencyCutoff n (T (A.patch j).chart y.1 y.2) : ℝ) : ℂ) • p₀ y.1 y.2) w := by
      let d := (A.patch j).chart
      have hd := (A.patch j).chart_mem_atlas
      by_cases hbase : c.symm w.1 ∈ P j
      · have hsource := hPsource j hbase
        -- The original full symbol is already smooth at every frequency.
        have hcM := subset_maximalAtlas (I := I) (n := ∞) hc
        have hdM := subset_maximalAtlas (I := I) (n := ∞) hd
        have hforward : ContDiffAt ℝ ∞ (d ∘ c.symm) w.1 :=
          ((contMDiffAt_of_mem_maximalAtlas hdM hsource).comp w.1
            (contMDiffAt_symm_of_mem_maximalAtlas hcM hw.1.1.1)).contDiffAt
        have hweightSmooth := (A.patch j).input.smooth_cutoff.contDiffAt.comp w
          (hforward.comp w contDiffAt_fst)
        have hcutSmooth := contDiff_highFrequencyCutoff.contDiffAt.comp w
          (htransition d hd w.1 w.2 hw.1.1.1 hsource)
        have hfactor := Complex.ofRealCLM.contDiff.contDiffAt.comp w
          (hweightSmooth.mul hcutSmooth)
        have hp : ContDiffAt ℝ ∞ (Function.uncurry p₀) w :=
          (p.property c hc e f).1.contDiffAt ((hV.prod isOpen_univ).mem_nhds hw)
        apply (hfactor.smul hp).congr_of_eventuallyEq
        filter_upwards [hbasecont (d.open_source.mem_nhds hsource)] with y hy
        change (((A.patch j).weight (c.symm y.1) *
          highFrequencyCutoff n (T d y.1 y.2) : ℝ) : ℂ) • p₀ y.1 y.2 =
          (((A.patch j).input.cutoff (d (c.symm y.1)) *
            highFrequencyCutoff n (T d y.1 y.2) : ℝ) : ℂ) • p₀ y.1 y.2
        have hy' : c.symm y.1 ∈ (A.patch j).chart.source := hy
        rw [QuantizationPatch.weight, ite_eq_left hy']
      · -- Across a patch boundary the fixed compact support leaves a genuine zero neighborhood.
        apply (contDiffAt_const (c := (0 : EuclideanSpace ℂ (Fin r) →L[ℂ]
          EuclideanSpace ℂ (Fin q)))).congr_of_eventuallyEq
        filter_upwards [hbasecont ((hP j).isClosed.isOpen_compl.mem_nhds hbase)] with y hy
        have hzero : (A.patch j).weight (c.symm y.1) = 0 := by
          by_contra hne
          exact hy (hweight j (c.symm y.1) hne)
        simp only [hzero, zero_mul, Complex.ofReal_zero, zero_smul]
    change ContDiffWithinAt ℝ ∞ (fun y ↦ ∑ j,
      (((A.patch j).weight (c.symm y.1) *
        highFrequencyCutoff n (T (A.patch j).chart y.1 y.2) : ℝ) : ℂ) • p₀ y.1 y.2)
      (V ×ˢ univ) w
    exact (ContDiffAt.sum (s := Finset.univ) (fun j _ ↦ hterm j)).contDiffWithinAt
  -- High-frequency recovery on a compact neighborhood controls all spatial derivatives.
  have hsub : globalSymbolInChart E F
      (A.regularizedSymbolFunction p.val - p.val) c e f =
        globalSymbolInChart E F (A.regularizedSymbolFunction p.val) c e f - p₀ := by
    ext z η v
    simp [globalSymbolInChart, p₀]
  rw [hsub]
  have hd := hreg.sub (p.property c hc e f).1
  refine ⟨hd, ?_⟩
  intro K hKV hK α β
  obtain ⟨K', hK', hKK', hK'V⟩ := exists_compact_between hK hV hKV
  have hint : interior K' ⊆ V := interior_subset.trans hK'V
  obtain ⟨R, hR, hrecovery⟩ :=
    A.regularizedSymbolFunction_eq_inChart_at_high_frequency p.val c hc e f K' hK' hK'V
  let d := globalSymbolInChart E F (A.regularizedSymbolFunction p.val) c e f - p₀
  have hsupp : ∀ z ∈ interior K', ∀ η, R ≤ ‖η‖ → d z η = 0 := by
    intro z hz η hη
    exact sub_eq_zero.mpr (hrecovery z (interior_subset hz) η hη)
  -- Smooth compact frequency support absorbs every requested real symbol weight.
  have hlocal := isSmoothingSymbol_of_frequency_support isOpen_interior d R
    (hd.mono (Set.prod_mono hint subset_rfl)) hsupp l
  exact hlocal.2 K hKK' hK α β

/-- Regularization preserves the principal class of a smooth homogeneous full symbol. -/
theorem QuantizationPresentation.regularizedSymbol_class_eq
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    {m : ℝ} (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hh : IsHomogeneousGlobalSymbol E F m p.val) :
    globalPrincipalSymbolClass E F m
        (A.regularizedSymbol m p.val p.property.isSmoothOffZeroGlobalSymbol hh) =
      globalPrincipalSymbolClass E F m p := by
  /- The previous difference estimate at l=m-1 places the actual difference in
  the submodule defining the principal quotient. Apply its equality criterion.
  The representatives may disagree at zero, even in order zero; only their
  quotient classes are equal. Homogeneity is used to bundle the regularization. -/
  -- The very same representatives differ by the quotient's order m-1 subspace.
  apply (globalPrincipalSymbolClass_eq_iff E F m _ _).mpr
  exact A.isGlobalSymbol_regularizedSymbolFunction_sub p (m - 1)

namespace DifferentialOperator

variable {m : ℕ} (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)

/-- The differential principal polynomial is smooth away from zero cotangent vectors. -/
theorem isSmoothOffZeroGlobalSymbol_principalSymbolFunction :
    IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F
      P.principalSymbolFunction := by
  /- Reconstruct the Hom-valued principal polynomial from its finitely many input
  columns. Each column is smooth by the original coordinate principal-symbol
  theorem. Fixed projection-and-value maps reconstruct the same continuous fiber
  map, proving smoothness on the full frequency domain. Restrict this smoothness
  to nonzero frequencies without invoking global symbol-order estimates. -/
  classical
  intro c hc e f _ _
  let V := EuclideanSpace ℂ (Fin r)
  let W := EuclideanSpace ℂ (Fin q)
  let a := Function.uncurry (globalSymbolInChart E F P.principalSymbolFunction c e f)
  let Ω := symbolChartDomain E F c e f ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin n)))
  -- Smoothness on each fixed input vector gives all columns in the original input frame.
  have hcolumn (v : V) : ContDiffOn ℝ ∞ (fun z ↦ a z v) Ω := by
    exact P.contDiffOn_principalSymbol_in_chart c hc e f v
  have hsum (v : V) : ∑ j : Fin r, v j • EuclideanSpace.single j 1 = v := by
    simpa only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin r) ℂ).toBasis.sum_repr v
  -- Reconstruct the same Hom-valued symbol from its finitely many smooth columns.
  have hs : ContDiffOn ℝ ∞
      (fun z ↦ ∑ j : Fin r, (EuclideanSpace.proj (𝕜 := ℂ) j).smulRight
        (a z (EuclideanSpace.single j 1))) Ω := by
    apply ContDiffOn.sum
    intro j _
    exact ((ContinuousLinearMap.smulRightL ℂ V W (EuclideanSpace.proj j)).restrictScalars
      ℝ).contDiff.comp_contDiffOn (hcolumn (EuclideanSpace.single j 1))
  have heq : (fun z ↦ ∑ j : Fin r, (EuclideanSpace.proj (𝕜 := ℂ) j).smulRight
      (a z (EuclideanSpace.single j 1))) = a := by
    funext z
    apply ContinuousLinearMap.ext
    intro v
    simpa only [sum_apply, ContinuousLinearMap.smulRight_apply, EuclideanSpace.proj,
      PiLp.proj_apply, ← map_smul, ← map_sum] using congrArg (a z) (hsum v)
  rw [heq] at hs
  -- Restriction retains the same chart and frames and makes no symbol-order estimate.
  exact hs.mono (Set.prod_mono le_rfl (Set.subset_univ _))

/-- Polynomial homogeneity agrees with positive real homogeneity of degree m. -/
theorem isHomogeneousGlobalSymbol_principalSymbolFunction :
    IsHomogeneousGlobalSymbol E F (m : ℝ) P.principalSymbolFunction := by
  /- Use principalSymbol_smul for real t on the underlying algebraic map.
  Real.rpow_natCast identifies t^(m:Real) with the natural power, and complex
  coercion preserves that power. ContinuousLinearMap extensionality upgrades the
  equality. The target uses only t>0 and nonzero covectors, and allows m=0. -/
  intro x ξ _ t _
  apply ContinuousLinearMap.ext
  intro v
  -- The algebraic polynomial and the continuous packaging have exactly the same values.
  change P.principalSymbol x (t • ξ) v =
    ((t ^ (m : ℝ) : ℝ) : ℂ) • P.principalSymbol x ξ v
  simpa only [Real.rpow_natCast, Complex.ofReal_pow, LinearMap.smul_apply] using
    LinearMap.congr_fun (P.principalSymbol_smul x ξ t) v

/-- Adding the continuity certificate preserves precisely differential ellipticity. -/
theorem isElliptic_iff_isEllipticGlobalSymbol :
    P.IsElliptic ↔ IsEllipticGlobalSymbol E F P.principalSymbolFunction := by
  /- Both predicates quantify over the same actual nonzero cotangent vectors
  and require bijectivity of the same fiber function. Project the continuous map
  with principalSymbolFunction_toLinearMap. No equality of bundle ranks or
  nonzero base dimension is imposed; any such consequences need separate hypotheses. -/
  -- Both sides test bijectivity of precisely the original fiber map, at the same covectors.
  exact Iff.rfl

variable [hC : CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hC hμ

/-- The original differential PDO has the principal class of its regularized top polynomial. -/
theorem principalSymbol_eq_regularizedSymbol
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F) :
    (P.toPseudodifferentialOperator μ).principalSymbol =
      globalPrincipalSymbolClass E F (m : ℝ)
        (A.regularizedSymbol (m : ℝ) P.principalSymbolFunction
          P.isSmoothOffZeroGlobalSymbol_principalSymbolFunction
          P.isHomogeneousGlobalSymbol_principalSymbolFunction) := by
  /- Identify the left side with the class of P.principalGlobalSymbol by the
  existing differential-to-PDO comparison. The regularization comparison gives
  the right side as the same class. Proof irrelevance identifies the smoothness
  certificates. Equality of classes does not identify the actual representatives. -/
  -- Compare the actual differential principal class and its prescribed regularization.
  rw [P.principalSymbol_toPseudodifferentialOperator μ]
  exact (A.regularizedSymbol_class_eq P.principalGlobalSymbol
    P.isHomogeneousGlobalSymbol_principalSymbolFunction).symm

/-- SG III.4.6: an elliptic differential operator has a two-sided smooth-kernel parametrix. -/
theorem exists_parametrix (hP : P.IsElliptic) :
    ∃ Q : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ (-(m : ℝ)),
      IsParametrix μ P.toLinearMap Q.toLinearMap := by
  /- Stage 1: choose finite quantization presentations for E-to-F and F-to-E.
  P's top polynomial is punctured smooth, homogeneous of degree m and elliptic,
  and the preceding theorem identifies the original PDO's principal class.
  Stage 2: apply exists_parametrix_of_homogeneous_principalSymbol to that PDO.
  Its section map is definitionally P.toLinearMap, so the resulting two smoothing
  errors concern P itself. This includes m=0 and imposes no Hermitian structure.
  Compactness is used for finite presentations and the global smooth-kernel calculus. -/
  obtain ⟨A⟩ := nonempty_quantizationPresentation (n := n) (r := r) (q := q)
    (E := E) (F := F)
  obtain ⟨B⟩ := nonempty_quantizationPresentation (n := n) (r := q) (q := r)
    (E := F) (F := E)
  exact exists_parametrix_of_homogeneous_principalSymbol μ A B
    (P.toPseudodifferentialOperator μ) P.principalSymbolFunction
    P.isSmoothOffZeroGlobalSymbol_principalSymbolFunction
    P.isHomogeneousGlobalSymbol_principalSymbolFunction
    (P.isElliptic_iff_isEllipticGlobalSymbol.mp hP)
    (P.principalSymbol_eq_regularizedSymbol μ A)

end DifferentialOperator

end AtiyahSinger
