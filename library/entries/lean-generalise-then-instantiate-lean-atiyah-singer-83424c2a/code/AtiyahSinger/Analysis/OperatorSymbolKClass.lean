/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CosphereIndex
public import AtiyahSinger.Analysis.CosphereKClass

/-!
# Symbol classes for displayed homogeneous principal representatives

Public module ID: M0839.

SG III.13 (13.5) is used only for explicitly displayed smooth homogeneous data.
General symbols in S^m are not assumed to possess such representatives. Equality
is tested in the actual principal quotient, not by equality of arbitrary full
symbols. This module constructs the symbol-side class. Analytic index descent
on Kc and finite-topological-type representability in III.13.3 are separate constructions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hC : CompactSpace M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

/-- The support class of explicitly smooth homogeneous elliptic data. -/
def homogeneousSymbolKClass (m : ℝ)
    (a : homogeneousGlobalSymbolSpace (n := n)
    (r := r)
    (q := q) E F m)
    (hi : IsEllipticGlobalSymbol E F a.val) :
    CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) :=
  symbolKClass a.val a.property.1.continuous hi

/-- The homogeneous class is the original continuous off-zero symbol class. -/
theorem homogeneousSymbolKClass_eq_symbol (m : ℝ)
    (a : homogeneousGlobalSymbolSpace (n := n)
    (r := r)
    (q := q) E F m)
    (hi : IsEllipticGlobalSymbol E F a.val) :
    homogeneousSymbolKClass m a hi = symbolKClass a.val a.property.1.continuous hi := by
  /- Unfold the definition, which forgets only the homogeneity and smoothness certificates
  after obtaining continuity. The original function and original source and target bundles
  remain unchanged. -/
  rfl

/-- The homogeneous class is computed by restriction to any chosen cosphere. -/
theorem homogeneousSymbolKClass_eq_cosphere
    (g : SmoothCotangentMetric (n := n)
    (M := M))
    (m : ℝ)
    (a : homogeneousGlobalSymbolSpace (n := n)
    (r := r)
    (q := q) E F m)
    (hi : IsEllipticGlobalSymbol E F a.val) :
    homogeneousSymbolKClass m a hi = cosphereKClass g (cosphereRestriction g a.val)
      (a.property.1.continuous.cosphereRestriction g)
      ((isEllipticCosphereSymbol_restriction_iff g m a.val a.property.2).mpr hi) := by
  /- Apply the symbol reconstruction theorem to the supplied degree-m homogeneity. Its off-zero
  continuity follows from the displayed chartwise smoothness, and degree independence
  identifies the canonical cosphere class. -/
  exact symbolKClass_eq_cosphere g m a.val a.property.1.continuous a.property.2 hi

variable [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

include hM hT hE hF in
/-- Equal regularized principal quotient classes give equal homogeneous K classes. -/
theorem homogeneousSymbolKClass_eq_of_principalClass_eq (m : ℝ)
    (R S : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hi : IsEllipticGlobalSymbol E F a.val) (hj : IsEllipticGlobalSymbol E F b.val)
    (hab : globalPrincipalSymbolClass E F m
        (R.regularizedSymbol m a.val a.property.1 a.property.2) =
      globalPrincipalSymbolClass E F m
        (S.regularizedSymbol m b.val b.property.1 b.property.2)) :
    homogeneousSymbolKClass m a hi = homogeneousSymbolKClass m b hj := by
  /- The fixed-degree regularized principal-class theorem identifies a and b at every nonzero
  covector, even for different quantization presentations. Apply off-zero invariance of the
  actual symbol class. There is no claim of equality at zero or of a homogeneous
  representative for a general principal quotient element. -/
  -- Recover equality on the original punctured fibers using these two presentations.
  have hoff := (R.regularizedSymbol_class_eq_iff S m a.val b.val
    a.property.1 a.property.2 b.property.1 b.property.2).mp hab
  exact symbolKClass_congr a.val a.property.1.continuous hi b.val
    b.property.1.continuous hj hoff


set_option linter.unusedSectionVars false in
/-- A cosphere homotopy identifies the classes of the displayed homogeneous endpoints. -/
theorem homogeneousSymbolKClass_eq_of_cosphereHomotopic
    (g : SmoothCotangentMetric (n := n) (M := M)) (m : ℝ)
    (a b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hi : IsEllipticGlobalSymbol E F a.val) (hj : IsEllipticGlobalSymbol E F b.val)
    (hab : EllipticCosphereHomotopic (r := r) (q := q) g
      (cosphereRestriction g a.val) (cosphereRestriction g b.val)) :
    homogeneousSymbolKClass m a hi = homogeneousSymbolKClass m b hj := by
  /- Compute each original homogeneous class using its cosphere restriction, and use the
  jointly continuous cosphere homotopy. This topological implication needs no smoothing of
  the time parameter and does not assert its converse for arbitrary K-class equality. -/
  -- Both endpoint classes use the same chosen sphere and the given continuous homotopy.
  rw [homogeneousSymbolKClass_eq_cosphere g m a hi,
    homogeneousSymbolKClass_eq_cosphere g m b hj]
  exact cosphereKClass_eq_of_homotopic g _ _ _ _ _ _ hab

variable [hSC : SecondCountableTopology M]
  [MeasurableSpace M] [hB : BorelSpace M]
  {μ : MeasureTheory.Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

namespace PseudodifferentialOperator

variable {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
include hM hT hE hF in
/-- Operator ellipticity agrees with ellipticity of its displayed homogeneous representative. -/
theorem isElliptic_iff_homogeneous (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hP : P.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m a.val a.property.1 a.property.2)) :
    P.IsElliptic ↔ IsEllipticGlobalSymbol E F a.val := by
  /- Use the actual principal-class equality to test the operator on the stated regularized
  full symbol. The existing regularization ellipticity theorem then recovers off-zero
  invertibility of exactly the supplied homogeneous function, with its smooth bundle and
  Hausdorff assumptions retained. -/
  -- The representative comparison preserves the original quantitative ellipticity witness.
  exact (P.isElliptic_iff_of_principalSymbol_eq
    (R.regularizedSymbol m a.val a.property.1 a.property.2) hP).trans
      (isEllipticFullGlobalSymbol_regularizedSymbol_iff R m a.val a.property.1 a.property.2)

/-- The symbol K class of an elliptic PDO with a displayed homogeneous principal representative. -/
def symbolKClassOfHomogeneous (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hP : P.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m a.val a.property.1 a.property.2)) (hi : P.IsElliptic) :
    CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) :=
  homogeneousSymbolKClass m a ((P.isElliptic_iff_homogeneous R a hP).mp hi)

/-- The operator-side construction uses the stated original homogeneous data. -/
theorem symbolKClassOfHomogeneous_eq (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hP : P.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m a.val a.property.1 a.property.2)) (hi : P.IsElliptic) :
    P.symbolKClassOfHomogeneous R a hP hi =
      homogeneousSymbolKClass m a ((P.isElliptic_iff_homogeneous R a hP).mp hi) := by
  /- Unfold the construction. The only step is extraction of homogeneous ellipticity from the
  displayed principal quotient equality, followed by the actual homogeneous support-class
  map. -/
  rfl

include hM hT hE hF in
/-- The PDO class is independent of the displayed homogeneous representative and presentation. -/
theorem symbolKClassOfHomogeneous_independent (R : QuantizationPresentation (n := n)
    (r := r)
    (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hP : P.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m a.val a.property.1 a.property.2)) (hi : P.IsElliptic)
    (S : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hQ : P.principalSymbol = globalPrincipalSymbolClass E F m
      (S.regularizedSymbol m b.val b.property.1 b.property.2)) :
    P.symbolKClassOfHomogeneous R a hP hi = P.symbolKClassOfHomogeneous S b hQ hi := by
  /- Both displayed regularized principal classes equal the original operator principal class.
  Their equality at the same degree determines the homogeneous functions off zero. Apply
  homogeneous class invariance, retaining both presentations and the original source and
  target bundles. -/
  -- Both fields are compared through this same operator's original principal quotient.
  exact homogeneousSymbolKClass_eq_of_principalClass_eq m R S a b _ _
    (hP.symm.trans hQ)

include hM hT hE hF in
/-- Equal principal classes of original PDOs give equal displayed symbol K classes. -/
theorem symbolKClassOfHomogeneous_eq_of_principalSymbol_eq (R : QuantizationPresentation (n := n)
    (r := r)
    (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hP : P.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m a.val a.property.1 a.property.2)) (hi : P.IsElliptic)
    (Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (S : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hQ : Q.principalSymbol = globalPrincipalSymbolClass E F m
      (S.regularizedSymbol m b.val b.property.1 b.property.2))
    (hj : Q.IsElliptic) (hPQ : P.principalSymbol = Q.principalSymbol) :
    P.symbolKClassOfHomogeneous R a hP hi = Q.symbolKClassOfHomogeneous S b hQ hj := by
  /- Combine the two representative equations with equality of the original PDO principal
  classes. Fixed-degree homogeneous recovery gives off-zero equality, which identifies the
  resulting geometric K classes. This conclusion alone does not prove analytic index descent
  through arbitrary stable K equivalence. -/
  -- Transport through the supplied equality of the two actual operator principal classes.
  have hab : globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m a.val a.property.1 a.property.2) =
        globalPrincipalSymbolClass E F m
          (S.regularizedSymbol m b.val b.property.1 b.property.2) :=
    hP.symm.trans (hPQ.trans hQ)
  exact homogeneousSymbolKClass_eq_of_principalClass_eq m R S a b _ _ hab

/-- The operator class is computed by the cosphere of any auxiliary cotangent metric. -/
theorem symbolKClassOfHomogeneous_eq_cosphere (R : QuantizationPresentation (n := n)
    (r := r)
    (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hP : P.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m a.val a.property.1 a.property.2)) (hi : P.IsElliptic)
    (g : SmoothCotangentMetric (n := n) (M := M)) :
    P.symbolKClassOfHomogeneous R a hP hi =
      cosphereKClass g (cosphereRestriction g a.val)
        (a.property.1.continuous.cosphereRestriction g)
        ((isEllipticCosphereSymbol_restriction_iff g m a.val a.property.2).mpr
          ((P.isElliptic_iff_homogeneous R a hP).mp hi)) := by
  /- Identify the operator construction with the homogeneous class of its displayed data. The
  homogeneous restriction theorem computes that class on the chosen cosphere, without
  modifying the underlying cotangent space. -/
  exact homogeneousSymbolKClass_eq_cosphere g m a _

end PseudodifferentialOperator

end AtiyahSinger
