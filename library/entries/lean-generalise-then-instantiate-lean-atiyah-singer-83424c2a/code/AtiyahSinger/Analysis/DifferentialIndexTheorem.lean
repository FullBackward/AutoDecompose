/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DifferentialParametrix
public import AtiyahSinger.Analysis.IndexTheorem

/-!
# Atiyah–Singer for the original elliptic differential operator

Public module ID: M0434.

T01: the differential principal polynomial supplies its own homogeneous
representative. Thus an elliptic differential operator needs no extra
classical-symbol assumption when applying the existing K-theoretic index
theorem. The support class below uses the original differential-to-PDO
inclusion, whose section map is unchanged, and the established regularized
principal-polynomial comparison. Its intrinsic description retains exactly
the same original symbol function and bundles.

Sources: SG III.1, the differential principal symbol and ellipticity,
pp.168--170; III.3.15 and III.3.18--19, the differential/PDO symbol comparison;
and III.13, Theorem 13.2 and its proof, pp.244--254. The supplied quantization
presentation and positive smooth density are construction choices, not
additional restrictions on the operator's principal symbol. No Hermitian
metric, spin structure, orientation, positive differential order, connectedness,
or equality of bundle ranks is imposed. The full Euclidean manifold model
has no boundary. The rank-zero and zero-dimensional symbol conventions of
the original support-class construction are retained. The intrinsic symbol-class
comparison and the final K-theoretic index equality are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 25

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

namespace DifferentialOperator

variable {m : ℕ} (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
  (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)

/-- The original differential operator's symbol class, using its actual principal polynomial. -/
def symbolKClass (hP : P.IsElliptic) :
    CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) := by
  -- The differential polynomial itself supplies the homogeneous representative.
  let a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F (m : ℝ) :=
    ⟨P.principalSymbolFunction, P.isSmoothOffZeroGlobalSymbol_principalSymbolFunction,
      P.isHomogeneousGlobalSymbol_principalSymbolFunction⟩
  have hp : (P.toPseudodifferentialOperator μ).principalSymbol =
      globalPrincipalSymbolClass E F (m : ℝ)
        (R.regularizedSymbol (m : ℝ) a.val a.property.1 a.property.2) :=
    P.principalSymbol_eq_regularizedSymbol μ R
  -- Ellipticity is derived for this same PDO and this same symbol, not assumed again.
  have hi : (P.toPseudodifferentialOperator μ).IsElliptic :=
    ((P.toPseudodifferentialOperator μ).isElliptic_iff_homogeneous R a hp).mpr
      (P.isElliptic_iff_isEllipticGlobalSymbol.mp hP)
  exact (P.toPseudodifferentialOperator μ).symbolKClassOfHomogeneous R a hp hi

/-- This class is intrinsically that of the unchanged differential principal polynomial. -/
theorem symbolKClass_eq_principalSymbol (hP : P.IsElliptic) :
    P.symbolKClass μ R hP =
      AtiyahSinger.symbolKClass P.principalSymbolFunction
        P.isSmoothOffZeroGlobalSymbol_principalSymbolFunction.continuous
        (P.isElliptic_iff_isEllipticGlobalSymbol.mp hP) := by
  /- Stage 1: unfold the differential adapter and the existing
  symbolKClassOfHomogeneous. Its representative is exactly the original
  principalSymbolFunction, whose algebraic fiber map is P.principalSymbol.
  Stage 2: unfold homogeneousSymbolKClass. The two continuity and
  ellipticity certificates prove properties of that identical function;
  proof irrelevance identifies them. No operator, symbol, fiber bundle,
  cotangent topology or compact-support convention changes.
  Consequently the right side involves neither the density nor the
  quantization presentation. In dimension zero the off-zero condition
  is vacuous, but the original class retains the source-minus-target
  bundle class; it is not replaced by zero or by equal virtual ranks. -/
  rfl

/-- Atiyah–Singer for an elliptic differential operator, without an extra representative premise. -/
theorem index_eq_cotangentTopologicalIndex (hP : P.IsElliptic) :
    P.analyticIndex hP = cotangentTopologicalIndex n M (P.symbolKClass μ R hP) := by
  /- Stage 1: use the actual homogeneous polynomial assembled in
  symbolKClass. DifferentialParametrix supplies its regularized principal
  quotient equality for the original toPseudodifferentialOperator μ,
  including differential order zero. The two existing ellipticity
  equivalences derive the corresponding PDO ellipticity from hP.
  Stage 2: apply PseudodifferentialOperator.index_eq_cotangentTopologicalIndex
  to this same operator, R, polynomial and derived certificates. Its
  displayed support class is exactly P.symbolKClass μ R hP by construction.
  The original differential-to-PDO inclusion retains P.toLinearMap, so
  its index equals the already defined P.analyticIndex hP.
  Stage 3: the preceding intrinsic-symbol comparison makes the result
  independent of the auxiliary R and μ without replacing the class.
  Disconnected and empty compact bases are covered by the full component
  index theorem; zero-dimensional bases keep the original rank difference.
  No existence of an unspecified homogeneous representative, equality of
  bundle ranks or positive order is supplied as an additional hypothesis. -/
  -- Retain the actual principal polynomial used in the definition of symbolKClass.
  let a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F (m : ℝ) :=
    ⟨P.principalSymbolFunction, P.isSmoothOffZeroGlobalSymbol_principalSymbolFunction,
      P.isHomogeneousGlobalSymbol_principalSymbolFunction⟩
  have hp : (P.toPseudodifferentialOperator μ).principalSymbol =
      globalPrincipalSymbolClass E F (m : ℝ)
        (R.regularizedSymbol (m : ℝ) a.val a.property.1 a.property.2) :=
    P.principalSymbol_eq_regularizedSymbol μ R
  have hi : (P.toPseudodifferentialOperator μ).IsElliptic :=
    ((P.toPseudodifferentialOperator μ).isElliptic_iff_homogeneous R a hp).mpr
      (P.isElliptic_iff_isEllipticGlobalSymbol.mp hP)
  -- The inclusion preserves the smooth-section map and hence its actual index.
  exact PseudodifferentialOperator.index_eq_cotangentTopologicalIndex
    μ (P.toPseudodifferentialOperator μ) R a hp hi

end DifferentialOperator

end AtiyahSinger
