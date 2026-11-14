# Specialise the PDO Atiyah-Singer theorem to the elliptic differential operator

| | |
|---|---|
| Kind | instance |
| Move | generalise-then-instantiate |
| Language | lean |
| Status | draft |
| Source | [lean-atiyah-singer](../../sources/lean-atiyah-singer/SOURCE.md) at `09fc7bab3f9f` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T12:38:04Z |

## Intent

A statement about an elliptic differential operator `P` is reduced to the
general PDO Atiyah–Singer theorem: the file embeds `P` as a PDO via
`toPseudodifferentialOperator`, derives the homogeneous representative and the
two ellipticity certificates from `P`'s own principal polynomial, and
instantiates the general theorem. Nothing — no homogeneous representative, no
ellipticity, no metric or rank assumption — is added to the hypotheses.

## The decomposition

### parent `index_eq_cotangentTopologicalIndex`: [`AtiyahSinger/Analysis/DifferentialIndexTheorem.lean` lines 107-138](https://github.com/alpha-squared-labs/Lean-Atiyah-Singer/blob/09fc7bab3f9ff606901bde4b5a5580470da63a70/AtiyahSinger/Analysis/DifferentialIndexTheorem.lean#L107-L138) ([local copy](code/AtiyahSinger/Analysis/DifferentialIndexTheorem.lean))

```lean
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
```

### child `isElliptic_iff_isEllipticGlobalSymbol`: [`AtiyahSinger/Analysis/DifferentialParametrix.lean` lines 318-325](https://github.com/alpha-squared-labs/Lean-Atiyah-Singer/blob/09fc7bab3f9ff606901bde4b5a5580470da63a70/AtiyahSinger/Analysis/DifferentialParametrix.lean#L318-L325) ([local copy](code/AtiyahSinger/Analysis/DifferentialParametrix.lean))

```lean
theorem isElliptic_iff_isEllipticGlobalSymbol :
    P.IsElliptic ↔ IsEllipticGlobalSymbol E F P.principalSymbolFunction := by
  /- Both predicates quantify over the same actual nonzero cotangent vectors
  and require bijectivity of the same fiber function. Project the continuous map
  with principalSymbolFunction_toLinearMap. No equality of bundle ranks or
  nonzero base dimension is imposed; any such consequences need separate hypotheses. -/
  -- Both sides test bijectivity of precisely the original fiber map, at the same covectors.
  exact Iff.rfl
```

### child `principalSymbol_eq_regularizedSymbol`: [`AtiyahSinger/Analysis/DifferentialParametrix.lean` lines 333-347](https://github.com/alpha-squared-labs/Lean-Atiyah-Singer/blob/09fc7bab3f9ff606901bde4b5a5580470da63a70/AtiyahSinger/Analysis/DifferentialParametrix.lean#L333-L347) ([local copy](code/AtiyahSinger/Analysis/DifferentialParametrix.lean))

```lean
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
```

### child `isElliptic_iff_homogeneous`: [`AtiyahSinger/Analysis/OperatorSymbolKClass.lean` lines 138-150](https://github.com/alpha-squared-labs/Lean-Atiyah-Singer/blob/09fc7bab3f9ff606901bde4b5a5580470da63a70/AtiyahSinger/Analysis/OperatorSymbolKClass.lean#L138-L150) ([local copy](code/AtiyahSinger/Analysis/OperatorSymbolKClass.lean))

```lean
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
```

### child `PseudodifferentialOperator.index_eq_cotangentTopologicalIndex`: [`AtiyahSinger/Analysis/IndexTheorem.lean` lines 220-242](https://github.com/alpha-squared-labs/Lean-Atiyah-Singer/blob/09fc7bab3f9ff606901bde4b5a5580470da63a70/AtiyahSinger/Analysis/IndexTheorem.lean#L220-L242) ([local copy](code/AtiyahSinger/Analysis/IndexTheorem.lean))

```lean
theorem PseudodifferentialOperator.index_eq_cotangentTopologicalIndex {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hp : P.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m a.val a.property.1 a.property.2)) (hi : P.IsElliptic) :
    P.toLinearMap.index =
      cotangentTopologicalIndex n M (P.symbolKClassOfHomogeneous R a hp hi) := by
  /- Stage 1: the original analytic symbol theorem evaluates
  analyticIndexOfComponents μ at exactly P.symbolKClassOfHomogeneous R a hp hi
  as the index of P.toLinearMap. Its finite-component and smoothing argument
  concerns the original operator; it is not replaced by a quantization choice.
  Stage 2: evaluate the cotangent homomorphism equality at that same class
  and reverse the analytic evaluation. The resulting integer is the existing
  positive-Bott topological index. hp records the source's classical leading
  symbol condition explicitly; full-symbol ellipticity alone does not supply
  such an a. The differential-operator specialization discharges this condition
  using its original homogeneous principal polynomial. -/
  -- The original operator evaluation uses precisely the supplied homogeneous class.
  have heval := PseudodifferentialOperator.analyticIndexOfComponents_symbolKClassOfHomogeneous
    μ P R a hp hi
  rw [analyticIndexOfComponents_eq_cotangentTopologicalIndex μ] at heval
  exact heval.symm
```

How the parts fit. The parent `index_eq_cotangentTopologicalIndex` is a thin
glue that assembles four children, one of which is the general theorem being
instantiated:

```
index_eq_cotangentTopologicalIndex  (parent, DifferentialIndexTheorem.lean:107-138)
├─ let a : homogeneousGlobalSymbolSpace … := ⟨P.principalSymbolFunction, …⟩   (assembled inline, not a lemma)
├─ have hp := P.principalSymbol_eq_regularizedSymbol μ R                       → principalSymbol_eq_regularizedSymbol
├─ have hi := (…isElliptic_iff_homogeneous R a hp).mpr
│             (P.isElliptic_iff_isEllipticGlobalSymbol.mp hP)                  → isElliptic_iff_homogeneous, isElliptic_iff_isEllipticGlobalSymbol
└─ exact PseudodifferentialOperator.index_eq_cotangentTopologicalIndex
       μ (P.toPseudodifferentialOperator μ) R a hp hi                          → PseudodifferentialOperator.index_eq_cotangentTopologicalIndex
```

The four children, and why each is a good leaf (a self-contained statement
whose proof closes on its own or from named siblings):

1. `principalSymbol_eq_regularizedSymbol` (DifferentialParametrix.lean:333-347).
   The boundary fact that the differential operator's PDO principal symbol
   equals the class of its regularized top polynomial. Its proof is
   `rw [P.principalSymbol_toPseudodifferentialOperator μ]` (the existing
   differential-to-PDO comparison) followed by
   `exact (A.regularizedSymbol_class_eq …).symm`. It closes from two named
   project lemmas, neither of which is the general index theorem.

2. `isElliptic_iff_isEllipticGlobalSymbol` (DifferentialParametrix.lean:318-325).
   Differential ellipticity agrees with global-symbol ellipticity of the
   principal polynomial. Its proof is the single step `exact Iff.rfl`: both
   predicates are definitionally the same test of bijectivity of the same
   fiber map.

3. `isElliptic_iff_homogeneous` (OperatorSymbolKClass.lean:138-150). For a PDO
   with a displayed homogeneous representative, operator ellipticity agrees
   with homogeneous-symbol ellipticity. Its proof is a single
   `exact (…).trans (…)` combining `isElliptic_iff_of_principalSymbol_eq` with
   `isEllipticFullGlobalSymbol_regularizedSymbol_iff`.

4. `PseudodifferentialOperator.index_eq_cotangentTopologicalIndex`
   (IndexTheorem.lean:220-242). The general theorem being instantiated. Its
   proof is `have heval := …analyticIndexOfComponents_symbolKClassOfHomogeneous …`,
   then `rw [analyticIndexOfComponents_eq_cotangentTopologicalIndex μ] at heval`,
   then `exact heval.symm`.

In the glue, the homogeneous representative `a` is built inline from
`P.principalSymbolFunction` and its two certificates; `hp` is supplied by child
1; `hi` is supplied by composing children 3 and 2 (`.mpr` of the homogeneous
equivalence applied to `.mp` of the differential equivalence); and the general
theorem (child 4) is applied to `P.toPseudodifferentialOperator μ` with those
data. No child re-opens the general argument: each is an iff or equality at an
abstraction boundary.

## Why it is good

1. The parent site (the glue) is 32 lines long (`check`, `lines(parent, 32)`),
   i.e. the whole argument is in the children, not the glue —
   [DifferentialIndexTheorem.lean#L107-L138](https://github.com/alpha-squared-labs/Lean-Atiyah-Singer/blob/09fc7bab3f9ff606901bde4b5a5580470da63a70/AtiyahSinger/Analysis/DifferentialIndexTheorem.lean#L107-L138).
2. The glue cites the boundary lemma `principalSymbol_eq_regularizedSymbol`
   (`check`, `cites(parent, principalSymbol_eq_regularizedSymbol)`), at
   [DifferentialIndexTheorem.lean#L132](https://github.com/alpha-squared-labs/Lean-Atiyah-Singer/blob/09fc7bab3f9ff606901bde4b5a5580470da63a70/AtiyahSinger/Analysis/DifferentialIndexTheorem.lean#L132).
3. The authors state the intent in the module docstring: "an elliptic
   differential operator needs no extra classical-symbol assumption when
   applying the existing K-theoretic index theorem" (`author-statement`),
   [DifferentialIndexTheorem.lean#L16-L22](https://github.com/alpha-squared-labs/Lean-Atiyah-Singer/blob/09fc7bab3f9ff606901bde4b5a5580470da63a70/AtiyahSinger/Analysis/DifferentialIndexTheorem.lean#L16-L22).
4. The same three-step specialisation is performed again by the sibling
   definition `symbolKClass` (`known-use`),
   [DifferentialIndexTheorem.lean#L71-L85](https://github.com/alpha-squared-labs/Lean-Atiyah-Singer/blob/09fc7bab3f9ff606901bde4b5a5580470da63a70/AtiyahSinger/Analysis/DifferentialIndexTheorem.lean#L71-L85).
5. The theorem-scale shape is `direct_lemmas = 4`, `glue_lines = 32`,
   `child_lines = [8, 15, 13, 23]`, and `depth = 2` along the chain
   `index_eq_cotangentTopologicalIndex` →
   `PseudodifferentialOperator.index_eq_cotangentTopologicalIndex` →
   `PseudodifferentialOperator.analyticIndexOfComponents_symbolKClassOfHomogeneous`
   (`measurement`); the grandchild is cited at
   [IndexTheorem.lean#L239](https://github.com/alpha-squared-labs/Lean-Atiyah-Singer/blob/09fc7bab3f9ff606901bde4b5a5580470da63a70/AtiyahSinger/Analysis/IndexTheorem.lean#L239)
   and declared at
   [ComponentAnalyticIndex.lean#L175](https://github.com/alpha-squared-labs/Lean-Atiyah-Singer/blob/09fc7bab3f9ff606901bde4b5a5580470da63a70/AtiyahSinger/Analysis/ComponentAnalyticIndex.lean#L175).

In my opinion the detail worth copying is the *shape of the boundary facts*:
three of the four children are iffs/equalities at an abstraction boundary
(`…_iff_…`, `…_eq_…`) whose proofs are one or two steps, so the instantiation
adds structure without re-proving anything. The general theorem is cited once,
at the very end, with the specific operator and its derived certificates.

## When to use it, and when not

Use it when a general theorem over the weaker/more general structure already
exists (here the PDO index theorem), the specific object embeds into it by a
definitional map (`P.toPseudodifferentialOperator μ`), and the instantiation
data — the homogeneous representative and the two ellipticity certificates —
can be derived from the specific object's own principal data by named boundary
lemmas rather than assumed.

Avoid it when the specific-to-general embedding is not definitional (the
boundary facts would then need deep proofs of their own), when the general
theorem's hypotheses are not discharged by the specific structure (the
homogeneous representative and its ellipticity would have to be added as
assumptions, defeating the point), or when the general theorem does not exist
yet, in which case instantiation is re-proving rather than reuse.

## Consequences

The move concentrates the proof burden in four boundary lemmas and leaves the
main theorem a thin glue: the parent's proof body (lines 126-138) only
assembles the homogeneous representative and passes it to the general PDO
theorem. Obligations created: every hypothesis of the general theorem must be
discharged for the specific operator — the PDO (`P.toPseudodifferentialOperator μ`,
definitional), the homogeneous representative `a` (assembled inline from
`P.principalSymbolFunction` and its certificates), the principal-symbol
equality `hp` (`principalSymbol_eq_regularizedSymbol`) and PDO ellipticity `hi`
(`isElliptic_iff_homogeneous` composed with `isElliptic_iff_isEllipticGlobalSymbol`).
Failure mode: if the specific-to-general embedding were not definitional, or if
the general theorem demanded data the specific object cannot supply (a Hermitian
metric, positive order, or equal bundle ranks — all explicitly excluded in the
module docstring), the instantiation would fail and the boundary lemmas would
need real proofs of their own.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: principalSymbol_eq_regularizedSymbol@AtiyahSinger/Analysis/DifferentialIndexTheorem.lean:132, isElliptic_iff_isEllipticGlobalSymbol@AtiyahSinger/Analysis/DifferentialIndexTheorem.lean:135, isElliptic_iff_homogeneous@AtiyahSinger/Analysis/DifferentialIndexTheorem.lean:134, PseudodifferentialOperator.index_eq_cotangentTopologicalIndex@AtiyahSinger/Analysis/DifferentialIndexTheorem.lean:107; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(parent, 32) -> lines: site parent has 32 lines | check_claims.py |
| 2 | verified | cites(parent, principalSymbol_eq_regularizedSymbol) -> cites: principalSymbol_eq_regularizedSymbol occurs at AtiyahSinger/Analysis/DifferentialIndexTheorem.lean:132 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/alpha-squared-labs/Lean-Atiyah-Singer at commit `09fc7bab3f9ff606901bde4b5a5580470da63a70`, under `Apache-2.0`; see the [source note](../../sources/lean-atiyah-singer/SOURCE.md) for the licence text and attribution.
