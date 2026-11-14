# Lower-and-upper-bound sandwich for the Fuchs-van de Graaf inequalities

| | |
|---|---|
| Kind | instance |
| Move | other |
| Language | lean |
| Status | accepted |
| Source | [humanfia-hoa-qed](../../sources/humanfia-hoa-qed/SOURCE.md) at `1c918ec9a96c` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T22:40:52Z |

## Intent

Assemble the Fuchs--van de Graaf inequalities, the two-sided comparison
`1 − F ≤ D ≤ √(1 − F²)` between trace distance `D` and quantum fidelity `F`,
as a conjunction of a lower bound and an upper bound, each proved by its own
dedicated lemma. The glue is a single line that pairs the two lemmas.

## The decomposition

### parent `fuchsVanDeGraafInequalities`: [`lean-qit-qlg/QIT/lean/problem_qit_NormFidelityAndContinuityTools_FuchsVanDeGraafInequalities.lean` lines 790-796](https://github.com/humanfia/hoa-qed/blob/1c918ec9a96c7751ce9c283304e1aebd7ffb19a3/lean-qit-qlg/QIT/lean/problem_qit_NormFidelityAndContinuityTools_FuchsVanDeGraafInequalities.lean#L790-L796) ([local copy](code/lean-qit-qlg/QIT/lean/problem_qit_NormFidelityAndContinuityTools_FuchsVanDeGraafInequalities.lean))

```lean
theorem fuchsVanDeGraafInequalities (rho sigma : State d) :
    1 - QITBench.OneShot.quantumFidelity rho.matrix sigma.matrix ≤
        traceDistance rho sigma ∧
      traceDistance rho sigma ≤
        Real.sqrt
          (1 - (QITBench.OneShot.quantumFidelity rho.matrix sigma.matrix) ^ 2) := by
  exact ⟨fuchsVanDeGraaf_lower rho sigma, fuchsVanDeGraaf_upper rho sigma⟩
```

### child `fuchsVanDeGraaf_lower`: [`lean-qit-qlg/QIT/lean/problem_qit_NormFidelityAndContinuityTools_FuchsVanDeGraafInequalities.lean` lines 467-590](https://github.com/humanfia/hoa-qed/blob/1c918ec9a96c7751ce9c283304e1aebd7ffb19a3/lean-qit-qlg/QIT/lean/problem_qit_NormFidelityAndContinuityTools_FuchsVanDeGraafInequalities.lean#L467-L590) ([local copy](code/lean-qit-qlg/QIT/lean/problem_qit_NormFidelityAndContinuityTools_FuchsVanDeGraafInequalities.lean))

```lean
private theorem fuchsVanDeGraaf_lower (rho sigma : State d) :
    1 - QITBench.OneShot.quantumFidelity rho.matrix sigma.matrix ≤
      traceDistance rho sigma := by
  let R := QITBench.OneShot.matrixSqrt rho.matrix
  let S := QITBench.OneShot.matrixSqrt sigma.matrix
  let N := R - S
  let Δ := rho.matrix - sigma.matrix
  have hR : Rᴴ = R := by
    apply Matrix.PosSemidef.isHermitian
    rw [← Matrix.nonneg_iff_posSemidef]
    exact CFC.sqrt_nonneg _
  have hS : Sᴴ = S := by
    apply Matrix.PosSemidef.isHermitian
    rw [← Matrix.nonneg_iff_posSemidef]
    exact CFC.sqrt_nonneg _
  have hRpos : R.PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]
    exact CFC.sqrt_nonneg _
  have hSpos : S.PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]
    exact CFC.sqrt_nonneg _
  have hRsq : R * R = rho.matrix :=
    CFC.sqrt_mul_sqrt_self rho.matrix (ha := rho.pos.nonneg)
  have hSsq : S * S = sigma.matrix :=
    CFC.sqrt_mul_sqrt_self sigma.matrix (ha := sigma.pos.nonneg)
  have hNherm : N.IsHermitian := by
    dsimp [N]
    rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, hR, hS]
  have hΔherm : Δ.IsHermitian := by
    dsimp [Δ]
    exact rho.pos.isHermitian.sub sigma.pos.isHermitian
  have hΔtr : Δ.trace = 0 := by
    simp [Δ, Matrix.trace_sub, rho.trace_eq_one, sigma.trace_eq_one]
  let P := positiveSupport N hNherm
  have hPpos : P.PosSemidef := by
    simpa [P] using positiveSupport_pos N hNherm
  have hPh : Pᴴ = P := hPpos.isHermitian
  have hPid : P * P = P := by
    simpa [P] using positiveSupport_idem N hNherm
  have hPle : P ≤ 1 := by
    simpa [P] using positiveSupport_le_one N hNherm
  have hNplusPos : (N⁺).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg N)
  have hNminusPos : (N⁻).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg N)
  have hNP : N * P = N⁺ := by
    simpa [P] using mul_positiveSupport N hNherm
  have hPN : P * N = N⁺ := by
    calc
      P * N = (N * P)ᴴ := by
        rw [Matrix.conjTranspose_mul, hNherm.eq, hPh]
      _ = (N⁺)ᴴ := by rw [hNP]
      _ = N⁺ := hNplusPos.isHermitian
  have hExpr : rho.matrix - S * R = N * R := by
    rw [← hRsq]
    dsimp [N]
    noncomm_ring
  have htotal_le_projected :
      Complex.re ((rho.matrix - S * R).trace) ≤
        Complex.re ((P * (rho.matrix - S * R)).trace) := by
    have hnegative :
        0 ≤ Complex.re ((N⁻ * R).trace) :=
      re_trace_mul_nonneg_of_posSemidef hNminusPos hRpos
    rw [hExpr, show P * (N * R) = N⁺ * R by
      rw [← Matrix.mul_assoc, hPN]]
    calc
      Complex.re ((N * R).trace) =
          Complex.re (((N⁺ - N⁻) * R).trace) := by
        rw [CFC.posPart_sub_negPart N hNherm]
      _ = Complex.re ((N⁺ * R).trace) -
          Complex.re ((N⁻ * R).trace) := by
        rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
      _ ≤ Complex.re ((N⁺ * R).trace) := by linarith
  have hDeltaSplit :
      Δ = (rho.matrix - S * R) + S * N := by
    dsimp [Δ, N]
    rw [← hRsq, ← hSsq]
    noncomm_ring
  have hprojected_le_delta :
      Complex.re ((P * (rho.matrix - S * R)).trace) ≤
        Complex.re ((P * Δ).trace) := by
    have hpositive :
        0 ≤ Complex.re ((N⁺ * S).trace) :=
      re_trace_mul_nonneg_of_posSemidef hNplusPos hSpos
    rw [hDeltaSplit, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
    have hcycle :
        Complex.re ((P * (S * N)).trace) =
          Complex.re ((N⁺ * S).trace) := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle P S N, hNP]
    rw [hcycle]
    linarith
  have hdelta_le_posPart :
      Complex.re ((P * Δ).trace) ≤ Complex.re ((Δ⁺).trace) := by
    have hbound := re_trace_mul_le_posPart Δ P hΔherm hPpos hPle
    rw [Matrix.trace_mul_comm Δ P] at hbound
    exact hbound
  have hmain :
      1 - Complex.re ((S * R).trace) ≤ Complex.re ((Δ⁺).trace) := by
    have htrace :
        Complex.re ((rho.matrix - S * R).trace) =
          1 - Complex.re ((S * R).trace) := by
      rw [Matrix.trace_sub, Complex.sub_re, rho.trace_eq_one]
      norm_num
    rw [← htrace]
    exact htotal_le_projected.trans
      (hprojected_le_delta.trans hdelta_le_posPart)
  have htrace_le_fidelity :
      Complex.re ((S * R).trace) ≤
        QITBench.OneShot.quantumFidelity rho.matrix sigma.matrix := by
    rw [quantumFidelity_eq_traceNorm_sqrt_mul_sqrt]
    have hbound := (traceNorm_eq_max_re_trace_unitary (S * R)).right
    simp only [upperBounds, Set.mem_setOf_eq] at hbound
    have hone := hbound
      (a := Complex.re ((((1 : Matrix.unitaryGroup d ℂ).val) * (S * R)).trace))
      ⟨1, rfl⟩
    simpa using hone
  have hposPart_eq_distance :
      Complex.re ((Δ⁺).trace) = traceDistance rho sigma := by
    change Complex.re ((Δ⁺).trace) =
      (1 / 2 : ℝ) * QITBench.OneShot.traceNorm Δ
    rw [traceNorm_eq_two_re_trace_posPart_of_trace_zero Δ hΔherm hΔtr]
    ring
  rw [← hposPart_eq_distance]
  linarith
```

### child `fuchsVanDeGraaf_upper`: [`lean-qit-qlg/QIT/lean/problem_qit_NormFidelityAndContinuityTools_FuchsVanDeGraafInequalities.lean` lines 615-787](https://github.com/humanfia/hoa-qed/blob/1c918ec9a96c7751ce9c283304e1aebd7ffb19a3/lean-qit-qlg/QIT/lean/problem_qit_NormFidelityAndContinuityTools_FuchsVanDeGraafInequalities.lean#L615-L787) ([local copy](code/lean-qit-qlg/QIT/lean/problem_qit_NormFidelityAndContinuityTools_FuchsVanDeGraafInequalities.lean))

```lean
private theorem fuchsVanDeGraaf_upper (rho sigma : State d) :
    traceDistance rho sigma ≤
      Real.sqrt
        (1 - (QITBench.OneShot.quantumFidelity rho.matrix sigma.matrix) ^ 2) := by
  let R := QITBench.OneShot.matrixSqrt rho.matrix
  let S := QITBench.OneShot.matrixSqrt sigma.matrix
  let F := QITBench.OneShot.quantumFidelity rho.matrix sigma.matrix
  have hR : Rᴴ = R := by
    apply Matrix.PosSemidef.isHermitian
    rw [← Matrix.nonneg_iff_posSemidef]
    exact CFC.sqrt_nonneg _
  have hS : Sᴴ = S := by
    apply Matrix.PosSemidef.isHermitian
    rw [← Matrix.nonneg_iff_posSemidef]
    exact CFC.sqrt_nonneg _
  have hRsq : R * R = rho.matrix :=
    CFC.sqrt_mul_sqrt_self rho.matrix (ha := rho.pos.nonneg)
  have hSsq : S * S = sigma.matrix :=
    CFC.sqrt_mul_sqrt_self sigma.matrix (ha := sigma.pos.nonneg)
  have hF :
      F = QITBench.OneShot.traceNorm (S * R) := by
    simpa [F, R, S] using
      quantumFidelity_eq_traceNorm_sqrt_mul_sqrt rho sigma
  obtain ⟨U, hUmax⟩ :=
    (traceNorm_eq_max_re_trace_unitary (S * R)).left
  have hUtrace :
      Complex.re ((U.val * (S * R)).trace) = F :=
    hUmax.trans hF.symm
  let C := U.val * S
  have hUstarU : U.valᴴ * U.val = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self U
  have hCstarC : Cᴴ * C = sigma.matrix := by
    dsimp [C]
    rw [Matrix.conjTranspose_mul, hS]
    rw [Matrix.mul_assoc S U.valᴴ (U.val * S),
      ← Matrix.mul_assoc U.valᴴ U.val S, hUstarU, one_mul,
      hSsq]
  have hRstarR : Rᴴ * R = rho.matrix := by
    rw [hR, hRsq]
  have hcross :
      Complex.re ((Rᴴ * C).trace) = F := by
    rw [hR]
    dsimp [C]
    rw [Matrix.trace_mul_comm R (U.val * S), Matrix.mul_assoc]
    exact hUtrace
  have hcrossStar :
      Complex.re ((Cᴴ * R).trace) = F := by
    calc
      Complex.re ((Cᴴ * R).trace) =
          Complex.re (((Rᴴ * C)ᴴ).trace) := by
            congr 2
            simp [Matrix.conjTranspose_mul]
      _ = Complex.re (star ((Rᴴ * C).trace)) := by
            rw [Matrix.trace_conjTranspose]
      _ = Complex.re ((Rᴴ * C).trace) := Complex.conj_re _
      _ = F := hcross
  have hfsR : frobeniusSq R = 1 := by
    unfold frobeniusSq
    rw [hRstarR, rho.trace_eq_one]
    norm_num
  have hfsC : frobeniusSq C = 1 := by
    unfold frobeniusSq
    rw [hCstarC, sigma.trace_eq_one]
    norm_num
  let X := R - C
  let Y := R + C
  have hfsX : frobeniusSq X = 2 - 2 * F := by
    have hexpand :
        Xᴴ * X =
          Rᴴ * R - Rᴴ * C - Cᴴ * R + Cᴴ * C := by
      dsimp [X]
      rw [Matrix.conjTranspose_sub]
      noncomm_ring
    unfold frobeniusSq
    rw [hexpand]
    simp only [Matrix.trace_add, Matrix.trace_sub,
      Complex.add_re, Complex.sub_re]
    rw [show Complex.re ((Rᴴ * R).trace) = frobeniusSq R by rfl,
      show Complex.re ((Cᴴ * C).trace) = frobeniusSq C by rfl,
      hfsR, hfsC, hcross, hcrossStar]
    ring
  have hfsY : frobeniusSq Y = 2 + 2 * F := by
    have hexpand :
        Yᴴ * Y =
          Rᴴ * R + Rᴴ * C + Cᴴ * R + Cᴴ * C := by
      dsimp [Y]
      rw [Matrix.conjTranspose_add]
      noncomm_ring
    unfold frobeniusSq
    rw [hexpand]
    simp only [Matrix.trace_add, Complex.add_re]
    rw [show Complex.re ((Rᴴ * R).trace) = frobeniusSq R by rfl,
      show Complex.re ((Cᴴ * C).trace) = frobeniusSq C by rfl,
      hfsR, hfsC, hcross, hcrossStar]
    ring
  have hdouble :
      (2 : ℂ) • (rho.matrix - sigma.matrix) =
        Xᴴ * Y + Yᴴ * X := by
    rw [← hRstarR, ← hCstarC]
    dsimp [X, Y]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_add]
    noncomm_ring
    module
  have hxy := traceNorm_conjTranspose_mul_le X Y
  have hyx := traceNorm_conjTranspose_mul_le Y X
  have hnorm :
      QITBench.OneShot.traceNorm (rho.matrix - sigma.matrix) ≤
        Real.sqrt (frobeniusSq X) * Real.sqrt (frobeniusSq Y) := by
    have htwo :
        2 * QITBench.OneShot.traceNorm (rho.matrix - sigma.matrix) ≤
          2 * (Real.sqrt (frobeniusSq X) *
            Real.sqrt (frobeniusSq Y)) := by
      calc
        2 * QITBench.OneShot.traceNorm (rho.matrix - sigma.matrix) =
            QITBench.OneShot.traceNorm
              ((2 : ℂ) • (rho.matrix - sigma.matrix)) :=
                (traceNorm_two_smul _).symm
        _ = QITBench.OneShot.traceNorm
              (Xᴴ * Y + Yᴴ * X) := by rw [hdouble]
        _ ≤ QITBench.OneShot.traceNorm (Xᴴ * Y) +
              QITBench.OneShot.traceNorm (Yᴴ * X) :=
                traceNorm_add_le _ _
        _ ≤ Real.sqrt (frobeniusSq X) * Real.sqrt (frobeniusSq Y) +
              Real.sqrt (frobeniusSq Y) * Real.sqrt (frobeniusSq X) :=
                add_le_add hxy hyx
        _ = 2 * (Real.sqrt (frobeniusSq X) *
              Real.sqrt (frobeniusSq Y)) := by ring
    linarith
  have hXnonneg : 0 ≤ 2 - 2 * F := by
    rw [← hfsX]
    exact frobeniusSq_nonneg X
  have hYnonneg : 0 ≤ 2 + 2 * F := by
    rw [← hfsY]
    exact frobeniusSq_nonneg Y
  have hradicand : 0 ≤ 1 - F ^ 2 := by
    nlinarith [mul_nonneg hXnonneg hYnonneg]
  have hsqrt_product :
      (1 / 2 : ℝ) * Real.sqrt (frobeniusSq X) *
          Real.sqrt (frobeniusSq Y) =
        Real.sqrt (1 - F ^ 2) := by
    rw [hfsX, hfsY]
    calc
      (1 / 2 : ℝ) * Real.sqrt (2 - 2 * F) *
          Real.sqrt (2 + 2 * F) =
          (1 / 2 : ℝ) *
            (Real.sqrt (2 - 2 * F) * Real.sqrt (2 + 2 * F)) := by ring
      _ = (1 / 2 : ℝ) *
            Real.sqrt ((2 - 2 * F) * (2 + 2 * F)) := by
              rw [Real.sqrt_mul hXnonneg]
      _ = (1 / 2 : ℝ) * Real.sqrt (4 * (1 - F ^ 2)) := by ring
      _ = (1 / 2 : ℝ) *
            (Real.sqrt 4 * Real.sqrt (1 - F ^ 2)) := by
              rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      _ = Real.sqrt (1 - F ^ 2) := by
            rw [show Real.sqrt 4 = 2 by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
                Real.sqrt_sq_eq_abs]
              norm_num]
            ring
  calc
    traceDistance rho sigma =
        (1 / 2 : ℝ) *
          QITBench.OneShot.traceNorm (rho.matrix - sigma.matrix) := rfl
    _ ≤ (1 / 2 : ℝ) *
          (Real.sqrt (frobeniusSq X) * Real.sqrt (frobeniusSq Y)) := by
            exact mul_le_mul_of_nonneg_left hnorm (by norm_num)
    _ = Real.sqrt (1 - F ^ 2) := by
          rw [← hsqrt_product]
          ring
    _ = Real.sqrt
        (1 -
          (QITBench.OneShot.quantumFidelity rho.matrix sigma.matrix) ^ 2) := rfl
```

### context `traceDistance`: [`lean-qit-qlg/QIT/lean/problem_qit_NormFidelityAndContinuityTools_FuchsVanDeGraafInequalities.lean` lines 23-25](https://github.com/humanfia/hoa-qed/blob/1c918ec9a96c7751ce9c283304e1aebd7ffb19a3/lean-qit-qlg/QIT/lean/problem_qit_NormFidelityAndContinuityTools_FuchsVanDeGraafInequalities.lean#L23-L25) ([local copy](code/lean-qit-qlg/QIT/lean/problem_qit_NormFidelityAndContinuityTools_FuchsVanDeGraafInequalities.lean))

```lean
/-- The trace distance `D(ρ, σ) = (1 / 2) ‖ρ - σ‖₁` between density states. -/
noncomputable def traceDistance (rho sigma : State d) : ℝ :=
  (1 / 2 : ℝ) * QITBench.OneShot.traceNorm (rho.matrix - sigma.matrix)
```

How the parts fit. The parent `fuchsVanDeGraafInequalities` is a conjunction
of two inequalities, closed by `exact ⟨fuchsVanDeGraaf_lower rho sigma,
fuchsVanDeGraaf_upper rho sigma⟩` (line 796). The lower bound `1 − F ≤ D` is
the child `fuchsVanDeGraaf_lower`; the upper bound `D ≤ √(1 − F²)` is the child
`fuchsVanDeGraaf_upper`. Each child is a `private theorem` in the same file and
closes on its own; no `sorry`, `admit` or `axiom` appears anywhere in the file.

Lemma graph (who uses whom, in text):

```text
fuchsVanDeGraafInequalities (790-796)     -- the conjunction, closed by ⟨lower, upper⟩
├── fuchsVanDeGraaf_lower (467-590)       -- 1 − F ≤ D
└── fuchsVanDeGraaf_upper (615-787)       -- D ≤ √(1 − F²)
```

The two children are good leaves in the sense that each is a self-contained
statement whose proof closes on its own from a stack of `private` lemmas
earlier in the file: the SVD / trace-norm / frobenius infrastructure
(`exists_svd_sqrt_eigenvalues`, `traceNorm_eq_max_re_trace_unitary`,
`traceNorm_conjTranspose_mul_le`, the `positiveSupport` and `frobeniusSq`
lemmas) is factored out first, and each side assembles it. The longest chain
of project lemmas below the main theorem is

```text
fuchsVanDeGraafInequalities → fuchsVanDeGraaf_upper → traceNorm_conjTranspose_mul_le
  → traceNorm_eq_max_re_trace_unitary → exists_svd_sqrt_eigenvalues → inner_mulVec_eq
```

traced through the citations at lines 796, 719, 422, 287 and 64; `inner_mulVec_eq`
is a leaf that closes by a single `rw` chain (lines 32-37).

The lower bound reduces the goal to `hmain : 1 − re((S·R).trace) ≤ re((Δ⁺).trace)`
and `htrace_le_fidelity`, then closes by `rw [← hposPart_eq_distance]; linarith`
(line 590). The upper bound chases `traceDistance` through a `calc` chain into
the frobenius norms of `X := R − C` and `Y := R + C`, closing with `linarith`
(line 743) and `rfl` (line 787).

## Why it is good

1. The parent is a real declaration, not a goal inside a larger proof
   (`check`, `declared(fuchsVanDeGraafInequalities, …, 790-796)`).
2. The file closes with no `sorry`, `admit` or `axiom` (`check`,
   `no_sorry(…, 1-800)`).
3. The glue cites the lower bound (`check`, `cites(parent,
   fuchsVanDeGraaf_lower)`); strict validation also checks the upper bound.
4. The shape is small on top and deep below: 2 direct lemmas, a 7-line glue
   (790-796), child sites of 124 and 173 lines, and a depth-5 chain of project
   lemmas (`measurement`).
5. The authors state the intent in the module doc comment: "This file states
   the two-sided comparison between trace distance and unsquared quantum
   fidelity for finite-dimensional density states." (lines 7-8,
   `author-statement`).

In my opinion the move is worth recording because it is the theorem-scale
shape AutoDecompose must produce — one hole per bounded prover — but with a
subtlety the `iff-split` vocabulary does not capture: the two children are
*not* the two directions of one relation (`a ≤ b` and `b ≤ a`) but two
*different* functions of the fidelity, `1 − F` and `√(1 − F²)`, so the move is
a genuine two-sided bound rather than an antisymmetry.

## When to use it, and when not

Use it when a headline result is a two-sided bound `P ≤ x ∧ x ≤ Q` whose two
sides are genuinely different expressions with independent, self-contained
proofs, so the conjunction is closed by one `exact ⟨lower, upper⟩`. Avoid it
when the two sides share a substantial argument that is not first lifted into
a private lemma (here the SVD / trace-norm / frobenius infrastructure is
factored out first), when only one side is nontrivial and the other follows by
a one-liner such as `linarith`, or when the statement is a single inequality
rather than a pair.

## Consequences

The move creates exactly two obligations — the lower bound and the upper
bound — and no side conditions or exhaustiveness obligations of its own. The
cost is that the two children are large (124 and 173 lines) and each carries a
full matrix-norm development, so the shared infrastructure must be lifted into
private lemmas first. A failure mode: if the two bounds need the same
intermediate fact and it is not lifted into a shared private lemma, that
argument is duplicated across the two children.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/lean.yml (on push to main, pull_request, workflow_dispatch) builds the 'qit' project at lean-qit-qlg/QIT/lean-project with lean-action v1.6.1; QITFormalized.lean (a lakefile defaultTarget) imports QITFormalized.problem_qit_NormFidelityAndContinuityTools_FuchsVanDeGraafInequalities, which is byte-identical (32276 bytes) to the entry file lean-qit-qlg/QIT/lean/problem_qit_NormFidelityAndContinuityTools_FuchsVanDeGraafInequalities.lean; pinned commit 1c918ec9a96c7751ce9c283304e1aebd7ffb19a3 is head of default branch main | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: fuchsVanDeGraaf_lower@lean-qit-qlg/QIT/lean/problem_qit_NormFidelityAndContinuityTools_FuchsVanDeGraafInequalities.lean:796, fuchsVanDeGraaf_upper@lean-qit-qlg/QIT/lean/problem_qit_NormFidelityAndContinuityTools_FuchsVanDeGraafInequalities.lean:796; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 1c918ec9a96c7751ce9c283304e1aebd7ffb19a3 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(fuchsVanDeGraafInequalities, lean-qit-qlg/QIT/lean/problem_qit_NormFidelityAndContinuityTools_FuchsVanDeGraafInequalities.lean, 790-796) -> declared: fuchsVanDeGraafInequalities is declared at lean-qit-qlg/QIT/lean/problem_qit_NormFidelityAndContinuityTools_FuchsVanDeGraafInequalities.lean:790 | check_claims.py |
| 2 | verified | no_sorry(lean-qit-qlg/QIT/lean/problem_qit_NormFidelityAndContinuityTools_FuchsVanDeGraafInequalities.lean, 1-800) -> no_sorry: none of sorry, admit, axiom in lean-qit-qlg/QIT/lean/problem_qit_NormFidelityAndContinuityTools_FuchsVanDeGraafInequalities.lean:1-800 | check_claims.py |
| 3 | verified | cites(parent, fuchsVanDeGraaf_lower) -> cites: fuchsVanDeGraaf_lower occurs at lean-qit-qlg/QIT/lean/problem_qit_NormFidelityAndContinuityTools_FuchsVanDeGraafInequalities.lean:796 | check_claims.py |
| 4 | verified | line 796: exact ⟨fuchsVanDeGraaf_lower rho sigma, fuchsVanDeGraaf_upper rho sigma⟩ (2 direct lemmas, glue 790-796 = 7 lines); child sites 467-590 = 124 lines, 615-787 = 173 lines; chain edges all located: fuchsVanDeGraaf_upper (decl at 615, spans 615-787) cites traceNorm_conjTranspose_mul_le at 719; traceNorm_conjTranspose_mul_le (decl 417) cites traceNorm_eq_max_re_trace_unitary at 422; traceNorm_eq_max_re_trace_unitary (decl 275) cites exists_svd_sqrt_eigenvalues at 287; exists_svd_sqrt_eigenvalues (decl 41) cites inner_mulVec_eq at 64 (decl 32) -> depth 5 | verifier |
| 5 | verified | module doc comment lines 7-8 read verbatim: 'This file states the two-sided comparison between trace distance and' / 'unsquared quantum fidelity for finite-dimensional density states.' | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent fuchsVanDeGraafInequalities (790-796) is a conjunction of 1-F<=D and D<=sqrt(1-F^2), closed by exact <fuchsVanDeGraaf_lower, fuchsVanDeGraaf_upper> (line 796), citing exactly those two children and nothing else; child statements and sites match (lower decl 467-469 closes at 590 with rw [<-hposPart_eq_distance]; linarith; upper decl 615-618 closes via calc 775-787 with linarith at 743 and rfl at 787); no sorry/admit/axiom (sorry-scan pass, file is 800 lines); shape numbers correct: glue 790-796=7 lines, child sites 467-590=124 and 615-787=173 lines, direct_lemmas=2, depth-5 chain fuchsVanDeGraaf_upper->traceNorm_conjTranspose_mul_le(719)->traceNorm_eq_max_re_trace_unitary(422)->exists_svd_sqrt_eigenvalues(287)->inner_mulVec_eq(64) all located. Decomposition closes as stated. | reviewer-correctness |
| generality | accept | Move stated generically: applicability.goal_shape/use_when/avoid_when parameterise over P<=x<=Q with two different functions of a shared parameter, and the README explicitly distinguishes it from iff-split/antisymmetry. avoid_when is specific (shared argument not lifted, one side trivial, single inequality) and consequences are honest (exactly two obligations, cost of two large 124/173-line children, duplication failure mode). Good-leaf rationale is present: each child is a self-contained statement closing from factored private lemmas; depth-5 chain verified at cited lines 64/287/422/719. | reviewer-generality |
| provenance-licence | accept | provenance pass (file byte-identical at 1c918ec9a96c7751ce9c283304e1aebd7ffb19a3); commit identical across entry.json, source.json, SOURCE.md; permalinks cite that commit and the cited line ranges (7-8 doc comment, 23-25 traceDistance, 467-590 lower, 615-787 upper, 790-796 parent) all match the local copy; licence 'Apache-2.0 AND CC-BY-4.0' matches source.json/SOURCE.md and the copied upstream-LICENSE (Apache 2.0), upstream-LICENSE-CC-BY-4.0 (CC BY 4.0) and NOTICE (code Apache-2.0, prose CC-BY-4.0). All traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/humanfia/hoa-qed at commit `1c918ec9a96c7751ce9c283304e1aebd7ffb19a3`, under `Apache-2.0`; see the [source note](../../sources/humanfia-hoa-qed/SOURCE.md) for the licence text and attribution. The copied file lies in `lean-qit-qlg/QIT/`, which the source's NOTICE lists as third-party material from QuAIR's Lean-QIT-Bench under Apache 2.0 (Copyright 2026 QuAIR; its `LICENSE` is copied into the source note).
