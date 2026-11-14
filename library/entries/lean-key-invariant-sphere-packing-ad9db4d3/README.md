# The ratio F/G as key invariant for the F-G inequality on the imaginary axis

| | |
|---|---|
| Kind | instance |
| Move | key-invariant |
| Language | lean |
| Status | accepted |
| Source | [sphere-packing](../../sources/sphere-packing/SOURCE.md) at `efe3bbbc1ece` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T11:05:48Z |

## Intent

Reduce the inequality `F(it) − 18π⁻² G(it) < 0` to the behaviour of one
quantity, the ratio `Q(t) = F(it)/G(it)`: `Q` is strictly antitone on `(0,∞)`
with right limit `18π⁻²` at `0`, so `Q(t) < 18π⁻²`, and positivity of `G` turns
this ratio bound into the additive inequality.

## The decomposition

### parent `FG_inequality_2`: [`SpherePacking/ModularForms/FG.lean` lines 541-548](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/ModularForms/FG.lean#L541-L548) ([local copy](code/SpherePacking/ModularForms/FG.lean))

```lean
theorem FG_inequality_2 {t : ℝ} (ht : 0 < t) :
    FReal t - 18 * (π ^ (-2 : ℤ)) * GReal t < 0 := by
  have hlt : FmodGReal t < 18 * (π ^ (-2 : ℤ)) :=
    (FmodG_strictAntiOn (half_pos ht) ht (half_lt_self ht)).trans_le <|
      ge_of_tendsto FmodG_rightLimitAt_zero <| by
        filter_upwards [Ioo_mem_nhdsGT (half_pos ht)] with s hs
        exact (FmodG_strictAntiOn hs.1 (half_pos ht) hs.2).le
  exact sub_neg.mpr ((div_lt_iff₀ (G_imag_axis_pos.2 t ht)).mp hlt)
```

### child `FmodG_strictAntiOn`: [`SpherePacking/ModularForms/FG.lean` lines 408-411](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/ModularForms/FG.lean#L408-L411) ([local copy](code/SpherePacking/ModularForms/FG.lean))

```lean
/-- **Proposition 8.12**: `FmodGReal` is strictly decreasing on `(0, ∞)`. -/
theorem FmodG_strictAntiOn : StrictAntiOn FmodGReal (Set.Ioi 0) :=
  strictAntiOn_of_deriv_neg (convex_Ioi 0) FmodGReal_differentiableOn.continuousOn fun t ht ↦
    deriv_FmodGReal_neg t (by rwa [interior_Ioi] at ht)
```

### child `FmodG_rightLimitAt_zero`: [`SpherePacking/ModularForms/FG.lean` lines 518-527](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/ModularForms/FG.lean#L518-L527) ([local copy](code/SpherePacking/ModularForms/FG.lean))

```lean
/-- `lim_{t → 0⁺} F(it) / G(it) = 18 π⁻²` (blueprint Lemma 8.8). -/
theorem FmodG_rightLimitAt_zero :
    Tendsto FmodGReal (nhdsWithin 0 (Set.Ioi 0)) (nhds (18 * (π ^ (-2 : ℤ)))) := by
  have hlim : Tendsto (fun s : ℝ ↦ FmodGReal (1 / s)) atTop (nhds (18 * π ^ (-2 : ℤ))) := by
    rw [show (18 : ℝ) * π ^ (-2 : ℤ) = 36 * π ^ (-2 : ℤ) / 2 by ring]
    refine (FmodG_numerator_tendsto.div FmodG_denominator_tendsto two_ne_zero).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    rw [FmodGReal, F_functional_eq_real hs, G_functional_eq_real hs, mul_assoc (s ^ 10)]
    exact (mul_div_mul_left _ _ (pow_ne_zero 10 hs.ne')).symm
  exact (hlim.comp tendsto_inv_nhdsGT_zero).congr fun t ↦ by simp
```

### child `G_imag_axis_pos`: [`SpherePacking/ModularForms/FG.lean` lines 205-207](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/ModularForms/FG.lean#L205-L207) ([local copy](code/SpherePacking/ModularForms/FG.lean))

```lean
/-- `G(it) > 0` for all `t > 0` (blueprint Lemma 8.6): all factors of `G` are positive there. -/
@[fun_prop]
theorem G_imag_axis_pos : ResToImagAxis.Pos G := by unfold G; fun_prop (disch := positivity)
```

### context `cor:ineqBnew`: [`blueprint/src/subsections/modform-ineq.tex` lines 223-231](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/blueprint/src/subsections/modform-ineq.tex#L223-L231) ([local copy](code/blueprint/src/subsections/modform-ineq.tex))

```latex
\begin{corollary}\label{cor:ineqBnew}\uses{lemma:Qlim, prop:Qdec, lemma:F-G-pos}\lean{FG_inequality_2}\leanok
\eqref{eqn:ineqBnew} holds.
\end{corollary}
\begin{proof}\leanok
\begin{equation}
    \frac{F(it)}{G(it)} = Q(t) < \lim_{u \to 0^+} Q(u) = \frac{18}{\pi^2}
\end{equation}
and by Lemma \ref{lemma:F-G-pos}, \eqref{eqn:ineqBnew} follows.
\end{proof}
```

### How the parts fit

The parent `FG_inequality_2` proves `F(it) − 18π⁻² G(it) < 0` by introducing one
quantity — the ratio `Q(t) = FmodGReal t = F(it)/G(it)` — and reducing the whole
inequality to two facts about that ratio plus one fact about `G`:

1. `FmodG_strictAntiOn` says `Q` is strictly antitone on `(0,∞)`, so in
   particular `Q(t) < Q(t/2)`. That is the first step of the glue,
   `(FmodG_strictAntiOn (half_pos ht) ht (half_lt_self ht)).trans_le` (line 544).
2. `FmodG_rightLimitAt_zero` says the right limit of `Q` at `0` is `18π⁻²`;
   combined with antitonicity it gives `Q(t/2) ≤ 18π⁻²` (the
   `ge_of_tendsto FmodG_rightLimitAt_zero` block, lines 545-547), hence
   `Q(t) < 18π⁻²`.
3. `G_imag_axis_pos` says `G(it) > 0`, which lets the glue cross-multiply the
   ratio bound `Q(t) < 18π⁻²` into `F(it) < 18π⁻² G(it)` and then into the
   additive form `F(it) − 18π⁻² G(it) < 0` (`div_lt_iff₀ (G_imag_axis_pos.2 t ht)`,
   line 548).

The lemma graph (each arrow reads "is cited in the proof of"), down to the
deepest branch the entry checks:

```
FG_inequality_2
├── FmodG_strictAntiOn ── deriv_FmodGReal_neg ── L₁₀_pos ── L₁₀_eventually_pos_imag_axis
│        ── L₁₀_div_FG_tendsto ── D_F_div_F_tendsto ── F_vanishing_order
│        ── E₂E₄_sub_E₆_div_q_tendsto ── qexp_tendsto_of_poly_bound
├── FmodG_rightLimitAt_zero ── FmodG_numerator_tendsto, FmodG_denominator_tendsto,
│        F_functional_eq_real, G_functional_eq_real
└── G_imag_axis_pos
```

The longest chain of project lemmas below the main theorem is 9: `FG_inequality_2`
→ `FmodG_strictAntiOn` (L544) → `deriv_FmodGReal_neg` (L411) → `L₁₀_pos` (L403) →
`L₁₀_eventually_pos_imag_axis` (L372) → `L₁₀_div_FG_tendsto` (L362) →
`D_F_div_F_tendsto` (L354) → `F_vanishing_order` (L323) →
`E₂E₄_sub_E₆_div_q_tendsto` (L318) → `qexp_tendsto_of_poly_bound` (L313), which stops
at an imported lemma (`QExp.tendsto_nat`).

Each of the three children is a good leaf — a self-contained statement whose proof
closes on its own or from named siblings:

- `FmodG_strictAntiOn` is a self-contained statement ("the ratio is strictly
  antitone on `(0,∞)`") closed in three lines by the derivative test
  `strictAntiOn_of_deriv_neg`, appealing only to two named siblings
  (`FmodGReal_differentiableOn`, `deriv_FmodGReal_neg`).
- `FmodG_rightLimitAt_zero` is self-contained ("the right limit of the ratio at 0
  is `18π⁻²`"); its proof divides two named sibling limits
  (`FmodG_numerator_tendsto`, `FmodG_denominator_tendsto`) after rewriting through
  the real functional equations `F_functional_eq_real` and `G_functional_eq_real`.
- `G_imag_axis_pos` closes outright by automation (`unfold G; fun_prop
  (disch := positivity)`), citing no further lemma.

The context excerpt is the blueprint node `cor:ineqBnew`, the authors' own record of
this decomposition: it `\uses{lemma:Qlim, prop:Qdec, lemma:F-G-pos}` — the same three
lemmas, mapped to the Lean targets `FmodG_rightLimitAt_zero`, `FmodG_strictAntiOn`,
`G_imag_axis_pos`.

## Why it is good

1. `FG_inequality_2` is a real declaration in `FG.lean` (check; [permalink](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/ModularForms/FG.lean#L541-L548)).
2. The whole file closes with no `sorry`, `admit` or `axiom` (check; [permalink](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/ModularForms/FG.lean)).
3. The glue — the parent proof — is 8 lines long (check; [permalink](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/ModularForms/FG.lean#L541-L548)).
4. The theorem-scale shape is 3 direct lemmas, an 8-line glue, children of 4/10/3
   lines, and a longest chain of 9 project lemmas below the main theorem
   (measurement; counted as site spans in `FG.lean`, the chain traced above).
5. The authors state this exact decomposition in the blueprint: the node
   `cor:ineqBnew` `\uses{lemma:Qlim, prop:Qdec, lemma:F-G-pos}` and its proof reads
   "Q(t) < lim_{u→0⁺} Q(u) = 18/π² … and by Lemma F-G-pos, ineqBnew follows"
   (author-statement; [permalink](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/blueprint/src/subsections/modform-ineq.tex#L223-L231)).

In my opinion the worth of this entry is that the *idea* is exactly one quantity —
the ratio `Q = F/G` — and the decomposition is the natural split of that idea into
"monotone", "has a limit", "denominator positive". The glue that reassembles them is
short and obvious, while the lemmas are each a natural bounded task: one for the
derivative sign of `Q` (via the Wronskian `L₁₀`), one for the endpoint limit (via the
modular functional equations), one for the sign of `G`. This is the shape AutoDecompose
should emit — a skeleton with one hole per fact about the invariant — and it is unusual
that a real research project states the decomposition twice (once in the blueprint,
once in Lean) so the intent is independently checkable.

## When to use it, and when not

Use it when an inequality `A(t) < c·B(t)` between two positive functions on a ray
can be rephrased as a bound on their ratio `A/B`, and that ratio has a monotonicity
and a computable one-sided limit at an endpoint. The three obligations — monotone,
limit, denominator sign — should each be a separate named lemma, since each closes
differently (derivative test, functional equation, positivity). This is the
`key-invariant` move: the ratio is the one quantity that carries the idea.

Avoid it when the ratio is not monotone, when the endpoint limit has no closed form,
or when the denominator changes sign (then `div_lt_iff₀` no longer applies and the
single ratio needs a case split). It is also the wrong move when the two sides have
the *same* sign and the inequality is a sum rather than a difference: the sibling
`FG_inequality_1` (`F + 18π⁻² G > 0`, lines 535-537 of the same file) needs only
positivity of the two terms and no ratio at all — the ratio invariant is forced by the
`−` sign, not by the positivity.

## Consequences

The move creates one obligation per fact about the ratio `Q`: strict monotonicity on
the ray, a computable one-sided limit at the endpoint, and positivity of the
denominator. The monotonicity and the limit are the real work — here they sink dozens
of lines each through the Wronskian `L₁₀` (for the derivative sign) and the modular
functional equations (for the limit) — while the glue that combines them is trivial.
Strictness is load-bearing: both the strict bound `Q(t) < 18π⁻²` and the strict
positivity `G(it) > 0` are needed, or the conclusion degrades to a non-strict `≤`. If
the denominator changed sign, the cross-multiplication `div_lt_iff₀` would not apply
and the single-ratio invariant would need a case split instead.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml builds the project via leanprover/lean-action and lake exe mk_all --check --module on push to main; commit efe3bbbc1ece548f4672a772b94d8f621c10fdda is on main | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: FmodG_strictAntiOn@SpherePacking/ModularForms/FG.lean:544, FmodG_rightLimitAt_zero@SpherePacking/ModularForms/FG.lean:545, G_imag_axis_pos@SpherePacking/ModularForms/FG.lean:548; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at efe3bbbc1ece548f4672a772b94d8f621c10fdda | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(FG_inequality_2, SpherePacking/ModularForms/FG.lean, 541-548) -> declared: FG_inequality_2 is declared at SpherePacking/ModularForms/FG.lean:541 | check_claims.py |
| 2 | verified | no_sorry(SpherePacking/ModularForms/FG.lean, 1-548) -> no_sorry: none of sorry, admit, axiom in SpherePacking/ModularForms/FG.lean:1-548 | check_claims.py |
| 3 | verified | lines(parent, 8) -> lines: site parent has 8 lines | check_claims.py |
| 4 | verified | Site spans checked directly in code: parent FG_inequality_2 L541-548 (8 lines), children FmodG_strictAntiOn L408-411 (4), FmodG_rightLimitAt_zero L518-527 (10), G_imag_axis_pos L205-207 (3) => 3 direct lemmas. Chain traced in code: FG_inequality_2 cites FmodG_strictAntiOn (L544) -> deriv_FmodGReal_neg (L411) -> L₁₀_pos -> L₁₀_eventually_pos_imag_axis -> L₁₀_div_FG_tendsto -> D_F_div_F_tendsto -> F_vanishing_order -> E₂E₄_sub_E₆_div_q_tendsto -> qexp_tendsto_of_poly_bound = 9 project lemmas below the main theorem | verifier |
| 5 | verified | Opened blueprint/src/subsections/modform-ineq.tex L223-231: node cor:ineqBnew has \uses{lemma:Qlim, prop:Qdec, lemma:F-G-pos} and proof reads F(it)/G(it) = Q(t) < lim_{u→0⁺} Q(u) = 18/π² and 'by Lemma F-G-pos ... ineqBnew follows' | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent FG_inequality_2 (FG.lean L541-548) cites exactly the three child project lemmas: FmodG_strictAntiOn (L544,547), FmodG_rightLimitAt_zero (L545), G_imag_axis_pos (L548); no other FG.lean lemma is cited, so children == lemmas the glue uses. Child statements in entry.json match the code verbatim (L409, L519-520, L207). Closing methods match: strictAntiOn_of_deriv_neg via FmodGReal_differentiableOn.continuousOn + deriv_FmodGReal_neg; FmodG_numerator_tendsto.div FmodG_denominator_tendsto via F_functional_eq_real/G_functional_eq_real; unfold G; fun_prop (disch:=positivity). Glue closes (ratio bound -> sub_neg via div_lt_iff₀). Shape numbers verified: direct_lemmas=3, glue_lines=8 (L541-548), child_lines=[4,10,3] (L408-411, L518-527, L205-207). Depth=9 chain traced link-by-link and each link confirmed: FG_inequality_2->FmodG_strictAntiOn(L544)->deriv_FmodGReal_neg(L411)->L10_pos(L403)->L10_eventually_pos_imag_axis(L362)->L10_div_FG_tendsto(L354)->D_F_div_F_tendsto(L323)->F_vanishing_order(L318)->E2E4_sub_E6_div_q_tendsto(L313)->qexp_tendsto_of_poly_bound(L286, private, ends at imported QExp.tendsto_nat). Blueprint context cor:ineqBnew matches verbatim. | reviewer-correctness |
| generality | accept | The move is stated generally (inequality A(t) < c·B(t) between functions on a ray, rephrased as a monotone ratio with a computable endpoint limit), not just as the F/G example. 'When not to use' is honest and specific: it lists non-monotone ratio, no closed-form limit, sign-changing denominator, and gives a concrete counterexample from the same file (FG_inequality_1 at L535-537, verified: it is a sum F + 18π⁻² G > 0 closed by add_pos with no ratio, confirming the ratio invariant is forced by the − sign). Consequences are specific and honest: strictness is load-bearing (else degrades to ≤), and a sign-changing denominator forces a case split. It does say what makes the leaves good for a bounded prover: each child is self-contained and closes on its own or via named siblings, one per fact about the invariant, each a natural bounded task (derivative test / functional equation / positivity automation). | reviewer-generality |
| provenance-licence | accept | Provenance and licence consistent and traceable: check_provenance passes (2 files byte-identical at efe3bbbc1ece548f4672a772b94d8f621c10fdda). source.json and SOURCE.md both pin commit efe3bbbc1ece548f4672a772b94d8f621c10fdda and licence Apache-2.0; entry.json source block matches; every permalink uses the same commit. upstream-LICENSE is Apache License 2.0. Cited line ranges match the copied files exactly: parent FG_inequality_2 L541-548, children FmodG_strictAntiOn L408-411, FmodG_rightLimitAt_zero L518-527, G_imag_axis_pos L205-207, context cor:ineqBnew L223-231. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean at commit `efe3bbbc1ece548f4672a772b94d8f621c10fdda`, under `Apache-2.0`; see the [source note](../../sources/sphere-packing/SOURCE.md) for the licence text and attribution.
