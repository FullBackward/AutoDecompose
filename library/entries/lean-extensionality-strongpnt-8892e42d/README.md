# Extensionality over the prime index for the zeta ratio identity

| | |
|---|---|
| Kind | instance |
| Move | extensionality |
| Language | lean |
| Status | accepted |
| Source | [strongpnt](../../sources/strongpnt/SOURCE.md) at `2f5835c32231` |
| Licence | `LicenseRef-unknown` |
| Licence recorded | 2026-11-14T09:19:34Z |

## Intent

The equality between the zeta ratio and its Euler product is proved by first
rewriting the left side into the same product shape as the right (via
`zeta_ratios`), then reducing the resulting product equality to a pointwise
equality over the prime index `p` (via `congr 1; ext p`), and closing the
single pointwise factor with the ratio identity at `z = p^{-s}`. The move of
interest is the pointwise reduction: the extensionality step turns one indexed
equation into one goal per index, and that goal is a named lemma.

## The decomposition

### parent `zeta_ratio_identity`: [`StrongPNT/PNT3_RiemannZeta.lean` lines 264-269](https://github.com/math-inc/strongpnt/blob/2f5835c322314f55f1026ec2f139d704b7c45c69/StrongPNT/PNT3_RiemannZeta.lean#L264-L269) ([local copy](code/StrongPNT/PNT3_RiemannZeta.lean))

```lean
theorem zeta_ratio_identity (s : ℂ) (hs : 1 < s.re) : riemannZeta (2 * s) / riemannZeta s = ∏' p : ℙ, (1 + ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹ := by
  rw [zeta_ratios s hs]; congr 1; ext p
  have hp : ((p : ℕ) : ℂ) ≠ 0 := by rw [ne_eq, Nat.cast_eq_zero]; exact Nat.Prime.ne_zero p.2
  have h1 : ((p : ℕ) : ℂ) ^ (-(2 * s)) = (((p : ℕ) : ℂ) ^ (-s))^2 := complex_cpow_neg_two_mul ((p : ℕ) : ℂ) s hp
  have h2 : norm (((p : ℕ) : ℂ) ^ (-s)) < 1 := p_s_abs_1 p s hs
  rw [h1]; exact ratio_invs (((p : ℕ) : ℂ) ^ (-s)) h2
```

### child `zeta_ratios`: [`StrongPNT/PNT3_RiemannZeta.lean` lines 225-228](https://github.com/math-inc/strongpnt/blob/2f5835c322314f55f1026ec2f139d704b7c45c69/StrongPNT/PNT3_RiemannZeta.lean#L225-L228) ([local copy](code/StrongPNT/PNT3_RiemannZeta.lean))

```lean
lemma zeta_ratios (s : ℂ) (hs : 1 < s.re) : riemannZeta (2 * s) / riemannZeta s = ∏' p : ℙ, ((1 - ((p : ℕ) : ℂ) ^ (-(2 * s) : ℂ))⁻¹ / (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) := by
  have h1 := zeta_ratio_prod s hs
  have h2 := simplify_prod_ratio s hs
  exact h1.trans h2
```

### child `complex_cpow_neg_two_mul`: [`StrongPNT/PNT3_RiemannZeta.lean` lines 258-262](https://github.com/math-inc/strongpnt/blob/2f5835c322314f55f1026ec2f139d704b7c45c69/StrongPNT/PNT3_RiemannZeta.lean#L258-L262) ([local copy](code/StrongPNT/PNT3_RiemannZeta.lean))

```lean
lemma complex_cpow_neg_two_mul (z w : ℂ) (hz : z ≠ 0) : z^(-(2*w)) = (z^(-w))^2 := by
  have h1 : -(2*w) = 2*(-w) := by ring
  rw [h1]
  have h2 : (2 : ℂ)*(-w) = ((2 : ℕ) : ℂ)*(-w) := by norm_cast
  rw [h2, Complex.cpow_nat_mul]
```

### child `p_s_abs_1`: [`StrongPNT/PNT3_RiemannZeta.lean` lines 7-27](https://github.com/math-inc/strongpnt/blob/2f5835c322314f55f1026ec2f139d704b7c45c69/StrongPNT/PNT3_RiemannZeta.lean#L7-L27) ([local copy](code/StrongPNT/PNT3_RiemannZeta.lean))

```lean
lemma p_s_abs_1 (p : ℙ) (s : ℂ) (hs : 1 < s.re) : norm (((p : ℕ) : ℂ) ^ (-s : ℂ)) < 1 := by
  -- p ≥ 2 ⇒ (p : ℝ) > 1
  have hx1 : 1 < ((p : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by
      exact_mod_cast (p.2.two_le : 2 ≤ (p : ℕ))
    exact lt_of_lt_of_le one_lt_two h2
  have hx0 : 0 < ((p : ℕ) : ℝ) := lt_trans zero_lt_one hx1
  -- compute the norm via the cpow formula for positive real bases
  have hnorm_eq : ‖(((p : ℕ) : ℂ) ^ (-s : ℂ))‖ = ((p : ℕ) : ℝ) ^ ((-s : ℂ).re) := by
    simpa using (Complex.norm_cpow_eq_rpow_re_of_pos hx0 (-s : ℂ))
  -- the exponent is negative since Re s > 1 > 0
  have hz : ((-s : ℂ).re) < 0 := by
    have h0 : 0 < s.re := lt_trans zero_lt_one hs
    have : -s.re < 0 := neg_lt_zero.mpr h0
    simpa using this
  -- apply the real inequality x^z < 1 when x > 1 and z < 0
  have hlt : ((p : ℕ) : ℝ) ^ ((-s : ℂ).re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hx1 hz
  -- conclude for the complex absolute value (norm)
  have : ‖(((p : ℕ) : ℂ) ^ (-s : ℂ))‖ < 1 := by simpa [hnorm_eq] using hlt
  simpa [norm] using this
```

### child `ratio_invs`: [`StrongPNT/PNT3_RiemannZeta.lean` lines 251-254](https://github.com/math-inc/strongpnt/blob/2f5835c322314f55f1026ec2f139d704b7c45c69/StrongPNT/PNT3_RiemannZeta.lean#L251-L254) ([local copy](code/StrongPNT/PNT3_RiemannZeta.lean))

```lean
lemma ratio_invs (z : ℂ) (hz : norm z < 1) : (1 - z^2)⁻¹ / (1 - z)⁻¹ = (1 + z)⁻¹ := by
  have hz1 : 1 - z ≠ 0 := one_sub_ne_zero_of_abs_lt_one z hz
  simpa [diff_of_squares z] using
    inv_mul_div_cancel_right_of_ne_zero (1 - z) (1 + z) hz1
```

### context `zeta_ratio_identity_node`: [`blueprint/src/PNT/PNT3_RiemannZeta.tex` lines 227-236](https://github.com/math-inc/strongpnt/blob/2f5835c322314f55f1026ec2f139d704b7c45c69/blueprint/src/PNT/PNT3_RiemannZeta.tex#L227-L236) ([local copy](code/blueprint/src/PNT/PNT3_RiemannZeta.tex))

```latex
\begin{theorem}[Ratio identity]\label{thm:zeta_ratio_identity} \lean{zeta_ratio_identity}
\leanok
\uses{def:NatPrimes}
For $s\in\C$ with $\Re(s)>1$, we have $\frac{\zeta(2s)}{\zeta(s)} = \prod'_{p\in\mathcal{P}}(1+p^{-s})^{-1}$.
\end{theorem}
\begin{proof}
\leanok
\uses{lem:zeta_ratios, lem:ratio_invs, lem:p_s_abs_1}
Apply Lemma \ref{lem:zeta_ratios} and Lemma \ref{lem:ratio_invs} with $z=p^{-s}$. We verify condition using \cref{lem:p_s_abs_1}.
\end{proof}
```

**How the parts fit.** The glue is the six-line proof of `zeta_ratio_identity`
(lines 264-269). Its first step, `rw [zeta_ratios s hs]`, replaces the left side
`riemannZeta (2 * s) / riemannZeta s` by the product of ratios
`∏' p, (1 - p^{-2s})^{-1} / (1 - p^{-s})^{-1}`, so the two sides are products
over the same index `ℙ` and differ only inside the product. `congr 1; ext p`
then turns the product equality into the single pointwise goal
`(1 - p^{-2s})^{-1} / (1 - p^{-s})^{-1} = (1 + p^{-s})^{-1}` for an arbitrary
prime `p`. That pointwise goal is closed by three named lemmas:
`complex_cpow_neg_two_mul` rewrites `p^{-2s}` to `(p^{-s})^2`, `p_s_abs_1`
gives `norm (p^{-s}) < 1`, and `ratio_invs` (applied at `z = p^{-s}`) closes it.

Lemma graph, project lemmas only (mathlib leaves named):

```text
zeta_ratio_identity
├── zeta_ratios ── zeta_ratio_prod
│               └─ simplify_prod_ratio ── prod_of_ratios ── prod_of_ratios_simplified ── lift_multipliable_of_nonzero
├── complex_cpow_neg_two_mul ── Complex.cpow_nat_mul
├── p_s_abs_1 ── Complex.norm_cpow_eq_rpow_re_of_pos, Real.rpow_lt_one_of_one_lt_of_neg
└── ratio_invs ── one_sub_ne_zero_of_abs_lt_one, diff_of_squares, inv_mul_div_cancel_right_of_ne_zero
```

Why each child is a good leaf:

- `zeta_ratios` is a one-line interface lemma (`h1.trans h2`) closing on two
  sibling lemmas already in the file; it packages the Euler-product
  manipulation so the parent does not re-derive it.
- `complex_cpow_neg_two_mul` is a self-contained bookkeeping identity
  (`z^{-2w} = (z^{-w})^2`) closed by `ring`, `norm_cast` and
  `Complex.cpow_nat_mul`; it is the one technical step the blueprint omits.
- `p_s_abs_1` is a self-contained analytic bound (`|p^{-s}| < 1`) from two
  mathlib facts; it supplies exactly the hypothesis `ratio_invs` needs.
- `ratio_invs` is the actual algebra identity, stated for a general `z` with
  `norm z < 1`; it closes on three tiny sibling lemmas in the same file.

## Why it is good

1. (check) The parent `zeta_ratio_identity` is declared at lines 264-269 of
   `StrongPNT/PNT3_RiemannZeta.lean` (form `declared`).
2. (check) The parent's proof, lines 264-269, contains no `sorry`, `admit` or
   `axiom` (form `no_sorry`).
3. (measurement) The theorem-scale shape is 4 direct lemmas, a 6-line glue,
   child proofs of 4/5/21/4 lines and depth 5 (the chain
   `zeta_ratios` → `simplify_prod_ratio` → `prod_of_ratios` →
   `prod_of_ratios_simplified` → `lift_multipliable_of_nonzero`).
4. (author-statement) The blueprint's proof of the same theorem cites the same
   lemmas the glue uses, at `blueprint/src/PNT/PNT3_RiemannZeta.tex` lines
   234-235.
5. (known-use) The same `congr 1; ext p` reduction proves `abs_zeta_prod_prime`
   in the same file, lines 65-66.

In my opinion the detail worth copying is the pairing of `congr 1` with
`ext p`: the rewrite (`zeta_ratios`) first forces the two sides into one
product, and only then does the pointwise split produce a goal that is exactly
a named lemma.

## When to use it, and when not

Use it when an equation's two sides are (or can be rewritten to) the same
indexed product or the same function, differing only inside the index, and
when the pointwise factor has a self-contained named lemma in the index
variable. It is especially apt when the product's convergence/multipliability
has already been handled elsewhere (here by `zeta_ratios`), so the
extensionality step only needs the pointwise algebra.

Avoid it when the two products are over different index types or carry
different weights (so `ext` does not apply), or when the pointwise factor is
not itself a named lemma and would need a further split per index. It also does
not help when the two sides differ in the index set itself rather than in the
terms.

## Consequences

The move creates one pointwise goal per index element (here a single `p`,
bound by `ext`). It relies on a prior rewrite putting both sides into the same
product shape, and it only applies because both sides are products over the
same index `ℙ`. If the pointwise factor does not close by one named lemma (as
`ratio_invs` does here), the per-index goal needs a further split and the move
does not help with that. The blueprint omits `complex_cpow_neg_two_mul`, a
Lean-only bookkeeping step, so the published structure has 3 leaves where the
Lean glue has 4.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/blueprint.yml (leanprover/lean-action@v1.2.0 builds the project); pinned commit 2f5835c322314f55f1026ec2f139d704b7c45c69 is on default branch main | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: zeta_ratios@StrongPNT/PNT3_RiemannZeta.lean:265, complex_cpow_neg_two_mul@StrongPNT/PNT3_RiemannZeta.lean:267, p_s_abs_1@StrongPNT/PNT3_RiemannZeta.lean:268, ratio_invs@StrongPNT/PNT3_RiemannZeta.lean:269; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at 2f5835c322314f55f1026ec2f139d704b7c45c69 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(zeta_ratio_identity, StrongPNT/PNT3_RiemannZeta.lean, 264-269) -> declared: zeta_ratio_identity is declared at StrongPNT/PNT3_RiemannZeta.lean:264 | check_claims.py |
| 2 | verified | no_sorry(StrongPNT/PNT3_RiemannZeta.lean, 264-269) -> no_sorry: none of sorry, admit, axiom in StrongPNT/PNT3_RiemannZeta.lean:264-269 | check_claims.py |
| 3 | verified | read parent site 264-269 (6 lines, 4 children cited: zeta_ratios@265, complex_cpow_neg_two_mul@267, p_s_abs_1@268, ratio_invs@269); child sites 225-228 (4), 258-262 (5), 7-27 (21), 251-254 (4); depth chain declarations all at stated lines: zeta_ratios@225 uses simplify_prod_ratio@189 uses prod_of_ratios@164 uses prod_of_ratios_simplified@131 uses lift_multipliable_of_nonzero@98 | verifier |
| 4 | verified | blueprint/src/PNT/PNT3_RiemannZeta.tex:234-235 contain exactly "\uses{lem:zeta_ratios, lem:ratio_invs, lem:p_s_abs_1}" and "Apply Lemma \ref{lem:zeta_ratios} and Lemma \ref{lem:ratio_invs} with z=p^{-s}. We verify condition using \cref{lem:p_s_abs_1}." | verifier |
| 5 | verified | StrongPNT/PNT3_RiemannZeta.lean:62-67, abs_zeta_prod_prime: 'congr 1' at line 65 then 'ext p' at line 66, the same pointwise reduction over the prime index | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Provenance pass (2 files byte-identical at 2f5835c). Parent zeta_ratio_identity is declared at 264-269 (6-line glue: rw [zeta_ratios]; congr 1; ext p; then close the pointwise goal) and closes with no sorry/admit/axiom. All four children are exactly the project lemmas the glue cites and their line ranges and statements match the code: zeta_ratios 225-228 (4 lines), complex_cpow_neg_two_mul 258-262 (5), p_s_abs_1 7-27 (21), ratio_invs 251-254 (4); closing methods match (h1.trans h2; ring/norm_cast/cpow_nat_mul; norm_cpow_eq_rpow_re_of_pos + rpow_lt_one_of_one_lt_of_neg; one_sub_ne_zero_of_abs_lt_one/diff_of_squares/inv_mul_div_cancel_right_of_ne_zero). Shape numbers correct: direct_lemmas 4, glue_lines 6, child_lines [4,5,21,4]; depth 5 confirmed by the real citation chain zeta_ratios(225)->simplify_prod_ratio(189)->prod_of_ratios(164)->prod_of_ratios_simplified(131)->lift_multipliable_of_nonzero(98). Blueprint (227-236) cites zeta_ratios/ratio_invs/p_s_abs_1 exactly as claimed; known-use abs_zeta_prod_prime uses congr 1/ext p at 65-66. Non-blocking note: claim 4 says the blueprint cites 'the same named lemmas the glue uses' but it omits complex_cpow_neg_two_mul (a Lean-only step); this is already disclosed in README Consequences and does not affect the decomposition or shape. | reviewer-correctness |
| generality | accept | Move stated generally: applicability.goal_shape/use_when and README 'When to use' describe any equality reduced to pointwise (f p = g p) over a shared index, and also_known_as generalizes to funext/Set.ext/Finset.ext. 'When not to use' and consequences are honest and specific: different index types/weights, sides differing in the index set itself, and a pointwise factor that is not one named lemma are all real ext failure modes; consequences correctly note the dependency on the prior rewrite (zeta_ratios) and the same-index requirement, and that the blueprint has 3 leaves vs 4 in Lean (verified: blueprint \uses cites zeta_ratios,ratio_invs,p_s_abs_1 only, omitting complex_cpow_neg_two_mul). Good leaves for a bounded prover are described: each child is self-contained and closes by rw/simp/ring/exact with no induction/case split (verified in lines 225-228, 258-262, 7-27, 251-254), matching metrics children_closed_by_automation=4. Known-use claim 5 verified: abs_zeta_prod_prime at lines 63-66 uses rw; congr 1; ext p (same-file second instance, honestly described as same file). | reviewer-generality |
| provenance-licence | accept | check_provenance pass (2 files byte-identical at 2f5835c3); commit consistent across entry.json source.commit, all file/site permalinks, README and sources/strongpnt/SOURCE.md+source.json; licence LicenseRef-unknown consistent everywhere with source note 'no licence file found at the root' (confirmed: repo root listing has no LICENSE/COPYING); permalink line anchors verified against local code (parent 264-269, children 225-228/258-262/7-27/251-254, tex 227-236 all match); README source section points to ../../sources/strongpnt/SOURCE.md | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/math-inc/strongpnt at commit `2f5835c322314f55f1026ec2f139d704b7c45c69`, under `LicenseRef-unknown`; see the [source note](../../sources/strongpnt/SOURCE.md) for the licence text and attribution.
