# Three-step calc lower-bounding |ζ(3)/ζ(3/2)| by |ζ(3/2 + it)| via the Euler product

| | |
|---|---|
| Kind | instance |
| Move | calc-chain |
| Language | lean |
| Status | accepted |
| Source | [strongpnt](../../sources/strongpnt/SOURCE.md) at `2f5835c32231` |
| Licence | `LicenseRef-unknown` |

## Intent

Prove the lower bound `|ζ(3/2 + it)| ≥ |ζ(3)/ζ(3/2)|` on the critical line by
factoring it into a three-link `calc`: evaluate the ratio `ζ(3)/ζ(3/2)` as a
real Euler product, compare that product factorwise to the product of inverse
norms of the Euler factors at `3/2 + it`, then fold that product back into
`|ζ(3/2 + it)|`.

## The decomposition

### parent `zeta_lower_bound`: [`StrongPNT/PNT3_RiemannZeta.lean` lines 639-651](https://github.com/math-inc/strongpnt/blob/2f5835c322314f55f1026ec2f139d704b7c45c69/StrongPNT/PNT3_RiemannZeta.lean#L639-L651) ([local copy](code/StrongPNT/PNT3_RiemannZeta.lean))

```lean
theorem zeta_lower_bound (t : ℝ) :
  norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2)) ≤
    norm (riemannZeta (((3 : ℝ) / 2) + t * Complex.I)) := by
  have hs : 1 < (((3 : ℝ) / 2 : ℂ) + t * Complex.I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, mul_zero, add_zero]
    norm_num
  calc
    norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2))
        = ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := abs_zeta_ratio_eval
    _ ≤ ∏' p : ℙ, (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹ :=
          abs_zeta_inequality t
    _ = norm (riemannZeta (((3 : ℝ) / 2 : ℂ) + t * Complex.I)) := by
          simpa using (abs_zeta_prod_prime (((3 : ℝ) / 2 : ℂ) + t * Complex.I) hs).symm
```

### child `abs_zeta_ratio_eval`: [`StrongPNT/PNT3_RiemannZeta.lean` lines 585-637](https://github.com/math-inc/strongpnt/blob/2f5835c322314f55f1026ec2f139d704b7c45c69/StrongPNT/PNT3_RiemannZeta.lean#L585-L637) ([local copy](code/StrongPNT/PNT3_RiemannZeta.lean))

```lean
lemma abs_zeta_ratio_eval : norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2)) = ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := by
  -- Start from the Euler product identity at 3/2
  have hratio := zeta_ratio_at_3_2
  -- Define complex and real Euler factors
  let w : ℙ → ℂ := fun p => (1 + ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) : ℂ)))⁻¹
  let u : ℙ → ℝ := fun p => (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹
  -- Multipliability of the real factors
  have hu_mult : Multipliable u :=
    multipliable_positive_inv_powers ((3 : ℝ) / 2) (by norm_num : 1 < (3 : ℝ) / 2)
  -- Show w is the complexification of u
  have hw_eq : w = fun p : ℙ => (u p : ℂ) := by
    funext p
    -- rewrite the complex cpow as a real rpow, using nonnegativity of the base
    have hx : 0 ≤ ((p : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le (p : ℕ))
    have hcpow : (((((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2))) : ℝ) : ℂ)
        = ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) : ℂ)) := by
      simpa using (Complex.ofReal_cpow (x := ((p : ℕ) : ℝ)) (hx := hx) (y := -((3 : ℝ) / 2)))
    calc
      w p = (1 + ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) : ℂ)))⁻¹ := rfl
      _ = (1 + (((((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2))) : ℝ) : ℂ))⁻¹ := by
        simp [hcpow]
      _ = (((1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ : ℝ) : ℂ) := by
        simp [Complex.ofReal_add, Complex.ofReal_inv, Complex.ofReal_one]
  -- Multipliability of the complex factors via mapping by ofReal
  have hw_mult : Multipliable w := by
    have hmap : Multipliable ((fun x : ℝ => (x : ℂ)) ∘ u) :=
      Multipliable.map (hf := hu_mult) Complex.ofRealHom Complex.continuous_ofReal
    simpa [hw_eq] using hmap
  -- Take absolute values inside the product
  have h_abs_tprod : norm (∏' p : ℙ, w p) = ∏' p : ℙ, norm (w p) :=
    abs_of_tprod w hw_mult
  -- For each factor, the absolute value equals the real factor
  have h_abs_eq_fun : (fun p : ℙ => norm (w p)) = u := by
    funext p
    -- u p ≥ 0
    have hge : 0 ≤ ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)) :=
      Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le (p : ℕ))) _
    have hpos : 0 < 1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)) := by linarith
    have hnonneg : 0 ≤ u p := by
      have : 0 < (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := inv_pos.mpr hpos
      exact this.le
    -- conclude
    simp [hw_eq, Complex.norm_real, abs_of_nonneg hnonneg]
  -- Rewrite the ratio using the identity, then conclude
  have h_abs_ratio : norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2))
      = norm (∏' p : ℙ, w p) := by
    simpa [w] using congrArg norm hratio
  calc
    norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2))
        = norm (∏' p : ℙ, w p) := h_abs_ratio
    _ = ∏' p : ℙ, norm (w p) := h_abs_tprod
    _ = ∏' p : ℙ, u p := by simp [h_abs_eq_fun]
    _ = ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := rfl
```

### child `abs_zeta_inequality`: [`StrongPNT/PNT3_RiemannZeta.lean` lines 519-581](https://github.com/math-inc/strongpnt/blob/2f5835c322314f55f1026ec2f139d704b7c45c69/StrongPNT/PNT3_RiemannZeta.lean#L519-L581) ([local copy](code/StrongPNT/PNT3_RiemannZeta.lean))

```lean
lemma abs_zeta_inequality (t : ℝ) :
  ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ ≤
  ∏' p : ℙ, (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹ := by
  -- Following the informal proof: use abs_term_inv_bound, prod_inequality, and zetaEulerprod

  -- Establish positivity for NNReal conversion
  have h_pos_left : ∀ p : ℙ, 0 < (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := by
    intro p
    apply inv_pos.mpr
    apply add_pos zero_lt_one
    -- Since p ≥ 2 > 0 and exponent is negative, p^(-3/2) > 0
    apply Real.rpow_pos_of_pos
    exact_mod_cast (p.property.pos : 0 < (p : ℕ))

  have h_pos_right : ∀ p : ℙ, 0 < (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹ := by
    intro p
    apply inv_pos.mpr
    -- norm z > 0 iff z ≠ 0, using the fact that norm = norm
    rw [norm_pos_iff]
    exact condp32 p t

  -- Establish multipliability using zetaEulerprod and given lemmas
  have h_mult_left : Multipliable (fun p : ℙ => (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹) :=
    multipliable_positive_inv_powers ((3 : ℝ) / 2) (by norm_num : 1 < (3 : ℝ) / 2)

  have h_mult_right : Multipliable (fun p : ℙ => (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹) := by
    let s := ((3 : ℝ) / 2) + t * Complex.I
    have hs : 1 < s.re := by
      simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, add_zero]
      norm_num
    -- Use zetaEulerprod to get multipliability
    have h_euler := (zetaEulerprod s hs).1
    have h_nonzero : ∀ p : ℙ, 1 - ((p : ℕ) : ℂ) ^ (-s) ≠ 0 := fun p => condp32 p t
    exact multipliable_complex_abs_inv (fun p : ℙ => ((p : ℕ) : ℂ) ^ (-s)) h_euler h_nonzero

  -- Convert to NNReal to use prod_inequality
  let f : ℙ → NNReal := fun p => ⟨(1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹, le_of_lt (h_pos_left p)⟩
  let g : ℙ → NNReal := fun p => ⟨(norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹, le_of_lt (h_pos_right p)⟩

  have hf : Multipliable f := multipliable_real_to_nnreal _ h_pos_left h_mult_left
  have hg : Multipliable g := multipliable_real_to_nnreal _ h_pos_right h_mult_right

  -- Apply pointwise inequality from abs_term_inv_bound
  have h_pointwise : ∀ p : ℙ, f p ≤ g p := by
    intro p
    simp only [f, g, ← NNReal.coe_le_coe, NNReal.coe_mk]
    exact abs_term_inv_bound p t

  -- Apply prod_inequality
  have h_nnreal_ineq : ∏' p, f p ≤ ∏' p, g p := prod_inequality f g hf hg h_pointwise

  -- Convert back to ℝ using nnreal_tprod_le_coe
  have h_convert : ∏' p, (f p : ℝ) ≤ ∏' p, (g p : ℝ) := nnreal_tprod_le_coe f g hf hg h_nnreal_ineq

  -- Show the equality with original expressions
  have h_eq_f : ∏' p, (f p : ℝ) = ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := by
    simp only [f, NNReal.coe_mk]

  have h_eq_g : ∏' p, (g p : ℝ) = ∏' p : ℙ, (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹ := by
    simp only [g, NNReal.coe_mk]

  rw [h_eq_f, h_eq_g] at h_convert
  exact h_convert
```

### child `abs_zeta_prod_prime`: [`StrongPNT/PNT3_RiemannZeta.lean` lines 62-67](https://github.com/math-inc/strongpnt/blob/2f5835c322314f55f1026ec2f139d704b7c45c69/StrongPNT/PNT3_RiemannZeta.lean#L62-L67) ([local copy](code/StrongPNT/PNT3_RiemannZeta.lean))

```lean
lemma abs_zeta_prod_prime (s : ℂ) (hs : 1 < s.re) :
  norm (riemannZeta s) = ∏' p : ℙ, (norm (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ)))⁻¹ := by
  rw [abs_zeta_prod s hs]
  congr 1
  ext p
  rw [abs_of_inv (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ)) (one_minus_p_s_neq_0 p s hs)]
```

How the parts fit. The parent `zeta_lower_bound` is a single `calc` of three
links, each closed by one named lemma, plus a `have hs` side condition
(`1 < Re(3/2 + it)`, lines 642-644, by `simp`/`norm_num`) that only the third
link needs. The lemma graph (each arrow = "is applied in"):

```text
zeta_lower_bound (639)
├─ link 1 (=): abs_zeta_ratio_eval (585)  — |ζ(3)/ζ(3/2)| = ∏_p (1 + p^{-3/2})⁻¹
├─ link 2 (≤): abs_zeta_inequality (519)   — ∏_p (1 + p^{-3/2})⁻¹ ≤ ∏_p |1 - p^{-(3/2+it)}|⁻¹
└─ link 3 (=): abs_zeta_prod_prime (62)    — ∏_p |1 - p^{-(3/2+it)}|⁻¹ = |ζ(3/2+it)|
```

with each child's own named-lemma dependencies:

- `abs_zeta_ratio_eval` (585) applies `zeta_ratio_at_3_2` (292), `abs_of_tprod`
  (38), `multipliable_positive_inv_powers` (386) and `Complex.ofReal_cpow`.
- `abs_zeta_inequality` (519) applies `abs_term_inv_bound` (358), `condp32`
  (343), `prod_inequality` (366), `multipliable_positive_inv_powers` (386),
  `multipliable_complex_abs_inv` (373), `multipliable_real_to_nnreal` (474),
  `nnreal_tprod_le_coe` (513) and `zetaEulerprod` (30).
- `abs_zeta_prod_prime` (62) applies `abs_zeta_prod` (46), `abs_of_inv` (50)
  and `one_minus_p_s_neq_0` (53).

Why each child is a good leaf:

- `abs_zeta_ratio_eval` is self-contained: its statement fixes the special
  value `s = 3/2` and has no hypotheses, so it closes on its own from
  `zeta_ratio_at_3_2` (already proved) and the general `abs_of_tprod`; its
  four-link `calc` only converts between the complex and real Euler factors.
- `abs_zeta_inequality` isolates the analytic heart: a factorwise bound between
  two real infinite products, closed by converting both sides to `NNReal`,
  applying `prod_inequality` (which is `Multipliable.tprod_le_tprod`) on the
  per-prime `abs_term_inv_bound`, and converting back. Its two multipliability
  obligations are named sub-lemmas of their own
  (`multipliable_positive_inv_powers`, `multipliable_complex_abs_inv`).
- `abs_zeta_prod_prime` is the reusable interface lemma: it is parametric in
  `s` (with only `1 < Re s`), so it is not tied to `3/2`, and it closes in
  four lines by `abs_zeta_prod`, `congr`/`ext`, and `abs_of_inv` with the
  nonzero side condition `one_minus_p_s_neq_0`.

The glue is thin (10 lines) because all three links' substance lives in the
children; the parent only states the side condition and lets `calc` check the
transitivity and the definitional matching of adjacent links.

## Why it is good

1. *(check)* The parent `zeta_lower_bound` (lines 639-651) is a single
   three-link `calc` whose links are discharged by exactly three named project
   lemmas — `abs_zeta_ratio_eval` (647), `abs_zeta_inequality t` (649),
   `abs_zeta_prod_prime` (651) — and whose only other proof text is the
   `have hs` side condition (642-644, `simp` + `norm_num`).
2. *(check)* `StrongPNT/PNT3_RiemannZeta.lean` (4778 lines) contains no
   `sorry`, `admit` or `axiom` token, so every lemma in the parent's
   dependency cone that lives in this file is closed without a hole.
3. *(measurement)* The glue is 10 lines (642-651) assembling 3 direct lemmas
   whose proof bodies are 52, 60 and 4 lines; the longest chain of project
   lemmas below the theorem is 10 deep (`zeta_lower_bound → abs_zeta_ratio_eval
   → zeta_ratio_at_3_2 → zeta_ratio_identity_ofReal_div_two →
   zeta_ratio_identity → zeta_ratios → simplify_prod_ratio → prod_of_ratios →
   prod_of_ratios_simplified → lift_multipliable_of_nonzero`).
4. *(author-statement)* The author labels the theorem `-- Theorem
   zeta_lower_bound` (line 583) and states the plan for the analytic child in a
   comment: `-- Following the informal proof: use abs_term_inv_bound,
   prod_inequality, and zetaEulerprod` (line 522).
6. *(known-use)* The same one-named-lemma-per-link `calc` move recurs in the
   file: `abs_zeta_ratio_eval`'s own body is a 4-link calc (632-637) and
   `prod_of_ratios_simplified` is a 7-link calc (145-160).

## When to use it, and when not

Use it when a real bound `A ≤ B` between two analytic values is proven by
rewriting both endpoints as infinite products over the *same* index set and
comparing them factorwise: the two product rewrites are one `=` link each, the
factorwise comparison is one `≤` link, and each link is clean enough to state
as its own named lemma. The middle terms must definitionally match so `calc`
joins them. This is the standard shape of an Euler-product estimate for the
Riemann zeta function (or any Dirichlet-series/Euler-product object), and the
third link is reusable when stated parametrically in `s`.

Avoid it when the product rewrites are one-line `rw`/`simp` steps (inline them
rather than name lemmas), when the factorwise bound needs so much local context
that it cannot be a clean standalone statement, or when the two products are
indexed by different sets so no single middle term joins the chain. Also avoid
forcing the `=`/`≤` structure if one endpoint has no product representation at
all — then the `calc` has no middle term to hang on.

## Consequences

The move creates three obligations, one per link: (a) evaluate the concrete
value to a product (`abs_zeta_ratio_eval`); (b) a factorwise bound between two
products, carrying a multipliability/summability obligation for both sides
(`abs_zeta_inequality`); (c) fold the product back into a function value,
carrying the side condition `1 < Re s` (`abs_zeta_prod_prime`, fed by the
parent's `have hs`). Failure modes: the side condition `hs` must be discharged
by the parent (here `simp`/`norm_num`) before link 3 elaborates; the factorwise
step is the analytic heart and its `NNReal` multipliability hypotheses are
heavy, so a child whose statement drifts from the chain endpoints will not
elaborate; and if the two product rewrites were not already available as named
lemmas, they would have to be stated first or inlined into the chain.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | Source CI .github/workflows/blueprint.yml (job build_project, step 'Build the project' via leanprover/lean-action@v1.2.0) builds the whole Lean project incl. StrongPNT/PNT3_RiemannZeta.lean; triggers on push to main. Pinned commit 2f5835c322314f55f1026ec2f139d704b7c45c69 is the tip of default branch main (GitHub compare 2f5835c...main = identical). | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 2f5835c322314f55f1026ec2f139d704b7c45c69 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read copied code/StrongPNT/PNT3_RiemannZeta.lean L639-651: calc with exactly three links = abs_zeta_ratio_eval (L647), <= abs_zeta_inequality t (L649), = abs_zeta_prod_prime ... hs (L651); have hs at L642-644 closed by simp only / norm_num. Matches claim. | verifier |
| 2 | verified | wc -l of copied file = 4778; grep -nE word-boundary (sorry|admit|axiom) over code/StrongPNT/PNT3_RiemannZeta.lean returned no matches. | verifier |
| 3 | verified | Read copied file: glue L642-651 = 10 lines; child proof bodies 586-637 (52 lines), 522-581 (60), 64-67 (4); 10-deep chain each arrow confirmed as an application: L647 abs_zeta_ratio_eval -> L587 zeta_ratio_at_3_2 -> L295 zeta_ratio_identity_ofReal_div_two -> L289 zeta_ratio_identity -> L265 zeta_ratios -> L227 simplify_prod_ratio -> L204 prod_of_ratios -> L186 prod_of_ratios_simplified -> L139/140 lift_multipliable_of_nonzero. | verifier |
| 4 | verified | Read copied file L583: comment '-- Theorem zeta_lower_bound'; L522: comment '-- Following the informal proof: use abs_term_inv_bound, prod_inequality, and zetaEulerprod'. Both match claim verbatim. | verifier |
| 5 | refuted | First half correct: abs_zeta_ratio_eval body L632-637 is a 4-link calc. Second half wrong: prod_of_ratios_simplified L145-160 has 7 equality links (L148,150,152,154,156,158,160), not 6 as claimed. | verifier |
| 6 | verified | Read copied code/StrongPNT/PNT3_RiemannZeta.lean: abs_zeta_ratio_eval body L632-637 is a calc with exactly 4 equality links (L634 h_abs_ratio, L635 h_abs_tprod, L636 simp [h_abs_eq_fun], L637 rfl); prod_of_ratios_simplified L145-160 is a calc with exactly 7 equality links (L148, L150, L152, L154, L156, L158, L160). Both line ranges and link counts match claim 6. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Verified against the copied file (byte-identical to commit 2f5835c3 per check_provenance). Parent zeta_lower_bound (639-651) is a single 3-link calc (=,<=,=) discharged by exactly the three named children: abs_zeta_ratio_eval (647), abs_zeta_inequality t (649), abs_zeta_prod_prime (651, applied with .symm under hs); only other text is have hs (642-644). Child statements and bodies in README/entry.json match the code lines 585-637, 519-581, 62-67 exactly. No sorry/admit/axiom tokens in the file (4778 lines), so nothing is left as a hole. Shape numbers verified: direct_lemmas=3, glue_lines=10 (642-651), child_lines=[52,60,4] (586-637, 522-581, 64-67). Depth-10 chain verified edge-by-edge: zeta_lower_bound->abs_zeta_ratio_eval->zeta_ratio_at_3_2(292)->zeta_ratio_identity_ofReal_div_two(288)->zeta_ratio_identity(264)->zeta_ratios(225)->simplify_prod_ratio(189)->prod_of_ratios(164)->prod_of_ratios_simplified(131)->lift_multipliable_of_nonzero(98), each edge present in the code. | reviewer-correctness |
| generality | accept | Move is stated beyond the example: 'When to use' generalizes to 'the standard shape of an Euler-product estimate ... (or any Dirichlet-series/Euler-product object)' and use_when requires only an Euler-product-analogue rewrite over a shared index set, not the zeta specifics. 'Avoid when' is honest and specific (inline one-line rw/simp rewrites; skip when factorwise bound needs too much local context; skip when products have different index sets). Consequences names three per-link obligations and honest failure modes (parent must discharge hs before link 3; the NNReal multipliability hypotheses are heavy; product rewrites must already exist as named lemmas). 'Why each child is a good leaf' directly answers the bounded-prover question: self-contained with no hypotheses (abs_zeta_ratio_eval), isolated analytic heart with named multipliability sub-lemmas (abs_zeta_inequality), and a reusable 4-line interface lemma parametric in s (abs_zeta_prod_prime). No objection. | reviewer-generality |
| provenance-licence | accept | Provenance and licence are consistent and traceable. Permalinks point to github.com/math-inc/strongpnt/blob/2f5835c322314f55f1026ec2f139d704b7c45c69/StrongPNT/PNT3_RiemannZeta.lean with line ranges that match the copied file exactly (abs_zeta_prod_prime 62-67, abs_zeta_inequality 519-581, abs_zeta_ratio_eval 585-637, zeta_lower_bound 639-651). Commit 2f5835c322314f55f1026ec2f139d704b7c45c69 is real (GitHub API, message 'Let there be light') and identical across entry.json, README, SOURCE.md and source.json. Licence is recorded as LicenseRef-unknown, matching SOURCE.md/source.json, and confirmed honest: the repo root has no LICENSE/COPYING file (GitHub API listing). check_provenance.py passes: file byte-identical at the pinned commit. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/math-inc/strongpnt at commit `2f5835c322314f55f1026ec2f139d704b7c45c69`, under `LicenseRef-unknown`; see the [source note](../../sources/strongpnt/SOURCE.md) for the licence text and attribution.
