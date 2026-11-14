# API lemma lem_Bf_off_K expands the Blaschke product Bf off the zero set

| | |
|---|---|
| Kind | instance |
| Move | interface-lemma |
| Language | lean |
| Status | accepted |
| Source | [strongpnt](../../sources/strongpnt/SOURCE.md) at `2f5835c32231` |
| Licence | `LicenseRef-unknown` |
| Licence recorded | 2026-11-14T09:18:37Z |

## Intent

`Bf` is a `noncomputable def` — the Blaschke product written as `Cf z` times a
finite product of factors. Unfolding it (and `Cf`) everywhere would leak the
definitional details into every client. This decomposition states the
expansion once, as the interface lemma `lem_Bf_off_K`, so that downstream
proofs rewrite by one lemma and never unfold `Bf` or `Cf` themselves.

## The decomposition

### parent `lem_Bf_off_K`: [`StrongPNT/PNT2_LogDerivative.lean` lines 967-987](https://github.com/math-inc/strongpnt/blob/2f5835c322314f55f1026ec2f139d704b7c45c69/StrongPNT/PNT2_LogDerivative.lean#L967-L987) ([local copy](code/StrongPNT/PNT2_LogDerivative.lean))

```lean
lemma lem_Bf_off_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f) :
    Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
    f z * ∏ ρ ∈ h_finite_zeros.toFinset,
      (((R : ℂ) - star ρ * z / (R : ℂ)) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat := by
  -- Start with lem_BfCf to get the initial form
  rw [lem_BfCf h_finite_zeros h_σ z hz]
  -- Use mul_div_assoc to rearrange f z * (A / B) = f z * A / B
  rw [mul_div_assoc]
  -- Work on the division part using congr
  congr 1
  -- Apply lem_Bf_div with explicit parameters
  rw [@lem_Bf_div R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros z hz]
  -- Apply lem_Bf_prodpow with explicit parameters
  rw [@lem_Bf_prodpow R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros z hz]
```

### child `lem_BfCf`: [`StrongPNT/PNT2_LogDerivative.lean` lines 912-936](https://github.com/math-inc/strongpnt/blob/2f5835c322314f55f1026ec2f139d704b7c45c69/StrongPNT/PNT2_LogDerivative.lean#L912-L936) ([local copy](code/StrongPNT/PNT2_LogDerivative.lean))

```lean
lemma lem_BfCf
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f) :
    Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
    f z * (∏ ρ ∈ h_finite_zeros.toFinset,
      ((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) /
    (∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat) := by
  -- Since z ∉ zerosetKfR R1, we know z is not in the zero set
  have hz_not_in : z ∉ zerosetKfR R1 (by linarith) f := hz.2

  -- Unfold Bf definition
  unfold Bf

  -- Unfold Cf definition and use the else branch since z ∉ zerosetKfR R1
  unfold Cf
  simp [hz_not_in]

  -- Now we have: (f z / ∏ ρ, (z - ρ)^m) * ∏ ρ, Blaschke_factor = goal
  -- Use div_mul_eq_mul_div: (a / b) * c = (a * c) / b
  exact div_mul_eq_mul_div _ _ _
```

### child `lem_Bf_div`: [`StrongPNT/PNT2_LogDerivative.lean` lines 938-951](https://github.com/math-inc/strongpnt/blob/2f5835c322314f55f1026ec2f139d704b7c45c69/StrongPNT/PNT2_LogDerivative.lean#L938-L951) ([local copy](code/StrongPNT/PNT2_LogDerivative.lean))

```lean
lemma lem_Bf_div
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f) :
    (∏ ρ ∈ h_finite_zeros.toFinset,
      ((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) /
    (∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat) =
    ∏ ρ ∈ h_finite_zeros.toFinset,
      (((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat /
       (z - ρ) ^ (analyticOrderAt f ρ).toNat) := by
  rw [Finset.prod_div_distrib]
```

### child `lem_Bf_prodpow`: [`StrongPNT/PNT2_LogDerivative.lean` lines 953-965](https://github.com/math-inc/strongpnt/blob/2f5835c322314f55f1026ec2f139d704b7c45c69/StrongPNT/PNT2_LogDerivative.lean#L953-L965) ([local copy](code/StrongPNT/PNT2_LogDerivative.lean))

```lean
lemma lem_Bf_prodpow
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f) :
    ∏ ρ ∈ h_finite_zeros.toFinset,
      (((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat /
       (z - ρ) ^ (analyticOrderAt f ρ).toNat) =
    ∏ ρ ∈ h_finite_zeros.toFinset,
      (((R : ℂ) - star ρ * z / (R : ℂ)) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat := by
  simp only [div_pow]
```

### context `Bf`: [`StrongPNT/PNT2_LogDerivative.lean` lines 897-910](https://github.com/math-inc/strongpnt/blob/2f5835c322314f55f1026ec2f139d704b7c45c69/StrongPNT/PNT2_LogDerivative.lean#L897-L910) ([local copy](code/StrongPNT/PNT2_LogDerivative.lean))

```lean
noncomputable def Bf
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (z : ℂ) : ℂ :=
  Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z *
  ∏ ρ ∈ h_finite_zeros.toFinset,
    ((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat
```

### How the parts fit

The parent `lem_Bf_off_K` is proved entirely by a chain of rewrites, each
step closing one obligation. Write `A` for the numerator product
`∏ ρ, (R - ρ̄ z / R) ^ m` and `B` for the denominator product
`∏ ρ, (z - ρ) ^ m`. The glue then is:

```
lem_Bf_off_K  Bf z = f z * ∏ ((R - ρ̄ z/R) / (z - ρ))^m        (parent, interface lemma)
├── rw [lem_BfCf ...]         unfold Bf and Cf off the zero set:  Bf z = f z * (A / B)
├── rw [mul_div_assoc]        (Mathlib) turn f z * A / B into f z * (A / B)
├── congr 1                   drop the shared factor f z, keep one product goal
├── rw [@lem_Bf_div ...]      A / B  =  ∏ (Aᵢ / Bᵢ)
└── rw [@lem_Bf_prodpow ...]  ∏ (Aᵢ / Bᵢ)  =  ∏ (Aᵢ / Bᵢ)^m
```

The first line of the proof cites `lem_BfCf`, the fourth `lem_Bf_div`, the
fifth `lem_Bf_prodpow` (lines 979, 985, 987); `mul_div_assoc` and `congr 1`
are Mathlib/tactic glue, not project lemmas. So there are exactly three
direct children.

Why each child is a good leaf:

- **`lem_BfCf`** is the only leaf that touches the definitions. It unfolds
  `Bf` and `Cf`, uses the fact that `z` is off the zero set so `Cf` takes its
  `else` branch (`simp [hz_not_in]`), and closes with one Mathlib rewrite,
  `exact div_mul_eq_mul_div _ _ _`. Everything that needs to know the
  definitions lives here; after it, no client unfolds them.
- **`lem_Bf_div`** moves a quotient of two finite products inside the product
  symbol; its whole proof is `rw [Finset.prod_div_distrib]`. It is a
  self-contained algebraic fact, closed on its own.
- **`lem_Bf_prodpow`** moves a quotient under a power, its whole proof
  `simp only [div_pow]`. Also self-contained and closed on its own.

The result is the canonical Blaschke-factor form
`∏ ((R - ρ̄ z / R) / (z - ρ)) ^ m`, which is the closed form the next results
(the `K ≤ 3 log B` bound, blueprint §2) want to reason about.

## Why it is good

1. The parent and its three children (lines 912-987) contain no `sorry`; the
   range was machine-checked with `check_claims.py` (`no_sorry`), so the
   decomposition closes rather than punts.
2. The glue cites its children: `lem_BfCf` occurs in the parent site (line
   979), and `lem_Bf_div`, `lem_Bf_prodpow` at lines 985 and 987; the
   `glue-cites-children` check records all three.
3. The shape is small and shallow: the glue is 21 lines, the children 25, 14
   and 13 lines, all in one chain of depth 1 (measured from the copied file,
   lines 912-987).
4. The authors publish the same dependency graph in the blueprint: the node
   "B off K" (`lem:Bf_off_K`) is proved "By \cref{lem:BfCf} and
   \cref{lem:Bf_div,lem:Bf_prodpow}" with `\uses{lem:BfCf, lem:Bf_div,
   lem:Bf_prodpow}` (blueprint `PNT2_LogDerivative.tex`, lines 569-579).

In my opinion the detail worth copying is that the interface lemma is split so
that only one child (`lem_BfCf`) ever unfolds the definitions, while the other
two are pure, reusable algebra. This keeps the definitional knowledge in one
place and lets the rest of the chain be closed by single Mathlib rewrites.

Note on the rule survey: the interface-lemma move is not one of survey F §10's
18 numbered rules (the closest is rule 17, "memoise canonical statements
across branches"); this entry is evidence that the move is worth naming on its
own.

## When to use it, and when not

Use it when a definition's unfolding is wanted by many downstream clients but
you want them to cite one canonical expansion rather than unfold it each time,
and when the expansion factors into a short chain of algebraic rewrites each
closable by a single Mathlib lemma. The goal shape is an equality
`F z = G z` where `F` is a `noncomputable def` (a composite of another def and
a finite product) and `G` is the intended closed form, possibly holding only
off a distinguished subset that becomes a hypothesis.

Avoid it when the expansion needs a case analysis or a non-algebraic argument
(then the leaves are not single rewrites, and the interface lemma hides real
work rather than removing it), when the closed form is needed in only one
place (unfold locally instead of adding an API lemma), or when the boundary
statement is not yet the stable form clients actually consume, so it would be
rewritten again downstream.

## Consequences

The move pins the closed form: a client that rewrites with `lem_Bf_off_K`
gets the `((R - ρ̄ z / R) / (z - ρ)) ^ m` factor form, so a later result that
needs a different grouping must re-split. The lemma holds only off the zero
set, so the hypothesis `z ∉ zerosetKfR R1 f` is a side condition every client
must supply. Unfolding is deferred, not removed — `lem_BfCf` still unfolds
`Bf` and `Cf`, so the interface lemma hides the definitions from clients but
not from the library. The `congr 1` step silently assumes the two sides agree
up to the scalar `f z` and one factor; if the statement changes shape that
step must be re-checked.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/blueprint.yml runs leanprover/lean-action@v1.2.0 (lake build of default target StrongPNT, which imports StrongPNT.PNT2_LogDerivative) on push to main; source pinned at ref HEAD (2f5835c) on default branch | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: lem_BfCf@StrongPNT/PNT2_LogDerivative.lean:978, lem_Bf_div@StrongPNT/PNT2_LogDerivative.lean:984, lem_Bf_prodpow@StrongPNT/PNT2_LogDerivative.lean:986; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 2f5835c322314f55f1026ec2f139d704b7c45c69 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | no_sorry(StrongPNT/PNT2_LogDerivative.lean, 912-987) -> no_sorry: none of sorry, admit, axiom in StrongPNT/PNT2_LogDerivative.lean:912-987 | check_claims.py |
| 2 | verified | cites(StrongPNT/PNT2_LogDerivative.lean:967-987, lem_BfCf) -> cites: lem_BfCf occurs at StrongPNT/PNT2_LogDerivative.lean:978 | check_claims.py |
| 3 | verified | read copied code StrongPNT/PNT2_LogDerivative.lean lines 897-987: glue lem_Bf_off_K = 21 lines (967-987), lem_BfCf = 25 (912-936), lem_Bf_div = 14 (938-951), lem_Bf_prodpow = 13 (953-965); parent proof cites the three children directly (rw [lem_BfCf], rw [@lem_Bf_div], rw [@lem_Bf_prodpow]) so depth 1 | verifier |
| 4 | verified | read blueprint/src/PNT/PNT2_LogDerivative.tex lines 569-579: \begin{lemma}[B off K]\label{lem:Bf_off_K}, proof contains \uses{lem:BfCf, lem:Bf_div, lem:Bf_prodpow} and 'By \cref{lem:BfCf} and \cref{lem:Bf_div,lem:Bf_prodpow}' | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent lem_Bf_off_K (967-987, 21 lines) is proved by rw[lem_BfCf]@979, rw[mul_div_assoc]@981, congr 1@983, rw[@lem_Bf_div]@985, rw[@lem_Bf_prodpow]@987; exactly the 3 project children, each closing by a single Mathlib rewrite (exact div_mul_eq_mul_div@936, rw[Finset.prod_div_distrib]@951, simp only [div_pow]@965), no sorry/admit/axiom in 912-987. Shape numbers match: glue_lines 21, child_lines [25,14,13], direct_lemmas 3, depth 1. | reviewer-correctness |
| generality | accept | Move stated generically beyond Blaschke/Bf/Cf: applicability gives a generic goal_shape (F z = G z, F a noncomputable def composite, closed form off a distinguished subset as hypothesis) and use_when cites 'one canonical expansion instead of unfolding each time, factoring into a short chain of single-Mathlib-lemma rewrites'. avoid_when is specific and honest (case analysis/non-algebraic hides real work; single-use -> unfold locally; unstable boundary -> rewritten downstream). Consequences honest: pins the closed form, z-not-in-zero-set side condition, unfolding deferred not removed (lem_BfCf still unfolds), and congr-1 fragility. Good-leaf criterion for a bounded prover is explicit: each child closes by one Mathlib rewrite/exact (div_mul_eq_mul_div, Finset.prod_div_distrib, div_pow), self-contained, depth 1, only lem_BfCf touches definitions. Verified the cited code (lines 897-987) matches these characterisations. | reviewer-generality |
| provenance-licence | accept | check_provenance passes (1 file byte-identical at 2f5835c322314f55f1026ec2f139d704b7c45c69). Commit is consistent everywhere: entry.json and SOURCE.md use the full 2f5835c322314f55f1026ec2f139d704b7c45c69, README uses the 12-char prefix 2f5835c32231. Licence is LicenseRef-unknown in entry.json source.licence, README and SOURCE.md; SOURCE.md records 'no licence file found at the root', matching the unknown licence. All file/site permalinks use the pinned commit and path StrongPNT/PNT2_LogDerivative.lean, which is the copied file. Sed-verified the cited ranges match the copied file: parent 967-987, children lem_BfCf 912-936, lem_Bf_div 938-951, lem_Bf_prodpow 953-965, context Bf 897-910. Everything traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/math-inc/strongpnt at commit `2f5835c322314f55f1026ec2f139d704b7c45c69`, under `LicenseRef-unknown`; see the [source note](../../sources/strongpnt/SOURCE.md) for the licence text and attribution.
