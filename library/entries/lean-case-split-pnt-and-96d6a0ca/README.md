# Case split on sigma <= 3/2 to glue a strip bound and a half-plane bound

| | |
|---|---|
| Kind | instance |
| Move | case-split |
| Language | lean |
| Status | accepted |
| Source | [pnt-and](../../sources/pnt-and/SOURCE.md) at `2c476fa6441c` |
| Licence | `Apache-2.0` |

## Intent

Bound `‖ζ' / ζ (σ + I·t)‖` uniformly by one constant `C` times `log²|t|` over
the whole region `σ ≥ 1 − F / log|t|`. The region is covered by two lemmas that
meet at `σ = 3/2`: the strip bound (valid for `1 − F/log|t| ≤ σ ≤ 3/2`) and the
half-plane bound (valid for `σ ≥ 3/2`). The glue takes `C = max C1 C2` and
splits on `σ ≤ 3/2`, applying each lemma on its own side.

## The decomposition

### parent `LogDerivZetaUniformLogSquaredBound`: [`PrimeNumberTheoremAnd/StrongPNT.lean` lines 2831-2850](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/StrongPNT.lean#L2831-L2850) ([local copy](code/PrimeNumberTheoremAnd/StrongPNT.lean))

```lean
theorem LogDerivZetaUniformLogSquaredBound : ∃ (C : ℝ) (_ : 0 < C),
    ∀ (σ t : ℝ), 3 < |t| → σ ∈ Set.Ici (1 - F / Real.log |t|) →
      ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ C * Real.log |t| ^ (2 : ℝ) := by
  obtain ⟨C1, hC1⟩ := LogDerivZetaUniformLogSquaredBoundStripSpec
  obtain ⟨C2, hC2⟩ := LogDerivZetaBdd_of_Re_ge_three_halves
  have hC2pos := (norm_nonneg _).trans (hC2 2 (by norm_num))
  use max C1 C2, lt_max_of_lt_left hC1.1
  intro σ t ht hσ
  by_cases hσ' : σ ≤ 3 / 2
  · apply (hC1.2 t (by grind) σ ⟨hσ, hσ'⟩).trans
    gcongr
    · exact le_max_left _ _
    · simp only [log_abs, rpow_ofNat, Std.le_refl]
  · refine (hC2 _ ?_).trans ?_
    · norm_num; linarith
    · nth_rewrite 1 [← mul_one C2, ← mul_one 1, ← sq]
      refine mul_le_mul (le_max_right _ _) ?_ (sq_nonneg _) ?_
      · rw [one_pow, rpow_ofNat, one_le_sq_iff_one_le_abs, abs_of_pos (Real.log_pos (by linarith)), Real.le_log_iff_exp_le (by linarith)]
        linarith [Real.exp_one_lt_d9]
      · linarith [le_max_right C1 C2]
```

### context `LogDerivZetaUniformLogSquaredBound-blueprint`: [`PrimeNumberTheoremAnd/StrongPNT.lean` lines 2821-2830](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/StrongPNT.lean#L2821-L2830) ([local copy](code/PrimeNumberTheoremAnd/StrongPNT.lean))

```lean
@[blueprint "LogDerivZetaUniformLogSquaredBound"
  (title := "LogDerivZetaUniformLogSquaredBound")
  (statement := /--
    There exists a constant $F\in(0,1/42)$ such that for all $t\in\mathbb{R}$ with $|t|\geq 3$ one has
    $$1-\frac{F}{\log|t|}\leq\sigma\implies\left|\frac{\zeta'}{\zeta}(\sigma+it)\right|\ll\log^2|t|$$
    where the implied constant is uniform in $\sigma$.
  -/)
  (proof := /--
    Put the previous two Lemmas together.
  -/)]
```

### child `LogDerivZetaUniformLogSquaredBoundStripSpec`: [`PrimeNumberTheoremAnd/StrongPNT.lean` lines 2761-2765](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/StrongPNT.lean#L2761-L2765) ([local copy](code/PrimeNumberTheoremAnd/StrongPNT.lean))

```lean
lemma LogDerivZetaUniformLogSquaredBoundStripSpec : ∃ (C : ℝ) (_ : 0 < C),
    ∀ (t : ℝ), 3 ≤ |t| →
      ∀ (σ : ℝ), σ ∈ Set.Icc (1 - F / Real.log |t|) (3 / 2) →
          ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ C * (Real.log |t|) ^ 2 :=
            LogDerivZetaUniformLogSquaredBoundStrip.choose_spec.2
```

### child `LogDerivZetaBdd_of_Re_ge_three_halves`: [`PrimeNumberTheoremAnd/StrongPNT.lean` lines 2771-2817](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/StrongPNT.lean#L2771-L2817) ([local copy](code/PrimeNumberTheoremAnd/StrongPNT.lean))

```lean
@[blueprint "LogDerivZetaBdd_of_Re_ge_three_halves"
  (title := "LogDerivZetaBdd-of-Re-ge-three-halves")
  (statement := /--
    There exists a uniform constant $C$ such that for $z=\sigma+it$ one has
    $$3/2\leq\sigma\implies\left|\frac{\zeta'}{\zeta}(z)\right|\leq C.$$
  -/)
  (proof := /--
    Note that
    $$\left|\frac{\zeta'}{\zeta}(z)\right|=\left|\sum_{n=1}^\infty\frac{\Lambda(n)}{n^z}\right|\leq
      \sum_{n=1}^\infty\frac{\Lambda(n)}{|n^z|}=\sum_{n=1}^\infty\frac{\Lambda(n)}{n^\sigma}\leq
      \sum_{n=1}^\infty\frac{\Lambda(n)}{n^{3/2}}<\infty$$
    by \ref{vonMangoldtLSeriesSummable}.
  -/)]
lemma LogDerivZetaBdd_of_Re_ge_three_halves :
    ∃ C, ∀ (s : ℂ), 3/2 ≤ s.re → ‖deriv riemannZeta s / riemannZeta s‖ ≤ C := by
  have threeHalvesRe : 1 < ((3 / 2) : ℂ).re := by norm_num
  have h_sum_converges : Summable (fun n : ℕ ↦ vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ)) := by
    apply Complex.summable_ofReal.mp
    convert (vonMangoldtLSeriesSummable threeHalvesRe) using 2 with n
    rw [ofReal_div, Complex.ofReal_cpow, ofReal_natCast, ofReal_div, ofReal_ofNat 3, ofReal_ofNat 2]
    exact cast_nonneg' n
  have h_log_deriv_sum : ∀ s : ℂ, 3 / 2 ≤ s.re →
      deriv riemannZeta s / riemannZeta s = -∑' n : ℕ, (vonMangoldt n : ℂ) / (n : ℂ) ^ s := by
    intro s hs; have h := LogDerivativeDirichlet s (by grind); linear_combination -h
  have h_triangle : ∀ s : ℂ,
      ‖∑' n : ℕ, (vonMangoldt n : ℂ) / (n : ℂ) ^ s‖ ≤
        ∑' n : ℕ, ‖(vonMangoldt n : ℂ) / (n : ℂ) ^ s‖ := fun s ↦ by
    by_cases h : Summable fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ s
    · exact norm_tsum_le_tsum_norm h.norm
    · simp only [tsum_eq_zero_of_not_summable h, norm_zero]
      exact tsum_nonneg fun _ ↦ by positivity
  have h_norm_summand : ∀ s : ℂ, 3 / 2 ≤ s.re → ∀ n : ℕ,
      ‖(vonMangoldt n : ℂ) / (n : ℂ) ^ s‖ ≤ (vonMangoldt n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) := by
    intro s hs n
    by_cases hn : n = 0 <;> simp_all [Complex.norm_cpow_of_ne_zero]
    ring_nf; norm_num
    rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity)
      (Real.rpow_le_rpow_of_exponent_le (mod_cast Nat.one_le_iff_ne_zero.mpr hn) hs))
      ArithmeticFunction.vonMangoldt_nonneg
  refine ⟨∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ),
    fun s hs ↦ ?_⟩
  have hSum : Summable fun n ↦ ‖(vonMangoldt n : ℂ) / (n : ℂ) ^ s‖ :=
    Summable.of_nonneg_of_le (fun n ↦ by positivity)
      (fun n ↦ h_norm_summand s hs n) h_sum_converges
  simpa [neg_div, h_log_deriv_sum s hs] using (h_triangle s).trans
    (hSum.tsum_le_tsum (fun n ↦ h_norm_summand s hs n) h_sum_converges)
```

How the parts fit. The parent first extracts a positive constant from each
child with `obtain ⟨C1, hC1⟩ := LogDerivZetaUniformLogSquaredBoundStripSpec`
and `obtain ⟨C2, hC2⟩ := LogDerivZetaBdd_of_Re_ge_three_halves`, then commits to
the single witness `max C1 C2` (line 2837). After introducing `σ t ht hσ`, the
glue is exactly one case split, `by_cases hσ' : σ ≤ 3/2` (line 2839):

- **Left case** `σ ≤ 3/2`: the hypothesis `hσ` gives `σ ≥ 1 − F/log|t|`, so
  `⟨hσ, hσ'⟩` places `σ` in the strip `Set.Icc (1 - F/log|t|) (3/2)` and the
  strip bound `hC1.2` applies; `gcongr` with `le_max_left` closes it (lines
  2840-2843).
- **Right case** `¬ σ ≤ 3/2`: `norm_num; linarith` turns it into `3/2 ≤ σ`,
  satisfying the half-plane bound `hC2`; the rest (lines 2846-2850) shows
  `C2 ≤ C2 · log²|t|` by rewriting to `1 ≤ log²|t|` and closing with
  `Real.exp_one_lt_d9`, then `le_max_right` finishes against `max C1 C2`.

So the lemma graph is:

```
LogDerivZetaUniformLogSquaredBound  (parent, 2831)
├── LogDerivZetaUniformLogSquaredBoundStripSpec  (child, 2761)  →  LogDerivZetaUniformLogSquaredBoundStrip.choose_spec  (2603)
│     └── LogDerivZetaUniformLogSquaredBoundStrip  (2603)  →  SumBoundII (2435), GapSize (2528), GlobalBound (1400), ZerosBound (874), ZetaFixedLowerBound (1252)
└── LogDerivZetaBdd_of_Re_ge_three_halves  (child, 2784)  →  vonMangoldtLSeriesSummable (2127), LogDerivativeDirichlet
```

Each child is a good leaf: `LogDerivZetaUniformLogSquaredBoundStripSpec` is a
one-line statement whose proof is the second projection
`LogDerivZetaUniformLogSquaredBoundStrip.choose_spec.2` of an already-proved
lemma in the same file, and `LogDerivZetaBdd_of_Re_ge_three_halves` is a
self-contained 32-line proof that closes from `vonMangoldtLSeriesSummable`
(defined at line 2127) and `LogDerivativeDirichlet`, with no reference back to
the parent. The parent never unfolds either child: it only uses the existential
statement of each.

## Why it is good

1. The parent is closed by its two children and a single case split: `obtain`
   the two constants, `use max C1 C2`, `by_cases` on `σ ≤ 3/2`, and each branch
   closes with one `.trans` (check; lines 2834-2850).
2. Nothing is left as a hole: the whole file `StrongPNT.lean` has no `sorry`,
   `admit` or `axiom` (the only "axioms" mention is the diagnostic `#print
   axioms StrongPNT` at line 2906) (check; whole-file read).
3. The authors give the plan in the blueprint: "Put the previous two Lemmas
   together." (lines 2828-2830), and the half-plane child's plan as the
   Dirichlet-series bound "…≤ Σ Λ(n)/n^(3/2) < ∞ by vonMangoldtLSeriesSummable"
   (lines 2777-2782) (author-statement).
4. The glue is 17 lines and uses 2 direct lemmas; the two children are 1 line
   and 32 lines of proof respectively, and the chain I checked below the parent
   is depth 3 (parent → StripSpec → LogDerivZetaUniformLogSquaredBoundStrip →
   SumBoundII) (measurement; lines 2834-2850, 2761-2765, 2771-2817, 2603-2752,
   2435-2441).

In my opinion the detail worth copying is not the split itself but the choice of
split point: `σ = 3/2` is exactly where the two lemmas' regions overlap, so the
left case can hand the whole region to the strip lemma and the right case to the
half-plane lemma, and the only glue arithmetic is the trivial `1 ≤ log²|t|`
needed to turn the constant bound into the `log²` gauge.

## When to use it, and when not

Use it when a goal `∃ C > 0, ∀ x, P x → Q x ≤ C · g x` is already covered by two
proved lemmas that bound the same quantity `Q x` on regions whose union is
`P x` and that meet (or overlap) at a boundary — here the strip `1 − F/log|t| ≤
σ ≤ 3/2` and the half-plane `σ ≥ 3/2`. The boundary must be a decidable linear
inequality so `by_cases` (or `rcases le_or_lt`) handles it, and both lemmas must
use the same gauge `g` or a gauge one dominates (the constant bound is dominated
by `log²|t|` once `|t| > 3`).

Avoid it when the regions leave a gap the split must also prove, when the two
lemmas use different gauges with no domination between them, when the boundary
is not an order on a linear-ordered type, or when one lemma's constant cannot be
carried into the other's region without extra work.

## Consequences

The move creates two goals via `by_cases hσ' : σ ≤ 3/2`, whose exhaustiveness is
discharged by the law of the excluded middle — no separate exhaustiveness child
as a finite `rcases` disjunction would need. Both branches must close against
the same witness `max C1 C2`, so each needs a `le_max_left`/`le_max_right` step,
and the weaker (constant) bound must be lifted to the `log²` gauge; here that
is the `1 ≤ log²|t|` step closed by `Real.exp_one_lt_d9`. Failure mode: if the
two gauges did not dominate one another, the `gcongr`/`nth_rewrite`
normalisation would not close, and a third lemma or a different split point
would be required. This is a case split of the "glue two regional bounds" kind,
which supports survey F §10 rule 5, though its exhaustiveness is by `by_cases`
(LEM) rather than by a finite-disjunction obligation closed with `arith`.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml: runs leanprover/lean-action (build-args :blueprint) on push/PR to main, which compiles the PrimeNumberTheoremAnd library including StrongPNT.lean; pinned commit 2c476fa6441c607096d93c8fc7ac0a227a655dae is on default branch main (compare API: main ahead 1, behind 0) | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 2c476fa6441c607096d93c8fc7ac0a227a655dae | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Opened copied code/PrimeNumberTheoremAnd/StrongPNT.lean L2831-2850: L2834 obtain from LogDerivZetaUniformLogSquaredBoundStripSpec, L2835 obtain from LogDerivZetaBdd_of_Re_ge_three_halves, L2837 use max C1 C2, L2839 by_cases hsigma : sigma <= 3/2; left branch (hC1.2 ...).trans + gcongr, right branch (hC2 _ ?_).trans. Exactly two named project lemmas, split and one .trans per branch. | verifier |
| 2 | verified | grep of copied StrongPNT.lean for sorry|admit|axiom matched only L2906 '#print axioms StrongPNT'; no sorry, admit or axiom terms anywhere in the file. | verifier |
| 3 | verified | L2828-2830 contain the blueprint proof 'Put the previous two Lemmas together.'; L2777-2782 contain the half-plane child blueprint with the Dirichlet-series bound ending '... <= sum Lambda(n)/n^(3/2) < oo by vonMangoldtLSeriesSummable'. | verifier |
| 4 | verified | Line counts checked in copied file: parent proof L2834-2850 = 17 lines using 2 direct lemmas; strip child proof L2765 = 1 line (LogDerivZetaUniformLogSquaredBoundStrip.choose_spec.2); half-plane child L2786-2817 = 32 lines; chain parent(2831) -> StripSpec(2761) -> LogDerivZetaUniformLogSquaredBoundStrip(2603, obtain SumBoundII at 2608) -> SumBoundII(2435) = depth 3. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent (2831-2833), both child statements and closed_by match the copied code verbatim: StripSpec (2761-2765) is closed by LogDerivZetaUniformLogSquaredBoundStrip.choose_spec.2; half-plane child (2784-2817) by the 32-line proof ending in the simpa ... trans ... tsum_le_tsum line. Glue is exactly use max C1 C2 (2837) + by_cases hσ' : σ ≤ 3/2 (2839), each branch closing by one .trans to the child bound (2840, 2844). Parent uses exactly these two project lemmas (2834-2835); the only other named lemma used (Real.exp_one_lt_d9, 2849) is a Mathlib lemma, not a project lemma. Closes: grep finds no sorry/admit/axiom in the whole file except the #print axioms StrongPNT diagnostic (2906). Shape numbers correct: direct_lemmas=2, depth=3 (parent→StripSpec→LogDerivZetaUniformLogSquaredBoundStrip(2603)→SumBoundII(2435), each edge present), glue_lines=17 (2834-2850), child_lines=[1,32] (2765; 2786-2817). | reviewer-correctness |
| generality | accept | Move is stated generically: goal shape '∃ C>0, ∀x, P x → Q x ≤ C·g x' covered by two regional lemmas meeting at a boundary b, with use_when/avoid_when naming concrete, honest failure modes (gap between regions, non-dominated gauges, non-order boundary, non-transferable constant). Consequences are specific (by_cases/LEM exhaustiveness vs finite-disjunction; both branches close against the shared witness max C1 C2; the constant gauge must be lifted to log²|t| via 1≤log²|t|; failure mode if gauges don't dominate). It explicitly names what makes the children good bounded-prover leaves: self-contained, closing without reference back to the parent, and the parent only consuming their existential statements. The opinion is honest that the split itself is trivial and the generalizable detail is the split-point choice plus gauge domination. | reviewer-generality |
| provenance-licence | accept | check_provenance pass (1 file byte-identical at 2c476fa6441c607096d93c8fc7ac0a227a655dae); commit 2c476fa... consistent across entry.json, sources/pnt-and/source.json and SOURCE.md; licence Apache-2.0 consistent in entry.json/source.json/SOURCE.md and upstream-LICENSE is the Apache 2.0 text (not copyleft/nc/unknown); all 5 permalinks use the pinned commit; copied file 151072 bytes and sha256 f777e11c... match entry.json. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd at commit `2c476fa6441c607096d93c8fc7ac0a227a655dae`, under `Apache-2.0`; see the [source note](../../sources/pnt-and/SOURCE.md) for the licence text and attribution.
