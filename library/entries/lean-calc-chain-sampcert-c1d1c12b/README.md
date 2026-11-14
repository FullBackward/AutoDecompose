# Normalizing the discrete Gaussian sampler loop by a chain of rewrites

| | |
|---|---|
| Kind | instance |
| Move | calc-chain |
| Language | lean |
| Status | accepted |
| Source | [sampcert](../../sources/sampcert/SOURCE.md) at `a2c53bb5ff79` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T15:48:35Z |

## Intent

Prove that the discrete Gaussian sampler loop is a proper distribution (its
mass sums to 1) by a chain of rewrites: replace the mixed Laplace sampler by
its equivalence, drop the two off-diagonal `if`-guarded masses with the
same-file `ite_simpl` lemmas, fold the Boolean sum with the Bernoulli
normalization lemma, and close the remaining factor with the Laplace
normalization lemma.

## The decomposition

### parent `DiscreteGaussianSampleLoop_normalizes`: [`SampCert/Samplers/Gaussian/Properties.lean` lines 60-91](https://github.com/leanprover/sampcert/blob/a2c53bb5ff790e729e252958060699b7eff898b9/SampCert/Samplers/Gaussian/Properties.lean#L60-L91) ([local copy](code/SampCert/Samplers/Gaussian/Properties.lean))

```lean
theorem DiscreteGaussianSampleLoop_normalizes (num den t : ℕ+) (mix : ℕ) :
  ∑' x, (DiscreteGaussianSampleLoop num den t mix) x = 1 := by
  simp only [DiscreteGaussianSampleLoop, Bind.bind, Int.natCast_natAbs, Pure.pure, SLang.bind_apply,
    SLang.pure_apply, tsum_bool, ENNReal.tsum_prod', Prod.mk.injEq, mul_ite, mul_one, mul_zero,
    and_true, and_false, ↓reduceIte, add_zero, zero_add, Bool.false_eq_true, Bool.true_eq_false,
    and_false]
  rw [DiscreteLaplaceSampleMixed_equiv]
  conv =>
    left
    arg 1
    ext a
    congr
    . rw [ENNReal.tsum_eq_add_tsum_ite a]
      right
      arg 1
      ext x
      rw [ite_simpl_gaussian_1]
    . rw [ENNReal.tsum_eq_add_tsum_ite a]
      right
      arg 1
      ext x
      rw [ite_simpl_gaussian_2]
  simp only [↓reduceIte, tsum_zero, add_zero]
  conv =>
    left
    arg 1
    ext a
    rw [← mul_add]
    rw [← tsum_bool]
    rw [BernoulliExpNegSample_normalizes]
  simp only [mul_one]
  rw [DiscreteLaplaceSample_normalizes]
```

### child `DiscreteLaplaceSampleMixed_equiv`: [`SampCert/Samplers/Laplace/Properties.lean` lines 1103-1109](https://github.com/leanprover/sampcert/blob/a2c53bb5ff790e729e252958060699b7eff898b9/SampCert/Samplers/Laplace/Properties.lean#L1103-L1109) ([local copy](code/SampCert/Samplers/Laplace/Properties.lean))

```lean
lemma DiscreteLaplaceSampleMixed_equiv (num den : PNat) (mix : ℕ) :
    DiscreteLaplaceSampleMixed num den mix = DiscreteLaplaceSample num den := by
  rw [DiscreteLaplaceSampleMixed]
  split
  · rfl
  · symm
    apply DiscreteLaplaceSample_equiv
```

### child `ite_simpl_gaussian_1`: [`SampCert/Samplers/Gaussian/Properties.lean` lines 28-40](https://github.com/leanprover/sampcert/blob/a2c53bb5ff790e729e252958060699b7eff898b9/SampCert/Samplers/Gaussian/Properties.lean#L28-L40) ([local copy](code/SampCert/Samplers/Gaussian/Properties.lean))

```lean
lemma ite_simpl_gaussian_1 (num den t: ℕ+) (x a : ℤ) :
  @ite ENNReal (x = a) (propDecidable (x = a)) 0
  (if a = x then
    DiscreteLaplaceSample t 1 x *
      BernoulliExpNegSample (Int.natAbs (Int.sub (|x| * ↑↑t * ↑↑den) ↑↑num) ^ 2) (2 * num * t ^ 2 * den) false
  else 0) = 0 := by
  split
  · simp
  · split
    · rename_i h1 h2
      subst h2
      contradiction
    · simp
```

### child `ite_simpl_gaussian_2`: [`SampCert/Samplers/Gaussian/Properties.lean` lines 42-54](https://github.com/leanprover/sampcert/blob/a2c53bb5ff790e729e252958060699b7eff898b9/SampCert/Samplers/Gaussian/Properties.lean#L42-L54) ([local copy](code/SampCert/Samplers/Gaussian/Properties.lean))

```lean
lemma ite_simpl_gaussian_2 (num den t: ℕ+) (x a : ℤ) :
  @ite ENNReal (x = a) (propDecidable (x = a)) 0
  (if a = x then
    DiscreteLaplaceSample t 1 x *
      BernoulliExpNegSample (Int.natAbs (Int.sub (|x| * ↑↑t * ↑↑den) ↑↑num) ^ 2) (2 * num * t ^ 2 * den) true
  else 0) = 0 := by
  split
  · simp
  · split
    · rename_i h1 h2
      subst h2
      contradiction
    · simp
```

### child `BernoulliExpNegSample_normalizes`: [`SampCert/Samplers/BernoulliNegativeExponential/Properties.lean` lines 1148-1169](https://github.com/leanprover/sampcert/blob/a2c53bb5ff790e729e252958060699b7eff898b9/SampCert/Samplers/BernoulliNegativeExponential/Properties.lean#L1148-L1169) ([local copy](code/SampCert/Samplers/BernoulliNegativeExponential/Properties.lean))

```lean
theorem BernoulliExpNegSample_normalizes (num : Nat) (den : PNat) :
  (∑' b : Bool, (BernoulliExpNegSample num den) b) = 1 := by
  unfold BernoulliExpNegSample
  split
  · rename_i h
    have A := BernoulliExpNegSampleUnit_normalizes num den h ((num : NNReal) / (den : NNReal)) rfl
    simp at *
    rw [A]
  · rename_i h
    simp
    rw [← add_assoc, ← mul_add]
    have e1 : ENNReal.ofReal (Real.exp (-(((num % (den : ℕ) : ℕ) : ℝ) / ((den : ℕ) : ℝ)))) +
        (1 - ENNReal.ofReal (Real.exp (-(((num % (den : ℕ) : ℕ) : ℝ) / ((den : ℕ) : ℝ))))) = 1 := by
      rw [add_comm]
      exact tsub_add_cancel_of_le
        (ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (by
          rw [neg_nonpos]; positivity)))
    rw [e1, mul_one]
    have B := BernoulliExpNegSampleGenLoop_normalizes (num / den)
    rw [tsum_bool] at B
    rw [add_comm]
    exact B
```

### child `DiscreteLaplaceSample_normalizes`: [`SampCert/Samplers/Laplace/Properties.lean` lines 420-454](https://github.com/leanprover/sampcert/blob/a2c53bb5ff790e729e252958060699b7eff898b9/SampCert/Samplers/Laplace/Properties.lean#L420-L454) ([local copy](code/SampCert/Samplers/Laplace/Properties.lean))

```lean
theorem DiscreteLaplaceSample_normalizes (num den : PNat) :
    ∑' x : ℤ, (DiscreteLaplaceSample num den) x = 1 := by
  have hloop_norm := DiscreteLaplaceSampleLoop_normalizes num den
  simp only [DiscreteLaplaceSample, Bind.bind, not_and, Pure.pure, SLang.bind_apply]
  simp_rw [probUntil_apply_norm _ _ _ hloop_norm, ENNReal.tsum_prod']
  rw [ENNReal.tsum_comm]
  conv =>
    left
    arg 1
    intro b
    rw [ENNReal.tsum_comm]
  simp only [decide_eq_true_eq, tsum_bool, forall_true_left, ite_not, ite_mul, zero_mul,
    SLang.pure_apply, mul_ite, mul_one, mul_zero, tsum_ite_eq]
  have hfactor : ∀ a : ℕ, (if a = 0 then (0 : ENNReal)
      else DiscreteLaplaceSampleLoop num den (true, a) *
        ((∑' b : ℕ, if false = true → ¬b = 0 then DiscreteLaplaceSampleLoop num den (false, b) else 0)
          + ∑' b : ℕ, if b = 0 then 0 else DiscreteLaplaceSampleLoop num den (true, b))⁻¹)
      = (if a = 0 then 0 else DiscreteLaplaceSampleLoop num den (true, a)) *
        ((∑' b : ℕ, if false = true → ¬b = 0 then DiscreteLaplaceSampleLoop num den (false, b) else 0)
          + ∑' b : ℕ, if b = 0 then 0 else DiscreteLaplaceSampleLoop num den (true, b))⁻¹ := by
    intro a; by_cases h : a = 0 <;> simp [h]
  conv => left; right; arg 1; intro a; rw [hfactor]
  simp only [Bool.false_eq_true, false_imp_iff, ↓reduceIte]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, ← add_mul]
  rw [ENNReal.mul_inv_cancel]
  · simp only [DiscreteLaplaceSampleLoop_apply, ne_eq, add_eq_zero, ENNReal.tsum_eq_zero,
      _root_.mul_eq_zero, pow_eq_zero_iff', ENNReal.ofReal_eq_zero, tsub_eq_zero_iff_le,
      ENNReal.one_le_ofReal, one_le_exp_iff, Left.nonneg_neg_iff, ENNReal.inv_eq_zero,
      ENNReal.natCast_ne_top, or_false, ite_eq_left_iff, not_and, not_forall, exists_prop]
    intro _
    exact ⟨1, by simp [exp_pos]⟩
  · refine ne_of_lt (lt_of_le_of_lt ?_ (by simp : (∑' (x : Bool × ℕ), DiscreteLaplaceSampleLoop num den x) < ⊤))
    rw [← ENNReal.tsum_add, ENNReal.tsum_prod', ENNReal.tsum_comm]
    simp_rw [tsum_bool]
    exact ENNReal.tsum_le_tsum fun a => by split_ifs <;> simp
```

How the parts fit. The parent is a chain of rewrites on the sum
`∑' x, (DiscreteGaussianSampleLoop num den t mix) x`. After the opening `simp`
unfolds `DiscreteGaussianSampleLoop` and its `bind`, the sum is a `ℤ`-indexed
Laplace factor times a two-point `Bool`-indexed Bernoulli factor, plus two
`if`-guarded masses that vanish off the diagonal `a = x`. The glue then runs
five one-step rewrites, each closed by one named lemma:

1. `rw [DiscreteLaplaceSampleMixed_equiv]` (line 66) replaces the mixed
   Laplace sampler by the plain one;
2. a `conv` block splits the sum at `a` and rewrites the two off-diagonal
   masses by `ite_simpl_gaussian_1` (line 76) and `ite_simpl_gaussian_2`
   (line 81);
3. `rw [← mul_add, ← tsum_bool, BernoulliExpNegSample_normalizes]` (lines
   88-89) folds the two `Bool` branches into one factor equal to 1;
4. `rw [DiscreteLaplaceSample_normalizes]` (line 91) closes the remaining
   `ℤ` sum to 1.

The lemma graph (which lemma uses which, in text):

```
DiscreteGaussianSampleLoop_normalizes
├── DiscreteLaplaceSampleMixed_equiv ──→ DiscreteLaplaceSample_equiv
├── ite_simpl_gaussian_1            (leaf: split/simp/subst/contradiction)
├── ite_simpl_gaussian_2            (leaf: split/simp/subst/contradiction)
├── BernoulliExpNegSample_normalizes
│     ├── BernoulliExpNegSampleUnit_normalizes ──→ BernoulliExpNegSampleUnitAux_normalizes
│     └── BernoulliExpNegSampleGenLoop_normalizes
└── DiscreteLaplaceSample_normalizes
      └── DiscreteLaplaceSampleLoop_normalizes
            └── BernoulliExpNegSample_normalizes (shared with the parent's own child)
```

Why each child is a good leaf:

- `DiscreteLaplaceSampleMixed_equiv` is a one-line bridge between two
  definitions, closed by `rw [DiscreteLaplaceSampleMixed]` and the existing
  `DiscreteLaplaceSample_equiv`; its statement (`=`) carries no hypothesis.
- `ite_simpl_gaussian_1` and `ite_simpl_gaussian_2` are self-contained: their
  statements name no sibling, and their proofs close on `split`, `simp`,
  `subst` and `contradiction` alone.
- `BernoulliExpNegSample_normalizes` is the Bernoulli sampler's own
  normalization fact, stated independently of the Gaussian loop, so it is
  reusable here and in `DiscreteLaplaceSampleLoop_normalizes` (line 278).
- `DiscreteLaplaceSample_normalizes` is the Laplace sampler's own
  normalization, stated independently; the Gaussian loop inherits it rather
  than re-proving it.

## Why it is good

1. The parent `DiscreteGaussianSampleLoop_normalizes` is declared at
   `SampCert/Samplers/Gaussian/Properties.lean`, lines 60-91 (check:
   `declared`; [permalink](https://github.com/leanprover/sampcert/blob/a2c53bb5ff790e729e252958060699b7eff898b9/SampCert/Samplers/Gaussian/Properties.lean#L60-L91)).
2. The parent site cites `DiscreteLaplaceSample_normalizes` (check: `cites`;
   [line 91](https://github.com/leanprover/sampcert/blob/a2c53bb5ff790e729e252958060699b7eff898b9/SampCert/Samplers/Gaussian/Properties.lean#L91)).
3. The decomposition has 5 direct lemmas; the glue is 32 lines
   (Gaussian/Properties.lean 60-91); the five children are 7, 13, 13, 22 and
   35 lines (declaration to last proof line, inclusive); the longest checked
   chain of project lemmas below the parent is 5 deep
   (`DiscreteGaussianSampleLoop_normalizes → DiscreteLaplaceSample_normalizes
   → DiscreteLaplaceSampleLoop_normalizes → BernoulliExpNegSample_normalizes
   → BernoulliExpNegSampleUnit_normalizes →
   BernoulliExpNegSampleUnitAux_normalizes`) (measurement; counted by reading
   the copied files).
4. The same-file closed-form theorem `DiscreteGaussianSample_apply` consumes
   this normalization lemma: at [line 245](https://github.com/leanprover/sampcert/blob/a2c53bb5ff790e729e252958060699b7eff898b9/SampCert/Samplers/Gaussian/Properties.lean#L245) it takes
   `have A := DiscreteGaussianSampleLoop_normalizes (num ^ 2) (den ^ 2) …` and
   feeds `A` to `probUntil_apply_norm` at line 252 (known-use).
5. The file states the theorem's purpose in a doc comment: "Gaussian sampling
   attempt is a proper distribution." (line 57) (author-statement;
   [lines 56-58](https://github.com/leanprover/sampcert/blob/a2c53bb5ff790e729e252958060699b7eff898b9/SampCert/Samplers/Gaussian/Properties.lean#L56-L58)).

In my opinion the detail worth copying is the two-step `conv` block: it splits
the sum at `a` and kills each off-diagonal mass with a dedicated `ite_simpl`
lemma, so the two normalization lemmas only ever meet the clean, on-diagonal
factor.

## When to use it, and when not

Use it when the goal is a sum over a product space that factors into
components whose normalization lemmas already exist (`Bernoulli`,
`Laplace`), so each simplification step is exactly one `rw` to a named lemma.
Use it when the off-diagonal terms are `if`-expressions a small `ite_simpl`
lemma can kill, and when a `conv` block can reach the exact subterm to
rewrite.

Avoid it when a step needs several lemmas at once or a `have` sub-proof (then
the child is not a one-line rewrite); when the normalizer lemmas carry
mismatched hypotheses (here both need only `PNat`/`ℕ` arguments); or when a
factor needs its own non-trivial bound rather than an already-proved `= 1`.

## Consequences

The chain creates four obligations, each discharged by one named lemma: bridge
the two definitions of the Laplace sampler (`DiscreteLaplaceSampleMixed_equiv`);
show two off-diagonal `if`-guarded masses are zero (`ite_simpl_gaussian_1`,
`ite_simpl_gaussian_2`); fold a two-point Boolean sum to 1
(`BernoulliExpNegSample_normalizes`); close the remaining `ℤ` sum
(`DiscreteLaplaceSample_normalizes`).

Failure modes: the `ite_simpl` lemmas match the exact `@ite` shape of the
unfolded sampler, so a change to the sampler definition or to the `simp`
normal form breaks the `rw`; the `conv` blocks target a fixed position
(`arg 1; ext a`), so reordering the sum or the product factors moves the
target and each `rw` lands on the wrong subterm.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/lean_build.yml (leanprover/lean-action@v1 runs lake build on the whole project incl. SampCert/Samplers/Gaussian/Properties.lean; triggers on push to main); pinned commit a2c53bb5ff790e729e252958060699b7eff898b9 is the head of default branch main | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: DiscreteLaplaceSampleMixed_equiv@SampCert/Samplers/Gaussian/Properties.lean:66, ite_simpl_gaussian_1@SampCert/Samplers/Gaussian/Properties.lean:76, ite_simpl_gaussian_2@SampCert/Samplers/Gaussian/Properties.lean:81, BernoulliExpNegSample_normalizes@SampCert/Samplers/Gaussian/Properties.lean:89, DiscreteLaplaceSample_normalizes@SampCert/Samplers/Gaussian/Properties.lean:91; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 3 file(s) byte-identical at a2c53bb5ff790e729e252958060699b7eff898b9 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(DiscreteGaussianSampleLoop_normalizes, SampCert/Samplers/Gaussian/Properties.lean, 60-91) -> declared: DiscreteGaussianSampleLoop_normalizes is declared at SampCert/Samplers/Gaussian/Properties.lean:60 | check_claims.py |
| 2 | verified | cites(parent, DiscreteLaplaceSample_normalizes) -> cites: DiscreteLaplaceSample_normalizes occurs at SampCert/Samplers/Gaussian/Properties.lean:91 | check_claims.py |
| 3 | verified | parent 60-91 = 32 lines (sed 60-91); 5 children with spans 1103-1109=7, 28-40=13, 42-54=13, 1148-1169=22, 420-454=35 (sed confirms declarations/last proof lines); depth chain 5 edges: parent:91 -> DiscreteLaplaceSample_normalizes (claim2), Laplace:422 -> DiscreteLaplaceSampleLoop_normalizes, Laplace:278 (inside DiscreteLaplaceSampleLoop_normalizes decl at :250) -> BernoulliExpNegSample_normalizes, Bernoulli:1153 -> BernoulliExpNegSampleUnit_normalizes, Bernoulli:1095 -> BernoulliExpNegSampleUnitAux_normalizes (grep -n) | verifier |
| 4 | verified | Gaussian/Properties.lean:245 have A := DiscreteGaussianSampleLoop_normalizes (num ^ 2) (den ^ 2) (↑num / ↑den : ℕ).succPNat mix; :252 rw [probUntil_apply_norm _ _ _ A] | verifier |
| 5 | verified | Gaussian/Properties.lean:57 doc comment 'Gaussian sampling attempt is a proper distribution.' (lines 56-58 /-- ... -/) | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent DiscreteGaussianSampleLoop_normalizes is at Gaussian/Properties.lean 60-91 (glue 32 lines); the glue cites exactly the five named children (DiscreteLaplaceSampleMixed_equiv L66, ite_simpl_gaussian_1 L76, ite_simpl_gaussian_2 L81, BernoulliExpNegSample_normalizes L89, DiscreteLaplaceSample_normalizes L91) and closes with rw [DiscreteLaplaceSample_normalizes] after simp [mul_one] (no sorry). Each child statement and closed_by reproduce the copied code verbatim. Shape numbers correct: direct_lemmas=5, child_lines=[7,13,13,22,35] match spans 1103-1109/28-40/42-54/1148-1169/420-454, depth=5 confirmed by the cited chain L91->L422->L278->L1153->L1095. | reviewer-correctness |
| generality | accept | Move is stated generally via applicability.goal_shape (sum over a bind of two primitive samplers; chain of rewrites i-iv) and README 'When to use it, and when not' (product space whose component normalization lemmas exist; each step one rw to a named lemma). 'Avoid when' and consequences are honest and specific: mismatched hypotheses, a step needing several lemmas/have sub-proof, a factor needing a non-trivial bound; failure modes match the copied code (ite_simpl lemmas match exact @ite shape; conv blocks fix arg 1; ext a). Good-leaf section explicitly says what makes lemmas bounded-prover-friendly (self-contained, no sibling in statement, close on split/simp/subst/contradiction; Bernoulli/Laplace normalization stated independently and reused). Verified reuse at Laplace/Properties.lean:278 and known-use at Gaussian/Properties.lean:245,252. | reviewer-generality |
| provenance-licence | accept | Provenance check passes: all 3 copied files byte-identical at pinned commit a2c53bb5ff790e729e252958060699b7eff898b9; file bytes (12473/39431/40190) match entry.json. Commit, licence (Apache-2.0) and every permalink in entry.json and README.md use the same pinned commit and match sources/sampcert/source.json and SOURCE.md; upstream-LICENSE is the Apache-2.0 text. Source note present with licence text and attribution; everything traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover/sampcert at commit `a2c53bb5ff790e729e252958060699b7eff898b9`, under `Apache-2.0`; see the [source note](../../sources/sampcert/SOURCE.md) for the licence text and attribution.
