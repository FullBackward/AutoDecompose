# Case-split at the prime 3 (the 3-5 switch) for Wiles semistable modularity

| | |
|---|---|
| Kind | instance |
| Move | case-split |
| Language | lean |
| Status | draft |
| Source | [flt-anthropic](../../sources/flt-anthropic/SOURCE.md) at `6e837e753555` |
| Licence | `Apache-2.0` |

## Intent

Reduce Wiles's semistable modularity theorem to a single case split on the mod-3 residual Galois representation `ρ̄_{W,3}`: each branch is then assembled from already-proved project lemmas (Langlands–Tunnell, modularity lifting, the 3-5 switch), with the ~35 lines of glue doing nothing but record-field extraction and two small `Nat` divisibility proofs.

## The decomposition

### parent `WeierstrassCurve.modularity_of_semistableModel'`: [`P2M/Sol/S_WeierstrassCurve_modularity_of_semistableModel.lean` lines 165-201](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_modularity_of_semistableModel.lean#L165-L201) ([local copy](code/P2M/Sol/S_WeierstrassCurve_modularity_of_semistableModel.lean))

```lean
theorem modularity_of_semistableModel' (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hW : W.IsSemistableModel) : (W.map (Int.castRingHom ℚ)).IsModular := by

  by_cases h3 : W.ModRepIsIrreducible 3
  ·

    obtain ⟨M₃, hM₃, hres₃, hcube₃, hns₃⟩ :=
      isResiduallyModular_three_and_noInertiaFixedTorsion_and_not_cube_dvd_of_isSemistableModel W hΔ hW h3
    haveI : NeZero M₃ := ⟨hM₃.ne'⟩
    exact isModular_map_of_mlc1
      (liftingAtConductor_three_of_level_hns 3 rfl W hΔ hW h3 M₃ hres₃ hns₃ hcube₃)
  ·

    have h5 : W.ModRepIsIrreducible 5 := (modThreeOrFiveIrreducible W hΔ hW).resolve_left h3

    obtain ⟨W', hΔ', hW', h3', hcong⟩ := threeFiveSwitchCurve W hΔ hW h5

    obtain ⟨M₃', hM₃', hres₃', hcube₃', hns₃'⟩ :=
      isResiduallyModular_three_and_noInertiaFixedTorsion_and_not_cube_dvd_of_isSemistableModel W' hΔ' hW' h3'
    haveI : NeZero M₃' := ⟨hM₃'.ne'⟩
    obtain ⟨N, hN0, hsq, hsupp, hmodN⟩ :=
      liftingAtConductor_three_of_level_hns 3 rfl W' hΔ' hW' h3' M₃' hres₃' hns₃' hcube₃'

    have hres5 : W.IsResiduallyModularOfLevel 5 N :=
      isResiduallyModularOfLevel_of_switch hmodN (fun ℓ hℓ h => (hsupp ℓ hℓ).mpr h) hcong

    have h25 : ¬ 5 ^ 2 ∣ N := by
      intro h
      have hu : IsUnit (5 : ℕ) := hsq 5 (by rwa [← pow_two])
      exact absurd (Nat.isUnit_iff.mp hu) (by decide)

    have hN3 : ∀ q : ℕ, q.Prime → q ≠ 5 → ¬ q ^ 3 ∣ N := fun q hq _ h =>
      hq.ne_one (Nat.isUnit_iff.mp (hsq q ((Dvd.intro q (by ring)).trans h)))
    haveI : NeZero N := ⟨hN0.ne'⟩

    exact isModular_map_of_mlc1
      (liftingAtConductor_threeFive_of_level_not_sq_dvd 5 (Or.inr rfl) W hΔ hW h5 N hres5 h25 hN3)
```

### child `WeierstrassCurve.isResiduallyModular_three_and_noInertiaFixedTorsion_and_not_cube_dvd_of_isSemistableModel`: [`Theorems/Thm_WeierstrassCurve_isResiduallyModular_three_and_noInertiaFixedTorsion_and_not_cube_dvd_of_isSemistableModel.lean` lines 57-66](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_WeierstrassCurve_isResiduallyModular_three_and_noInertiaFixedTorsion_and_not_cube_dvd_of_isSemistableModel.lean#L57-L66) ([local copy](code/Theorems/Thm_WeierstrassCurve_isResiduallyModular_three_and_noInertiaFixedTorsion_and_not_cube_dvd_of_isSemistableModel.lean))

```lean
theorem WeierstrassCurve.isResiduallyModular_three_and_noInertiaFixedTorsion_and_not_cube_dvd_of_isSemistableModel
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel)
    (h3 : W.ModRepIsIrreducible 3) :
    ∃ M : ℕ, 0 < M ∧ W.IsResiduallyModularOfLevel 3 M ∧
      (∀ q : ℕ, q.Prime → q ≠ 3 → ¬ q ^ 3 ∣ M) ∧
      (3 ^ 2 ∣ M →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 3 →
          ∀ x : Submodule.torsionBy ℤ
              ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point (3 : ℕ),
            (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x) → x = 0) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_isResiduallyModular_three_and_noInertiaFixedTorsion_and_not_cube_dvd_of_isSemistableModel.solution
```

### child `WeierstrassCurve.isModular_map_of_mlc1`: [`P2M/Sol/S_WeierstrassCurve_modularity_of_semistableModel.lean` lines 160-163](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_modularity_of_semistableModel.lean#L160-L163) ([local copy](code/P2M/Sol/S_WeierstrassCurve_modularity_of_semistableModel.lean))

```lean
theorem isModular_map_of_mlc1 {W : WeierstrassCurve ℤ} (h : Mlc1IsModularModelOfExactConductorLevel W) :
    (W.map (Int.castRingHom ℚ)).IsModular :=
  isModular_map_of_isModularModel
    (IsModularModelOfExactConductorLevel.isModularModelOfConductorLevel h).isModularModel
```

### child `WeierstrassCurve.liftingAtConductor_three_of_level_hns`: [`P2M/Sol/S_WeierstrassCurve_modularity_of_semistableModel.lean` lines 142-151](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_modularity_of_semistableModel.lean#L142-L151) ([local copy](code/P2M/Sol/S_WeierstrassCurve_modularity_of_semistableModel.lean))

```lean
theorem liftingAtConductor_three_of_level_hns (p : ℕ) (hp : p = 3)
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel) (hirr : W.ModRepIsIrreducible p)
    (M₀ : ℕ) [NeZero M₀] (hres₀ : W.IsResiduallyModularOfLevel p M₀)
    (hns : p ^ 2 ∣ M₀ →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ x : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p,
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x) → x = 0)
    (hM₀3 : ∀ q : ℕ, q.Prime → q ≠ p → ¬ q ^ 3 ∣ M₀) :
    Mlc1IsModularModelOfExactConductorLevel W :=
  modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd p hp W hΔ hW hirr M₀ hres₀ hns hM₀3
```

### child `WeierstrassCurve.modThreeOrFiveIrreducible`: [`Theorems/Thm_WeierstrassCurve_modThreeOrFiveIrreducible.lean` lines 15-15](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_WeierstrassCurve_modThreeOrFiveIrreducible.lean#L15-L15) ([local copy](code/Theorems/Thm_WeierstrassCurve_modThreeOrFiveIrreducible.lean))

```lean
theorem WeierstrassCurve.modThreeOrFiveIrreducible (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel) : W.ModRepIsIrreducible 3 ∨ W.ModRepIsIrreducible 5 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_modThreeOrFiveIrreducible.solution
```

### child `WeierstrassCurve.threeFiveSwitchCurve`: [`Theorems/Thm_WeierstrassCurve_threeFiveSwitchCurve.lean` lines 16-16](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_WeierstrassCurve_threeFiveSwitchCurve.lean#L16-L16) ([local copy](code/Theorems/Thm_WeierstrassCurve_threeFiveSwitchCurve.lean))

```lean
theorem WeierstrassCurve.threeFiveSwitchCurve (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel) (h5 : W.ModRepIsIrreducible 5) : ∃ W' : WeierstrassCurve ℤ, W'.Δ ≠ 0 ∧ W'.IsSemistableModel ∧ W'.ModRepIsIrreducible 3 ∧ ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → W'.IsGoodPrimeFor ℓ → ℓ ≠ 5 → (5 : ℤ) ∣ (W'.apOfModel ℓ - W.apOfModel ℓ) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_threeFiveSwitchCurve.solution
```

### child `WeierstrassCurve.isResiduallyModularOfLevel_of_switch`: [`Theorems/Thm_WeierstrassCurve_isResiduallyModularOfLevel_of_switch.lean` lines 5-10](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_WeierstrassCurve_isResiduallyModularOfLevel_of_switch.lean#L5-L10) ([local copy](code/Theorems/Thm_WeierstrassCurve_isResiduallyModularOfLevel_of_switch.lean))

```lean
theorem WeierstrassCurve.isResiduallyModularOfLevel_of_switch {W W' : WeierstrassCurve ℤ} {N : ℕ}
    (hmod : W'.IsModularModelOfLevel N)
    (hND : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ W'.Δ → ℓ ∣ N)
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → W'.IsGoodPrimeFor ℓ → ℓ ≠ 5 →
      (5 : ℤ) ∣ (W'.apOfModel ℓ - W.apOfModel ℓ)) :
    W.IsResiduallyModularOfLevel 5 N := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_isResiduallyModularOfLevel_of_switch.solution
```

### child `WeierstrassCurve.liftingAtConductor_threeFive_of_level_not_sq_dvd`: [`P2M/Sol/S_WeierstrassCurve_modularity_of_semistableModel.lean` lines 153-158](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_modularity_of_semistableModel.lean#L153-L158) ([local copy](code/P2M/Sol/S_WeierstrassCurve_modularity_of_semistableModel.lean))

```lean
theorem liftingAtConductor_threeFive_of_level_not_sq_dvd (p : ℕ) (hp : p = 3 ∨ p = 5)
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel) (hirr : W.ModRepIsIrreducible p)
    (M₀ : ℕ) [NeZero M₀] (hres₀ : W.IsResiduallyModularOfLevel p M₀) (hM₀ : ¬ p ^ 2 ∣ M₀)
    (hM₀3 : ∀ q : ℕ, q.Prime → q ≠ p → ¬ q ^ 3 ∣ M₀) :
    Mlc1IsModularModelOfExactConductorLevel W :=
  modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd p hp W hΔ hW hirr M₀ hres₀ hM₀ hM₀3
```

### context `WeierstrassCurve.modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd`: [`Theorems/Thm_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd.lean` lines 120-129](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd.lean#L120-L129) ([local copy](code/Theorems/Thm_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd.lean))

```lean
theorem WeierstrassCurve.modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd (p : ℕ) (hp : p = 3)
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel) (hirr : W.ModRepIsIrreducible p)
    (M₀ : ℕ) [NeZero M₀] (hres₀ : W.IsResiduallyModularOfLevel p M₀)
    (hns : p ^ 2 ∣ M₀ →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ x : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p,
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x) → x = 0)

    (hM₀3 : ∀ q : ℕ, q.Prime → q ≠ p → ¬ q ^ 3 ∣ M₀) :
    Mlc1IsModularModelOfExactConductorLevel W := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd.solution
```

### context `PROOF-PATH step 4 modularity`: [`PROOF-PATH.md` lines 39-64](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md#L39-L64) ([local copy](code/PROOF-PATH.md))

```markdown
**4. Modularity.** `FreyPackage.frey_isModular` follows from `WeierstrassCurve.modularity_of_semistableModel`: every
integral Weierstrass model with Δ ≠ 0 and no prime dividing both Δ and c₄ (`IsSemistableModel`) is modular
(`IsModular`: a_ℓ matches a normalised weight-2 eigenform on some Γ₀(N) at good primes; both in
`Definitions/Def_FLTPrelim_Modularity.lean`; cusp forms, Γ₀(N) and q-expansions are Mathlib's). The proof is Wiles's:
- one of ρ̄_{W,3}, ρ̄_{W,5} is irreducible (`WeierstrassCurve.modThreeOrFiveIrreducible`: if both were reducible W would
  have a rational 15-isogeny, and `WeierstrassCurve.fifteenIsogenyClassification` pins c₄³/Δ of such a curve to one of
  four values, none of which a semistable model can have);
- Langlands-Tunnell in the weight-2, level-conditioned form Wiles uses,
  `WeierstrassCurve.isResiduallyModular_three_and_noInertiaFixedTorsion_and_not_cube_dvd_of_isSemistableModel`: a
  weight-one form for the odd octahedral representation lifting ρ̄_{W,3}
  (`LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_eq_trace_lift`, for surjective ρ̄₃ with cyclotomic determinant,
  by Tunnell's argument: monomial automorphy over the subfields cut out by subgroups of GL₂(F₃), cyclic base change,
  a converse theorem with Rankin-Selberg integrals), then multiplication by the Eisenstein series E₁(1, χ₋₃) and a
  Deligne-Serre lifting lemma to reach a congruent weight-2 eigenform;
- two modularity lifting theorems, R = T by Taylor-Wiles patching in Diamond's formulation
  (`GaloisRep.DeformationRingData`, `CuspForm.HeckeGaloisRepDatum`, `Algebra.PatchingDatum`,
  `GaloisRep.DeformationRingData.exists_surjective_algHom_of_heckeGaloisRepDatum`):
  `WeierstrassCurve.modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd`
  (p = 3; a condition on inertia-fixed 3-torsion when 9 divides the residual level) and
  `WeierstrassCurve.modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd` (p ∈ {3, 5}; p² not
  dividing the residual level);
- the 3-5 switch `WeierstrassCurve.threeFiveSwitchCurve` (a second semistable model W′ with ρ̄_{W′,3} irreducible and
  a_ℓ(W′) ≡ a_ℓ(W) (mod 5) at common good primes ℓ ≠ 5, built beneath from a curve with W′[5] ≅ W[5] taken from an
  explicit family in the `RubinSilverberg` namespace) and `WeierstrassCurve.isResiduallyModularOfLevel_of_switch`.
If ρ̄_{W,3} is irreducible, Langlands-Tunnell and lifting at 3; otherwise the switch gives W′, the first case makes
W′ modular, W is residually modular mod 5, and lifting at 5 finishes.
```

How the parts fit. The parent is a `by_cases h3 : W.ModRepIsIrreducible 3` split — the 3-5 switch — with exactly two branches.

Branch 1 (`h3` holds, lines 168-175). `isResiduallyModular_three_and_noInertiaFixedTorsion_and_not_cube_dvd_of_isSemistableModel` supplies a residual level `M₃` with its level conditions (`hres₃`, `hcube₃`, `hns₃`); `liftingAtConductor_three_of_level_hns` turns that into a `Mlc1IsModularModelOfExactConductorLevel W`; `isModular_map_of_mlc1` converts it to the goal `(W.map …).IsModular`. The only glue is a `NeZero M₃` instance.

Branch 2 (`¬ h3`, lines 176-201). `modThreeOrFiveIrreducible` yields `h5 : W.ModRepIsIrreducible 5` (its `.resolve_left h3` discharges the `∨`). `threeFiveSwitchCurve` produces a second semistable model `W'` with `ρ̄_{W',3}` irreducible and traces congruent mod 5 at every common good prime `ℓ ≠ 5`. Branch 1's argument is re-run on `W'` (`isResiduallyModular_three_…`, then `liftingAtConductor_three_of_level_hns`) to get a modular model at a level `N`; `isResiduallyModularOfLevel_of_switch` transfers residual modularity back to `W` at level 5; two local `have`s (`h25 : ¬ 5² ∣ N`, `hN3 : ∀ q, q ≠ 5 → ¬ q³ ∣ N`) close the level conditions; `liftingAtConductor_threeFive_of_level_not_sq_dvd` and `isModular_map_of_mlc1` finish.

Lemma graph (text). `modularity_of_semistableModel'` uses directly: `isResiduallyModular_three_and_noInertiaFixedTorsion_and_not_cube_dvd_of_isSemistableModel`, `isModular_map_of_mlc1`, `liftingAtConductor_three_of_level_hns`, `modThreeOrFiveIrreducible`, `threeFiveSwitchCurve`, `isResiduallyModularOfLevel_of_switch`, `liftingAtConductor_threeFive_of_level_not_sq_dvd`. Below them: `liftingAtConductor_three_of_level_hns` uses `modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd` (the context site), whose proof is `P2M.Sol.S_…_solution`; `isModular_map_of_mlc1` uses `isModular_map_of_isModularModel`.

Why each child is a good leaf. Every child is a self-contained statement — an `∃`-witness with all side conditions (`isResiduallyModular_three_…`, `threeFiveSwitchCurve`), a disjunction (`modThreeOrFiveIrreducible`), or a record `Mlc1IsModularModelOfExactConductorLevel` — whose proof closes on its own: the four `Theorems/` children are one-line wrappers `by p2m_exact_reverting @…solution` over a `P2M.Sol` proof, and the three same-file children are one-line applications of a deeper project lemma. None of the deep mathematics leaks into the glue, so the parent is a pure skeleton over named holes.

## Why it is good

1. (*check*) The parent closes as a two-branch `by_cases h3 : W.ModRepIsIrreducible 3`, and each branch ends in `exact isModular_map_of_mlc1 (liftingAtConductor_…)` — no other closing tactic (lines 165-201).
2. (*measurement*) The main proof (lines 167-201) is 35 lines, invokes 7 distinct named lemmas (10 invocations), and its only local proofs are two `have`s of `Nat` divisibility/unit bookkeeping (`h25`, `hN3`).
3. (*author-statement*) PROOF-PATH.md step 4 ends with the exact two-branch plan: "If ρ̄_{W,3} is irreducible, Langlands-Tunnell and lifting at 3; otherwise the switch gives W′, … lifting at 5 finishes" (PROOF-PATH.md lines 63-64).
4. (*check*) A chain of three project lemmas lies below the main theorem: `modularity_of_semistableModel'` → `liftingAtConductor_three_of_level_hns` → `modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd` → its `P2M.Sol` solution.
5. (*known-use*) The same-file `solution` theorem (lines 208-210) reuses `modularity_of_semistableModel'` unchanged, so this is exactly the step the top-level FLT proof plugs into.

In my opinion the detail worth copying is the *symmetric* second branch: rather than reproving modularity at 5 from scratch, the switch lemma re-enters branch 1's argument at 3 and transfers it back via a trace congruence. That is what keeps 35 lines of glue sufficient for a theorem this deep.

## When to use it, and when not

Use it when a universal statement over some structure forks on a decidable property at a fixed small prime, and both alternatives are already proved as standalone project lemmas; when one branch can be reduced to the other by a "switch" construction that hands over a second object and a congruence of traces; and when the remaining glue is only record-field extraction and small divisibility conditions. Avoid it when the branch lemmas do not exist yet — here each is a deep theorem (Langlands–Tunnell, Taylor-Wiles `R = T` lifting, the Rubin–Silverberg switch), so the split is a roadmap over holes rather than a proof you can fill in directly; when the disjunction is not decidable (the exhaustiveness would then be its own child); or when the two branches need genuinely different arguments that no switch lemma can bridge.

## Consequences

The split creates exactly two obligations (`h3` and `¬h3`) and no separate exhaustiveness child: `by_cases` discharges exhaustiveness via excluded middle on the decidable `Prop` `W.ModRepIsIrreducible 3` (a `mod_cases` residue split, by contrast, needs an exhaustiveness proof). Each branch must produce a `Mlc1IsModularModelOfExactConductorLevel` for `isModular_map_of_mlc1`, which forces the glue to carry a residual level and its conditions — the two local `have`s (`h25`, `hN3`) and the two `NeZero` instances are exactly those obligations. The branches are symmetric only because `threeFiveSwitchCurve` carries the mod-5 congruence at every common good prime `ℓ ≠ 5`; if that congruence were missing, the `isResiduallyModularOfLevel_of_switch` call would not typecheck.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/anthropics/fermats-last-theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, under `Apache-2.0`; see the [source note](../../sources/flt-anthropic/SOURCE.md) for the licence text and attribution.
