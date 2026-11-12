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

TODO: one or two sentences on what this decomposition achieves.

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

### child `WeierstrassCurve.isModular_map_of_mlc1`: [`P2M/Sol/S_WeierstrassCurve_modularity_of_semistableModel.lean` lines 160-162](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_modularity_of_semistableModel.lean#L160-L162) ([local copy](code/P2M/Sol/S_WeierstrassCurve_modularity_of_semistableModel.lean))

```lean
theorem isModular_map_of_mlc1 {W : WeierstrassCurve ℤ} (h : Mlc1IsModularModelOfExactConductorLevel W) :
    (W.map (Int.castRingHom ℚ)).IsModular :=
  isModular_map_of_isModularModel
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

TODO: explain how the parts fit: which child closes which obligation, and how each child was closed.

## Why it is good

TODO: numbered claims, each matching one entry of `claims` in entry.json, with its kind of evidence and a pointer.

## When to use it, and when not

TODO

## Consequences

TODO: obligations created, failure modes.

## Verification

<!-- verification:start -->
Not yet verified.
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/anthropics/fermats-last-theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, under `Apache-2.0`; see the [source note](../../sources/flt-anthropic/SOURCE.md) for the licence text and attribution.
