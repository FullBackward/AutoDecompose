# throwaway 3-site probe

| | |
|---|---|
| Kind | instance |
| Move | other |
| Language | lean |
| Status | deprecated |
| Source | [flt-imperial](../../sources/flt-imperial/SOURCE.md) at `a3210204ad88` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T09:37:17Z |

## Intent

TODO: one or two sentences on what this decomposition achieves.

## The decomposition

### child `smul_lemma`: [`FLT/Patching/System.lean` lines 387-418](https://github.com/ImperialCollegeLondon/FLT/blob/a3210204ad8876e851e32f73dd97d882bf1ccd0a/FLT/Patching/System.lean#L387-L418) ([local copy](code/FLT/Patching/System.lean))

```lean
lemma smul_lemma
    (HCompat : ∀ i m (r : R i), sM i (Submodule.Quotient.mk (r • m)) =
      sR i (Ideal.Quotient.mk _ r) • sM i (Submodule.Quotient.mk m))
    (m : PatchingAlgebra R F)
      (x : PatchingModule Λ M F ⧸ (𝔫 • ⊤ : Submodule (PatchingAlgebra R F)
      (PatchingModule Λ M F))) :
      PatchingModule.quotientEquivOver Λ M F 𝔫 sM (m • x) =
      ((PatchingAlgebra.quotientToOver Λ R F 𝔫 sR).comp (Ideal.Quotient.mk _)) m •
       PatchingModule.quotientEquivOver Λ M F 𝔫 sM x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  apply (PatchingModule.constEquiv Λ F M₀).injective
  refine ((PatchingModule.constEquiv Λ F M₀).apply_symm_apply _).trans ?_
  have (i : ι) : Nontrivial (R i ⧸ Ideal.map (algebraMap Λ (R i)) 𝔫) :=
    (sR i).toRingHom.domain_nontrivial
  have (i : ι) : IsLocalHom (Ideal.Quotient.mk (𝔫.map (algebraMap Λ (R i)))) :=
    .of_surjective _ (Ideal.Quotient.mk_surjective)
  convert smul_lemma₀ Λ R M F 𝔫 sR sM HCompat x m
  · obtain ⟨x, hx⟩ := x
    obtain ⟨m, hm⟩ := m
    obtain ⟨x, rfl⟩ := PatchingModule.ofPi_surjective x
    obtain ⟨m, rfl⟩ := PatchingAlgebra.ofPi_surjective m
    rfl
  rw [smul_lemma₁]
  congr 1
  · refine ((PatchingAlgebra.constEquiv F R₀).apply_symm_apply _).trans ?_
    obtain ⟨m, hm⟩ := m
    obtain ⟨m, rfl⟩ := PatchingAlgebra.ofPi_surjective m
    rfl
  · refine ((PatchingModule.constEquiv Λ F M₀).apply_symm_apply _).trans ?_
    obtain ⟨x, hx⟩ := x
    obtain ⟨x, rfl⟩ := PatchingModule.ofPi_surjective x
    rfl
```

### parent `support_eq_top`: [`FLT/Patching/System.lean` lines 422-457](https://github.com/ImperialCollegeLondon/FLT/blob/a3210204ad8876e851e32f73dd97d882bf1ccd0a/FLT/Patching/System.lean#L422-L457) ([local copy](code/FLT/Patching/System.lean))

```lean
lemma support_eq_top
    (HCompat : ∀ i m (r : R i), sM i (Submodule.Quotient.mk (r • m)) =
      sR i (Ideal.Quotient.mk _ r) • sM i (Submodule.Quotient.mk m))
    (H₀ : ringKrullDim Rₒₒ < ⊤)
    (H : .some (Module.depth Λ Λ) = ringKrullDim Rₒₒ) : Module.support R₀ M₀ = Set.univ := by
  have : Module.Finite Λ M₀ := by
    cases isEmpty_or_nonempty ι
    · cases F.neBot.1 (Subsingleton.elim _ _)
    have i := Nonempty.some (inferInstance: Nonempty ι)
    exact Module.Finite.equiv (sM i)
  have : Module.Finite R₀ M₀ := .of_restrictScalars_finite Λ _ _
  have := PatchingAlgebra.faithfulSMul Λ R M F fRₒₒ hfRₒₒ hfRₒₒ' H₀ H
  rw [Module.support_eq_zeroLocus, ← Set.univ_subset_iff]
  intro p hp
  let f₀ := ((PatchingAlgebra.quotientToOver Λ R F 𝔫 sR).comp (Ideal.Quotient.mk _))
  have hf₀ : Function.Surjective f₀ :=
    (PatchingAlgebra.surjective_quotientToOver Λ R F 𝔫 sR).comp Ideal.Quotient.mk_surjective
  let p' := PrimeSpectrum.comap f₀ p
  have hp' : 𝔫.map (algebraMap _ _) ≤ p'.asIdeal := by
    simp only [PrimeSpectrum.comap_comp, p', f₀]
    refine le_trans ?_ (Ideal.comap_mono (f := Ideal.Quotient.mk _) bot_le)
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  let inst := Module.compHom M₀ f₀
  let := f₀.toAlgebra
  have : IsScalarTower (PatchingAlgebra R F) R₀ M₀ := .of_algebraMap_smul fun _ _ ↦ rfl
  let e' : (PatchingModule Λ M F ⧸ (𝔫 • ⊤ : Submodule (PatchingAlgebra R F) (PatchingModule Λ M F)))
    ≃ₗ[PatchingAlgebra R F] M₀ :=
    { __ := (PatchingModule.quotientEquivOver Λ M F 𝔫 sM),
      map_smul' := smul_lemma Λ R M F 𝔫 sR sM HCompat }
  have := congr(PrimeSpectrum.zeroLocus (R := PatchingAlgebra R F) ↑($(e'.annihilator_eq)))
  rw [← Submodule.map_algebraMap_smul, ← Module.support_eq_zeroLocus,
    Module.support_quotient,  Module.support_eq_zeroLocus,
    Module.annihilator_eq_bot.mpr inferInstance, ← Module.comap_annihilator (R := R₀),
    ← image_comap_zeroLocus_eq_zeroLocus_comap _ _ (by exact hf₀)] at this
  simp only [Submodule.bot_coe, PrimeSpectrum.zeroLocus_singleton_zero, Set.univ_inter] at this
  exact (PrimeSpectrum.comap_injective_of_surjective _ hf₀).mem_set_image.mp (this.le hp')
```

### child `PatchingAlgebra.faithfulSMul`: [`FLT/Patching/System.lean` lines 246-284](https://github.com/ImperialCollegeLondon/FLT/blob/a3210204ad8876e851e32f73dd97d882bf1ccd0a/FLT/Patching/System.lean#L246-L284) ([local copy](code/FLT/Patching/System.lean))

```lean
lemma PatchingAlgebra.faithfulSMul
    (H₀ : ringKrullDim Rₒₒ < ⊤)
    (H : .some (Module.depth Λ Λ) = ringKrullDim Rₒₒ) :
    FaithfulSMul (PatchingAlgebra R F) (PatchingModule Λ M F) := by
  let f := PatchingAlgebra.lift R F (fun i ↦ (fRₒₒ i).toRingHom)
  have hf : Function.Surjective f :=
    lift_surjective R F _ hfRₒₒ' hfRₒₒ
  have hf' (r) : f (algebraMap Λ _ r) = algebraMap Λ _ r := by
    refine Subtype.ext (funext fun k ↦ UltraProduct.π_eq_iff.mpr (.of_forall fun i ↦ ?_))
    simp
  let := f.toAlgebra
  let := Module.compHom (PatchingModule Λ M F) f
  suffices FaithfulSMul Rₒₒ (PatchingModule Λ M F) by
    refine ⟨fun {x₁ x₂} H ↦ ?_⟩
    obtain ⟨x₁, rfl⟩ := hf x₁
    obtain ⟨x₂, rfl⟩ := hf x₂
    obtain rfl : x₁ = x₂ := FaithfulSMul.eq_of_smul_eq_smul H
    rfl
  have : Nontrivial (PatchingModule Λ M F) := by
    by_contra H
    rw [not_nontrivial_iff_subsingleton] at H
    obtain ⟨i, ⟨e⟩⟩ := (Module.UniformlyBoundedRank.rank_spec Λ M F).exists
    have := PatchingModule.rank_patchingModule Λ M F
    simp only [rank_subsingleton', @eq_comm Cardinal 0, Nat.cast_eq_zero] at this
    have : Subsingleton (Fin (rank Λ M F) → Λ ⧸ Module.annihilator Λ (M i)) := by
      rw [this]
      infer_instance
    exact not_subsingleton _ e.subsingleton
  have : IsScalarTower Λ Rₒₒ (PatchingModule Λ M F) := .of_algebraMap_smul <| by
    intro r m
    conv_rhs => rw [← IsScalarTower.algebraMap_smul (PatchingAlgebra R F), ← hf']
    rfl
  have : Module.Finite Rₒₒ (PatchingModule Λ M F) :=
    Module.Finite.of_restrictScalars_finite Λ _ _
  apply Module.faithfulSMul_of_depth_eq_ringKrullDim _ _ H₀
  refine le_antisymm (Module.depth_le_dim _ _) ?_
  have : Module.depth Λ Λ ≤ Module.depth Rₒₒ (PatchingModule Λ M F) :=
    (Module.depth_le_of_free _ _).trans (Module.depth_of_isScalarTower Λ _ _)
  rwa [← H, WithBot.coe_le_coe]
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
Status: **deprecated** (empty shell left by the timed-out pilot-3 extraction of FLT/Patching/System.lean:422; duplicate of lean-other-flt-imperial-ac21422b)

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/ImperialCollegeLondon/FLT at commit `a3210204ad8876e851e32f73dd97d882bf1ccd0a`, under `Apache-2.0`; see the [source note](../../sources/flt-imperial/SOURCE.md) for the licence text and attribution.
