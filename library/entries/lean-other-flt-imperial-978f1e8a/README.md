# throwaway smul_lemma excerpt probe

| | |
|---|---|
| Kind | instance |
| Move | other |
| Language | lean |
| Status | deprecated |
| Source | [flt-imperial](../../sources/flt-imperial/SOURCE.md) at `a3210204ad88` |
| Licence | `Apache-2.0` |

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
