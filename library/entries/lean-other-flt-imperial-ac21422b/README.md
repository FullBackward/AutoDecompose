# support_eq_top: the patched module's support is all of Spec R0 via faithfulSMul and smul_lemma

| | |
|---|---|
| Kind | instance |
| Move | other |
| Language | lean |
| Status | draft |
| Source | [flt-imperial](../../sources/flt-imperial/SOURCE.md) at `a3210204ad88` |
| Licence | `Apache-2.0` |

## Intent

Show that the support of the patched module `M₀` over `R₀` is all of `Spec R₀`.
The proof does not compute the support directly; it factors the argument into
two named lemmas — `PatchingAlgebra.faithfulSMul` (the patching module is
faithful over the patching algebra, so its annihilator is `⊥`) and `smul_lemma`
(the compatibility of the patching data, which is exactly the `map_smul` of a
quotient equivalence) — and then finishes by a prime-spectrum rewrite that
transports the triviality of the annihilator along that equivalence and pulls it
back along the surjection `f₀`.

## The decomposition

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

How the parts fit. The glue (the parent's proof) is a straight assembly from
two named lemmas, one per obligation, followed by a spectrum computation:

```
support_eq_top (parent, 422-457)
├── PatchingAlgebra.faithfulSMul (child, 246-284)   — cited at line 433
└── smul_lemma (child, 387-418)                      — cited at line 450
    ├── smul_lemma₀ (310-369)                        — cited at line 403
    └── smul_lemma₁ (372-376)                        — cited at line 409
```

- The first obligation is *faithfulness*: after deriving `Module.Finite R₀ M₀`
  (lines 431-432), the glue invokes `PatchingAlgebra.faithfulSMul Λ R M F fRₒₒ
  hfRₒₒ hfRₒₒ' H₀ H` (line 433). This child is a self-contained statement —
  "if `ringKrullDim Rₒₒ < ⊤` and `Module.depth Λ Λ = ringKrullDim Rₒₒ`, then
  `PatchingModule Λ M F` is faithful over `PatchingAlgebra R F`" — whose proof
  closes on its own from a surjection `f := PatchingAlgebra.lift`, nontriviality,
  and `Module.faithfulSMul_of_depth_eq_ringKrullDim`. It needs no sibling.
- The second obligation is the *compatibility of the patching data*: the glue
  builds the quotient equivalence `e'` with `map_smul' := smul_lemma Λ R M F 𝔫
  sR sM HCompat` (line 450). `smul_lemma` is a self-contained compatibility
  statement ("`quotientEquivOver` commutes with the scalar action") whose proof
  closes from its two named siblings in the same file: `convert smul_lemma₀`
  (line 403, the generic statement) and `rw [smul_lemma₁]` (line 409, the
  constant-module statement, itself `:= rfl`). The `map_smul'` field of `e'` is
  exactly `smul_lemma`, so no inline compatibility proof appears in the glue.
- The rest of the glue (lines 434-457) is a prime-spectrum rewrite: it rewrites
  `Module.support_eq_zeroLocus`, uses `e'.annihilator_eq` to transport the
  annihilator, then pulls the zero locus back along the surjection `f₀` (whose
  surjectivity uses `PatchingAlgebra.surjective_quotientToOver`, line 438, an
  infrastructure lemma not treated as a child here) and closes with
  `PrimeSpectrum.comap_injective_of_surjective`.

Both children are good leaves: each is a named statement with a proof that closes
either on its own (`faithfulSMul`) or from named siblings (`smul_lemma` via
`smul_lemma₀` and `smul_lemma₁`), and neither needs to unfold the patching
construction in the glue.

## Why it is good

1. `support_eq_top` is declared in `FLT/Patching/System.lean` at line 422
   (`check`, `declared(support_eq_top, FLT/Patching/System.lean, 422-422)`).
2. `PatchingAlgebra.faithfulSMul` occurs in the parent site (line 433)
   (`check`, `cites(parent, PatchingAlgebra.faithfulSMul)`).
3. `smul_lemma` occurs in the parent site (line 450)
   (`check`, `cites(parent, smul_lemma)`).
4. No `sorry`, `admit`, or `axiom` occurs in the parent's lines 422-457
   (`check`, `no_sorry(FLT/Patching/System.lean, 422-457)`).
5. The decomposition is 2 project lemmas deep below the main theorem:
   `support_eq_top` (System.lean:422) → `smul_lemma` (System.lean:387) →
   `smul_lemma₀` (System.lean:310), all three proved in the same file
   (`measurement`, the call chain at #L450, #L403, #L310).

In my opinion the detail worth copying is the structure literal at lines
446-450: the quotient equivalence `e'` is built by giving its `map_smul'` field
as the *named* lemma `smul_lemma`, so the compatibility obligation is an actual
lemma hole in the skeleton, not an inline sub-proof. That is the shape a bounded
prover can be handed as a single hole.

## When to use it, and when not

Use it when a "support is everything" goal (`Module.support A M = Set.univ`)
reduces to the triviality of `M`'s annihilator, and that triviality is already
available as a named faithfulness lemma (here `faithfulSMul`), while the action
agreement needed to build the quotient equivalence is a separate named lemma
(here `smul_lemma`). The shape is: derive finiteness, invoke the faithfulness
lemma, build the equivalence from the compatibility lemma, then run a zero-locus
rewrite along it and pull back along a surjective map.

Avoid it when the faithfulness is the hard content rather than a known lemma —
then there is no "assembly from named lemmas" to decompose, and the real work is
inside the faithfulness proof. Avoid it too when the two actions do not agree
through a single named lemma (the `map_smul'` field must then be filled inline,
and one of the two leaf-holes disappears), or when the support does not factor
through one quotient equivalence, so the spectrum computation needs a different
transport.

## Consequences

The decomposition creates two real leaf-holes. `faithfulSMul` must deliver
`FaithfulSMul (PatchingAlgebra R F) (PatchingModule Λ M F)` from only the two
hypotheses `H₀` and `H`; `smul_lemma` must deliver the exact `map_smul` equation
so the structure literal `e'` closes. If the compatibility equation is stated
with the wrong scalar (say on `PatchingModule.constEquiv` instead of
`quotientEquivOver`), the `map_smul'` field of `e'` will not close and the whole
support computation fails at the structure literal. The remaining steps are side
conditions discharged in the glue — the finiteness of `M₀` over `R₀` (lines
431-432) and the surjectivity of `f₀` (lines 437-438), the latter needed for the
final `PrimeSpectrum.comap_injective_of_surjective`. A module that is not
faithful (non-trivial annihilator) breaks `Module.annihilator_eq_bot.mpr` and the
support would come out as a proper closed subset rather than `Set.univ`.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/ImperialCollegeLondon/FLT at commit `a3210204ad8876e851e32f73dd97d882bf1ccd0a`, under `Apache-2.0`; see the [source note](../../sources/flt-imperial/SOURCE.md) for the licence text and attribution.
