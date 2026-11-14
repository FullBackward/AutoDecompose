# Gromov's h-principle for open ample relations via the key invariant P₀ P₁ P₂

| | |
|---|---|
| Kind | instance |
| Move | key-invariant |
| Language | lean |
| Status | accepted |
| Source | [sphere-eversion](../../sources/sphere-eversion/SOURCE.md) at `33ab3d626854` |
| Licence | `Apache-2.0` |

## Intent

A statement of Gromov's h-principle — an ample, open first-order differential
relation `R` on a manifold satisfies the relative C⁰-dense h-principle — is
reduced to a generic induction over the manifold by choosing one key invariant:
three predicates `P₀ P₁ P₂` on one-jet germs (`P₀` = correct section, in `R`,
smooth, agrees with the formal solution `𝓕₀` on the closed set `A`, and τ-close;
`P₁` = holonomic; `P₂` = smooth in time and space). The proof then is: prove `P₀`
holds initially, prove it survives one local improvement step, and hand the
predicates to the induction engine `inductive_htpy_construction`, whose output is
exactly the homotopy the theorem asks for.

## The decomposition

### parent `RelMfld.Ample.satisfiesHPrinciple`: [`SphereEversion/Global/Gromov.lean` lines 37-178](https://github.com/leanprover-community/sphere-eversion/blob/33ab3d626854a0f0f04ed5772e3102d652e96475/SphereEversion/Global/Gromov.lean#L37-L178) ([local copy](code/SphereEversion/Global/Gromov.lean))

```lean
theorem RelMfld.Ample.satisfiesHPrinciple (hRample : R.Ample) (hRopen : IsOpen R) (hA : IsClosed A)
    (hδ_pos : ∀ x, 0 < δ x) (hδ_cont : Continuous δ) : R.SatisfiesHPrinciple A δ := by
  borelize EX
  let := manifoldMetric IM M
  have := Manifold.locallyCompact_of_finiteDimensional (M := M) (I := IM)
  have := Manifold.locallyCompact_of_finiteDimensional (M := X) (I := IX)
  refine RelMfld.satisfiesHPrinciple_of_weak hA fun A hA 𝓕₀ h𝓕₀ ↦ ?_
  obtain (hM | hM) := isEmpty_or_nonempty M
  · refine ⟨emptyHtpyFormalSol R, ?_, ?_, ?_, ?_⟩ <;> intro
    all_goals try intro
    all_goals exact (IsEmpty.false ‹M›).elim
  obtain (hX | hX) := isEmpty_or_nonempty X
  · exfalso
    inhabit M
    exact (IsEmpty.false <| 𝓕₀.bs default).elim
  -- We now start the main proof under the assumption that `M` and `X` are nonempty.
  have cont : Continuous 𝓕₀.bs := 𝓕₀.contMDiff_bs.continuous
  rcases exists_stability_dist IM IX cont with ⟨ε, ε_pos, ε_cont, hε⟩
  let τ := fun x : M ↦ min (δ x) (ε x)
  have τ_pos : ∀ x, 0 < τ x := fun x ↦ lt_min (hδ_pos x) (ε_pos x)
  have τ_cont : Continuous τ := hδ_cont.min ε_cont
  let P₀ : ∀ x : M, Germ (𝓝 x) J¹ → Prop := fun x F ↦
    F.value.1.1 = x ∧
      F.value ∈ R ∧
        F.ContMDiffAt' IM ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ∞ ∧
          RestrictGermPredicate (fun x F' ↦ F'.value = 𝓕₀ x) A x F ∧
            dist F.value.1.2 (𝓕₀.bs x) < τ x
  let P₁ : ∀ x : M, Germ (𝓝 x) J¹ → Prop := fun x F ↦ IsHolonomicGerm F
  let P₂ : ∀ p : ℝ × M, Germ (𝓝 p) J¹ → Prop := fun p F ↦
    F.ContMDiffAt' (𝓘(ℝ).prod IM) ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ∞
  have hP₂ : ∀ (a b : ℝ) (p : ℝ × M) (f : ℝ × M → J¹),
      P₂ (a * p.1 + b, p.2) f → P₂ p fun p : ℝ × M ↦ f (a * p.1 + b, p.2) := by
    rintro a b ⟨t, x⟩ f h
    change ContMDiffAt _ _ _ (f ∘ fun p : ℝ × M ↦ (a * p.1 + b, p.2)) (t, x)
    change ContMDiffAt _ _ _ f ((fun p : ℝ × M ↦ (a * p.1 + b, p.2)) (t, x)) at h
    have :
      CMDiffAt ∞ (fun p : ℝ × M ↦ (a * p.1 + b, p.2)) (t, x) :=
      haveI h₁ : CMDiffAt ∞ (fun t ↦ a * t + b) t :=
        contMDiffAt_iff_contDiffAt.mpr
          (((contDiffAt_id : ContDiffAt ℝ ∞ id t).const_smul a).add contDiffAt_const)
      h₁.prodMap contMDiffAt_id
    exact h.comp (t, x) this
  have init : ∀ x : M, P₀ x (𝓕₀ : M → J¹) := by
    refine fun x ↦ ⟨rfl, 𝓕₀.is_sol x, 𝓕₀.contMDiff x, ?_, ?_⟩
    · revert x
      exact forall_restrictGermPredicate_of_forall fun x ↦ rfl
    · erw [dist_self]
      exact τ_pos x
  have hP₂' : ∀ (t : ℝ) (x : M) (f : M → J¹), P₀ x f → P₂ (t, x) fun p : ℝ × M ↦ f p.2 :=
    fun t x f hf ↦ ContMDiffAt.comp (t, x) hf.2.2.1 contMDiffAt_snd
  have ind : ∀ m : M, ∃ V ∈ 𝓝 m, ∀ K₁ ⊆ V, ∀ K₀ ⊆ interior K₁, IsCompact K₀ → IsCompact K₁ →
      ∀ (C : Set M) (f : M → J¹), IsClosed C →
      (∀ x, P₀ x f) → (∀ᶠ x in 𝓝ˢ C, P₁ x f) →
        ∃ F : ℝ → M → J¹, (∀ t x, P₀ x (F t)) ∧
                          (∀ᶠ x in 𝓝ˢ (C ∪ K₀), P₁ x (F 1)) ∧
                          (∀ (p : ℝ × M), P₂ p ↿F) ∧
                          (∀ t, ∀ x ∉ K₁, F t x = f x) ∧
                          (∀ᶠ t in 𝓝ˢ (Iic 0), F t = f) ∧
                          ∀ᶠ t in 𝓝ˢ (Ici 1), F t = F 1 := by
    intro m
    rcases hε m with ⟨φ, ψ, ⟨e, rfl⟩, hφψ⟩
    have : φ '' ball e 1 ∈ 𝓝 (φ e) := by
      rw [← φ.isOpenEmbedding.map_nhds_eq]
      exact image_mem_map (ball_mem_nhds e zero_lt_one)
    use φ '' (ball e 1), this
    intro K₁ hK₁ K₀ K₀K₁ K₀_cpct K₁_cpct C f C_closed P₀f fC
    have K₁φ : K₁ ⊆ range φ := SurjOn.subset_range hK₁
    have K₀φ : K₀ ⊆ range φ := K₀K₁.trans interior_subset |>.trans K₁φ
    replace K₀_cpct : IsCompact (φ ⁻¹' K₀) :=
      φ.isOpenEmbedding.toIsInducing.isCompact_preimage' K₀_cpct K₀φ
    replace K₁_cpct : IsCompact (φ ⁻¹' K₁) :=
      φ.isOpenEmbedding.toIsInducing.isCompact_preimage' K₁_cpct K₁φ
    have K₀K₁' : φ ⁻¹' K₀ ⊆ interior (φ ⁻¹' K₁) := by
      rw [← φ.isOpenMap.preimage_interior_eq_interior_preimage φ.continuous]
      gcongr
    simp only [P₀, forall_and] at P₀f
    rcases P₀f with ⟨hf_sec, hf_sol, hf_smooth, hf_A, hf_dist⟩
    rw [forall_restrictGermPredicate_iff] at hf_A
    let F : FormalSol R := mkFormalSol f hf_sec hf_sol hf_smooth
    have hFAC : ∀ᶠ x near A ∪ C, F.IsHolonomicAt x := by
      rw [Eventually.union_nhdsSet]
      refine ⟨(hf_A.and h𝓕₀).eventually_nhdsSet.mono fun x hx ↦ ?_, fC⟩
      rw [eventually_and] at hx
      refine hx.2.self_of_nhds.congr (hx.1.mono fun x' hx' ↦ ?_)
      simp only [FormalSol.toOneJetSec_coe, mkFormalSol_apply, F]
      exact hx'.symm
    have hFφψ : F.bs '' (range φ) ⊆ range ψ := by
      rw [← range_comp]
      apply hφψ
      intro x
      calc
        dist (F.bs x) (𝓕₀.bs x) = dist (f x).1.2 (𝓕₀.bs x) := by simp only [F, mkFormalSol_bs_apply]
        _ < τ x := (hf_dist x)
        _ ≤ ε x := min_le_right _ _
    let η : M → ℝ := fun x ↦ τ x - dist (f x).1.2 (𝓕₀.bs x)
    have η_pos : ∀ x, 0 < η x := fun x ↦ sub_pos.mpr (hf_dist x)
    have η_cont : Continuous η := by
      have : ContMDiff IM ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ∞ f := fun x ↦ hf_smooth x
      apply τ_cont.sub
      exact (oneJetBundle_proj_continuous.comp this.continuous).snd.dist 𝓕₀.contMDiff_bs.continuous
    rcases φ.improve_formalSol ψ hRample hRopen (hA.union C_closed) η_pos η_cont hFφψ hFAC K₀_cpct
        K₁_cpct K₀K₁' with
      ⟨F', hF'₀, hF'₁, hF'AC, hF'K₁, hF'η, hF'hol⟩
    refine ⟨fun t x ↦ F' t x, ?_, ?_, ?_, ?_, ?_, ?_⟩; all_goals beta_reduce
    · refine fun t x ↦ ⟨rfl, F'.is_sol, (F' t).contMDiff x, ?_, ?_⟩
      · revert x
        rw [forall_restrictGermPredicate_iff]
        rw [Eventually.union_nhdsSet] at hF'AC
        apply (hF'AC.1.and hf_A).mono
        rintro x ⟨hx, hx'⟩
        change F' t x = _
        rw [hx t, ← hx', mkFormalSol_apply]
        rfl
      · calc
          dist (F' t x).1.2 (𝓕₀.bs x) ≤ dist (F' t x).1.2 (F.bs x) + dist (F.bs x) (𝓕₀.bs x) :=
            dist_triangle _ _ _
          _ < η x + dist (F.bs x) (𝓕₀.bs x) := (add_lt_add_left (hF'η t x) _)
          _ = τ x := by simp [F, η]
    · rw [union_assoc, Eventually.union_nhdsSet, image_preimage_eq_of_subset K₀φ] at hF'hol
      exact hF'hol.2
    · exact F'.contMDiff
    · intro t x hx
      replace hx : x ∉ φ '' (φ ⁻¹' K₁) := by rwa [image_preimage_eq_of_subset K₁φ]
      simpa [F] using hF'K₁ t x hx
    · apply hF'₀.mono fun x hx ↦ ?_
      erw [hx]
      ext1 y
      simp [F]
    · exact hF'₁.mono (fun _ hx ↦ DFunLike.ext'_iff.mp hx)
  rcases inductive_htpy_construction P₀ P₁ P₂ hP₂ hP₂' init ind with ⟨F, hF₀, hFP₀, hFP₁, hFP₂⟩
  simp only [P₀, forall_and] at hFP₀
  rcases hFP₀ with ⟨hF_sec, hF_sol, _hF_smooth, hF_A, hF_dist⟩
  refine ⟨mkHtpyFormalSol F hF_sec hF_sol hFP₂, ?_, hFP₁, ?_, ?_⟩
  · intro x
    rw [mkHtpyFormalSol_apply, hF₀]
  · intro x hx t
    rw [mkHtpyFormalSol_apply]
    exact (forall_restrictGermPredicate_iff.mp <| hF_A t).self_of_nhdsSet x hx
  · intro t x
    change dist (mkHtpyFormalSol F hF_sec hF_sol hFP₂ t x).1.2 (𝓕₀.bs x) ≤ δ x
    rw [mkHtpyFormalSol_apply]
    exact (hF_dist t x).le.trans (min_le_left _ _)
```

### child `RelMfld.satisfiesHPrinciple_of_weak`: [`SphereEversion/Global/Relation.lean` lines 353-360](https://github.com/leanprover-community/sphere-eversion/blob/33ab3d626854a0f0f04ed5772e3102d652e96475/SphereEversion/Global/Relation.lean#L353-L360) ([local copy](code/SphereEversion/Global/Relation.lean))

```lean
theorem RelMfld.satisfiesHPrinciple_of_weak [FiniteDimensional ℝ E] [T2Space M]
    [SigmaCompactSpace M] {R : RelMfld I M IX X} {ε : M → ℝ} {C : Set M} (hC : IsClosed C)
    (h : ∀ A : Set M, IsClosed A → R.SatisfiesHPrincipleWeak A ε) : R.SatisfiesHPrinciple C ε := by
  have := Manifold.metrizableSpace I M
  intro 𝓕₀ h𝓕₀
  obtain ⟨C', hCC', hC', h𝓕₀C'⟩ := h𝓕₀.closed_neighborhood hC
  obtain ⟨𝓕, h1, h2, h3, h4⟩ := h C' hC' 𝓕₀ h𝓕₀C'
  exact ⟨𝓕, h1, h2, eventually_of_mem hCC' h3, h4⟩
```

### child `_root_.exists_stability_dist`: [`SphereEversion/Global/LocalisationData.lean` lines 174-187](https://github.com/leanprover-community/sphere-eversion/blob/33ab3d626854a0f0f04ed5772e3102d652e96475/SphereEversion/Global/LocalisationData.lean#L174-L187) ([local copy](code/SphereEversion/Global/LocalisationData.lean))

```lean
theorem _root_.exists_stability_dist {f : M → M'} (hf : Continuous f) :
    ∃ ε : M → ℝ, (∀ m, 0 < ε m) ∧ Continuous ε ∧
      ∀ x : M,
        ∃ φ : OpenSmoothEmbedding 𝓘(ℝ, E) E I M,
        ∃ ψ : OpenSmoothEmbedding 𝓘(ℝ, E') E' I' M',
          x ∈ range φ ∧
          ∀ (g : M → M'), (∀ m, dist (g m) (f m) < ε m) → range (g ∘ φ) ⊆ range ψ := by
  let L := stdLocalisationData E I E' I' hf
  use L.ε, L.ε_pos, L.ε_cont
  intro x
  rcases mem_iUnion.mp <| eq_univ_iff_forall.mp L.h₁ x with ⟨i, hi⟩
  use L.φ i, L.ψj i, mem_range_of_mem_image (φ L i) _ hi, ?_
  have := L.ε_spec
  tauto
```

### child `OpenSmoothEmbedding.improve_formalSol`: [`SphereEversion/Global/LocalizedConstruction.lean` lines 22-114](https://github.com/leanprover-community/sphere-eversion/blob/33ab3d626854a0f0f04ed5772e3102d652e96475/SphereEversion/Global/LocalizedConstruction.lean#L22-L114) ([local copy](code/SphereEversion/Global/LocalizedConstruction.lean))

```lean
theorem OpenSmoothEmbedding.improve_formalSol (φ : OpenSmoothEmbedding 𝓘(ℝ, EM) EM IM M)
    (ψ : OpenSmoothEmbedding 𝓘(ℝ, EX) EX IX X) {R : RelMfld IM M IX X} (hRample : R.Ample)
    (hRopen : IsOpen R) {C : Set M} (hC : IsClosed C) {δ : M → ℝ} (hδ_pos : ∀ x, 0 < δ x)
    (hδ_cont : Continuous δ) {F : FormalSol R} (hFφψ : F.bs '' range φ ⊆ range ψ)
    (hFC : ∀ᶠ x near C, F.IsHolonomicAt x) {K₀ K₁ : Set EM} (hK₀ : IsCompact K₀)
    (hK₁ : IsCompact K₁) (hK₀K₁ : K₀ ⊆ interior K₁) :
    ∃ F' : HtpyFormalSol R,
      (∀ᶠ t near Iic (0 : ℝ), F' t = F) ∧
        (∀ᶠ t near Ici (1 : ℝ), F' t = F' 1) ∧
          (∀ᶠ x near C, ∀ t, F' t x = F x) ∧
            (∀ t, ∀ x ∉ φ '' K₁, F' t x = F x) ∧
              (∀ t x, dist ((F' t).bs x) (F.bs x) < δ x) ∧
                ∀ᶠ x near C ∪ φ '' K₀, (F' 1).IsHolonomicAt x := by
```

*The 80-line proof body (file lines 35-114) is elided here to keep the README
short; it is in the [local copy](code/SphereEversion/Global/LocalizedConstruction.lean).
It localises `R` to the chart pair `φ ψ`, runs the local h-principle
`𝓕.improve_htpy'`, and rebuilds `F' := p.mkHtpy F 𝓕'`, closing each of the six
conjuncts from the chart-pair projection lemmas `dist_update'`, `localize`,
`mkHtpy`, `mkHtpy_*` proved in the same file.*

### child `inductive_htpy_construction`: [`SphereEversion/InductiveConstructions.lean` lines 424-467](https://github.com/leanprover-community/sphere-eversion/blob/33ab3d626854a0f0f04ed5772e3102d652e96475/SphereEversion/InductiveConstructions.lean#L424-L467) ([local copy](code/SphereEversion/InductiveConstructions.lean))

```lean
theorem inductive_htpy_construction {X Y : Type*}
    [EMetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
    (P₀ P₁ : ∀ x : X, Germ (𝓝 x) Y → Prop)
    (P₂ : ∀ p : ℝ × X, Germ (𝓝 p) Y → Prop)
    (hP₂ : ∀ (a b) (p : ℝ × X) (f : ℝ × X → Y), P₂ (a * p.1 + b, p.2) f →
      P₂ p fun p : ℝ × X ↦ f (a * p.1 + b, p.2))
    (hP₂' : ∀ t x (f : X → Y), P₀ x f → P₂ (t, x) fun p : ℝ × X ↦ f p.2)
    {f₀ : X → Y} (init : ∀ x, P₀ x f₀)
    (ind : ∀ x, ∃ V ∈ 𝓝 x, ∀ K₁ ⊆ V, ∀ K₀ ⊆ interior K₁, IsCompact K₀ → IsCompact K₁ →
      ∀ (C : Set X) (f : X → Y), IsClosed C → (∀ x, P₀ x f) →
      (∀ᶠ x near C, P₁ x f) → ∃ F : ℝ → X → Y, (∀ t, ∀ x, P₀ x <| F t)
        ∧ (∀ᶠ x near C ∪ K₀, P₁ x <| F 1) ∧
      (∀ p, P₂ p ↿F) ∧ (∀ t, ∀ x ∉ K₁, F t x = f x) ∧
      (∀ᶠ t near Iic 0, F t = f) ∧ ∀ᶠ t near Ici 1, F t = F 1) :
    ∃ F : ℝ → X → Y, F 0 = f₀ ∧ (∀ t x, P₀ x (F t)) ∧ (∀ x, P₁ x (F 1)) ∧ ∀ p, P₂ p ↿F := by
  let P (V : Set X) : Prop :=  ∀ K₁ ⊆ V, ∀ K₀ ⊆ interior K₁, IsCompact K₀ → IsCompact K₁ →
      ∀ (C : Set X) (f : X → Y), IsClosed C → (∀ x, P₀ x f) →
      (∀ᶠ x near C, P₁ x f) → ∃ F : ℝ → X → Y, (∀ t, ∀ x, P₀ x <| F t)
        ∧ (∀ᶠ x near C ∪ K₀, P₁ x <| F 1) ∧
      (∀ p, P₂ p ↿F) ∧ (∀ t, ∀ x ∉ K₁, F t x = f x) ∧
      (∀ᶠ t near Iic 0, F t = f) ∧ ∀ᶠ t near Ici 1, F t = F 1
  have P_anti : Antitone P := fun U V UV hV K₁ K₁U ↦ hV K₁ (K₁U.trans UV)
  have P_empty : P ∅ := by
    intro K₁ K₁V K₀ K₀K₁ _ _ C f _ hf hf'
    have K₀_eq : K₀ = ∅ := subset_empty_iff.mp <| K₀K₁.trans interior_subset |>.trans K₁V
    use fun _ x ↦ f x
    simp [hf, hf', K₀_eq]
    tauto
  rcases exists_locallyFinite_subcover_of_locally isClosed_univ P_anti P_empty
    (by simpa only [mem_univ, forall_true_left] using ind) with
    ⟨K : IndexType 0 → Set X, W : IndexType 0 → Set X, K_cpct, W_op, hW, K_subW, W_fin, K_cover⟩
  apply inductive_htpy_construction' P₀ P₁ P₂ hP₂ W_fin (univ_subset_iff.mp K_cover) init
    (fun ⟨t, x⟩ ↦  hP₂' t x f₀ (init x))
  intro i f hf₀ hf₁
  obtain ⟨K₁, K₁_cpct, KiK₁, K₁W⟩ : ∃ K₁, IsCompact K₁ ∧ K i ⊆ interior K₁ ∧ K₁ ⊆ W i :=
    exists_compact_between (K_cpct i) (W_op i) (K_subW i)
  rcases hW i K₁ K₁W (K i) KiK₁ (K_cpct i) K₁_cpct (⋃ j < i, K j) f
    ((finite_lt_nat i).isClosed_biUnion fun j _ ↦ (K_cpct j).isClosed) hf₀ hf₁
    with ⟨F, hF₀, hF₁, hF₂, hFK₁, ht⟩
  refine ⟨F, hF₀, ?_, hF₂, ?_, ht⟩
  · apply hF₁.filter_mono
    gcongr
    rw [biUnion_le]
  · exact fun t x hx ↦ hFK₁ t x (notMem_subset K₁W hx)
```

### child `emptyHtpyFormalSol`: [`SphereEversion/Global/Relation.lean` lines 311-315](https://github.com/leanprover-community/sphere-eversion/blob/33ab3d626854a0f0f04ed5772e3102d652e96475/SphereEversion/Global/Relation.lean#L311-L315) ([local copy](code/SphereEversion/Global/Relation.lean))

```lean
def emptyHtpyFormalSol [IsEmpty M] : HtpyFormalSol R where
  bs _t x := (IsEmpty.false x).elim
  ϕ _t x := (IsEmpty.false x).elim
  contMDiff' := fun ⟨_t, x⟩ ↦ (IsEmpty.false x).elim
  is_sol' _t x := (IsEmpty.false x).elim
```

### child `mkHtpyFormalSol`: [`SphereEversion/Global/Relation.lean` lines 274-289](https://github.com/leanprover-community/sphere-eversion/blob/33ab3d626854a0f0f04ed5772e3102d652e96475/SphereEversion/Global/Relation.lean#L274-L289) ([local copy](code/SphereEversion/Global/Relation.lean))

```lean
def mkHtpyFormalSol (F : ℝ → M → OneJetBundle I M I' M') (hsec : ∀ t x, (F t x).1.1 = x)
    (hsol : ∀ t x, F t x ∈ R)
    (hsmooth : ContMDiff (𝓘(ℝ).prod I) ((I.prod I').prod 𝓘(ℝ, E →L[ℝ] E')) ∞ ↿F) : HtpyFormalSol R
    where
  bs t m := (F t m).1.2
  ϕ t m := (F t m).2
  contMDiff' := by
    convert hsmooth using 1
    ext ⟨t, x⟩
    · exact (hsec t x).symm
    all_goals rfl
  is_sol' t m := by
    convert hsol t m
    ext
    on_goal 1 => rw [hsec]
    all_goals rfl
```

How the parts fit. The glue (the parent, `Gromov.lean` 37-178) runs in this order:

1. `RelMfld.satisfiesHPrinciple_of_weak` (line 43) reduces the strong h-principle
   to the weak one, so everything after it only has to prove the weak form "for
   every closed `A`".
2. The two empty-manifold corners are discharged first: `emptyHtpyFormalSol`
   (line 45) when `M` is empty, and an `exfalso` when `X` is empty.
3. `exists_stability_dist` (line 54) supplies `ε`, the positive continuous
   "stability distance" that keeps local perturbations inside the open ample
   relation; the glue then works at `τ := min (δ x) (ε x)`.
4. The invariant `P₀ P₁ P₂` is defined (lines 58-66). `P₀` is the strengthened
   hypothesis — a germ whose value is a section over `x`, lies in `R`, is smooth,
   agrees with `𝓕₀` on `A`, and is τ-close to `𝓕₀`. `P₁` is holonomicity, `P₂`
   time-space smoothness. `init` (line 79) proves `𝓕₀` satisfies `P₀`; `hP₂` and
   `hP₂'` (lines 67-86) prove the two compatibility facts the engine needs.
5. The `ind` block (lines 87-165) proves the invariant survives one local step:
   from an `f` that is `P₀` everywhere and `P₁` near `C`, it produces an `F` that
   is `P₀` everywhere, `P₁` near `C ∪ K₀`, `P₂` everywhere, equal to `f` outside
   `K₁` and for `t ≤ 0`, and constant for `t ≥ 1`. Its engine is
   `OpenSmoothEmbedding.improve_formalSol` (line 137), the one local corrugation;
   `mkFormalSol` (line 115) rebuilds the `FormalSol` around it.
6. `inductive_htpy_construction` (line 166) is called with `P₀ P₁ P₂`, `init` and
   `ind`, and returns `F` with `F 0 = 𝓕₀`, `P₀` everywhere, `P₁` at `t = 1`, `P₂`
   everywhere — the invariant turned back into a homotopy.
7. `mkHtpyFormalSol` (line 169) wraps `F` into a `HtpyFormalSol`; the four
   conjuncts of `SatisfiesHPrinciple` then close from `hF₀` (value at 0), `hFP₁`
   (holonomic at 1), `hF_A` (agreement near `A`) and `hF_dist` (closeness ≤ δ).

The lemma graph (who uses whom):

```
RelMfld.Ample.satisfiesHPrinciple
├── RelMfld.satisfiesHPrinciple_of_weak   (reduce strong → weak)
├── emptyHtpyFormalSol                    (M empty)
├── exists_stability_dist                 (the stability distance ε)
├── OpenSmoothEmbedding.improve_formalSol (the local step, inside ind)
├── inductive_htpy_construction           (the induction engine)
│     └── inductive_htpy_construction'    (InductiveConstructions.lean 285)
│           └── inductive_construction    (InductiveConstructions.lean 66)
└── mkHtpyFormalSol                       (wrap the result)
```

Why each child is a good leaf:

- `RelMfld.satisfiesHPrinciple_of_weak` is a self-contained statement whose proof
  closes on its own from Mathlib (`Manifold.metrizableSpace`,
  `h𝓕₀.closed_neighborhood`, `eventually_of_mem`).
- `_root_.exists_stability_dist` is self-contained; it closes on its own from
  `stdLocalisationData` and its `ε_spec` projection, ending in `tauto`.
- `OpenSmoothEmbedding.improve_formalSol` is the one big leaf (93 lines); it
  closes from the local h-principle `𝓕.improve_htpy'` plus the chart-pair
  projection lemmas (`dist_update'`, `localize`, `mkHtpy`, `mkHtpy_*`) proved in
  the same file.
- `inductive_htpy_construction` closes from its named sibling one level down,
  `inductive_htpy_construction'`, reached through a locally-finite subcover.
- `emptyHtpyFormalSol` (5 lines) and `mkHtpyFormalSol` (16 lines) are trivial
  packaging: the first closes by `(IsEmpty.false x).elim`, the second by
  `convert`/`rfl`.

In my opinion the detail worth copying is the *shape* of `P₀`: it is not the
conclusion (holonomic) but the conclusion plus the four side conditions
(section, in-`R`, smooth, agrees on `A`, τ-close) that the single step
`improve_formalSol` needs in order to be re-applied, and which collapse to the
conclusion at `t = 1`. That is the whole content of the move.

## Why it is good

1. The parent `RelMfld.Ample.satisfiesHPrinciple` is declared in
   `SphereEversion/Global/Gromov.lean` lines 37-178 (`check`, `declared`).
2. `inductive_htpy_construction` occurs in the parent's site, at line 166 — the
   single call that hands the invariant `P₀ P₁ P₂` to the induction engine
   (`check`, `cites`).
3. No `sorry`/`admit`/`axiom` closes a goal in the parent proof, `Gromov.lean`
   37-178 (`check`, `no_sorry`).
4. The glue is 142 lines and cites six named project lemmas; the longest checked
   chain of project lemmas below it is three, `inductive_htpy_construction →
   inductive_htpy_construction' → inductive_construction`, all in
   `InductiveConstructions.lean` (`measurement`).
5. The authors state the weak/strong split as a design choice in the docstring of
   `SatisfiesHPrincipleWeak`: "The weak version has ∀ x ∈ C, ∀ t : ℝ, 𝓕 t x =
   𝓕₀ x while the strong one has ∀ᶠ x near C, ∀ t, 𝓕 t x = 𝓕₀ x. The strong
   version is easy to derive from the weak one if we prove the weak one for *all*
   closed sets" (`author-statement`, `Relation.lean` 326-329).

Regarding the survey F §10 rules: the entry supports rule 6 (induction), and in
particular its "strengthen the hypothesis" clause — `P₀` is exactly an induction
hypothesis chosen strong enough that the step (`ind`) survives, the failure mode
rule 6 warns about ("an IH that is too weak shows up as a counterexample to the
step").

## When to use it, and when not

Use it when a theorem of the shape "every formal solution is homotopic to a
holonomic one" (an h-principle, a local-to-global statement) is proved by an
induction whose step does one local improvement, and the real content is a
predicate that (a) implies the conclusion at the end, (b) holds initially, and
(c) survives the step. The invariant is typically a conjunction of the target
property with the side conditions — smoothness, agreement on a closed set,
closeness — that make the step re-appliable; that is the situation here.

Avoid it when there is no generic engine to hand the predicates to (then the
induction itself is the work, and this is just `induction`, not `key-invariant`);
when the invariant is the conclusion with no extra side conditions (the move
collapses to plain induction); or when the step changes the invariant in a way
that needs per-index bookkeeping, which the engine's fixed three-predicate
signature (`P₀ P₁ P₂` plus the reindex and slice conditions `hP₂`, `hP₂'`) does
not express.

## Consequences

The move replaces "prove the h-principle" with three obligations: prove the
invariant holds initially (`init`, `Gromov.lean` 79-84), prove it survives one
local step (the `ind` block, 87-165), and prove the two compatibility facts the
engine needs (`hP₂` affine-reindex, 67-78; `hP₂'` slice, 85-86). The predicates
must match the engine's exact signature. The main failure mode is a mis-chosen
`P₀`: too weak and `ind` cannot be re-applied; too strong and `init` or the
boundary agreement fails. The empty-manifold corner still needs its own witness
(`emptyHtpyFormalSol`), and the weak→strong reduction has to be discharged
separately (`satisfiesHPrinciple_of_weak`), so the invariant does not absorb
those two obligations.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/blueprint.yml 'Build project' step runs 'lake build SphereEversion' on branch master (the default branch; source pinned ref HEAD = 33ab3d6). SphereEversion target includes SphereEversion/Global/Gromov.lean, so CI builds the parent file. | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: RelMfld.satisfiesHPrinciple_of_weak@SphereEversion/Global/Gromov.lean:43, _root_.exists_stability_dist@SphereEversion/Global/Gromov.lean:54, OpenSmoothEmbedding.improve_formalSol@SphereEversion/Global/Gromov.lean:137, inductive_htpy_construction@SphereEversion/Global/Gromov.lean:166, emptyHtpyFormalSol@SphereEversion/Global/Gromov.lean:45, mkHtpyFormalSol@SphereEversion/Global/Gromov.lean:169; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 7 file(s) byte-identical at 33ab3d626854a0f0f04ed5772e3102d652e96475 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(RelMfld.Ample.satisfiesHPrinciple, SphereEversion/Global/Gromov.lean, 37-178) -> declared: RelMfld.Ample.satisfiesHPrinciple is declared at SphereEversion/Global/Gromov.lean:37 | check_claims.py |
| 2 | verified | cites(parent, inductive_htpy_construction) -> cites: inductive_htpy_construction occurs at SphereEversion/Global/Gromov.lean:166 | check_claims.py |
| 3 | verified | no_sorry(SphereEversion/Global/Gromov.lean, 37-178) -> no_sorry: none of sorry, admit, axiom in SphereEversion/Global/Gromov.lean:37-178 | check_claims.py |
| 4 | verified | Parent site Gromov.lean 37-178 is 142 lines (178-37+1). Six lemmas cited at the stated lines: satisfiesHPrinciple_of_weak L43, emptyHtpyFormalSol L45, exists_stability_dist L54, improve_formalSol L137, inductive_htpy_construction L166, mkHtpyFormalSol L169 (grep -n). Chain of 3 in InductiveConstructions.lean: inductive_htpy_construction (L424) calls inductive_htpy_construction' (L455), which calls inductive_construction (L412); inductive_htpy_construction' declared L285, inductive_construction declared L66. | verifier |
| 5 | verified | Relation.lean L326-L329 comment matches verbatim (modulo Lean backticks around code): 'The weak version has ... while the strong one has ... The strong version is easy to derive from the weak one if we prove the weak one for *all* closed sets, see RelMfld.satisfiesHPrinciple_of_weak below.' | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Verified parent site Gromov.lean 37-178 (theorem RelMfld.Ample.satisfiesHPrinciple): statement matches entry.json verbatim, ends at line 178 with a complete proof (no sorry/admit/axiom). All 6 children statements match the copied code verbatim, and each closing method matches: satisfiesHPrinciple_of_weak -> exact <F,h1,h2,eventually_of_mem hCC' h3,h4>; exists_stability_dist -> have := L.eps_spec; tauto; improve_formalSol -> F.improve_htpy' + p.mkHtpy/dist_update'/mkHtpy_*; inductive_htpy_construction -> apply inductive_htpy_construction'; emptyHtpyFormalSol -> (IsEmpty.false x).elim; mkHtpyFormalSol -> convert/rfl. All 6 children are cited in the glue at exactly the claimed lines (43,45,54,137,166,169); none is extra. Shape numbers right: glue_lines 178-37+1=142; child_lines [8,14,93,44,5,16] match the cited ranges; depth 3 confirmed (inductive_htpy_construction@424 -> inductive_htpy_construction'@285/455 -> inductive_construction@66/412). Minor note (not material): the glue also uses the trivial def mkFormalSol (Relation.lean 83) at line 115, transparently mentioned in the README, so direct_lemmas=6 counts the six decomposition leaves, not this internal constructor. | reviewer-correctness |
| generality | accept | Move generalised beyond the example: 'use when' abstracts to any local-to-global theorem proved by an induction whose step does one local improvement, with the invariant = target property + side conditions (smoothness, agreement on a closed set, closeness) that make the step re-appliable; also_known_as (loop invariant, potential method, strengthened IH) and rule F10.6 'strengthen the hypothesis' tie it to the wider technique. When-not-to-use is specific and honest: no generic engine (collapses to plain induction), invariant = bare conclusion, or per-index bookkeeping the fixed three-predicate signature P0 P1 P2 + hP2/hP2' cannot express. Consequences are specific: three obligations (init, ind, two compatibility facts) plus the failure modes (P0 too weak => ind unprovable, too strong => init/boundary fails) and honest about what is NOT absorbed (empty-manifold corner, weak->strong reduction). Good-leaf/bounded-prover question answered in 'Why each child is a good leaf' (self-contained, closes on its own) plus honest shape metrics child_lines [8,14,93,44,5,16] and trivial_children=2, flagging improve_formalSol as the one 93-line leaf. Author-statement quote and both known_uses verified against code. | reviewer-generality |
| provenance-licence | accept | provenance pass: 7 files byte-identical at pinned commit 33ab3d626854a0f0f04ed5772e3102d652e96475. Commit hash is consistent across entry.json, README, SOURCE.md and every permalink. Licence Apache-2.0 is consistent: entry.json, SOURCE.md and upstream-LICENSE (Apache License 2.0 text) all agree. All cited line ranges verified against the copied files (Gromov.lean 37-178, Relation.lean 353-360/311-315/274-289/326-329, LocalisationData.lean 174-187, LocalizedConstruction.lean 22-114, InductiveConstructions.lean 424-467). Everything traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover-community/sphere-eversion at commit `33ab3d626854a0f0f04ed5772e3102d652e96475`, under `Apache-2.0`; see the [source note](../../sources/sphere-eversion/SOURCE.md) for the licence text and attribution.
