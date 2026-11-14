# Strengthen to the not-in-coset case, then strong-induct, for asymmetric weak PFR over Z^d

| | |
|---|---|
| Kind | instance |
| Move | suffices-or-strengthen |
| Language | lean |
| Status | verified |
| Source | [pfr](../../sources/pfr/SOURCE.md) at `1ef23c3c5a83` |
| Licence | `Apache-2.0` |

## Intent

The theorem `weak_PFR_asymm` states, for finite non-empty `A, B ⊆ G` over a
free ℤ-module `G`, that there are non-empty `A' ⊆ A`, `B' ⊆ B` with
`log ((|A|·|B|) / (|A'|·|B'|)) ≤ 34·dᵤ[A # B]` and
`max (dim A') (dim B') ≤ (40/log 2)·dᵤ[A # B]`. The proof does not tackle that
statement directly. It *strengthens* the goal — via one `suffices` — to the
version that also assumes `NotInCoset A B`, strong-inducts on
`Nat.card A + Nat.card B` over that stronger statement, and finally transfers
the conclusion back to the original sets. The three named lemmas that carry
this are the reduction (`wlog_notInCoset`), the induction step
(`weak_PFR_asymm_prelim`), and the transfer (`conclusion_transfers`).

## The decomposition

### parent `weak_PFR_asymm`: [`PFR/WeakPFR.lean` lines 859-971](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/WeakPFR.lean#L859-L971) ([local copy](code/PFR/WeakPFR.lean))

```lean
/-- If $A,B\subseteq \mathbb{Z}^d$ are finite non-empty sets then there exist non-empty
$A'\subseteq A$ and $B'\subseteq B$ such that
\[\log\frac{\lvert A\rvert\lvert B\rvert}{\lvert A'\rvert\lvert B'\rvert}\leq 34 d[U_A;U_B]\]
such that $\max(\dim A',\dim B')\leq \frac{40}{\log 2} d[U_A;U_B]$. -/
lemma weak_PFR_asymm (A B : Set G) (hA : A.Finite) (hB : B.Finite) (hA₀ : A.Nonempty)
    (hB₀ : B.Nonempty) : WeakPFRAsymmConclusion A B := by
  set M := Nat.card A + Nat.card B with hM
  clear_value M
  induction M using Nat.strong_induction_on generalizing G with | ind M ih
  -- wlog we can assume A, B are not in cosets of a smaller subgroup
  suffices H : ∀ (G : Type _) (hG_comm : AddCommGroup G) (_hG_free : Module.Free ℤ G)
    (_hG_fin : Module.Finite ℤ G) (_hG_count : Countable G) (hG_mes : MeasurableSpace G)
    (_hG_sing : MeasurableSingletonClass G) (A B : Set G) (_hA_fin : Finite A) (_hB_fin : Finite B)
      (_hA_non : A.Nonempty) (_hB_non : B.Nonempty) (_hM : Nat.card A + Nat.card B ≤ M)
    (_hnot : NotInCoset A B), WeakPFRAsymmConclusion A B by
    obtain ⟨G', A', B', hAA', hBB', hnot'⟩ := wlog_notInCoset hA₀ hB₀
    have hG'_fin : Module.Finite ℤ G' :=
      Module.Finite.iff_fg (N := AddSubgroup.toIntSubmodule G').2 (IsNoetherian.noetherian _)
    have hG'_free : Module.Free ℤ G' := by
      rcases Submodule.nonempty_basis_of_pid (Module.Free.chooseBasis ℤ G)
        (AddSubgroup.toIntSubmodule G') with ⟨n, ⟨b⟩⟩
      exact Module.Free.of_basis b
    have hAA'_card : Nat.card A = Nat.card A' :=
      Nat.card_image_of_injective Subtype.val_injective _ ▸ hAA'.card_congr
    have hBB'_card : Nat.card B = Nat.card B' :=
      Nat.card_image_of_injective Subtype.val_injective _ ▸ hBB'.card_congr
    have : Finite A := hA.to_subtype
    have : Finite B := hB.to_subtype
    have : Nonempty A := hA₀.to_subtype
    have : Nonempty B := hB₀.to_subtype
    rw [hAA'_card, hBB'_card] at hM
    have hA'_nonfin : A'.Nonempty ∧ Finite A' := by
      convert Nat.card_pos_iff.mp ?_
      · exact Iff.symm nonempty_coe_sort
      · simpa [hAA'_card] using Nat.card_pos (α := A)
    have hB'_nonfin : B'.Nonempty ∧ Finite B' := by
      convert Nat.card_pos_iff.mp ?_
      · exact Iff.symm nonempty_coe_sort
      · simpa [hBB'_card] using Nat.card_pos (α := B)
    obtain ⟨hA'_non, hA'_fin⟩ := hA'_nonfin
    obtain ⟨hB'_non, hB'_fin⟩ := hB'_nonfin
    replace this := H G' _ hG'_free hG'_fin (by infer_instance) (by infer_instance)
      (by infer_instance) A' B' hA'_fin hB'_fin hA'_non hB'_non hM.ge hnot'
    exact conclusion_transfers G' A' B' hAA' hBB' hA'_non hB'_non this
  intro G hG_comm hG_free hG_fin hG_count hG_mes hG_sing A B hA_fin hB_fin hA_non hB_non hM hnot
  obtain ⟨N, x, y, Ax, By, hAx_non, hBy_non, hAx_fin, hBy_fin, hAx, hBy, hdim, hcard⟩ :=
    weak_PFR_asymm_prelim A B hA_non hB_non
  have hAxA : Ax ⊆ A := by rw [hAx]; simp
  have hByB : By ⊆ B := by rw [hBy]; simp
  have hA_pos : (0 : ℝ) < Nat.card A := Nat.cast_pos.mpr (@Nat.card_pos _ hA_non.to_subtype _)
  have hB_pos : (0 : ℝ) < Nat.card B := Nat.cast_pos.mpr (@Nat.card_pos _ hB_non.to_subtype _)
  rcases lt_or_ge (Nat.card Ax + Nat.card By) (Nat.card A + Nat.card B) with h | h
  · replace h := ih (Nat.card Ax + Nat.card By) (h.trans_le hM) Ax By (mod_cast hAx_fin) hBy_fin
      hAx_non hBy_non rfl
    rcases h with ⟨A', B', hA', hB', hA'_non, hB'_non, hcard_ineq, hdim_ineq⟩
    use A', B'
    have hAx_fin' := Set.finite_coe_iff.mpr hAx_fin
    have hBy_fin' := Set.finite_coe_iff.mpr hBy_fin
    have hA'_fin' := Set.finite_coe_iff.mpr (Set.Finite.subset hAx_fin hA')
    have hB'_fin' := Set.finite_coe_iff.mpr (Set.Finite.subset hBy_fin hB')
    have hAx_non' := Set.nonempty_coe_sort.mpr hAx_non
    have hBy_non' := Set.nonempty_coe_sort.mpr hBy_non
    have hA'_non' := Set.nonempty_coe_sort.mpr hA'_non
    have hB'_non' := Set.nonempty_coe_sort.mpr hB'_non
    have hAx_pos : (0 : ℝ) < Nat.card Ax := Nat.cast_pos.mpr Nat.card_pos
    have hBy_pos : (0 : ℝ) < Nat.card By := Nat.cast_pos.mpr Nat.card_pos
    have hA'_pos : (0 : ℝ) < Nat.card A' := Nat.cast_pos.mpr Nat.card_pos
    have hB'_pos : (0 : ℝ) < Nat.card B' := Nat.cast_pos.mpr Nat.card_pos
    have hAxA_le : (Nat.card Ax : ℝ) ≤ Nat.card A := by gcongr; exact Nat.card_mono A.toFinite hAxA
    have hByB_le : (Nat.card By : ℝ) ≤ Nat.card B := by gcongr; exact Nat.card_mono B.toFinite hByB
    refine ⟨hA'.trans hAxA, hB'.trans hByB, hA'_non, hB'_non, ?_, ?_⟩
    · rw [four_logs hA_pos hB_pos hA'_pos hB'_pos]
      rw [four_logs hAx_pos hBy_pos hA'_pos hB'_pos] at hcard_ineq
      linarith only [hcard, hcard_ineq]
    apply hdim_ineq.trans
    gcongr
    linarith only [Real.log_le_log hAx_pos hAxA_le, Real.log_le_log hBy_pos hByB_le, hcard]
  use A, B
  refine ⟨Eq.subset rfl, Eq.subset rfl, hA_non, hB_non, ?_, ?_⟩
  · have := hA_non.to_subtype
    have := hB_non.to_subtype
    apply LE.le.trans _ <| mul_nonneg (by norm_num) <| setRuzsaDist_nonneg A B
    rw [div_self (by positivity)]
    simp
  have hAx_eq : Ax = A := by
    apply Set.Finite.eq_of_subset_of_card_le A.toFinite hAxA
    linarith only [h, Nat.card_mono B.toFinite hByB]
  have hBy_eq : By = B := by
    apply Set.Finite.eq_of_subset_of_card_le B.toFinite hByB
    linarith only [h, Nat.card_mono A.toFinite hAxA]
  have hN : N = ⊤ := by
    have : (A-A) ∪ (B-B) ⊆ N := by
      rw [← hAx_eq, ← hBy_eq, hAx, hBy]
      intro z hz
      simp only [mk'_apply, mem_union, mem_sub, mem_ofPred_eq] at hz
      refine (QuotientAddGroup.eq_zero_iff z).mp ?_
      rcases hz with ⟨a, ⟨-, ha⟩, a', ⟨-, ha'⟩, haa'⟩ | ⟨b, ⟨-, hb⟩, b', ⟨-,hb'⟩, hbb'⟩
      · rw [← haa']; simp [ha, ha']
      rw [← hbb']; simp [hb, hb']
    rw [← AddSubgroup.closure_le, hnot] at this
    exact top_le_iff.mp this
  have : Nat.card (G ⧸ N) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    constructor
    · rw [hN]
      exact QuotientAddGroup.subsingleton_quotient_top
    infer_instance
  simp only [this, Nat.cast_one, log_one, zero_add] at hdim
  rw [← le_div_iff₀' (by positivity)] at hdim
  convert! le_trans ?_ hdim using 1
  · field_simp
  simp only [Nat.cast_max, max_le_iff, Nat.cast_le]
  exact ⟨AffineSpace.finrank_le_moduleFinrank, AffineSpace.finrank_le_moduleFinrank⟩
```

### child `wlog_notInCoset`: [`PFR/WeakPFR.lean` lines 50-81](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/WeakPFR.lean#L50-L81) ([local copy](code/PFR/WeakPFR.lean))

```lean
/-- Without loss of generality, one can move (up to translation and embedding) any pair A, B of
non-empty sets into a subgroup where they are not in a coset. -/
lemma wlog_notInCoset (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ (G' : AddSubgroup G) (A' B' : Set (G' : Set G)),
    IsShift A A' ∧ IsShift B B' ∧ NotInCoset A' B' := by
  obtain ⟨x, hx⟩ := hA
  obtain ⟨y, hy⟩ := hB
  set G' := AddSubgroup.closure ((A - A) ∪ (B - B)) with hG'
  set A' : Set (G' : Set G) := (↑) ⁻¹' ((-x) +ᵥ A) with hA'
  set B' : Set (G' : Set G) := (↑) ⁻¹' ((-y) +ᵥ B) with hB'
  have hxA : -x +ᵥ A ⊆ range ((↑) : G' → G) := by
    simp only [← singleton_add', ← neg_singleton, neg_add_eq_sub, Subtype.range_coe_subtype]
    exact (sub_subset_sub_left <| singleton_subset_iff.2 hx).trans <| (subset_union_left ..).trans
      AddSubgroup.subset_closure
  have hyB : -y +ᵥ B ⊆ range ((↑) : G' → G) := by
    simp only [← singleton_add', ← neg_singleton, neg_add_eq_sub, Subtype.range_coe_subtype]
    exact (sub_subset_sub_left <| singleton_subset_iff.2 hy).trans <| (subset_union_right ..).trans
      AddSubgroup.subset_closure
  have hA : IsShift A A' := ⟨x, by rwa [hA', Set.image_preimage_eq_of_subset, vadd_neg_vadd]⟩
  have hB : IsShift B B' := ⟨y, by rwa [hB', Set.image_preimage_eq_of_subset, vadd_neg_vadd]⟩
  refine ⟨G', A', B', hA, hB, ?_⟩
  unfold NotInCoset
  convert! AddSubgroup.closure_preimage_eq_top ((A - A) ∪ (B - B))
  simp_rw [preimage_union, hA.sub_self_congr, hB.sub_self_congr]
  rw [preimage_sub, preimage_sub]
  · simp only [A', B', Subtype.image_preimage_coe]
    simp only [SetLike.coe_sort_coe, AddSubgroup.coe_subtype, preimage_inter]
    rw [Subtype.coe_preimage_self, Subtype.coe_preimage_self, Subtype.coe_preimage_self,
      Subtype.coe_preimage_self]
    simp only [univ_inter]
    rfl
  all_goals apply_rules [Subtype.coe_injective, (image_preimage_subset ..).trans, hxA, hyB]
```

### child `weak_PFR_asymm_prelim`: [`PFR/WeakPFR.lean` lines 625-782](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/WeakPFR.lean#L625-L782) ([local copy](code/PFR/WeakPFR.lean))

```lean
/-- Given two non-empty finite subsets A, B of a rank n free Z-module G, there exists a subgroup N
and points x, y in G/N such that the fibers Ax, By of A, B over x, y respectively are non-empty,
one has the inequality $$\log\frac{|A| |B|}{|A_x| |B_y|} ≤ 34 (d[U_A; U_B] - d[U_{A_x}; U_{B_y}])$$
and one has the dimension bound $$n \log 2 ≤ \log |G/N| + 40 d[U_A; U_B]$$. -/
lemma weak_PFR_asymm_prelim (A B : Set G) [A_fin : Finite A] [B_fin : Finite B]
    (hnA : A.Nonempty) (hnB : B.Nonempty) :
    ∃ (N : AddSubgroup G) (x y : G ⧸ N) (Ax By : Set G), Ax.Nonempty ∧ By.Nonempty ∧
    Set.Finite Ax ∧ Set.Finite By ∧ Ax = {z : G | z ∈ A ∧ QuotientAddGroup.mk' N z = x } ∧
    By = {z : G | z ∈ B ∧ QuotientAddGroup.mk' N z = y } ∧
    (log 2) * Module.finrank ℤ G ≤ log (Nat.card (G ⧸ N)) +
      40 * dᵤ[A # B ] ∧ log (Nat.card A) + log (Nat.card B) - log (Nat.card Ax) - log (Nat.card By)
      ≤ 34 * (dᵤ[A # B ] - dᵤ[Ax # By ]) := by
  have : Nonempty A := hnA.to_subtype
  have : Nonempty B := hnB.to_subtype
  set ψ : G →+ G := zsmulAddGroupHom 2
  set G₂ := LinearMap.range (LinearMap.lsmul ℤ G 2)
  set H := ModN G 2
  set φ : G →ₗ[ℤ] H := G₂.mkQ
  let : MeasurableSpace H := ⊤
  have : Finite H := ModN.instFinite
  let h_fintype : Fintype H := .ofFinite H
  have : HasUniqueDiv G :=.of_isTorsionFree ℤ _
  obtain ⟨Ω, mΩ, UA, hμ, hUA_mes, hUA_unif, hUA_mem, hUA_fin⟩ :=
    exists_isUniform_measureSpace' A A_fin hnA
  obtain ⟨Ω', mΩ', UB, hμ', hUB_mes, hUB_unif, hUB_mem, hUB_fin⟩ :=
    exists_isUniform_measureSpace' B B_fin hnB
  obtain ⟨H', hH1, hH2⟩ := PFR_projection (φ ∘ UA) (φ ∘ UB) ℙ ℙ (by fun_prop) (by fun_prop)
  let N := AddSubgroup.comap φ.toAddMonoidHom H'.toAddSubgroup
  set φ' := QuotientAddGroup.mk' N
  have _cGN : Countable (G ⧸ N) := Surjective.countable (QuotientAddGroup.mk'_surjective N)
  have _msGN : MeasurableSingletonClass (G ⧸ N) :=
    ⟨fun x ↦ MeasurableSpace.map_def.mpr .of_discrete⟩
  rcases third_iso H'.toAddSubgroup with ⟨e : H ⧸ H' ≃+ G ⧸ N, he⟩
  rcases single_fibres φ' hnA hnB hUA_mes hUB_mes hUA_unif hUB_unif hUA_mem hUB_mem with
    ⟨x, y, Ax, By, hAx, hBy, hnAx, hnBy, hcard_ineq⟩
  have : Nonempty Ax := hnAx.to_subtype
  have : Nonempty By := hnBy.to_subtype
  have Axf : Finite Ax := by rw [hAx]; infer_instance
  have Byf : Finite By := by rw [hBy]; infer_instance
  have h1 := torsion_dist_shrinking (G := G) (H := H) UA UB ℙ ℙ hUA_mes hUB_mes φ
  have h2 := torsion_dist_shrinking (G := G) (H := H) UB UA ℙ ℙ hUB_mes hUA_mes φ
  rw [rdist_symm] at h2
  rw [← setRuzsaDist_eq_rdist hUA_unif hUB_unif hUA_mes hUB_mes] at h1 h2
  -- using explicit .toFun casts as this saves a lot of heartbeats
  change H[φ ∘ UA] ≤ 10 * dᵤ[A # B] at h1
  change H[φ ∘ UB] ≤ 10 * dᵤ[A # B] at h2
  replace hH1 : log (Nat.card H') ≤ 40 * dᵤ[A # B] := by
    apply hH1.trans
    linarith
  replace h_card : log 2 * Module.finrank ℤ G
      ≤ log (Nat.card (G ⧸ N)) + 40 * dᵤ[A # B] := by
    rw [mul_comm, ← log_rpow (by norm_num)]
    norm_cast
    classical
    rwa [← ModN.natCard_eq, ← Nat.card_congr e.toEquiv, H'.card_eq_card_quotient_mul_card,
      Nat.cast_mul, log_mul, add_comm, add_le_add_iff_left]
    all_goals norm_cast; rw [Nat.card_eq_fintype_card]; exact Fintype.card_ne_zero
  use N, x, y, Ax, By
  refine ⟨hnAx, hnBy, Ax.toFinite, By.toFinite, hAx, hBy, h_card, ?_⟩
  replace hH2 : H[φ'.toFun ∘ UA] + H[φ'.toFun ∘ UB] ≤ 34 * d[φ'.toFun ∘ UA # φ'.toFun ∘ UB] := by
    set X := (H'.mkQ.toFun ∘ φ.toFun) ∘ UA
    set Y := (H'.mkQ.toFun ∘ φ.toFun) ∘ UB
    have hX : Measurable X := Measurable.comp .of_discrete hUA_mes
    have hY : Measurable Y := Measurable.comp .of_discrete hUB_mes
    change H[X] + H[Y] ≤ 34 * d[X # Y] at hH2
    have ha : φ'.toFun ∘ UA = e.toFun ∘ X := by ext x; exact (he (UA x)).symm
    have hb : φ'.toFun ∘ UB = e.toFun ∘ Y := by ext x; exact (he (UB x)).symm
    have he_inj : Injective e.toFun := e.injective
    rw [ha, hb, entropy_comp_of_injective _ hX _ he_inj, entropy_comp_of_injective _ hY _ he_inj]
    have : d[e.toFun ∘ X # e.toFun ∘ Y] = d[X # Y] := rdist_of_inj hX hY e.toAddMonoidHom he_inj
    rwa [this]
  set X : Ω → G ⧸ N := φ'.toFun ∘ UA
  set Y : Ω' → G ⧸ N := φ'.toFun ∘ UB
  have hX : Measurable X := Measurable.comp .of_discrete hUA_mes
  have hY : Measurable Y := Measurable.comp .of_discrete hUB_mes
  rcases le_iff_lt_or_eq.mp (rdist_nonneg (μ := ℙ) (μ' := ℙ) hX hY) with h | h
  swap
  · rw [← h] at hH2
    have hH2A : H[X] ≥ 0 := entropy_nonneg _ _
    have hH2B : H[Y] ≥ 0 := entropy_nonneg _ _
    have hH2A' : H[X] ≤ 0 := by linarith only [hH2, hH2A, hH2B]
    have hH2B' : H[Y] ≤ 0 := by linarith only [hH2, hH2A, hH2B]
    rcases const_of_nonpos_entropy (μ := ℙ) hX hH2A' with ⟨x', hx⟩
    rcases const_of_nonpos_entropy (μ := ℙ) hY hH2B' with ⟨y', hy⟩
    have hAAx {z : G} (hz : z ∈ A) : φ'.toFun z = x' := by
      change (ℙ).real (UA⁻¹' (φ'⁻¹' {x'})) = 1 at hx
      rw [← MeasureTheory.map_measureReal_apply hUA_mes .of_discrete] at hx
      set Af := A.toFinite.toFinset
      have hUAf : IsUniform Af UA := by
        convert hUA_unif; simp only [Af, Set.Finite.coe_toFinset]
      have hnAf : 0 < Nat.card Af := by simp only [Af, Set.Finite.mem_toFinset, Nat.card_pos]
      have hzf : z ∈ Af := by simp [Af, Set.Finite.mem_toFinset, hz]
      have : (Measure.map UA ℙ).real {z} > 0 := by
        rw [IsUniform.measureReal_preimage_of_mem' hUAf hUA_mes hzf]
        simp only [one_div, gt_iff_lt, inv_pos, Nat.cast_pos, Finset.card_pos]
        exact (Finite.toFinset_nonempty (toFinite A)).mpr hnA
      replace this := single ((ℙ).map UA) hx this
      rwa [Set.mem_preimage, Set.mem_singleton_iff] at this
    have hxx : Ax = A := by
      have h : hnAx.some ∈ Ax := hnAx.some_mem
      simp only [hAx, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, mem_inter_iff, mem_preimage,
        mem_singleton_iff, inter_eq_left] at h ⊢
      have := hAAx h.1
      simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, h.2] at this
      intro z hz
      simp only [this, mem_preimage, mem_singleton_iff]
      exact hAAx hz
    have hBBy {z : G} (hz : z ∈ B) : φ'.toFun z = y' := by
      change (ℙ).real (UB⁻¹' (φ'⁻¹' {y'})) = 1 at hy
      rw [← MeasureTheory.map_measureReal_apply hUB_mes .of_discrete] at hy
      set Bf := B.toFinite.toFinset
      have hUBf : IsUniform Bf UB := by convert hUB_unif; simp only [Bf, Set.Finite.coe_toFinset]
      have hnBf : 0 < Nat.card Bf := by simp only [Bf, Set.Finite.mem_toFinset, Nat.card_pos]
      have hzf : z ∈ Bf := by simp [Bf, Set.Finite.mem_toFinset, hz]
      have : (Measure.map UB ℙ).real {z} > 0 := by
        rw [IsUniform.measureReal_preimage_of_mem' hUBf hUB_mes hzf]
        simp only [one_div, gt_iff_lt, inv_pos, Nat.cast_pos, Finset.card_pos]
        exact (Finite.toFinset_nonempty (toFinite B)).mpr hnB
      replace this := single ((ℙ).map UB) hy this
      rwa [Set.mem_preimage, Set.mem_singleton_iff] at this
    have hyy : By = B := by
      have h : hnBy.some ∈ By := hnBy.some_mem
      simp only [hBy, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, mem_inter_iff, mem_preimage,
        mem_singleton_iff, inter_eq_left] at h ⊢
      have := hBBy h.1
      simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, h.2] at this
      intro z hz
      simp only [this, mem_preimage, mem_singleton_iff]
      exact hBBy hz
    simp [hxx, hyy]
  have := calc d[φ'.toFun ∘ UA # φ'.toFun ∘ UB] *
    (log (Nat.card A) + log (Nat.card B) - log (Nat.card Ax) - log (Nat.card By))
    _ = d[φ'.toFun ∘ UA # φ'.toFun ∘ UB] *
        log (Nat.card A * Nat.card B / ((Nat.card Ax) * (Nat.card By))) := by
      congr
      convert (four_logs ?_ ?_ ?_ ?_).symm
      all_goals norm_cast; exact Nat.card_pos
    _ ≤ (H[φ'.toFun ∘ UA] + H[φ'.toFun ∘ UB]) * (d[UA # UB] - dᵤ[Ax # By]) := hcard_ineq
    _ ≤ (34 * d[φ'.toFun ∘ UA # φ'.toFun ∘ UB]) * (d[UA # UB] - dᵤ[Ax # By]) := by
      apply mul_le_mul_of_nonneg_right hH2
      have := rdist_le_avg_ent (Measurable.comp (.of_discrete (f := φ'.toFun)) hUA_mes)
        (Measurable.comp (.of_discrete (f := φ'.toFun)) hUB_mes)
      replace this : 0 < H[φ'.toFun ∘ UA] + H[φ'.toFun ∘ UB] := by linarith
      rw [← mul_le_mul_iff_right₀ this]
      apply le_trans _ hcard_ineq
      rw [mul_zero]
      change 0 ≤ d[φ'.toFun ∘ UA # φ'.toFun ∘ UB]
        * log (Nat.card A * Nat.card B / ((Nat.card Ax) * (Nat.card By)))
      rw [← mul_zero d[φ'.toFun ∘ UA # φ'.toFun ∘ UB], mul_le_mul_iff_right₀ h]
      apply Real.log_nonneg
      rw [one_le_div (mod_cast mul_pos Nat.card_pos Nat.card_pos)]
      gcongr
      · apply Nat.card_mono (Set.toFinite A) (hAx ▸ Set.inter_subset_left)
      · apply Nat.card_mono (Set.toFinite B) (hBy ▸ Set.inter_subset_left)
    _ = d[φ'.toFun ∘ UA # φ'.toFun ∘ UB] * (34 * (d[UA # UB] - dᵤ[Ax # By])) := by ring
    _ = d[φ'.toFun ∘ UA # φ'.toFun ∘ UB] * (34 * (dᵤ[A # B] - dᵤ[Ax # By])) := by
      rw [←  setRuzsaDist_eq_rdist hUA_unif hUB_unif hUA_mes hUB_mes]
  exact (mul_le_mul_iff_right₀ h).mp this
```

### child `conclusion_transfers`: [`PFR/WeakPFR.lean` lines 813-857](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/WeakPFR.lean#L813-L857) ([local copy](code/PFR/WeakPFR.lean))

```lean
omit [Module.Finite ℤ G] [Module.Free ℤ G] in
lemma conclusion_transfers {A B : Set G} (G' : AddSubgroup G) (A' B' : Set (G' : Set G))
    (hA : IsShift A A') (hB : IsShift B B') [Finite A'] [Finite B']
    (hA' : A'.Nonempty) (hB' : B'.Nonempty)
    (h : WeakPFRAsymmConclusion A' B') : WeakPFRAsymmConclusion A B := by
  have : Nonempty A' := hA'.to_subtype
  have : Nonempty B' := hB'.to_subtype
  rcases h with ⟨A'', B'', hA'', hB'', hA''_non, hB''_non, hcard_ineq, hdim_ineq⟩
  rcases hA with ⟨x, hA⟩
  set f : G' → G := fun a ↦ (a : G) + x
  have hf : Injective f := by simp [Injective, f]
  have hA' : A = f '' A' := by
    simp_rw [hA, ← Set.image_vadd, Set.image_image, vadd_eq_add, f, add_comm]; rfl
  rcases hB with ⟨y, hB⟩
  set g : G' → G := fun a ↦ (a : G) + y
  have hg : Injective g := by simp [Injective, g]
  have hB' : B = g '' B' := by
    simp_rw [hB, ← Set.image_vadd, Set.image_image, vadd_eq_add, g, add_comm]; rfl
  use f '' A'', g '' B''
  have : dᵤ[A # B] = dᵤ[A' # B'] := by
    rw [← setRuzsaDist_of_inj _ _ (φ := G'.subtype) Subtype.val_injective,
      ← setRuzsaDist_add_const (G'.subtype '' A') (G'.subtype '' B') x y]
    congr
    · rw [hA]
      ext y
      simp [Set.mem_vadd_set_iff_neg_vadd_mem, add_comm]
    · rw [hB]
      ext x
      simp [Set.mem_vadd_set_iff_neg_vadd_mem, add_comm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hA', hf, hA'']
  · simp [hB', hg, hB'']
  · simp [hA''_non]
  · simp [hB''_non]
  · convert hcard_ineq using 2
    · congr 3
      · rw [hA', Nat.card_image_of_injective hf]
      · rw [hB', Nat.card_image_of_injective hg]
      · rw [Nat.card_image_of_injective hf]
      rw [Nat.card_image_of_injective hg]
  · convert! LE.le.trans _ hdim_ineq using 2
    norm_cast
    apply max_le_max
    · exact (dimension_of_shift A'' x).le
    · exact (dimension_of_shift B'' y).le
```

### How the parts fit

The parent proof is organised as a `suffices` (lines 869-873) that swaps the
goal for a stronger one: for *any* group `G` with the same instances, and *any*
`A, B` with `Nat.card A + Nat.card B ≤ M` **and** `NotInCoset A B`, the
conclusion holds. The comment at line 868 says the plan in one line:
"wlog we can assume A, B are not in cosets of a smaller subgroup". The rest of
the proof closes the original goal from the strengthened one, then proves the
strengthened one.

```
weak_PFR_asymm (parent, 859-971)
├── wlog_notInCoset (50-81)          — reduces the goal to the NotInCoset case
├── weak_PFR_asymm_prelim (625-782)  — the induction step: subgroup N + fibres + bounds
└── conclusion_transfers (814-857)   — maps the strengthened conclusion back
```

The glue proceeds in three moves:

1. **Reduction** (lines 874-902): `wlog_notInCoset hA₀ hB₀` returns a subgroup
   `G'`, sets `A', B'` with `IsShift A A'`, `IsShift B B'`, and `NotInCoset A'
   B'`. The proof rebuilds the instances of `G'` (`Module.Finite`, `Module.Free`),
   transfers the card equality, and feeds `G', A', B'` to the strengthened
   hypothesis `H`, then closes with `conclusion_transfers G' A' B' …`.

2. **Induction step** (lines 903-935): inside the strengthened statement,
   `weak_PFR_asymm_prelim A B hA_non hB_non` produces a subgroup `N`, points
   `x, y : G ⧸ N`, and non-empty fibres `Ax, By` with the card bound and the
   dimension bound. When `Nat.card Ax + Nat.card By < Nat.card A + Nat.card B`
   the induction hypothesis `ih` recurses on `Ax, By`, and the card/log
   inequality is reassembled with `four_logs`.

3. **Equality case** (lines 936-971): when the sum does not decrease, the proof
   shows `Ax = A`, `By = B`, hence `N = ⊤` and `Nat.card (G ⧸ N) = 1`; the
   dimension bound then collapses through `QuotientAddGroup.subsingleton_quotient_top`
   and `AffineSpace.finrank_le_moduleFinrank`.

Why each child is a good leaf:

- `wlog_notInCoset` is self-contained: it closes on its own by constructing the
  subgroup `G' := AddSubgroup.closure ((A - A) ∪ (B - B))` and reducing the
  `NotInCoset` obligation to `AddSubgroup.closure_preimage_eq_top` (line 161).
  It is exactly the reduction the `suffices` needs and nothing more.
- `weak_PFR_asymm_prelim` is the hard leaf, but it is *one statement* whose
  proof closes from named siblings lower in the file (`PFR_projection`,
  `third_iso`, `single_fibres`, `torsion_dist_shrinking`, `single`,
  `four_logs`), ending in a single `calc` (line 782). It packages everything
  the induction needs (the subgroup, the fibres, and both bounds) behind one
  name.
- `conclusion_transfers` is a pure transfer: it closes on its own by pulling the
  witnesses `A'', B''` back through the shift embeddings `f`, `g` and using
  `dimension_of_shift` for the dimension bound, so the parent can forget the
  subgroup it descended into.

The glue also invokes the one-line log identity `four_logs` (line 408) directly
(lines 930-931), but it is a shared arithmetic utility rather than a lemma
written for this theorem, so it is not counted among the children.

## Why it is good

1. *(check)* A declaration named `weak_PFR_asymm` starts in lines 859-971 of
   `PFR/WeakPFR.lean`. The `suffices` inside it is the whole move: lines 869-873
   strengthen the goal before any induction runs.
2. *(check)* The parent site cites each of its three children in turn:
   `wlog_notInCoset` (line 874), `weak_PFR_asymm_prelim` (line 905) and
   `conclusion_transfers` (line 902), so the glue really is assembled from the
   named lemmas.
3. *(check)* No `sorry`, `admit` or `axiom` occurs anywhere in the copied file
   (lines 1-1079), so the strengthened statement is actually proved, not
   assumed.
4. *(measurement)* The glue is 113 lines; the three children are 32, 158 and 45
   lines (235 total). The parent's 113 lines are thin — a `suffices`, two
   `obtain`s and two `rcases` branches — while the real content sits in the
   children.
5. *(measurement)* A chain of at least six project lemmas runs below the main
   theorem: `weak_PFR_asymm → weak_PFR_asymm_prelim → PFR_projection →
   PFR_projection' → app_ent_PFR → app_ent_PFR' → ent_of_proj_le` (depth at
   least 6), and `app_ent_PFR'` also calls `diff_ent_le_rdist` and
   `entropic_PFR_conjecture_improv`. The prelim lemma hides a further chain, so
   the theorem's skeleton is shallow on top of a deep leaf.
6. *(author-statement)* The author writes the plan as an in-proof comment,
   "wlog we can assume A, B are not in cosets of a smaller subgroup"
   (code/PFR/WeakPFR.lean line 868), immediately before the `suffices`.

This entry supports survey F §10 rule 8 (backward rule and `suffices` as a
template): the strengthened statement is introduced with a single `suffices`,
and the two obligations it creates — reduce to the stronger hypothesis, then
transfer back — are exactly the two cheap children `wlog_notInCoset` and
`conclusion_transfers`.

In my opinion the detail worth copying is the *pairing*: the `suffices` is only
worth it because a matching reduction lemma and transfer lemma already exist, so
the strengthening costs two one-line invocations instead of one hard proof.

## When to use it, and when not

Use it when the direct induction hypothesis is too weak and the missing
strength can be stated as an extra hypothesis on the sets (here: not lying in a
coset of a proper subgroup), with two cheap lemmas available — one that reduces
the general case to the strengthened case (`wlog_notInCoset`) and one that
transfers the conclusion back (`conclusion_transfers`). The pattern is a
`wlog`/`suffices` pair.

Avoid it when the reduction or the transfer is itself the hard content (then
it is the theorem, not a wrapper); when the strengthened statement is not
actually stronger over the induction variable, so the recursion does not
decrease; or when the strengthening changes the group or structure enough that
the transfer back is not a bijection-preserving map (here it relies on shifts
`x +ᵥ ·` being injective and Ruzsa-distance invariant).

## Consequences

The move creates three obligations, one per part of the skeleton: reduce to the
strengthened case (`wlog_notInCoset`), prove the strengthened statement (the
strong induction with `NotInCoset` assumed), and transfer the conclusion back
(`conclusion_transfers`). The strengthened statement must re-generalise over the
group `G` (the `suffices` re-abstracts `G` and all its instance arguments), and
the induction must actually decrease: the proof branches on
`lt_or_ge (Nat.card Ax + Nat.card By) (Nat.card A + Nat.card B)`, recursing when
it decreases and closing an equality case (`N = ⊤`,
`Nat.card (G ⧸ N) = 1`) otherwise.

Failure modes: if the transfer or the reduction carries a real bound, the
`suffices` hides it and a one-sided inequality can silently weaken the result;
`conclusion_transfers` must preserve both the size and the dimension bound, so
it cannot be a bare projection. If `wlog_notInCoset`'s embedding ever failed to
be injective or Ruzsa-distance preserving, the strengthened proof would prove a
statement about different sets than the original.

## Verification

<!-- verification:start -->
Status: **verified**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push.yml build job runs leanprover/lean-action@v1.2.0 (whole-project lake build) on push to default branch master; pinned commit 1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a is on master (branches-where-head); the build compiles PFR/WeakPFR.lean | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: wlog_notInCoset@PFR/WeakPFR.lean:874, weak_PFR_asymm_prelim@PFR/WeakPFR.lean:905, conclusion_transfers@PFR/WeakPFR.lean:902; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(weak_PFR_asymm, PFR/WeakPFR.lean, 859-971) -> declared: weak_PFR_asymm is declared at PFR/WeakPFR.lean:863 | check_claims.py |
| 2 | verified | cites(parent, wlog_notInCoset) -> cites: wlog_notInCoset occurs at PFR/WeakPFR.lean:874 | check_claims.py |
| 3 | verified | cites(parent, weak_PFR_asymm_prelim) -> cites: weak_PFR_asymm_prelim occurs at PFR/WeakPFR.lean:905 | check_claims.py |
| 4 | verified | cites(parent, conclusion_transfers) -> cites: conclusion_transfers occurs at PFR/WeakPFR.lean:902 | check_claims.py |
| 5 | verified | no_sorry(PFR/WeakPFR.lean, 1-1079) -> no_sorry: none of sorry, admit, axiom in PFR/WeakPFR.lean:1-1079 | check_claims.py |
| 6 | verified | lines(parent, 113) -> lines: site parent has 113 lines | check_claims.py |
| 7 | refuted | The 5 stated links are each at the cited lines (weak_PFR_asymm calls weak_PFR_asymm_prelim at 905, weak_PFR_asymm_prelim calls PFR_projection at 651, PFR_projection calls PFR_projection' at 396, PFR_projection' calls app_ent_PFR at 321, app_ent_PFR calls app_ent_PFR' at 295). But the chain does not stop at app_ent_PFR': its body (lines 244-287) calls project lemmas entropic_PFR_conjecture_improv (line 257, imported via PFR.ImprovedPFR), ent_of_proj_le (lines 265-266) and diff_ent_le_rdist (lines 278-279), so a chain of 6 lemmas below weak_PFR_asymm exists, contradicting 'longest ... five lemmas (depth 5)'. | verifier |
| 8 | verified | Line 868 is exactly '-- wlog we can assume A, B are not in cosets of a smaller subgroup', immediately followed at line 869 by 'suffices H : forall (G : Type _) ...' whose binder list includes '(_hnot : NotInCoset A B)' (line 873), matching the claim. | verifier |
| 9 | verified | grep -n on code/PFR/WeakPFR.lean confirms every cited call site: weak_PFR_asymm_prelim at 905, PFR_projection at 651, PFR_projection' at 396, app_ent_PFR at 321, app_ent_PFR' at 295; app_ent_PFR' (lemma at 244) calls entropic_PFR_conjecture_improv at 257, ent_of_proj_le at 265-266 and diff_ent_le_rdist at 279-280. All six lemmas are declared in the same file (244, 291, 303, 392, 629, 863), so the chain is at least six project lemmas and does not end at app_ent_PFR'. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | object | Decomposition, children, closing and shape all correct: parent weak_PFR_asymm (859-971 = 113 lines) cites wlog_notInCoset@874, conclusion_transfers@902, weak_PFR_asymm_prelim@905; child sites 50-81/625-782/813-857 = 32/158/45 lines; chain weak_PFR_asymm->weak_PFR_asymm_prelim(905)->PFR_projection(651)->PFR_projection'(396)->app_ent_PFR(321)->app_ent_PFR'(295)->ent_of_proj_le(265-266) gives depth 6; four_logs@408 is a shared utility, excluded with justification. One factual error: entry.json children[0].closed_by and README 'How the parts fit' cite the NotInCoset closure at 'line 161', but AddSubgroup.closure_preimage_eq_top is applied at line 72 (line 161 is inside an unrelated entropy proof). Fix: change 161 to 72 in both places. | reviewer-correctness |
| generality | accept | Generality lens. (1) Move stated beyond the example: applicability.goal_shape/use_when/avoid_when and README 'When to use it, and when not' describe the move generally — an extra hypothesis added via suffices/wlog plus two cheap lemmas (reduce wlog_notInCoset, transfer conclusion_transfers); the suffices re-abstracts G and instance args (verified sed 859-873), so re-generalisation is real, not asserted. (2) when-not-to-use and consequences are honest and specific: avoid_when names two failure modes (hard reduce/transfer; recursion not decreasing) and README adds a third (transfer must be bijection-preserving / Ruzsa-invariant), which conclusion_transfers actually satisfies via Injective f/g + setRuzsaDist_of_inj/add_const; consequences names the three obligations and the failure mode (one-sided inequality silently weakening the bound). (3) 'Why each child is a good leaf' answers the bounded-prover question: wlog_notInCoset and conclusion_transfers are self-contained (close on their own), and the hard leaf weak_PFR_asymm_prelim is one named statement packaging subgroup+fibres+bounds behind one name, with thin 113-line glue over 235 lines of children (measurement claims 4/6, depth-6 chain). Minor non-blocking nit: the prose bullet cites AddSubgroup.closure_preimage_eq_top at 'line 161' but it sits at ~line 70 of the file — a locator typo, not a generality defect. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note all consistent and traceable. Commit 1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a is identical in entry.json, source.json, SOURCE.md, and every permalink (README header's short 1ef23c3c5a83 is the same commit's prefix). Licence Apache-2.0 matches entry.json, README, source.json and SOURCE.md, and sources/pfr/upstream-LICENSE is genuinely Apache License 2.0. Copied code/PFR/WeakPFR.lean is 60974 bytes with sha256 f5bf403c...660, matching files[0] (bytes 60974, same sha256); check_provenance.py passes byte-identical at the pinned commit. Source note ../../sources/pfr/SOURCE.md exists and carries the licence text and attribution. All four site permalinks resolve to the cited line ranges of the same file at the same commit. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/teorth/pfr at commit `1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a`, under `Apache-2.0`; see the [source note](../../sources/pfr/SOURCE.md) for the licence text and attribution.
