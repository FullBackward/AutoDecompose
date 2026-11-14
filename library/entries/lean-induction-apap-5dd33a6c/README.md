# Induction on the codimension-increase step for the finite-field 3AP bound (ff)

| | |
|---|---|
| Kind | instance |
| Move | induction |
| Language | lean |
| Status | accepted |
| Source | [apap](../../sources/apap/SOURCE.md) at `fb5cb9c4f594` |
| Licence | `Apache-2.0` |

## Intent

Reduce the finite-field 3AP bound `finrank (ZMod q) G ≤ 2^148 * 𝓛 A.dens^9` to an
induction on the number of density-increment steps: a successor step applies
`di_in_ff` to descend from `(V, B)` to a subspace `V' ≤ V` of bounded codimension
where the density of the translated preimage `B'` rises by the fixed factor
`1 + 64⁻¹`; the loop terminates because density is at most 1, leaving an inner
product that the 3AP-free identity rewrites to a bound on the original density.

## The decomposition

### parent `ff`: [`APAP/FiniteField.lean` lines 511-645](https://github.com/YaelDillies/apap/blob/fb5cb9c4f594cbeeb160c715618d13640984c521/APAP/FiniteField.lean#L511-L645) ([local copy](code/APAP/FiniteField.lean))

```lean
public theorem ff (hq₃ : 3 ≤ q) (hq : q.Prime) (hA₀ : A.Nonempty) (hA : ThreeAPFree (α := G) A) :
    finrank (ZMod q) G ≤ 2 ^ 148 * 𝓛 A.dens ^ 9 := by
  let n : ℝ := finrank (ZMod q) G
  let α : ℝ := A.dens
  have : 1 < (q : ℝ) := mod_cast hq₃.trans_lt' (by norm_num)
  have : 1 ≤ (q : ℝ) := this.le
  have : NeZero q := ⟨by positivity⟩
  have : Fact q.Prime := ⟨hq⟩
  have hq' : Odd q := hq.odd_of_ne_two <| by rintro rfl; simp at hq₃
  have : 1 ≤ α⁻¹ := (one_le_inv₀ (by positivity)).2 (by simp [α])
  have hα₀ : 0 < α := by positivity
  have : 0 ≤ log α⁻¹ := log_nonneg ‹_›
  have : 0 < 𝓛 α := by positivity
  have : 0 < log q := log_pos ‹_›
  obtain hα | hα := le_total (q ^ (n / 2) : ℝ) (2 * α⁻¹ ^ 2)
  · rw [rpow_le_iff_le_log, log_mul, log_pow, Nat.cast_two, ← mul_div_right_comm,
      mul_div_assoc, ← le_div_iff₀] at hα
    any_goals positivity
    calc
      _ ≤ (log 2 + 2 * log α⁻¹) / (log q / 2) := hα
      _ = 4 / log q * (log 2 / 2 + log α⁻¹) := by ring
      _ ≤ 2 ^ 148 * 𝓛 α ^ 9 := by
        grw [← hq₃, pow_succ _ 8, ← mul_assoc, log_two_lt_d9]
        gcongr
        · norm_cast
          grw [← log_three_gt_d9, ← ‹1 ≤ α⁻¹›]
          norm_num
        · bound
  have ind (i : ℕ) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Fintype V) (_ : DecidableEq V) (_ : Module (ZMod q) V)
      (B : Finset V), n ≤ finrank (ZMod q) V + 2 ^ 140 * i * 𝓛 α ^ 8 ∧ ThreeAPFree (B : Set V)
        ∧ α ≤ B.dens ∧
      (B.dens < (65 / 64 : ℝ) ^ i * α →
        2⁻¹ ≤ card V * ⟪μ_[ℝ] B ∗ᵈ μ B, μ (B.image (2 • ·))⟫_[ℝ]) := by
    induction i with
    | zero =>
      classical
      exact ⟨G, inferInstance, inferInstance, inferInstance, inferInstance, A, by simp [n], hA,
        by simp [α], by simp [α, nnratCast_dens]⟩
    | succ i ih =>
    obtain ⟨V, _, _, _, _, B, hV, hB, hαβ, hBV⟩ := ih
    obtain hB' | hB' := le_or_gt 2⁻¹ (card V * ⟪μ_[ℝ] B ∗ᵈ μ B, μ (B.image (2 • ·))⟫_[ℝ])
    · exact ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, B,
        hV.trans (by gcongr; exact i.le_succ), hB, hαβ, fun _ ↦ hB'⟩
    let : MeasurableSpace V := ⊤
    have : 0 < 𝓛 B.dens := curlog_pos (by positivity) (by simp)
    have : 2⁻¹ ≤ |card V * ⟪μ_[ℝ] B ∗ᵈ μ B, μ (B.image (2 • ·))⟫_[ℝ] - 1| := by
      rw [abs_sub_comm, le_abs, le_sub_comm]
      norm_num at hB' ⊢
      exact .inl hB'.le
    obtain ⟨V', _, hVV', hv'⟩ := di_in_ff hq (by positivity) two_inv_lt_one (by
      rwa [Finset.dens_image (Nat.Coprime.nsmul_right_bijective _)]
      simpa [Module.card_eq_pow_finrank (K := ZMod q) (V := V), ZMod.card] using hq'.pow) hα₀ this
    rw [dLinftyNorm_eq_iSup_norm, ← Finset.sup'_univ_eq_ciSup, Finset.le_sup'_iff] at hv'
    obtain ⟨x, -, hx⟩ := hv'
    let B' : Finset V' := (-x +ᵥ B).preimage (↑) Set.injOn_subtype_val
    have hβ := calc
      ((1 + 64⁻¹ : ℝ) * B.dens : ℝ) = (1 + 2⁻¹ / 32) * B.dens := by ring
      _ ≤ ‖(𝟭_[(B : Set V), ℝ] ∗ᵈ μ (V' : Set V).toFinset) x‖ := hx
      _ = B'.dens := by
        rw [Real.norm_of_nonneg (ddconv_apply_nonneg Set.indicator_one_nonneg mu_nonneg _),
          dens_addSubgroup_preimage_vadd_eq_indicator_one_ddconv_mu]
    refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, B', ?_, ?_, ?_,
      fun h ↦ ?_⟩
    · calc
        n ≤ finrank (ZMod q) V + 2 ^ 140 * i * 𝓛 α ^ 8 := hV
        _ ≤ finrank (ZMod q) V' + ↑(finrank (ZMod q) V - finrank (ZMod q) V') +
            2 ^ 140 * i * 𝓛 α ^ 8 := by gcongr; norm_cast; exact le_add_tsub
        _ ≤ finrank (ZMod q) V' + 2 ^ 128 * 𝓛 B.dens ^ 4 * 𝓛 α ^ 4 / 2⁻¹ ^ 12 +
            2 ^ 140 * i * 𝓛 α ^ 8 := by gcongr
        _ ≤ finrank (ZMod q) V' + 2 ^ 128 * 𝓛 α ^ 4 * 𝓛 α ^ 4 / 2⁻¹ ^ 12 +
            2 ^ 140 * i * 𝓛 α ^ 8 := by have := hα₀.trans_le hαβ; gcongr
        _ = _ := by push_cast; ring
    · exact .of_image .subtypeVal Set.injOn_subtype_val (Set.subset_univ _)
        (hB.vadd_set (a := -x) |>.mono <| by simp [B'])
    · calc
        α ≤ B.dens := hαβ
        _ ≤ (1 + 64⁻¹) * B.dens := by simp [one_add_mul, NNRat.cast_nonneg]
        _ ≤ B'.dens := hβ
    · refine (h.not_ge <| ?_).elim
      calc
        (65 / 64) ^ (i + 1) * α = (1 + 64⁻¹) * ((65 / 64) ^ i * α) := by ring
        _ ≤ (1 + 64⁻¹) * B.dens := by gcongr; simpa [hB'.not_ge] using hBV
        _ ≤ B'.dens := hβ
  obtain ⟨V, _, _, _, _, B, hV, hB, hαβ, hBV⟩ := ind ⌊𝓛 α / log (65 / 64)⌋₊
  let β : ℝ := B.dens
  have aux : 0 < log (65 / 64) := log_pos (by norm_num)
  specialize hBV <| by
    calc
      _ ≤ (1 : ℝ) := mod_cast dens_le_one
      _ < _ := ?_
    rw [← inv_lt_iff_one_lt_mul₀, lt_pow_iff_log_lt, ← div_lt_iff₀]
    any_goals positivity
    calc
      log α⁻¹ / log (65 / 64)
        < ⌊log α⁻¹ / log (65 / 64)⌋₊ + 1 := Nat.lt_floor_add_one _
      _ = ⌊(log (65 / 64) + log α⁻¹) / log (65 / 64)⌋₊ := by
        rw [add_comm (log _), ← div_add_one aux.ne', Nat.floor_add_one, Nat.cast_succ]
        bound
      _ ≤ ⌊𝓛 α / log (65 / 64)⌋₊ := by
        gcongr
        calc
          log (65 / 64) ≤ 65/64 - 1 := log_le_sub_one_of_pos <| by norm_num
          _ ≤ 1 := by norm_num
  rw [hB.wInner_one_mu_ddconv_mu_mu_two_smul_mu] at hBV
  swap
  · simpa [Module.card_eq_pow_finrank (K := ZMod q) (V := V), ZMod.card] using hq'.pow
  suffices h : (q ^ (n - 2 ^ 147 * 𝓛 α ^ 9) : ℝ) ≤ q ^ (n / 2) by
    rwa [rpow_le_rpow_left_iff ‹_›, sub_le_comm, sub_half, div_le_iff₀' zero_lt_two, ← mul_assoc,
      ← pow_succ'] at h
  calc
    _ ≤ ↑q ^ (finrank (ZMod q) V : ℝ) := by
      gcongr
      rw [sub_le_comm]
      calc
        n - finrank (ZMod q) V ≤ 2 ^ 140 * ⌊𝓛 α / log (65 / 64)⌋₊ * 𝓛 α ^ 8 := by
          rwa [sub_le_iff_le_add']
        _ ≤ 2 ^ 140 * (𝓛 α / log (65 / 64)) * 𝓛 α ^ 8 := by
          gcongr; exact Nat.floor_le (by positivity)
        _ = 2 ^ 140 * (log (65 / 64)) ⁻¹ * 𝓛 α ^ 9 := by ring
        _ ≤ 2 ^ 140 * 2 ^ 7 * 𝓛 α ^ 9 := by
          gcongr
          refine inv_le_of_inv_le₀ (by positivity) ?_
          calc
            (2 ^ 7)⁻¹ ≤ 1 - (65 / 64)⁻¹ := by norm_num
            _ ≤ log (65 / 64) := one_sub_inv_le_log_of_pos (by positivity)
        _ = 2 ^ 147 * 𝓛 α ^ 9 := by ring
    _ = ↑(card V) := by simp [Module.card_eq_pow_finrank (K := ZMod q) (V := V)]
    _ ≤ 2 * β⁻¹ ^ 2 := by
      rw [← natCast_card_mul_nnratCast_dens, mul_pow, mul_inv, ← mul_assoc,
        ← div_eq_mul_inv (card V : ℝ), ← zpow_one_sub_natCast₀ (by positivity)] at hBV
      have : 0 < (card V : ℝ) := by positivity
      simpa [le_inv_mul_iff₀, mul_inv_le_iff₀, this, zero_lt_two, mul_comm] using hBV
    _ ≤ 2 * α⁻¹ ^ 2 := by gcongr
    _ ≤ _ := hα
```

### child `di_in_ff`: [`APAP/FiniteField.lean` lines 332-509](https://github.com/YaelDillies/apap/blob/fb5cb9c4f594cbeeb160c715618d13640984c521/APAP/FiniteField.lean#L332-L509) ([local copy](code/APAP/FiniteField.lean))

```lean
public lemma di_in_ff [DecidableEq G] [MeasurableSpace G] [DiscreteMeasurableSpace G] (hq : q.Prime)
    (hε₀ : 0 < ε) (hε₁ : ε < 1) (hγC : γ ≤ C.dens) (hγ : 0 < γ)
    (hAC : ε ≤ |card G * ⟪μ_[ℝ] A ∗ᵈ μ A, μ C⟫_[ℝ] - 1|) :
    ∃ (V : Submodule (ZMod q) G) (_ : DecidablePred (· ∈ V)),
        ↑(finrank (ZMod q) G - finrank (ZMod q) V) ≤
            2 ^ 128 * 𝓛 A.dens ^ 4 * 𝓛 γ ^ 4 / ε ^ 12 ∧
          (1 + ε / 32) * A.dens ≤ ‖𝟭_[(A : Set G), ℝ] ∗ᵈ μ (Set.toFinset V)‖_[∞] := by
  have hγ₁ : γ ≤ 1 := hγC.trans (by norm_cast; exact dens_le_one)
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · refine ⟨⊤, Classical.decPred _, ?_, by simp⟩
    simp only [finrank_top, tsub_self, CharP.cast_eq_zero, dens_empty, NNRat.cast_zero, inv_zero,
      log_zero, add_zero, one_pow, mul_one]
    positivity
  have hε₁' : 1 ≤ ε⁻¹ := (one_le_inv₀ hε₀).2 hε₁.le
  let α : ℝ := A.dens
  have hα₀ : 0 < α := by positivity
  have hα₁ : α ≤ 1 := by unfold α; exact mod_cast A.dens_le_one
  have : 0 ≤ log γ⁻¹ := log_nonneg <| (one_le_inv₀ hγ).2 hγ₁
  have : 0 < 𝓛 γ := curlog_pos hγ.le hγ₁
  have : 1 ≤ 𝓛 γ := one_le_curlog hγ.le hγ₁
  let p : ℕ := 2 * ⌈𝓛 γ⌉₊
  have hpupper : p ≤ 4 * 𝓛 γ := by
    unfold p; push_cast; grw [Nat.ceil_le_two_mul (by linarith)]; grind
  have : 0 < p := by positivity
  let f : G → ℝ := balance (μ A)
  obtain ⟨p', hp'upper, unbalancing⟩ :
    ∃ p' : ℕ, p' ≤ 2 ^ 10 * (ε / 2)⁻¹ ^ 2 * p ∧
      1 + ε / 2 / 2 ≤ ‖card G • (f ○ᵈ f) + 1‖_[p', μ univ] := by
    refine unbalancing _ (mul_ne_zero two_ne_zero (Nat.ceil_pos.2 <| curlog_pos hγ.le hγ₁).ne')
      (ε / 2) (by positivity) (div_le_one_of_le₀ (hε₁.le.trans <| by norm_num) <| by norm_num)
      (card G • (balance (μ A) ○ᵈ balance (μ A))) (sqrt (card G) • balance (μ A)) (μ univ) ?_ ?_ ?_
    · ext a : 1
      simp [smul_dddconv, dddconv_smul, ← mul_assoc, ← sq, ← Complex.ofReal_pow]
    · simp
    · have global_dichotomy := global_dichotomy hA₀ hγC hγ hAC
      simpa [wLpNorm_nsmul, ← nsmul_eq_mul, div_le_iff₀' (show (0 : ℝ) < card G by positivity),
        ← div_div, rpow_neg, inv_rpow] using global_dichotomy
  have : 0 < p' := pos_iff_ne_zero.2 <| by rintro rfl; simp at unbalancing; linarith
  let q' : ℕ := max (2 * p') (2 ^ 4 * ⌈ε⁻¹ * log (64 / ε)⌉₊)
  have : 0 < q' := by positivity
  have hq'even : Even q' := by grind
  have hp'q' : p' ≤ q' := by unfold q'; grw [← le_max_left]; lia
  have hq'lower : 2 ^ 4 * ε⁻¹ * log (64 / ε) ≤ q' := by
    unfold q'; grw [mul_assoc, ← le_max_right]; push_cast; grw [← Nat.le_ceil]; norm_num
  have hq'upper : q' ≤ 2 ^ 16 * 𝓛 γ / ε ^ 2 := by
    unfold q'
    push_cast
    grw [hp'upper, hpupper, max_le_add_of_nonneg (by positivity) (by positivity),
      (64 / ε).log_le_self (by positivity)]
    ring_nf
    grw [Nat.ceil_le_two_mul <| by grw [← hε₁']; norm_num]
    ring_nf
    bound
  have : 0 < log (6 / ε) := log_pos <| (one_lt_div hε₀).2 (by linarith)
  have : 0 < log (64 / ε) := log_pos <| (one_lt_div hε₀).2 (by linarith)
  obtain ⟨A₁, A₂, hA, hA₁, hA₂⟩ : ∃ (A₁ A₂ : Finset G),
      1 - ε / 32 ≤ ∑ x ∈ s q' (ε / 16) univ univ A, (μ A₁ ○ᵈ μ A₂) x ∧
        (4⁻¹ : ℝ) * A.dens ^ (2 * q') ≤ A₁.dens ∧ (4⁻¹ : ℝ) * A.dens ^ (2 * q') ≤ A₂.dens := by
    refine sifting_cor (by positivity) (by linarith) (by positivity)
      hq'even (by positivity) ?_ hA₀
    calc
      (ε / 16)⁻¹ * log (2 / (ε / 32)) = 2 ^ 4 * ε⁻¹ * log (64 / ε) := by ring_nf
      _ ≤ q' := hq'lower
  have : card G • (f ○ᵈ f) + 1 = card G • (μ A ○ᵈ μ A) := by
    unfold f
    rw [← balance_dddconv, balance, smul_sub, smul_const, Fintype.card_smul_expect]
    simp [sum_dddconv, hA₀]
  have := calc
    1 + ε / 4 = 1 + ε / 2 / 2 := by ring
    _ ≤ ‖card G • (f ○ᵈ f) + 1‖_[p', μ univ] := unbalancing
    _ = card G • ‖(μ_[ℝ] A ○ᵈ μ A)‖_[p', μ univ] := by simp [this, wLpNorm_nsmul, -nsmul_eq_mul]
    _ ≤ card G • ‖(μ_[ℝ] A ○ᵈ μ A)‖_[q', μ univ] := by
      have : Nonempty G := hA₀.to_type
      gcongr
      exact mod_cast sum_mu ℝ≥0 univ_nonempty
  let s' : Finset G := {x | 1 + ε / 8 ≤ card G • (μ A ○ᵈ μ A) x}
  have hss' : s q' (ε / 16) univ univ A ⊆ s' := by
    simp only [subset_iff, mem_s', ENNReal.coe_natCast, mu_univ_dddconv_mu_univ,
      mem_filter, mem_univ, true_and, s']
    rintro x hx
    calc
      1 + ε / 8 ≤ (1 - ε / 16) * (1 + ε / 4) := one_add_le_one_sub_mul_one_add <| calc
          ε / 8 + ε / 16 + ε / 16 * (ε / 4) ≤ ε / 8 + ε / 16 + ε / 16 * (1 / 4) := by gcongr
          _ ≤ ε / 4 := by linarith
      _ ≤ (1 - ε / 16) * card G • ‖μ_[ℝ] A ○ᵈ μ A‖_[q', μ univ] := by gcongr; linarith
      _ = card G • ((1 - ε / 16) * ‖μ_[ℝ] A ○ᵈ μ A‖_[q', μ univ]) := mul_smul_comm ..
      _ ≤ card G • (μ A ○ᵈ μ A) x := by gcongr
  obtain ⟨V, _, hVdim, hV⟩ : ∃ (V : Submodule (ZMod q) G) (_ : DecidablePred (· ∈ V)),
    ↑(finrank (ZMod q) G - finrank (ZMod q) V) ≤
        2 ^ 32 * 𝓛 (4⁻¹ * α ^ (2 * q')) ^ 2 * 𝓛 (ε / 32 * (4⁻¹ * α ^ (2 * q'))) ^ 2 * (ε / 32)⁻¹ ^ 2
          ∧ |∑ x ∈ s', (μ (Set.toFinset V) ∗ᵈ μ A₁ ○ᵈ μ A₂) x -
            ∑ x ∈ s', (μ A₁ ○ᵈ μ A₂) x| ≤ ε / 32 :=
    ap_in_ff' _ hq (by positivity)
    (calc
      4⁻¹ * (A.dens : ℝ) ^ (2 * q') ≤ 4⁻¹ * 1 := by
        gcongr; exact pow_le_one₀ (by positivity) <| mod_cast A.dens_le_one
      _ ≤ 2⁻¹ := by norm_num) (by positivity) (by linarith) hA₁ hA₂
  replace hV :=
    calc
      1 - ε / 16 = 1 - ε / 32 - ε / 32 := by ring
      _ ≤ ∑ x ∈ s q' (ε / 16) univ univ A, (μ A₁ ○ᵈ μ A₂) x -
        |∑ x ∈ s', (μ (Set.toFinset V) ∗ᵈ μ A₁ ○ᵈ μ A₂) x - ∑ x ∈ s', (μ A₁ ○ᵈ μ A₂) x| := by gcongr
      _ ≤ ∑ x ∈ s', (μ A₁ ○ᵈ μ A₂) x -
        -(∑ x ∈ s', (μ (Set.toFinset V) ∗ᵈ μ A₁ ○ᵈ μ A₂) x - ∑ x ∈ s', (μ A₁ ○ᵈ μ A₂) x) := by
        gcongr
        · have : 0 ≤ μ_[ℝ] A₁ ○ᵈ μ A₂ := dddconv_nonneg mu_nonneg mu_nonneg
          exact fun _ _ _ ↦ this _
        · exact neg_le_abs _
      _ = ∑ x ∈ s', (μ (Set.toFinset V) ∗ᵈ μ A₁ ○ᵈ μ A₂) x := by ring
  refine ⟨V, inferInstance, ?_, ?_⟩
  · calc
      ↑(finrank (ZMod q) G - finrank (ZMod q) V)
        ≤ 2 ^ 32 * 𝓛 (4⁻¹ * α ^ (2 * q')) ^ 2 *
          𝓛 (ε / 32 * (4⁻¹ * α ^ (2 * q'))) ^ 2 * (ε / 32)⁻¹ ^ 2 := hVdim
      _ ≤ 2 ^ 32 * (8 * q' * 𝓛 α) ^ 2 *
          (2 ^ 8 * q' * 𝓛 α / ε) ^ 2 * (ε / 32)⁻¹ ^ 2 := by
        have : α ^ (2 * q') ≤ 1 := by bound
        have : 4⁻¹ * α ^ (2 * q') ≤ 1 := by bound
        have : ε / 32 * (4⁻¹ * α ^ (2 * q')) ≤ 1 := by bound
        have : 0 ≤ log (ε / 32 * (4⁻¹ * α ^ (2 * q')))⁻¹ := by bound
        have : 0 ≤ log (4⁻¹ * α ^ (2 * q'))⁻¹ := by bound
        have : 0 ≤ log (α ^ (2 * q'))⁻¹ := by bound
        have := calc
          𝓛 (4⁻¹ * α ^ (2 * q')) ≤ 4⁻¹⁻¹ * 𝓛 (α ^ (2 * q')) :=
            curlog_mul_le (by norm_num) (by norm_num) (by positivity) ‹_›
          _ ≤ 4⁻¹⁻¹ * (↑(2 * q') *  𝓛 α) := by gcongr; exact curlog_pow_le hα₀ (by positivity)
          _ = 8 * q' * 𝓛 α := by push_cast; ring
        gcongr
        calc
          𝓛 (ε / 32 * (4⁻¹ * α ^ (2 * q'))) ≤ (ε / 32)⁻¹ * 𝓛 (4⁻¹ * (α ^ (2 * q'))) :=
            curlog_mul_le (by positivity) (by linarith) (by positivity) ‹_›
          _ ≤ (ε / 32)⁻¹ * (8 * q' * 𝓛 α) := by gcongr
          _ = 2 ^ 8 * q' * 𝓛 α / ε := by ring
      _ = 2 ^ 64 * q' ^ 4 * 𝓛 α ^ 4 / ε ^ 4 := by ring
      _ ≤ 2 ^ 64 * (2 ^ 16 * 𝓛 γ / ε ^ 2) ^ 4 * 𝓛 α ^ 4 / ε ^ 4 := by gcongr
      _ = 2 ^ 128 * 𝓛 α ^ 4 * 𝓛 γ ^ 4 / ε ^ 12 := by ring
  · rw [← le_div_iff₀ (by positivity)]
    have : 0 ≤ μ_[ℝ] (Set.toFinset V) ∗ᵈ μ A₁ ○ᵈ μ A₂ :=
      dddconv_nonneg (ddconv_nonneg mu_nonneg mu_nonneg) mu_nonneg
    calc
      1 + ε / 32 ≤ (1 + ε / 8) * (1 - ε / 16) := one_add_le_one_add_mul_one_sub <|
        calc
          ε / 32 + ε / 16 + ε / 8 * (ε / 16) ≤ ε / 32 + ε / 16 + ε / 8 * (1 / 16) := by gcongr
          _ ≤ ε / 8 := by linarith
      _ ≤ (1 + ε / 8) * ∑ x ∈ s', (μ (Set.toFinset V) ∗ᵈ μ A₁ ○ᵈ μ A₂) x := by gcongr
      _ = ∑ x ∈ s', (1 + ε / 8) * (μ (Set.toFinset V) ∗ᵈ μ A₁ ○ᵈ μ A₂) x := mul_sum ..
      _ ≤ ∑ x ∈ s', card G • (μ A ○ᵈ μ A) x * (μ (Set.toFinset V) ∗ᵈ μ A₁ ○ᵈ μ A₂) x := by
        gcongr with x hx
        · exact this _
        · exact (mem_filter.1 hx).2
      _ ≤ ∑ x, card G • (μ A ○ᵈ μ A) x * (μ (Set.toFinset V) ∗ᵈ μ A₁ ○ᵈ μ A₂) x := by
        gcongr
        · rintro x - -
          have : (0 : ℝ) ≤ _ := this x
          have : 0 ≤ μ_[ℝ] A ○ᵈ μ A := dddconv_nonneg mu_nonneg mu_nonneg
          have : (0 : ℝ) ≤ _ := this x
          positivity
        · exact subset_univ _
      _ = card G • ⟪μ_[ℝ] (Set.toFinset V) ∗ᵈ μ A, μ A ∗ᵈ μ A₂ ○ᵈ μ A₁⟫_[ℝ] := by
        rw [← wInner_one_dddconv_eq_ddconv_wInner_one, dddconv_right_comm,
          ddconv_dddconv_right_comm (μ A), wInner_one_dddconv_eq_ddconv_wInner_one,
          ← dddconv_wInner_one_eq_wInner_one_ddconv, ← conj_wInner_symm]
        simp only [nsmul_eq_mul, mul_assoc, wInner_one_eq_sum, inner_apply, conj_trivial, map_sum,
          smul_sum]
      _ ≤ card G • (‖μ_[ℝ] (Set.toFinset V) ∗ᵈ μ A‖_[∞] * ‖μ_[ℝ] A ∗ᵈ μ A₂ ○ᵈ μ A₁‖_[1]) := by
        gcongr; exact wInner_one_le_dLpNorm_mul_dLpNorm _ _
      _ = _ := by
        have : 0 < (4 : ℝ)⁻¹ * A.dens ^ (2 * q') := by positivity
        replace hA₁ : A₁.Nonempty := by simpa using this.trans_le hA₁
        replace hA₂ : A₂.Nonempty := by simpa using this.trans_le hA₂
        rw [dL1Norm_dddconv, dL1Norm_ddconv]
        · simp [eq_div_iff, hA₀.dens_ne_zero, hA₀, hA₁, hA₂, ← card_smul_mu, smul_ddconv,
            dLpNorm_nsmul, -nsmul_eq_mul]
          simp [← mul_assoc, mul_comm, ddconv_comm]
        · exact mu_nonneg
        · exact mu_nonneg
        · exact ddconv_nonneg mu_nonneg mu_nonneg
        · exact mu_nonneg
```

### child `ThreeAPFree.wInner_one_mu_ddconv_mu_mu_two_smul_mu`: [`APAP/Prereqs/Convolution/ThreeAP.lean` lines 20-41](https://github.com/YaelDillies/apap/blob/fb5cb9c4f594cbeeb160c715618d13640984c521/APAP/Prereqs/Convolution/ThreeAP.lean#L20-L41) ([local copy](code/APAP/Prereqs/Convolution/ThreeAP.lean))

```lean
lemma ThreeAPFree.wInner_one_mu_ddconv_mu_mu_two_smul_mu (hG : Odd (card G))
    (hs : ThreeAPFree (s : Set G)) :
    ⟪μ_[ℝ] s ∗ᵈ μ s, μ (s.image (2 • ·))⟫_[ℝ] = (#s ^ 2 : ℝ)⁻¹ := by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · simp
  simp only [wInner_one_eq_sum, inner_apply', sum_ddconv_mul, ← sum_product', RCLike.conj_to_real]
  rw [← diag_union_offDiag univ, sum_union (disjoint_diag_offDiag _), sum_diag, ←
    sum_add_sum_compl s, @sum_eq_card_nsmul _ _ _ _ _ (#s ^ 3 : ℝ)⁻¹, nsmul_eq_mul,
    Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero, add_zero, pow_succ', mul_inv,
    mul_inv_cancel_left₀]
  · exact Nat.cast_ne_zero.2 hs'.card_pos.ne'
  · refine fun i hi ↦ not_ne_iff.1 fun h ↦ (mem_offDiag.1 hi).2.2 ?_
    simp_rw [mul_ne_zero_iff, ← mem_support, support_mu, mem_coe, mem_image, two_smul] at h
    obtain ⟨b, hb, hab⟩ := h.2
    obtain rfl := hs h.1.1 hb h.1.2 hab.symm
    simpa using hab
  · simpa using fun _ ↦ Or.inl
  · rintro a ha
    simp only [mu_apply, ha, ite_true, mul_one, mem_image, mul_ite, mul_zero]
    rw [ite_eq_left ⟨_, ha, two_smul _ _⟩, card_image_of_injective, pow_three', mul_inv, mul_inv]
    rw [← Nat.card_eq_fintype_card] at hG
    exact hG.coprime_two_right.nsmul_right_bijective.injective
```

How the parts fit. The glue (`ff`, 511-645) first handles an *easy case*
(lines 525-538): if `q^(n/2) ≤ 2 * α⁻¹ ^ 2`, a short `calc` of logarithms closes
the goal, no induction needed. Otherwise it runs a density-increment induction.

The induction is the `have ind (i : ℕ) : ∃ V B, …` block (lines 539-594). Its
invariant packages four facts about the pair `(V, B)`:

  `n ≤ finrank V + 2^140 * i * 𝓛 α^8`  (the codimension has grown by at most `i` increments),
  `ThreeAPFree B`, `α ≤ B.dens`, and
  `B.dens < (65/64)^i * α → 2⁻¹ ≤ card V * ⟪μ B ∗ᵈ μ B, μ (B.image (2 • ·))⟫`.

The zero case (546-549) takes `V = G, B = A`. In the successor case (550-594),
either the inner product is already `≥ 2⁻¹` (then pass through, 553-554), or it
is `< 2⁻¹` and the proof applies the child `di_in_ff` (line 561) to get `V'`
and a density increment; it sets `B' = (-x +ᵥ B).preimage (↑)`, then proves the
invariant survives: the density rises by `1 + 64⁻¹` via the bookkeeping identity
[`Finset.dens_addSubgroup_preimage_vadd_eq_indicator_one_ddconv_mu`](https://github.com/YaelDillies/apap/blob/fb5cb9c4f594cbeeb160c715618d13640984c521/APAP/Prereqs/Convolution/Discrete/Basic.lean#L213-L222)
(line 572), while codimension and 3AP-freeness follow by `calc`.

Running `ind` at `i = ⌊𝓛 α / log (65 / 64)⌋₊` (line 595) gives the terminal pair
`(V, B)`. Because `B.dens ≤ 1`, the density-growth hypothesis fails at that index
(lines 598-614), so the inner product is `≥ 2⁻¹`, and the child
`ThreeAPFree.wInner_one_mu_ddconv_mu_mu_two_smul_mu` (line 615) rewrites it to
`card V * (#B^2)⁻¹`, giving `card V ≤ 2 * (B.dens)⁻²`. Feeding that into the
codimension bound closes the theorem (calc, 621-645).

Lemma graph (direct uses):

```
ff
├─ di_in_ff                                         (successor step of the induction, line 561)
└─ ThreeAPFree.wInner_one_mu_ddconv_mu_mu_two_smul_mu  (limit case, line 615)
```

and one level down, the child `di_in_ff` is itself assembled from (the depth
of this entry):

```
di_in_ff ── ap_in_ff' (line 424) ── ap_in_ff (line 327)
```

Why each child is a good leaf. `di_in_ff` is self-contained: from a set `A` with
a large inner product it returns a subspace `V` of bounded codimension where the
density of `A` rises by `1 + ε/32`; its proof closes on its own from named
siblings (`global_dichotomy`, `unbalancing`, `sifting_cor`, `ap_in_ff'`), so the
induction needs only its two conclusions, not how it works.
`ThreeAPFree.wInner_one_mu_ddconv_mu_mu_two_smul_mu` is also self-contained: the
3AP-free condition makes `⟪μ s ∗ᵈ μ s, μ (s.image (2 • ·))⟫` exactly
`(#s^2)⁻¹`, and its proof closes on its own by a diagonal/off-diagonal split, so
the limit case reduces to arithmetic on `card V` and `B.dens`.

## Why it is good

1. The parent `ff` is 135 lines long — a skeleton whose two structural moves are
   the induction and the final inner-product rewrite (`check`, form
   `lines(parent, 135)`, lines 511-645).
2. The glue applies `di_in_ff` inside the successor step of the induction to
   raise the density by a fixed factor (`check`, form `cites(parent, di_in_ff)`,
   line 561).
3. The glue applies `wInner_one_mu_ddconv_mu_mu_two_smul_mu` to close the limit
   case (`check`, form `cites(parent, ThreeAPFree.wInner_one_mu_ddconv_mu_mu_two_smul_mu)`,
   line 615).
4. The authors' blueprint for the node `ff` states exactly these two ingredients:
   `\uses{no3aps_inner_prod, di_in_ff}`, where `no3aps_inner_prod` is the
   blueprint label of `ThreeAPFree.wInner_one_mu_ddconv_mu_mu_two_smul_mu`
   (`author-statement`, [blueprint/src/chapter/ff.tex#L200-L202](https://github.com/YaelDillies/apap/blob/fb5cb9c4f594cbeeb160c715618d13640984c521/blueprint/src/chapter/ff.tex#L200-L202)).
5. The decomposition is 3 deep below `ff`: `di_in_ff` (332-509) applies
   `ap_in_ff'` (line 424), which applies `ap_in_ff` (line 327), all in the
   copied file (`measurement`; the chain is read in `code/APAP/FiniteField.lean`).

In my opinion the detail worth copying is the *packaged invariant*: the induction
is not stated over `V` and `B` directly but over the conjunction of four facts,
so the successor step has to prove exactly one new thing (the density increment)
and the terminal step has to prove exactly one thing (the inner product is large).

## When to use it, and when not

Use it when a density bound has a *density-increment* step available: from a set
with a large inner product, a lemma (`di_in_ff` here) descends to a subspace
where the density rises by a fixed factor at a bounded codimension cost, and a
terminal identity rewrites the surviving inner product in terms of the original
density, with the loop stopping because density is bounded above by 1. This is
the standard Roth/density-increment argument, so it fits whenever that structure
is present.

Avoid it when the increment's density gain or codimension cost does not telescope
into the final bound, when the terminal identity needs hypotheses beyond the
induction invariant, or when the invariant is too weak to survive a step. State
the invariant explicitly (the `have ind` here packages both codimension and
density); an induction stated only over the pair `(V, B)` would close without
yielding the bound.

## Consequences

The move creates a natural-number induction with an explicit invariant (the
`have ind` block). The obligations are: the invariant must survive the
density-increment step, and it must convert into the final bound at the terminal
index. The increment step relies on `di_in_ff`'s hypothesis
`ε ≤ |card G * ⟪μ A ∗ᵈ μ A, μ C⟫ - 1|`; the proof manufactures it in the
non-terminal branch by rewriting `¬(2⁻¹ ≤ x)` into `2⁻¹ ≤ |x - 1|`. A weaker
invariant (one omitting the density-growth clause) would let the induction close
without yielding the codimension bound. There is a non-inductive easy case before
the loop (`q^(n/2) ≤ 2 * α⁻¹ ^ 2`), so a decomposition that skips it would fail
to cover all inputs.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push.yml build job (leanprover/lean-action, builds whole APAP project incl. APAP/FiniteField.lean) on default branch master; pinned commit fb5cb9c4f594cbeeb160c715618d13640984c521 is on master | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: di_in_ff@APAP/FiniteField.lean:561, ThreeAPFree.wInner_one_mu_ddconv_mu_mu_two_smul_mu@APAP/FiniteField.lean:615; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at fb5cb9c4f594cbeeb160c715618d13640984c521 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(parent, 135) -> lines: site parent has 135 lines | check_claims.py |
| 2 | verified | cites(parent, di_in_ff) -> cites: di_in_ff occurs at APAP/FiniteField.lean:561 | check_claims.py |
| 3 | verified | cites(parent, ThreeAPFree.wInner_one_mu_ddconv_mu_mu_two_smul_mu) -> cites: ThreeAPFree.wInner_one_mu_ddconv_mu_mu_two_smul_mu occurs at APAP/FiniteField.lean:615 | check_claims.py |
| 4 | verified | blueprint/src/chapter/ff.tex L201 = '\uses{no3aps_inner_prod, di_in_ff}' (within L200-L202); L177 '\label{no3aps_inner_prod}', L178 '\lean{ThreeAPFree.wInner_one_mu_ddconv_mu_mu_two_smul_mu}' (within L176-L178) | verifier |
| 5 | verified | read code/APAP/FiniteField.lean: ap_in_ff' at 322-327 cites ap_in_ff at 327; di_in_ff (332-509) applies ap_in_ff' at 424; ff (511-645) cites di_in_ff at 561 and wInner_one_mu_ddconv_mu_mu_two_smul_mu at 615 | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent ff is APAP/FiniteField.lean 511-645 (135 lines, last line of file, confirmed by sed/wc); child di_in_ff is 332-509 (178 lines); child ThreeAPFree.wInner_one_mu_ddconv_mu_mu_two_smul_mu is ThreeAP.lean 20-41 (22 lines), the set_option line being line 19 just outside. All three declarations and statements match entry.json verbatim modulo the 'public' visibility attribute. The glue cites exactly the two children: di_in_ff at line 561 (obtain ... := di_in_ff hq ...) and ThreeAPFree.wInner_one_mu_ddconv_mu_mu_two_smul_mu at line 615 (rw [hB.wInner_one_mu_ddconv_mu_mu_two_smul_mu] at hBV), matching the blueprint \uses{no3aps_inner_prod, di_in_ff}. Depth chain verified: ff -> di_in_ff cites ap_in_ff' at 424, ap_in_ff' (322-327) cites ap_in_ff at 327, giving depth 3. No sorry/admit/axiom in any of the three site ranges, so it closes. Shape numbers all correct: parent_lines 135, direct_lemmas 2, depth 3, child_lines [178,22]. | reviewer-correctness |
| generality | accept | Move is scoped beyond the example: 'When to use it' names the three structural preconditions (a density-increment lemma, a terminal identity rewriting the surviving inner product, loop termination from density <= 1) and situates the pattern as the standard Roth/density-increment argument, so it applies whenever that structure is present rather than only to this bound. 'When not to use' and consequences are honest and specific: they name concrete failure modes (increment gain/codimension cost not telescoping into the final bound, terminal identity needing hypotheses beyond the invariant, invariant too weak to survive a step) and the README/consequences tie each to actual code (the manufactured epsilon-hypothesis from not(2^-1 <= x) at lines 72-75, the non-inductive easy case at 525-538, the packaged four-fact invariant). The entry does say what makes the leaves good for a bounded prover: 'Why each child is a good leaf' states di_in_ff and the ThreeAPFree identity each close on their own from named siblings, so the induction needs only their conclusions, not how they work - exactly the one-hole-per-bounded-prover property. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are consistent and traceable. Commit fb5cb9c4f594cbeeb160c715618d13640984c521 is used uniformly across entry.json, README.md, sources/apap/SOURCE.md and source.json; check_provenance.py passes (2 files byte-identical at the pinned commit). Licence Apache-2.0 is recorded consistently in all four, and sources/apap/upstream-LICENSE is the Apache-2.0 text. Site permalink line anchors match the local copies: parent ff at FiniteField.lean 511-645 (135 lines), child di_in_ff at 332-509, child ThreeAPFree.wInner_one_mu_ddconv_mu_mu_two_smul_mu at ThreeAP.lean 20-41; code/ holds exactly the two files listed in entry.json. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/YaelDillies/apap at commit `fb5cb9c4f594cbeeb160c715618d13640984c521`, under `Apache-2.0`; see the [source note](../../sources/apap/SOURCE.md) for the licence text and attribution.
