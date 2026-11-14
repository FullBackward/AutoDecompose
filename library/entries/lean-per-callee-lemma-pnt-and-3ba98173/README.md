# Per-row lemma dispatch for FKS2 Corollary 24's eleven Table-7 rows

| | |
|---|---|
| Kind | instance |
| Move | per-callee-lemma |
| Language | lean |
| Status | draft |
| Source | [pnt-and](../../sources/pnt-and/SOURCE.md) at `2c476fa6441c` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T11:04:35Z |

## Intent

FKS2's Corollary 24 asserts `Eπ x ≤ B x` for every row `(B, I)` of Table 7, an eleven-row table of explicit coefficient functions. The authors give one named lemma per row — `corollary_24_row1 … row11`, each proved in its own file — and assemble the full statement `corollary_24_all` with an eleven-way `rcases` over `(B, I) ∈ table7` that hands each row to its lemma, so the assembly is 18 lines and the real work lives in the per-row files.

## The decomposition

### parent `corollary_24_all`: [`PrimeNumberTheoremAnd/IEANTN/FKS2Cor24All.lean` lines 31-48](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24All.lean#L31-L48) ([local copy](code/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24All.lean))

```lean
theorem corollary_24_all (B : ℝ → ℝ) (I : Set ℝ) (h : (B, I) ∈ table7) :
    ∀ x, Real.log x ∈ I → Eπ x ≤ B x := by
  intro x hx
  simp only [table7, List.mem_cons, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
  · exact corollary_24_row1 x hx
  · exact corollary_24_row2 x hx
  · exact corollary_24_row3 x hx
  · exact corollary_24_row4 x hx
  · exact corollary_24_row5 x hx
  · exact corollary_24_row6 x hx
  · exact corollary_24_row7 x hx
  · exact corollary_24_row8 x hx
  · exact corollary_24_row9 x hx
  · exact corollary_24_row10 x hx
  · exact corollary_24_row11 x hx
  · exact absurd h (by simp)
```

### child `corollary_24_row1`: [`PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row1.lean` lines 91-119](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row1.lean#L91-L119) ([local copy](code/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row1.lean))

```lean
theorem corollary_24_row1 :
    ∀ x, Real.log x ∈ Set.Icc (1:ℝ) 57 → Eπ x ≤ 2 * Real.log x * x ^ (-(1:ℝ) / 2) := by
  intro x hlog
  obtain ⟨hlo, hhi⟩ := hlog
  rcases lt_trichotomy x 0 with hxneg | hx0 | hxpos
  · -- x < 0: `x^{-1/2} = exp(...)·cos(-π/2) = 0`, so RHS = 0; and `Eπ x ≤ 0`
    have hLpos : (0:ℝ) < Real.log x := by linarith
    have hEle0 : Eπ x ≤ 0 := by
      unfold Eπ
      apply div_nonpos_of_nonneg_of_nonpos (abs_nonneg _)
      exact le_of_lt (div_neg_of_neg_of_pos hxneg hLpos)
    have hxhalf0 : x ^ (-(1:ℝ) / 2) = 0 := by
      rw [Real.rpow_def_of_neg hxneg,
        show (-(1:ℝ) / 2) * π = -(π / 2) by ring, Real.cos_neg, Real.cos_pi_div_two, mul_zero]
    rw [hxhalf0, mul_zero]
    exact hEle0
  · -- x = 0: `log 0 = 0` contradicts `1 ≤ log x`
    exfalso; rw [hx0, Real.log_zero] at hlo; linarith
  · -- x > 0: dispatch to the three segments split at `log x = 4, 43`
    have cvt : ∀ a b : ℝ, a ≤ Real.log x → Real.log x ≤ b →
        x ∈ Set.Icc (Real.exp a) (Real.exp b) := by
      intro a b ha hb
      exact ⟨by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr ha,
             by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr hb⟩
    rcases le_total (Real.log x) 4 with h1 | h1
    · exact floor_checked_row1 x (cvt 1 4 hlo h1)
    · rcases le_total (Real.log x) 43 with h2 | h2
      · exact floor_row1 x (cvt 4 43 h1 h2)
      · exact band_row1 x (cvt 43 57 h2 hhi)
```

### child `corollary_24_row2`: [`PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row2.lean` lines 97-126](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row2.lean#L97-L126) ([local copy](code/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row2.lean))

```lean
theorem corollary_24_row2 :
    ∀ x, Real.log x ∈ Set.Icc (1:ℝ) 65.65 →
      Eπ x ≤ (Real.log x) ^ (3/2 : ℝ) * x ^ (-(1:ℝ) / 2) := by
  intro x hlog
  obtain ⟨hlo, hhi⟩ := hlog
  rcases lt_trichotomy x 0 with hxneg | hx0 | hxpos
  · -- x < 0: `x^{-1/2} = exp(...)·cos(-π/2) = 0`, so RHS = 0; and `Eπ x ≤ 0`
    have hLpos : (0:ℝ) < Real.log x := by linarith
    have hEle0 : Eπ x ≤ 0 := by
      unfold Eπ
      apply div_nonpos_of_nonneg_of_nonpos (abs_nonneg _)
      exact le_of_lt (div_neg_of_neg_of_pos hxneg hLpos)
    have hxhalf0 : x ^ (-(1:ℝ) / 2) = 0 := by
      rw [Real.rpow_def_of_neg hxneg,
        show (-(1:ℝ) / 2) * π = -(π / 2) by ring, Real.cos_neg, Real.cos_pi_div_two, mul_zero]
    rw [hxhalf0, mul_zero]
    exact hEle0
  · -- x = 0: `log 0 = 0` contradicts `1 ≤ log x`
    exfalso; rw [hx0, Real.log_zero] at hlo; linarith
  · -- x > 0: dispatch to the three segments split at `log x = 8, 43`
    have cvt : ∀ a b : ℝ, a ≤ Real.log x → Real.log x ≤ b →
        x ∈ Set.Icc (Real.exp a) (Real.exp b) := by
      intro a b ha hb
      exact ⟨by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr ha,
             by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr hb⟩
    rcases le_total (Real.log x) 8 with h1 | h1
    · exact floor_trusted_row2 x (cvt 1 8 hlo h1)
    · rcases le_total (Real.log x) 43 with h2 | h2
      · exact floor_row2 x (cvt 8 43 h1 h2)
      · exact band_row2 x (cvt 43 65.65 h2 hhi)
```

### child `corollary_24_row3`: [`PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row3.lean` lines 112-141](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row3.lean#L112-L141) ([local copy](code/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row3.lean))

```lean
theorem corollary_24_row3 :
    ∀ x, Real.log x ∈ Set.Icc (8:ℝ) 60.8 →
      Eπ x ≤ (1 / (8 * π)) * (Real.log x) ^ 2 * x ^ (-(1:ℝ) / 2) := by
  intro x hlog
  obtain ⟨hlo, hhi⟩ := hlog
  rcases lt_trichotomy x 0 with hxneg | hx0 | hxpos
  · -- x < 0: `x^{-1/2} = exp(...)·cos(-π/2) = 0`, so RHS = 0; and `Eπ x ≤ 0`
    have hLpos : (0:ℝ) < Real.log x := by linarith
    have hEle0 : Eπ x ≤ 0 := by
      unfold Eπ
      apply div_nonpos_of_nonneg_of_nonpos (abs_nonneg _)
      exact le_of_lt (div_neg_of_neg_of_pos hxneg hLpos)
    have hxhalf0 : x ^ (-(1:ℝ) / 2) = 0 := by
      rw [Real.rpow_def_of_neg hxneg,
        show (-(1:ℝ) / 2) * π = -(π / 2) by ring, Real.cos_neg, Real.cos_pi_div_two, mul_zero]
    rw [hxhalf0, mul_zero]
    exact hEle0
  · -- x = 0: `log 0 = 0` contradicts `8 ≤ log x`
    exfalso; rw [hx0, Real.log_zero] at hlo; linarith
  · -- x > 0: dispatch to the three segments split at `log x = 9, 43`
    have cvt : ∀ a b : ℝ, a ≤ Real.log x → Real.log x ≤ b →
        x ∈ Set.Icc (Real.exp a) (Real.exp b) := by
      intro a b ha hb
      exact ⟨by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr ha,
             by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr hb⟩
    rcases le_total (Real.log x) 9 with h1 | h1
    · exact floor_trusted_row3 x (cvt 8 9 hlo h1)
    · rcases le_total (Real.log x) 43 with h2 | h2
      · exact floor_row3 x (cvt 9 43 h1 h2)
      · exact band_row3 x (cvt 43 60.8 h2 hhi)
```

### child `corollary_24_row4`: [`PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row4.lean` lines 239-267](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row4.lean#L239-L267) ([local copy](code/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row4.lean))

```lean
theorem corollary_24_row4 :
    ∀ x, Real.log x ∈ Set.Icc (1:ℝ) 70.6 → Eπ x ≤ (Real.log x) ^ 2 * x ^ (-(1:ℝ) / 2) := by
  intro x hlog
  obtain ⟨hlo, hhi⟩ := hlog
  rcases lt_trichotomy x 0 with hxneg | hx0 | hxpos
  · -- x < 0: `x^{-1/2} = exp(...)·cos(-π/2) = 0`, so RHS = 0; and `Eπ x ≤ 0`
    have hLpos : (0:ℝ) < Real.log x := by linarith
    have hEle0 : Eπ x ≤ 0 := by
      unfold Eπ
      apply div_nonpos_of_nonneg_of_nonpos (abs_nonneg _)
      exact le_of_lt (div_neg_of_neg_of_pos hxneg hLpos)
    have hxhalf0 : x ^ (-(1:ℝ) / 2) = 0 := by
      rw [Real.rpow_def_of_neg hxneg,
        show (-(1:ℝ) / 2) * π = -(π / 2) by ring, Real.cos_neg, Real.cos_pi_div_two, mul_zero]
    rw [hxhalf0, mul_zero]
    exact hEle0
  · -- x = 0: `log 0 = 0` contradicts `1 ≤ log x`
    exfalso; rw [hx0, Real.log_zero] at hlo; linarith
  · -- x > 0: dispatch to the three segments split at `log x = 3, 43`
    have cvt : ∀ a b : ℝ, a ≤ Real.log x → Real.log x ≤ b →
        x ∈ Set.Icc (Real.exp a) (Real.exp b) := by
      intro a b ha hb
      exact ⟨by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr ha,
             by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr hb⟩
    rcases le_total (Real.log x) 3 with h1 | h1
    · exact floor_trusted_row4 x (cvt 1 3 hlo h1)
    · rcases le_total (Real.log x) 43 with h2 | h2
      · exact floor_row4 x (cvt 3 43 h1 h2)
      · exact band_row4 x (cvt 43 70.6 h2 hhi)
```

### child `corollary_24_row5`: [`PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row5.lean` lines 91-119](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row5.lean#L91-L119) ([local copy](code/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row5.lean))

```lean
theorem corollary_24_row5 :
    ∀ x, Real.log x ∈ Set.Icc (1:ℝ) 80 → Eπ x ≤ (Real.log x) ^ 3 * x ^ (-(1:ℝ) / 2) := by
  intro x hlog
  obtain ⟨hlo, hhi⟩ := hlog
  rcases lt_trichotomy x 0 with hxneg | hx0 | hxpos
  · -- x < 0: `x^{-1/2} = exp(...)·cos(-π/2) = 0`, so RHS = 0; and `Eπ x ≤ 0`
    have hLpos : (0:ℝ) < Real.log x := by linarith
    have hEle0 : Eπ x ≤ 0 := by
      unfold Eπ
      apply div_nonpos_of_nonneg_of_nonpos (abs_nonneg _)
      exact le_of_lt (div_neg_of_neg_of_pos hxneg hLpos)
    have hxhalf0 : x ^ (-(1:ℝ) / 2) = 0 := by
      rw [Real.rpow_def_of_neg hxneg,
        show (-(1:ℝ) / 2) * π = -(π / 2) by ring, Real.cos_neg, Real.cos_pi_div_two, mul_zero]
    rw [hxhalf0, mul_zero]
    exact hEle0
  · -- x = 0: `log 0 = 0` contradicts `1 ≤ log x`
    exfalso; rw [hx0, Real.log_zero] at hlo; linarith
  · -- x > 0: dispatch to the three segments split at `log x = 3, 43`
    have cvt : ∀ a b : ℝ, a ≤ Real.log x → Real.log x ≤ b →
        x ∈ Set.Icc (Real.exp a) (Real.exp b) := by
      intro a b ha hb
      exact ⟨by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr ha,
             by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr hb⟩
    rcases le_total (Real.log x) 3 with h1 | h1
    · exact floor_trusted_row5 x (cvt 1 3 hlo h1)
    · rcases le_total (Real.log x) 43 with h2 | h2
      · exact floor_xhalf_row5 x (cvt 3 43 h1 h2)
      · exact band_row5 x (cvt 43 80 h2 hhi)
```

### child `corollary_24_row6`: [`PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row6.lean` lines 121-152](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row6.lean#L121-L152) ([local copy](code/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row6.lean))

```lean
theorem corollary_24_row6 :
    ∀ x, Real.log x ∈ Set.Icc (1:ℝ) 80.55 → Eπ x ≤ x ^ (-(1:ℝ)/3) := by
  intro x hlog
  obtain ⟨hlo, hhi⟩ := hlog
  rcases lt_trichotomy x 0 with hxneg | hx0 | hxpos
  · -- x < 0: `Eπ x ≤ 0 < x^{-1/3}`
    have hLpos : (0:ℝ) < Real.log x := by linarith
    have hEle0 : Eπ x ≤ 0 := by
      unfold Eπ
      apply div_nonpos_of_nonneg_of_nonpos (abs_nonneg _)
      exact le_of_lt (div_neg_of_neg_of_pos hxneg hLpos)
    have hRpos : (0:ℝ) < x ^ (-(1:ℝ)/3) := by
      rw [Real.rpow_def_of_neg hxneg]
      apply mul_pos (Real.exp_pos _)
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [Real.pi_pos, Real.pi_le_four]
    linarith
  · -- x = 0: `log 0 = 0` contradicts `1 ≤ log x`
    exfalso; rw [hx0, Real.log_zero] at hlo; linarith
  · -- x > 0: dispatch to the four segments
    have cvt : ∀ a b : ℝ, a ≤ Real.log x → Real.log x ≤ b →
        x ∈ Set.Icc (Real.exp a) (Real.exp b) := by
      intro a b ha hb
      exact ⟨by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr ha,
             by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr hb⟩
    rcases le_total (Real.log x) 8 with h1 | h1
    · exact floor_trusted_row6 x (cvt 1 8 hlo h1)
    · rcases le_total (Real.log x) 10 with h2 | h2
      · exact floor_row6 x (cvt 8 10 h1 h2)
      · rcases le_total (Real.log x) 80 with h3 | h3
        · exact mid_row6 x (cvt 10 80 h2 h3)
        · exact sliver_row6 x (cvt 80 80.55 h3 hhi)
```

### child `corollary_24_row10`: [`PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row10.lean` lines 122-153](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row10.lean#L122-L153) ([local copy](code/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row10.lean))

```lean
theorem corollary_24_row10 :
    ∀ x, Real.log x ∈ Set.Icc (1:ℝ) 1358.6 → Eπ x ≤ x ^ (-(1:ℝ)/50) := by
  intro x hlog
  obtain ⟨hlo, hhi⟩ := hlog
  rcases lt_trichotomy x 0 with hxneg | hx0 | hxpos
  · -- x < 0: `Eπ x ≤ 0 < x^{-1/50}`
    have hLpos : (0:ℝ) < Real.log x := by linarith
    have hEle0 : Eπ x ≤ 0 := by
      unfold Eπ
      apply div_nonpos_of_nonneg_of_nonpos (abs_nonneg _)
      exact le_of_lt (div_neg_of_neg_of_pos hxneg hLpos)
    have hRpos : (0:ℝ) < x ^ (-(1:ℝ)/50) := by
      rw [Real.rpow_def_of_neg hxneg]
      apply mul_pos (Real.exp_pos _)
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [Real.pi_pos, Real.pi_le_four]
    linarith
  · -- x = 0: `log 0 = 0` contradicts `1 ≤ log x`
    exfalso; rw [hx0, Real.log_zero] at hlo; linarith
  · -- x > 0: dispatch to the four segments
    have cvt : ∀ a b : ℝ, a ≤ Real.log x → Real.log x ≤ b →
        x ∈ Set.Icc (Real.exp a) (Real.exp b) := by
      intro a b ha hb
      exact ⟨by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr ha,
             by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr hb⟩
    rcases le_total (Real.log x) 3.5 with h1 | h1
    · exact floor_checked_row10 x (cvt 1 3.5 hlo h1)
    · rcases le_total (Real.log x) 10 with h2 | h2
      · exact floor_row10 x (cvt 3.5 10 h1 h2)
      · rcases le_total (Real.log x) 1358 with h3 | h3
        · exact mid_row10 x (cvt 10 1358 h2 h3)
        · exact sliver_row10 x (cvt 1358 1358.6 h3 hhi)
```

### child `corollary_24_row11`: [`PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row11.lean` lines 441-472](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row11.lean#L441-L472) ([local copy](code/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row11.lean))

```lean
theorem corollary_24_row11 :
    ∀ x, Real.log x ∈ Set.Icc (1:ℝ) 3757.6 → Eπ x ≤ x ^ (-(1:ℝ)/100) := by
  intro x hlog
  obtain ⟨hlo, hhi⟩ := hlog
  rcases lt_trichotomy x 0 with hxneg | hx0 | hxpos
  · -- x < 0: `Eπ x ≤ 0 < x^{-1/100}`
    have hLpos : (0:ℝ) < Real.log x := by linarith
    have hEle0 : Eπ x ≤ 0 := by
      unfold Eπ
      apply div_nonpos_of_nonneg_of_nonpos (abs_nonneg _)
      exact le_of_lt (div_neg_of_neg_of_pos hxneg hLpos)
    have hRpos : (0:ℝ) < x ^ (-(1:ℝ)/100) := by
      rw [Real.rpow_def_of_neg hxneg]
      apply mul_pos (Real.exp_pos _)
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [Real.pi_pos, Real.pi_le_four]
    linarith
  · -- x = 0: `log 0 = 0` contradicts `1 ≤ log x`
    exfalso; rw [hx0, Real.log_zero] at hlo; linarith
  · -- x > 0: dispatch to the four segments
    have cvt : ∀ a b : ℝ, a ≤ Real.log x → Real.log x ≤ b →
        x ∈ Set.Icc (Real.exp a) (Real.exp b) := by
      intro a b ha hb
      exact ⟨by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr ha,
             by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr hb⟩
    rcases le_total (Real.log x) 3.5 with h1 | h1
    · exact floor_checked_row11 x (cvt 1 3.5 hlo h1)
    · rcases le_total (Real.log x) 10 with h2 | h2
      · exact floor_row11 x (cvt 3.5 10 h1 h2)
      · rcases le_total (Real.log x) 3756 with h3 | h3
        · exact mid_row11 x (cvt 10 3756 h2 h3)
        · exact sliver_row11 x (cvt 3756 3757.6 h3 hhi)
```

`corollary_24_all` is pure dispatch: it unfolds `(B, I) ∈ table7` with `simp only [table7, List.mem_cons, Prod.mk.injEq]`, then splits the resulting disjunction with an eleven-way `rcases`. Each of the eleven named branches is `exact corollary_24_rowN x hx`; the final `| h` branch closes by `absurd h (by simp)`, because a list-membership disjunction of eleven explicit pairs is exhaustive. The glue is one citation per row and no arithmetic.

```text
corollary_24_all ── rcases (B,I) ∈ table7 ──┬─ row1  (x^{-1/2}·2·log x,      log x ∈ [1,57])
                                             ├─ row2  (x^{-1/2}·(log x)^{3/2}, [1,65.65])
                                             ├─ row3  (x^{-1/2}·(log x)²/(8π), [8,60.8])
                                             ├─ row4  (x^{-1/2}·(log x)²,      [1,70.6])
                                             ├─ row5  (x^{-1/2}·(log x)³,      [1,80])
                                             ├─ row6  (x^{-1/3},  [1,80.55])
                                             ├─ row7  (x^{-1/4},  [1,107.6])
                                             ├─ row8  (x^{-1/5},  [1,134.8])
                                             ├─ row9  (x^{-1/10}, [1,270.8])
                                             ├─ row10 (x^{-1/50}, [1,1358.6])
                                             └─ row11 (x^{-1/100},[1,3757.6])
```

Three of these row lemmas are copied into [`code/`](code/) but shown above only by name, because they are clones of `corollary_24_row6` instantiated at a different `n`. Their declarations, with permalinks:

- `corollary_24_row7` — `n = 4`, `log x ∈ [1, 107.6]`: [FKS2Cor24Row7.lean#L121-L152](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row7.lean#L121-L152)
- `corollary_24_row8` — `n = 5`, `log x ∈ [1, 134.8]`: [FKS2Cor24Row8.lean#L121-L152](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row8.lean#L121-L152)
- `corollary_24_row9` — `n = 10`, `log x ∈ [1, 270.8]`: [FKS2Cor24Row9.lean#L121-L152](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24Row9.lean#L121-L152)

Why each row is a good leaf: every `corollary_24_rowN` is a named, self-contained statement whose own proof is again a dispatch — `rcases lt_trichotomy x 0` closes the non-positive `x` cases by sign reasoning, and the `x > 0` case hands the interval to two or three per-segment lemmas (`floor_*`, `mid_*`, `sliver_*`) declared earlier in the same file. So the parent stays trivial while the segment-level content is local to each row's file; nothing is shared across rows except the `Table4Ext` machinery each file imports.

## Why it is good

1. **check** — `corollary_24_all` is declared in `FKS2Cor24All.lean` at lines 31–48 ([permalink](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24All.lean#L31-L48)).
2. **check** — `FKS2Cor24All.lean` contains no `sorry`, `admit`, or `axiom` token in lines 1–50 ([permalink](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24All.lean#L1-L50)).
3. **measurement** — the glue is 18 lines dispatching 11 direct per-row lemmas; the longest chain below the parent is depth 5 (`corollary_24_all → corollary_24_row4 → floor_row4 → floor_xhalf_of_check → Epi_le_evalLhsE_wide → Buthe.theorem_2e`); the eight shown children have 29, 30, 30, 29, 29, 32, 32, 32 lines.
4. **author-statement** — the file's doc comment says the dispatch '… each proved in its own file `FKS2Cor24Row{1..11}.lean`' and that it 'Mirrors `FKS2Cor23All.lean`'s Table-6 dispatch' ([permalink](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/IEANTN/FKS2Cor24All.lean#L13-L24)).
5. **known-use** — the same per-row dispatch is used for Corollary 23 in `FKS2Cor23All.lean` ([permalink](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/IEANTN/FKS2Cor23All.lean#L27-L50)).

## When to use it, and when not

Use it when a theorem's only substantive hypothesis is a finite, explicit case table and each case is substantial enough to deserve its own declaration and file — especially when a template file can carry the shared machinery that the per-case files instantiate (here `FKS2Cor24Row11` carries the generic `x^{-1/n}` helpers that rows 6–11 clone). Do not use it when the cases differ only in a scalar or a numeric bound — one parameterised lemma beats a family of clones — or when the case set is open-ended rather than a finite list membership, since there is then no exhaustive case split to dispatch.

## Consequences

It creates one named child per row, so the glue becomes a mechanical case split whose exhaustiveness and injectivity (`Prod.mk.injEq`) are discharged by `simp` and the `rcases`; the final branch closes by `absurd h (by simp)` because the disjunction is exhaustive. Each per-row file must be genuinely self-contained, and any argument shared by two rows is duplicated unless lifted into the shared template (rows 1–5 lift the `x^{-1/2}` floor machinery, rows 6–11 the `x^{-1/n}` machinery, into `Table4Ext`). Trust boundary: the row lemmas close without `sorry`, but their floor-trusted, band and sliver segments delegate to `FKS2.Cor24Trusted.*` (rows 1/10/11's floor-checked to `FKS2.Cor24Checked.*`), the project's authorised trusted Theorem-6 interpolation results.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: corollary_24_row1@PrimeNumberTheoremAnd/IEANTN/FKS2Cor24All.lean:37, corollary_24_row2@PrimeNumberTheoremAnd/IEANTN/FKS2Cor24All.lean:38, corollary_24_row3@PrimeNumberTheoremAnd/IEANTN/FKS2Cor24All.lean:39, corollary_24_row4@PrimeNumberTheoremAnd/IEANTN/FKS2Cor24All.lean:40, corollary_24_row5@PrimeNumberTheoremAnd/IEANTN/FKS2Cor24All.lean:41, corollary_24_row6@PrimeNumberTheoremAnd/IEANTN/FKS2Cor24All.lean:42, corollary_24_row10@PrimeNumberTheoremAnd/IEANTN/FKS2Cor24All.lean:46, corollary_24_row11@PrimeNumberTheoremAnd/IEANTN/FKS2Cor24All.lean:47; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(corollary_24_all, PrimeNumberTheoremAnd/IEANTN/FKS2Cor24All.lean, 31-48) -> declared: corollary_24_all is declared at PrimeNumberTheoremAnd/IEANTN/FKS2Cor24All.lean:31 | check_claims.py |
| 2 | verified | no_sorry(PrimeNumberTheoremAnd/IEANTN/FKS2Cor24All.lean, 1-50) -> no_sorry: none of sorry, admit, axiom in PrimeNumberTheoremAnd/IEANTN/FKS2Cor24All.lean:1-50 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd at commit `2c476fa6441c607096d93c8fc7ac0a227a655dae`, under `Apache-2.0`; see the [source note](../../sources/pnt-and/SOURCE.md) for the licence text and attribution.
