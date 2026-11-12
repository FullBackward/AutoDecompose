# Case split on the attainable sunny-line counts {0,1,3} for IMO 2025 P1

| | |
|---|---|
| Kind | instance |
| Move | case-split |
| Language | lean |
| Status | accepted |
| Source | [harmonic-imo2025](../../sources/harmonic-imo2025/SOURCE.md) at `72b62405a176` |
| Licence | `LicenseRef-unknown` |

## Intent

Reduce the statement "the attainable sunny-line counts are exactly {0,1,3}" to
three constructions and two impossibilities. The forward direction of the set
equality enumerates the finite answer set `{0,1,3}` and closes each member with
a construction lemma (`k = 0, 1, 3`); the backward direction bounds `k ≤ 3` with
an impossibility lemma, then `interval_cases k` and rules out `k = 2` with a
second impossibility lemma.

## The decomposition

### parent `main_theorem`: [`HarmonicLean/IMO2025P1.lean` lines 1387-1431](https://github.com/harmonic-ai/IMO2025/blob/72b62405a176a7eaeadb335a7fa6ee80b6667161/HarmonicLean/IMO2025P1.lean#L1387-L1431) ([local copy](code/HarmonicLean/IMO2025P1.lean))

```lean
theorem main_theorem
  (n : ℕ)
  (hn : n ≥ 3) :
  {0, 1, 3} = { k | ∃ lines : Finset (Set (ℝ × ℝ)),
      (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = { v : ℝ × ℝ | a * v.1 + b * v.2 + c = 0 }) ∧
      lines.card = n ∧
      (∀ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b ≤ n + 1 → ∃ (l : Set (ℝ × ℝ)), l ∈ lines ∧ ((a : ℝ), (b : ℝ)) ∈ l) ∧
      ((lines.filter (fun l => ∃ a b c, l = { v : ℝ × ℝ | a * v.1 + b * v.2 + c = 0 } ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b)).card = k) } := by
        ext k;
        -- For the forward direction, if k is 0, 1, or 3, then by the lemmas we have, there exists such a set of lines.
        apply Iff.intro;
        · simp +zetaDelta at *;
          -- For each case, we can apply the corresponding lemma to construct the required set of lines.
          intro hk
          cases' hk with hk0 hk1 hk3;
          · convert lem_k0_possible n hn;
            · aesop;
            · -- By definition of $s$, if $(a, b) \in s n$, then there exist $a$ and $b$ such that $0 < a$, $0 < b$, $a + b \leq n + 1$, and $(a, b) = ((a : ℝ), (b : ℝ))$.
              unfold s; aesop;
            · -- By definition of Sunny, if there exist a, b, c such that the line is defined by a*x + b*y + c = 0 and a, b are non-zero and not equal, then the line is sunny.
              unfold Sunny; aesop;
          · bound;
            · convert lem_k1_possible n hn;
              · bound;
              · unfold s; aesop;
              · unfold Sunny; aesop;
            · convert lem_k3_possible n hn;
              · bound;
              · unfold s; aesop;
              · unfold Sunny; aesop;
        · -- By combining the results from the lemmas, we can conclude that k must be 0, 1, or 3.
          intros hk
          obtain ⟨lines, hlines⟩ := hk;
          -- By Lemma~\ref{lem:k_ge_4_impossible}, $k \leq 3$.
          have hk_le_3 : k ≤ 3 := by
            have := lem_k_ge_4_impossible n k hn;
            contrapose! this;
            simp +zetaDelta at *;
            exact ⟨ this, lines, hlines.1, hlines.2.1, fun a b hab => by rcases hab with ⟨ a', b', ha', hb', hab', rfl, rfl ⟩ ; exact hlines.2.2.1 a' b' ha' hb' hab', by convert hlines.2.2.2 using 2; ext; unfold Sunny; aesop ⟩;
          interval_cases k <;> norm_num;
          -- By Lemma~\ref{lem:k2_impossible}, there cannot be a configuration with $k=2$.
          apply lem_k2_impossible n hn;
          use lines;
          unfold Sunny; aesop;
          cases a_1 ; aesop
```

### child `lem_k0_possible`: [`HarmonicLean/IMO2025P1.lean` lines 121-137](https://github.com/harmonic-ai/IMO2025/blob/72b62405a176a7eaeadb335a7fa6ee80b6667161/HarmonicLean/IMO2025P1.lean#L121-L137) ([local copy](code/HarmonicLean/IMO2025P1.lean))

```lean
lemma lem_k0_possible (n : ℕ) (hn : n ≥ 3) :
  ∃ lines : Finset (Set (ℝ × ℝ)),
    (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = { v | a * v.1 + b * v.2 + c = 0 }) ∧
    lines.card = n ∧
    (∀ p ∈ s n, ∃ l ∈ lines, p ∈ l) ∧
    (lines.filter Sunny).card = 0 := by
      -- Apply the lemma to obtain the set of lines.
      obtain ⟨lines, hlines⟩ := lem_k0_construction n hn;
      use Finset.image ( fun i : ℕ => { v : ℝ × ℝ | v.1 = ( i : ℝ ) } ) ( Finset.Icc 1 n );
      aesop;
      · exact ⟨ 1, 0, by norm_num, -x, by ext; aesop ; linarith ⟩;
      · cases a_1 ; aesop;
        linarith;
      · -- Since all lines in the image are non-sunny, the filter of sunny lines is empty.
        ext l
        simp [hlines];
        exact fun x hx₁ hx₂ hx₃ => fun h => hlines l x hx₁ hx₂ hx₃ |>.2 h
```

### child `lem_k1_possible`: [`HarmonicLean/IMO2025P1.lean` lines 170-196](https://github.com/harmonic-ai/IMO2025/blob/72b62405a176a7eaeadb335a7fa6ee80b6667161/HarmonicLean/IMO2025P1.lean#L170-L196) ([local copy](code/HarmonicLean/IMO2025P1.lean))

```lean
lemma lem_k1_possible (n : ℕ) (hn : n ≥ 3) :
  ∃ lines : Finset (Set (ℝ × ℝ)),
    (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = { v | a * v.1 + b * v.2 + c = 0 }) ∧
    lines.card = n ∧
    (∀ p ∈ s n, ∃ l ∈ lines, p ∈ l) ∧
    (lines.filter Sunny).card = 1 := by
      -- Let's construct the set of lines L1 as described.
      set L1 : Finset (Set (ℝ × ℝ)) := insert {v : ℝ × ℝ | v.2 = v.1} (Finset.image (fun j : ℕ => {v : ℝ × ℝ | v.1 + v.2 = (j : ℝ)}) (Finset.Icc 3 (n + 1)));
      refine' ⟨ L1, _, _, _, _ ⟩;
      · aesop;
        · exact ⟨ -1, 1, by norm_num, 0, by ext; aesop ; linarith ⟩;
        · exact ⟨ 1, 1, by norm_num, -w, by ext; aesop ; linarith ⟩;
      · rw [ Finset.card_insert_of_not_mem ] <;> norm_num;
        · -- The function j ↦ {v | v.1 + v.2 = j} is injective, so the cardinality of the image is the same as the cardinality of the domain.
          have h_inj : Function.Injective (fun j : ℕ => {v : ℝ × ℝ | v.1 + v.2 = (j : ℝ)}) := by
            exact fun a b h => by simpa using Set.ext_iff.mp h ( 0, ↑a ) ;
          rw [ Finset.card_image_of_injective _ h_inj ] ; norm_num;
          omega;
        · intro x hx₁ hx₂; rw [ Set.ext_iff ] ; push_neg; use ( 0, x ) ; aesop;
      · -- For any point $p \in s n$, if $p.1 = p.2$, then $p$ lies on the line $y = x$. Otherwise, since $p.1 + p.2 \leq n + 1$, there exists $j \in \{3, 4, \ldots, n + 1\}$ such that $p.1 + p.2 = j$, so $p$ lies on the line $x + y = j$.
        intro p hp
        by_cases h_eq : p.1 = p.2;
        · aesop;
        · cases hp ; aesop;
          exact Or.inr ⟨ w + w_1, ⟨ by omega, by omega ⟩, by norm_cast ⟩;
      · have := lem_k1_construction n hn;
        exact this.2
```

### child `lem_k3_possible`: [`HarmonicLean/IMO2025P1.lean` lines 307-318](https://github.com/harmonic-ai/IMO2025/blob/72b62405a176a7eaeadb335a7fa6ee80b6667161/HarmonicLean/IMO2025P1.lean#L307-L318) ([local copy](code/HarmonicLean/IMO2025P1.lean))

```lean
lemma lem_k3_possible (n : ℕ) (hn : n ≥ 3) :
  ∃ lines : Finset (Set (ℝ × ℝ)),
    (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = { v | a * v.1 + b * v.2 + c = 0 }) ∧
    lines.card = n ∧
    (∀ p ∈ s n, ∃ l ∈ lines, p ∈ l) ∧
    (lines.filter Sunny).card = 3 := by
      -- By Lemma~\ref{lem:induction_step}, we can construct a set of $n$ lines covering $S_n$ with $k=3$ sunny lines for any $n \geq 3$.
      induction' n, Nat.succ_le.mpr hn using Nat.le_induction with n ih;
      · exact?;
      · -- Apply Lemma~\ref{lem:induction_step} to construct the set of lines for $n+1$.
        apply lem_induction_step n 3 ih;
        aesop
```

### child `lem_k_ge_4_impossible`: [`HarmonicLean/IMO2025P1.lean` lines 1217-1268](https://github.com/harmonic-ai/IMO2025/blob/72b62405a176a7eaeadb335a7fa6ee80b6667161/HarmonicLean/IMO2025P1.lean#L1217-L1268) ([local copy](code/HarmonicLean/IMO2025P1.lean))

```lean
lemma lem_k_ge_4_impossible (n k : ℕ) (hn : n ≥ 3) (hk : k ≥ 4) :
  ¬ (∃ lines : Finset (Set (ℝ × ℝ)),
    (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = { v | a * v.1 + b * v.2 + c = 0 }) ∧
    lines.card = n ∧
    (∀ p ∈ s n, ∃ l ∈ lines, p ∈ l) ∧
    (lines.filter Sunny).card = k) := by
      -- By induction on $n$, we can conclude that for all $n \geq 3$, it is impossible to have a configuration with $k \geq 4$ sunny lines.
      induction' n, Nat.succ_le.mpr hn using Nat.le_induction with n ih;
      · -- Apply the reduction lemma to the assumed configuration with k=4 for n=3.
        by_contra h_contra
        obtain ⟨lines, hlines⟩ := h_contra;
        simp +zetaDelta at *;
        linarith [ show ( Finset.filter Sunny lines ).card ≤ 3 by exact hlines.2.1 ▸ Finset.card_filter_le _ _ ];
      · -- Apply Lemma~\ref{lem:reduction} to the assumed configuration for $n+1$.
        intro h
        obtain ⟨lines, hlines⟩ := h;
        by_cases h_non_sunny : ∃ l ∈ lines, ¬Sunny l ∧ (l = {v : ℝ × ℝ | v.1 = (1:ℝ)} ∨ l = {v : ℝ × ℝ | v.2 = (1:ℝ)} ∨ l = {v : ℝ × ℝ | v.1 + v.2 = (n + 2 : ℝ)});
        · -- Apply the reduction lemma to the current configuration, using the non-sunny line identified in h_non_sunny.
          obtain ⟨lines', hlines'⟩ := lem_reduction (n + 1) k (by linarith) ⟨lines, hlines.1, hlines.2.1, hlines.2.2.1, hlines.2.2.2, by
            bound;
            · exact Or.inl left_2;
            · exact Or.inr <| Or.inl left_2;
            · exact Or.inr <| Or.inr <| by convert left_2 using 1; push_cast; ring;⟩;
          exact ‹n ≥ 3 → ¬∃ lines : Finset ( Set ( ℝ × ℝ ) ), ( ∀ line ∈ lines, ∃ a b c : ℝ, ¬ ( a = 0 ∧ b = 0 ) ∧ line = { v : ℝ × ℝ | a * v.1 + b * v.2 + c = 0 } ) ∧ lines.card = n ∧ ( ∀ p ∈ s n, ∃ l ∈ lines, p ∈ l ) ∧ ( Finset.filter Sunny lines ).card = k› ih ⟨ lines', hlines'.1, hlines'.2.1, hlines'.2.2.1, hlines'.2.2.2 ⟩;
        · by_cases h_boundary : {v : ℝ × ℝ | v.1 = (1:ℝ)} ∈ lines ∨ {v : ℝ × ℝ | v.2 = (1:ℝ)} ∈ lines ∨ {v : ℝ × ℝ | v.1 + v.2 = (n + 2 : ℝ)} ∈ lines;
          · norm_num +zetaDelta at *;
            rcases h_boundary with ( h | h | h );
            · specialize h_non_sunny _ h;
              norm_num at h_non_sunny;
              obtain ⟨ a, b, c, h₁, h₂, h₃, h₄ ⟩ := h_non_sunny;
              norm_num [ Set.Subset.antisymm_iff, Set.subset_def ] at h₁;
              exact h₃ ( by linarith [ h₁.1 1 0 rfl, h₁.1 1 1 rfl ] );
            · have h_non_sunny_y1 : ¬Sunny {v : ℝ × ℝ | v.2 = 1} := by
                rintro ⟨ a, b, c, h₁, h₂, h₃, h₄ ⟩;
                norm_num [ Set.Subset.antisymm_iff, Set.subset_def ] at h₁;
                exact h₂ ( by linarith [ h₁.1 0, h₁.1 1 ] );
              exact h_non_sunny _ h h_non_sunny_y1 |>.2.1 rfl;
            · specialize h_non_sunny _ h;
              norm_num +zetaDelta at *;
              obtain ⟨ a, b, c, h₁, h₂, h₃, h₄ ⟩ := h_non_sunny;
              norm_num [ Set.Subset.antisymm_iff, Set.subset_def ] at h₁;
              exact h₄ ( by linarith [ h₁.1 ( n + 2 ) 0 ( by ring ), h₁.1 ( n + 1 ) 1 ( by ring ), h₁.1 ( n ) 2 ( by ring ) ] );
          · have h_all_sunny : ∀ l ∈ lines, Sunny l := by
              intros l hl;
              contrapose! h_non_sunny;
              use l;
              bound;
              have := lem_boundary_lines_implication ( n + 1 ) ( by linarith ) lines;
              norm_num +zetaDelta at *;
              exact absurd ( this left_1 left left_2 h_boundary.1 h_boundary.2.1 ( mod_cast h_boundary.2.2 ) l hl ) h_non_sunny;
            have := lem_kn_impossible ( n + 1 ) ( by linarith );
            exact this ⟨ lines, hlines.2.1, h_all_sunny, hlines.2.2.1 ⟩
```

### child `lem_k2_impossible`: [`HarmonicLean/IMO2025P1.lean` lines 1352-1379](https://github.com/harmonic-ai/IMO2025/blob/72b62405a176a7eaeadb335a7fa6ee80b6667161/HarmonicLean/IMO2025P1.lean#L1352-L1379) ([local copy](code/HarmonicLean/IMO2025P1.lean))

```lean
lemma lem_k2_impossible (n : ℕ) (hn : n ≥ 3) :
  ¬ (∃ lines : Finset (Set (ℝ × ℝ)),
    (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = { v | a * v.1 + b * v.2 + c = 0 }) ∧
    lines.card = n ∧
    (∀ p ∈ s n, ∃ l ∈ lines, p ∈ l) ∧
    (lines.filter Sunny).card = 2) := by
      -- Assume for contradiction that there exists a configuration with $k=2$ sunny lines.
      by_contra h_contra;
      -- By Lemma~\ref{lem:reduction}, if there exists a configuration with $k=2$ for $n \geq 4$, then there exists a configuration with $k=2$ for $n-1$.
      have h_reduction : ∀ n ≥ 4, (∃ lines : Finset (Set (ℝ × ℝ)), (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = {v : ℝ × ℝ | a * v.1 + b * v.2 + c = 0}) ∧ lines.card = n ∧ (∀ p ∈ s n, ∃ l ∈ lines, p ∈ l) ∧ (Finset.filter Sunny lines).card = 2) → (∃ lines : Finset (Set (ℝ × ℝ)), (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = {v : ℝ × ℝ | a * v.1 + b * v.2 + c = 0}) ∧ lines.card = n - 1 ∧ (∀ p ∈ s (n - 1), ∃ l ∈ lines, p ∈ l) ∧ (Finset.filter Sunny lines).card = 2) := by
        -- Apply Lemma~\ref{lem:reduction} to the given configuration for $n \geq 4$.
        intros n hn h_config
        obtain ⟨lines, hlines⟩ := h_config;
        by_cases h_boundary : {v : ℝ × ℝ | v.1 = (1:ℝ)} ∈ lines ∨ {v : ℝ × ℝ | v.2 = (1:ℝ)} ∈ lines ∨ {v : ℝ × ℝ | v.1 + v.2 = (n + 1 : ℝ)} ∈ lines;
        · have := lem_reduction n 2 ( by linarith );
          exact this ⟨ lines, hlines.1, hlines.2.1, hlines.2.2.1, hlines.2.2.2, h_boundary ⟩;
        · have := lem_boundary_lines_implication n ( by linarith ) lines;
          simp_all ( config := { decide := Bool.true } );
          exact absurd hlines.2.2.2 ( by rw [ Finset.filter_true_of_mem this ] ; linarith );
      -- By repeatedly applying the reduction lemma, we can reduce the problem to the case where $n=3$.
      have h_reduction_to_3 : ∀ n ≥ 4, (∃ lines : Finset (Set (ℝ × ℝ)), (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = {v : ℝ × ℝ | a * v.1 + b * v.2 + c = 0}) ∧ lines.card = n ∧ (∀ p ∈ s n, ∃ l ∈ lines, p ∈ l) ∧ (Finset.filter Sunny lines).card = 2) → (∃ lines : Finset (Set (ℝ × ℝ)), (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = {v : ℝ × ℝ | a * v.1 + b * v.2 + c = 0}) ∧ lines.card = 3 ∧ (∀ p ∈ s 3, ∃ l ∈ lines, p ∈ l) ∧ (Finset.filter Sunny lines).card = 2) := by
        intro n hn h;
        induction' hn with n hn ih;
        · exact h_reduction 4 ( by norm_num ) h;
        · exact ih ( h_reduction _ ( Nat.le_succ_of_le hn ) h );
      by_cases hn4 : n ≥ 4;
      · exact lem_k2_impossible_n3 ( h_reduction_to_3 n hn4 h_contra );
      · exact lem_k2_impossible_n3 ( by interval_cases n ; exact h_contra )
```

### context `definitions`: [`HarmonicLean/IMO2025P1.lean` lines 40-53](https://github.com/harmonic-ai/IMO2025/blob/72b62405a176a7eaeadb335a7fa6ee80b6667161/HarmonicLean/IMO2025P1.lean#L40-L53) ([local copy](code/HarmonicLean/IMO2025P1.lean))

```lean
/-
A line in the plane is called sunny if it is not parallel to the $x$-axis, the $y$-axis, or the line $x+y=0$. A line is non-sunny otherwise.
--/
def Sunny (l : Set (ℝ × ℝ)) : Prop :=
  ∃ a b c, l = { v | a * v.1 + b * v.2 + c = 0 } ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b

def NonSunny (l : Set (ℝ × ℝ)) : Prop :=
  (∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ l = { v | a * v.1 + b * v.2 + c = 0 }) ∧ ¬ Sunny l

/-
For a positive integer $n$, define the set of points $S_n = \{(a,b) \in \mathbb{Z}^+ \times \mathbb{Z}^+ : a+b \leq n+1\}$.
--/
def s (n : ℕ) : Set (ℝ × ℝ) :=
  { v | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b ≤ n + 1 ∧ v = ((a : ℝ), (b : ℝ)) }
```

The parent `main_theorem` is a set equality `{0,1,3} = {k | …}`; its proof
(lines 1395-1431) is glue over five named lemmas, all stated and proved earlier
in the same file:

```
main_theorem
├─ forward  {0,1,3} ⊆ {k | …}        cases' hk with hk0 hk1 hk3   (line 1401)
│   ├─ k = 0 → lem_k0_possible       (line 1402) → lem_k0_construction
│   ├─ k = 1 → lem_k1_possible       (line 1409) → lem_k1_construction
│   └─ k = 3 → lem_k3_possible       (line 1413) → lem_induction_step → lem_induction_step_coverage
│                                                    (base n=3: lem_n3_k3_exists)
└─ backward  {k | …} ⊆ {0,1,3}       intros hk; obtain ⟨lines, hlines⟩ := hk  (1418-1419)
    ├─ k ≤ 3        from lem_k_ge_4_impossible   (line 1422)
    ├─ interval_cases k                           (line 1426)
    └─ k = 2        from lem_k2_impossible        (line 1428) → lem_reduction / lem_k2_impossible_n3
```

**Forward direction.** `apply Iff.intro` (line 1397) then
`cases' hk with hk0 hk1 hk3` (1401) turns the finite set `{0,1,3}` into three
goals `k = 0 ∨ k = 1 ∨ k = 3`. Each goal is closed by
`convert <construction lemma> n hn` (1402, 1409, 1413), the residual
differences repaired by `unfold s; aesop` and `unfold Sunny; aesop`. The three
children `lem_k0_possible`, `lem_k1_possible`, `lem_k3_possible` are the
constructive direction: each has the same statement shape
`∃ lines, … ∧ lines.card = n ∧ (∀ p ∈ s n, ∃ l ∈ lines, p ∈ l) ∧ (lines.filter Sunny).card = K`
for `K ∈ {0,1,3}`, so `convert` closes the goal up to definitional unfolding of
`s` and `Sunny`.

**Backward direction.** After `obtain ⟨lines, hlines⟩ := hk` (1419) the glue
does not split `k` directly. It first derives `k ≤ 3` by contraposition from
`lem_k_ge_4_impossible` (1421-1425), then `interval_cases k <;> norm_num`
(1426) splits `k` into 0, 1, 2, 3. The only non-trivial residual is `k = 2`,
closed by `apply lem_k2_impossible n hn` (1428).

**Why each child is a good leaf.** Each child is a self-contained statement
whose proof closes on its own or from named siblings, with no `sorry`/`axiom`:

- `lem_k0_possible` (121-137) is the `k=0` construction; it closes from the
  sibling `lem_k0_construction` (a cardinality/`NonSunny` fact about the `n`
  vertical lines `x = i`) plus `use`/`aesop`.
- `lem_k1_possible` (170-196) is the `k=1` construction; it builds
  `L1 = {y=x} ∪ {x+y=j : 3 ≤ j ≤ n+1}` and closes its sunny-count conjunct from
  the sibling `lem_k1_construction`.
- `lem_k3_possible` (307-318) is the `k=3` construction; it closes by induction
  on `n` (`Nat.le_induction`), the base case by `exact?` (which resolves to
  `lem_n3_k3_exists`), the step by `lem_induction_step n 3 ih`.
- `lem_k_ge_4_impossible` (1217-1268) rules out `k ≥ 4`; it closes by induction
  on `n`, the step by `lem_reduction` when a non-sunny boundary line exists and
  by `lem_boundary_lines_implication` + `lem_kn_impossible` when all lines are
  sunny.
- `lem_k2_impossible` (1352-1379) rules out `k = 2`; it closes by reducing `n`
  down to 3 with `lem_reduction`/`lem_boundary_lines_implication` and finishing
  with `lem_k2_impossible_n3`.

The `definitions` excerpt supplies the vocabulary (`Sunny`, `NonSunny`, `s`)
that every statement above quantifies over.

## Why it is good

1. The parent's proof is pure glue over the five named lemmas. Its 37 tactic
   lines invoke `lem_k0_possible`, `lem_k1_possible`, `lem_k3_possible`,
   `lem_k_ge_4_impossible`, `lem_k2_impossible` and no other project lemma
   (`check`, lines 1395-1431).
2. All five children are stated and proved in the same file, above the main
   theorem, and close without `sorry`/`axiom`/`admit`; the file ends with
   `#print axioms main_theorem` (line 1433) for inspecting axiom use (`check`,
   child ranges plus line 1433).
3. The shape is `scale: "theorem"`, 5 direct lemmas, 37 glue lines, and a
   longest checked chain of project lemmas below `main_theorem` 6 deep:
   `main_theorem → lem_k_ge_4_impossible → lem_kn_impossible →
   lem_kn_impossible_n_ge_5 → lem_kn_impossible_n_ge_5_point_coverage →
   lem_kn_point_22 → lem_kn_setup` (`measurement`, call sites 1422, 1210, 1133,
   1019, 845).
4. The authors recorded the answer and the case plan in comments: the file
   header ends "Answer: 0, 1, 3" (line 7), and the glue's comments name the
   lemmas it applies ("By Lemma~\ref{lem:k_ge_4_impossible}, $k \leq 3$", line
   1420; "By Lemma~\ref{lem:k2_impossible} …", line 1427) (`author-statement`,
   lines 7 and 1420-1427).

In my opinion the noteworthy detail is that the backward split on `k` is
*staged*: the glue does not case on `k` immediately but first forces the bound
`k ≤ 3` out of an impossibility lemma, so that `interval_cases k` becomes a
small, exhaustible split with a single excluded case (`k = 2`) left to rule
out.

## When to use it, and when not

Use it when the goal is "exactly these finitely many values are attainable" (a
set equality between a literal finite set and a comprehension), when each
attainable value already has a construction lemma and each excluded value an
impossibility lemma, and when the excluded values can be bounded by a single
lemma so `interval_cases` terminates. It helps if the construction lemmas share
one statement shape, so `convert`/`unfold` closes each case uniformly (here all
three constructions differ only in the sunny count `0/1/3`).

Avoid it when the answer set is large or unknown, when the constructions and
impossibilities are not already isolated as named lemmas (then the glue is not
the content), or when the excluded-case reasoning cannot be compressed into a
single bounding lemma and a small `interval_cases`.

## Consequences

Forward: `cases' hk with hk0 hk1 hk3` on the finite set `{0,1,3}` creates one
goal per element and leaves the exhaustiveness of that enumeration to Lean (the
disjunction over the finset). Each goal must be closed by `convert` to a lemma
whose statement matches up to unfolding; here `unfold s`/`unfold Sunny`/`aesop`
repair the mismatch. Backward: the split on `k` is indirect — the glue proves
`k ≤ 3` first (contraposing `lem_k_ge_4_impossible`), then `interval_cases k`
yields the finite cases 0,1,2,3, and the single excluded case `k = 2` is
disposed of by `lem_k2_impossible`. Failure mode: `convert` requires the goal
and child to be definitionally close; if a child's statement diverges from the
parent's inline predicates, each case needs its own normalisation and the
shared `convert … <;> unfold …` pattern breaks.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/lean_action_ci.yml runs leanprover/lean-action@v1 (lake build of the whole project, including HarmonicLean/IMO2025P1.lean) on push/PR; pinned commit 72b62405a176a7eaeadb335a7fa6ee80b6667161 is on the default branch main (verified via API branches-where-head) | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 72b62405a176a7eaeadb335a7fa6ee80b6667161 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read copied file lines 1395-1431: the only named project lemmas invoked are convert lem_k0_possible (1402), convert lem_k1_possible (1409), convert lem_k3_possible (1413), have := lem_k_ge_4_impossible (1422), apply lem_k2_impossible (1428); rest of body is aesop/unfold/simp/norm_num/interval_cases/bound/contrapose!/cases' | verifier |
| 2 | verified | Read copied file: five children defined at 121, 170, 307, 1217, 1352 (all above main_theorem at 1387) with proof bodies in the stated ranges; grep found no 'sorry', 'admit' or 'axiom' keyword anywhere in the file; line 1433 is '#print axioms main_theorem' | verifier |
| 3 | verified | Verified call sites in copied file: main_theorem->lem_k_ge_4_impossible at 1422; ->lem_kn_impossible at 1267; ->lem_kn_impossible_n_ge_5 at 1210; ->lem_kn_impossible_n_ge_5_point_coverage at 1133; ->lem_kn_point_22 at 1019; ->lem_kn_setup at 845 (leaf at 532). Lemma defs match cited ranges. Glue = 1431-1395+1 = 37 lines; 5 direct lemmas; 6 project lemmas below main_theorem | verifier |
| 4 | verified | Read copied file: line 7 is "Answer: 0, 1, 3"; line 1420 comment "-- By Lemma~\ref{lem:k_ge_4_impossible}, $k \leq 3$."; line 1427 comment "-- By Lemma~\ref{lem:k2_impossible}, there cannot be a configuration with $k=2$." | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Independently read the copied code at HarmonicLean/IMO2025P1.lean (provenance pass, byte-identical at 72b62405). Decomposition matches the entry: main_theorem (1387-1431) is pure glue — forward direction cases' hk into the {0,1,3} cases and closes each with convert lem_k0_possible (1402) / lem_k1_possible (1409) / lem_k3_possible (1413); backward direction proves k<=3 via lem_k_ge_4_impossible (1422), interval_cases k, then lem_k2_impossible (1428). The five children are exactly the lemmas the glue invokes; each child's closed_by matches its code (k0: lem_k0_construction+image+aesop 128-137; k1: refine'+lem_k1_construction 177-196; k3: Nat.le_induction, exact? -> lem_n3_k3_exists, lem_induction_step 314-318; k_ge_4: Nat.le_induction, card_filter_le base, lem_reduction / lem_boundary_lines_implication + lem_kn_impossible 1224-1268; k2: lem_reduction+lem_boundary_lines_implication to n=3 then lem_k2_impossible_n3 1358-1379). Closes: grep found no sorry/admit/axiom in the file; #print axioms main_theorem at 1433. Shape numbers verified: direct_lemmas=5, glue_lines=1431-1395+1=37, child_lines=[11,21,6,46,22] (127-137, 176-196, 313-318, 1223-1268, 1358-1379), parent_lines=45, depth=6 chain main_theorem->lem_k_ge_4_impossible(1422)->lem_kn_impossible(1267)->lem_kn_impossible_n_ge_5(1210)->lem_kn_impossible_n_ge_5_point_coverage(1133)->lem_kn_point_22(1019)->lem_kn_setup(845, leaf 532) all real. | reviewer-correctness |
| generality | accept | Move generalized beyond the example to the goal shape "set equality between a literal finite set and a comprehension": use-when names a construction lemma per attainable value, an impossibility lemma per excluded value, and one bounding lemma so interval_cases terminates; avoid-when names large/unknown answer set, lemmas not already isolated, and excluded-case reasoning that will not compress into one bound plus a small interval_cases. Consequences give a specific failure mode (convert needs the goal and child definitionally close; a diverging child statement breaks the shared convert/unfold pattern). Leaf quality for a bounded prover is stated: each child is self-contained, closes on its own or from named siblings with no sorry/axiom, and the constructions share one statement shape; the staged backward split (bound k<=3, interval_cases, one excluded case k=2 left) is honestly described. | reviewer-generality |
| provenance-licence | accept | check_provenance passes (1 file byte-identical at 72b62405a176a7eaeadb335a7fa6ee80b6667161); copied-file sha256 b763f019... matches entry.json; commit consistent across entry.json, SOURCE.md and ledger/sources.jsonl; licence LicenseRef-unknown correct - jsDelivr listing at the pinned commit shows no LICENSE/COPYING file at root; permalinks use the pinned commit and path HarmonicLean/IMO2025P1.lean, all line ranges within the 1433-line file. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/harmonic-ai/IMO2025 at commit `72b62405a176a7eaeadb335a7fa6ee80b6667161`, under `LicenseRef-unknown`; see the [source note](../../sources/harmonic-imo2025/SOURCE.md) for the licence text and attribution.
