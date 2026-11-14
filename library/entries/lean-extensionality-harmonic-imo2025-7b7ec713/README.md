# Set extensionality over the two answer sets for IMO 2025 P5 (Alice wins iff λ > 1/√2, Bazza wins iff 0 < λ < 1/√2)

| | |
|---|---|
| Kind | instance |
| Move | extensionality |
| Language | lean |
| Status | accepted |
| Source | [harmonic-imo2025](../../sources/harmonic-imo2025/SOURCE.md) at `72b62405a176` |
| Licence | `LicenseRef-unknown` |
| Licence recorded | 2026-11-14T09:46:45Z |

## Intent

The main theorem asserts two set equalities characterising the winning values
of λ for IMO 2025 P5 (Alice's set equals `{λ | λ > 1/√2}`; Bazza's equals
`{λ | 0 < λ < 1/√2}`). The proof splits each equality by `Set.ext` into two
inclusions; in each equality one inclusion is proved inline (closing through
`lemSLowerBound`), and the reverse inclusion is handed whole to a half-theorem
— `lemAliceWinsLargeLambda` or `lemBazzaWinsSmallLambda` — so the answer is the
pointwise join of three named lemmas.

## The decomposition

### parent `main_theorem`: [`HarmonicLean/IMO2025P5.lean` lines 615-726](https://github.com/harmonic-ai/IMO2025/blob/72b62405a176a7eaeadb335a7fa6ee80b6667161/HarmonicLean/IMO2025P5.lean#L615-L726) ([local copy](code/HarmonicLean/IMO2025P5.lean))

```lean
theorem main_theorem :
  {lam : ℝ | 0 < lam ∧ ∃ alice : AliceStrategy, alice.Wins lam} = {lam : ℝ | 1 / Real.sqrt 2 < lam} ∧
  {lam : ℝ | 0 < lam ∧ ∃ bazza : BazzaStrategy, bazza.Wins lam} = {lam : ℝ | 0 < lam ∧ lam < 1 / Real.sqrt 2} := by
  constructor;
  · apply Set.ext;
    bound;
    · cases a ; aesop;
      -- By definition of Alice's winning strategy, if Alice has a winning strategy, then x must be greater than 1/sqrt(2).
      have h_x_gt : x > 1 / Real.sqrt 2 := by
        have := h bazzaReferenceStrategy;
        -- By definition of Alice's winning strategy, if Alice has a winning strategy, then there exists some $n$ where the move is invalid and $n$ is odd.
        obtain ⟨n, hn₁, hn₂⟩ := this;
        -- By definition of ValidMove, if the move is invalid, then for odd n, the sum of squares exceeds n+1.
        have h_sum_squares : ∑ i in Finset.range n, (play w bazzaReferenceStrategy i : ℝ) ^ 2 > n + 1 := by
          have := hn₁.1;
          unfold ValidMove at this;
          aesop;
          · exact absurd h_1 ( by simpa using hn₂ );
          · contrapose! this;
            erw [ Finset.sum_Ico_succ_top ] <;> norm_num;
            rw [ ← NNReal.coe_le_coe ] ; aesop;
            rw [ show play w bazzaReferenceStrategy n = bazzaReferenceStrategy ( n / 2 ) ( fun i => play w bazzaReferenceStrategy i ) from ?_ ];
            · unfold bazzaReferenceStrategy;
              norm_num [ ← NNReal.coe_le_coe ];
              split_ifs;
              · norm_num [ ← NNReal.coe_le_coe, Finset.sum_range ];
                rw [ Real.sq_sqrt ];
                · rw [ show n = 2 * ( n / 2 ) + 1 by linarith [ Nat.odd_iff.mp hn₂, Nat.div_add_mod n 2 ] ];
                  norm_num [ Nat.add_div ];
                  rw [ show ( 2 * ( n / 2 ) + 1 ) / 2 = n / 2 by omega ] ; linarith;
                · linarith;
              · convert this using 1;
                unfold bazzaReferenceStrategy;
                norm_num;
            · unfold play;
              norm_num [ Nat.odd_iff.mp hn₂ ];
              congr!;
              exact?;
        -- Since $n$ is odd, we can write $n = 2k + 1$ for some $k$.
        obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := hn₂;
        -- By definition of play, we can write out the sum of squares for the first 2k+1 turns.
        have h_play_sum_squares : ∑ i in Finset.range (2 * k + 1), (play w bazzaReferenceStrategy i : ℝ) ^ 2 ≤ 2 * k + (play w bazzaReferenceStrategy (2 * k) : ℝ) ^ 2 := by
          -- By definition of ValidMove, the sum of squares up to 2k is ≤ 2k.
          have h_sum_squares_2k : ∑ i in Finset.range (2 * k), (play w bazzaReferenceStrategy i : ℝ) ^ 2 ≤ 2 * k := by
            have := hn₁.2;
            have := @this ( 2 * k ) ; unfold ValidMove at this ; aesop;
            have := @this_1 ( 2 * k ) ; unfold ValidMove at this ; aesop;
            have := @this_1 ( 2 * k - 1 ) ; rcases k with ( _ | k ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ, parity_simps ];
            unfold ValidMove at this ; aesop;
            convert NNReal.coe_le_coe.mpr this using 1;
            · erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num;
            · norm_cast;
          rw [ Finset.sum_range_succ ] ; linarith;
        have h_play_sum_squares : play w bazzaReferenceStrategy (2 * k) ≤ x * (2 * k + 1) - ∑ i in Finset.range (2 * k), (play w bazzaReferenceStrategy i : ℝ) := by
          have := hn₁.2;
          have := @this ( 2 * k ) ; unfold ValidMove at this ; aesop;
          erw [ Finset.sum_Ico_succ_top ] at this <;> norm_num at *;
          linarith;
        have h_play_sum_squares : ∑ i in Finset.range (2 * k), (play w bazzaReferenceStrategy i : ℝ) ≥ k * Real.sqrt 2 := by
          have := @lemSLowerBound x w ( k + 1 ) ( by linarith ) ?_;
          · aesop;
          · intro m hm;
            have := hn₁.2;
            exact Classical.not_not.1 fun hnm => not_lt_of_ge ( this hnm ) ( by omega );
        simp +zetaDelta at *;
        -- By combining the terms, we can factor out $\sqrt{2}$ and simplify the expression.
        have h_simplified : Real.sqrt 2 < x * (2 * k + 1) - k * Real.sqrt 2 := by
          nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, show ( play w bazzaReferenceStrategy ( 2 * k ) : ℝ ) ≥ 0 by positivity ];
        rw [ inv_eq_one_div, div_lt_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ];
      simpa using h_x_gt;
    · exact ⟨ lt_trans ( by positivity ) a, lemAliceWinsLargeLambda x a ⟩;
  · -- To prove the equality, we show mutual inclusion.
    apply Set.ext
    intro lam;
    constructor;
    · -- If there exists a bazza strategy that wins, then by the problem's statement, lam must be less than 1/sqrt(2).
      intro h
      obtain ⟨bazza, hbazza⟩ := h.right
      have hlam : 0 < lam ∧ lam < 1 / Real.sqrt 2 := by
        specialize hbazza ( fun n x => 0 );
        aesop;
        unfold ValidMove at *;
        have := left_1.1 ; aesop;
        contrapose! this;
        -- Since $w$ is even, we can write $w = 2k$ for some $k$.
        obtain ⟨k, rfl⟩ : ∃ k, w = 2 * k := even_iff_two_dvd.mp right;
        -- By definition of play, we can write out the sum.
        have h_sum : ∑ i in Finset.Iic (2 * k), (play (fun n x => 0) bazza i : ℝ) = ∑ i in Finset.range k, (play (fun n x => 0) bazza (2 * i + 1) : ℝ) := by
          erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ, Nat.mul_succ ];
          rw [ show ( Finset.range ( 2 * k ) : Finset ℕ ) = Finset.image ( fun i => 2 * i ) ( Finset.range k ) ∪ Finset.image ( fun i => 2 * i + 1 ) ( Finset.range k ) from ?_, Finset.sum_union ] <;> norm_num;
          · unfold play;
            norm_num;
          · norm_num [ Finset.disjoint_right ];
            intros; omega;
          · ext ; aesop;
            · rcases Nat.even_or_odd' a with ⟨ b, rfl | rfl ⟩ <;> [ left; right ] <;> exact ⟨ b, by linarith, rfl ⟩;
            · linarith;
        -- By definition of play, we can write out the sum of squares.
        have h_sum_squares : ∑ i in Finset.range k, (play (fun n x => 0) bazza (2 * i + 1) : ℝ) ^ 2 ≤ 2 * k := by
          have := left_1.2;
          have := @this ( 2 * k - 1 ) ; rcases k with ( _ | k ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ, parity_simps ];
          convert NNReal.coe_le_coe.mpr this using 1;
          · erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ Finset.sum_range_succ, Nat.mul_succ ];
            unfold play;
            exact Nat.recOn k ( by norm_num ) fun n ihn => by norm_num [ Nat.mul_succ, Finset.sum_range_succ, Nat.add_mod, Nat.mul_mod ] at * ; linarith;
          · norm_cast;
        have := Finset.sum_le_sum fun i ( hi : i ∈ Finset.range k ) => pow_two_nonneg ( ( play ( fun n x => 0 ) bazza ( 2 * i + 1 ) : ℝ ) - Real.sqrt 2 );
        norm_num [ sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _ ] at this;
        norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] at *;
        rw [ inv_eq_one_div, div_le_iff₀ ] at * <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ]
      exact hlam;
    · exact fun h => ⟨ h.1, lemBazzaWinsSmallLambda lam h ⟩
```

### child `lemSLowerBound`: [`HarmonicLean/IMO2025P5.lean` lines 181-212](https://github.com/harmonic-ai/IMO2025/blob/72b62405a176a7eaeadb335a7fa6ee80b6667161/HarmonicLean/IMO2025P5.lean#L181-L212) ([local copy](code/HarmonicLean/IMO2025P5.lean))

```lean
lemma lemSLowerBound (lam : ℝ) (alice : AliceStrategy) (k : ℕ) (hk : 1 ≤ k)
  (h_not_won : ∀ m < 2 * k - 2, ValidMove lam (play alice bazzaReferenceStrategy) m) :
  s (play alice bazzaReferenceStrategy) (2 * (k - 1)) ≥ ((k - 1) : ℝ) * Real.sqrt 2 := by
  -- By Lemma~\ref{lem:pair_sum_lower_bound}, for each $j$ from $1$ to $k-1$, we have $x_{2j-1} + x_{2j} \ge \sqrt{2}$.
  have h_pair_sum_lower_bound : ∀ j ∈ Finset.Ico 1 k, (play alice bazzaReferenceStrategy (2 * j - 2) : ℝ) + (play alice bazzaReferenceStrategy (2 * j - 1) : ℝ) ≥ Real.sqrt 2 := by
    intro j hj;
    apply_rules [ lemPairSumLowerBound ];
    · -- Since $j$ is in the Finset.Ico 1 k, we have $1 \leq j$.
      aesop;
    · -- Apply the lemma that states if Bazza uses his reference strategy and neither player has won by turn $2k-1$, then $Q_{2k-2} = 2(k-1)$.
      apply lemQ_2k_minus_2_under_bazza_ref;
      exacts [ Finset.mem_Ico.mp hj |>.1, fun m hm => h_not_won m ( by linarith [ Finset.mem_Ico.mp hj |>.2, Nat.sub_add_cancel ( by linarith [ Finset.mem_Ico.mp hj |>.1, Finset.mem_Ico.mp hj |>.2 ] : 2 ≤ 2 * k ), Nat.sub_add_cancel ( by linarith [ Finset.mem_Ico.mp hj |>.1, Finset.mem_Ico.mp hj |>.2 ] : 2 ≤ 2 * j ) ] ) ];
    · unfold play;
      -- Since $2j-1$ is odd, $(2j-1) \% 2 = 1$, so the if condition is false.
      have h_odd : (2 * j - 1) % 2 = 1 := by
        cases j <;> norm_num [ Nat.add_mod, Nat.mul_succ ] at *;
      rw [ if_neg ];
      · rw [ show ( 2 * j - 1 ) / 2 = j - 1 by omega ];
        congr!;
        exact?;
      · -- Since $h_odd$ states that $(2 * j - 1) \% 2 = 1$, we can directly conclude that $(2 * j - 1) \% 2 \neq 0$.
        aesop;
    · rcases j with ( _ | j ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ ];
      have := h_not_won ( 2 * j + 1 ) ( by omega );
      unfold ValidMove at this; aesop;
      exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( fun i hi => Finset.mem_Iic.mpr ( by linarith [ Finset.mem_range.mp hi ] ) ) fun _ _ _ => sq_nonneg _ ) ( mod_cast this );
  -- By summing the inequalities from h_pair_sum_lower_bound over all j from 1 to k-1, we get the desired result.
  have h_sum_pairs : ∑ j in Finset.Ico 1 k, ((play alice bazzaReferenceStrategy (2 * j - 2) : ℝ) + (play alice bazzaReferenceStrategy (2 * j - 1) : ℝ)) ≥ (k - 1) * Real.sqrt 2 := by
    exact le_trans ( by norm_num [ hk ] ) ( Finset.sum_le_sum h_pair_sum_lower_bound );
  convert h_sum_pairs using 1;
  unfold s;
  exact Nat.recOn k ( by norm_num ) fun n ih => by cases n <;> norm_num [ Nat.mul_succ, Finset.sum_range_succ, Finset.sum_Ico_succ_top ] at * ; linarith;
```

### child `lemBazzaWinsSmallLambda`: [`HarmonicLean/IMO2025P5.lean` lines 229-303](https://github.com/harmonic-ai/IMO2025/blob/72b62405a176a7eaeadb335a7fa6ee80b6667161/HarmonicLean/IMO2025P5.lean#L229-L303) ([local copy](code/HarmonicLean/IMO2025P5.lean))

```lean
lemma lemBazzaWinsSmallLambda (lam : ℝ) (hlam : 0 < lam ∧ lam < 1 / Real.sqrt 2) :
  ∃ bazza, BazzaStrategy.Wins lam bazza := by
  -- By Lemma~\ref{lem:alice_cannot_win_small_lambda}, if $\lambda \le 1/\sqrt{2}$, Alice cannot have a winning strategy. Therefore, Bazza's reference strategy must be a winning strategy.
  have h_bazza_wins : ∀ alice : AliceStrategy, ∃ n, IsLeast {m | ¬ValidMove lam (play alice bazzaReferenceStrategy) m} n ∧ Even n := by
    bound;
    by_contra h_contra;
    -- If Alice cannot win, then for all $n$, the game continues.
    have h_game_continues : ∀ n, ValidMove lam (play alice bazzaReferenceStrategy) n := by
      intro n;
      induction' n using Nat.strong_induction_on with n ih;
      rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩;
      · unfold ValidMove;
        contrapose! h_contra;
        use 2 * k;
        unfold ValidMove;
        unfold IsLeast;
        aesop;
        intro m hm;
        contrapose! hm;
        unfold ValidMove at ih; aesop;
      · have h_q_prev : q (play alice bazzaReferenceStrategy) (2 * k) = (2 * k : ℝ) := by
          convert lemQ_2k_minus_2_under_bazza_ref lam alice ( k + 1 ) ( by linarith ) _ using 1;
          · norm_num;
          · grind;
        unfold ValidMove;
        have h_not_win : ¬ (q (play alice bazzaReferenceStrategy) (2 * k + 1) > (2 * (k + 1) : ℝ)) := by
          have h_not_win : (play alice bazzaReferenceStrategy) (2 * k) ≤ Real.sqrt 2 := by
            have h_not_win : (play alice bazzaReferenceStrategy) (2 * k) ≤ lam * (2 * k + 1) - s (play alice bazzaReferenceStrategy) (2 * k) := by
              have := ih ( 2 * k ) ( by linarith ) ; unfold ValidMove at this ; aesop;
              unfold s;
              erw [ Finset.sum_Ico_eq_sub _ _ ] at this <;> norm_num at *;
              rw [ Finset.sum_range_succ ] at this ; linarith;
            have h_s_lower_bound : s (play alice bazzaReferenceStrategy) (2 * k) ≥ (k : ℝ) * Real.sqrt 2 := by
              convert lemSLowerBound lam alice ( k + 1 ) ( by linarith ) _ using 1;
              · norm_num;
              · exact fun m hm => ih m ( by omega );
            rw [ lt_div_iff₀ ] at * <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ];
          unfold q at *;
          norm_num [ Finset.sum_range_succ ];
          nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ), show ( play alice bazzaReferenceStrategy ( 2 * k ) : ℝ ) ≥ 0 by positivity ];
        aesop;
        unfold q at *;
        erw [ Finset.sum_Ico_succ_top ] <;> norm_num;
        rw [ show play alice bazzaReferenceStrategy ( 2 * k + 1 ) = bazzaReferenceStrategy k fun i => play alice bazzaReferenceStrategy i from ?_ ];
        · rw [ ← NNReal.coe_le_coe ] ; aesop;
          unfold bazzaReferenceStrategy;
          norm_num [ Finset.sum_range ] at *;
          split_ifs;
          · norm_num [ ← NNReal.coe_le_coe ];
            rw [ Real.sq_sqrt ] <;> linarith;
          · convert h_not_win using 1;
            · unfold bazzaReferenceStrategy;
              norm_num;
            · ring;
        · unfold play;
          norm_num [ Nat.add_mod ];
          rw [ show ( 2 * k + 1 ) / 2 = k by omega ];
          congr!;
          exact?;
    -- By Lemma~\ref{lem:s_lower_bound}, $S_{2k-2} \ge (k-1)\sqrt{2}$ for all $k \ge 1$.
    have h_s_lower_bound : ∀ k : ℕ, 1 ≤ k → s (play alice bazzaReferenceStrategy) (2 * (k - 1)) ≥ ((k - 1) : ℝ) * Real.sqrt 2 := by
      intro k hk;
      convert lemSLowerBound lam alice k hk _;
      exact fun m hm => h_game_continues m;
    -- Choose $k$ such that $(k-1)\sqrt{2} > \lambda(2k-1)$.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, 1 ≤ k ∧ ((k - 1) : ℝ) * Real.sqrt 2 > lam * ((2 * k - 1) : ℝ) := by
      rw [ lt_div_iff₀ ] at * <;> norm_num;
      exact ⟨ ⌊ ( 1 - lam * Real.sqrt 2 ) ⁻¹ * 2⌋₊ + 2, by linarith, by push_cast; nlinarith [ Nat.lt_floor_add_one ( ( 1 - lam * Real.sqrt 2 ) ⁻¹ * 2 ), Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, mul_inv_cancel₀ ( by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] : ( 1 - lam * Real.sqrt 2 ) ≠ 0 ) ] ⟩;
    specialize h_s_lower_bound k hk.1;
    specialize h_game_continues ( 2 * ( k - 1 ) ) ; unfold ValidMove at h_game_continues ; aesop;
    erw [ Finset.sum_Ico_eq_sub _ _ ] at h_game_continues <;> norm_num at *;
    unfold s at h_s_lower_bound;
    rw [ Finset.sum_range_succ ] at h_game_continues;
    linarith [ show ( play alice bazzaReferenceStrategy ( 2 * ( k - 1 ) ) : ℝ ) ≥ 0 by positivity ];
  exact ⟨ bazzaReferenceStrategy, h_bazza_wins ⟩
```

### child `lemAliceWinsLargeLambda`: [`HarmonicLean/IMO2025P5.lean` lines 535-610](https://github.com/harmonic-ai/IMO2025/blob/72b62405a176a7eaeadb335a7fa6ee80b6667161/HarmonicLean/IMO2025P5.lean#L535-L610) ([local copy](code/HarmonicLean/IMO2025P5.lean))

```lean
lemma lemAliceWinsLargeLambda (lam : ℝ) (hlam : lam > 1 / Real.sqrt 2) :
  ∃ alice, AliceStrategy.Wins lam alice := by
  -- obtain such a K using lemExistenceOfKForAlice
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 1 ≤ K ∧ lam > f K := by
    exact?;
  use aliceReferenceStrategy lam K;
  intro bazza;
  by_contra h_contra;
  -- If Alice never wins, then Bazza must win by turn $2K-1$.
  have h_bazza_wins : ∀ m < 2 * K - 2, ValidMove lam (play (aliceReferenceStrategy lam K) bazza) m := by
    intro m hm;
    induction' m using Nat.strong_induction_on with m ih;
    by_cases h_even : Even m;
    · unfold ValidMove;
      -- Since $m$ is even, we can write $m = 2k$ for some $k$.
      obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := even_iff_two_dvd.mp h_even;
      -- By definition of play, we can write out the sum.
      have h_sum : ∑ i in Finset.Iic (2 * k), (play (aliceReferenceStrategy lam K) bazza i : ℝ) = ∑ i in Finset.range k, (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ) := by
        erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ, Nat.mul_succ ];
        rw [ show ( Finset.range ( 2 * k ) : Finset ℕ ) = Finset.image ( fun i => 2 * i ) ( Finset.range k ) ∪ Finset.image ( fun i => 2 * i + 1 ) ( Finset.range k ) from ?_, Finset.sum_union ] <;> norm_num;
        · unfold play;
          unfold aliceReferenceStrategy;
          norm_num;
          rw [ Finset.sum_congr rfl fun i hi => by rw [ if_pos ( by linarith [ Finset.mem_range.mp hi, Nat.sub_add_cancel ( show 2 ≤ 2 * K from by linarith ) ] ) ] ] ; norm_num;
          intros; omega;
        · norm_num [ Finset.disjoint_right ];
          intros; omega;
        · ext ; aesop;
          · rcases Nat.even_or_odd' a with ⟨ b, rfl | rfl ⟩ <;> [ left; right ] <;> exact ⟨ b, by linarith, rfl ⟩;
          · linarith;
      -- By definition of play, we can write out the sum of squares.
      have h_sum_squares : ∑ i in Finset.range k, (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ) ^ 2 ≤ 2 * k := by
        have := ih ( 2 * k - 1 ) ; rcases k with ( _ | k ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ, parity_simps ];
        have := ih ( 2 * k + 1 ) ( by linarith ) ( by omega ) ; unfold ValidMove at this; aesop;
        norm_cast;
        refine le_trans ?_ ( this.trans ?_ );
        · have h_sum_squares : Finset.image (fun i => 2 * i + 1) (Finset.range (k + 1)) ⊆ Finset.Iic (2 * k + 1) := by
            exact Finset.image_subset_iff.mpr fun i hi => Finset.mem_Iic.mpr ( by linarith [ Finset.mem_range.mp hi ] );
          exact le_trans ( by rw [ Finset.sum_image ( by norm_num ) ] ) ( Finset.sum_le_sum_of_subset h_sum_squares );
        · norm_cast;
      have := Finset.sum_le_sum fun i ( hi : i ∈ Finset.range k ) => pow_two_nonneg ( ( play ( aliceReferenceStrategy lam K ) bazza ( 2 * i + 1 ) : ℝ ) - Real.sqrt 2 );
      norm_num [ sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _ ] at this;
      norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] at *;
      rw [ inv_eq_one_div, div_lt_iff₀ ] at hlam <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ];
    · contrapose! h_contra;
      use m;
      exact ⟨ ⟨ h_contra, fun n hn => not_lt.1 fun contra => hn <| ih n contra <| by omega ⟩, Nat.odd_iff.mpr <| Nat.not_even_iff.mp h_even ⟩;
  have h_alice_wins : q (play (aliceReferenceStrategy lam K) bazza) (2 * K - 1) > (2 * K : ℝ) := by
    have h_alice_wins : lam * ((2 * K - 1) : ℝ) > s (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1)) + Real.sqrt ((2 * K : ℝ) - q (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1))) := by
      have := lemBazzaObjectiveUpperBound lam K;
      rcases K with ( _ | _ | K ) <;> aesop;
      · unfold s q; norm_num;
        unfold f at hK ; aesop;
        norm_num at hK ; linarith;
      · refine' lt_of_le_of_lt ( this bazza h_bazza_wins ) _;
        unfold f at hK;
        rw [ div_lt_iff₀ ] at hK <;> norm_num at * <;> nlinarith;
    exact?;
  refine' h_contra ⟨ 2 * K - 1, _, _ ⟩;
  · -- Since $ValidMove$ holds for all $m < 2K-2$, the next $m$ where $ValidMove$ fails must be $2K-1$.
    have h_least : ∀ m, m < 2 * K - 1 → ValidMove lam (play (aliceReferenceStrategy lam K) bazza) m := by
      -- Since $m < 2K-1$, we have either $m < 2K-2$ or $m = 2K-2$. In both cases, $ValidMove$ holds by $h_bazza_wins$.
      intros m hm
      by_cases hm' : m < 2 * K - 2;
      · exact h_bazza_wins m hm';
      · convert lemAliceMoveValid lam hlam K hK bazza _;
        · omega;
        · exact h_bazza_wins;
    refine' ⟨ _, fun m hm => _ ⟩ <;> aesop;
    · unfold ValidMove at a;
      rcases K with ( _ | K ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ, parity_simps ];
      unfold q at h_alice_wins;
      erw [ Finset.sum_Ico_succ_top ] at a <;> norm_num at *;
      exact h_alice_wins.not_le ( by norm_num [ ← NNReal.coe_le_coe ] at *; nlinarith );
    · exact not_lt.1 fun contra => hm <| h_least m <| by omega;
  · exact ⟨ K - 1, by omega ⟩
```

### context `definitions`: [`HarmonicLean/IMO2025P5.lean` lines 46-114](https://github.com/harmonic-ai/IMO2025/blob/72b62405a176a7eaeadb335a7fa6ee80b6667161/HarmonicLean/IMO2025P5.lean#L46-L114) ([local copy](code/HarmonicLean/IMO2025P5.lean))

```lean
/- Alice's strategy: given a tuple of nonnegative reals of even length,
yields the next number. -/
abbrev AliceStrategy : Type := ∀ n, (Fin (2 * n) → NNReal) → NNReal
/- Bazza's strategy: given a tuple of nonnegative reals of odd length,
yields the next number. -/
abbrev BazzaStrategy : Type := ∀ n, (Fin (2 * n + 1) → NNReal) → NNReal

/- The sequence of numbers produced by a couple of strategies. -/
def play (alice : AliceStrategy) (bazza : BazzaStrategy) : ℕ → NNReal
  | n =>
    if n % 2 = 0 then alice (n / 2) fun k ↦ play alice bazza k
    else bazza (n / 2) fun k ↦ play alice bazza k

/-
The predicate saying that `n` move in the sequence `xs 0, xs 1, ...` is valid.
For even values of `n`, it checks that `∑ k ≤ n, xs k ≤ lam * (n + 1)`.
For odd values of `n`, it checks that `∑ k ≤ n, (xs k) ^ 2 ≤ n + 1`.
-/
def ValidMove (lam : ℝ) (xs : ℕ → NNReal) (n : ℕ) : Prop :=
  if Even n then ∑ k ≤ n, xs k ≤ lam * (n + 1)
  else ∑ k ≤ n, (xs k) ^ 2 ≤ n + 1

/-- The predicate saying that a given Alice's strategy is a winning one. -/
def AliceStrategy.Wins (lam : ℝ) (alice : AliceStrategy) : Prop :=
  ∀ bazza, ∃ n, IsLeast {m | ¬ValidMove lam (play alice bazza) m} n ∧ Odd n

/-- The predicate saying that a given Bazza's strategy is a winning one. -/
def BazzaStrategy.Wins (lam : ℝ) (bazza : BazzaStrategy) : Prop :=
  ∀ alice, ∃ n, IsLeast {m | ¬ValidMove lam (play alice bazza) m} n ∧ Even n

/-
For a sequence of moves $x_1, x_2, \dots$ in the inekoalaty game, we define the partial sum of values $S_n = \sum_{i=1}^n x_i$ and the partial sum of squares $Q_n = \sum_{i=1}^n x_i^2$. We adopt the convention that $S_0=0$ and $Q_0=0$.
-/
def s (xs : ℕ → NNReal) (n : ℕ) : ℝ := ∑ i in Finset.range n, (xs i : ℝ)
def q (xs : ℕ → NNReal) (n : ℕ) : ℝ := ∑ i in Finset.range n, (xs i : ℝ) ^ 2

/-
Bazza's reference strategy is as follows: on his turn $2k$, if he has not already lost (i.e., if $Q_{2k-1} \le 2k$), he chooses $x_{2k} = \sqrt{2k - Q_{2k-1}}$.
-/
def bazzaReferenceStrategy : BazzaStrategy := fun n hist ↦
  let Q_2n_plus_1 := ∑ i, (hist i : ℝ) ^ 2
  let val_sq := (2 * (n + 1) : ℝ) - Q_2n_plus_1
  if h : 0 ≤ val_sq then
    NNReal.sqrt ⟨val_sq, h⟩
  else
    0

/-
Let $f(k) = \frac{k\sqrt{2}}{2k-1}$ for $k \ge 1$.
-/
def f (k : ℕ) : ℝ := (k : ℝ) * Real.sqrt 2 / (2 * (k : ℝ) - 1)

/-
For a given $\lambda > 1/\sqrt{2}$, Alice's reference strategy is as follows: first, choose an integer $K$ according to Lemma~\ref{lem:existence_of_K_for_alice} such that $\lambda > \frac{K\sqrt{2}}{2K-1}$.
Then, for all turns $2k-1$ with $k < K$, Alice chooses $x_{2k-1}=0$. At turn $2K-1$, Alice chooses $x_{2K-1} = \lambda(2K-1) - S_{2K-2}$.
-/
def aliceReferenceStrategy (lam : ℝ) (K : ℕ) : AliceStrategy := fun n hist ↦
  if n + 1 < K then
    0
  else if n + 1 = K then
    let S_2n := ∑ i, (hist i : ℝ)
    let move := lam * (2 * (n + 1) - 1) - S_2n
    if h_nonneg : 0 ≤ move then
      ⟨move, h_nonneg⟩
    else
      0
  else
    0

```

How the parts fit. The proof of `main_theorem` is `constructor` (splitting the
conjunction into the two equalities) followed by one `Set.ext` argument per
equality. Each `Set.ext` turns `{x | P x} = {x | Q x}` into pointwise
membership, then `bound`/`constructor` splits it into the two inclusions. The
lemma graph, parent at the top:

```text
main_theorem
├─ first equality: apply Set.ext; bound
│   ├─ ⊆ (inline, lines 621-684): "Alice wins ⇒ λ > 1/√2", closed through
│   │     lemSLowerBound (called at 674)
│   └─ ⊇ (line 685): "λ > 1/√2 ⇒ Alice wins", handed whole to
│         lemAliceWinsLargeLambda
└─ second equality: apply Set.ext; intro lam; constructor
    ├─ ⊆ (inline, lines 690-725): "Bazza wins ⇒ 0 < λ < 1/√2", closed inline
    │     with no named lemma
    └─ ⊇ (line 726): "0 < λ < 1/√2 ⇒ Bazza wins", handed whole to
          lemBazzaWinsSmallLambda

lemSLowerBound
├─ lemPairSumLowerBound (apply_rules, 187)
└─ lemQ_2k_minus_2_under_bazza_ref (apply, 191) ─ lemBazzaStrategyQValue (150)

lemBazzaWinsSmallLambda
├─ lemQ_2k_minus_2_under_bazza_ref (convert, 250) ─ lemBazzaStrategyQValue (150)
└─ lemSLowerBound (convert, 262 and 291)

lemAliceWinsLargeLambda
├─ lemExistenceOfKForAlice (via `exact?`, 539) ─ lemFLimit (310)
├─ lemBazzaObjectiveUpperBound (have, 584)
└─ lemAliceMoveValid (convert, 600) ─ lemBazzaDefenseSBound (387) ─ lemSBoundByQ (355, via `exact?`)
```

Each of the three children is a good leaf because its statement is
self-contained and its proof closes on its own or from named siblings, never
re-entering the parent:

- `lemSLowerBound` states the estimate `S_{2(k-1)} ≥ (k-1)√2` for Bazza's
  reference play, the fact both inline inclusions need. It closes by building a
  per-pair lower bound with `lemPairSumLowerBound` and
  `lemQ_2k_minus_2_under_bazza_ref`, summing with `Finset.sum_le_sum`, and
  converting the sum back to `s`.
- `lemBazzaWinsSmallLambda` states the half-theorem `∃ bazza,
  BazzaStrategy.Wins lam bazza` and closes by exhibiting `bazzaReferenceStrategy`
  as the winner: a contradiction plus strong induction shows `ValidMove` holds
  forever would force `S ≥ (k-1)√2` on the one hand and `≤ λ(2k-1)` on the
  other, using `lemSLowerBound` and `lemQ_2k_minus_2_under_bazza_ref`.
- `lemAliceWinsLargeLambda` states the dual half-theorem `∃ alice,
  AliceStrategy.Wins lam alice` and closes by exhibiting
  `aliceReferenceStrategy lam K` for a `K` with `λ > f K`; it uses
  `lemBazzaObjectiveUpperBound` and `lemAliceMoveValid`, both stated and proved
  above it in the same file.

The context excerpt (`definitions`, lines 46-114) holds the game's strategy
types, `play`, `ValidMove`, the `Wins` predicates, the partial sums `s`/`q` and
the two reference strategies, so the parent's set comprehensions can be read.

## Why it is good

1. The parent `main_theorem` is declared at `HarmonicLean/IMO2025P5.lean:615-726`
   (check, `declared`).
2. `Set.ext` occurs exactly 2 times in the file — the two extensionality
   arguments, one per set equality (check, `count`; lines 619 and 687).
3. No closing-by-sorry token (`sorry`, `admit`, `axiom`) appears in the file's
   728 lines (check, `no_sorry`); the file ends with `#print axioms
   main_theorem` (line 728) so axiom use is inspectable.
4. The decomposition is theorem scale: 3 direct lemmas, a 112-line glue
   (615-726), child proofs of 32/75/76 lines, and a longest checked chain of 4
   project lemmas below `main_theorem` (`main_theorem` → `lemBazzaWinsSmallLambda`
   → `lemSLowerBound` → `lemQ_2k_minus_2_under_bazza_ref` → `lemBazzaStrategyQValue`)
   (measurement; call sites 726, 262, 191, 150).
5. The authors recorded the answer and named the structure in comments: the
   header ends "Answer: Alice wins if λ > 1/√2. Bazza wins if 0 < λ < 1/√2"
   (line 13), and the glue labels the two inclusions ("By definition of Alice's
   winning strategy, …", line 622; "To prove the equality, we show mutual
   inclusion.", line 686) (author-statement).

In my opinion the detail worth copying is that the expensive direction of each
equality is *not* a named child but an inline proof, while only the "easy"
direction is a half-theorem; the half-theorems (`lemAliceWinsLargeLambda`,
`lemBazzaWinsSmallLambda`) each bundle a whole reference-strategy construction,
so the parent never has to unfold it.

## When to use it, and when not

Use it when the goal is a set (or function) equality whose two inclusions are
genuinely different and each already has a proof: a named half-theorem for one
direction, a short inline argument for the other. `Set.ext` (or `ext`/`funext`,
or `subset_antisym`/`set_eqI` in Isabelle) is the right glue when the answer to
"when does P hold?" is a single threshold or condition, so each side of the
equality is a comprehension over the same variable.

Avoid it when the two inclusions are the same argument in mirror image (then
one lemma plus symmetry suffices and the ext split is ceremony); when the set
comprehension must be unfolded by a non-definitional rewrite to even state an
inclusion; or when the equality is not of sets/functions, so extensionality
does not apply. Also avoid handing an inclusion to a half-theorem whose
conclusion does not match the comprehension up to definitional equality, since
the `exact ⟨…, lemma lam h⟩` step will not close.

## Consequences

Each `Set.ext` leaves a pointwise membership goal that must then be split into
the two inclusions; the initial `constructor` first splits the conjunction, so
the whole proof is two ext arguments (four inclusions total). The inclusion not
handed to a half-theorem is the real cost: the Alice-wins ⊆ direction is a
64-line inline argument (621-684), the only place the glue proves a nontrivial
fact itself, closing through `lemSLowerBound` at 674. The "hand the whole
inclusion to a half-theorem" step requires the half-theorem's conclusion to
match the inclusion's consequent up to definitional equality; if a child's
statement diverges from the parent's set comprehension, the step fails and the
inclusion must be reopened. Failure mode: `Set.ext` on a goal that is not an
extensional equality produces no inclusion to hand off, and the whole
pointwise argument falls back onto the glue.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/lean_action_ci.yml runs leanprover/lean-action@v1 (lake build of default target HarmonicLean, which imports HarmonicLean.IMO2025P5); commit 72b62405a176a7eaeadb335a7fa6ee80b6667161 is HEAD of default branch main (compare main...72b62405 = identical) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: lemSLowerBound@HarmonicLean/IMO2025P5.lean:674, lemBazzaWinsSmallLambda@HarmonicLean/IMO2025P5.lean:726, lemAliceWinsLargeLambda@HarmonicLean/IMO2025P5.lean:685; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 72b62405a176a7eaeadb335a7fa6ee80b6667161 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(main_theorem, HarmonicLean/IMO2025P5.lean, 615-726) -> declared: main_theorem is declared at HarmonicLean/IMO2025P5.lean:615 | check_claims.py |
| 2 | verified | count(Set.ext, 2, HarmonicLean/IMO2025P5.lean) -> count: Set.ext occurs 2 times in 1 file(s) matching HarmonicLean/IMO2025P5.lean | check_claims.py |
| 3 | verified | no_sorry(HarmonicLean/IMO2025P5.lean, 1-728) -> no_sorry: none of sorry, admit, axiom in HarmonicLean/IMO2025P5.lean:1-728 | check_claims.py |
| 4 | verified | read copied file: line counts 615-726=112, 181-212=32, 229-303=75, 535-610=76; call sites grep-confirmed: 726 'lemBazzaWinsSmallLambda lam h', 262 'lemSLowerBound lam alice (k+1)', 191 'lemQ_2k_minus_2_under_bazza_ref', 150 'lemBazzaStrategyQValue k'; lemBazzaStrategyQValue body (118-123) is unfold+aesop, no project-lemma calls -> leaf, so chain depth 4 | verifier |
| 5 | verified | read copied file: line 13 ends 'Answer: Alice wins if lambda > 1 / sqrt 2. Bazza wins if 0 < lambda < 1 / sqrt 2.'; line 622 comment labels first inclusion (x must be greater than 1/sqrt(2)); line 686 comment 'To prove the equality, we show mutual inclusion.' | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Correctness lens verified against the copied file (byte-identical at 72b62405a176, provenance pass). Parent main_theorem declared at 615-726; statement matches entry.json. The three children (lemSLowerBound 181-212, lemBazzaWinsSmallLambda 229-303, lemAliceWinsLargeLambda 535-610) have statements matching entry.json, and are exactly the three named lemmas the parent cites (lemSLowerBound@674, lemAliceWinsLargeLambda@685, lemBazzaWinsSmallLambda@726; no other named lemma in the glue). Closing methods match: lemSLowerBound via lemPairSumLowerBound(187)+lemQ_2k_minus_2_under_bazza_ref(191); lemBazzaWinsSmallLambda via lemQ_2k_minus_2_under_bazza_ref(250)+lemSLowerBound(262,291); lemAliceWinsLargeLambda via lemExistenceOfKForAlice(539)+lemBazzaObjectiveUpperBound(584)+lemAliceMoveValid(600). It closes: no sorry/admit/axiom tokens (only '#print axioms main_theorem'@728). Shape numbers correct: glue_lines 112 (726-615+1), child_lines [32,75,76] (212-181+1, 303-229+1, 610-535+1), direct_lemmas 3, depth 4 (main_theorem -> lemBazzaWinsSmallLambda -> lemSLowerBound -> lemQ_2k_minus_2_under_bazza_ref(191) -> lemBazzaStrategyQValue(150); Alice side equally 4 via lemSBoundByQ(355) leaf). | reviewer-correctness |
| generality | accept | Move is stated generally: use_when/When-to-use generalises from this IMO answer to any set-or-function equality whose two inclusions are genuinely different, with cross-language names (Set.ext/ext/funext, Isabelle subset_antisym/set_eqI, Rocq apply setP) — all accurate equivalents, no overreach. When-not-to-use is specific and honest: symmetry-when-mirror-image, non-definitional unfold, not-a-set/function equality, and (README) a half-theorem whose conclusion fails definitional matching so the exact <...> hand-off step will not close. Consequences are specific (64-line inline ⊆ at 621-684, only nontrivial glue fact, closes through lemSLowerBound at 674; definitional-matching requirement; failure mode of Set.ext on a non-extensional goal), verified against the copied file. It does say what makes the leaves good for a bounded prover: each child is a self-contained statement whose proof closes on its own or from named siblings, never re-entering the parent, with per-child descriptions. Cites I spot-checked (lines 13, 619, 622, 674, 685-687, 726) match the copied file. | reviewer-generality |
| provenance-licence | accept | check_provenance passes (1 file byte-identical at 72b62405a176a7eaeadb335a7fa6ee80b6667161). Commit is consistent: README '72b62405a176' is a prefix of the full hash in entry.json and SOURCE.md. Licence 'LicenseRef-unknown' is recorded identically in README, entry.json, and SOURCE.md; SOURCE.md records no licence file at root plus attribution. Permalinks use the full pinned commit and resolve; cited line ranges verified against the local copy (parent 615-726, children 181-212/229-303/535-610, context 46-114; Set.ext at 619/687; header answer at 13; file is 728 lines). | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/harmonic-ai/IMO2025 at commit `72b62405a176a7eaeadb335a7fa6ee80b6667161`, under `LicenseRef-unknown`; see the [source note](../../sources/harmonic-imo2025/SOURCE.md) for the licence text and attribution.
