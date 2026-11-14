# Strengthen sum mu(n)/n = o(1) to a K-parameterised O(x/K) bound (mu_pnt_alt)

| | |
|---|---|
| Kind | instance |
| Move | suffices-or-strengthen |
| Language | lean |
| Status | accepted |
| Source | [pnt-and](../../sources/pnt-and/SOURCE.md) at `2c476fa6441c` |
| Licence | `Apache-2.0` |

## Intent

The alternate Möbius form of the prime number theorem — the partial sum of
`μ(n)/n` up to `x` is `o(1)` — is not attacked directly. The glue first
*strengthens* the quantity into a bound that is uniform in a free parameter
`K`: `h_bound` bounds `|S(x/K)|` by `1/K + 1/x + (tail)/x` for every `K > 0`
and `x ≥ 1`, where `S(y)` is the partial sum of `μ(n)/n`. The tail is then
killed by a little-o estimate, and the proof finishes by choosing `K` with
`1/K < ε/3` and letting `x → ∞`. This is the "it suffices to show `O(x/N)`"
reduction of the blueprint node, carried out in Lean.

## The decomposition

### context `mu_pnt_alt_blueprint`: [`PrimeNumberTheoremAnd/Consequences.lean` lines 2377-2403](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/Consequences.lean#L2377-L2403) ([local copy](code/PrimeNumberTheoremAnd/Consequences.lean))

```lean
@[blueprint
  "mu-pnt-alt"
  (title := "Alternate M\\\"obius form of prime number theorem")
  (statement := /-- We have $\sum_{n \leq x} \mu(n)/n = o(1)$. -/)
  (proof := /--
  As in the proof of Theorem \ref{mun}, we have
    $$ 1 = \sum_{d \leq x} \mu(d) \lfloor \frac{x}{d} \rfloor$$
    $$ = x \sum_{d \leq x} \frac{\mu(d)}{d} - \sum_{d \leq x} \mu(d) \{ \frac{x}{d} \}$$
  so it will suffice to show that
  $$ \sum_{d \leq x} \mu(d) \{ \frac{x}{d} \} = o(x).$$
  Let $N$  be a natural number.  It suffices to show that
  $$ \sum_{d \leq x} \mu(d) \{ \frac{x}{d} \} = O(x/N).$$
  if $x$ is large enough depending on $N$.
  We can split the left-hand side as the sum of
  $$ \sum_{d \leq x/N} \mu(d) \{ \frac{x}{d} \} $$
  and
  $$ \sum_{j=1}^{N-1} \sum_{x/(j+1) < d \leq x/j} \mu(d) (x/d - j).$$
  The first term is clearly $O(x/N)$.  For the second term, we can use Theorem \ref{mu-pnt}
  and summation by parts (using the fact that $x/d-j$ is monotone and bounded) to find that
  $$ \sum_{x/(j+1) < d \leq x/j} \mu(d) (x/d - j) = o(x)$$
  for any given $j$, so in particular
  $$ \sum_{x/(j+1) < d \leq x/j} \mu(d) (x/d - j) = O(x/N^2)$$
  for all $j=1,\dots,N-1$ if $x$ is large enough depending on $N$.
  Summing all the bounds, we obtain the claim.
  -/)
  (proofUses := ["mu-pnt"])
  (latexEnv := "proposition")]
```

### parent `mu_pnt_alt`: [`PrimeNumberTheoremAnd/Consequences.lean` lines 2404-2435](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/Consequences.lean#L2404-L2435) ([local copy](code/PrimeNumberTheoremAnd/Consequences.lean))

```lean
theorem mu_pnt_alt : (fun x : ℝ ↦ ∑ n ∈ range ⌊x⌋₊, (μ n : ℝ) / n) =o[atTop] fun _ ↦ (1 : ℝ) := by
  rw [Asymptotics.isLittleO_iff_tendsto'] <;> norm_num
  have h_sum_zero : Filter.Tendsto (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ) / n) Filter.atTop (nhds 0) := by
    set S : ℝ → ℝ := fun y => ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (μ n : ℝ) / n
    have h_bound : ∀ K : ℕ, 0 < K → ∀ x : ℝ, 1 ≤ x → |S (x / K)| ≤ 1 / K + 1 / x + |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| / x := by
      intros K hK x hx
      have h_approx : |x * S (x / K) - 1| ≤ x / K + |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| := by
        convert sum_mobius_div_approx x K hK hx using 1
      rw [abs_le] at *
      ring_nf at *
      constructor <;> nlinarith [inv_pos.2 (by positivity : 0 < x), mul_inv_cancel₀ (by positivity : x ≠ 0), abs_nonneg (∑ n ∈ Finset.Ioc ⌊ (K : ℝ) ⁻¹ * x⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x * (n : ℝ) ⁻¹⌋)]
    have h_tail_zero : ∀ K : ℕ, 0 < K → Filter.Tendsto (fun x : ℝ => |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| / x) Filter.atTop (nhds 0) := by
      intro K hK
      have h_tail_zero : Filter.Tendsto (fun x : ℝ => |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| / x) Filter.atTop (nhds 0) := by
        have := sum_mobius_floor_tail_isLittleO K hK
        rw [Asymptotics.isLittleO_iff_tendsto'] at this
        · simpa [abs_div] using this.abs.congr' (by filter_upwards [Filter.eventually_gt_atTop 0] with x hx using by rw [abs_div, abs_of_nonneg hx.le])
        · filter_upwards [Filter.eventually_gt_atTop 0] with x hx hx' using absurd hx' hx.ne'
      convert h_tail_zero using 1
    have h_eps : ∀ ϵ > 0, ∃ Y : ℝ, ∀ y ≥ Y, |S y| < ϵ := by
      intros ϵ hϵ_pos
      obtain ⟨K, hK_pos, hK⟩ : ∃ K : ℕ, 0 < K ∧ 1 / (K : ℝ) < ϵ / 3 := by
        exact ⟨⌊ϵ⁻¹ * 3⌋₊ + 1, Nat.succ_pos _, by rw [div_lt_iff₀] <;> push_cast <;> nlinarith [Nat.lt_floor_add_one (ϵ⁻¹ * 3), mul_inv_cancel₀ hϵ_pos.ne']⟩
      obtain ⟨Y, hY⟩ : ∃ Y : ℝ, ∀ x ≥ Y, |S (x / K)| < ϵ := by
        have h_tail_zero : Filter.Tendsto (fun x : ℝ => 1 / (K : ℝ) + 1 / x + |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| / x) Filter.atTop (nhds (1 / (K : ℝ))) := by
          simpa using Filter.Tendsto.add (tendsto_const_nhds.add (tendsto_inv_atTop_zero)) (h_tail_zero K hK_pos)
        exact Filter.eventually_atTop.mp (h_tail_zero.eventually (gt_mem_nhds <| by linarith)) |> fun ⟨Y, hY⟩ ↦ ⟨Max.max Y 1, fun x hx ↦ lt_of_le_of_lt (h_bound K hK_pos x <| le_trans (le_max_right _ _) hx) <| hY x <| le_trans (le_max_left _ _) hx⟩
      use Y / K; intros y hy; specialize hY (y * K) (by nlinarith [show (K : ℝ) ≥ 1 by norm_cast, div_mul_cancel₀ Y (by positivity : (K : ℝ) ≠ 0)]) ; simp_all +decide [ne_of_gt]
    exact Metric.tendsto_atTop.mpr fun ε hε => by simpa using h_eps ε hε
  have h_sum_zero : Filter.Tendsto (fun x : ℝ => ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (μ n : ℝ) / n) Filter.atTop (nhds 0) := by
    convert h_sum_zero using 2 ; erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num [Finset.sum_range_succ']
  simpa [Finset.sum_range_succ] using h_sum_zero.sub (show Filter.Tendsto (fun x : ℝ => (μ ⌊x⌋₊ : ℝ) / ⌊x⌋₊) Filter.atTop (nhds 0) from tendsto_zero_iff_norm_tendsto_zero.mpr <| squeeze_zero (fun _ => by positivity) (fun x => by simpa using div_le_div_of_nonneg_right (show |(μ ⌊x⌋₊ : ℝ)| ≤ 1 from mod_cast by { unfold ArithmeticFunction.moebius; aesop }) <| Nat.cast_nonneg _) <| tendsto_inv_atTop_zero.comp <| tendsto_natCast_atTop_atTop.comp <| tendsto_nat_floor_atTop)
```

### child `sum_mobius_floor_tail_isLittleO`: [`PrimeNumberTheoremAnd/Consequences.lean` lines 2270-2355](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/Consequences.lean#L2270-L2355) ([local copy](code/PrimeNumberTheoremAnd/Consequences.lean))

```lean
lemma sum_mobius_floor_tail_isLittleO (K : ℕ) (hK : 0 < K) :
    (fun x : ℝ => ∑ n ∈ Finset.Ioc ⌊x/K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)) =o[atTop] fun x => x := by
      have h_group : ∀ x : ℝ, x ≥ 1 → ∑ n ∈ Finset.Ioc ⌊x / (K : ℝ)⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x / n⌋ = ∑ k ∈ Finset.Ico 1 K, k * (∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) := by
        intro x hx
        have h_group : ∑ n ∈ Finset.Ioc ⌊x / (K : ℝ)⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x / n⌋ = ∑ k ∈ Finset.Ico 1 K, ∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ) * k := by
          have h_group : Finset.Ioc ⌊x / (K : ℝ)⌋₊ ⌊x⌋₊ = Finset.biUnion (Finset.Ico 1 K) (fun k => Finset.Ioc (⌊x / (k + 1 : ℝ)⌋₊) (⌊x / (k : ℝ)⌋₊)) := by
            ext n
            simp only [mem_Ioc, mem_biUnion, mem_Ico]
            constructor
            · intro hn
              refine ⟨⌊x / n⌋₊, ?_, ?_, ?_⟩
              all_goals generalize_proofs at *
              · rw [Nat.floor_lt', div_lt_iff₀] <;> norm_num <;> try linarith [show (n : ℝ) ≥ 1 by norm_cast; linarith]
                exact ⟨by rw [le_div_iff₀ (Nat.cast_pos.mpr <| by linarith)] ; nlinarith [Nat.floor_le (show 0 ≤ x by linarith), Nat.lt_floor_add_one x, show (n : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast hn.2], by rw [Nat.floor_lt (by positivity)] at *; rw [div_lt_iff₀ (by positivity)] at *; norm_num at *; linarith⟩
              · rw [Nat.floor_lt', div_lt_iff₀] <;> norm_num <;> try linarith [Nat.lt_floor_add_one (x / n)]
                nlinarith [Nat.lt_floor_add_one (x / n), show (n : ℝ) ≥ 1 by norm_cast; linarith, div_mul_cancel₀ x (show (n : ℝ) ≠ 0 by norm_cast; linarith)]
              · refine Nat.le_floor ?_
                rw [le_div_iff₀] <;> norm_num
                · exact le_trans (mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (Nat.cast_nonneg _)) (by rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr <| by linarith)])
                · exact Nat.floor_pos.mpr (by rw [le_div_iff₀ (Nat.cast_pos.mpr <| pos_of_gt hn.1)] ; nlinarith [Nat.floor_le (show 0 ≤ x by positivity), Nat.lt_floor_add_one x, show (n : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast hn.2, div_mul_cancel₀ x (show (K : ℝ) ≠ 0 by positivity)])
            · field_simp
              rintro ⟨a, ⟨ha₁, ha₂⟩, ha₃, ha₄⟩
              refine ⟨lt_of_le_of_lt ?_ ha₃, ha₄.trans ?_⟩
              · gcongr ; norm_cast
              · exact Nat.floor_mono <| div_le_self (by positivity) <| mod_cast ha₁
          rw [h_group, Finset.sum_biUnion]
          · refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun n hn => ?_
            simp +zetaDelta only [ge_iff_le, mem_Ico, mem_Ioc, mul_eq_mul_left_iff, Int.cast_eq_zero] at *
            rw [Nat.floor_lt (by positivity), Nat.le_floor_iff (by positivity)] at *
            exact Or.inl <| mod_cast Int.floor_eq_iff.mpr ⟨by rw [le_div_iff₀ <| Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by rintro rfl; norm_num at hn; linarith [show x / (k + 1 : ℝ) > 0 by positivity]] ; norm_num; nlinarith [show (k : ℝ) ≥ 1 by norm_cast; linarith, div_mul_cancel₀ x (show (k : ℝ) ≠ 0 by norm_cast; linarith), div_mul_cancel₀ x (show (k + 1 : ℝ) ≠ 0 by positivity)], by rw [div_lt_iff₀ <| Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by rintro rfl; norm_num at hn; linarith [show x / (k + 1 : ℝ) > 0 by positivity]] ; norm_num; nlinarith [show (k : ℝ) ≥ 1 by norm_cast; linarith, div_mul_cancel₀ x (show (k : ℝ) ≠ 0 by norm_cast; linarith), div_mul_cancel₀ x (show (k + 1 : ℝ) ≠ 0 by positivity)]⟩
          · intros k hk l hl hkl; simp_all +decide [Finset.disjoint_left]
            field_simp
            intro a ha₁ ha₂ ha₃; contrapose! hkl
            rw [Nat.le_floor_iff (by positivity), Nat.floor_lt (by positivity)] at *
            rw [div_lt_iff₀ (by positivity), le_div_iff₀ (by norm_cast; linarith)] at *
            exact Nat.le_antisymm (Nat.le_of_lt_succ <| by { rw [← @Nat.cast_lt ℝ] ; push_cast; nlinarith }) (Nat.le_of_lt_succ <| by { rw [← @Nat.cast_lt ℝ] ; push_cast; nlinarith })
        simpa only [mul_comm, Finset.mul_sum _ _ _] using h_group
      have h_M_x_over_k : ∀ k : ℕ, 1 ≤ k → k < K → (fun x : ℝ => ∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) =o[atTop] (fun x => x) := by
        have h_M : (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ)) =o[atTop] (fun x => x) := by
          have h_M : (fun x : ℝ => ∑ n ∈ Finset.range ⌊x⌋₊, (μ n : ℝ)) =o[atTop] (fun x => x) := by
            refine Asymptotics.IsLittleO.of_norm_left ?_
            simpa only [← Int.norm_cast_real, Int.cast_sum] using mu_pnt.norm_left
          have h_M : (fun x : ℝ => ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (μ n : ℝ)) =o[atTop] (fun x => x) := by
            simp_all +decide only [ge_iff_le, Finset.sum_range_succ]
            refine h_M.add ?_
            rw [Asymptotics.isLittleO_iff_tendsto] <;> norm_num
            refine squeeze_zero_norm' (a := fun x : ℝ => 1 / |x|) ?_ ?_
            · norm_num [abs_div]
              exact ⟨1, fun x hx => mul_le_of_le_one_left (by positivity) (mod_cast by exact abs_moebius_le_one)⟩
            · exact tendsto_const_nhds.div_atTop (tendsto_norm_atTop_atTop)
          convert! h_M.sub (show (fun x : ℝ => (μ 0 : ℝ)) =o[Filter.atTop] fun x : ℝ => x from ?_) using 2 <;> norm_num [Finset.sum_range_succ']
          erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num [Finset.sum_range_succ']
        intros k hk_pos hk_lt_K
        have h_M_x_over_k : (fun x : ℝ => ∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) = (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) - (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x / (k + 1 : ℝ)⌋₊, (μ n : ℝ)) := by
          ext x
          simp only [Pi.sub_apply]
          rw [eq_sub_iff_add_eq']
          simp only [show Finset.Icc (1 : ℕ) (⌊x / (↑k + 1)⌋₊) = Finset.Ioc (0 : ℕ) (⌊x / (↑k + 1)⌋₊) by
              simpa using (Finset.Icc_add_one_left_eq_Ioc (a := (0 : ℕ)) (b := ⌊x / (↑k + 1)⌋₊)),
            show Finset.Icc (1 : ℕ) (⌊x / ↑k⌋₊) = Finset.Ioc (0 : ℕ) (⌊x / ↑k⌋₊) by
              simpa using (Finset.Icc_add_one_left_eq_Ioc (a := (0 : ℕ)) (b := ⌊x / ↑k⌋₊))]
          rw [Finset.sum_Ioc_consecutive] <;> norm_num

          by_cases hx : 0 ≤ x <;> simp_all +decide only [ge_iff_le, floor_div_natCast, not_le]
          · rw [Nat.le_div_iff_mul_le (by positivity)]
            exact Nat.le_floor <| by push_cast; nlinarith [Nat.floor_le (show 0 ≤ x / (k + 1) by positivity), Nat.lt_floor_add_one (x / (k + 1)), mul_div_cancel₀ x (by positivity : (k + 1 : ℝ) ≠ 0)]
          · rw [Nat.floor_of_nonpos (div_nonpos_of_nonpos_of_nonneg hx.le (by positivity)), Nat.floor_of_nonpos hx.le] ; norm_num
        rw [h_M_x_over_k]
        refine Asymptotics.IsLittleO.sub ?_ ?_
        · field_simp
          refine h_M.comp_tendsto (Filter.tendsto_id.atTop_mul_const (by positivity)) |> fun h => h.trans_isBigO ?_
          exact Asymptotics.isBigO_iff.mpr ⟨(k : ℝ) ⁻¹, Filter.eventually_atTop.mpr ⟨1, fun x hx => by simp +decide ; ring_nf; norm_num [show k ≠ 0 by linarith]⟩⟩
        · have := h_M.comp_tendsto (show Filter.Tendsto (fun x : ℝ => x / (k + 1)) Filter.atTop Filter.atTop from Filter.tendsto_id.atTop_div_const (by positivity))
          rw [Asymptotics.isLittleO_iff] at *
          intro c hc; filter_upwards [this (show 0 < c * (k + 1) by positivity), Filter.eventually_gt_atTop 0] with x hx₁ hx₂; simp_all +decide only [ge_iff_le, norm_eq_abs, eventually_atTop, Function.comp_apply, norm_div, cast_nonneg,
    zero_le_one, add_nonneg, abs_of_nonneg]
          exact hx₁.trans (by rw [mul_assoc, mul_div_cancel₀ _ (by positivity)])
      have h_sum_o_x : (fun x : ℝ => ∑ k ∈ Finset.Ico 1 K, (k : ℝ) * (∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ))) =o[atTop] (fun x => x) := by
        rw [Asymptotics.isLittleO_iff_tendsto']
        · have h_sum_little_o : ∀ k ∈ Finset.Ico 1 K, Filter.Tendsto (fun x : ℝ => (∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) / x) Filter.atTop (nhds 0) := by
            intro k hk; specialize h_M_x_over_k k (Finset.mem_Ico.mp hk |>.1) (Finset.mem_Ico.mp hk |>.2) ; rw [Asymptotics.isLittleO_iff_tendsto'] at h_M_x_over_k <;> aesop
          simpa [Finset.sum_div _ _ _, mul_div_assoc] using tendsto_finsetSum _ fun k hk => h_sum_little_o k hk |> Filter.Tendsto.const_mul _
        · filter_upwards [Filter.eventually_gt_atTop 0] with x hx hx' using absurd hx' hx.ne'
      exact h_sum_o_x.congr'
        (by filter_upwards [Filter.eventually_ge_atTop 1] with x hx using by rw [h_group x hx])
        (by norm_num)
```

### child `sum_mobius_div_approx`: [`PrimeNumberTheoremAnd/Consequences.lean` lines 2358-2373](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/Consequences.lean#L2358-L2373) ([local copy](code/PrimeNumberTheoremAnd/Consequences.lean))

```lean
lemma sum_mobius_div_approx (x : ℝ) (K : ℕ) (hK : 0 < K) (hx : 1 ≤ x) :
  |x * (∑ n ∈ Icc 1 ⌊x/K⌋₊, (μ n : ℝ) / n) - 1| ≤ x/K + |∑ n ∈ Ioc ⌊x/K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| := by
    have h_split : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋ = (∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋) + (∑ n ∈ Finset.Ioc ⌊x / (K : ℝ)⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋) := by
      erw [Finset.sum_Ioc_consecutive] <;> norm_num
      · rfl
      · exact Nat.floor_mono <| div_le_self (by positivity) <| mod_cast hK
    have h_floor : ∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋ = x * ∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) / (n : ℝ) - ∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) * (x / (n : ℝ) - ⌊x / (n : ℝ)⌋) := by
      rw [Finset.mul_sum _ _ _] ; rw [← Finset.sum_sub_distrib] ; exact Finset.sum_congr rfl fun _ _ => by ring
    have h_bound : |∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) * (x / (n : ℝ) - ⌊x / (n : ℝ)⌋)| ≤ ⌊x / (K : ℝ)⌋₊ := by
      have h_bound : ∀ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, |(μ n : ℝ) * (x / (n : ℝ) - ⌊x / (n : ℝ)⌋)| ≤ 1 := by
        norm_num [abs_mul]
        exact fun n hn₁ hn₂ => (mul_le_of_le_one_left (abs_nonneg _) (mod_cast by exact abs_moebius_le_one)).trans (abs_le.mpr ⟨by linarith [Int.fract_nonneg (x / n)], by linarith [Int.fract_lt_one (x / n)]⟩)
      exact le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum h_bound) (by norm_num))
    have h_sum_floor : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋ = 1 := by
      convert sum_mobius_floor x hx using 1
    cases abs_cases (x * ∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ) ⌋₊, (μ n : ℝ) / n - 1) <;> cases abs_cases (∑ n ∈ Finset.Ioc ⌊x / (K : ℝ) ⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ) ⌋) <;> linarith [abs_le.mp h_bound, Nat.floor_le (show 0 ≤ x / (K : ℝ) by positivity), Nat.lt_floor_add_one (x / (K : ℝ))]
```

### How the parts fit

```
mu_pnt_alt                                   (parent, 2404-2435, the glue)
├─ cites sum_mobius_div_approx               (child, 2358-2373)
│     └─ cites sum_mobius_floor              (2260)  ── cites sum_mobius_mul_floor  (1653, leaf)
└─ cites sum_mobius_floor_tail_isLittleO     (child, 2270-2355)
      └─ cites mu_pnt                        (1959, the main PNT, a sibling node)
```

The glue `mu_pnt_alt` reduces its goal to two obligations, one per child:

- **The head (the parameterised bound).** `h_bound` needs `|x·S(x/K) − 1| ≤ x/K + (tail)`, and the glue gets it from
  `sum_mobius_div_approx` (line 2411, `convert sum_mobius_div_approx x K hK hx using 1`). That child is the
  *strengthening*: it splits the full identity `∑_{n≤x} μ(n)⌊x/n⌋ = 1` at `n = ⌊x/K⌋` and turns the head into
  `x·S(x/K)` plus a fractional-part error bounded by `⌊x/K⌋`. Its proof closes by Finset algebra plus one
  named sibling (`sum_mobius_floor`) and a final case split on the absolute values closed by `linarith`.
- **The tail (the little-o).** `h_tail_zero` needs the tail over `(⌊x/K⌋, ⌊x⌋]` to be `o(x)`, and the glue gets it
  from `sum_mobius_floor_tail_isLittleO` (line 2418, `have := sum_mobius_floor_tail_isLittleO K hK`). That child
  partitions the interval into `K−1` slabs, shows each slab's Möbius sum is `o(x)` by `mu_pnt` (the full PNT), and
  closes by `h_sum_o_x.congr'`.

Why each child is a good leaf: each has a self-contained statement — one a pure inequality with a free `K`, the
other a pure little-o — and each closes either on its own (Finset/`linarith` algebra) or from a named sibling already
proved in the same file (`sum_mobius_floor` → `sum_mobius_mul_floor`; `mu_pnt`), so the glue needs to know nothing
about *how* they are proved, only their statements.

## Why it is good

1. **No hole closes the decomposition.** There is no `sorry`, `admit` or `axiom` anywhere in the glue or either
   child (lines 2270-2435 of `PrimeNumberTheoremAnd/Consequences.lean`) — a machine check (`no_sorry`, claim 1).
2. **The glue cites both children.** `sum_mobius_div_approx` and `sum_mobius_floor_tail_isLittleO` each occur in the
   parent site (claims 2 and 3, `cites`).
3. **The glue is short relative to what it joins.** The parent is 32 lines, while the two lemmas it combines are 86 and
   16 lines (claim 4, `measurement`): the argument's weight sits in the leaves, not in the assembly.
4. **The authors say the move in their own words.** The `@[blueprint]` node above the theorem states the plan: "It
   suffices to show that `∑_{d≤x} μ(d){x/d} = O(x/N)` if `x` is large enough depending on `N`" (claim 5,
   `author-statement`, lines 2387-2389).

In my opinion the detail worth copying is that the free parameter `K` is introduced *before* the limit in `x` is
taken: `h_bound` holds for all `K` and all `x ≥ 1` at once, which is what lets the proof pick `K` from `ε` afterwards.
A bound that fixed `K` first would not close.

Against the candidate rules of survey F §10, this is the `suffices` half of `suffices-or-strengthen`: the target is
reduced to a *sufficient stronger* statement rather than split into premises, so it maps to rule 8 (backward rule,
`suffices`, and witnesses as templates). That support is for the `suffices` component only — rule 8's emphasis is on
backward-premise templates, whereas this reduction is a strengthening, which survey F §8 lists as a separate
"generalise / strengthen" free move rather than as a §10 rule.

## When to use it, and when not

Use it when the target is a little-o / limit statement `F(x) =o[atTop] g(x)` about a partial sum, and that partial
sum `S` has (i) an exact identity on the full sum and (ii) a tail estimate, so that `S(x/K)` can be bounded by an
expression `a(K) + b(x) + tail(x)/x` where `a(K) → 0` as `K → ∞`, `b(x) → 0` as `x → ∞` and `tail(x) = o(x)`. The
move is exactly "prove a stronger statement first": the parameterised bound is stronger (it holds uniformly in `K`
and `x`) and more convenient (the two limits are taken in turn).

Avoid it when there is no clean split identity to separate the head from the tail, when the tail does not shrink as
`K` grows, or when the strengthened uniform bound needs the very theorem being proved (circularity). It is also
overkill when a direct partial-summation argument is shorter than the parameterised one.

## Consequences

The move introduces a free parameter `K` and splits the goal into two obligations: a uniform bound (for all `K > 0`
and all `x ≥ 1`) and a tail limit. `K` must be fixed before the limit in `x` is taken, so the bound must hold
uniformly in `x` for each fixed `K`; the `ε/3` choice of `K` then drives the head below `ε` while the tail and `1/x`
vanish. The main failure mode is a bound that is only *pointwise* in `K` (i.e. proved after `K` is fixed), which
cannot be re-specialised once `K` is chosen from `ε`.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml runs leanprover/lean-action (build-args :blueprint) on push/PR to main; lakefile.toml defaultTargets = [PrimeNumberTheoremAnd], so the library including PrimeNumberTheoremAnd/Consequences.lean is compiled; pinned commit 2c476fa6441c607096d93c8fc7ac0a227a655dae is on default branch main (compare main...2c476fa: ahead_by 0, behind_by 2) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: sum_mobius_floor_tail_isLittleO@PrimeNumberTheoremAnd/Consequences.lean:2418, sum_mobius_div_approx@PrimeNumberTheoremAnd/Consequences.lean:2411; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 2c476fa6441c607096d93c8fc7ac0a227a655dae | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | no_sorry(PrimeNumberTheoremAnd/Consequences.lean, 2270-2435) -> no_sorry: none of sorry, admit, axiom in PrimeNumberTheoremAnd/Consequences.lean:2270-2435 | check_claims.py |
| 2 | verified | cites(parent, sum_mobius_div_approx) -> cites: sum_mobius_div_approx occurs at PrimeNumberTheoremAnd/Consequences.lean:2411 | check_claims.py |
| 3 | verified | cites(parent, sum_mobius_floor_tail_isLittleO) -> cites: sum_mobius_floor_tail_isLittleO occurs at PrimeNumberTheoremAnd/Consequences.lean:2418 | check_claims.py |
| 4 | verified | counted in copied code/PrimeNumberTheoremAnd/Consequences.lean: parent mu_pnt_alt spans 2404-2435 = 32 lines (theorem at 2404, closing simpa at 2435); child sum_mobius_floor_tail_isLittleO spans 2270-2355 = 86 lines (lemma at 2270, closing (by norm_num) at 2355); child sum_mobius_div_approx spans 2358-2373 = 16 lines (lemma at 2358, closing cases/linarith at 2373) | verifier |
| 5 | verified | opened copied code/PrimeNumberTheoremAnd/Consequences.lean L2387-2389 of the @[blueprint "mu-pnt-alt"] proof text: "Let N be a natural number. It suffices to show that [sum_{d<=x} mu(d) {x/d} = O(x/N).] if x is large enough depending on N." — matches the claimed strategy statement verbatim | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent mu_pnt_alt (2404-2435) strengthens the little-o target into h_bound, a bound uniform in K, then closes by epsilon-K; matches the suffices-or-strengthen move and intent. Both children match the copied code: sum_mobius_div_approx (2358-2373) closes by 'cases abs_cases <;> linarith' (matches closed_by), sum_mobius_floor_tail_isLittleO (2270-2355) closes by 'exact h_sum_o_x.congr'' (matches closed_by). The glue cites exactly these two project lemmas (sum_mobius_div_approx@2411, sum_mobius_floor_tail_isLittleO@2418) and no other project lemma, so the children are exactly the lemmas the main proof uses; no sorry/admit/axiom in 2270-2435, so it closes. Shape numbers verified: glue_lines 32 (2404-2435), child_lines [86,16] (2270-2355, 2358-2373), direct_lemmas 2, and depth 3 via chain sum_mobius_div_approx->sum_mobius_floor(2262 cites sum_mobius_mul_floor@1653) all confirmed in the copied file. | reviewer-correctness |
| generality | accept | Move is stated generally (little-o of a partial sum with an exact identity + tail estimate, bounded by a(K)+b(x)+tail(x)/x, free parameter K separating two limits), not just for mu(n)/n; 'when not to use' and consequences are honest and specific (no split identity, circularity, overkill vs direct partial summation; K-before-x ordering, pointwise-in-K failure mode). README 228-231 'Why each child is a good leaf' explicitly says the leaves have self-contained statements and close on their own or from a named sibling, so glue needs only statements. Minor: 'tail does not shrink as K grows' conflates the head 1/K (shrinks in K) with the tail (o(x) in x), but surrounding a(K)/tail(x)=o(x) framing is correct. | reviewer-generality |
| provenance-licence | accept | provenance check passes (Consequences.lean byte-identical at 2c476fa); commit 2c476fa6441c607096d93c8fc7ac0a227a655dae consistent across source.json, SOURCE.md, entry.json and every permalink; licence Apache-2.0 in source.json/entry.json matches upstream-LICENSE (Apache 2.0); copied file sha256 3e5f6ccd... and bytes 139214 match entry.json; cited line ranges verified in copied file (2270/2358 declarations, 2377 blueprint, 2404 parent, 2435 end). Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd at commit `2c476fa6441c607096d93c8fc7ac0a227a655dae`, under `Apache-2.0`; see the [source note](../../sources/pnt-and/SOURCE.md) for the licence text and attribution.
