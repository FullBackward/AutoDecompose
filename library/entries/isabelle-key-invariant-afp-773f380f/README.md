# Strong absolute form of Mertens' First Theorem via a key identity

| | |
|---|---|
| Kind | instance |
| Move | key-invariant |
| Language | isabelle |
| Status | draft |
| Source | [afp](../../sources/afp/SOURCE.md) at `07cd9ca548d1` |
| Licence | `BSD-3-Clause` |
| Licence recorded | 2026-11-14T22:40:52Z |

## Intent

Prove the absolute bound ℳ(n) − ln n ∈ (−1 − 9/π², ln 4] by routing the target
remainder through one key identity ℳ n − ln n = ln (fact n) / n − ln n + r / n −
R / n, so that three already-proved project lemmas bound the three terms on the
right and a single transitivity step closes the interval.

## The decomposition

### parent `mertens_bound_strong`: [`thys/Prime_Number_Theorem/Mertens_Theorems.thy` lines 250-374](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/Prime_Number_Theorem/Mertens_Theorems.thy#L250-L374) ([local copy](code/thys/Prime_Number_Theorem/Mertens_Theorems.thy))

```isabelle
theorem mertens_bound_strong:
  fixes n :: nat assumes n: "n > 0"
  shows   "\<MM> n - ln n \<in> {-1 - 9 / pi\<^sup>2<..ln 4}"
proof (cases "n \<ge> 3")
  case False
  with n consider "n = 1" | "n = 2" by force
  thus ?thesis
  proof cases
    assume [simp]: "n = 1"
    have "-1 + (-9 / pi\<^sup>2) < 0"
      by (intro add_neg_neg divide_neg_pos) auto
    thus ?thesis by simp
  next
    assume [simp]: "n = 2"
    have eq: "\<MM> n - ln n = -ln 2 / 2" by (simp add: eval_\<MM>)
    have "-1 - 9 / pi ^ 2 + ln 2 / 2 \<le> -1 - 9 / 4 ^ 2 + 25 / 36 / 2"
      using pi_less_4 ln2_le_25_over_36
      by (intro diff_mono add_mono divide_left_mono divide_right_mono power_mono) auto
    also have "\<dots> < 0" by simp
    finally have "-ln 2 / 2 > -1 - 9 / pi\<^sup>2" by simp
    moreover {
      have "-ln 2 / 2 \<le> (0::real)" by (intro divide_nonpos_pos) auto
      also have "\<dots> \<le> ln 4" by simp
      finally have "-ln 2 / 2 \<le> ln (4 :: real)" by simp
    }
    ultimately show ?thesis unfolding eq by simp
  qed

next
  case True
  hence n: "n \<ge> 3" by simp
  have finite: "finite {(p, i). prime p \<and> i \<ge> 1 \<and> p ^ i \<le> n}"
  proof (rule finite_subset)
    show "{(p, i). prime p \<and> i \<ge> 1 \<and> p ^ i \<le> n}
            \<subseteq> {..nat \<lfloor>root 1 (real n)\<rfloor>} \<times> {..nat \<lfloor>log 2 (real n)\<rfloor>}"
      using primepows_le_subset[of "real n" 1] n unfolding of_nat_le_iff by auto
  qed auto

  define r where "r = prime_sum_upto (\<lambda>p. ln (real p) * frac (real n / real p)) n"
  define R where "R = (\<Sum>(p,i) | prime p \<and> i > 1 \<and> p ^ i \<le> n. ln (real p) * real (n div (p ^ i)))"
  define R' where "R' = (\<Sum>(p,i) | prime p \<and> i > 1 \<and> p ^ i \<le> n. ln (real p) / p ^ i)"
  have [simp]: "ln (4 :: real) = 2 * ln 2"
    using ln_realpow[of 2 2] by simp
  from pi_less_4 have "ln pi \<le> ln 4" by (subst ln_le_cancel_iff) auto
  also have "\<dots> = 2 * ln 2" by simp
  also have "\<dots> \<le> 2 * (25 / 36)" by (intro mult_left_mono ln2_le_25_over_36) auto
  finally have ln_pi: "ln pi \<le> 25 / 18" by simp
  have "ln 3 \<le> ln (4::nat)" by (subst ln_le_cancel_iff) auto
  also have "\<dots> = 2 * ln 2" by simp
  also have "\<dots> \<le> 2 * (25 / 36)" by (intro mult_left_mono ln2_le_25_over_36) auto
  finally have ln_3: "ln (3::real) \<le> 25 / 18" by simp
  
  have "R / n = (\<Sum>(p,i) | prime p \<and> i > 1 \<and> p ^ i \<le> n. ln (real p) * (real (n div (p ^ i)) / n))"
    by (simp add: R_def sum_divide_distrib field_simps case_prod_unfold)
  also have "\<dots> \<le> (\<Sum>(p,i) | prime p \<and> i > 1 \<and> p ^ i \<le> n. ln (real p) * (1 / p ^ i))"
    unfolding R'_def case_prod_unfold using n
    by (intro sum_mono mult_left_mono) (auto simp: field_simps real_of_nat_div dest: prime_gt_0_nat)
  also have "\<dots> = R'" by (simp add: R'_def)
  also have "R' < 9 / pi\<^sup>2"
    unfolding R'_def using mertens_remainder_aux_bound[of n] by simp
  finally have "R / n < 9 / pi\<^sup>2" .
  moreover have "R \<ge> 0"
    unfolding R_def by (intro sum_nonneg mult_nonneg_nonneg) (auto dest: prime_gt_0_nat)
  ultimately have R_bounds: "R / n \<in> {0..<9 / pi\<^sup>2}" by simp

  have "ln (fact n :: real) \<le> ln (2 * pi * n) / 2 + n * ln n - n + 1 / (12 * n)"
    using ln_fact_bounds(2)[of n] n by simp
  also have "\<dots> / n - ln n = -1 + (ln 2 + ln pi) / (2 * n) + (ln n / n) / 2 + 1 / (12 * real n ^ 2)"
    using n by (simp add: power2_eq_square field_simps ln_mult)
  also have "\<dots> \<le> -1 + (ln 2 + ln pi) / (2 * 3) + (ln 3 / 3) / 2 + 1 / (12 * 3\<^sup>2)"
    using exp_le n pi_gt3
    by (intro add_mono divide_right_mono divide_left_mono mult_mono
              mult_pos_pos ln_x_over_x_mono power_mono) auto
  also have "\<dots> \<le> -1 + (25 / 36 + 25 / 18) / (2 * 3) + (25 / 18 / 3) / 2 + 1 / (12 * 3\<^sup>2)"
    using ln_pi ln2_le_25_over_36 ln_3 by (intro add_mono divide_left_mono divide_right_mono) auto
  also have "\<dots> \<le> 0" by simp
  finally have "ln n - ln (fact n) / n \<ge> 0" using n by (simp add: divide_right_mono)
  have "-ln (fact n) \<le> -ln (2 * pi * n) / 2 - n * ln n + n"
    using ln_fact_bounds(1)[of n] n by simp
  also have "ln n + \<dots> / n = -ln (2 * pi) / (2 * n) - (ln n / n) / 2 + 1"
    using n by (simp add: field_simps ln_mult)
  also have "\<dots> \<le> 0 - 0 + 1"
    using pi_gt3 n by (intro add_mono diff_mono) auto
  finally have upper: "ln n - ln (fact n) / n \<le> 1"
    using n by (simp add: divide_right_mono)
  with \<open>ln n - ln (fact n) / n \<ge> 0\<close> have fact_bounds: "ln n - ln (fact n) / n \<in> {0..1}" by simp

  have "r \<le> prime_sum_upto (\<lambda>p. ln p * 1) n"
    using less_imp_le[OF frac_lt_1] unfolding r_def \<theta>_def prime_sum_upto_def
    by (intro sum_mono mult_left_mono) (auto simp: dest: prime_gt_0_nat)
  also have "\<dots> = \<theta> n" by (simp add: \<theta>_def)
  also have "\<dots> < ln 4 * n" using n by (intro \<theta>_upper_bound) auto
  finally have "r / n < ln 4" using n by (simp add: field_simps)
  moreover have "r \<ge> 0" unfolding r_def prime_sum_upto_def
    by (intro sum_nonneg mult_nonneg_nonneg) (auto dest: prime_gt_0_nat)
  ultimately have r_bounds: "r / n \<in> {0..<ln 4}" by simp

  have "ln (fact n :: real) = sum_upto (\<lambda>k. mangoldt k * real (n div k)) (real n)"
    by (simp add: ln_fact_conv_sum_upto_mangoldt)
  also have "\<dots> = (\<Sum>(p,i) | prime p \<and> i > 0 \<and> real (p ^ i) \<le> real n.
                       ln (real p) * real (n div (p ^ i)))"
    by (intro sum_upto_primepows) (auto simp: mangoldt_non_primepow)
  also have "{(p, i). prime p \<and> i > 0 \<and> real (p ^ i) \<le> real n} =
               {(p, i). prime p \<and> i = 1 \<and> p \<le> n} \<union>
               {(p, i). prime p \<and> i > 1 \<and> (p ^ i) \<le> n}" unfolding of_nat_le_iff
    by (auto simp: not_less le_Suc_eq)
  also have "(\<Sum>(p,i)\<in>\<dots>. ln (real p) * real (n div (p ^ i))) =
               (\<Sum>(p,i) | prime p \<and> i = 1 \<and> p \<le> n. ln (real p) * real (n div (p ^ i))) + R"
    (is "_ = ?S + _")
    by (subst sum.union_disjoint) (auto intro!: finite_subset[OF _ finite] simp: R_def)
  also have "?S = prime_sum_upto (\<lambda>p. ln (real p) * real (n div p)) n"
    unfolding prime_sum_upto_def
    by (intro sum.reindex_bij_witness[of _ "\<lambda>p. (p, 1)" fst]) auto
  also have "\<dots> = prime_sum_upto (\<lambda>p. ln (real p) * real n / real p) n - r"
    unfolding r_def prime_sum_upto_def sum_subtractf[symmetric] using n
    by (intro sum.cong) (auto simp: frac_def real_of_nat_div algebra_simps)
  also have "prime_sum_upto (\<lambda>p. ln (real p) * real n / real p) n = n * \<MM> n"
    by (simp add: primes_M_def sum_distrib_left sum_distrib_right prime_sum_upto_def field_simps)
  finally have "\<MM> n - ln n = ln (fact n) / n - ln n + r / n - R / n"
    using n by (simp add: field_simps)
  hence "ln n - \<MM> n = ln n - ln (fact n) / n - r / n + R / n"
    by simp
  with fact_bounds r_bounds R_bounds show "\<MM> n - ln n \<in> {-1 - 9 / pi\<^sup>2<..ln 4}"
    by simp
qed
```

### child `mertens_remainder_aux_bound`: [`thys/Prime_Number_Theorem/Mertens_Theorems.thy` lines 118-236](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/Prime_Number_Theorem/Mertens_Theorems.thy#L118-L236) ([local copy](code/thys/Prime_Number_Theorem/Mertens_Theorems.thy))

```isabelle
lemma mertens_remainder_aux_bound:
  fixes x :: real
  defines "R \<equiv> (\<Sum>(p,i) | prime p \<and> i > 1 \<and> real (p ^ i) \<le> x. ln (real p) / p ^ i)"
  shows   "R < 9 / pi\<^sup>2"
proof -
  define S' where "S' = {(p, i). prime p \<and> i > 1 \<and> real (p ^ i) \<le> x}"
  define S'' where "S'' = {(p, i). prime p \<and> i > 1 \<and> real (p ^ Suc i) \<le> x}"

  have finite_row: "finite {i. i > 1 \<and> real (p ^ (i + k)) \<le> x}" if p: "prime p" for p k
  proof (rule finite_subset)
    show "{i. i > 1 \<and> real (p ^ (i + k)) \<le> x} \<subseteq> {..nat \<lfloor>x\<rfloor>}"
    proof safe
      fix i assume i: "i > 1" "real (p ^ (i + k)) \<le> x"
      have "i < 2 ^ (i + k)" by (induction i) auto
      also from p have "\<dots> \<le> p ^ (i + k)" by (intro power_mono) (auto dest: prime_gt_1_nat) 
      also have "real \<dots> \<le> x" using i by simp
      finally show "i \<le> nat \<lfloor>x\<rfloor>" by linarith
    qed
  qed auto

  have "S'' \<subseteq> S'" unfolding S''_def S'_def
  proof safe
    fix p i assume pi: "prime p" "real (p ^ Suc i) \<le> x" "i > 1"
    have "real (p ^ i) \<le> real (p ^ Suc i)"
      using pi unfolding of_nat_le_iff by (intro power_increasing) (auto dest: prime_gt_1_nat)
    also have "\<dots> \<le> x" by fact
    finally show "real (p ^ i) \<le> x" .
  qed

  have S'_alt:  "S' = (SIGMA p:{p. prime p \<and> real p \<le> x}. {i. i > 1 \<and> real (p ^ i) \<le> x})"
    unfolding S'_def
  proof safe
    fix p i assume "prime p" "real (p ^ i) \<le> x" "i > 1"
    hence "p ^ 1 \<le> p ^ i"
      by (intro power_increasing) (auto dest: prime_gt_1_nat)
    also have "real \<dots> \<le> x" by fact
    finally show "real p \<le> x" by simp
  qed

  have finite: "finite {p. prime p \<and> real p \<le> x}"
    by (rule finite_subset[OF _ finite_Nats_le_real[of x]]) (auto dest: prime_gt_0_nat)
  have "finite S'" unfolding S'_alt using finite_row[of _ 0]
    by (intro finite_SigmaI finite) auto

  have "R \<le> 3 / 2 * (\<Sum>(p, i) | (p, i) \<in> S' \<and> even i. ln (real p) / real (p ^ i))"
  proof -
    have "R = (\<Sum>y\<in>{0, 1}. \<Sum>z | z \<in> S' \<and> snd z mod 2 = y. ln (real (fst z)) / real (fst z ^ snd z))"
      using \<open>finite S'\<close> by (subst sum.group) (auto simp: case_prod_unfold R_def S'_def)
    also have "\<dots> = (\<Sum>(p,i) | (p, i) \<in> S' \<and> even i. ln (real p) / real (p ^ i)) +
                    (\<Sum>(p,i) | (p, i) \<in> S' \<and> odd i. ln (real p) / real (p ^ i))"
      unfolding even_iff_mod_2_eq_zero odd_iff_mod_2_eq_one by (simp add: case_prod_unfold)
    also have "(\<Sum>(p,i) | (p, i) \<in> S' \<and> odd i. ln (real p) / real (p ^ i)) =
                 (\<Sum>(p,i) | (p, i) \<in> S'' \<and> even i. ln (real p) / real (p ^ Suc i))"
      by (intro sum.reindex_bij_witness[of _ "\<lambda>(p,i). (p, Suc i)" "\<lambda>(p,i). (p, i - 1)"])
         (auto simp: case_prod_unfold S'_def S''_def elim: oddE simp del: power_Suc)
    also have "\<dots> \<le> (\<Sum>(p,i) | (p, i) \<in> S' \<and> even i. ln (real p) / real (p ^ Suc i))"
      using \<open>S'' \<subseteq> S'\<close> unfolding case_prod_unfold
      by (intro sum_mono2 divide_nonneg_pos ln_ge_zero finite_subset[OF _ \<open>finite S'\<close>])
         (auto simp: S'_def S''_def case_prod_unfold dest: prime_gt_0_nat simp del: power_Suc)
    also have "\<dots> \<le> (\<Sum>(p,i) | (p, i) \<in> S' \<and> even i. ln (real p) / real (2 * p ^ i))"
      unfolding case_prod_unfold
      by (intro sum_mono divide_left_mono) (auto simp: S'_def dest!: prime_gt_1_nat)
    also have "\<dots> = (1 / 2) * (\<Sum>(p,i) | (p, i) \<in> S' \<and> even i. ln (real p) / real (p ^ i))"
      by (subst sum_distrib_left) (auto simp: case_prod_unfold)
    also have "(\<Sum>(p,i) | (p, i) \<in> S' \<and> even i. ln (real p) / real (p ^ i)) + \<dots> =
                   3 / 2 * (\<Sum>(p,i) | (p, i) \<in> S' \<and> even i. ln (real p) / real (p ^ i))"
      by simp
    finally show ?thesis by simp
  qed

  also have "(\<Sum>(p,i) | (p, i) \<in> S' \<and> even i. ln (real p) / real (p ^ i)) =
               (\<Sum>p | prime p \<and> real p \<le> x. ln (real p) * 
                 (\<Sum>i | i > 0 \<and> even i \<and> real (p ^ i) \<le> x. (1 / real p) ^ i))"
   unfolding sum_distrib_left
  proof (subst sum.Sigma[OF _ ballI])
    fix p assume p: "p \<in> {p. prime p \<and> real p \<le> x}"
    thus "finite {i. 0 < i \<and> even i \<and> real (p ^ i) \<le> x}"
      by (intro finite_subset[OF _ exponents_le_finite[of p 1 0 x]]) (auto dest: prime_gt_1_nat)
  qed (auto intro!: sum.cong finite_subset[OF _ finite_Nats_le_real[of x]]
            dest: prime_gt_0_nat simp: S'_alt power_divide)
  also have "\<dots> \<le> (\<Sum>p | prime p \<and> real p \<le> x. ln (real p) / (real p ^ 2 - 1))"
  proof (rule sum_mono)
    fix p assume p: "p \<in> {p. prime p \<and> real p \<le> x}"
    have "p > 1" using p by (auto dest: prime_gt_1_nat)
    have "(\<Sum>i | i > 0 \<and> even i \<and> real (p ^ i) \<le> x. (1 / real p) ^ i) =
            (\<Sum>i | real (p ^ (2 * i + 2)) \<le> x. (1 / real p) ^ (2 * i)) / real p ^ 2"
      (is "_ = ?S / _") unfolding sum_divide_distrib
      by (rule sum.reindex_bij_witness[of _ "\<lambda>i. 2 * Suc i" "\<lambda>i. (i - 2) div 2"])
         (insert \<open>p > 1\<close>, auto simp: numeral_3_eq_3 power2_eq_square power_diff
                 algebra_simps elim!: evenE)
    also have "?S = (\<Sum>i | real (p ^ (2 * i + 2)) \<le> x. (1 / real p ^ 2) ^ i)"
      by (subst power_mult) (simp_all add: algebra_simps power_divide)
    also have "\<dots> \<le> (\<Sum>i. (1 / real p ^ 2) ^ i)"
      using exponents_le_finite[of p 2 2 x] \<open>p > 1\<close>
      by (intro sum_le_suminf) (auto simp: summable_geometric_iff)
    also have "\<dots> = real p ^ 2 / (real p ^ 2 - 1)"
      using \<open>p > 1\<close> by (subst suminf_geometric) (auto simp: field_simps)
    also have "\<dots> / real p ^ 2 = 1 / (real p ^ 2 - 1)"
      using \<open>p > 1 \<close> by (simp add: divide_simps)
    finally have "(\<Sum>i | 0 < i \<and> even i \<and> real (p ^ i) \<le> x. (1 / real p) ^ i) \<le>
                     1 / (real p ^ 2 - 1)" (is "?lhs \<le> ?rhs")
      using \<open>p > 1\<close> by (simp add: divide_right_mono)
    thus "ln (real p) * ?lhs \<le> ln (real p) / (real p ^ 2 - 1)"
      using \<open>p > 1\<close> by (simp add: divide_simps)
  qed
  also have "\<dots> = (\<Sum>\<^sub>a p | prime p \<and> real p \<le> x. ln (real p) / (real p ^ 2 - 1))"
    using finite by (intro infsetsum_finite [symmetric]) auto
  also have "\<dots> \<le> (\<Sum>\<^sub>a p | prime p. ln (real p) / (real p ^ 2 - 1))"
    using eval_fds_logderiv_zeta_real[of 2] finite
    by (intro infsetsum_mono_neutral_left divide_nonneg_pos) (auto simp: dest: prime_gt_1_nat)
  also have "\<dots> = -Re (deriv zeta (of_real 2) / zeta (of_real 2))"
    by (subst eval_fds_logderiv_zeta_real) auto
  also have "\<dots> = (-Re (deriv zeta 2)) * (6 / pi\<^sup>2)"
    by (simp add: zeta_even_numeral)
  also have "\<dots> < 1 * (6 / pi\<^sup>2)"
    using deriv_zeta_2_bound by (intro mult_strict_right_mono) auto
  also have "3 / 2 * \<dots> = 9 / pi\<^sup>2" by simp
  finally show ?thesis by simp
qed
```

### child `primepows_le_subset`: [`thys/Prime_Number_Theorem/Prime_Number_Theorem_Library.thy` lines 1226-1245](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/Prime_Number_Theorem/Prime_Number_Theorem_Library.thy#L1226-L1245) ([local copy](code/thys/Prime_Number_Theorem/Prime_Number_Theorem_Library.thy))

```isabelle
lemma primepows_le_subset:
  assumes x: "x > 0" and l: "l > 0"
  shows   "{(p, i). prime p \<and> l \<le> i \<and> real (p ^ i) \<le> x} \<subseteq> {..nat \<lfloor>root l x\<rfloor>} \<times> {..nat \<lfloor>log 2 x\<rfloor>}"
proof safe
  fix p i :: nat assume pi: "prime p" "i \<ge> l" "real (p ^ i) \<le> x"
  have "real p ^ l \<le> real p ^ i" using pi x l
    by (intro power_increasing) (auto dest: prime_gt_0_nat)
  also have "\<dots> \<le> x" using pi by simp
  finally have "root l (real p ^ l) \<le> root l x"
    using x pi l by (subst real_root_le_iff) auto
  also have "root l (real p ^ l) = real p"
    using pi l by (subst real_root_pos2) auto
  finally show "p \<le> nat \<lfloor>root l x\<rfloor>" using pi l x by (simp add: le_nat_iff' le_floor_iff)

  from pi have "2 ^ i \<le> real p ^ i" using l
    by (intro power_mono) (auto dest: prime_gt_1_nat)
  also have "\<dots> \<le> x" using pi by simp
  finally show "i \<le> nat \<lfloor>log 2 x\<rfloor>" using pi x
    by (auto simp: le_nat_iff' le_floor_iff le_log_iff powr_realpow)
qed
```

### child `ln_fact_conv_sum_upto_mangoldt`: [`thys/Prime_Number_Theorem/Prime_Number_Theorem_Library.thy` lines 45-55](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/Prime_Number_Theorem/Prime_Number_Theorem_Library.thy#L45-L55) ([local copy](code/thys/Prime_Number_Theorem/Prime_Number_Theorem_Library.thy))

```isabelle
lemma ln_fact_conv_sum_upto_mangoldt:
  "ln (fact n) = sum_upto (\<lambda>k. mangoldt k * (n div k)) n"
proof -
  have [simp]: "{0<..Suc n} = insert (Suc n) {0<..n}" for n by auto
  have "ln (fact n) = sum_upto (\<lambda>n. ln (real n)) n"
    by (induction n) (auto simp: sum_upto_altdef nat_add_distrib ln_mult)
  also have "\<dots> = sum_upto (\<lambda>k. mangoldt k * (n div k)) n"
    unfolding sum_upto_ln_conv_sum_upto_mangoldt
    by (intro sum_upto_cong) (auto simp: floor_divide_of_nat_eq)
  finally show ?thesis .
qed
```

### child `\<theta>_upper_bound`: [`thys/Prime_Number_Theorem/Prime_Counting_Functions.thy` lines 923-943](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/Prime_Number_Theorem/Prime_Counting_Functions.thy#L923-L943) ([local copy](code/thys/Prime_Number_Theorem/Prime_Counting_Functions.thy))

```isabelle
lemma \<theta>_upper_bound:
  assumes x: "x \<ge> 1"
  shows   "\<theta> x < ln 4 * x"
proof -
  have "4 powr (\<theta> x / ln 4) = (\<Prod>p | prime p \<and> p \<le> nat \<lfloor>x\<rfloor>. 4 powr (log 4 (real p)))"
    by (simp add: \<theta>_def powr_sum prime_sum_upto_altdef2 sum_divide_distrib log_def)
  also have "\<dots> = (\<Prod>p | prime p \<and> p \<le> nat \<lfloor>x\<rfloor>. real p)"
    by (intro prod.cong) (auto dest: prime_gt_1_nat)
  also have "\<dots> = real (\<Prod>p | prime p \<and> p \<le> nat \<lfloor>x\<rfloor>. p)"
    by simp
  also have "(\<Prod>p | prime p \<and> p \<le> nat \<lfloor>x\<rfloor>. p) < 4 ^ nat \<lfloor>x\<rfloor>"
    using x by (intro prod_primes_upto_less) auto
  also have "\<dots> = 4 powr real (nat \<lfloor>x\<rfloor>)"
    using x by (subst powr_realpow) auto
  also have "\<dots> \<le> 4 powr x"
    using x by (intro powr_mono) auto
  finally have "4 powr (\<theta> x / ln 4) < 4 powr x"
    by simp
  thus "\<theta> x < ln 4 * x"
    by (subst (asm) powr_less_cancel_iff) (auto simp: field_simps)
qed
```

### child `sum_upto_primepows`: [`thys/Prime_Number_Theorem/Prime_Counting_Functions.thy` lines 99-117](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/Prime_Number_Theorem/Prime_Counting_Functions.thy#L99-L117) ([local copy](code/thys/Prime_Number_Theorem/Prime_Counting_Functions.thy))

```isabelle
lemma sum_upto_primepows:
  fixes f :: "nat \<Rightarrow> 'a :: comm_monoid_add"
  assumes "\<And>n. \<not>primepow n \<Longrightarrow> f n = 0" "\<And>p i. prime p \<Longrightarrow> i > 0 \<Longrightarrow> f (p ^ i) = g p i"
  shows   "sum_upto f x = (\<Sum>(p, i) | prime p \<and> i > 0 \<and> real (p ^ i) \<le> x. g p i)"
proof -
  let ?d = aprimedivisor
  have g: "g (?d n) (multiplicity (?d n) n) = f n" if "primepow n" for n using that 
      by (subst assms(2) [symmetric])
         (auto simp: primepow_decompose aprimedivisor_prime_power primepow_gt_Suc_0
               intro!: aprimedivisor_nat multiplicity_aprimedivisor_gt_0_nat)
  have "sum_upto f x = (\<Sum>n | primepow n \<and> real n \<le> x. f n)"
    unfolding sum_upto_def using assms
    by (intro sum.mono_neutral_cong_right) (auto simp: primepow_gt_0_nat)
  also have "\<dots> = (\<Sum>(p, i) | prime p \<and> i > 0 \<and> real (p ^ i) \<le> x. g p i)" (is "_ = sum _ ?S")
    by (rule sum.reindex_bij_witness[of _ "\<lambda>(p,i). p ^ i" "\<lambda>n. (?d n, multiplicity (?d n) n)"])
       (auto simp: aprimedivisor_prime_power primepow_decompose primepow_gt_Suc_0 g
             simp del: of_nat_power intro!: aprimedivisor_nat multiplicity_aprimedivisor_gt_0_nat)
  finally show ?thesis .
qed
```

How the parts fit. The parent `mertens_bound_strong` is the glue. It first
disposes of `n = 1` and `n = 2` by direct arithmetic (lines 253-276). For
`n ≥ 3` it proceeds through one key identity, building up three interval
bounds and combining them:

1. `primepows_le_subset` gives finiteness of the index set
   `{(p, i). prime p ∧ i ≥ 1 ∧ p^i ≤ n}` (line 285), so the sums below are finite.
2. It defines the three quantities the identity will expose: `r` (a
   fractional-part correction), `R` and `R'` (the higher prime-power terms,
   lines 288-290).
3. The `R` term is bounded by `mertens_remainder_aux_bound`: `R / n ≤ R' < 9/π²`
   (lines 302-313), giving `R_bounds : R / n ∈ {0..<9 / pi²}`.
4. The log-factorial term is bounded by Stirling's `ln_fact_bounds` (an import
   from `Stirling_Formula`, not a project lemma) into
   `fact_bounds : ln n − ln(fact n) / n ∈ {0..1}` (lines 315-335).
5. The `r` term is bounded by `\<theta>_upper_bound`:
   `r / n < ln 4`, giving `r_bounds : r / n ∈ {0..<ln 4}` (lines 337-345).
6. `ln_fact_conv_sum_upto_mangoldt` then `sum_upto_primepows` rewrite
   `ln (fact n)` as a sum over prime powers, which is split into the `i = 1`
   part (the θ-sum minus `r`) and the `i > 1` part (`R`) (lines 347-367).
7. The key identity (line 368) `\<MM> n − ln n = ln(fact n)/n − ln n + r/n − R/n`
   is the carried statement: `with fact_bounds r_bounds R_bounds` closes the
   interval by `simp` (lines 370-372).

The lemma graph (arrows = "is cited by"):

```
mertens_bound_strong (glue)
 ├─ mertens_remainder_aux_bound ── uses deriv_zeta_2_bound, exponents_le_finite (same file)
 ├─ primepows_le_subset
 ├─ ln_fact_conv_sum_upto_mangoldt ── uses sum_upto_ln_conv_sum_upto_mangoldt (same file)
 ├─ \<theta>_upper_bound ── uses prod_primes_upto_less (Prime_Counting_Functions.thy)
 └─ sum_upto_primepows
   (external: ln_fact_bounds from Stirling_Formula.Stirling_Formula)
```

Why each child is a good leaf — a self-contained statement whose proof closes
on its own or from named siblings:

- `mertens_remainder_aux_bound` states `R < 9 / π²` and closes on its own from
  `deriv_zeta_2_bound` (its sibling in the same file, lines 61-111) and the
  Euler-product log-derivative identity `eval_fds_logderiv_zeta_real`.
- `primepows_le_subset` states a pure finite-subset inclusion and closes by two
  elementary estimates, `power_increasing` and `power_mono`.
- `ln_fact_conv_sum_upto_mangoldt` closes by induction on `n` plus the sibling
  `sum_upto_ln_conv_sum_upto_mangoldt` (same file, lines 32-43).
- `\<theta>_upper_bound` is a self-contained Chebyshev estimate and closes from
  `prod_primes_upto_less`.
- `sum_upto_primepows` is a self-contained reindexing identity, closed by
  `sum.reindex_bij_witness` over the prime-divisor bijection `p^i ↦ (p, i)`.

## Why it is good

1. The glue is 125 lines long (`check`, machine-checked as `lines(parent, 125)`;
   the parent site is
   [Mertens_Theorems.thy lines 250-374](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/Prime_Number_Theorem/Mertens_Theorems.thy#L250-L374)).
2. The parent proof cites `mertens_remainder_aux_bound` (`check`, machine-checked
   as `cites(parent, mertens_remainder_aux_bound)`; the cite is at line 309).
3. The parent theorem `mertens_bound_strong` is declared at
   [Mertens_Theorems.thy lines 250-374](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/Prime_Number_Theorem/Mertens_Theorems.thy#L250-L374)
   (`check`, machine-checked as `declared(mertens_bound_strong, thys/Prime_Number_Theorem/Mertens_Theorems.thy, 250-374)`).
4. The authors state the plan in a comment: "estimate both sides in different
   ways", "split the sum into those $p^i$ with $i = 1$ and those with $i \geq 2$",
   then "Applying the bound we have just shown and some more routine estimates"
   (`author-statement`, [Mertens_Theorems.thy lines 238-249](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/Prime_Number_Theorem/Mertens_Theorems.thy#L238-L249)).
5. The decomposition is shallow: 5 direct lemmas, a longest project-lemma chain
   of length 3, glue 125 lines, child proofs of 119, 20, 11, 21 and 19 lines
   (`measurement`; line counts of the sites, declaration through `qed`).

In my opinion the detail worth copying is the choice of the one identity at
line 368: instead of estimating ℳ(n) − ln n directly, the proof re-expresses
it as the sum of three terms each of which has a ready-made bound, so the only
new work in the glue is the transitivity that combines the three intervals.

## When to use it, and when not

Use it when the goal is an *absolute* (not asymptotic) bound on a remainder of
the shape ℳ(n) − ln n — or, more generally, a sum over primes — that must hold
on the whole domain, and when the target quantity can be rewritten through one
key identity into a few terms each bounded by an independently-proved named
lemma. Here the three terms are log factorial (Stirling), a Chebyshev θ bound,
and the higher prime-power remainder R.

Avoid it when only a Big-O bound is needed (the careful absolute estimates are
overkill), when the terms are not genuinely independent so the leaves cannot be
proved before the parent is assembled, or when the key identity itself needs a
non-trivial proof that outweighs the estimates it enables.

## Consequences

The move creates two kinds of obligation. First, the small cases (`n = 1` and
`n = 2`) must be closed by direct arithmetic, outside the key identity. Second,
each of the three terms the identity exposes must be bounded into a non-negative
interval of the right width, so that their combination via the identity lands in
the target interval: `R / n ∈ {0..<9/π²}`, `r / n ∈ {0..<ln 4}`, and
`ln n − ln(fact n) / n ∈ {0..1}`. Failure mode: if any one estimate is not tight
enough or has the wrong sign, the final `with fact_bounds r_bounds R_bounds …
by simp` no longer closes the interval, and the whole theorem must be re-proved
around a tighter bound.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: mertens_remainder_aux_bound@thys/Prime_Number_Theorem/Mertens_Theorems.thy:309, primepows_le_subset@thys/Prime_Number_Theorem/Mertens_Theorems.thy:285, ln_fact_conv_sum_upto_mangoldt@thys/Prime_Number_Theorem/Mertens_Theorems.thy:348, \<theta>_upper_bound@thys/Prime_Number_Theorem/Mertens_Theorems.thy:341, sum_upto_primepows@thys/Prime_Number_Theorem/Mertens_Theorems.thy:351; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(parent, 125) -> lines: site parent has 125 lines | check_claims.py |
| 2 | verified | cites(parent, mertens_remainder_aux_bound) -> cites: mertens_remainder_aux_bound occurs at thys/Prime_Number_Theorem/Mertens_Theorems.thy:309 | check_claims.py |
| 3 | verified | declared(mertens_bound_strong, thys/Prime_Number_Theorem/Mertens_Theorems.thy, 250-374) -> declared: mertens_bound_strong is declared at thys/Prime_Number_Theorem/Mertens_Theorems.thy:250 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/isabelle-prover/mirror-afp-devel at commit `07cd9ca548d180f234c63f06bf5d1cb85c7fc5df`, under `BSD-3-Clause`; see the [source note](../../sources/afp/SOURCE.md) for the licence text and attribution.
