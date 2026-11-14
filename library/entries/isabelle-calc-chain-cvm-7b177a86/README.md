# Inequality chain bounding the failure probability of the CVM estimate

| | |
|---|---|
| Kind | instance |
| Move | calc-chain |
| Language | isabelle |
| Status | draft |
| Source | [cvm](../../sources/cvm/SOURCE.md) at `aee8c4ba0bdc` |
| Licence | `BSD-2-Clause` |

## Intent

Reduce the main CVM correctness theorem — that the probability the estimate
returned by `cvm` is wrong is at most `δ` — to five named lemmas: one
discharges the trivial empty-list / oversized-threshold case exactly, and the
other four supply the three links of a single `also … finally` chain that
bounds the failure probability, the `k > l` error and the `k ≤ l` out-of-range
error, whose bounds sum to `δ`.

## The decomposition

### parent `prob_cvm_incorrect_le`: [`isabelle/CVM_Transforms/CVM_Correctness.thy` lines 94-149](https://github.com/joewatt95/cvm/blob/aee8c4ba0bdc244048d4a8ea24a1789d6d9de2bb/isabelle/CVM_Transforms/CVM_Correctness.thy#L94-L149) ([local copy](code/isabelle/CVM_Transforms/CVM_Correctness.thy))

```isabelle
theorem prob_cvm_incorrect_le :
  assumes
    \<open>0 < \<epsilon>\<close> \<open>0 \<le> \<delta>\<close>
    \<open>\<lbrakk>xs \<noteq> []; threshold \<le> card_xs\<rbrakk> \<Longrightarrow>
      \<epsilon> \<le> 1 \<and>
      2 \<le> r \<and> r \<le> threshold \<and>
      \<epsilon>\<^sup>2 * threshold \<ge> 6 * r \<and>
      r * card_xs \<le> two_l_threshold \<and> two_l_threshold \<le> 2 * r * card_xs \<and>
      prob_fail_bound + prob_k_gt_l_bound + prob_k_le_l_and_est_out_of_range_bound
      \<le> \<delta>\<close>
  shows
    \<open>\<P>(estimate in cvm xs.
      estimate |> is_None_or_pred
        (\<lambda> estimate. estimate >[\<epsilon>] card (set xs)))
    \<le> \<delta>\<close>
    (is \<open>?L \<le> ?R\<close>)
proof (cases \<open>xs = [] \<or> threshold > card (set xs)\<close>)
  case True
  with assms have \<open>?L = 0\<close>
    by (simp add: cvm_correct_of_empty_or_threshold algebra_split_simps)

  with assms show ?thesis by (simp add: prob_bounds_defs)
next
  case False
  then have \<open>xs \<noteq> []\<close> \<open>threshold \<le> card (set xs)\<close> by simp_all

  with assms interpret cvm_error_bounds_assms threshold r l \<epsilon> xs
    by unfold_locales fastforce

  let ?run_eager_algo =
    \<open>run_with_bernoulli_matrix <|
      run_reader <<< flip run_steps_eager initial_state\<close>

  from prob_run_steps_is_None_or_pred_le
  have \<open>?L \<le>
    prob_fail_bound +
    \<P>(estimate in run_steps_no_fail xs initial_state.
      compute_estimate estimate >[\<epsilon>] card (set xs))\<close>
    unfolding prob_bounds_defs cvm_def
    apply simp unfolding comp_apply .

  also from run_steps_no_fail_eq_run_steps_eager_bernoulli_matrix[where xs = xs]
  have \<open>\<dots> \<le> (
    prob_fail_bound +
    \<P>(state in ?run_eager_algo. state_k state > l) +
    \<P>(state in ?run_eager_algo. 
      state_k state \<le> l \<and> compute_estimate state >[\<epsilon>] card (set xs)))\<close>
    by (fastforce intro: pmf_add)

  also from
    assms \<open>xs \<noteq> []\<close> \<open>threshold \<le> card (set xs)\<close>
    prob_eager_algo_k_gt_l_le prob_eager_algo_k_le_l_and_est_out_of_range_le
  have \<open>\<dots> \<le> ?R\<close> unfolding prob_bounds_defs by fastforce

  finally show ?thesis .
qed
```

### context `prob_bounds_defs`: [`isabelle/CVM_Transforms/CVM_Correctness.thy` lines 83-92](https://github.com/joewatt95/cvm/blob/aee8c4ba0bdc244048d4a8ea24a1789d6d9de2bb/isabelle/CVM_Transforms/CVM_Correctness.thy#L83-L92) ([local copy](code/isabelle/CVM_Transforms/CVM_Correctness.thy))

```isabelle
definition \<open>prob_fail_bound \<equiv> length xs * f ^ threshold\<close>

abbreviation \<open>card_xs \<equiv> card (set xs)\<close>

abbreviation \<open>two_l_threshold \<equiv> 2 ^ l * threshold\<close>

lemmas prob_bounds_defs =
  prob_fail_bound_def
  prob_k_gt_l_bound_def
  prob_k_le_l_and_est_out_of_range_bound_def
```

### child `cvm_correct_of_empty_or_threshold`: [`isabelle/CVM_Transforms/CVM_Correctness.thy` lines 53-76](https://github.com/joewatt95/cvm/blob/aee8c4ba0bdc244048d4a8ea24a1789d6d9de2bb/isabelle/CVM_Transforms/CVM_Correctness.thy#L53-L76) ([local copy](code/isabelle/CVM_Transforms/CVM_Correctness.thy))

```isabelle
theorem cvm_correct_of_empty_or_threshold :
  assumes \<open>xs = [] \<or> threshold > card (set xs)\<close>
  shows \<open>cvm xs = return_spmf (card <| set xs)\<close>
proof -
  let ?step = \<open>case_option fail_spmf <<< step\<close>
  let ?P = \<open>\<lambda> index.
    (=) (Some \<lparr>state_k = 0, state_chi = set (take index xs)\<rparr>)\<close>

  from assms have \<open>\<turnstile>pmf
    \<lbrakk>(\<lambda> state. (index, x) \<in> set (indexed_from 0 xs) \<and> ?P index state)\<rbrakk>
    ?step x
    \<lbrakk>?P (Suc index)\<rbrakk>\<close> for index x
    unfolding compute_estimate_def step_def step_1_def' step_2_def' step_3_def
    apply (simp add: AE_measure_pmf_iff in_set_indexed_from_eq)
    by (metis List.finite_set Un_insert_right append.right_neutral bot_nat_0.extremum_strict card_mono less_irrefl_nat list.set(2) list.size(3) order.strict_trans1 set_append
      set_take_subset take_Suc_conv_app_nth)

  then have \<open>\<turnstile>pmf \<lbrakk>?P 0\<rbrakk> foldM_pmf ?step xs \<lbrakk>?P (length xs)\<rbrakk>\<close>
    by (intro pmf_hoare_foldM_indexed) simp_all

  then show ?thesis
    unfolding cvm_def compute_estimate_def initial_state_def foldM_spmf_eq_foldM_pmf_case 
    by (auto simp add: AE_measure_pmf_iff map_pmf_eq_return_pmf_iff)
qed
```

### child `prob_run_steps_is_None_or_pred_le`: [`isabelle/CVM_Transforms/CVM_Algo_No_Fail.thy` lines 198-213](https://github.com/joewatt95/cvm/blob/aee8c4ba0bdc244048d4a8ea24a1789d6d9de2bb/isabelle/CVM_Transforms/CVM_Algo_No_Fail.thy#L198-L213) ([local copy](code/isabelle/CVM_Transforms/CVM_Algo_No_Fail.thy))

```isabelle
theorem prob_run_steps_is_None_or_pred_le :
  \<open>\<P>(state in run_steps xs initial_state. state |> is_None_or_pred P)
  \<le> real (length xs) * f ^ threshold +
    \<P>(state in run_steps_no_fail xs initial_state. P state)\<close>
  (is \<open>?L is_None_or_pred \<le> ?R\<close>)
proof -
  have \<open>?L is_None_or_pred =
    prob_fail (run_steps xs initial_state) + ?L is_Some_and_pred\<close>
    by (metis measure_spmf_eq_measure_pmf_is_Some_and_pred prob_is_None_or_pred_eq_prob_fail_plus_prob)

  with
    prob_fail_run_steps_le
    prob_measure_spmf_le_of_ord_spmf[OF run_steps_le_run_steps_no_fail]
  show ?thesis
    by (smt (verit, del_insts) Collect_cong measure_spmf_eq_measure_pmf_is_Some_and_pred measure_spmf_spmf_of_pmf)
qed
```

### child `run_steps_no_fail_eq_run_steps_eager_bernoulli_matrix`: [`isabelle/CVM_Transforms/CVM_Algo_Lazy_Eager.thy` lines 512-519](https://github.com/joewatt95/cvm/blob/aee8c4ba0bdc244048d4a8ea24a1789d6d9de2bb/isabelle/CVM_Transforms/CVM_Algo_Lazy_Eager.thy#L512-L519) ([local copy](code/isabelle/CVM_Transforms/CVM_Algo_Lazy_Eager.thy))

```isabelle
corollary run_steps_no_fail_eq_run_steps_eager_bernoulli_matrix :
  assumes "length xs \<le> n"
  shows
    "run_steps_no_fail xs initial_state = (
      bernoulli_matrix n n f
        |> map_pmf (run_reader <| run_steps_eager xs initial_state))"
  using assms run_steps_no_fail_eq_lazy sample_run_steps_eager_eq_run_steps_lazy
  by (metis bernoulli_matrix_def local.space_def sample_def)
```

### child `prob_eager_algo_k_gt_l_le`: [`isabelle/CVM_Transforms/CVM_Error_Bounds.thy` lines 354-455](https://github.com/joewatt95/cvm/blob/aee8c4ba0bdc244048d4a8ea24a1789d6d9de2bb/isabelle/CVM_Transforms/CVM_Error_Bounds.thy#L354-L455) ([local copy](code/isabelle/CVM_Transforms/CVM_Error_Bounds.thy))

```isabelle
theorem prob_eager_algo_k_gt_l_le :
  assumes \<open>r \<ge> 2\<close> \<open>2 ^ l * threshold \<ge> r * card (set xs)\<close>
  shows
    \<open>\<P>(state in
      run_with_bernoulli_matrix <| run_reader <<< flip run_steps_eager initial_state.
      state_k state > l)
    \<le> prob_k_gt_l_bound\<close>
    (is \<open>?L \<le> _\<close>)
proof (cases \<open>l > length xs\<close>)
  case True
  with initial_state_k_bounded run_steps_eager_k_bounded
  have \<open>?L = 0\<close>
    apply (simp add: measure_pmf.prob_eq_0 AE_measure_pmf_iff not_less)
    by (meson basic_trans_rules(23) bot_nat_0.extremum_unique leD nat_le_linear)
  then show ?thesis by (simp add: prob_k_gt_l_bound_def) 
next
  case False
  then have \<open>l \<le> length xs\<close> by simp

  let ?exp_term = \<open>exp (-3 * real threshold * (r - 1)\<^sup>2 / (5 * r + 2 * r\<^sup>2))\<close>

  from exists_index_threshold_exceeded_of_k_exceeds
  have \<open>?L \<le>
    \<P>(\<phi> in bernoulli_matrix (length xs) (length xs) f.
      \<exists> i < length xs. (
        let state = run_reader (run_steps_eager_then_step_1 i xs) \<phi>
        in state_k state = l \<and> card (state_chi state) \<ge> threshold))\<close>
    by (auto intro: pmf_mono simp add: Let_def)

  text \<open>Union bound\<close>
  also have \<open>\<dots> \<le> (
    \<Sum> i < length xs.
      \<P>(\<phi> in bernoulli_matrix (length xs) (length xs) f.
        let state = run_reader (run_steps_eager_then_step_1 i xs) \<phi>
        in state_k state = l \<and> card (state_chi state) \<ge> threshold))\<close>
    proof -
      have [simp] : \<open>{\<omega>. \<exists> i < n. P i \<omega>} = (\<Union> i < n. {\<omega>. P i \<omega>})\<close>
        for n and P :: \<open>nat \<Rightarrow> 'b \<Rightarrow> bool\<close> by blast
      show ?thesis by (auto intro: measure_pmf.finite_measure_subadditive_finite)
    qed

  also have \<open>\<dots> \<le> (
    \<Sum> i < length xs.
      \<P>(estimate in binomial_pmf (card <| set <| take (Suc i) xs) (1 / 2 ^ l).
        real estimate \<ge> real threshold))\<close>
    (is \<open>_ \<le> (\<Sum> i < _. ?prob i)\<close>)
    using
      prob_eager_algo_then_step_1_le_binomial[where xs = xs] \<open>l \<le> length xs\<close>
    by (auto intro: sum_mono simp add: field_simps)

  also have \<open>\<dots> \<le> real (length xs) * ?exp_term\<close>
  proof (intro sum_bounded_above[where A = \<open>{..< length xs}\<close>, simplified card_lessThan])
    fix i show \<open>?prob i \<le> ?exp_term\<close>
    proof (cases xs)
      case Nil
      then show ?thesis
        by (simp add: binomial_pmf_0 threshold initial_state_def)
    next
      define p :: real and n \<mu> \<alpha> where
        [simp] : \<open>p \<equiv> 1 / 2 ^ l\<close> and
        \<open>n \<equiv> card (set <| take (Suc i) xs)\<close> and
        [simp] : \<open>\<mu> \<equiv> n * p\<close> and
        \<open>\<alpha> \<equiv> threshold / \<mu>\<close>

      case (Cons _ _)
      then have \<open>n \<ge> 1\<close> by (simp add: n_def leI)
      with \<open>2 ^ l * threshold \<ge> r * (card <| set xs)\<close>
      have \<open>\<alpha> \<ge> r\<close> and [simp] : \<open>threshold = \<alpha> * \<mu>\<close>
        apply (simp_all add: \<alpha>_def n_def field_simps Cons)
        by (metis (full_types) List.finite_set Multiseries_Expansion.intyness_simps(2) card_mono le_trans list.set(2) local.Cons mult_le_mono2 of_nat_le_iff of_nat_numeral of_nat_power
          push_bit_nat_def set_take_subset take_Suc_Cons)

      text \<open>Apply multiplicative upper-tail Chernoff bound\<close>
      with binomial_distribution.chernoff_prob_ge[
        of p \<open>\<alpha> - 1\<close> n, simplified binomial_distribution_def]
      have \<open>?prob i \<le> exp (- real n * p * (\<alpha> - 1)\<^sup>2 / (2 + 2 * (\<alpha> - 1) / 3))\<close>
        using \<open>r \<ge> 2\<close> by (simp add: n_def algebra_simps)

      also have \<open>\<dots> \<le> ?exp_term\<close>
      proof -
        have
          \<open>27*\<alpha>\<^sup>2*r - 24*\<alpha>*r\<^sup>2 - 6*\<alpha>*r - 6*\<alpha>\<^sup>2 + 6*r\<^sup>2 - 12*\<alpha> + 15*r \<ge> 0\<close>
          (is \<open>?expr r \<ge> 0\<close>)
          if \<open>\<alpha> \<ge> r\<close> \<open>r \<ge> 2\<close> for r :: real using that by sos

        with \<open>\<alpha> \<ge> r\<close> \<open>r \<ge> 2\<close> have
          \<open>2 ^ l * n * ?expr r \<ge> 0\<close>
          \<open>4 * 2 ^ l + \<alpha> * (2 * 2 ^ l) > 0\<close>
          by (simp_all add: pos_add_strict)

        with \<open>n \<ge> 1\<close> \<open>\<alpha> \<ge> r\<close> \<open>r \<ge> 2\<close> show ?thesis
          by (auto simp add:
            field_split_simps power_numeral_reduce add_increasing less_le_not_le
            Multiseries_Expansion.of_nat_diff_real)
      qed

      finally show ?thesis .
    qed
  qed

  finally show ?thesis unfolding prob_k_gt_l_bound_def .
qed
```

### child `prob_eager_algo_k_le_l_and_est_out_of_range_le`: [`isabelle/CVM_Transforms/CVM_Error_Bounds.thy` lines 97-248](https://github.com/joewatt95/cvm/blob/aee8c4ba0bdc244048d4a8ea24a1789d6d9de2bb/isabelle/CVM_Transforms/CVM_Error_Bounds.thy#L97-L248) ([local copy](code/isabelle/CVM_Transforms/CVM_Error_Bounds.thy))

```isabelle
theorem prob_eager_algo_k_le_l_and_est_out_of_range_le :
  assumes \<open>0 < \<epsilon>\<close> \<open>\<epsilon> \<le> 1\<close> \<open>\<epsilon>\<^sup>2 * threshold \<ge> 6 * r\<close>
  shows
    \<open>\<P>(state in run_with_bernoulli_matrix <|
        run_reader <<< flip run_steps_eager initial_state.
      state_k state \<le> l \<and> compute_estimate state >[\<epsilon>] card (set xs))
    \<le> prob_k_le_l_and_est_out_of_range_bound\<close>
    (is \<open>?L (\<le>) l \<le> _\<close>)
proof (cases xs)
  case Nil
  with \<open>\<epsilon> > 0\<close> show ?thesis
    unfolding
      compute_estimate_def prob_k_le_l_and_est_out_of_range_bound_def
      initial_state_def
    by simp
next
  case (Cons _ _)

  let ?exp_bound =
    \<open>exp (-\<epsilon>\<^sup>2 * threshold / (4 * real r * (1 + \<epsilon> / 3)))\<close>
  let ?exp_term = \<open>\<lambda> k.
    exp (- (real (card (set xs)) * f ^ k * \<epsilon>\<^sup>2 / (2 + 2 * \<epsilon> / 3)))\<close>
  let ?binom_mean = \<open>\<lambda> k. f ^ k * real (card <| set xs)\<close>

  text \<open>Apply subadditivity.\<close>
  have \<open>?L (\<le>) l \<le> (\<Sum> k \<le> l. ?L (=) k)\<close>
  proof -
    have [simp] :
      \<open>{x. f x \<le> l \<and> P x} = (
        \<Union> k \<le> l. {x. f x = k \<and> P x})\<close> for f :: \<open>'b \<Rightarrow> nat\<close> and P by auto
    show ?thesis
      by (auto
        intro: measure_pmf.finite_measure_subadditive_finite
        simp add: vimage_def)
  qed

  text \<open>Transform to binomial distribution and weaken $>$ to $\ge$.\<close>
  also have \<open>\<dots> \<le> (
    \<Sum> k \<le> l.
      \<P>(estimate in binomial_pmf (card <| set xs) <| f ^ k.
        \<bar>real estimate - ?binom_mean k\<bar> \<ge> \<epsilon> * ?binom_mean k))\<close>
    (is \<open>(\<Sum> k \<le> _. ?L k) \<le> (\<Sum> k \<le> _. ?R k)\<close>)
  proof (intro sum_mono, unfold atMost_iff)
    fix k assume \<open>k \<le> l\<close>
    with
      \<open>\<epsilon> > 0\<close> l_le_length_xs
      prob_eager_algo_le_binomial[where
        k = k and xs = xs and m = \<open>length xs\<close> and n = \<open>length xs\<close> and
        P = \<open>\<lambda> est. est / f ^ k >[\<epsilon>] card (set xs)\<close>]
    show \<open>?L k \<le> ?R k\<close>
      unfolding compute_estimate_def
      apply (simp add: Let_def field_simps)
      by (smt (verit, ccfv_threshold) mem_Collect_eq mult.commute pmf_mono)
  qed

  text \<open>Apply multiplicative two-sided Chernoff bound to each term.\<close>
  also have
    \<open>\<dots> \<le> (\<Sum> k \<le> l. 2 * ?exp_term k)\<close> (is \<open>(\<Sum> k \<le> _. ?L k) \<le> (\<Sum> k \<le> _. ?R k)\<close>)
  proof (intro sum_mono)
    fix k
    from \<open>\<epsilon> > 0\<close>
      binomial_distribution.chernoff_prob_abs_ge[
        where n = \<open>card <| set xs\<close> and p = \<open>f ^ k\<close> and \<delta> = \<epsilon>]
    show \<open>?L k \<le> ?R k\<close>
      unfolding binomial_distribution_def
      by (simp add: power_le_one algebra_simps)
  qed

  text
    \<open>In preparation to bound via a geometric series, we first transform each
    term to be of the form ${2 * \text{exp\_term}(l)} ^ {2 ^ r}$ so that we can
    later pull out a factor of $2 * \text{exp\_term}(l)$ from each term.

    Note that $\text{exp\_term}(l) < 1$ and that this is important for obtaining
    a tight bound later on.\<close>
  also from \<open>\<epsilon> > 0\<close> have
    \<open>\<dots> = (\<Sum> k \<le> l. 2 * ((?exp_term l) powr (1 / f ^ (l - k))))\<close>
    (is \<open>_ = (\<Sum> k \<le> _. ?g k)\<close>)
    apply (intro sum.cong refl)
    apply (simp add: exp_powr_real field_split_simps Cons)
    unfolding Multiseries_Expansion.intyness_simps
    by (smt (verit, best) Multiseries_Expansion.intyness_simps(5) linordered_semidom_class.add_diff_inverse more_arith_simps(11) mult.commute mult_pos_pos not_less of_nat_0_less_iff power_add
      rel_simps(51) zero_less_power)

  text
    \<open>Now we do the following:
    \begin{enumerate}
      \item Reverse the sum from $l \longrightarrow 0$, to $0 \longrightarrow l$

      \item Reindex the sum to be taken over exponents $r$ of the form $2 ^ k$
       instead of being over all $k$.

      \item Pull out a factor of $2 * \text{exp\_term}(l)$ from each term.
    \end{enumerate}\<close>
  also from assms have
    \<open>\<dots> = 2 * ?exp_term l * (\<Sum> r \<in> power 2 ` {.. l}. ?exp_term l ^ (r - 1))\<close>
    unfolding
      sum_distrib_left
      sum.atLeastAtMost_rev[of ?g 0 l, simplified atLeast0AtMost]
    apply (intro sum.reindex_bij_witness[of _ floor_log \<open>(^) 2\<close>])
      by (auto
        simp flip: exp_of_nat_mult exp_add
        simp add: exp_powr_real field_split_simps)

  text
    \<open>Upper bound by a partial geometric series, taken over all $r \in \mathbb{N}$
    up to $2 ^ l$.\<close>
  also have \<open>\<dots> \<le> 2 * ?exp_term l * (\<Sum> r \<le> 2 ^ l - 1. ?exp_term l ^ r)\<close>
    apply (intro mult_mono sum_le_included[where i = Suc] sum_nonneg)
      apply simp_all
      by (meson Suc_pred atMost_iff diff_le_mono less_eq_real_def nat_zero_less_power_iff pos2 power_increasing rel_simps(25))

  text \<open>Upper bound by infinite geometric series.\<close>
  also have \<open>\<dots> \<le> 2 * ?exp_term l * (1 / (1 - ?exp_term l))\<close>
  proof -
    from Cons \<open>\<epsilon> > 0\<close> have \<open>?exp_term l < 1\<close> using order_less_le by fastforce
    with \<open>\<epsilon> > 0\<close> show ?thesis
      by (auto intro: sum_le_suminf simp flip: suminf_geometric)
  qed

  also have \<open>\<dots> \<le> 4 * ?exp_bound\<close>
  proof -
    have
      \<open>2 * x / (1 - x) \<le> 4 * y\<close>
      if \<open>0 \<le> x\<close> \<open>x \<le> y\<close> \<open>y \<le> 1 / 2\<close> for x y :: real
      using that by sos

    then show ?thesis when
      \<open>?exp_term l \<le> ?exp_bound\<close> (is ?thesis_0)
      \<open>?exp_bound \<le> 1 / 2\<close> (is ?thesis_1) 
      using that by simp_all

    from \<open>2 ^ l * threshold \<le> 2 * r * card (set xs)\<close> \<open>\<epsilon> > 0\<close> r_pos threshold
    show ?thesis_0
      by (auto
        intro: add_mono
        simp add: field_split_simps pos_add_strict approximation_preproc_nat(13))

    from \<open>0 < \<epsilon>\<close> \<open>\<epsilon> \<le> 1\<close> have
      \<open>4 * r * (1 + 1 * \<epsilon> / 3) \<le> \<epsilon>\<^sup>2 * threshold\<close>
      if \<open>\<epsilon>\<^sup>2 * threshold \<ge> 6 * r\<close> \<open>r \<ge> 1\<close> for r threshold
      using that by sos

    with \<open>\<epsilon>\<^sup>2 * threshold \<ge> 6 * r\<close> \<open>\<epsilon> > 0\<close> r_pos
    have \<open>?exp_bound \<le> exp (- 1)\<close> by simp
    also have \<open>\<dots> \<le> 1 / 2\<close>
      by (metis (no_types, lifting) divide_le_eq_1_pos exp_ge_add_one_self exp_gt_zero exp_minus' le_divide_eq_numeral1(1) mult_2_right times_divide_eq_left)
    finally show ?thesis_1 .
  qed

  finally show ?thesis unfolding prob_k_le_l_and_est_out_of_range_bound_def .
qed
```

How the parts fit. The parent `prob_cvm_incorrect_le` first case-splits on
`xs = [] ∨ threshold > card (set xs)` (line 110 of the file):

- In the `True` branch the glue applies `cvm_correct_of_empty_or_threshold` to
  get `?L = 0` (line 113) and finishes with `simp` (lines 112-115).
- In the `False` branch the glue builds one `also … finally` chain of three
  links, each supplied by a named lemma:
  1. `prob_run_steps_is_None_or_pred_le` (CVM_Algo_No_Fail.thy:198-213) bounds
     the probability that `run_steps` fails or is wrong by `prob_fail_bound +
     Pr(estimate in run_steps_no_fail …)`, one step below `prob_fail_bound`
     (lines 127-133).
  2. `run_steps_no_fail_eq_run_steps_eager_bernoulli_matrix`
     (CVM_Algo_Lazy_Eager.thy:512-519) rewrites `run_steps_no_fail` to the
     eager algorithm over a Bernoulli matrix, splitting the residual into
     `Pr(k > l) + Pr(k ≤ l ∧ out of range)` (lines 135-141).
  3. `prob_eager_algo_k_gt_l_le` (CVM_Error_Bounds.thy:354-455) and
     `prob_eager_algo_k_le_l_and_est_out_of_range_le`
     (CVM_Error_Bounds.thy:97-248) bound the two residual terms by
     `prob_k_gt_l_bound` and `prob_k_le_l_and_est_out_of_range_bound`
     respectively; `finally` (line 148) closes the chain, and `unfolding
     prob_bounds_defs` shows the three bounds sum to at most `δ` (lines
     143-146).

The lemma graph (each arrow is "the proof above cites the lemma below"):

```
prob_cvm_incorrect_le (parent)
├── trivial case ── cvm_correct_of_empty_or_threshold
└── general case, one also … finally chain
    ├─ link 1 ── prob_run_steps_is_None_or_pred_le
    │             └─ run_steps_le_run_steps_no_fail ── step_le_step_no_fail
    ├─ link 2 ── run_steps_no_fail_eq_run_steps_eager_bernoulli_matrix
    └─ link 3 ── prob_eager_algo_k_gt_l_le
                 prob_eager_algo_k_le_l_and_est_out_of_range_le
```

Why each lemma is a good leaf — a self-contained statement whose proof closes
on its own or from named siblings:

- `cvm_correct_of_empty_or_threshold` closes by a `pmf_hoare_foldM_indexed`
  induction over the folded step plus `auto`, with no dependence on the
  error-bound machinery.
- `prob_run_steps_is_None_or_pred_le` is generic in the predicate `P`, so it
  is proved once and the glue instantiates `P` with the wrong-estimate event.
- `run_steps_no_fail_eq_run_steps_eager_bernoulli_matrix` is a corollary that
  closes by `metis` from the lazy/eager equivalence lemmas, isolating the
  "algorithm 2 = eager algorithm" equality.
- `prob_eager_algo_k_gt_l_le` and
  `prob_eager_algo_k_le_l_and_est_out_of_range_le` are the two real
  error-bound leaves; each is its own `also … finally` chain over a union
  bound / Chernoff bound / geometric series, so the main theorem's glue stays
  short (40 lines) while the weight lives in these leaves (102 and 152 lines).

## Why it is good

1. The main theorem `prob_cvm_incorrect_le` is declared in
   [`CVM_Correctness.thy` lines 94-149](https://github.com/joewatt95/cvm/blob/aee8c4ba0bdc244048d4a8ea24a1789d6d9de2bb/isabelle/CVM_Transforms/CVM_Correctness.thy#L94-L149)
   (check, `declared` form).
2. The parent's proof (the glue) cites the child
   `prob_eager_algo_k_le_l_and_est_out_of_range_le` (check, `cites` form;
   [lines 94-149](https://github.com/joewatt95/cvm/blob/aee8c4ba0bdc244048d4a8ea24a1789d6d9de2bb/isabelle/CVM_Transforms/CVM_Correctness.thy#L94-L149)).
3. No `sorry` token occurs in the parent's proof,
   [lines 94-149](https://github.com/joewatt95/cvm/blob/aee8c4ba0bdc244048d4a8ea24a1789d6d9de2bb/isabelle/CVM_Transforms/CVM_Correctness.thy#L94-L149)
   (check, `no_sorry` form).
4. The decomposition has depth 3 below the main theorem:
   `prob_cvm_incorrect_le` → `prob_run_steps_is_None_or_pred_le` →
   `run_steps_le_run_steps_no_fail` → `step_le_step_no_fail`, all in the
   copied files (measurement; citations at
   [CVM_Correctness.thy:127](https://github.com/joewatt95/cvm/blob/aee8c4ba0bdc244048d4a8ea24a1789d6d9de2bb/isabelle/CVM_Transforms/CVM_Correctness.thy#L127),
   [CVM_Algo_No_Fail.thy:210](https://github.com/joewatt95/cvm/blob/aee8c4ba0bdc244048d4a8ea24a1789d6d9de2bb/isabelle/CVM_Transforms/CVM_Algo_No_Fail.thy#L210)
   and
   [CVM_Algo_No_Fail.thy:189](https://github.com/joewatt95/cvm/blob/aee8c4ba0bdc244048d4a8ea24a1789d6d9de2bb/isabelle/CVM_Transforms/CVM_Algo_No_Fail.thy#L189)).
5. The authors label `prob_cvm_incorrect_le` "the main correctness theorem as
   in Theorem 2 of `\cite{cvm_2023}`" (author-statement;
   [CVM_Correctness.thy:17-18](https://github.com/joewatt95/cvm/blob/aee8c4ba0bdc244048d4a8ea24a1789d6d9de2bb/isabelle/CVM_Transforms/CVM_Correctness.thy#L17-L18)).

In my opinion the detail worth copying is that the case split and the chain are
stated once, but the two error-bound children carry their own deep sub-chains:
the glue is a three-link skeleton whose links are themselves calcuational
chains, so the decomposition is recursive without being tangled.

## When to use it, and when not

Use it when the goal is an upper bound `Pr[event] ≤ δ` whose event is a
disjunction ("the algorithm fails" or "the algorithm returns a wrong
estimate"), and each link of the resulting `≤` chain is non-trivial enough to
deserve its own named lemma, with the links ordered in one direction
(`<` / `≤` / `=`) so Isar's `also` composes them. The trivial cases (empty
input, oversized threshold) should be split off first and closed exactly, as
here.

Avoid it when the links are one-off rewrites with no reuse (fold them inline);
when the chain needs `≥` steps, which Isar's `also` does not compose by
default; when a single library theorem closes the whole bound; or when the
trivial branch of the case split needs the same machinery as the general
branch.

## Consequences

The move creates one obligation per link: each named lemma must be proved in
its own right before `also … finally` composes them, and transitivity is
automatic. A link stated too weak breaks the final result; here the last step
needs `prob_fail_bound + prob_k_gt_l_bound +
prob_k_le_l_and_est_out_of_range_bound ≤ δ`, which the assumptions package as a
single hypothesis discharged by `unfolding prob_bounds_defs`. The two
error-bound children carry their own Chernoff and geometric-series sub-chains,
so the decomposition's weight lies in the leaves, not in the 40-line glue.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: cvm_correct_of_empty_or_threshold@isabelle/CVM_Transforms/CVM_Correctness.thy:113, prob_run_steps_is_None_or_pred_le@isabelle/CVM_Transforms/CVM_Correctness.thy:127, run_steps_no_fail_eq_run_steps_eager_bernoulli_matrix@isabelle/CVM_Transforms/CVM_Correctness.thy:135, prob_eager_algo_k_gt_l_le@isabelle/CVM_Transforms/CVM_Correctness.thy:145, prob_eager_algo_k_le_l_and_est_out_of_range_le@isabelle/CVM_Transforms/CVM_Correctness.thy:145; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(prob_cvm_incorrect_le, isabelle/CVM_Transforms/CVM_Correctness.thy, 94-149) -> declared: prob_cvm_incorrect_le is declared at isabelle/CVM_Transforms/CVM_Correctness.thy:94 | check_claims.py |
| 2 | verified | cites(parent, prob_eager_algo_k_le_l_and_est_out_of_range_le) -> cites: prob_eager_algo_k_le_l_and_est_out_of_range_le occurs at isabelle/CVM_Transforms/CVM_Correctness.thy:145 | check_claims.py |
| 3 | verified | no_sorry(isabelle/CVM_Transforms/CVM_Correctness.thy, 94-149) -> no_sorry: none of sorry in isabelle/CVM_Transforms/CVM_Correctness.thy:94-149 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/joewatt95/cvm at commit `aee8c4ba0bdc244048d4a8ea24a1789d6d9de2bb`, under `BSD-2-Clause`; see the [source note](../../sources/cvm/SOURCE.md) for the licence text and attribution.
