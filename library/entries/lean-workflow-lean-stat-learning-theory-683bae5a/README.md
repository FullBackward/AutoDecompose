# workflow: the vibe-recipe — name one project lemma per proof step, then solve one-by-one

| | |
|---|---|
| Kind | instance |
| Move | workflow |
| Language | lean |
| Status | draft |
| Source | [lean-stat-learning-theory](../../sources/lean-stat-learning-theory/SOURCE.md) at `d0f506f0a695` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T15:59:19Z |

## Intent

The vibe-recipe decomposition workflow, realized for the Gaussian log-Sobolev inequality: the prompt (the skill-text site) states the target theorem once and lays the proof out as seven named steps, one project lemma per step, and the glue assembles `gaussian_logSobolev_W12_real` from those lemmas — a smooth compact-support approximation, L²/L¹ convergence transfer, the compact-support LSI, gradient convergence and an a.e.-subsequence extraction — each proved separately and solved one-by-one.

## The decomposition

### parent `gaussian_logSobolev_W12_real`: [`SLT/GaussianLSI/OneDimGLSI.lean` lines 415-939](https://github.com/yuanhez/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/SLT/GaussianLSI/OneDimGLSI.lean#L415-L939) ([local copy](code/SLT/GaussianLSI/OneDimGLSI.lean))

```lean
theorem gaussian_logSobolev_W12_real {f : ℝ → ℝ}
    (hf : MemW12GaussianReal f (gaussianReal 0 1))
    (hf_diff : Differentiable ℝ f) (hf_grad_cont : Continuous (fun x => fderiv ℝ f x)) :
    LogSobolev.entropy GaussianPoincare.stdGaussianMeasure (fun x => (f x)^2) ≤
      2 * ∫ x, ‖fderiv ℝ f x‖^2 ∂GaussianPoincare.stdGaussianMeasure := by
  classical
  let μ : Measure ℝ := gaussianReal 0 1
  have hprob : IsProbabilityMeasure μ := by infer_instance
  obtain ⟨g, hg_smooth, hg_supp, h_sob_tend⟩ :=
    exists_smooth_compactSupport_seq_tendsto_real f hf hf_diff hf_grad_cont
  let q : ℝ → ℝ := fun x => (f x)^2
  let qk : ℕ → ℝ → ℝ := fun k x => (g k x)^2
  have h_L2 : Tendsto (fun k => eLpNorm (f - g k) 2 μ) atTop (nhds 0) :=
    tendsto_eLpNorm_sub_of_sobolev f g μ h_sob_tend
  have h_L1 : Tendsto (fun k => eLpNorm (fun x => qk k x - q x) (1 : ENNReal) μ)
      atTop (nhds 0) := by
    have hf_cont : Continuous f := hf_diff.continuous
    have hg_cont : ∀ k, Continuous (g k) := fun k => (hg_smooth k).continuous
    have hf_mem : MemLp f 2 μ := hf.1
    simpa [q, qk] using
      (tendsto_eLpNorm_sq_sub_of_tendsto_L2 f g μ hf_cont hg_cont hf_mem h_L2)
  have h_int_q : Integrable q μ := hf.1.integrable_sq
  have h_int_qk : ∀ k, Integrable (qk k) μ := by
    intro k
    have hg_cont : Continuous (g k) := (hg_smooth k).continuous
    have hqk_cont : Continuous (fun x => (g k x)^2) := by
      fun_prop
    have hqk_supp : HasCompactSupport (fun x => (g k x)^2) :=
      hasCompactSupport_sq (hg_supp k)
    exact hqk_cont.integrable_of_hasCompactSupport hqk_supp
  have h_int_qk_event : ∀ᶠ k in atTop, Integrable (qk k) μ :=
    Eventually.of_forall h_int_qk
  have h_m_tend :
      Tendsto (fun k => ∫ x, qk k x ∂μ) atTop (nhds (∫ x, q x ∂μ)) := by
    have h_int_tend := tendsto_integral_of_L1' (f := q)
      h_int_q.aestronglyMeasurable h_int_qk_event h_L1
    simpa [q, qk] using h_int_tend
  have h_mlog_tend :
      Tendsto (fun k =>
        (∫ x, qk k x ∂μ) * Real.log (∫ x, qk k x ∂μ))
        atTop (nhds ((∫ x, q x ∂μ) * Real.log (∫ x, q x ∂μ))) := by
    exact (Real.continuous_mul_log.continuousAt.tendsto).comp h_m_tend
  let a : ℕ → ℝ := fun k => ∫ x, phi (qk k x) ∂μ
  have h_phi_int : ∀ k, Integrable (fun x => phi (qk k x)) μ := by
    intro k
    have hg_cont : Continuous (g k) := (hg_smooth k).continuous
    exact integrable_phi_sq_of_compactSupport (μ := μ) hg_cont (hg_supp k)
  have h_a_lower : ∀ k, -(1 / Real.exp 1) ≤ a k := by
    intro k
    have h_nonneg : ∀ᵐ x ∂μ, -(1 / Real.exp 1) ≤ phi (qk k x) := by
      refine Eventually.of_forall ?_
      intro x
      have hqk : 0 ≤ qk k x := sq_nonneg _
      exact mul_log_ge_neg_inv_exp (qk k x) hqk
    have h_const_int : (∫ x, (-(1 / Real.exp 1)) ∂μ) = -(1 / Real.exp 1) := by
      simp [integral_const]
    have h_le := integral_mono_ae (integrable_const (-(1 / Real.exp 1)))
      (h_phi_int k) h_nonneg
    linarith [h_le, h_const_int]
  have h_a_bdd_below : IsBoundedUnder (· ≥ ·) atTop a :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall h_a_lower)
  have hg_compact : ∀ k, EfronSteinApp.CompactlySupportedSmooth (g k) := by
    intro k
    constructor
    · have h2_le : (2 : ℕ∞) ≤ ⊤ := le_top
      exact ContDiff.of_le (hg_smooth k) (WithTop.coe_le_coe.mpr h2_le)
    · exact hg_supp k
  have h_entropy_le :
      ∀ k, LogSobolev.entropy μ (qk k) ≤ 2 * ∫ x, ‖fderiv ℝ (g k) x‖^2 ∂μ := by
    intro k
    have h :=
      GaussianLSI.gaussian_logSobolev_CompSmo_fderiv (f := g k) (hg_compact k)
    simpa [GaussianPoincare.stdGaussianMeasure, GaussianPoincare.stdGaussian, μ, qk] using h
  have h_grad_cont : ∀ k, Continuous (fun x => fderiv ℝ (g k) x) := by
    intro k
    have hg_contdiff1 : ContDiff ℝ 1 (g k) := (hg_smooth k).of_le (by simp)
    exact (contDiff_one_iff_fderiv.mp hg_contdiff1).2
  have h_grad_int_tend :
      Tendsto (fun k => ∫ x, ‖fderiv ℝ (g k) x‖^2 ∂μ) atTop
        (nhds (∫ x, ‖fderiv ℝ f x‖^2 ∂μ)) := by
    have hf_mem : MemLp (fun x => ‖fderiv ℝ f x‖) 2 μ := hf.2.norm
    have hg_mem : ∀ k, MemLp (fun x => ‖fderiv ℝ (g k) x‖) 2 μ := by
      intro k
      obtain ⟨C, hC_nonneg, hC_bound⟩ := TaylorBound.deriv_bounded_of_compactlySupported (hg_compact k)
      have h_bound : ∀ x, ‖fderiv ℝ (g k) x‖ ≤ C := by
        intro x
        have h_deriv : |deriv (g k) x| ≤ C := hC_bound x
        have h_norm : ‖fderiv ℝ (g k) x‖ = |deriv (g k) x| := by
          calc
            ‖fderiv ℝ (g k) x‖ = ‖deriv (g k) x‖ := by
              simp [norm_deriv_eq_norm_fderiv (f := g k) (x := x)]
            _ = |deriv (g k) x| := by
              simp [Real.norm_eq_abs]
        simpa [h_norm] using h_deriv
      have h_aesm :
          AEStronglyMeasurable (fun x => ‖fderiv ℝ (g k) x‖) μ :=
        (h_grad_cont k).aestronglyMeasurable.norm
      have h_bdd : ∀ᵐ x ∂μ, (fun x => ‖fderiv ℝ (g k) x‖) x ∈ Set.Icc 0 C := by
        refine Eventually.of_forall ?_
        intro x
        exact ⟨norm_nonneg _, h_bound x⟩
      exact memLp_of_bounded h_bdd h_aesm 2
    have hf_grad_cont' : Continuous (fun x => ‖fderiv ℝ f x‖) :=
      continuous_norm.comp hf_grad_cont
    have hg_grad_cont' : ∀ k, Continuous (fun x => ‖fderiv ℝ (g k) x‖) :=
      fun k => continuous_norm.comp (h_grad_cont k)
    have h_norm_tend :
        Tendsto
          (fun k =>
            eLpNorm
              (fun x => (‖fderiv ℝ (g k) x‖)^2 - (‖fderiv ℝ f x‖)^2) (1 : ENNReal) μ)
          atTop (nhds 0) := by
      have h_grad_tend :
          Tendsto (fun k =>
            eLpNorm (fun x => ‖fderiv ℝ f x - fderiv ℝ (g k) x‖) 2 μ)
            atTop (nhds 0) :=
        tendsto_eLpNorm_fderiv_sub_of_sobolev f g μ hf_diff (fun k => (contDiff_one_iff_fderiv.mp
          ((hg_smooth k).of_le (by simp))).1) h_sob_tend
      have h_norm_tend' :
          Tendsto (fun k =>
            eLpNorm (fun x => ‖fderiv ℝ f x‖ - ‖fderiv ℝ (g k) x‖) 2 μ)
            atTop (nhds 0) := by
        have h_le : ∀ k,
            eLpNorm (fun x => ‖fderiv ℝ f x‖ - ‖fderiv ℝ (g k) x‖) 2 μ ≤
              eLpNorm (fun x => ‖fderiv ℝ f x - fderiv ℝ (g k) x‖) 2 μ := by
          intro k
          refine eLpNorm_mono_ae ?_
          refine Eventually.of_forall ?_
          intro x
          simpa [Real.norm_eq_abs] using
            (abs_norm_sub_norm_le (fderiv ℝ f x) (fderiv ℝ (g k) x))
        refine
          tendsto_of_tendsto_of_tendsto_of_le_of_le
            (g := fun _ => (0 : ℝ≥0∞))
            (h := fun k => eLpNorm (fun x => ‖fderiv ℝ f x - fderiv ℝ (g k) x‖) 2 μ)
            (tendsto_const_nhds) h_grad_tend (by intro k; exact bot_le) h_le
      simpa using
        (tendsto_eLpNorm_sq_sub_of_tendsto_L2
          (f := fun x => ‖fderiv ℝ f x‖) (g := fun k x => ‖fderiv ℝ (g k) x‖) (μ := μ)
          hf_grad_cont' hg_grad_cont' hf_mem h_norm_tend')
    have h_int_f : Integrable (fun x => ‖fderiv ℝ f x‖^2) μ :=
      hf_mem.integrable_sq
    have h_int_g : ∀ᶠ k in atTop, Integrable (fun x => ‖fderiv ℝ (g k) x‖^2) μ :=
      Eventually.of_forall (fun k => (hg_mem k).integrable_sq)
    have h_int_tend :=
      tendsto_integral_of_L1' (f := fun x => ‖fderiv ℝ f x‖^2)
        h_int_f.aestronglyMeasurable h_int_g h_norm_tend
    simpa using h_int_tend
  have h_grad_bound : ∀ᶠ k in atTop,
      ∫ x, ‖fderiv ℝ (g k) x‖^2 ∂μ ≤ ∫ x, ‖fderiv ℝ f x‖^2 ∂μ + 1 := by
    have h := (tendsto_order.1 h_grad_int_tend).2 (∫ x, ‖fderiv ℝ f x‖^2 ∂μ + 1)
      (by linarith)
    exact h.mono (fun k hk => le_of_lt hk)
  have h_mlog_bound : ∀ᶠ k in atTop,
      (∫ x, qk k x ∂μ) * Real.log (∫ x, qk k x ∂μ) ≤
        (∫ x, q x ∂μ) * Real.log (∫ x, q x ∂μ) + 1 := by
    have h := (tendsto_order.1 h_mlog_tend).2
      ((∫ x, q x ∂μ) * Real.log (∫ x, q x ∂μ) + 1) (by linarith)
    exact h.mono (fun k hk => le_of_lt hk)
  have h_a_bdd_above : IsBoundedUnder (· ≤ ·) atTop a := by
    let B := 2 * (∫ x, ‖fderiv ℝ f x‖^2 ∂μ + 1) + ((∫ x, q x ∂μ) * Real.log (∫ x, q x ∂μ) + 1)
    refine isBoundedUnder_of_eventually_le (a := B) ?_
    filter_upwards [h_grad_bound, h_mlog_bound] with k hk_grad hk_mlog
    have h_entropy := h_entropy_le k
    have h_expr : a k = LogSobolev.entropy μ (qk k) +
        (∫ x, qk k x ∂μ) * Real.log (∫ x, qk k x ∂μ) := by
      simp [a, LogSobolev.entropy, qk, phi, sub_eq_add_neg, add_comm]
    calc
      a k = LogSobolev.entropy μ (qk k) +
        (∫ x, qk k x ∂μ) * Real.log (∫ x, qk k x ∂μ) := h_expr
      _ ≤ 2 * (∫ x, ‖fderiv ℝ (g k) x‖^2 ∂μ) +
        (∫ x, qk k x ∂μ) * Real.log (∫ x, qk k x ∂μ) := by
          exact add_le_add h_entropy le_rfl
      _ ≤ B := by nlinarith
  have h_cobdd : IsCoboundedUnder (· ≥ ·) atTop a :=
    h_a_bdd_above.isCoboundedUnder_ge
  let L : ℝ := Filter.liminf a atTop
  have hfreq : ∀ n : ℕ, ∃ᶠ k in atTop, a k < L + 1 / (n + 1 : ℝ) := by
    intro n
    have hlt : L < L + 1 / (n + 1 : ℝ) := by
      have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by
        have hpos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
        exact one_div_pos.mpr hpos
      linarith
    exact frequently_lt_of_liminf_lt (f := atTop) (u := a) (b := L + 1 / (n + 1 : ℝ))
      h_cobdd hlt
  obtain ⟨φ, hφ_mono, hφ_bound⟩ := extraction_forall_of_frequently hfreq
  have h_liminf_subseq : L ≤ Filter.liminf (fun n => a (φ n)) atTop := by
    have h_map : map φ atTop ≤ (atTop : Filter ℕ) := (StrictMono.tendsto_atTop hφ_mono)
    have h_bdd_above_map : IsBoundedUnder (· ≤ ·) (map φ atTop) a := by
      obtain ⟨B, hB⟩ := h_a_bdd_above
      exact ⟨B, h_map hB⟩
    have h_cobdd_subseq : IsCoboundedUnder (· ≥ ·) (map φ atTop) a :=
      h_bdd_above_map.isCoboundedUnder_ge
    have h_le :
        Filter.liminf a atTop ≤ Filter.liminf a (map φ atTop) :=
      liminf_le_liminf_of_le h_map h_a_bdd_below h_cobdd_subseq
    calc
      L = Filter.liminf a atTop := rfl
      _ ≤ Filter.liminf a (map φ atTop) := h_le
      _ = Filter.liminf (a ∘ φ) atTop := (Filter.liminf_comp a φ atTop).symm
      _ = Filter.liminf (fun n => a (φ n)) atTop := rfl
  have h_bdd_below_subseq : IsBoundedUnder (· ≥ ·) atTop (fun n => a (φ n)) := by
    obtain ⟨B, hB⟩ := IsBoundedUnder.eventually_ge h_a_bdd_below
    have hB' : ∀ᶠ n in atTop, B ≤ a (φ n) :=
      (StrictMono.tendsto_atTop hφ_mono).eventually hB
    exact isBoundedUnder_of_eventually_ge hB'
  have h_bdd_above_subseq : IsBoundedUnder (· ≤ ·) atTop (fun n => a (φ n)) := by
    refine isBoundedUnder_of_eventually_le (a := L + 1) ?_
    refine Eventually.of_forall ?_
    intro n
    have hle : (1 / (n + 1 : ℝ)) ≤ 1 := by
      have hge : (1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have h := one_div_le_one_div_of_le (α := ℝ) (a := 1) (b := n + 1) one_pos hge
      simp only [one_div, inv_one] at h
      rw [one_div]
      exact h
    have := hφ_bound n
    linarith
  have h_limsup_subseq : Filter.limsup (fun n => a (φ n)) atTop ≤ L := by
    have h_cobdd_subseq : IsCoboundedUnder (· ≤ ·) atTop (fun n => a (φ n)) :=
      h_bdd_below_subseq.isCoboundedUnder_le
    have h_lim : Tendsto (fun n : ℕ => L + 1 / (n + 1 : ℝ)) atTop (nhds L) := by
      have h_tend :
          Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ))) atTop (nhds (0 : ℝ)) := by
        have h := @tendsto_one_div_add_atTop_nhds_zero_nat ℝ _ _ _ _
        simpa using h
      simpa using (tendsto_const_nhds.add h_tend)
    have h_limsup_bound :
        Filter.limsup (fun n : ℕ => L + 1 / (n + 1 : ℝ)) atTop = L := by
      exact (Filter.Tendsto.limsup_eq h_lim)
    have h_bdd_v : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => L + 1 / (n + 1 : ℝ)) := by
      refine isBoundedUnder_of_eventually_le (a := L + 1) ?_
      refine Eventually.of_forall ?_
      intro n
      have : 1 / (n + 1 : ℝ) ≤ 1 := by
        have hge : (1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        have h := one_div_le_one_div_of_le (by linarith : (0 : ℝ) < 1) hge
        simp only [div_one] at h
        exact h
      linarith
    have h_le := limsup_le_limsup (f := atTop)
      (Filter.Eventually.of_forall (fun n => (le_of_lt (hφ_bound n))))
      h_cobdd_subseq h_bdd_v
    calc Filter.limsup (fun n => a (φ n)) atTop
        ≤ Filter.limsup (fun n : ℕ => L + 1 / (n + 1 : ℝ)) atTop := h_le
      _ = L := h_limsup_bound
  have h_a_tend : Tendsto (fun n => a (φ n)) atTop (nhds L) :=
    tendsto_of_le_liminf_of_limsup_le h_liminf_subseq h_limsup_subseq
      h_bdd_above_subseq h_bdd_below_subseq
  have h_L1_subseq :
      Tendsto (fun n => eLpNorm (fun x => qk (φ n) x - q x) (1 : ENNReal) μ)
        atTop (nhds 0) :=
    h_L1.comp (StrictMono.tendsto_atTop hφ_mono)
  obtain ⟨ns, hns_mono, h_ae_tend⟩ :=
    exists_seq_tendsto_ae_of_tendsto_eLpNorm_one
      (f := fun n x => qk (φ n) x) (g := q)
      (hf := fun n => (hg_smooth (φ n)).continuous.aestronglyMeasurable.pow 2)
      (hg := hf_diff.continuous.aestronglyMeasurable.pow 2) h_L1_subseq
  let qk' : ℕ → ℝ → ℝ := fun n x => qk (φ (ns n)) x
  have h_ae_tend' :
      ∀ᵐ x ∂μ, Tendsto (fun i => qk' i x) atTop (nhds (q x)) := by
    filter_upwards [h_ae_tend] with x hx
    simpa [qk'] using hx
  have h_a_tend' : Tendsto (fun n => a (φ (ns n))) atTop (nhds L) :=
    h_a_tend.comp (StrictMono.tendsto_atTop hns_mono)
  let h : ℝ → ℝ := fun x => phi (q x) + 1 / Real.exp 1
  let hk : ℕ → ℝ → ℝ := fun n x => phi (qk' n x) + 1 / Real.exp 1
  have h_nonneg : 0 ≤ᵐ[μ] h := by
    refine Eventually.of_forall ?_
    intro x
    have hq : 0 ≤ q x := sq_nonneg _
    exact phi_add_inv_exp_nonneg hq
  have hk_nonneg : ∀ n, 0 ≤ᵐ[μ] hk n := by
    intro n
    refine Eventually.of_forall ?_
    intro x
    have hqk : 0 ≤ qk' n x := sq_nonneg _
    exact phi_add_inv_exp_nonneg hqk
  have h_meas : ∀ n, Measurable (fun x => ENNReal.ofReal (hk n x)) := by
    intro n
    have hk_cont : Continuous (hk n) := by
      have hqk_cont : Continuous (qk' n) := by
        have hcont : Continuous (g (φ (ns n))) := (hg_smooth (φ (ns n))).continuous
        have : Continuous (fun x => (g (φ (ns n)) x)^2) := by fun_prop
        simpa [qk', qk] using this
      exact (phi_continuous.comp hqk_cont).add continuous_const
    exact ENNReal.measurable_ofReal.comp hk_cont.measurable
  have h_tend_hk : ∀ᵐ x ∂μ, Tendsto (fun n => ENNReal.ofReal (hk n x)) atTop
      (nhds (ENNReal.ofReal (h x))) := by
    filter_upwards [h_ae_tend'] with x hx
    have hphi : Tendsto (fun n => phi (qk' n x)) atTop (nhds (phi (q x))) :=
      (phi_continuous.tendsto _).comp hx
    have hsum : Tendsto (fun n => hk n x) atTop (nhds (h x)) := by
      simpa [hk, h, add_comm] using hphi.const_add (1 / Real.exp 1)
    exact ENNReal.tendsto_ofReal hsum
  have h_liminf_eq :
      ∀ᵐ x ∂μ, Filter.liminf (fun n => ENNReal.ofReal (hk n x)) atTop =
        ENNReal.ofReal (h x) := by
    filter_upwards [h_tend_hk] with x hx
    exact (Filter.Tendsto.liminf_eq hx)
  have h_fatou :
      ∫ x, h x ∂μ ≤ Filter.liminf (fun n => ∫ x, hk n x ∂μ) atTop := by
    have h_fatou_enn :
        ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (hk n x)) atTop ∂μ ≤
          Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (hk n x) ∂μ) atTop :=
      lintegral_liminf_le h_meas
    have h_lhs :
        (∫ x, h x ∂μ) =
          ENNReal.toReal (∫⁻ x, ENNReal.ofReal (h x) ∂μ) := by
      exact integral_eq_lintegral_of_nonneg_ae h_nonneg
        (by
          have h_cont : Continuous h := by
            have hq_cont : Continuous q := hf_diff.continuous.pow 2
            exact (phi_continuous.comp hq_cont).add continuous_const
          exact h_cont.aestronglyMeasurable)
    have h_liminf_eq' :
        (∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (hk n x)) atTop ∂μ) =
          ∫⁻ x, ENNReal.ofReal (h x) ∂μ := by
      refine lintegral_congr_ae ?_
      exact h_liminf_eq
    have h_lim_tend :
        Tendsto (fun n => ∫ x, hk n x ∂μ) atTop (nhds (L + 1 / Real.exp 1)) := by
      have h_tend' :
          Tendsto (fun n => a (φ (ns n)) + 1 / Real.exp 1) atTop (nhds (L + 1 / Real.exp 1)) := by
        simpa [a, add_comm] using h_a_tend'.const_add (1 / Real.exp 1)
      have h_eq : (fun n => ∫ x, hk n x ∂μ) =
          fun n => a (φ (ns n)) + 1 / Real.exp 1 := by
        funext n
        simp only [hk, qk', a, one_div]
        rw [integral_add (h_phi_int (φ (ns n))) (integrable_const _)]
        rw [integral_const, smul_eq_mul]
        simp
      simpa [h_eq] using h_tend'
    have h_rhs' :
        Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (hk n x) ∂μ) atTop =
          ENNReal.ofReal (L + 1 / Real.exp 1) := by
      have h_tend_enn :
          Tendsto (fun n => ENNReal.ofReal (∫ x, hk n x ∂μ)) atTop
            (nhds (ENNReal.ofReal (L + 1 / Real.exp 1))) :=
        (ENNReal.tendsto_ofReal h_lim_tend)
      have h_eq' : (fun n => ∫⁻ x, ENNReal.ofReal (hk n x) ∂μ) =
          fun n => ENNReal.ofReal (∫ x, hk n x ∂μ) := by
        funext n
        have hk_int : Integrable (hk n) μ := by
          have hqk_cont : Continuous (g (φ (ns n))) := (hg_smooth (φ (ns n))).continuous
          exact integrable_phi_sq_add_const (μ := μ) hqk_cont (hg_supp (φ (ns n)))
        have hk_eq :
            ENNReal.ofReal (∫ x, hk n x ∂μ) = ∫⁻ x, ENNReal.ofReal (hk n x) ∂μ :=
          MeasureTheory.ofReal_integral_eq_lintegral_ofReal hk_int (hk_nonneg n)
        simp [hk_eq]
      simpa [h_eq'] using (Filter.Tendsto.liminf_eq h_tend_enn)
    have h_lhs' : (∫ x, h x ∂μ) =
        ENNReal.toReal (∫⁻ x, ENNReal.ofReal (h x) ∂μ) := h_lhs
    have h_rhs'' :
        Filter.liminf (fun n => ∫ x, hk n x ∂μ) atTop = L + 1 / Real.exp 1 := by
      simpa using (Filter.Tendsto.liminf_eq h_lim_tend)
    -- finish: prove the outer h_fatou goal
    have h_le_enn : ∫⁻ x, ENNReal.ofReal (h x) ∂μ ≤ ENNReal.ofReal (L + 1 / Real.exp 1) := by
      calc ∫⁻ x, ENNReal.ofReal (h x) ∂μ
          = ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (hk n x)) atTop ∂μ := h_liminf_eq'.symm
        _ ≤ Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (hk n x) ∂μ) atTop := h_fatou_enn
        _ = ENNReal.ofReal (L + 1 / Real.exp 1) := h_rhs'
    have h_rhs_ne : ENNReal.ofReal (L + 1 / Real.exp 1) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h_lhs_ne : ∫⁻ x, ENNReal.ofReal (h x) ∂μ ≠ ⊤ :=
      ne_top_of_le_ne_top h_rhs_ne h_le_enn
    have h_le_real := ENNReal.toReal_le_toReal h_lhs_ne h_rhs_ne |>.mpr h_le_enn
    have h_rhs_toReal : (ENNReal.ofReal (L + 1 / Real.exp 1)).toReal = L + 1 / Real.exp 1 := by
      apply ENNReal.toReal_ofReal
      -- L is the liminf of a, and a k ≥ -1/e for all k
      have hL_lower : L ≥ -(1 / Real.exp 1) := by
        have h_lower_bdd : ∀ k, -(1 / Real.exp 1) ≤ a k := h_a_lower
        exact le_liminf_of_le h_cobdd (Eventually.of_forall h_lower_bdd)
      linarith
    rw [h_lhs', h_rhs'']
    rwa [h_rhs_toReal] at h_le_real
  have h_phi_liminf :
      ∫ x, phi (q x) ∂μ ≤ Filter.liminf (fun n => a n) atTop := by
    have h_lim_tend' :
        Tendsto (fun n => ∫ x, hk n x ∂μ) atTop (nhds (L + 1 / Real.exp 1)) := by
      have h_tend'' :
          Tendsto (fun n => a (φ (ns n)) + 1 / Real.exp 1) atTop (nhds (L + 1 / Real.exp 1)) := by
        simpa [a, add_comm] using h_a_tend'.const_add (1 / Real.exp 1)
      have h_eq' : (fun n => ∫ x, hk n x ∂μ) = fun n => a (φ (ns n)) + 1 / Real.exp 1 := by
        funext n
        simp only [hk, qk', a, one_div]
        rw [integral_add (h_phi_int (φ (ns n))) (integrable_const _)]
        rw [integral_const, smul_eq_mul]
        simp
      simpa [h_eq'] using h_tend''
    have h_liminf_hk :
        Filter.liminf (fun n => ∫ x, hk n x ∂μ) atTop = L + 1 / Real.exp 1 := by
      simpa using (Filter.Tendsto.liminf_eq h_lim_tend')
    have h_phi : ∫ x, phi (q x) ∂μ = ∫ x, h x ∂μ - 1 / Real.exp 1 := by
      have h_eq_fun : (fun x => phi (q x)) = fun x => h x - 1 / Real.exp 1 := by
        funext x
        simp [h, phi, add_comm]
      have h_int_h : Integrable h μ := by
        have h_cont : Continuous h := by
          have hq_cont : Continuous q := hf_diff.continuous.pow 2
          exact (phi_continuous.comp hq_cont).add continuous_const
        have h_asm : AEStronglyMeasurable h μ := h_cont.aestronglyMeasurable
        have h_lintegral_le : ∫⁻ x, ENNReal.ofReal (h x) ∂μ ≤ ENNReal.ofReal (L + 1 / Real.exp 1) := by
          calc ∫⁻ x, ENNReal.ofReal (h x) ∂μ
              = ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (hk n x)) atTop ∂μ := by
                refine lintegral_congr_ae ?_
                filter_upwards [h_liminf_eq] with x hx
                exact hx.symm
            _ ≤ Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (hk n x) ∂μ) atTop :=
                lintegral_liminf_le h_meas
            _ = Filter.liminf (fun n => ENNReal.ofReal (∫ x, hk n x ∂μ)) atTop := by
                refine Filter.liminf_congr ?_
                filter_upwards with n
                have hk_int : Integrable (hk n) μ := by
                  have hqk_cont : Continuous (g (φ (ns n))) := (hg_smooth (φ (ns n))).continuous
                  exact integrable_phi_sq_add_const (μ := μ) hqk_cont (hg_supp (φ (ns n)))
                exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hk_int (hk_nonneg n)).symm
            _ = ENNReal.ofReal (L + 1 / Real.exp 1) := by
                exact ENNReal.tendsto_ofReal h_lim_tend' |>.liminf_eq
        have h_lhs_ne : ∫⁻ x, ENNReal.ofReal (h x) ∂μ ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.ofReal_ne_top h_lintegral_le
        exact lintegral_ofReal_ne_top_iff_integrable h_asm h_nonneg |>.mp h_lhs_ne
      rw [h_eq_fun, integral_sub h_int_h (integrable_const _), integral_const, smul_eq_mul]
      simp
    linarith
  have h_b_tend :
      Tendsto (fun k =>
        (∫ x, qk k x ∂μ) * Real.log (∫ x, qk k x ∂μ))
        atTop (nhds ((∫ x, q x ∂μ) * Real.log (∫ x, q x ∂μ))) := h_mlog_tend
  have h_b_liminf :
      Filter.liminf (fun k =>
        -((∫ x, qk k x ∂μ) * Real.log (∫ x, qk k x ∂μ))) atTop =
        -((∫ x, q x ∂μ) * Real.log (∫ x, q x ∂μ)) := by
    have h_tend := h_b_tend.neg
    simpa using (Filter.Tendsto.liminf_eq h_tend)
  have h_entropy_liminf :
      LogSobolev.entropy μ q ≤ Filter.liminf (fun k => LogSobolev.entropy μ (qk k)) atTop := by
    have h_lim :
        Filter.liminf (fun k => a k) atTop +
            Filter.liminf (fun k =>
              -((∫ x, qk k x ∂μ) * Real.log (∫ x, qk k x ∂μ))) atTop ≤
          Filter.liminf (fun k =>
            a k - (∫ x, qk k x ∂μ) * Real.log (∫ x, qk k x ∂μ)) atTop := by
      have h_bdd_above : IsBoundedUnder (· ≤ ·) atTop a := h_a_bdd_above
      have h_bdd_below : IsBoundedUnder (· ≥ ·) atTop a := h_a_bdd_below
      have h_bdd_below' :
          IsBoundedUnder (· ≥ ·) atTop
            (fun k =>
              -((∫ x, qk k x ∂μ) * Real.log (∫ x, qk k x ∂μ))) := by
        let B' := -((∫ x, q x ∂μ) * Real.log (∫ x, q x ∂μ) + 1)
        refine isBoundedUnder_of_eventually_ge (a := B') ?_
        filter_upwards [h_mlog_bound] with k hk
        linarith
      have h_cobdd :
          IsCoboundedUnder (· ≥ ·) atTop
            (fun k =>
              -((∫ x, qk k x ∂μ) * Real.log (∫ x, qk k x ∂μ))) := by
        have h_bdd_le : IsBoundedUnder (· ≤ ·) atTop
            (fun k =>
              -((∫ x, qk k x ∂μ) * Real.log (∫ x, qk k x ∂μ))) := by
          let C := -(((∫ x, q x ∂μ) * Real.log (∫ x, q x ∂μ)) - 1)
          refine isBoundedUnder_of_eventually_le (a := C) ?_
          have h_event := (tendsto_order.1 h_b_tend).1
            (((∫ x, q x ∂μ) * Real.log (∫ x, q x ∂μ)) - 1) (by linarith)
          filter_upwards [h_event] with k hk
          simp only [C]
          linarith
        exact h_bdd_le.isCoboundedUnder_ge
      have h := le_liminf_add (f := atTop)
        (u := a)
        (v := fun k => -((∫ x, qk k x ∂μ) * Real.log (∫ x, qk k x ∂μ)))
        h_bdd_below h_bdd_above h_bdd_below' h_cobdd
      have ha : (fun k => a k) = a := rfl
      have h_add :
          (a + fun k => -((∫ x, qk k x ∂μ) * Real.log (∫ x, qk k x ∂μ))) =
            fun k => a k + -((∫ x, qk k x ∂μ) * Real.log (∫ x, qk k x ∂μ)) := by
        funext k
        rfl
      simpa [ha, h_add, sub_eq_add_neg] using h
    have h_phi :
        LogSobolev.entropy μ q =
          ∫ x, phi (q x) ∂μ -
            (∫ x, q x ∂μ) * Real.log (∫ x, q x ∂μ) := by
      simp [LogSobolev.entropy, phi, q]
    have h_entropy_lim :
        Filter.liminf (fun k => LogSobolev.entropy μ (qk k)) atTop =
          Filter.liminf (fun k =>
            a k - (∫ x, qk k x ∂μ) * Real.log (∫ x, qk k x ∂μ)) atTop := by
      rfl
    linarith [h_phi, h_phi_liminf, h_lim, h_b_liminf]
  have h_entropy_liminf_bound :
      Filter.liminf (fun k => LogSobolev.entropy μ (qk k)) atTop ≤
        2 * ∫ x, ‖fderiv ℝ f x‖^2 ∂μ := by
    have h_le :
        Filter.liminf (fun k => LogSobolev.entropy μ (qk k)) atTop ≤
          Filter.liminf (fun k => 2 * ∫ x, ‖fderiv ℝ (g k) x‖^2 ∂μ) atTop := by
      refine liminf_le_liminf (h := Filter.Eventually.of_forall h_entropy_le) ?_ ?_
      · have h_bdd : IsBoundedUnder (· ≥ ·) atTop (fun k => LogSobolev.entropy μ (qk k)) := by
          let B := -(1 / Real.exp 1) - ((∫ x, q x ∂μ) * Real.log (∫ x, q x ∂μ) + 1)
          refine isBoundedUnder_of_eventually_ge (a := B) ?_
          filter_upwards [h_mlog_bound] with k hk_mlog
          have hk_a := h_a_lower k
          simp only [LogSobolev.entropy, phi, a] at hk_a ⊢
          linarith
        exact h_bdd
      · have h_bdd : IsCoboundedUnder (· ≥ ·) atTop
          (fun k => 2 * ∫ x, ‖fderiv ℝ (g k) x‖^2 ∂μ) := by
          have h_bdd_le : IsBoundedUnder (· ≤ ·) atTop
              (fun k => 2 * ∫ x, ‖fderiv ℝ (g k) x‖^2 ∂μ) := by
            let D := 2 * (∫ x, ‖fderiv ℝ f x‖^2 ∂μ + 1)
            refine isBoundedUnder_of_eventually_le (a := D) ?_
            filter_upwards [h_grad_bound] with k hk
            nlinarith
          exact h_bdd_le.isCoboundedUnder_ge
        exact h_bdd
    have h_lim :
        Filter.liminf (fun k => 2 * ∫ x, ‖fderiv ℝ (g k) x‖^2 ∂μ) atTop =
          2 * ∫ x, ‖fderiv ℝ f x‖^2 ∂μ := by
      have h_tend := h_grad_int_tend.const_mul (2 : ℝ)
      simpa using (Filter.Tendsto.liminf_eq h_tend)
    simpa [h_lim] using h_le
  have h_final :
      LogSobolev.entropy μ q ≤ 2 * ∫ x, ‖fderiv ℝ f x‖^2 ∂μ :=
    le_trans h_entropy_liminf h_entropy_liminf_bound
  simpa [GaussianPoincare.stdGaussianMeasure, GaussianPoincare.stdGaussian, μ, q] using h_final
```

### child `exists_smooth_compactSupport_seq_tendsto_real`: [`SLT/GaussianSobolevDense/Density.lean` lines 823-859](https://github.com/yuanhez/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/SLT/GaussianSobolevDense/Density.lean#L823-L859) ([local copy](code/SLT/GaussianSobolevDense/Density.lean))

```lean
theorem exists_smooth_compactSupport_seq_tendsto_real (f : ℝ → ℝ)
    (hf : MemW12GaussianReal f (gaussianReal 0 1))
    (hf_diff : Differentiable ℝ f) (hf_grad_cont : Continuous (fun x => fderiv ℝ f x)) :
    ∃ g : ℕ → (ℝ → ℝ),
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (g k)) ∧
      (∀ k, HasCompactSupport (g k)) ∧
      Tendsto (fun k => GaussianSobolevNormSqReal (f - g k) (gaussianReal 0 1)) atTop (nhds 0) := by
  -- Transform f to E 1
  let f' := toE1Fun f
  -- Verify hypotheses for the general theorem
  have hf' : GaussianSobolev.MemW12Gaussian 1 f' (stdGaussianE 1) :=
    memW12Gaussian_toE1Fun f hf hf_diff
  have hf'_diff : Differentiable ℝ f' := differentiable_toE1Fun f hf_diff
  have hf'_grad_cont : Continuous (fun x => fderiv ℝ f' x) :=
    continuous_fderiv_toE1Fun f hf_diff hf_grad_cont
  -- Apply the general density theorem
  obtain ⟨g', hg'_smooth, hg'_supp, hg'_conv⟩ :=
    GaussianSobolev.exists_smooth_compactSupport_seq_tendsto f' hf' hf'_diff hf'_grad_cont
  -- Transform the sequence back to ℝ
  use fun k => fromE1Fun (g' k)
  refine ⟨?_, ?_, ?_⟩
  · -- Smoothness
    intro k
    exact contDiff_fromE1Fun (g' k) (hg'_smooth k)
  · -- Compact support
    intro k
    exact hasCompactSupport_fromE1Fun (g' k) (hg'_supp k)
  · -- Convergence
    -- The key is: ‖f - fromE1Fun (g' k)‖ = ‖toE1Fun f - g' k‖
    have heq : (fun k => GaussianSobolevNormSqReal (f - fromE1Fun (g' k)) (gaussianReal 0 1)) =
        fun k => GaussianSobolev.GaussianSobolevNormSq 1 (f' - g' k) (stdGaussianE 1) := by
      ext k
      rw [gaussianSobolevNormSq_sub_eq f (g' k) hf_diff hf_grad_cont]
      -- g' k is ContDiff ⊤, hence ContDiff 1
      exact (hg'_smooth k).of_le (WithTop.coe_le_coe.mpr le_top)
    rw [heq]
    exact hg'_conv
```

### child `tendsto_eLpNorm_sub_of_sobolev`: [`SLT/GaussianLSI/OneDimGLSI.lean` lines 105-129](https://github.com/yuanhez/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/SLT/GaussianLSI/OneDimGLSI.lean#L105-L129) ([local copy](code/SLT/GaussianLSI/OneDimGLSI.lean))

```lean
lemma tendsto_eLpNorm_sub_of_sobolev (f : ℝ → ℝ) (g : ℕ → ℝ → ℝ) (μ : Measure ℝ)
    (h_tend : Tendsto (fun k => GaussianSobolevNormSqReal (f - g k) μ) atTop (nhds 0)) :
    Tendsto (fun k => eLpNorm (f - g k) 2 μ) atTop (nhds 0) := by
  have h_tend_sq :
      Tendsto (fun k => eLpNorm (f - g k) 2 μ ^ 2) atTop (nhds 0) := by
    have h_le : ∀ k,
        eLpNorm (f - g k) 2 μ ^ 2 ≤ GaussianSobolevNormSqReal (f - g k) μ := by
      intro k
      simp [GaussianSobolevNormSqReal]
    have h_nonneg : ∀ k, (0 : ℝ≥0∞) ≤ eLpNorm (f - g k) 2 μ ^ 2 := by
      intro k
      exact bot_le
    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        (g := fun _ => (0 : ℝ≥0∞))
        (h := fun k => GaussianSobolevNormSqReal (f - g k) μ)
        (tendsto_const_nhds) h_tend h_nonneg h_le
  rw [ENNReal.tendsto_nhds_zero] at h_tend_sq ⊢
  intro ε hε
  have hε' : 0 < ε ^ 2 := by
    have hε0 : ε ≠ 0 := ne_of_gt hε
    simpa [pow_two] using ENNReal.mul_pos hε0 hε0
  have h_eventually := h_tend_sq (ε ^ 2) hε'
  filter_upwards [h_eventually] with k hk
  exact (ENNReal.pow_le_pow_left_iff (n := 2) (by decide)).1 hk
```

### child `tendsto_eLpNorm_sq_sub_of_tendsto_L2`: [`SLT/GaussianLSI/OneDimGLSI.lean` lines 132-247](https://github.com/yuanhez/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/SLT/GaussianLSI/OneDimGLSI.lean#L132-L247) ([local copy](code/SLT/GaussianLSI/OneDimGLSI.lean))

```lean
lemma tendsto_eLpNorm_sq_sub_of_tendsto_L2
    (f : ℝ → ℝ) (g : ℕ → ℝ → ℝ) (μ : Measure ℝ)
    (hf_cont : Continuous f) (hg_cont : ∀ k, Continuous (g k))
    (hf_mem : MemLp f 2 μ)
    (h_tend : Tendsto (fun k => eLpNorm (f - g k) 2 μ) atTop (nhds 0)) :
    Tendsto (fun k => eLpNorm (fun x => (g k x)^2 - (f x)^2) (1 : ENNReal) μ) atTop (nhds 0) := by
  have h_holder : ∀ k,
      eLpNorm (fun x => (g k x)^2 - (f x)^2) (1 : ENNReal) μ ≤
        eLpNorm (fun x => g k x - f x) 2 μ * eLpNorm (fun x => g k x + f x) 2 μ := by
    intro k
    have h_meas1 : AEStronglyMeasurable (fun x => g k x - f x) μ :=
      (hg_cont k).aestronglyMeasurable.sub hf_cont.aestronglyMeasurable
    have h_meas2 : AEStronglyMeasurable (fun x => g k x + f x) μ :=
      (hg_cont k).aestronglyMeasurable.add hf_cont.aestronglyMeasurable
    have h_bound :
        ∀ᵐ x ∂μ,
          ‖(g k x - f x) * (g k x + f x)‖ ≤
            (1 : ℝ) * ‖g k x - f x‖ * ‖g k x + f x‖ := by
      refine Eventually.of_forall ?_
      intro x
      simp [norm_mul]
    have h_holder' := (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := 2) (q := 2) (r := 1)
        h_meas1 h_meas2 (fun a b => a * b) 1 h_bound)
    have h_eq : (fun x => (g k x)^2 - (f x)^2) =
        fun x => (g k x - f x) * (g k x + f x) := by
      ext x
      ring
    simpa [h_eq, mul_comm, mul_left_comm, mul_assoc] using h_holder'
  have h_tend' : Tendsto (fun k => eLpNorm (fun x => g k x - f x) 2 μ) atTop (nhds 0) := by
    refine h_tend.congr' ?_
    filter_upwards with k
    calc
      eLpNorm (f - g k) 2 μ
          = eLpNorm (fun x => f x - g k x) 2 μ := by
              rfl
      _ = eLpNorm (fun x => -(f x - g k x)) 2 μ := by
              symm
              exact eLpNorm_neg (fun x => f x - g k x) (2 : ENNReal) μ
      _ = eLpNorm (fun x => g k x - f x) 2 μ := by
              simp
  have h_eventually_small : ∀ᶠ k in atTop, eLpNorm (fun x => g k x - f x) 2 μ ≤ 1 := by
    have := (ENNReal.tendsto_nhds_zero.mp h_tend') 1 (by simp)
    filter_upwards [this] with k hk
    exact hk
  have h_bound_add : ∀ᶠ k in atTop,
      eLpNorm (fun x => g k x + f x) 2 μ ≤
        1 + 2 * eLpNorm f 2 μ := by
    filter_upwards [h_eventually_small] with k hk
    have h_meas1 : AEStronglyMeasurable (fun x => g k x - f x) μ :=
      (hg_cont k).aestronglyMeasurable.sub hf_cont.aestronglyMeasurable
    have h_meas2 : AEStronglyMeasurable (fun x => (2 : ℝ) * f x) μ :=
      hf_cont.aestronglyMeasurable.const_mul (2 : ℝ)
    have h_tri := eLpNorm_add_le h_meas1 h_meas2 (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_eq : (fun x => g k x + f x) = fun x => (g k x - f x) + (2 : ℝ) * f x := by
      funext x
      ring
    have h_scale : eLpNorm (fun x => (2 : ℝ) * f x) 2 μ = 2 * eLpNorm f 2 μ := by
      have h_scale' :
          eLpNorm ((2 : ℝ) • f) 2 μ = ‖(2 : ℝ)‖ₑ * eLpNorm f 2 μ := by
        simpa using
          (eLpNorm_const_smul (c := (2 : ℝ)) (f := f) (p := (2 : ℝ≥0∞)) (μ := μ))
      have h_norm : (‖(2 : ℝ)‖ₑ : ℝ≥0∞) = 2 := by
        rw [Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      have h_eq : (fun x => (2 : ℝ) * f x) = (2 : ℝ) • f := by
        funext x
        simp
      simpa [h_eq, h_norm] using h_scale'
    have h_tri' : eLpNorm (fun x => g k x + f x) 2 μ ≤
        eLpNorm (fun x => g k x - f x) 2 μ + 2 * eLpNorm f 2 μ := by
      have h_tri'' :
          eLpNorm (fun x => (g k x - f x) + (2 : ℝ) * f x) 2 μ ≤
            eLpNorm (fun x => g k x - f x) 2 μ + eLpNorm (fun x => (2 : ℝ) * f x) 2 μ := by
        have h_add :
            ((fun x => g k x - f x) + fun x => (2 : ℝ) * f x) =
              fun x => (g k x - f x) + (2 : ℝ) * f x := by
          funext x
          rfl
        simpa [h_add] using h_tri
      simpa [h_eq, h_scale] using h_tri''
    have h_bound :
        eLpNorm (fun x => g k x - f x) 2 μ + 2 * eLpNorm f 2 μ ≤
          1 + 2 * eLpNorm f 2 μ := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_le_add_right hk (2 * eLpNorm f 2 μ))
    exact le_trans h_tri' h_bound
  have h_mul_tend :
      Tendsto (fun k => (1 + 2 * eLpNorm f 2 μ) * eLpNorm (fun x => g k x - f x) 2 μ)
        atTop (nhds 0) := by
    have hf_ne : eLpNorm f 2 μ ≠ ∞ := by
      exact ne_of_lt hf_mem.eLpNorm_lt_top
    have h_const_ne : (1 + 2 * eLpNorm f 2 μ) ≠ ∞ := by
      apply ENNReal.add_ne_top.2
      constructor
      · simp
      · exact ENNReal.mul_ne_top (by simp) hf_ne
    have h_tend_mul :=
      ENNReal.Tendsto.const_mul h_tend' (Or.inr h_const_ne)
    simpa [mul_zero] using h_tend_mul
  refine
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds) h_mul_tend ?_ ?_)
  · filter_upwards with k
    exact (by simp)
  · filter_upwards [h_bound_add] with k hk
    have h_le := h_holder k
    have h_mul :
        eLpNorm (fun x => g k x - f x) 2 μ * eLpNorm (fun x => g k x + f x) 2 μ ≤
          eLpNorm (fun x => g k x - f x) 2 μ * (1 + 2 * eLpNorm f 2 μ) := by
      have h_mul' :=
        mul_le_mul_right hk (eLpNorm (fun x => g k x - f x) 2 μ)
      simpa [mul_comm] using h_mul'
    have h_mul' :
        eLpNorm (fun x => g k x - f x) 2 μ * eLpNorm (fun x => g k x + f x) 2 μ ≤
          (1 + 2 * eLpNorm f 2 μ) * eLpNorm (fun x => g k x - f x) 2 μ := by
      simpa [mul_comm] using h_mul
    exact le_trans h_le h_mul'
```

### child `phi_continuous`: [`SLT/GaussianLSI/OneDimGLSI.lean` lines 58-60](https://github.com/yuanhez/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/SLT/GaussianLSI/OneDimGLSI.lean#L58-L60) ([local copy](code/SLT/GaussianLSI/OneDimGLSI.lean))

```lean
lemma phi_continuous : Continuous phi := by
  change Continuous (fun t : ℝ => t * Real.log t)
  exact Real.continuous_mul_log
```

### child `mul_log_ge_neg_inv_exp`: [`SLT/GaussianLSI/OneDimGLSI.lean` lines 64-100](https://github.com/yuanhez/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/SLT/GaussianLSI/OneDimGLSI.lean#L64-L100) ([local copy](code/SLT/GaussianLSI/OneDimGLSI.lean))

```lean
lemma mul_log_ge_neg_inv_exp (t : ℝ) (ht : 0 ≤ t) : -(1 / Real.exp 1) ≤ t * Real.log t := by
  by_cases ht0 : t = 0
  · simp only [ht0, zero_mul]
    exact Left.neg_nonpos_iff.mpr (div_nonneg one_pos.le (Real.exp_pos 1).le)
  · have ht_pos : 0 < t := ht.lt_of_ne' ht0
    have hexp_pos : Real.exp 1 > 0 := Real.exp_pos 1
    by_cases ht1 : t > 1
    · have hlog_pos : Real.log t > 0 := Real.log_pos ht1
      have hprod_pos : t * Real.log t > 0 := mul_pos ht_pos hlog_pos
      have hexp_inv_pos : 1 / Real.exp 1 > 0 := div_pos one_pos hexp_pos
      linarith
    · push Not at ht1
      let u := Real.log t
      have ht_eq : t = Real.exp u := (Real.exp_log ht_pos).symm
      have hkey : u * Real.exp u ≥ -Real.exp (-1) := by
        have h : u + Real.exp (-1 - u) ≥ 0 := by
          have hbound : -1 - u + 1 ≤ Real.exp (-1 - u) := Real.add_one_le_exp (-1 - u)
          linarith
        have h_exp_div : Real.exp (-1) / Real.exp u = Real.exp (-1 - u) := by
          rw [← Real.exp_sub]
        have h_prod : u * Real.exp u + Real.exp (-1) ≥ 0 := by
          have h1 : u * Real.exp u + Real.exp (-1) =
              Real.exp u * (u + Real.exp (-1) / Real.exp u) := by field_simp
          rw [h1, h_exp_div]
          have h2 : Real.exp u * (u + Real.exp (-1 - u)) ≥ Real.exp u * 0 :=
            mul_le_mul_of_nonneg_left h (le_of_lt (Real.exp_pos u))
          simp at h2
          exact h2
        linarith
      have hinv_eq : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
      have hinv_eq' : (Real.exp 1)⁻¹ = 1 / Real.exp 1 := (one_div _).symm
      calc t * Real.log t = Real.exp u * Real.log (Real.exp u) := by rw [ht_eq]
        _ = Real.exp u * u := by rw [Real.log_exp u]
        _ = u * Real.exp u := by ring
        _ ≥ -Real.exp (-1) := hkey
        _ = -(Real.exp 1)⁻¹ := by rw [hinv_eq]
        _ = -(1 / Real.exp 1) := by rw [hinv_eq']
```

### child `gaussian_logSobolev_CompSmo_fderiv`: [`SLT/GaussianLSI/OneDimGLSICompSmo.lean` lines 94-97](https://github.com/yuanhez/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/SLT/GaussianLSI/OneDimGLSICompSmo.lean#L94-L97) ([local copy](code/SLT/GaussianLSI/OneDimGLSICompSmo.lean))

```lean
theorem gaussian_logSobolev_CompSmo_fderiv {f : ℝ → ℝ} (hf : CompactlySupportedSmooth f) :
    LogSobolev.entropy stdGaussianMeasure (fun x => (f x)^2) ≤
    2 * ∫ x, ‖fderiv ℝ f x‖^2 ∂stdGaussianMeasure := by
  simpa [deriv_sq_eq_norm_fderiv_sq] using (gaussian_logSobolev_CompSmo (f := f) hf)
```

### child `tendsto_eLpNorm_fderiv_sub_of_sobolev`: [`SLT/GaussianLSI/OneDimGLSI.lean` lines 250-289](https://github.com/yuanhez/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/SLT/GaussianLSI/OneDimGLSI.lean#L250-L289) ([local copy](code/SLT/GaussianLSI/OneDimGLSI.lean))

```lean
lemma tendsto_eLpNorm_fderiv_sub_of_sobolev (f : ℝ → ℝ) (g : ℕ → ℝ → ℝ) (μ : Measure ℝ)
    (hf_diff : Differentiable ℝ f) (hg_diff : ∀ k, Differentiable ℝ (g k))
    (h_tend : Tendsto (fun k => GaussianSobolevNormSqReal (f - g k) μ) atTop (nhds 0)) :
    Tendsto (fun k => eLpNorm (fun x => ‖fderiv ℝ f x - fderiv ℝ (g k) x‖) 2 μ)
      atTop (nhds 0) := by
  have h_tend_sq :
      Tendsto (fun k => eLpNorm (fun x => ‖fderiv ℝ (f - g k) x‖) 2 μ ^ 2) atTop (nhds 0) := by
    have h_le : ∀ k,
        eLpNorm (fun x => ‖fderiv ℝ (f - g k) x‖) 2 μ ^ 2 ≤
          GaussianSobolevNormSqReal (f - g k) μ := by
      intro k
      simp [GaussianSobolevNormSqReal]
    have h_nonneg : ∀ k, (0 : ℝ≥0∞) ≤ eLpNorm (fun x => ‖fderiv ℝ (f - g k) x‖) 2 μ ^ 2 := by
      intro k
      exact bot_le
    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        (g := fun _ => (0 : ℝ≥0∞))
        (h := fun k => GaussianSobolevNormSqReal (f - g k) μ)
        (tendsto_const_nhds) h_tend h_nonneg h_le
  have h_tend_grad :
      Tendsto (fun k => eLpNorm (fun x => ‖fderiv ℝ (f - g k) x‖) 2 μ) atTop (nhds 0) := by
    rw [ENNReal.tendsto_nhds_zero] at h_tend_sq ⊢
    intro ε hε
    have hε' : 0 < ε ^ 2 := by
      have hε0 : ε ≠ 0 := ne_of_gt hε
      simpa [pow_two] using ENNReal.mul_pos hε0 hε0
    have h_eventually := h_tend_sq (ε ^ 2) hε'
    filter_upwards [h_eventually] with k hk
    exact (ENNReal.pow_le_pow_left_iff (n := 2) (by decide)).1 hk
  refine h_tend_grad.congr' ?_
  filter_upwards with k
  have h_eq :
      (fun x => ‖fderiv ℝ (f - g k) x‖) =
        fun x => ‖fderiv ℝ f x - fderiv ℝ (g k) x‖ := by
    funext x
    have h_sub : fderiv ℝ (f - g k) x = fderiv ℝ f x - fderiv ℝ (g k) x := by
      exact fderiv_sub (hf_diff x) (hg_diff k x)
    simp [h_sub]
  simp [h_eq]
```

### child `exists_seq_tendsto_ae_of_tendsto_eLpNorm_one`: [`SLT/ConvergenceL1Subseq.lean` lines 15-24](https://github.com/yuanhez/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/SLT/ConvergenceL1Subseq.lean#L15-L24) ([local copy](code/SLT/ConvergenceL1Subseq.lean))

```lean
theorem exists_seq_tendsto_ae_of_tendsto_eLpNorm_one
    [NormedAddCommGroup E] {f : ℕ → α → E} {g : α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) mu)
    (hg : AEStronglyMeasurable g mu)
    (hfg : Tendsto (fun n => eLpNorm (f n - g) (1 : ENNReal) mu) atTop (nhds 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂mu, Tendsto (fun i => f (ns i) x) atTop (nhds (g x)) := by
  have h_in_measure : TendstoInMeasure mu f atTop g :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := (1 : ENNReal)) (by simp) hf hg hfg
  exact h_in_measure.exists_seq_tendsto_ae
```

### skill-text `vibe-recipe decomposition prompt`: [`vibe-recipe/EXAMPLE_INSTRUCTIONS.md` lines 108-316](https://github.com/yuanhez/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/vibe-recipe/EXAMPLE_INSTRUCTIONS.md#L108-L316) ([local copy](code/vibe-recipe/EXAMPLE_INSTRUCTIONS.md))

```markdown
## Target Theorem Statement

By `exists_smooth_compactSupport_seq_tendsto_real`, we can construct a sequence of smooth compactly supported functions $\{g_k\}_{k=1}^\infty \subset C_c^\infty(\mathbb{R})$ converging to any $f$ in the strong Gaussian Sobolev function class ($f\in W^{1,2}(\gamma)$ with $f\in C^1(\mathbb{R})$) in the 1D Gaussian Sobolev norm.

Your task is to extend the one-dimensional Gaussian logarithmic Sobolev inequality from twice-differentiable functions with compact support to strong Gaussian Sobolev function class ($f\in W^{1,2}(\gamma)$ with $f\in C^1(\mathbb{R})$).

**`STRONG` MEANS THE FUNCTION IS CONTINUOUSLY DIFFERENTIABLE**

Therefore, our **TARGET THEOREM** is:

> For any continuously differentiable ($f\in C^1$) function $f : \mathbb{R} \to \mathbb{R}$ with $f\in W^{1,2}(\gamma)$, we have
> $$\text{Ent}(f^2) \leq 2\mathbf{E}\left[\|\nabla f(X)\|^2\right].$$

---

## Optimal Proof for Formalization

### Step 1: Preliminaries about ($x\log x$), WELL-FORMALIZED

Define $\phi:[0,\infty)\to\mathbb R$ by $\phi(x)=x\log x$ (has been formalized as `def phi`).

#### Fact 1 (continuity)

$\phi$ is continuous on $[0,\infty)$. This has been formalized as `phi_continuous`.

#### Fact 2 (bounded below)

$$
\inf_{x\ge 0} \phi(x) = -\frac1e.
$$
Hence
$$
\phi(x)+\frac1e \ge 0\quad\text{for all }x\ge 0.
\tag{1}
$$
This “shift to nonnegativity” is what makes Fatou immediately applicable, which has been formalized in `mul_log_ge_neg_inv_exp`.

---

### Step 2: A subsequence lemma (from (L^{1}) to a.e.), WELL-FORMALIZED

#### Lemma (a.e. convergent subsequence)

Convergence in $L^1(\mu)$ yields an a.e.-convergent subsequence, has been formalized as `exists_seq_tendsto_ae_of_tendsto_eLpNorm_one` in SLT/ConvergenceL1Subseq.lean .

---

### Step 3: Lower semicontinuity of $\int g\log g$ via Fatou's lemma

**IMPORTANT: FROM HERE, WE WORK IN ENNREAL!!!**

#### Proposition (lower semicontinuity)

Assume $q_k\ge 0$ and $q_k\to q$ in $L^{1}(\gamma)$. Then
$$
\int \phi(q)\,d\gamma \le \liminf_{k\to\infty}\int \phi(q_k)\,d\gamma,
\quad\text{i.e.}\quad
\int q\log q\,d\gamma \le \liminf_{k\to\infty}\int q_k\log q_k\,d\gamma,
\tag{3}
$$
**allowing the value $+\infty$ on either side.** (We will set $q_k=g^2_k$, $q=f^2$ later)

##### Proof

Let
$$
L:=\liminf_{k\to\infty}\int \phi(q_k)\,d\gamma \in [-1/e,\infty].
$$
Choose a subsequence (still denoted $q_k$ for simplicity) such that
$$
\int \phi(q_k)\,d\gamma \to L.
\tag{4}
$$
(4) can be proven via:
Set
$$
a_k := \int \phi(q_k)\,d\mu \in \left[-\frac1e,\infty\right]\quad\text{where }\phi(x)=x\log x.
$$
Let
$$
L := \liminf_{k\to\infty} a_k \in \left[-\frac1e,\infty\right].
$$
If $L<\infty$, then there exists a subsequence $(a_{k_j}^*)_{j\ge1}$ such that
$$
a^*_{k_j}\to L.
$$
If $L=\infty$, then there is nothing to choose: “$\le \liminf$” is automatic whenever the right-hand side is $+\infty$.

Define the tail infima
$$
b_j := \inf_{k\ge j} a_k.
$$
Then $(b_j)$ is nondecreasing and $b_j\uparrow L$ by definition of $\liminf$.

For each $j$, by the definition of infimum, there exists some index $k_j\ge j$ such that
$$
a_{k_j} \le b_j + \frac1j.
$$
Then,
$$
b_j \le a_{k_j} \le b_j+\frac1j,
$$
so as $j\to\infty$,
$$
a_{k_j}\to L.
$$
This is the subsequence you used. It is a standard “almost minimizer of tail infimum” construction.

Given $q_k\to q$ in $L^{1}(\gamma)$, apply the lemma `exists_seq_tendsto_ae_of_tendsto_eLpNorm_one` to extract a **subsequence** such that $q_k\to q$ a.e.

By continuity of $\phi$ (Fact 1), we have $\phi(q_k)\to \phi(q)$ a.e., hence
$$
\phi(q) \le \liminf_{k\to\infty}\phi(q_k)\quad\text{a.e.}
\tag{5}
$$
Now shift to nonnegativity using (1): define
$$
h_k := \phi(q_k)+\frac1e \ge 0,\qquad h:=\phi(q)+\frac1e\ge 0.
$$
From (5), $$h \le \liminf_k h_k\quad a.e.$$
Fatou’s lemma for nonnegative functions **(`lintegral_liminf_le`!!!)** gives
$$
\int h\,d\gamma \le \liminf_{k\to\infty}\int h_k\,d\gamma.
$$
Subtract $1/e$ from both sides (note $\gamma$ is a probability measure, so $\int \tfrac1e d\gamma=\tfrac1e$) to get
$$
\int \phi(q)\,d\gamma \le \liminf_{k\to\infty}\int \phi(q_k)\,d\gamma.
$$
Using (4), the right-hand side equals $L$, which is $\liminf_{k}\int\phi(g_k)$. This proves (3). ∎

**Integrability remarks.**

* We did **not** assume $\phi(g_k)\in L^1$. If $\int \phi(g_k)=+\infty$ along a subsequence, Fatou still applies because $h_k\ge0$ and the integrals are allowed to be $+\infty$.
* The negative part is never a problem because $\phi\ge -1/e$; that is exactly why the shift works.

---

### Step 4: Lower semicontinuity of entropy

Define, for $q\ge0$,
$$
Ent(q)=\int q\log q\,d\gamma - m\log m,\qquad m:=\int q\,d\gamma.
$$

#### Corollary

If $q_k\ge0$ and $q_k\to q$ in $L^1(\gamma)$, then
$$
Ent(q) \le \liminf_{k\to\infty}Ent(q_k).
\tag{6}
$$

##### Proof

From $L^1$-convergence, $m_k:=\int q_k\,d\gamma \to \int q\,d\gamma = m$. The map $x\mapsto x\log x$ is continuous on $[0,\infty)$, so
$$
m_k\log m_k \to m\log m.
\tag{7}
$$
From the proposition,
$$
\int q\log q\,d\gamma \le \liminf_{k\to\infty} \int q_k\log q_k\,d\gamma.
\tag{8}
$$
Combine (7)–(8):
$$
Ent(q)
= \int q\log q\,d\gamma - m\log m
\le \liminf_k \int q_k\log q_k\,d\gamma - \lim_k m_k\log m_k
= \liminf_k Ent(q_k).
$$
∎

---

### Step 5: Application in Our Case

Take $q_k=f_k^2$ and $q=f^2$. So the corollary gives
$$
Ent(f^2)\le \liminf_{k\to\infty}Ent(g_k^2),
$$
which is the exact lower semicontinuity.

---

### Step 6: Back to Real Space

By `tendsto_integral_norm_fderiv_sq_of_sobolev` and `gaussian_logSobolev_CompSmo_fderiv`, we can obtain
$$
\liminf_{k\to\infty}Ent(g_k)
\le
\liminf_{k\to\infty} 2\int |\nabla g_k|^2\,d\gamma
=2\int |\nabla f|^2\,d\gamma
< \infty. \tag{*}
$$
Now combine (*) with

$$
Ent(f^2)\le \liminf_{k\to\infty}Ent(g_k^2),
$$

to get all finiteness, then we can convert back to real space.

---

### Step 7: Conclude the Limit

$$\text{Ent}(f^2) \leq 2\mathbf{E}\left[\|\nabla f(X)\|^2\right]$$
follows from results formalized, add the proof by yourself.
```

This is a theorem-scale instance of the `workflow` move. The **parent** `gaussian_logSobolev_W12_real` is the main theorem (the Gaussian LSI for W^{1,2} functions); its 525-line proof is the *glue*. The **skill-text** is the prompt (`EXAMPLE_INSTRUCTIONS.md` lines 108-316), which states the target once and pre-plans the proof as seven steps, each attached to a named project lemma before any tactic is written. The eight **children** below are the named project lemmas the glue cites directly, in the order the argument uses them:

1. `exists_smooth_compactSupport_seq_tendsto_real` (Density.lean) — the approximation: produces smooth compactly-supported `g_k` with `GaussianSobolevNormSqReal (f - g k) → 0`. The glue calls it at line 424.
2. `tendsto_eLpNorm_sub_of_sobolev` — Sobolev convergence ⇒ L² convergence of `g_k → f` (glue line 428).
3. `tendsto_eLpNorm_sq_sub_of_tendsto_L2` — L² convergence ⇒ L¹ convergence of the squares `g_k² → f²` (glue line 435).
4. `phi_continuous` and 5. `mul_log_ge_neg_inv_exp` — the two facts about the entropy density `φ(t) = t log t` (continuity, and the lower bound `φ ≥ -1/e`) that make Fatou's lemma applicable (glue lines 468, 701).
6. `gaussian_logSobolev_CompSmo_fderiv` — the known compact-support LSI, applied to each `g_k` (glue line 486).
7. `tendsto_eLpNorm_fderiv_sub_of_sobolev` — Sobolev convergence ⇒ L² convergence of the gradients (glue line 531).
8. `exists_seq_tendsto_ae_of_tendsto_eLpNorm_one` — L¹ convergence ⇒ an a.e.-convergent subsequence (glue line 670).

How each child is closed is recorded in `closed_by` in entry.json. Five further project lemmas are cited directly by the glue but are not shown as child sites (they are inlined helpers in `OneDimGLSI.lean` / `TaylorBound.lean`): `hasCompactSupport_sq` ([OneDimGLSI.lean 353-366](https://github.com/yuanhez/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/SLT/GaussianLSI/OneDimGLSI.lean#L353-L366), cited line 443), `integrable_phi_sq_of_compactSupport` ([386-396](https://github.com/yuanhez/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/SLT/GaussianLSI/OneDimGLSI.lean#L386-L396), cited line 461), `phi_add_inv_exp_nonneg` ([345-348](https://github.com/yuanhez/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/SLT/GaussianLSI/OneDimGLSI.lean#L345-L348), cited lines 687/693), `integrable_phi_sq_add_const` ([399-406](https://github.com/yuanhez/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/SLT/GaussianLSI/OneDimGLSI.lean#L399-L406), cited lines 761/830) and `TaylorBound.deriv_bounded_of_compactlySupported` ([TaylorBound.lean 200](https://github.com/yuanhez/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/SLT/GaussianPoincare/TaylorBound.lean#L200), cited line 498). That is 13 direct lemmas in all — see `shape.direct_lemmas`.

One notable divergence from the plan: the prompt's Step 6 names `tendsto_integral_norm_fderiv_sq_of_sobolev` as the gradient-convergence lemma, but the glue never cites it — it re-derives the same conclusion in place (lines 492-562) from `TaylorBound.deriv_bounded_of_compactlySupported`, `tendsto_eLpNorm_fderiv_sub_of_sobolev` and `tendsto_eLpNorm_sq_sub_of_tendsto_L2`. So the realized decomposition replaces the planned lemma with `tendsto_eLpNorm_fderiv_sub_of_sobolev`.

## Why it is good

The numbered claims below match `claims` in entry.json; kinds follow protocol §7.

1. *check* — The parent theorem `gaussian_logSobolev_W12_real` is declared in `SLT/GaussianLSI/OneDimGLSI.lean` within lines 415-939. ([permalink](https://github.com/yuanhez/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/SLT/GaussianLSI/OneDimGLSI.lean#L415-L419))
2. *check* — The parent site cites the child `gaussian_logSobolev_CompSmo_fderiv`. ([permalink](https://github.com/yuanhez/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/SLT/GaussianLSI/OneDimGLSI.lean#L486))
3. *check* — There is no sorry, admit or axiom in the parent site `SLT/GaussianLSI/OneDimGLSI.lean` lines 415-939. ([permalink](https://github.com/yuanhez/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/SLT/GaussianLSI/OneDimGLSI.lean#L415-L939))
4. *measurement* — The theorem-scale shape has 13 direct lemmas (8 shown as child sites of 37, 25, 116, 3, 37, 4, 40 and 10 lines), a parent glue of 525 lines, and a longest checked project-lemma chain of depth 2 (`gaussian_logSobolev_W12_real` → `gaussian_logSobolev_CompSmo_fderiv` → `gaussian_logSobolev_CompSmo`).
5. *author-statement* — The recipe's Step 1 instructs to "Decompose Proofs into Small Lemmas" ([vibe-recipe/README.md L18](https://github.com/yuanhez/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/vibe-recipe/README.md#L18)), and the prompt's Rule 2 defines success as "`lake build` passes + zero sorries + zero custom axioms" ([EXAMPLE_INSTRUCTIONS.md L323](https://github.com/yuanhez/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/vibe-recipe/EXAMPLE_INSTRUCTIONS.md#L323)).

*Opinion.* The workflow's strength is not the lemmas themselves (each is a routine analysis fact) but the discipline: it forces the plan to be written as a flat list of named lemmas before any tactic is typed, and it tells the agent to "solve one-by-one" and "fix errors one-by-one" rather than rewrite the proof. I read the recipe's "decompose into small lemmas" as a granularity rule of the same kind as survey-F §10 rule 14 ("target nearly trivial given parents"), with the agent's single-context-window completion (~300 lines) as its informal acceptance test in place of a hammer.

## When to use it, and when not

Use it when the target theorem can be pre-planned as a handful of named proof steps (approximation, convergence transfer, a known special case, a subsequence/liminf argument) and each step is small enough to state and prove as its own named project lemma within one agent context window (~300 lines). The move is a prompt: state the target once, attach each step to a named lemma before any tactic is written, then prove them one-by-one.

Do not use it when the steps do not separate into named lemmas (the glue is one monolithic tactic block), when a step is too large for one context window and cannot be split further, or when the glue needs a lemma the prompt names but never actually proves. Here `tendsto_integral_norm_fderiv_sq_of_sobolev` is named in Step 6 but the glue inlines its conclusion instead of citing it (OneDimGLSI.lean 492-562).

## Consequences

Obligations created: the glue must discharge each child's hypotheses in order — `exists_smooth_compactSupport_seq_tendsto_real` delivers `hg_smooth`/`hg_supp`/`h_sob_tend` (line 424); `tendsto_eLpNorm_sub_of_sobolev` consumes `h_sob_tend` (line 428); `tendsto_eLpNorm_sq_sub_of_tendsto_L2` needs continuity and `MemLp` of `f` plus the L² convergence (line 435); `gaussian_logSobolev_CompSmo_fderiv` needs `CompactlySupportedSmooth (g k)`, rebuilt from `hg_smooth`/`hg_supp` (lines 476-481); `tendsto_eLpNorm_fderiv_sub_of_sobolev` needs differentiability plus `h_sob_tend` (line 531); `exists_seq_tendsto_ae_of_tendsto_eLpNorm_one` needs the L¹ convergence of `qk - q` (line 670). The lemmas therefore close only bottom-up.

Failure modes: a planned lemma the realization does not cite (Step 6's `tendsto_integral_norm_fderiv_sq_of_sobolev`), and a side condition delivered only by a later step (the L¹ convergence of squares needs the L² convergence first), which breaks the one-by-one order if the steps are attempted top-down.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: exists_smooth_compactSupport_seq_tendsto_real@SLT/GaussianLSI/OneDimGLSI.lean:424, tendsto_eLpNorm_sub_of_sobolev@SLT/GaussianLSI/OneDimGLSI.lean:428, tendsto_eLpNorm_sq_sub_of_tendsto_L2@SLT/GaussianLSI/OneDimGLSI.lean:435, phi_continuous@SLT/GaussianLSI/OneDimGLSI.lean:701, mul_log_ge_neg_inv_exp@SLT/GaussianLSI/OneDimGLSI.lean:468, gaussian_logSobolev_CompSmo_fderiv@SLT/GaussianLSI/OneDimGLSI.lean:486, tendsto_eLpNorm_fderiv_sub_of_sobolev@SLT/GaussianLSI/OneDimGLSI.lean:531, exists_seq_tendsto_ae_of_tendsto_eLpNorm_one@SLT/GaussianLSI/OneDimGLSI.lean:670; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(gaussian_logSobolev_W12_real, SLT/GaussianLSI/OneDimGLSI.lean, 415-939) -> declared: gaussian_logSobolev_W12_real is declared at SLT/GaussianLSI/OneDimGLSI.lean:415 | check_claims.py |
| 2 | verified | cites(parent, gaussian_logSobolev_CompSmo_fderiv) -> cites: gaussian_logSobolev_CompSmo_fderiv occurs at SLT/GaussianLSI/OneDimGLSI.lean:486 | check_claims.py |
| 3 | verified | no_sorry(SLT/GaussianLSI/OneDimGLSI.lean, 415-939) -> no_sorry: none of sorry, admit, axiom in SLT/GaussianLSI/OneDimGLSI.lean:415-939 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/yuanhez/lean-stat-learning-theory at commit `d0f506f0a695018265dccb33bcb05e2f5ca1c876`, under `Apache-2.0`; see the [source note](../../sources/lean-stat-learning-theory/SOURCE.md) for the licence text and attribution.
