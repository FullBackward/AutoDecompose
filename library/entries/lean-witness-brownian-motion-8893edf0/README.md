# Witness pair (S - A, A) for the Doob-Meyer decomposition of a cadlag class D submartingale

| | |
|---|---|
| Kind | instance |
| Move | witness |
| Language | lean |
| Status | accepted |
| Source | [brownian-motion](../../sources/brownian-motion/SOURCE.md) at `8fd8dc52830c` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T12:12:06Z |

## Intent

Prove the Doob-Meyer decomposition — every càdlàg submartingale of class D
is the sum of a càdlàg martingale and a predictable, càdlàg, monotone
increasing process vanishing at `⊥` — by constructing the two witnesses
`M := S - A` and `A := G.indicator L` (the limsup of convex step extensions,
restricted to a good set `G` of full measure) and discharging each conjunct
of the resulting existence statement from the martingale-part and
predictable-part lemmas.

## The decomposition

### parent `ProbabilityTheory.ClassD.doob_meyer`: [`BrownianMotion/StochasticIntegral/DoobMeyer.lean` lines 2901-2954](https://github.com/RemyDegenne/brownian-motion/blob/8fd8dc52830cdd07cf9cc8eadd533e284425fa6f/BrownianMotion/StochasticIntegral/DoobMeyer.lean#L2901-L2954) ([local copy](code/BrownianMotion/StochasticIntegral/DoobMeyer.lean))

```lean
theorem ProbabilityTheory.ClassD.doob_meyer {ι Ω : Type*} [CompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] [MeasurableSpace ι]
    [BorelSpace ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : ι → Ω → ℝ}
    {𝓕 : Filtration ι mΩ} [𝓕.IsRightContinuous] [𝓕.IsComplete P]
    (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (hc : ∀ ω, IsCadlag (S · ω)) :
    ∃ (M A : ι → Ω → ℝ), S = M + A ∧ Martingale M 𝓕 P ∧ (∀ ω, IsCadlag (M · ω)) ∧
      IsStronglyPredictable 𝓕 A ∧ (∀ ω, IsCadlag (A · ω)) ∧ (∀ ω, Monotone (A · ω)) ∧
      A ⊥ = 0 := by
  have hc' : ∀ᵐ ω ∂P, IsCadlag (S · ω) := .of_forall hc
  -- the limsup process `L` and the good set `G`, whose complement is a null set
  let L : ι → Ω → ℝ := fun t ω ↦ limsup (predictableConvexStep hd hs · t ω) atTop
  have hL : IsStronglyPredictable 𝓕 L := isStronglyPredictable_limsup_predictableConvexStep hd hs
  let G : Set Ω := {ω | (∀ t, L t ω = predictablePartLim hd hs t ω) ∧
    Monotone (predictablePartLim hd hs · ω) ∧ IsCadlag (predictablePartLim hd hs · ω)}
  have hG_ae : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [limsup_predictableConvexStep_eq_predictablePartLim hd hs hc',
      predictablePartLim_monotone_ae hd hs hc', isCadlag_predictablePartLim_ae hd hs hc']
      with ω h1 h2 h3 using ⟨h1, h2, h3⟩
  have hN_null : P Gᶜ = 0 := hG_ae
  have hG_meas (t : ι) : MeasurableSet[𝓕 t] G :=
    (Filtration.IsComplete.measurableSet_of_null hN_null t).of_compl
  -- the predictable part `A` and its values on `G` and `Gᶜ`
  let A : ι → Ω → ℝ := fun t ↦ G.indicator (L t)
  have hA_mem {ω : Ω} (hω : ω ∈ G) (t : ι) : A t ω = predictablePartLim hd hs t ω := by
    simp only [A, Set.indicator_of_mem hω, hω.1 t]
  have hA_notMem {ω : Ω} (hω : ω ∉ G) (t : ι) : A t ω = 0 := Set.indicator_of_notMem hω _
  have hA_pred : IsStronglyPredictable 𝓕 A := by
    have h_eq : Function.uncurry A = (Set.univ ×ˢ G).indicator (Function.uncurry L) := by
      ext ⟨t, ω⟩
      by_cases hω : ω ∈ G <;> simp [A, hω]
    rw [IsStronglyPredictable, h_eq]
    exact StronglyMeasurable.indicator hL (measurableSet_predictable_univ_prod (hG_meas ⊥))
  have hM_mem {ω : Ω} (hω : ω ∈ G) (t : ι) : (S - A) t ω = martingalePartLim hd hs t ω := by
    simp only [Pi.sub_apply, hA_mem hω t, predictablePartLim, sub_sub_cancel]
  have hA_bot : A ⊥ = 0 := by
    have hL_bot : L ⊥ = 0 := by
      funext ω
      simp [L, predictableConvexStep_bot]
    simp [A, hL_bot]
  refine ⟨S - A, A, (sub_add_cancel S A).symm, ?_, fun ω ↦ ?_, hA_pred, fun ω ↦ ?_, fun ω ↦ ?_,
    hA_bot⟩
  · refine (martingale_martingalePartLim hd hs).congr ?_ ?_
    · exact fun t ↦ (hs.stronglyAdapted t).sub (hA_pred.stronglyAdapted t)
    · intro t
      filter_upwards [hG_ae] with ω hω using (hM_mem hω t).symm
  · by_cases hω : ω ∈ G
    · simpa only [hM_mem hω] using isCadlag_martingalePartLim hd hs ω
    · simpa only [Pi.sub_apply, hA_notMem hω, sub_zero] using hc ω
  · by_cases hω : ω ∈ G
    · simpa only [hA_mem hω] using hω.2.2
    · simpa only [hA_notMem hω] using IsCadlag.const (X := ι) (c := (0 : ℝ))
  · by_cases hω : ω ∈ G
    · simpa only [hA_mem hω] using hω.2.1
    · simpa only [hA_notMem hω] using monotone_const (α := ι) (c := (0 : ℝ))
```

### child `isCadlag_martingalePartLim`: [`BrownianMotion/StochasticIntegral/DoobMeyer.lean` lines 1524-1526](https://github.com/RemyDegenne/brownian-motion/blob/8fd8dc52830cdd07cf9cc8eadd533e284425fa6f/BrownianMotion/StochasticIntegral/DoobMeyer.lean#L1524-L1526) ([local copy](code/BrownianMotion/StochasticIntegral/DoobMeyer.lean))

```lean
lemma isCadlag_martingalePartLim (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (ω : Ω) :
    IsCadlag (martingalePartLim hd hs · ω) :=
  isCadlag_cadlagModifReal ω
```

### child `martingale_martingalePartLim`: [`BrownianMotion/StochasticIntegral/DoobMeyer.lean` lines 1542-1551](https://github.com/RemyDegenne/brownian-motion/blob/8fd8dc52830cdd07cf9cc8eadd533e284425fa6f/BrownianMotion/StochasticIntegral/DoobMeyer.lean#L1542-L1551) ([local copy](code/BrownianMotion/StochasticIntegral/DoobMeyer.lean))

```lean
lemma martingale_martingalePartLim [𝓕.IsRightContinuous] [𝓕.IsComplete P]
    (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) :
    Martingale (martingalePartLim hd hs) 𝓕 P := by
  refine ⟨stronglyAdapted_martingalePartLim hd hs, fun i j hij ↦ ?_⟩
  calc P[martingalePartLim hd hs j | 𝓕 i]
      =ᵐ[P] P[P[martingaleLim hd hs | 𝓕 j] | 𝓕 i] :=
        condExp_congr_ae (martingalePartLim_ae_eq hd hs j)
    _ =ᵐ[P] P[martingaleLim hd hs | 𝓕 i] :=
        (martingale_condExp (martingaleLim hd hs) 𝓕 P).condExp_ae_eq hij
    _ =ᵐ[P] martingalePartLim hd hs i := (martingalePartLim_ae_eq hd hs i).symm
```

### child `isCadlag_predictablePartLim_ae`: [`BrownianMotion/StochasticIntegral/DoobMeyer.lean` lines 1635-1642](https://github.com/RemyDegenne/brownian-motion/blob/8fd8dc52830cdd07cf9cc8eadd533e284425fa6f/BrownianMotion/StochasticIntegral/DoobMeyer.lean#L1635-L1642) ([local copy](code/BrownianMotion/StochasticIntegral/DoobMeyer.lean))

```lean
lemma isCadlag_predictablePartLim_ae {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P)
    (hs : Submartingale S 𝓕 P) (hc : ∀ᵐ ω ∂P, IsCadlag (S · ω)) :
    ∀ᵐ ω ∂P, IsCadlag (predictablePartLim hd hs · ω) := by
  filter_upwards [hc] with ω hω
  exact hω.sub (isCadlag_martingalePartLim hd hs ω)
```

### child `predictablePartLim_monotone_ae`: [`BrownianMotion/StochasticIntegral/DoobMeyer.lean` lines 2275-2284](https://github.com/RemyDegenne/brownian-motion/blob/8fd8dc52830cdd07cf9cc8eadd533e284425fa6f/BrownianMotion/StochasticIntegral/DoobMeyer.lean#L2275-L2284) ([local copy](code/BrownianMotion/StochasticIntegral/DoobMeyer.lean))

```lean
lemma predictablePartLim_monotone_ae {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
    [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} [𝓕.IsRightContinuous]
    (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (hc : ∀ᵐ ω ∂P, IsCadlag (S · ω)) :
    ∀ᵐ ω ∂P, Monotone fun t ↦ predictablePartLim hd hs t ω := by
  filter_upwards [predictablePartLim_monotoneOn_denseSet_ae hd hs,
    isRightContinuous_predictablePartLim_ae hd hs hc] with ω hmono hrcω
  exact (denseSet_dense ι).monotone_of_isRightContinuous (fun _ ↦ mem_denseSet_of_nhdsGT_eq_bot)
    (fun s t hst ↦ hmono s.2 t.2 hst) hrcω
```

### child `isStronglyPredictable_limsup_predictableConvexStep`: [`BrownianMotion/StochasticIntegral/DoobMeyer.lean` lines 2352-2358](https://github.com/RemyDegenne/brownian-motion/blob/8fd8dc52830cdd07cf9cc8eadd533e284425fa6f/BrownianMotion/StochasticIntegral/DoobMeyer.lean#L2352-L2358) ([local copy](code/BrownianMotion/StochasticIntegral/DoobMeyer.lean))

```lean
lemma isStronglyPredictable_limsup_predictableConvexStep {ι Ω : Type*} [TopologicalSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [LinearOrder ι] [OrderBot ι]
    [OrderTop ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} (hd : ClassD S 𝓕 P)
    (hs : Submartingale S 𝓕 P) :
    IsStronglyPredictable 𝓕 (fun t ω => limsup (predictableConvexStep hd hs · t ω) atTop) :=
  IsStronglyPredictable.limsup fun n => isStronglyPredictable_predictableConvexStep hd hs n
```

### child `predictableConvexStep_bot`: [`BrownianMotion/StochasticIntegral/DoobMeyer.lean` lines 2656-2659](https://github.com/RemyDegenne/brownian-motion/blob/8fd8dc52830cdd07cf9cc8eadd533e284425fa6f/BrownianMotion/StochasticIntegral/DoobMeyer.lean#L2656-L2659) ([local copy](code/BrownianMotion/StochasticIntegral/DoobMeyer.lean))

```lean
lemma predictableConvexStep_bot (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (n : ℕ) :
    predictableConvexStep hd hs n ⊥ = 0 := by
  funext ω
  simp [predictableConvexStep, Finsupp.sum, Finset.sum_apply, predictableSeqStep_bot]
```

### child `limsup_predictableConvexStep_eq_predictablePartLim`: [`BrownianMotion/StochasticIntegral/DoobMeyer.lean` lines 2854-2894](https://github.com/RemyDegenne/brownian-motion/blob/8fd8dc52830cdd07cf9cc8eadd533e284425fa6f/BrownianMotion/StochasticIntegral/DoobMeyer.lean#L2854-L2894) ([local copy](code/BrownianMotion/StochasticIntegral/DoobMeyer.lean))

```lean
lemma limsup_predictableConvexStep_eq_predictablePartLim {ι : Type*} [CompleteLinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] [MeasurableSpace ι]
    [BorelSpace ι] {S : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ} [𝓕.IsRightContinuous] [𝓕.IsComplete P]
    (hd : ClassD S 𝓕 P) (hs : Submartingale S 𝓕 P) (hc : ∀ᵐ ω ∂P, IsCadlag (S · ω)) :
    ∀ᵐ ω ∂P, ∀ t, limsup (predictableConvexStep hd hs · t ω) atTop =
      predictablePartLim hd hs t ω := by
  -- the début theorem below is stated for Polish spaces
  have : PolishSpace ι := .of_compactSpace_of_secondCountableTopology
  set L : ι → Ω → ℝ := fun t ω ↦ limsup (predictableConvexStep hd hs · t ω) atTop
  set A : ι → Ω → ℝ := predictablePartLim hd hs
  -- the set `B k` of times at which `A - L > 1 / (k + 1)` is progressively measurable
  have hAL : IsStronglyProgressive 𝓕 (fun t ω ↦ A t ω - L t ω) :=
    (isStronglyProgressive_predictablePartLim hd hs).sub
      (isStronglyPredictable_limsup_predictableConvexStep hd hs).isStronglyProgressive
  let B (k : ℕ) : Set (ι × Ω) := {p | 1 / ((k : ℝ) + 1) < A p.1 p.2 - L p.1 p.2}
  have hB (k : ℕ) : ProgMeasurableSet (B k) 𝓕 := measurableSet_Ioi.progMeasurableSet_preimage hAL
  -- hence its début, truncated at `⊤`, is a finite stopping time, at which `L` and `A` coincide
  let σ (k : ℕ) : Ω → WithTop ι := fun ω ↦ min (debut (B k) ⊥ ω) ((⊤ : ι) : WithTop ι)
  have hσ (k : ℕ) : IsStoppingTime 𝓕 (σ k) :=
    (isStoppingTime_debut P (hB k) ⊥).min (isStoppingTime_const 𝓕 ⊤)
  have hσ_ne (k : ℕ) (ω : Ω) : σ k ω ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)
  have h_eq : ∀ᵐ ω ∂P, ∀ k, L (σ k ω).untopA ω = A (σ k ω).untopA ω := ae_all_iff.2 fun k ↦
    limsup_stoppedValue_predictableConvexStep_ae_eq_stoppedValue_predictablePartLim hd hs (hσ k)
      (hσ_ne k) hc
  filter_upwards [h_eq, limsup_predictableConvexStep_le_predictablePartLim_ae hd hs hc,
    finite_setOf_lt_predictablePartLim_sub_limsup_predictableConvexStep_ae hd hs hc]
    with ω h_eq h_le h_fin t
  refine le_antisymm (h_le t) (not_lt.1 fun h_lt ↦ ?_)
  -- if `L t ω < A t ω` then some `B k` has a nonempty and finite section at `ω`, which contains
  -- its début: a contradiction since `L` and `A` coincide at the début
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 h_lt)
  have hex : ∃ s ≥ ⊥, (s, ω) ∈ B k := ⟨t, bot_le, hk⟩
  have hmem : ((debut (B k) ⊥ ω).untopA, ω) ∈ B k :=
    debut_mem_set_of_finite ((h_fin _ (by positivity)).subset fun s hs ↦ hs.2) hex
  have hσ_eq : σ k ω = debut (B k) ⊥ ω :=
    min_eq_left (WithTop.le_coe_top.2 (debut_ne_top_iff.2 hex))
  have h_eq' := h_eq k
  rw [hσ_eq] at h_eq'
  simp only [B, Set.mem_ofPred_eq, h_eq', sub_self] at hmem
  exact absurd hmem (not_lt.2 (by positivity))
```

### child `measurableSet_predictable_univ_prod`: [`BrownianMotion/StochasticIntegral/Predictable.lean` lines 129-134](https://github.com/RemyDegenne/brownian-motion/blob/8fd8dc52830cdd07cf9cc8eadd533e284425fa6f/BrownianMotion/StochasticIntegral/Predictable.lean#L129-L134) ([local copy](code/BrownianMotion/StochasticIntegral/Predictable.lean))

```lean
lemma measurableSet_predictable_univ_prod {s : Set Ω} (hs : MeasurableSet[𝓕 ⊥] s) :
    MeasurableSet[𝓕.predictable] (univ ×ˢ s) := by
  rw [(by simp : univ = {⊥} ∪ Ioi ⊥), union_prod]
  refine MeasurableSet.union ?_ ?_
  · exact measurableSet_predictable_singleton_bot_prod hs
  · exact measurableSet_predictable_Ioi_prod hs
```

How the parts fit. The theorem is an existence statement, and the glue
constructs two witnesses then proves each conjunct. The candidate predictable
part is `L`, the limsup of the convex step extensions
`predictableConvexStep`; the candidate martingale part is `S - A`. The
witnesses are fixed only on a good set `G` of full measure and filled in
trivially off it:

- `have hL : IsStronglyPredictable 𝓕 L := isStronglyPredictable_limsup_predictableConvexStep`
  (child `isStronglyPredictable_limsup_predictableConvexStep`).
- `have hG_ae : ∀ᵐ ω ∂P, ω ∈ G` is assembled by `filter_upwards` from three
  children that give, almost everywhere, `L = predictablePartLim`
  (`limsup_predictableConvexStep_eq_predictablePartLim`), monotonicity
  (`predictablePartLim_monotone_ae`) and càdlàg paths
  (`isCadlag_predictablePartLim_ae`) of `predictablePartLim`.
- The witness `A := G.indicator L` is strongly predictable by
  `StronglyMeasurable.indicator hL (measurableSet_predictable_univ_prod ...)`
  (child `measurableSet_predictable_univ_prod`), and satisfies `A ⊥ = 0` by
  `predictableConvexStep_bot`.
- The `refine ⟨S - A, A, (sub_add_cancel S A).symm, ...⟩` closes the
  existence. The martingale conjunct is
  `(martingale_martingalePartLim hd hs).congr ...` (child
  `martingale_martingalePartLim`); càdlàg paths of `S - A` follow from
  `isCadlag_martingalePartLim` on `G` and from `hc` off `G`.

The lemma graph (direct edges among the children and the parent's glue):

```
doob_meyer (glue)
 ├─ martingale_martingalePartLim                          (martingale conjunct)
 ├─ isCadlag_martingalePartLim                            (cadlag of M on G)
 ├─ isCadlag_predictablePartLim_ae                        (cadlag of A on G, via hG_ae)
 ├─ predictablePartLim_monotone_ae                        (monotone of A on G, via hG_ae)
 ├─ isStronglyPredictable_limsup_predictableConvexStep    (predictability of L)
 ├─ predictableConvexStep_bot                             (A ⊥ = 0)
 ├─ limsup_predictableConvexStep_eq_predictablePartLim    (L = A on G)
 └─ measurableSet_predictable_univ_prod                   (predictability of A = indicator on G)

children used by other children (below the glue):
 isCadlag_predictablePartLim_ae  ──uses──▶  isCadlag_martingalePartLim
 limsup_predictableConvexStep_eq_predictablePartLim  ──uses──▶  isStronglyPredictable_limsup_predictableConvexStep
```

Why each child is a good leaf — a self-contained statement whose proof closes
on its own or from named siblings:

- `isCadlag_martingalePartLim` closes in one line from `isCadlag_cadlagModifReal`.
- `martingale_martingalePartLim` closes from `stronglyAdapted_martingalePartLim`
  (adaptedness) plus a `calc` of conditional expectations (the tower property).
- `isCadlag_predictablePartLim_ae` closes from its sibling
  `isCadlag_martingalePartLim` by `hω.sub`.
- `predictablePartLim_monotone_ae` closes from
  `predictablePartLim_monotoneOn_denseSet_ae` and
  `isRightContinuous_predictablePartLim_ae` (monotone on a dense set +
  right-continuous).
- `isStronglyPredictable_limsup_predictableConvexStep` closes by
  `IsStronglyPredictable.limsup` over `isStronglyPredictable_predictableConvexStep`.
- `predictableConvexStep_bot` closes by `simp` with `predictableSeqStep_bot`.
- `limsup_predictableConvexStep_eq_predictablePartLim` is the deep leaf: a
  début-time argument (`le_antisymm` + `debut_mem_set_of_finite`) that `L` and
  `predictablePartLim` are indistinguishable.
- `measurableSet_predictable_univ_prod` closes by rewriting
  `univ = {⊥} ∪ Ioi ⊥` and using the singleton and interval predictable-set
  lemmas.

## Why it is good

1. The parent `ProbabilityTheory.ClassD.doob_meyer` is declared in
   [`BrownianMotion/StochasticIntegral/DoobMeyer.lean` lines 2901-2954](https://github.com/RemyDegenne/brownian-motion/blob/8fd8dc52830cdd07cf9cc8eadd533e284425fa6f/BrownianMotion/StochasticIntegral/DoobMeyer.lean#L2901-L2954)
   (`check`, `declared`).
2. The glue cites the martingale-part lemma `martingale_martingalePartLim`
   ([line 2942](https://github.com/RemyDegenne/brownian-motion/blob/8fd8dc52830cdd07cf9cc8eadd533e284425fa6f/BrownianMotion/StochasticIntegral/DoobMeyer.lean#L2942))
   (`check`, `cites`).
3. The glue cites the predictable-part lemma
   `limsup_predictableConvexStep_eq_predictablePartLim`
   ([line 2916](https://github.com/RemyDegenne/brownian-motion/blob/8fd8dc52830cdd07cf9cc8eadd533e284425fa6f/BrownianMotion/StochasticIntegral/DoobMeyer.lean#L2916))
   (`check`, `cites`).
4. No `sorry`/`admit`/`Admitted`/`axiom` token appears in the parent's range
   (lines 2901-2954) (`check`, `no_sorry`).
5. The glue is 54 lines, against 89 lines across the eight children (3 + 10 + 8
   + 10 + 7 + 4 + 41 + 6) (`check`, `lines`; the per-child counts are the
   `shape.child_lines`).
6. The authors name the theorem in its docstring: "**Doob–Meyer
   decomposition** of a càdlàg submartingale of class D."
   ([line 2900](https://github.com/RemyDegenne/brownian-motion/blob/8fd8dc52830cdd07cf9cc8eadd533e284425fa6f/BrownianMotion/StochasticIntegral/DoobMeyer.lean#L2900))
   (`author-statement`).
7. The longest checked chain of project lemmas below `doob_meyer` has length 4:
   `martingale_martingalePartLim` → `stronglyAdapted_martingalePartLim` →
   `stronglyAdapted_cadlagModifReal` → `stronglyAdapted_cadlagModifOf`
   (`measurement`; each link read at the pinned commit — see entry.json claim 7).

In my opinion the move worth copying is the split of the witnesses by the good
set: `A := G.indicator L` makes the hard part (`A` is predictable, càdlàg,
monotone, and vanishes at `⊥`) hold for free on `G` where the earlier lemmas
apply, and the `by_cases hω : ω ∈ G` branches reduce the complement of `G` to
the constant zero process, so the glue never has to re-prove a path property
away from `G`.

## When to use it, and when not

Use it when an existence goal's witnesses factor through objects whose
properties are already proved in separate lemmas (here the martingale-part and
predictable-part lemmas), so each conjunct of the existence statement is one
lemma and the glue only splices them onto the chosen witnesses. Use it when the
witness is canonical: `martingalePartLim` and `predictablePartLim` are fixed by
the submartingale, so the off-`G` branches only have to fall back to the zero
process.

Avoid it when the witnesses are not canonical or their properties are not
already lemmatised — then each conjunct needs a fresh argument in the glue, and
a witness that serves one conjunct may fail the next. Avoid it when the
existence statement is too weak to pin down a witness, or when the good set
does not have full measure, which would force the complement branches to carry
real content instead of the trivial zero-process fallback.

## Consequences

The move turns one existence goal into one obligation per conjunct of the
body, each discharged against a chosen witness. The witnesses `M := S - A` and
`A := G.indicator L` must be chosen so that every conjunct is a lemma already
proved about that object: the martingale property comes from
`martingale_martingalePartLim`; path regularity and monotonicity of `A` come
from the definition of the good set `G`, whose complement is null via
`limsup_predictableConvexStep_eq_predictablePartLim`,
`predictablePartLim_monotone_ae` and `isCadlag_predictablePartLim_ae`; and
`A ⊥ = 0` comes from `predictableConvexStep_bot`.

Failure modes: picking a witness that satisfies some conjuncts but not others
(e.g. a predictable part that is not monotone off the good set), or a good set
that is not of full measure, which forces the `by_cases hω : ω ∈ G` branches to
prove the properties from scratch for the zero process instead of falling back
to it.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/blueprint.yml builds the project (lean-action build:true lint:true) on pushes/PRs to master; commit 8fd8dc52830cdd07cf9cc8eadd533e284425fa6f on default branch master | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: isCadlag_martingalePartLim@BrownianMotion/StochasticIntegral/DoobMeyer.lean:2947, martingale_martingalePartLim@BrownianMotion/StochasticIntegral/DoobMeyer.lean:2942, isCadlag_predictablePartLim_ae@BrownianMotion/StochasticIntegral/DoobMeyer.lean:2917, predictablePartLim_monotone_ae@BrownianMotion/StochasticIntegral/DoobMeyer.lean:2917, isStronglyPredictable_limsup_predictableConvexStep@BrownianMotion/StochasticIntegral/DoobMeyer.lean:2912, predictableConvexStep_bot@BrownianMotion/StochasticIntegral/DoobMeyer.lean:2938, limsup_predictableConvexStep_eq_predictablePartLim@BrownianMotion/StochasticIntegral/DoobMeyer.lean:2916, measurableSet_predictable_univ_prod@BrownianMotion/StochasticIntegral/DoobMeyer.lean:2932; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at 8fd8dc52830cdd07cf9cc8eadd533e284425fa6f | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): BrownianMotion/StochasticIntegral/DoobMeyer.lean:2970 (sorry) | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(ProbabilityTheory.ClassD.doob_meyer, BrownianMotion/StochasticIntegral/DoobMeyer.lean, 2901-2954) -> declared: ProbabilityTheory.ClassD.doob_meyer is declared at BrownianMotion/StochasticIntegral/DoobMeyer.lean:2901 | check_claims.py |
| 2 | verified | cites(parent, martingale_martingalePartLim) -> cites: martingale_martingalePartLim occurs at BrownianMotion/StochasticIntegral/DoobMeyer.lean:2942 | check_claims.py |
| 3 | verified | cites(parent, limsup_predictableConvexStep_eq_predictablePartLim) -> cites: limsup_predictableConvexStep_eq_predictablePartLim occurs at BrownianMotion/StochasticIntegral/DoobMeyer.lean:2916 | check_claims.py |
| 4 | verified | no_sorry(BrownianMotion/StochasticIntegral/DoobMeyer.lean, 2901-2954) -> no_sorry: none of sorry, admit, axiom in BrownianMotion/StochasticIntegral/DoobMeyer.lean:2901-2954 | check_claims.py |
| 5 | verified | lines(parent, 54) -> lines: site parent has 54 lines | check_claims.py |
| 6 | verified | DoobMeyer.lean line 2900 docstring reads '/-- **Doob–Meyer decomposition** of a càdlàg submartingale of class D. -/' | verifier |
| 7 | verified | chain of 4 checked: doob_meyer cites martingale_martingalePartLim at DoobMeyer.lean:2942; martingale_martingalePartLim cites stronglyAdapted_martingalePartLim at :1545; stronglyAdapted_martingalePartLim cites stronglyAdapted_cadlagModifReal at :1538; stronglyAdapted_cadlagModifReal cites stronglyAdapted_cadlagModifOf at CadlagModification.lean:1410 | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Provenance pass (2 files byte-identical at 8fd8dc52830cdd07cf9cc8eadd533e284425fa6f). Parent doob_meyer at DoobMeyer.lean 2901-2954 matches README excerpt and entry.json statement verbatim; docstring line 2900 confirms the Doob-Meyer name. All 8 children read at their cited ranges match code and entry statements/closing methods: isCadlag_martingalePartLim 1524-1526 (=isCadlag_cadlagModifReal), martingale_martingalePartLim 1542-1551 (refine/calc), isCadlag_predictablePartLim_ae 1635-1642 (hω.sub), predictablePartLim_monotone_ae 2275-2284, isStronglyPredictable_limsup_predictableConvexStep 2352-2358, predictableConvexStep_bot 2656-2659, limsup_predictableConvexStep_eq_predictablePartLim 2854-2894 (le_antisymm/debut), measurableSet_predictable_univ_prod Predictable.lean 129-134. Glue cites all 8 (each conjunct discharged; refine ⟨S-A,A,...⟩ closes 7 conjuncts; no sorry/admit/axiom in 2901-2954). Shape numbers correct: direct_lemmas=8, glue_lines=54 (2954-2901+1), child_lines=[3,10,8,10,7,4,41,6] each matching its site length; depth=4 consistent with claim 7 chain (martingale_martingalePartLim@1545 -> stronglyAdapted_martingalePartLim@1535/1538 -> stronglyAdapted_cadlagModifReal). Children are exactly the project lemmas the glue uses. | reviewer-correctness |
| generality | accept | Move is stated beyond the example: applicability/use-when abstracts to 'existence goal whose witnesses factor through objects with already-proved properties' plus a canonical witness, and the good-set trick (A := G.indicator L) is generalised to 'full-measure good set + trivial zero fallback'. When-not-to-use is honest and specific: non-canonical/unlemmatised witnesses, too-weak existence statement, and non-full-measure good set forcing real content in the complement branches. Consequences name concrete failure modes (a predictable part not monotone off G; G not full measure). The 'Why each child is a good leaf' section answers the bounded-prover question: each child is self-contained and closes in one line or from named siblings (verified against the copied code: isCadlag_martingalePartLim one-liner, martingale_martingalePartLim calc, sibling reuse via hω.sub, simp closes), and the one deep leaf (limsup_predictableConvexStep_eq_predictablePartLim, 41 lines, debut-time) is flagged so a bounded prover knows to budget more there. No generality objection. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are mutually consistent and traceable. All 9 site permalinks and both file permalinks pin commit 8fd8dc52830cdd07cf9cc8eadd533e284425fa6f, matching source.json, sources/brownian-motion/SOURCE.md and entry.json source.commit. check_provenance.py passes: 2 files byte-identical at that commit. sha256 of the copied DoobMeyer.lean and Predictable.lean match entry.json files[].sha256. Licence is Apache-2.0 consistently in entry.json, README, SOURCE.md, source.json, and upstream-LICENSE is the Apache License 2.0 text. Source note names the right repo (RemyDegenne/brownian-motion), commit, licence files, and attribution. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/RemyDegenne/brownian-motion at commit `8fd8dc52830cdd07cf9cc8eadd533e284425fa6f`, under `Apache-2.0`; see the [source note](../../sources/brownian-motion/SOURCE.md) for the licence text and attribution.
