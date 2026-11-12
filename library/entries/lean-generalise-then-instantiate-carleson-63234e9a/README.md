# Instantiate the abstract discrete Carleson theorem to prove finitary Carleson (Proposition 2.0.1)

| | |
|---|---|
| Kind | instance |
| Move | generalise-then-instantiate |
| Language | lean |
| Status | accepted |
| Source | [carleson](../../sources/carleson/SOURCE.md) at `d75f54374f7f` |
| Licence | `Apache-2.0` |

## Intent

The headline Proposition 2.0.1 states the finitary Carleson bound for a concrete
per-scale tile sum. The proof reduces it to the already-proved abstract theorem
`discrete_carleson`, which is stated over the typeclass `[TileStructure Q D κ S o]`
and in terms of the abstract operator `carlesonSum`. Two structure instantiations
(`grid_existence`, `tile_existence`) supply the concrete instances, and one
rewrite lemma (`tile_sum_operator`) unfolds `carlesonSum` into the concrete sum
over scales, so the only thing left for the glue is a unit-norm phase factor.

## The decomposition

### parent `finitary_carleson`: [`Carleson/FinitaryCarleson.lean` lines 110-124](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/FinitaryCarleson.lean#L110-L124) ([local copy](code/Carleson/FinitaryCarleson.lean))

```lean
theorem finitary_carleson : ∃ G', MeasurableSet G' ∧ 2 * volume G' ≤ volume G ∧
    ∀ f : X → ℂ, Measurable f → (∀ x, ‖f x‖ ≤ F.indicator 1 x) →
    ∫⁻ x in G \ G', ‖∑ s ∈ Icc (σ₁ x) (σ₂ x), ∫ y, Ks s x y * f y * exp (I * Q x y)‖ₑ ≤
    C2_0_1 a nnq * (volume G) ^ (1 - q⁻¹) * (volume F) ^ q⁻¹ := by
  have g : GridStructure X D κ S o := grid_existence X
  have t : TileStructure Q D κ S o := tile_existence X
  clear g
  rcases discrete_carleson X with ⟨G', hG', h2G', hfG'⟩
  refine ⟨G', hG', h2G', fun f meas_f h2f ↦ le_of_eq_of_le ?_ (hfG' f meas_f h2f)⟩
  refine setLIntegral_congr_fun (measurableSet_G.diff hG') fun x hx ↦ ?_
  simp_rw [carlesonSum, mem_univ, Finset.filter_true, tile_sum_operator hx, mul_sub, exp_sub,
    mul_div, div_eq_mul_inv,
    ← smul_eq_mul, integral_smul_const, ← Finset.sum_smul, _root_.enorm_smul]
  suffices ‖(cexp (I • ((Q x) x : ℂ)))⁻¹‖ₑ = 1 by rw [this, mul_one]
  simp [mul_comm I, enorm_eq_nnnorm]
```

### child `discrete_carleson`: [`Carleson/Discrete/MainTheorem.lean` lines 43-68](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/Discrete/MainTheorem.lean#L43-L68) ([local copy](code/Carleson/Discrete/MainTheorem.lean))

```lean
variable (X) in
theorem discrete_carleson :
    ∃ G', MeasurableSet G' ∧ 2 * volume G' ≤ volume G ∧
    ∀ f : X → ℂ, Measurable f → (∀ x, ‖f x‖ ≤ F.indicator 1 x) →
    ∫⁻ x in G \ G', ‖carlesonSum univ f x‖ₑ ≤
    C2_0_2 a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ := by
  have exc := exceptional_set (X := X)
  rw [zpow_neg_one, ← ENNReal.div_eq_inv_mul] at exc
  use G', measurable_G', ENNReal.mul_le_of_le_div' exc; intro f measf hf
  classical
  calc
    _ ≤ ∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ f x‖ₑ + ‖carlesonSum 𝔓₁ᶜ f x‖ₑ := by
      refine setLIntegral_mono (by fun_prop) fun x _ ↦ ?_
      rw [carlesonSum, ← Finset.sum_filter_add_sum_filter_not _ (· ∈ 𝔓₁ (X := X))]
      simp_rw [Finset.filter_filter, mem_univ, true_and, carlesonSum, mem_compl_iff]
      apply enorm_add_le
    _ = (∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ f x‖ₑ) + ∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ᶜ f x‖ₑ :=
      lintegral_add_left (by fun_prop) _
    _ ≤ C5_1_2 a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ +
        C5_1_3 a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ :=
      add_le_add (forest_union hf measf) (forest_complement hf measf)
    _ ≤ _ := by
      simp_rw [mul_assoc, ← add_mul]
      gcongr
      norm_cast
      apply le_C2_0_2 (four_le_a X) (q_mem_Ioc X)
```

### child `grid_existence`: [`Carleson/TileExistence.lean` lines 1571-1652](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/TileExistence.lean#L1571-L1652) ([local copy](code/Carleson/TileExistence.lean))

```lean
variable (X) in
/-- Proof that there exists a grid structure. -/
@[implicit_reducible]
def grid_existence : GridStructure X D κ S o where
  Grid := 𝓓 X
  fintype_Grid := @Fintype.ofFinite (𝓓 X) (𝓓_finite X)
  coeGrid := fun z => z.coe
  s := fun z => z.k
  c := fun z => z.y
  inj := fun ⟨k,hk,hk_max,y,hsub⟩ ⟨k2,hk2,hk2_max,y2,hsub'⟩ h => by
    simp only [Prod.mk.injEq, 𝓓.mk.injEq] at h hsub hsub' ⊢
    dsimp [𝓓.coe] at h hsub hsub'
    obtain ⟨hl, hr⟩ := h
    subst hr
    simp only [heq_eq_eq, true_and]
    apply I3_prop_1 hk2 (x := y)
    rw [← hl]
    simp only [inter_self]
    apply I3_prop_3_1
    simpa using by positivity [realD_pos a]
  range_s_subset i := by
    push _ ∈ _
    simp only [forall_exists_index]
    rintro x rfl
    use x.hk, x.hk_max
  topCube := max_𝓓 X
  s_topCube := rfl
  c_topCube := rfl
  subset_topCube := by
    intro i
    exact i.hsub
  Grid_subset_biUnion := by
    intro i l hl
    simp only [mem_Ico] at hl
    push _ ∈ _
    have : i.coe ⊆ (max_𝓓 X).coe := i.hsub
    intro x hx
    simp only [mem_iUnion, exists_prop]
    have : i.coe ⊆ ⋃ y', I3 hl.left y' := cover_by_cubes hl.left hl.right.le i.hk i.y
    specialize this hx
    simp only [mem_iUnion] at this
    obtain ⟨y', hy'⟩ := this
    have : I3 (hl.left) y' ⊆ (max_𝓓 X).coe := by
      apply dyadic_property
      · exact hl.right.le.trans i.hk_max
      · rw [Set.not_disjoint_iff]
        exact ⟨x, hy', this hx⟩
    use ⟨l,hl.left,hl.right.le.trans i.hk_max,y',this⟩
    simpa only [true_and]
  fundamental_dyadic' := by
    intro i j hk
    by_cases h : Disjoint i.coe j.coe
    · exact Or.inr h
    · exact Or.inl (dyadic_property i.hk hk j.hk j.y i.y h)
  ball_subset_Grid := by
    intro i
    apply Subset.trans (ball_subset_ball _) (I3_prop_3_1 i.hk i.y)
    rw [div_eq_mul_inv,mul_comm]
    gcongr
    norm_num
  Grid_subset_ball {i} := I3_prop_3_2 i.hk i.y
  small_boundary := by
    intro i t ht
    by_cases ht' : t < 1
    · apply boundary_measure' i.hk i.y
      · simp only [mem_Ioo]
        refine ⟨?_, ht'⟩
        apply lt_of_lt_of_le (zpow_pos (realD_pos a) _) ht
      rw [zpow_sub₀, div_le_iff₀] at ht
      · exact ht
      · exact zpow_pos (realD_pos a) _
      apply LT.lt.ne'
      exact realD_pos a
    · trans volume.real i.coe
      · apply measureReal_mono (sep_subset _ _) <|
          volume.mono (I3_prop_3_2 i.hk i.y) |>.trans_lt _ |>.ne
        simp only [OuterMeasure.measureOf_eq_coe, Measure.coe_toOuterMeasure]
        exact measure_ball_lt_top
      apply le_mul_of_one_le_left (measureReal_nonneg)
      have : 1 ≤ (t : ℝ) ^ κ := Real.one_le_rpow (le_of_not_gt ht') κ_nonneg
      linarith
  coeGrid_measurable {i} := I3_measurableSet i.hk i.y
```

### child `tile_existence`: [`Carleson/TileExistence.lean` lines 2009-2021](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/TileExistence.lean#L2009-L2021) ([local copy](code/Carleson/TileExistence.lean))

```lean
variable (X) in
set_option backward.isDefEq.respectTransparency false in
@[implicit_reducible] def tile_existence : TileStructure Q D κ S o where
  Ω := Construction.Ω
  biUnion_Ω {I} := by rw [← SimpleFunc.coe_range]; exact Construction.Ω_biUnion
  disjoint_Ω := Construction.Ω_disjoint
  relative_fundamental_dyadic {p q} := Construction.Ω_RFD
  cball_subset {p} := by
    rw [Construction.Ω]; split_ifs with h
    · have : ball_(p) (𝒬 p) 5⁻¹ ⊆ ball_(p) (𝒬 p) C𝓩 := ball_subset_ball (by norm_num)
      exact this.trans (Construction.ball_subset_Ω₁ p)
    · simp
  subset_cball {p} := Construction.Ω_subset_cball
```

### child `tile_sum_operator`: [`Carleson/FinitaryCarleson.lean` lines 69-98](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/FinitaryCarleson.lean#L69-L98) ([local copy](code/Carleson/FinitaryCarleson.lean))

```lean
/-- Lemma 4.0.3 -/
theorem tile_sum_operator {G' : Set X} {f : X → ℂ} {x : X} (hx : x ∈ G \ G') :
    ∑ (p : 𝔓 X), carlesonOn p f x =
    ∑ s ∈ Icc (σ₁ x) (σ₂ x), ∫ y, Ks s x y * f y * exp (I * (Q x y - Q x x)) := by
  classical
  rw [𝔓_biUnion, Finset.sum_biUnion]; swap
  · exact fun s _ s' _ hss' A hAs hAs' p pA ↦ False.elim <| hss' (𝔰_eq (hAs pA) ▸ 𝔰_eq (hAs' pA))
  rw [← (Icc (-S : ℤ) S).toFinset.sum_filter_add_sum_filter_not (fun s ↦ s ∈ Icc (σ₁ x) (σ₂ x))]
  rw [Finset.sum_eq_zero sum_eq_zero_of_notMem_Icc, add_zero]
  refine Finset.sum_congr (Finset.ext fun s ↦ ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩) (fun s hs ↦ ?_)
  · rw [Finset.mem_filter, ← mem_toFinset] at hs
    exact hs.2
  · rw [mem_toFinset] at hs
    rw [toFinset_Icc, Finset.mem_filter]
    exact ⟨Finset.mem_Icc.2 (Icc_σ_subset_Icc_S hs), hs⟩
  · rcases exists_Grid hx.1 hs with ⟨I, Is, xI⟩
    obtain ⟨p, 𝓘pI, Qp⟩ : ∃ (p : 𝔓 X), 𝓘 p = I ∧ Q x ∈ Ω p := by simpa using! biUnion_Ω ⟨x, rfl⟩
    have p𝔓Xs : p ∈ 𝔓X_s s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [𝔰, 𝓘pI]; exact Is⟩
    have : ∀ p' ∈ 𝔓X_s s, p' ≠ p → carlesonOn p' f x = 0 := by
      intro p' p'𝔓Xs p'p
      apply indicator_of_notMem
      simp only [E, mem_ofPred_eq, not_and]
      refine fun x_in_𝓘p' Qp' ↦ False.elim ?_
      have s_eq := 𝔰_eq p𝔓Xs ▸ 𝔰_eq p'𝔓Xs
      have : ¬ Disjoint (𝓘 p' : Set X) (𝓘 p : Set X) := not_disjoint_iff.2 ⟨x, x_in_𝓘p', 𝓘pI ▸ xI⟩
      exact disjoint_left.1 (disjoint_Ω p'p <| Or.resolve_right (eq_or_disjoint s_eq) this) Qp' Qp
    rw [Finset.sum_eq_single_of_mem p p𝔓Xs this]
    have xEp : x ∈ E p :=
      ⟨𝓘pI ▸ xI, Qp, by simpa only [toFinset_Icc, Finset.mem_Icc, 𝔰_eq p𝔓Xs] using! hs⟩
    simp_rw [carlesonOn_def', indicator_of_mem xEp, 𝔰_eq p𝔓Xs]
```

How the parts fit. The glue proves the concrete Proposition 2.0.1 in four steps,
one per child:

1. `have g : GridStructure X D κ S o := grid_existence X` (line 114) then
   `clear g` (line 116) registers the concrete grid as the `GridStructure`
   instance. The `clear g` is the Lean idiom for "add this term as an instance
   and forget the name": typeclass synthesis picks it up from then on.
2. `have t : TileStructure Q D κ S o := tile_existence X` (line 115) registers
   the concrete tile structure, which is built *on top of* the grid of step 1 —
   its `TileStructure` instance needs a `GridStructure` (see the `extends` in the
   excerpt of `TileStructure` above).
3. `rcases discrete_carleson X with ⟨G', hG', h2G', hfG'⟩` (line 117) applies the
   abstract theorem, which requires `[TileStructure …]` (supplied by step 2). It
   returns the exceptional set `G'` with `hG' : MeasurableSet G'` and
   `h2G' : 2 * volume G' ≤ volume G`, and the abstract bound `hfG'` stated in
   terms of `carlesonSum univ f x`. The first two goals of the parent are closed
   verbatim by `hG'` and `h2G'` (line 118); only the bound needs work.
4. `simp_rw [carlesonSum, …, tile_sum_operator hx, …]` (lines 120-122) unfolds the
   abstract `carlesonSum univ` to `∑ p, carlesonOn p` and applies
   `tile_sum_operator hx` to rewrite it to the concrete per-scale sum. The
   trailing `suffices` (line 123) absorbs the leftover phase factor
   `exp (I * Q x x)`, whose `‖·‖ₑ` is 1 (line 124), so the concrete phase
   `exp (I * Q x y)` in the target is reached from `tile_sum_operator`'s
   `exp (I * (Q x y - Q x x))`.

The lemma graph, one arrow per "uses":

    finitary_carleson ──► grid_existence      (supplies GridStructure)
                      ──► tile_existence      (supplies TileStructure; needs GridStructure)
                      ──► discrete_carleson   (abstract bound over [TileStructure])
                      ──► tile_sum_operator   (carlesonSum ≐ per-scale sum)

    discrete_carleson ──► exceptional_set, forest_union, forest_complement, le_C2_0_2
    tile_sum_operator ──► 𝔓_biUnion, sum_eq_zero_of_notMem_Icc, 𝔰_eq, exists_Grid,
                          biUnion_Ω, disjoint_Ω
    exists_Grid        ──► G_subset, ball_subset_Grid, Grid_subset_biUnion
    grid_existence     ──► cover_by_cubes, dyadic_property, I3_prop_3_1, …

Why each child is a good leaf. `discrete_carleson` is the whole Carleson estimate
abstracted away from any concrete grid; it closes on its own from the forest
lemmas (`exceptional_set`, `forest_union`, `forest_complement`). `grid_existence`
and `tile_existence` are self-contained constructions of the two structures; each
field is closed by a named geometric lemma and none depends on the parent's goal.
`tile_sum_operator` is the single interface lemma between the abstract
`carlesonSum` and the concrete per-scale integral; it closes from private set
lemmas and the `biUnion_Ω`/`disjoint_Ω` tile axioms, so the parent never unfolds
`carlesonOn` itself.

## Why it is good

1. The parent `finitary_carleson`'s proof body (lines 114-124, 11 lines) closes
   from exactly four named project facts — `grid_existence`, `tile_existence`,
   `discrete_carleson`, `tile_sum_operator` — with no `sorry` or `axiom`
   (`check`; the file is type-checked by the project's CI, `.github/workflows/push.yml`).
2. The authors mark the instantiation in the docstrings: `finitary_carleson` is
   "/-- Proposition 2.0.1 -/" (line 109), `discrete_carleson`'s section header is
   "Proposition 2.0.2" (`MainTheorem.lean` line 14), and the constant `C2_0_1` is
   literally defined as `C2_0_2` (line 104) with the docstring "The constant used
   in Proposition 2.0.1. Has value `2 ^ (442 * a ^ 3) / (q - 1) ^ 5` in the
   blueprint." — the concrete proposition reuses the abstract proposition's
   constant (`author-statement`).
3. The theorem-scale shape is `direct_lemmas = 4`, `glue_lines = 11`, `depth = 4`,
   `child_lines = [20, 78, 10, 26]`; counted as proof-body lines of the copied
   files (see the measurement claim) (`measurement`).
4. The same generalise-then-instantiate move is recorded in three other pilot-2
   entries (compfiles, mathlib4, sphere-packing), so it is a recurring Lean
   pattern rather than a one-off (`known-use`).

In my opinion the detail worth copying is the *layering* of the instantiation:
`grid_existence` → `TileStructure` (via `tile_existence`) → `discrete_carleson`,
with the abstract-to-concrete rewrite confined to the single lemma
`tile_sum_operator`. That keeps the headline glue to four `have`/`rcases`/`simp_rw`
lines, and it is the shape AutoDecompose's skeleton is meant to produce. This is
recorded against survey F §10 rule 15 ("shallow and wide … keeping proved nodes"):
the headline decomposition is shallow (depth 1 to its four direct lemmas), and all
the depth is pushed into named, previously-proved lemmas that a replan would keep.

## When to use it, and when not

Use it when a general statement over a typeclass or weaker structure is already
proved (`discrete_carleson`), the concrete setting provides instances of that
structure (`grid_existence`, `tile_existence`), and the abstract notion in the
general statement rewrites into the concrete one by a single named lemma
(`tile_sum_operator`) up to a unit-norm phase. The key precondition is that the
concrete statement is a genuine *specialisation* — same shape, concrete operator
in place of the abstract one — so that the glue is `have`/`rcases`/`simp_rw` and
not new mathematics.

Avoid it when no general theorem exists yet (then "instantiation" is really
re-proving the general theorem, and you should first write that general theorem);
when the concrete-to-abstract rewrite is itself a deep proof rather than a routine
unfold (`tile_sum_operator` is a 26-line lemma, not a `simp` lemma — its existence
is a prerequisite, not a by-product); or when the concrete statement differs from
the abstract one by more than a definitional rewrite plus a removable unit phase,
which will break the single `simp_rw` step.

## Consequences

The move shifts all the work out of the concrete theorem. The obligations it
creates are exactly the four children: build the `GridStructure` instance
(`grid_existence`), build the `TileStructure` instance on top of it
(`tile_existence`), prove the abstract bound over `[TileStructure]`
(`discrete_carleson`), and prove the abstract-to-concrete rewrite
(`tile_sum_operator`). Each is a substantial, self-contained proof — `grid_existence`
alone is 78 proof lines and `discrete_carleson` bottoms out in the forest estimates
`forest_union`/`forest_complement` — but none mentions the parent's goal.

The glue itself is nearly definitional; its only non-routine step is removing the
constant phase factor `exp (-I · Q x x)`, whose `‖·‖ₑ` is shown to be 1 by the
`suffices` at line 123. The failure mode is a mismatch: if the concrete target's
operator differs from `carlesonSum` by more than unfolding plus a unit-norm phase,
the `simp_rw` at line 120 will not close, and either the abstract theorem must be
re-generalised or a new rewrite lemma proved. This entry also illustrates the
risk the survey calls "reject identity" (F §10 rule 13): `discrete_carleson` is
*not* smaller than the parent — it is the same statement one level of abstraction
up — so this is a valid move only because `discrete_carleson` is a *previously
proved* theorem being reused, not a child being proved afresh.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push.yml builds the whole Carleson project (leanprover/lean-action build:true, build-args 'Carleson Challenge Solution', mk_all-check true --lib Carleson) on push to master; pinned commit d75f54374f7f930e70a86b443f20d0e0935c275e is the current HEAD of master (default branch, confirmed via GitHub API) | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 7 file(s) byte-identical at d75f54374f7f930e70a86b443f20d0e0935c275e | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Opened code/Carleson/FinitaryCarleson.lean: proof body lines 114-124 (11 lines) uses grid_existence (l.114), tile_existence (l.115), discrete_carleson (l.117), tile_sum_operator (l.120); grep over code/ finds no sorry/axiom (only a comment 'axioms:' in TileStructure.lean l.53). CI .github/workflows/push.yml builds the project. | verifier |
| 2 | verified | Opened code copies: FinitaryCarleson.lean l.109 '/-- Proposition 2.0.1 -/', l.102-104 docstring 'The constant used in Proposition 2.0.1...' + 'def C2_0_1 (a) (q) := C2_0_2 a q'; Discrete/MainTheorem.lean l.14 '/-! ## Proposition 2.0.2 -/'. | verifier |
| 3 | verified | Counted from code copies: parent proof 114-124 = 11 lines; children discrete_carleson 49-68 = 20, grid_existence 1575-1652 = 78, tile_existence 2012-2021 = 10, tile_sum_operator 73-98 = 26; depth chain: tile_sum_operator hx (FinitaryCarleson:120) -> exists_Grid (:84) -> ball_subset_Grid/Grid_subset_biUnion (:61,67) -> cover_by_cubes/dyadic_property (TileExistence:1609,1614) = 4 edges. | verifier |
| 4 | verified | Opened entry.json of lean-generalise-then-instantiate-compfiles-f96a55bd, -mathlib4-57b9f5e4, -sphere-packing-9e03f73b: all three exist and have move 'generalise-then-instantiate'. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Decomposition matches the code: finitary_carleson (FinitaryCarleson.lean:110-113) instantiates discrete_carleson X (l.117) via the two structure instances grid_existence X (l.114) and tile_existence X (l.115), then rewrites carlesonSum into the per-scale tile sum with tile_sum_operator hx (l.120). The 4 children are exactly the facts the glue uses directly, and each closed_by field matches its proof: discrete_carleson's calc steps use exceptional_set/forest_union/forest_complement/le_C2_0_2 (MainTheorem.lean:49-68); grid_existence builds each GridStructure field from the cited lemmas (TileExistence.lean:1574-1652); tile_existence takes all six TileStructure fields from Construction.Ω* (TileExistence.lean:2011-2021); tile_sum_operator uses 𝔓_biUnion/sum_eq_zero_of_notMem_Icc/𝔰_eq/exists_Grid/biUnion_Ω/disjoint_Ω (FinitaryCarleson.lean:70-98). The proof closes: body 114-124 has no sorry/axiom and the final suffices+simp (l.123-124) closes the phase-factor goal. Shape numbers are right: direct_lemmas=4, glue_lines=11 (114-124), child_lines=[20,78,10,26] = proof bodies 49-68, 1575-1652, 2012-2021, 73-98, and depth=4 along finitary_carleson→tile_sum_operator→exists_Grid→Grid_subset_biUnion→cover_by_cubes/dyadic_property (TileExistence.lean:1609,1614). | reviewer-correctness |
| generality | accept | Generality: the move is stated beyond the example — use_when/avoid_when (entry.json applicability; README 'When to use it, and when not') give the general preconditions (a general statement over a typeclass/weaker structure already proved; concrete instances supplied; abstract notion rewrites to concrete by one named lemma up to a unit phase), not just a recounting of this proof, and known_uses cites three other pilot-2 entries. 'When not to use' and consequences are honest and specific: it names the three negative conditions and is self-aware that tile_sum_operator is a 26-line lemma (a prerequisite, not a by-product), states the work is shifted not removed, and flags the reject-identity subtlety (discrete_carleson is the same statement one abstraction up, valid only as reuse of a previously-proved theorem). It says what makes the children good leaves: the dedicated 'Why each child is a good leaf' subsection gives self-containedness, closure by named lemmas, independence from the parent's goal, and a single interface lemma so the parent never unfolds carlesonOn, while honestly noting their sizes (78/20/10/26 proof lines). | reviewer-generality |
| provenance-licence | accept | check_provenance passes: all 7 files byte-identical at d75f54374f7f930e70a86b443f20d0e0935c275e. entry.json source.commit/url/source_id match library/sources/carleson/source.json and SOURCE.md (same commit, https://github.com/fpvandoorn/carleson). Licence Apache-2.0 is consistent across entry.json, source.json, SOURCE.md, and upstream-LICENSE (which is the Apache License 2.0 text). All site permalink line ranges match the copied code: finitary_carleson L110-124, tile_sum_operator L69-98, C2_0_1 def L104 with docstring L102-103, discrete_carleson L43-68 with 'Proposition 2.0.2' header at L14, grid_existence L1571-1652, tile_existence L2009-2021. All permalinks pin the same commit. Everything traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/fpvandoorn/carleson at commit `d75f54374f7f930e70a86b443f20d0e0935c275e`, under `Apache-2.0`; see the [source note](../../sources/carleson/SOURCE.md) for the licence text and attribution.
