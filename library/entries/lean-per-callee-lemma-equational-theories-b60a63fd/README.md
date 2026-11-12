# Per-component enlargement lemmas assemble the greedy chain for equation 1729 not implying 817

| | |
|---|---|
| Kind | instance |
| Move | per-callee-lemma |
| Language | lean |
| Status | verified |
| Source | [equational-theories](../../sources/equational-theories/SOURCE.md) at `8b87204d5b20` |
| Licence | `Apache-2.0` |

## Intent

The existence of a magma satisfying equation 1729 but not 817 is reduced to a
greedy chain over a task indexed by the three-component sum `N ⊕ N ⊕ (N × N)`,
seeded by `TrivialPartialSolution` and turned into a magma by `use_chain`.
The glue is a dispatch over those three components, and each component is
closed by its own, near-identical enlargement lemma.

## The decomposition

### parent `not_817`: [`equational_theories/ManuallyProved/Equation1729.lean` lines 14-43](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/ManuallyProved/Equation1729.lean#L14-L43) ([local copy](code/equational_theories/ManuallyProved/Equation1729.lean))

```lean
@[equational_result]
theorem not_817 : ∃ (G: Type) (_: Magma G), Equation1729 G ∧ ¬ Equation817 G := by
  let β := N ⊕ N ⊕ (N × N)
  let task : β → Set PartialSolution := fun s => match s with
    | Sum.inl x => { sol | x ∈ fill sol.Predom_L₀' }
    | Sum.inr (Sum.inl x) => { sol | x ∈ sol.Dom_S' }
    | Sum.inr (Sum.inr (x,y)) => { sol | (x,y) ∈ sol.Dom_op }
  have := exists_greedy_chain task ?_ TrivialPartialSolution
  . obtain ⟨ sols, hchain, hnon, _, h ⟩ := this
    apply use_chain hchain
    . rw [nonempty_subtype]
      use TrivialPartialSolution
    . intro x
      exact h (Sum.inl x)
    . intro x
      exact h (Sum.inr (Sum.inl x))
    intro x y
    exact h (Sum.inr (Sum.inr (x,y)))
  intro sol b
  match b with
  | Sum.inl x =>
      simp only [Set.mem_setOf_eq, task]
      obtain ⟨sol', hsol', hx_sol', _⟩ := enlarge_L₀' sol x
      exact ⟨sol', hsol', hx_sol'⟩
  | Sum.inr (Sum.inl x) =>
      simp only [Set.mem_setOf_eq, task]
      exact enlarge_S' sol x
  | Sum.inr (Sum.inr (x,y)) =>
      simp only [Set.mem_setOf_eq, task]
      exact enlarge_op sol x y
```

### child `TrivialPartialSolution`: [`equational_theories/ManuallyProved/Equation1729/MagmaConstruction.lean` lines 56-108](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/ManuallyProved/Equation1729/MagmaConstruction.lean#L56-L108) ([local copy](code/equational_theories/ManuallyProved/Equation1729/MagmaConstruction.lean))

```lean
def TrivialPartialSolution : PartialSolution := {
  L₀' := fun _ ↦ 1
  op := fun _ ↦ fun _ ↦ Sum.inl 0
  S' := fun _ ↦ 0
  I := Finset.empty
  Predom_L₀' := Finset.empty
  Dom_op := Finset.empty
  Dom_S' := Finset.empty
  axiom_i'' := by
    intro _ _ h
    contrapose! h
    exact Finset.notMem_empty _
  axiom_S := by
    intro _ _ h
    contrapose! h
    exact Finset.notMem_empty _
  axiom_iii'' := by
    intro _ _ _ h
    contrapose! h
    exact Finset.notMem_empty _
  axiom_iv'' := by
    intro _ h
    contrapose! h
    exact Finset.notMem_empty _
  axiom_v'' := by
    intro _ h
    contrapose! h
    exact Finset.notMem_empty _
  axiom_vi'' := by
    intro _ _ h
    contrapose! h
    exact Finset.notMem_empty _
  axiom_vii'' := by
    intro _ _ _ _ h
    contrapose! h
    exact Finset.notMem_empty _
  axiom_P := by
    intro _ _ _ h
    contrapose! h
    exact Finset.notMem_empty _
  axiom_P' := by
    intro _ _ _ _ h
    contrapose! h
    exact Finset.notMem_empty _
  axiom_P'' := by
    intro _ _ _ h
    contrapose! h
    exact Finset.notMem_empty _
  axiom_L := by
    intro _ _ _ _ _ h
    contrapose! h
    simp
}
```

### child `use_chain`: [`equational_theories/ManuallyProved/Equation1729/MagmaConstruction.lean` lines 135-205](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/ManuallyProved/Equation1729/MagmaConstruction.lean#L135-L205) ([local copy](code/equational_theories/ManuallyProved/Equation1729/MagmaConstruction.lean))

```lean
lemma use_chain {sols : Set PartialSolution} (hchain: IsChain (fun (sol1 sol2 : PartialSolution) => sol1 ≤ sol2) sols ) (hnon: Nonempty sols) (htotal_L₀' : ∀ x : N, ∃ sol ∈ sols, x ∈ sol.Dom_L₀') (htotal_S' : ∀ x : N, ∃ sol ∈ sols, x ∈ sol.Dom_S') (htotal_op : ∀ (x y : N), ∃ sol ∈ sols, (x,y) ∈ sol.Dom_op) : ∃ (G: Type) (_: Magma G), Equation1729 G ∧ ¬ Equation817 G := by
  let f := Filter.atTop (α := sols)
  have fnon : f.NeBot := Filter.atTop_neBot_iff.mpr ⟨hnon, IsChain.IsDirected hchain⟩
  let S' (x : N) := (Set.choose (htotal_S' x)).1.S' x
  have S'_lim (x : N) : ∀ᶠ sol in f, x ∈ sol.1.Dom_S' ∧ sol.1.S' x = S' x := by
    set sol := Set.choose (htotal_S' x)
    set sol_spec := Set.choose_spec (htotal_S' x)
    apply Filter.Eventually.mono (Filter.eventually_ge_atTop sol)
    exact fun _ h ↦ ⟨h.2.2.1 sol_spec, (h.2.2.2.2.2 x sol_spec).symm⟩
  let op (x y:N) := (Set.choose (htotal_op x y)).1.op x y
  have op_lim (x y:N) : ∀ᶠ sol in f, (x,y) ∈ sol.1.Dom_op ∧ sol.1.op x y = op x y := by
    set sol := Set.choose (htotal_op x y)
    set sol_spec := Set.choose_spec (htotal_op x y)
    apply Filter.Eventually.mono (Filter.eventually_ge_atTop sol)
    exact fun _ h ↦ ⟨h.2.1 sol_spec, (h.2.2.2.2.1 (x,y) sol_spec).symm⟩
  classical -- didn't want to deal with a Decidable issue
  let L₀' (x : N) := (Set.choose (htotal_L₀' x)).1.L₀' x
  have L₀'_lim (x : N) : ∀ᶠ sol in f, x ∈ fill sol.1.Predom_L₀' ∧ sol.1.L₀' x = L₀' x := by
    set sol := Set.choose (htotal_L₀' x)
    set sol_spec := Set.choose_spec (htotal_L₀' x)
    apply Filter.Eventually.mono (Filter.eventually_ge_atTop sol)
    exact fun _ h ↦ ⟨fill_mono h.1 sol_spec , (h.2.2.2.1 x sol_spec).symm⟩
  apply @reduce_to_new_axioms S' L₀' op
  · ext x
    apply (Filter.eventually_const (f := f)).mp
    filter_upwards [L₀'_lim x, L₀'_lim (L₀' x)] with sol h1 h2
    obtain ⟨y, ⟨m, hx⟩, hy⟩ := h1.1
    change L₀' (L₀' x) = (e 0)⁻¹ * x
    have := sol.1.axiom_i'' y (sol.1.L₀' y) hy rfl m
    rw [← h2.2, ←h1.2, hx, this.2.1, this.2.2, <-mul_assoc]
    congr
    group
  · intro a x y h
    apply (Filter.eventually_const (f := f)).mp
    filter_upwards [L₀'_lim ((R' (S (a - S' x))) y), L₀'_lim ((R' (S (S' y))) ((R' (a - S' x)).symm (L₀' ((R' (S (a - S' x))) y)))), S'_lim x, S'_lim y] with sol h1 h2 h3 h4
    rw [← h2.2, ← h1.2, ← h3.2, ← h4.2]
    exact (sol.1.axiom_iii'' x y a h3.1 h4.1 h).2.2
  · intro x
    apply (Filter.eventually_const (f := f)).mp
    filter_upwards [L₀'_lim ((R' (S (S' x))) x), L₀'_lim ((R' (S (S' x))) ((R' (S' x)).symm (L₀' ((R' (S (S' x))) x)))), S'_lim x] with sol h1 h2 h3
    rw [← h2.2, ←h1.2, ←h3.2]
    exact (sol.1.axiom_iv'' x h3.1).2.2
  · intro x
    apply (Filter.eventually_const (f := f)).mp
    filter_upwards [op_lim x x, S'_lim x] with sol h1 h2
    rw [← h2.2, ←h1.2]
    exact (sol.1.axiom_v'' x h1.1).2
  · intro y a
    apply (Filter.eventually_const (f := f)).mp
    filter_upwards [op_lim (R' a y) y, S'_lim y] with sol h1 h2
    rw [← h2.2, ←h1.2]
    exact (sol.1.axiom_vi'' y a h1.1).2
  -- this one is a little trickier than the previous axioms because it involves a variable z that is not initially defined
  intro x y h h'
  have : ∃ z, op x y = Sum.inr z := by
    apply (Filter.eventually_const (f := f)).mp
    filter_upwards [op_lim x y] with sol h1
    rw [← h1.2]
    obtain ⟨z, this, _⟩ :=  sol.1.axiom_vii'' x y h h' h1.1
    exact ⟨z, this⟩
  obtain ⟨z, hz⟩ := this
  refine ⟨z, hz, ?_⟩
  apply (Filter.eventually_const (f := f)).mp
  filter_upwards [op_lim z x, op_lim x y, L₀'_lim ((R' 0) ((R' (S' x)) y)), S'_lim x] with sol h1 h2 h3 h4
  rw [← h1.2, ←h3.2, ←h4.2]
  have := sol.1.axiom_vii'' x y h h' h2.1
  obtain ⟨z', hz1, hz2⟩ := this
  rcases hz2 with hz2 | ⟨hz3, hz4, hz5, hz6⟩
  · have := (sol.1.axiom_P x y z' hz2).2.1
    aesop
  aesop
```

### child `enlarge_L₀'`: [`equational_theories/ManuallyProved/Equation1729/MagmaConstruction.lean` lines 513-562](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/ManuallyProved/Equation1729/MagmaConstruction.lean#L513-L562) ([local copy](code/equational_theories/ManuallyProved/Equation1729/MagmaConstruction.lean))

```lean
lemma enlarge_L₀' (sol : PartialSolution) (x : N)  : ∃ sol', sol ≤ sol' ∧ x ∈ fill sol'.Predom_L₀' ∧ sol.Dom_S' = sol'.Dom_S' := by
  by_cases hx : x ∈ sol.Dom_L₀'
  · exact ⟨sol, sol.refl, hx, rfl⟩
  set extras : Finset M := {Sum.inr x}
  set d := E <| sol.fresh_generator extras 0
  have hed : e d ∉ sol.Dom_L₀' := gen_fresh_not_in_fill sol extras 0
  have h_see_x : sol.sees extras x := by apply sol.extras_involved extras; simp [extras]
  have hd : 0 ≠ d := (E_ne_zero _).symm
  have hsd : S d ≠ d := (E_ne_SE _ _).symm
  have hsd' : 0 ≠ S d := (SE_ne_zero _).symm
  have hvalx : val d x = 0 := by
      apply val_of_nonsupp_eq_zero
      have : ¬ sol.reaches extras d := fresh_not_in_generators _ _
      contrapose! this
      rw [PartialSolution.reaches, in_generators]
      exact this.trans h_see_x
  have hvalx' : val (S d) x = 0 := by
      apply val_of_nonsupp_eq_zero
      have : ¬ sol.reaches extras (S d) := Sfresh_not_in_generators _ _
      contrapose! this
      rw [PartialSolution.reaches, in_generators]
      exact this.trans h_see_x
  have hcol1 (a : SM) (n:ℤ) : (e 0)^n * e d ≠ (R' a <| (R' (S a)).symm <| (e 0)^n * x)  := by
    by_contra! this
    by_cases h : a = d
    · rw [h] at this
      apply_fun val (S d) at this
      simp [R', hsd.symm, hvalx'] at this
    apply_fun val d at this
    by_cases h' : S a = d
    all_goals simp [R',hvalx,h,h'] at this
    linarith
  have hcol2 (a : SM) (n:ℤ): (e 0)^(n-1) * x ≠ (R' a <| (R' (S a)).symm <| (e 0)^n * e d) := by
    by_contra this
    by_cases h : a = d
    · rw [h] at this
      apply_fun val (S d) at this
      simp [R', hsd.symm, hsd', hvalx'] at this
    apply_fun val d at this
    by_cases h' : S a = d
    all_goals simp [R',hvalx,h,h',hd] at this
    exact E_ne_S _ _ h'.symm
  set sol' : PartialSolution := enlarge_L₀'_by hx hed (gen_fresh_not_rel_extra sol 0 (Finset.mem_singleton.mpr rfl)) hcol1 hcol2
  refine ⟨sol', ?_, ?_, rfl⟩
  · refine ⟨Finset.subset_union_left, by rfl, by rfl, fun _ hx' ↦ ?_, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
    exact (sol.enlarge_L₀'_extends hx hed hx').symm
  apply subset_fill
  rw [Finset.mem_coe]
  apply Finset.mem_union_right
  simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
```

### child `enlarge_S'`: [`equational_theories/ManuallyProved/Equation1729/MagmaConstruction.lean` lines 2043-2052](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/ManuallyProved/Equation1729/MagmaConstruction.lean#L2043-L2052) ([local copy](code/equational_theories/ManuallyProved/Equation1729/MagmaConstruction.lean))

```lean
lemma enlarge_S' (sol : PartialSolution) (x : N) :
    ∃ sol', sol ≤ sol' ∧ x ∈ sol'.Dom_S' := by
  apply WellFoundedLT.induction x (fun z hz ↦ ?_)
  by_cases z_one: z = 1
  · exact enlarge_S'_induction (by simp [z_one, ← bot_eq_one])
  · obtain ⟨parent_sol, h_parent_sol, h_parent_z_in⟩ := hz (parent z) (parent_lt z_one)
    have hind : ∀ y: N, y < z → y ∈ parent_sol.Dom_S' :=
      fun y hy ↦ parent_sol.axiom_S (parent z) y h_parent_z_in <| PredOrder.le_pred_of_lt hy
    obtain ⟨sol', hsol', z_sol'⟩ := enlarge_S'_induction hind
    exact ⟨sol', Preorder.le_trans sol parent_sol sol' h_parent_sol hsol', z_sol'⟩
```

### child `enlarge_op`: [`equational_theories/ManuallyProved/Equation1729/MagmaConstruction.lean` lines 2054-2420](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/ManuallyProved/Equation1729/MagmaConstruction.lean#L2054-L2420) ([local copy](code/equational_theories/ManuallyProved/Equation1729/MagmaConstruction.lean))

```lean
lemma enlarge_op (sol : PartialSolution) (x y :N) : ∃ sol', sol ≤ sol' ∧ (x,y) ∈ sol'.Dom_op := by
  wlog hx : x ∈ sol.Dom_S'
  · obtain ⟨sol', hsol, hx⟩ := enlarge_S' sol x
    obtain ⟨sol'', hsol', hx'⟩ := this sol' x y hx
    exact ⟨sol'', hsol.trans hsol', hx'⟩
  wlog hy : y ∈ sol.Dom_S'
  · obtain ⟨sol', hsol, hy⟩ := enlarge_S' sol y
    obtain ⟨sol'', hsol', hy'⟩ := this sol' x y (hsol.2.2.1 hx) hy
    exact ⟨sol'', hsol.trans hsol', hy'⟩
  set w := R' 0 <| R' (sol.S' x) <| y
  wlog hw : w ∈ sol.Dom_L₀'
  · obtain ⟨sol', hsol, hw, _⟩ := enlarge_L₀' sol w
    obtain ⟨sol'', hsol', hw'⟩ := this sol' x y (hsol.2.2.1 hx) (hsol.2.2.1 hy) ((hsol.2.2.2.2.2 x hx) ▸ hw)
    exact ⟨sol'', hsol.trans hsol', hw'⟩
  have no_pending : ¬ ∃ z, (y,z,x) ∈ sol.I := by
    by_contra this
    obtain ⟨z, hz⟩ := this
    have := sol.axiom_P y z x hz
    exact this.1 hy
  by_cases hdef : (x,y) ∈ sol.Dom_op
  · exact ⟨sol, sol.refl, hdef⟩
  by_cases hxy : x = y
  · rw [← hxy] at hdef no_pending ⊢
    set sol' : PartialSolution := {
      L₀' := sol.L₀'
      op := fun x' y' ↦ if (x',y') = (x,x) then Sum.inl (sol.S' x) else sol.op x' y'
      S' := sol.S'
      Predom_L₀' := sol.Predom_L₀'
      Dom_op := sol.Dom_op ∪ {(x,x)}
      Dom_S' := sol.Dom_S'
      I := sol.I
      axiom_i'' := sol.axiom_i''
      axiom_S := sol.axiom_S
      axiom_iii'' := sol.axiom_iii''
      axiom_iv'' := sol.axiom_iv''
      axiom_v'' := by
        intro x' hx'
        simp only [Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq, and_self] at hx'
        rcases hx' with hx' | hx'
        · have := sol.axiom_v'' x' hx'
          by_cases hxx' : x' = x
          · simp only [hxx', hx, ↓reduceIte, and_self]
          simp only [this, Prod.mk.injEq, hxx', and_self, ↓reduceIte]
        simp only [hx', hx, ↓reduceIte, and_self]
      axiom_vi'' := by
        intro y' a hya
        have : ¬ (R' a y' = x ∧ y' = x) := by
          by_contra this
          obtain ⟨h1, h2⟩ := this
          rw [← h2] at h1
          simp only [R', Equiv.coe_fn_mk, mul_eq_right, FreeGroup.of_ne_one] at h1
        simp [this]
        exact sol.axiom_vi'' y' a (by aesop)
      axiom_vii'' := by
        intro x' y' hxy' hxay hop
        have hop' : (x',y') ∈ sol.Dom_op := by
          simp only [Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq] at hop
          rcases hop  with hop | hop
          · exact hop
          rw [hop.2] at hxy'
          exfalso
          exact hxy' hop.1
        have hne : (x',y') ≠ (x,x) := by
          contrapose! hxy'
          rw [Prod.mk.injEq] at hxy'
          rw [hxy'.1, hxy'.2]
        obtain ⟨z, h1, h2⟩ := sol.axiom_vii'' x' y' hxy' hxay hop'
        rcases h2 with h2 | ⟨h3, h4, h5⟩
        · aesop
        · aesop
      axiom_P := by
        intro x' y' z hI
        obtain ⟨h1, h2, h3, h4⟩ := sol.axiom_P x' y' z hI
        aesop
      axiom_P' := sol.axiom_P'
      axiom_P'' := by
        intro x' y z hI
        have := sol.axiom_P'' x' y z hI
        aesop
      axiom_L := sol.axiom_L
    }
    refine ⟨sol', ⟨by rfl, Finset.subset_union_left, by rfl, fun _ _ ↦ rfl, ?_, fun _ _ ↦ rfl⟩, ?_⟩
    · intro ⟨z₁, z₂⟩ hz
      have hne : (z₁, z₂) ≠ (x, x) := fun h => hdef (h ▸ hz)
      show sol.op z₁ z₂ = (if (z₁, z₂) = (x,x) then Sum.inl (sol.S' x) else sol.op z₁ z₂)
      rw [if_neg hne]
    · show (x,x) ∈ sol.Dom_op ∪ {(x,x)}
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  by_cases hray : ∃ a, x = R' a y
  · obtain ⟨a, hray⟩ := hray
    rw [hray] at hx no_pending hdef hxy ⊢
    set sol' : PartialSolution := {
      L₀' := sol.L₀'
      op := fun x' y' ↦ if (x',y') = ((R' a) y,y) then Sum.inl (a - sol.S' y) else sol.op x' y'
      S' := sol.S'
      Predom_L₀' := sol.Predom_L₀'
      Dom_op := sol.Dom_op ∪ {((R' a) y,y)}
      Dom_S' := sol.Dom_S'
      I := sol.I
      axiom_i'' := sol.axiom_i''
      axiom_S := sol.axiom_S
      axiom_iii'' := sol.axiom_iii''
      axiom_iv'' := sol.axiom_iv''
      axiom_v'' := by
        intro x' hx'
        have : (x',x') ≠ ((R' a) y, y) := by
          contrapose! hxy
          simp only [Prod.mk.injEq] at hxy
          rw [← hxy.1, ←hxy.2]
        simp only [Finset.mem_union, Finset.mem_singleton, this, or_false] at hx'
        simp [this, ↓reduceIte]
        exact sol.axiom_v'' x' hx'
      axiom_vi'' := by
        intro y' a' hy'
        simp only [Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq] at hy'
        by_cases heq : (R' a') y' = (R' a) y ∧ y' = y
        · aesop
        have : ((R' a') y', y') ∈ PartialSolution.Dom_op := by tauto
        simp only [Prod.mk.injEq, heq, ↓reduceIte]
        exact sol.axiom_vi'' y' a' this
      axiom_vii'' := by
        intro x' y' hxy' hneq hin
        have h1 : (x',y') ≠ (R' a y, y) := by aesop
        simp only [h1, ↓reduceIte, Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq]
        obtain ⟨z, h3, h4⟩ := sol.axiom_vii'' x' y' hxy' hneq (by aesop)
        refine ⟨z, h3, ?_⟩
        rcases h4 with h4 | ⟨h5, h6, h7⟩
        · exact Or.inl h4
        refine Or.inr ⟨Or.inl h5, h6, ?_⟩
        have h8 : ¬ (z = (R' a) y ∧ x' = y) := by
          contrapose! hdef
          rwa [hdef.1, hdef.2] at h5
        rwa [if_neg h8]
      axiom_P := by
        intro x' y' z' hI
        obtain ⟨h1, h2, h3⟩ := sol.axiom_P x' y' z' hI
        refine ⟨h1, ?_, h3⟩
        simp only [Finset.mem_union, h2, Finset.mem_singleton, Prod.mk.injEq, false_or]
        by_contra h4
        obtain ⟨h4, h5⟩ := h4
        rw [← h5] at h4
        exact (h3.2.1 a).1 h4
      axiom_P' := sol.axiom_P'
      axiom_P'' := by
        intro x' y' z hI
        have := sol.axiom_P'' x' y' z hI
        aesop
      axiom_L := sol.axiom_L
    }
    refine ⟨sol', ⟨by rfl, Finset.subset_union_left, by rfl, fun _ _ ↦ rfl, ?_, fun _ _ ↦ rfl⟩, ?_⟩
    · intro ⟨z₁, z₂⟩ hz
      have hne : (z₁, z₂) ≠ ((R' a) y, y) := fun h => hdef (h ▸ hz)
      show sol.op z₁ z₂ = (if (z₁, z₂) = ((R' a) y, y) then Sum.inl (a - sol.S' y) else sol.op z₁ z₂)
      rw [if_neg hne]
    · show ((R' a) y, y) ∈ sol.Dom_op ∪ {((R' a) y, y)}
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  set extras : Finset M := {Sum.inr x, Sum.inr y, Sum.inr w}
  set d₀ := E <| sol.fresh_generator extras 0
  set z := (e d₀)^2
  have hz_invis : ¬ sol.sees extras z := sol.fresh_invis_pow extras 0 (Ne.symm (Nat.zero_ne_add_one 1))
  have hz_invis' : ¬ sol.sees extras (e d₀) := sol.fresh_invis extras 0
  classical
  set z' := (R' (S (sol.S' x))).symm <| sol.L₀' w
  set sol' : PartialSolution := {
    L₀' := sol.L₀'
    op := fun x' y' ↦ if (x',y') = (x,y) then Sum.inr <| z else if (x',y') = (z,x) then Sum.inr z' else sol.op x' y'
    S' := sol.S'
    Predom_L₀' := sol.Predom_L₀'
    Dom_op := sol.Dom_op ∪ { (x,y), (z, x) }
    Dom_S' := sol.Dom_S'
    I := sol.I ∪ {(z,x,z')}
    axiom_i'' := sol.axiom_i''
    axiom_S := sol.axiom_S
    axiom_iii'' := sol.axiom_iii''
    axiom_iv'' := sol.axiom_iv''
    axiom_v'' := by
      intro x' hx'
      simp only [Finset.union_insert, Finset.mem_insert, Prod.mk.injEq, Finset.mem_union,
        Finset.mem_singleton] at hx'
      rcases hx' with hx' | hx' | hx'
      · rw [← hx'.1, ←hx'.2] at hxy
        contrapose! hxy
        rfl
      · obtain ⟨h1, h2⟩ := sol.axiom_v'' x' hx'
        have h3 : ¬ (x' = x ∧ x' = y) := by
          contrapose! hxy
          rw [← hxy.1, ←hxy.2]
        have h4 : ¬ (x' = z ∧ x' = x) := by
          contrapose! hx
          rw [← hx.2, hx.1]
          exact gen_fresh_pow_not_in_dom_S' _ _ _ (Ne.symm (Nat.zero_ne_add_one 1))
        simp [h1, ←h2, h3, h4]
      rw [← hx'.2, hx'.1] at hx
      contrapose! hx
      exact gen_fresh_pow_not_in_dom_S' _ _ _ (Ne.symm (Nat.zero_ne_add_one 1))
    axiom_vi'' := by
      intro y' a hray'
      simp only [Finset.union_insert, Finset.mem_insert, Prod.mk.injEq, Finset.mem_union,
        Finset.mem_singleton] at hray'
      have hnot : ¬ (R' a y' = x ∧ y' = y) := by aesop
      have hnot' : ¬ (R' a y' = z ∧ y' = x) := by
          by_contra h
          obtain ⟨h1, h2⟩ := h
          rw [h2] at h1
          have : x = (e a)⁻¹ * (e d₀)^2 := by
            simp [R', z] at h1
            calc
              _ = (e a)⁻¹ * (e a * x)  := by group
              _ = _ := by rw [h1]
          rw [this] at hx
          replace hx := (sol.dom_S'_involved extras hx).1
          simp only [sol.sees_iff] at hx
          apply sol.fresh_not_in_gen extras 0 <| hx d₀ <| basis_elements_of_prod_gen d₀ a
      simp only [hnot, hnot', or_false, false_or] at hray'
      obtain ⟨h1, h2⟩ := sol.axiom_vi'' y' a hray'
      rw [← h2]
      simp [h1, hnot, hnot']
    axiom_vii'' := by
      intro x' y' hneq hxray hop
      simp only [Finset.union_insert, Finset.mem_insert, Prod.mk.injEq, Finset.mem_union,
        Finset.mem_singleton] at hop
      by_cases hop1 : x' = x ∧ y' = y
      · simp only [hop1.1, hop1.2, ↓reduceIte, Sum.inr.injEq, Finset.mem_union,
        Finset.mem_singleton, Prod.mk.injEq, Finset.union_insert, Finset.mem_insert, and_true,
        exists_eq_left', or_true, true_and, z]
        right
        simp only [hx, hxy, and_false, ↓reduceIte, and_true, true_and, z', w]
        convert hw
      by_cases hop2 : x' = z ∧ y' = x
      · rw [hop2.1, hop2.2]
        use z'
        simp only [Prod.mk.injEq, hxy, and_false, ↓reduceIte, Finset.mem_union, Finset.mem_singleton,
        or_true, Finset.union_insert, Finset.mem_insert, true_or, and_self]
      have hop3 : (x', y') ∈ PartialSolution.Dom_op := by tauto
      have := sol.axiom_vii'' x' y' hneq hxray hop3
      obtain ⟨z'', h1, h2⟩ := this
      refine ⟨z'', ?_, ?_⟩
      · simp only [Prod.mk.injEq, hop1, ↓reduceIte, hop2, h1]
      rcases h2 with h2 | ⟨h3, h3', h4, h5⟩
      · simp only [Finset.mem_union, h2, Finset.mem_singleton, Prod.mk.injEq, true_or,
        Finset.union_insert, Finset.mem_insert]
      right
      have h6 : ¬ (z'' = x ∧ x' = y) := by
        contrapose! hdef
        rwa [hdef.1, hdef.2] at h3
      have h7 : ¬ (z'' = z ∧ x' = x) := by
        by_contra h7
        rw [h7.1] at h3
        exact hz_invis (sol.dom_op_involved extras h3).1
      simp only [Finset.union_insert, Finset.mem_insert, Prod.mk.injEq, h6, Finset.mem_union, h3, h3',
        Finset.mem_singleton, h7, or_false, or_true, ↓reduceIte, true_and, h4, h5]
    axiom_P := by
      intro x'' y'' z'' hI
      simp only [Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq] at hI
      rcases hI with hI | ⟨rfl, rfl, rfl⟩
      · convert sol.axiom_P x'' y'' z'' hI using 2
        have h1 : ¬ (z'' = x ∧ x'' = y) := by
          contrapose! no_pending
          rw [no_pending.1, no_pending.2] at hI
          exact ⟨y'', hI⟩
        have h2 : ¬ (z'' = z ∧ x'' = x) := by
          by_contra h2
          rw [h2.1, h2.2] at hI
          exact (sol.axiom_P x y'' z hI).1 hx
        simp only [Finset.union_insert, Finset.mem_insert, Prod.mk.injEq, h1, Finset.mem_union,
          Finset.mem_singleton, h2, or_false, false_or]
      have hz : z ∉ sol.Dom_S' := by
        by_contra h3
        exact hz_invis <| (sol.dom_S'_involved extras h3).1
      have hz'_vis : sol.sees extras z' := by
        simp only [z']
        exact sol.sees_R'_inv (sol.reaches_S <| sol.reaches_involved <| (sol.dom_S'_involved _ hx).2) (sol.dom_L₀'_involved _ hw).2
      refine ⟨hz, ?_, ?_, ?_, ?_, ?_⟩
      · by_contra h3
        simp only [Finset.union_insert, Finset.mem_insert, Prod.mk.injEq, Finset.mem_union,
          Finset.mem_singleton] at h3
        rcases h3 with ⟨h3, h4⟩ | h3 | ⟨h3, h4⟩
        · rw [h4] at hz
          exact hz hy
        · exact hz_invis (sol.dom_op_involved extras h3).2.1
        rw [h4] at hz
        exact hz hx
      · by_contra h
        contrapose! hz_invis
        rw [← h]
        exact hz'_vis
      · intro a
        have h1 : ¬ sol.sees extras ( R' a z ) := by
          by_contra h
          dsimp [R',z] at h
          simp only [sol.sees_iff] at h
          apply sol.fresh_not_in_gen extras 0 <| h d₀ <| basis_elements_of_prod_gen' d₀ a
        have h2 : ¬ sol.sees extras ( (R' a).symm z ) := by
          by_contra h
          dsimp [R',z] at h
          simp only [sol.sees_iff] at h
          apply sol.fresh_not_in_gen extras 0 <| h d₀ <| basis_elements_of_prod_gen d₀ a
        constructor
        · aesop
        contrapose! h2
        apply_fun (R' a).symm at h2
        simp only [Equiv.symm_apply_apply] at h2
        rw [← h2]
        exact hz'_vis
      · contrapose! hz_invis
        rw [← hz_invis]
        apply sol.extras_involved
        simp only [extras, Finset.mem_insert, Finset.mem_singleton, true_or]
      simp only [z, parent_of_e_sq]
      contrapose! hz_invis'
      rw [← hz_invis']
      apply sol.extras_involved
      simp only [extras, Finset.mem_insert, Finset.mem_singleton, true_or]
    axiom_P' := by
      intro x₁ y₁ y'₁ z₁ hy hy'
      simp only [Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq] at hy hy'
      have (y₁ : N) : (z, y₁, z₁) ∉ sol.I := by
        contrapose! hz_invis
        exact (sol.I_involved _ hz_invis).1
      rcases hy with hy | ⟨hy₁, hy₂, hy₃⟩
      · rcases hy' with hy' | ⟨hy'₁, hy'₂, hy'₃⟩
        · exact sol.axiom_P' x₁ y₁ y'₁ z₁ hy hy'
        replace this := this y₁
        contrapose! this
        rwa [hy'₁] at hy
      rcases hy' with hy' | ⟨hy'₁, hy'₂, hy'₃⟩
      · replace this := this y'₁
        contrapose! this
        rwa [hy₁] at hy'
      rw [hy₂, hy'₂]
    axiom_P'' := by
      intro x₁ y₁ z₁ hI
      simp only [Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq] at hI
      rcases hI with hI | ⟨rfl, rfl, rfl⟩
      · have := sol.axiom_P'' x₁ y₁ z₁ hI
        constructor
        · exact Finset.mem_union_left _ this.1
        have h1 : (x₁,y₁) ≠ (x,y) := by
          contrapose! hdef
          rw [← hdef]
          exact this.1
        have h2 : (x₁,y₁) ≠ (z,x) := by
          contrapose! hz_invis
          simp only [Prod.mk.injEq] at hz_invis
          rw [← hz_invis.1]
          exact (sol.I_involved extras hI).1
        simp [this.2, h1, h2]
      constructor
      · simp only [Finset.union_insert, Finset.mem_insert, Prod.mk.injEq, Finset.mem_union,
        Finset.mem_singleton, or_true]
      have : (z,y₁) ≠ (y₁,y) := by
        contrapose! hxy
        simp only [Prod.mk.injEq] at hxy
        exact hxy.2
      simp only [this, ↓reduceIte]
    axiom_L := sol.axiom_L
  }
  refine ⟨sol', ?_, ?_⟩
  · refine ⟨Finset.Subset.refl _, Finset.subset_union_left, Finset.Subset.refl _, fun _ _ ↦ rfl, ?_, fun _ _ ↦ rfl⟩
    intro ⟨p₁, p₂⟩ hp
    have h1 : (p₁, p₂) ≠ (x, y) := fun h => hdef (h ▸ hp)
    have h2 : (p₁, p₂) ≠ (z, x) := fun h => hz_invis (sol.dom_op_involved extras (h ▸ hp)).1
    show sol.op p₁ p₂ = (if (p₁, p₂) = (x, y) then Sum.inr z else if (p₁, p₂) = (z, x) then Sum.inr z' else sol.op p₁ p₂)
    rw [if_neg h1, if_neg h2]
  · show (x, y) ∈ sol.Dom_op ∪ {(x, y), (z, x)}
    refine Finset.mem_union_right _ ?_
    simp
```

How the parts fit. The parent `not_817` is a 29-line glue (lines 15-43). It
builds a task indexed by the three-component sum `β := N ⊕ N ⊕ (N × N)` (line
16): each component states one totality condition a partial solution must
eventually satisfy — `x ∈ fill sol.Predom_L₀'`, `x ∈ sol.Dom_S'`, or
`(x,y) ∈ sol.Dom_op`. It hands that task, with the seed
`TrivialPartialSolution`, to Mathlib's `exists_greedy_chain` (line 21), which
returns a chain of partial solutions total in the limit. The chain becomes a
magma via `use_chain` (line 23), which consumes exactly the three totality
hypotheses the task was built to provide (lines 26-31). The one remaining
obligation — that the greedy-chain combinator can always extend a partial
solution to cover the next element of `β` — is discharged by
`intro sol b; match b with` (lines 32-43), which dispatches on the component of
`β` and calls one enlargement lemma per component: `enlarge_L₀'` for `Sum.inl x`
(line 36), `enlarge_S'` for `Sum.inr (Sum.inl x)` (line 40), `enlarge_op` for
`Sum.inr (Sum.inr (x,y))` (line 43).

The lemma graph, in text:

- `not_817` uses `exists_greedy_chain` (Mathlib), `TrivialPartialSolution`
  (the seed), `use_chain`, `enlarge_L₀'`, `enlarge_S'`, `enlarge_op`.
- `use_chain` uses `reduce_to_new_axioms` (SmallMagma.lean:431), `Set.choose`,
  and `IsChain.IsDirected` (MagmaConstruction.lean:129).
- `enlarge_op` uses `enlarge_S'` (lines 2056, 2060) and `enlarge_L₀'` (line
  2065).
- `enlarge_S'` uses `enlarge_S'_induction` (lines 2049, 2053), which uses
  `enlarge_S'_induction_with_axioms` (lines 1990, 2038) and
  `enlarge_L₀'_multiple` (line 1996); `enlarge_L₀'_multiple` uses `enlarge_L₀'`
  (line 569).
- `enlarge_L₀'` uses `enlarge_L₀'_by` (line 555) and `enlarge_L₀'_extends`
  (line 558).

The longest chain of project lemmas below `not_817` that I checked is
`not_817 → enlarge_op → enlarge_S' → enlarge_S'_induction →
enlarge_S'_induction_with_axioms`, four levels deep.

Why each direct lemma is a good leaf — a self-contained statement whose proof
closes on its own or from named siblings:

- `TrivialPartialSolution` — the empty partial solution; every `axiom_*` field
  closes from `Finset.notMem_empty`. It is the base of the chain, not a
  theorem.
- `use_chain` — takes a chain plus three totality hypotheses and returns the
  goal type; its proof is a filter limit plus `reduce_to_new_axioms`,
  independent of how the totality was achieved.
- `enlarge_L₀'`, `enlarge_S'`, `enlarge_op` — the three component-wise
  enlargement lemmas, each stated `(sol : PartialSolution) (x : N) : ∃ sol',
  sol ≤ sol' ∧ …` and closed by building one bigger `PartialSolution`. They are
  near-identical in shape — hence "one lemma per component" — and each closes
  on its own, with `enlarge_op` and `enlarge_S'` delegating sub-steps to the
  other two.

## Why it is good

1. The parent `not_817` closes from the five named items: `exists_greedy_chain`
   is instantiated with the task and seed `TrivialPartialSolution` (line 21),
   `use_chain` is applied to the chain (line 23), and the three closure
   obligations are discharged by `enlarge_L₀'` (line 36), `enlarge_S'` (line
   40) and `enlarge_op` (line 43) in the `match b with` dispatch (`check`, the
   parent permalink in `sites`).
2. The glue dispatches over the three components of `β = N ⊕ N ⊕ (N × N)` (the
   `match b with` at lines 32-43), one enlargement lemma per component, and the
   whole main proof is 29 lines, lines 15-43 (`measurement`, the parent
   permalink plus the three child permalinks in `sites`).
3. The authors' blueprint node `1729_refute_817` lists the proof dependencies
   as `partial-exist, enlarge-l0, enlarge-S, enlarge-op, chain`
   (`\uses{...}` at `blueprint/src/chapter/1729.tex:302`), which map one-to-one
   onto `TrivialPartialSolution`, `enlarge_L₀'`, `enlarge_S'`, `enlarge_op`,
   `use_chain` (`author-statement`, the blueprint permalink quoted in the
   claim).
4. No `sorry`, `admit` or `Admitted` appears in the copied files, so no child
   closes on a hole (`check`, a grep over the copied files at the pinned
   commit).

In my opinion the detail worth copying is the symmetry between the task's
three components and the three enlargement lemmas: the index type `β` is the
single place the construction's components are enumerated, and every place the
glue must branch (the task definition and the closure of the greedy-chain
obligation) is a case analysis over exactly those constructors.

## When to use it, and when not

Use it when a goal `∃ (G : Type) (_ : Magma G), P G ∧ ¬ Q G` is met by a
greedy/back-and-forth limit of finite partial solutions, and the single-step
move is a family of near-identical enlargement lemmas, one per component of a
sum-indexed totality condition, so the glue reduces to a dispatch over that
index. A generic chain combinator (`exists_greedy_chain`) and a
chain-to-result lemma (`use_chain`) must already exist or the glue will carry
real work.

Avoid it when the components need genuinely different enlargement arguments
that do not share one partial-solution structure (then they are not one
family and the per-component lemma stops being "generated by rule"); when
there is no off-the-shelf limit combinator to absorb the chain reasoning; or
when the index has many components, where a generated or folded form beats
one hand-written lemma per component.

## Consequences

Each constructor of the index sum `β = N ⊕ N ⊕ (N × N)` is a separate closure
obligation on the greedy chain: `Sum.inl x`, `Sum.inr (Sum.inl x)`,
`Sum.inr (Sum.inr (x,y))`. The glue must (a) instantiate `exists_greedy_chain`
with a task whose three components match `use_chain`'s three totality
hypotheses, (b) seed it nonempty with `TrivialPartialSolution`, and (c) cover
every constructor in the match — exhaustiveness is Lean's coverage check on
`match b with`, not a separate lemma. The failure mode is a component whose
enlargement lemma does not preserve the other components' domains:
`enlarge_L₀'` therefore returns `sol.Dom_S' = sol'.Dom_S'` explicitly, and
`enlarge_op` wlogs its prerequisites via `enlarge_S'`/`enlarge_L₀'` before
extending `Dom_op`.

## Verification

<!-- verification:start -->
Status: **verified**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/blueprint-paper.yml (job build_project, '~/.elan/bin/lake build equational_theories' line 110) triggers on push to main with paths '**/*.lean'; pinned commit 8b87204d5b201e1cf6c69b8dcabb0558109bee00 is HEAD of main (compare status identical) | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 3 file(s) byte-identical at 8b87204d5b201e1cf6c69b8dcabb0558109bee00 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read code/equational_theories/ManuallyProved/Equation1729.lean L14-43 (byte-identical at pinned commit): L21 'have := exists_greedy_chain task ?_ TrivialPartialSolution', L23 'apply use_chain hchain', L36 'enlarge_L₀' sol x', L40 'enlarge_S' sol x', L43 'enlarge_op sol x y', dispatch 'match b with' over Sum.inl/Sum.inr at L33-43 | verifier |
| 2 | verified | Read Equation1729.lean: L16 'let β := N ⊕ N ⊕ (N × N)'; match branches L34 (enlarge_L₀'), L38 (enlarge_S'), L41 (enlarge_op), one per component; proof spans L15-43 = 29 lines. Note 'match b with' is at L33 (range 32-43 in claim includes L32 'intro sol b') | verifier |
| 3 | verified | Fetched blueprint/src/chapter/1729.tex at pinned commit via raw view: label '1729_refute_817' (\lean{Eq1729.not_817}); proof header '\begin{proof}\uses{partial-exist, enlarge-l0, enlarge-S, enlarge-op,chain}\leanok' matches the quoted string verbatim | verifier |
| 4 | verified | grep over the three copied files (byte-identical at pinned commit) for 'sorry|admit|Admitted' returned no matches; case-insensitive 'sorry|admit' also no matches | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | object | Decomposition is correct and closes: no sorry/admit/Admitted; parent not_817 closes from exists_greedy_chain, TrivialPartialSolution, use_chain, enlarge_L0', enlarge_S', enlarge_op; all five children statements match code verbatim and are exactly what the main proof uses. glue_lines 29, child_lines [53,71,50,10,367], direct_lemmas 5 are right. But shape.depth is 4 while the entry's own README documents a 5-level chain: not_817 -> enlarge_op (wlog calls enlarge_S' at 2056/2060) -> enlarge_S' (calls enlarge_S'_induction at 2051) -> enlarge_S'_induction (calls enlarge_L0'_multiple at 1996) -> enlarge_L0'_multiple (calls enlarge_L0' at 569) -> enlarge_L0'. Fix: recompute depth to at least 5. Minor: TrivialPartialSolution has eleven axiom fields and axiom_L closes with simp not Finset.notMem_empty, so closed_by ten-fields-each-by-notMem_empty is wrong; enlarge_S' closed_by cites call sites 2049/2053 but enlarge_S'_induction is called at 2047/2051; claim 2 places match b with at line 32 but it is line 33. | reviewer-correctness |
| generality | accept | Move generalized beyond the example: README 'When to use it' abstracts goal 1729-not-817 to '∃ G, P G ∧ ¬ Q G via a greedy/back-and-forth limit of finite partial solutions' and the concrete index to 'a sum-indexed totality condition with one enlargement lemma per component, glue = dispatch over the index'; applicability.goal_shape/use_when restate it. avoid_when names three specific honest failures (components with genuinely different arguments → not one family; no off-the-shelf combinator → glue carries the work; many components → generated/folded form wins). Consequences list concrete obligations (instantiate exists_greedy_chain, seed nonempty, exhaustiveness via match coverage check) plus the domain-preservation failure mode with specifics (enlarge_L₀' returns Dom_S'=Dom_S'; enlarge_op wlogs via enlarge_S'/enlarge_L₀'). Good-leaf section states the bounded-prover criterion ('self-contained statement whose proof closes on its own or from named siblings') per lemma. | reviewer-generality |
| provenance-licence | accept | check_provenance.py passes: all 3 copied files byte-identical at pinned commit 8b87204d5b201e1cf6c69b8dcabb0558109bee00, and recorded sha256 hashes match the local copies; commit agrees across entry.json, source.json and SOURCE.md; licence Apache-2.0 consistent across entry.json, source.json, SOURCE.md and the copied upstream-LICENSE (Apache 2.0 text with Equational Theories Project copyright); every file and site permalink points at github.com/teorth/equational_theories/blob/<commit>/<path> matching the copied paths. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/teorth/equational_theories at commit `8b87204d5b201e1cf6c69b8dcabb0558109bee00`, under `Apache-2.0`; see the [source note](../../sources/equational-theories/SOURCE.md) for the licence text and attribution.
