import Mathlib
set_option pp.numericTypes true
set_option pp.funBinderTypes true
set_option maxHeartbeats 0
open Classical Finset

abbrev State (n : ℕ) : Type := (Fin n → Fin 3) × Finset (Fin n → Fin 3)

abbrev State.validNext {n : ℕ} (s : State n) : Finset (State n) :=
  {s' |
    s'.1 ∈ s.2 ∧
    (∃ (i : Fin n) (δ : ({1, -1} : Finset ℤ)),
      s'.1 i = s.1 i + δ.val ∧ ∀ j ≠ i, s'.1 j = s.1 j) ∧
    s'.2 = s.2.erase s'.1}

abbrev State.init (n : ℕ) : State n :=
  ⟨fun _ ↦ 0, Finset.univ.erase (fun _ ↦ 0)⟩

abbrev Strategy (n : ℕ) : Type := State n → State n

abbrev IsRollout {n : ℕ} (a b : Strategy n) (s : ℕ → State n) : Prop :=
  s 0 = State.init n ∧
  (∀ i, Even i → s (i + 1) = a (s i)) ∧
  (∀ i, Odd i → s (i + 1) = b (s i))

-- Helper: swap 1 ↔ 2 in Fin 3
def swap12 (v : Fin 3) : Fin 3 :=
  if v = 0 then 0 else if v = 1 then 2 else 1

lemma swap12_ne_zero {v : Fin 3} (hv : v ≠ 0) : swap12 v ≠ 0 := by
  fin_cases v <;> simp [swap12] at *

lemma swap12_invol (v : Fin 3) : swap12 (swap12 v) = v := by
  fin_cases v <;> simp [swap12]

-- Helper: first nonzero coordinate
def firstNonzero {n : ℕ} (x : Fin n → Fin 3) (hx : x ≠ fun _ => 0) : Fin n :=
  Fin.find (fun i => x i ≠ 0) (by
    by_contra h
    push_neg at h
    exact hx (funext h))

lemma firstNonzero_spec {n : ℕ} (x : Fin n → Fin 3) (hx : x ≠ fun _ => 0) :
    x (firstNonzero x hx) ≠ 0 := by
  unfold firstNonzero
  exact @Fin.find_spec n (fun i => x i ≠ 0) (by infer_instance) _

lemma firstNonzero_min {n : ℕ} (x : Fin n → Fin 3) (hx : x ≠ fun _ => 0)
    (j : Fin n) (hj : j < firstNonzero x hx) : x j = 0 := by
  unfold firstNonzero at hj
  have := @Fin.find_min n (fun i => x i ≠ 0) (by infer_instance) _ j hj
  push_neg at this
  exact this

-- The matching function σ
def σ {n : ℕ} (x : Fin n → Fin 3) (hx : x ≠ fun _ => 0) : Fin n → Fin 3 := fun i =>
  if i = firstNonzero x hx then swap12 (x i) else x i

lemma σ_ne_zero {n : ℕ} (x : Fin n → Fin 3) (hx : x ≠ fun _ => 0) :
    σ x hx ≠ fun _ => 0 := by
  intro h
  have hk : x (firstNonzero x hx) ≠ 0 := firstNonzero_spec x hx
  have h1 : σ x hx (firstNonzero x hx) = swap12 (x (firstNonzero x hx)) := by simp only [σ, ite_true]
  have h2 : σ x hx (firstNonzero x hx) = 0 := by simp [h]
  rw [h2] at h1
  have := swap12_ne_zero hk
  rw [← h1] at this
  exact this rfl

lemma σ_at_firstNonzero {n : ℕ} (x : Fin n → Fin 3) (hx : x ≠ fun _ => 0) :
    (σ x hx) (firstNonzero x hx) = swap12 (x (firstNonzero x hx)) := by
  simp only [σ, ite_true]

lemma σ_away_firstNonzero {n : ℕ} (x : Fin n → Fin 3) (hx : x ≠ fun _ => 0)
    (j : Fin n) (hj : j ≠ firstNonzero x hx) : (σ x hx) j = x j := by
  simp only [σ, hj, ite_false]

lemma firstNonzero_σ {n : ℕ} (x : Fin n → Fin 3) (hx : x ≠ fun _ => 0) :
    firstNonzero (σ x hx) (σ_ne_zero x hx) = firstNonzero x hx := by
  let k := firstNonzero x hx
  have hσk : (σ x hx) k ≠ 0 := by
    rw [σ_at_firstNonzero]
    exact swap12_ne_zero (firstNonzero_spec x hx)
  have hσj : ∀ j < k, (σ x hx) j = 0 := by
    intro j hj
    rw [σ_away_firstNonzero x hx j (ne_of_lt hj)]
    exact firstNonzero_min x hx j hj
  unfold firstNonzero
  rw [Fin.find_eq_iff]
  constructor
  · exact hσk
  · intro j hj
    simp [hσj j hj]

lemma σ_invol {n : ℕ} (x : Fin n → Fin 3) (hx : x ≠ fun _ => 0) :
    σ (σ x hx) (σ_ne_zero x hx) = x := by
  ext i
  have hk_σ : firstNonzero (σ x hx) (σ_ne_zero x hx) = firstNonzero x hx := firstNonzero_σ x hx
  by_cases hi : i = firstNonzero x hx
  · subst hi
    have eq1 : (σ (σ x hx) (σ_ne_zero x hx)) (firstNonzero x hx) =
               swap12 ((σ x hx) (firstNonzero x hx)) := by
      conv_lhs => rw [σ, if_pos hk_σ.symm]
    have eq2 : (σ x hx) (firstNonzero x hx) = swap12 (x (firstNonzero x hx)) :=
      σ_at_firstNonzero x hx
    rw [eq1, eq2, swap12_invol]
  · have eq1 : (σ (σ x hx) (σ_ne_zero x hx)) i = (σ x hx) i := by
      conv_lhs => rw [σ, if_neg (by rwa [hk_σ])]
    have eq2 : (σ x hx) i = x i := σ_away_firstNonzero x hx i hi
    rw [eq1, eq2]

-- σ is proof-irrelevant: if the functions are equal, σ returns equal results
lemma σ_congr {n : ℕ} (x y : Fin n → Fin 3) (hx : x ≠ fun _ => 0) (hy : y ≠ fun _ => 0)
    (heq : x = y) : σ x hx = σ y hy := by
  subst heq
  rfl

-- σ is injective (as a function that depends on a proof of nonzero)
-- Key insight: σ only modifies the first nonzero position, so if σ x = σ y, then
-- firstNonzero x = firstNonzero y and the values agree elsewhere and at the first position (via swap)
lemma σ_inj {n : ℕ} (x y : Fin n → Fin 3) (hx : x ≠ fun _ => 0) (hy : y ≠ fun _ => 0) :
    σ x hx = σ y hy → x = y := by
  intro hσeq
  -- From σ x = σ y, at all positions j ≠ firstNonzero x we have x j = (σ x) j = (σ y) j
  -- At position firstNonzero x, we have swap12(x (firstNonzero x)) = (σ x)(firstNonzero x) = (σ y)(firstNonzero x)
  ext i
  have h1 := σ_invol x hx  -- σ(σ x) = x
  have h2 := σ_invol y hy  -- σ(σ y) = y
  -- The key: σ(σ x) i = σ(σ y) i for all i
  -- Since σ x = σ y as functions, σ(σ x) and σ(σ y) should agree
  -- We compute each side:
  have lhs : (σ (σ x hx) (σ_ne_zero x hx)) i = x i := congrFun h1 i
  have rhs : (σ (σ y hy) (σ_ne_zero y hy)) i = y i := congrFun h2 i
  rw [← lhs, ← rhs]
  -- Need: σ(σ x) i = σ(σ y) i
  -- This follows because σ x = σ y (as functions)
  have h_fn_eq : σ x hx = σ y hy := hσeq
  -- Use the lemma firstNonzero_σ
  have hfn_σx := firstNonzero_σ x hx
  have hfn_σy := firstNonzero_σ y hy
  -- firstNonzero(σ x) = firstNonzero x, firstNonzero(σ y) = firstNonzero y
  -- We also need firstNonzero x = firstNonzero y
  have h_fn_x_eq_fn_y : firstNonzero x hx = firstNonzero y hy := by
    -- From σ x = σ y, looking at values away from firstNonzero, x = y there
    -- And at firstNonzero, swap12(x k) = swap12(y k')
    -- Since firstNonzero is the minimal index where the function is nonzero...
    -- This requires more work. Let's use a direct approach.
    by_contra h
    -- Without loss of generality, assume firstNonzero x < firstNonzero y
    rcases Ne.lt_or_gt h with hlt | hlt
    · -- firstNonzero x < firstNonzero y
      have hx_zero_at_fn_x : (σ x hx) (firstNonzero x hx) = swap12 (x (firstNonzero x hx)) := σ_at_firstNonzero x hx
      have hy_at_fn_x : (σ y hy) (firstNonzero x hx) = y (firstNonzero x hx) := σ_away_firstNonzero y hy _ (ne_of_lt hlt)
      have hy_zero : y (firstNonzero x hx) = 0 := firstNonzero_min y hy _ hlt
      have hσeq_at : (σ x hx) (firstNonzero x hx) = (σ y hy) (firstNonzero x hx) := congrFun h_fn_eq _
      rw [hx_zero_at_fn_x, hy_at_fn_x, hy_zero] at hσeq_at
      have hx_ne : x (firstNonzero x hx) ≠ 0 := firstNonzero_spec x hx
      exact swap12_ne_zero hx_ne hσeq_at
    · -- firstNonzero y < firstNonzero x
      have hy_at_fn_y : (σ y hy) (firstNonzero y hy) = swap12 (y (firstNonzero y hy)) := σ_at_firstNonzero y hy
      have hx_at_fn_y : (σ x hx) (firstNonzero y hy) = x (firstNonzero y hy) := σ_away_firstNonzero x hx _ (ne_of_lt hlt)
      have hx_zero : x (firstNonzero y hy) = 0 := firstNonzero_min x hx _ hlt
      have hσeq_at : (σ x hx) (firstNonzero y hy) = (σ y hy) (firstNonzero y hy) := congrFun h_fn_eq _
      rw [hy_at_fn_y, hx_at_fn_y, hx_zero] at hσeq_at
      have hy_ne : y (firstNonzero y hy) ≠ 0 := firstNonzero_spec y hy
      exact swap12_ne_zero hy_ne hσeq_at.symm
  -- Now we know firstNonzero x = firstNonzero y
  -- Show σ(σ x) i = σ(σ y) i by working with the specific index i
  -- We use lhs and rhs which give us σ(σ x) i = x i and σ(σ y) i = y i
  -- So we need x i = y i
  rw [lhs, rhs]
  -- Now we need (x i : ℕ) = (y i : ℕ) but x i = y i as Fin 3 suffices
  -- Apply extensionality at i
  have h_σx_i_eq : (σ x hx) i = (σ y hy) i := congrFun h_fn_eq i
  by_cases hi : i = firstNonzero x hx
  · -- i = firstNonzero x = firstNonzero y
    subst hi
    have h1 : (σ x hx) (firstNonzero x hx) = swap12 (x (firstNonzero x hx)) := σ_at_firstNonzero x hx
    have h2 : (σ y hy) (firstNonzero y hy) = swap12 (y (firstNonzero y hy)) := σ_at_firstNonzero y hy
    rw [h1, h_fn_x_eq_fn_y, h2] at h_σx_i_eq
    -- swap12(x k) = swap12(y k), and swap12 is injective
    have swap_eq := congrArg swap12 h_σx_i_eq
    simp only [swap12_invol] at swap_eq
    rw [h_fn_x_eq_fn_y]
    simp only [swap_eq]
  · -- i ≠ firstNonzero x
    have h1 : (σ x hx) i = x i := σ_away_firstNonzero x hx i hi
    have h2 : (σ y hy) i = y i := σ_away_firstNonzero y hy i (by rw [← h_fn_x_eq_fn_y]; exact hi)
    rw [h1, h2] at h_σx_i_eq
    simp only [h_σx_i_eq]

lemma swap12_diff {v : Fin 3} (hv : v ≠ 0) :
    ((swap12 v : ℤ) - (v : ℤ)) ∈ ({1, -1} : Finset ℤ) := by
  fin_cases v <;> simp [swap12] at *

lemma swap12_eq_add_diff (v : Fin 3) :
    (swap12 v : ℤ) = (v : ℤ) + ((swap12 v : ℤ) - (v : ℤ)) := by ring

lemma σ_adjacent {n : ℕ} (x : Fin n → Fin 3) (hx : x ≠ fun _ => 0) :
    ∃ (i : Fin n) (δ : ({1, -1} : Finset ℤ)),
      (σ x hx) i = x i + δ.val ∧ ∀ j ≠ i, (σ x hx) j = x j := by
  let k := firstNonzero x hx
  have hxk : x k ≠ 0 := firstNonzero_spec x hx
  have hdiff : ((swap12 (x k) : ℤ) - (x k : ℤ)) ∈ ({1, -1} : Finset ℤ) := swap12_diff hxk
  use k
  use ⟨(swap12 (x k) : ℤ) - (x k : ℤ), hdiff⟩
  constructor
  · rw [σ_at_firstNonzero]
    exact swap12_eq_add_diff (x k)
  · intro j hj
    exact σ_away_firstNonzero x hx j hj

lemma swap12_ne_self {v : Fin 3} (hv : v ≠ 0) : swap12 v ≠ v := by
  fin_cases v <;> simp [swap12] at *

lemma σ_ne_self {n : ℕ} (x : Fin n → Fin 3) (hx : x ≠ fun _ => 0) : σ x hx ≠ x := by
  intro h
  have hxk : x (firstNonzero x hx) ≠ 0 := firstNonzero_spec x hx
  have heq : σ x hx (firstNonzero x hx) = x (firstNonzero x hx) := by rw [h]
  rw [σ_at_firstNonzero] at heq
  exact swap12_ne_self hxk heq

-- B's strategy
noncomputable def strategyB (n : ℕ) : Strategy n := fun s =>
  if h : s.1 = fun _ => 0 then s
  else ⟨σ s.1 h, s.2.erase (σ s.1 h)⟩

-- Key lemma: after a valid move from position 0, position is nonzero
lemma valid_move_pos_nonzero {n : ℕ} (s s' : State n)
    (hs : s' ∈ s.validNext) (hs0 : s.1 = fun _ => 0) : s'.1 ≠ fun _ => 0 := by
  simp only [State.validNext, mem_filter, mem_univ, true_and] at hs
  obtain ⟨_, ⟨i, δ, hδ_eq, _⟩, _⟩ := hs
  intro h0
  have hi : s'.1 i = 0 := by simp [h0]
  have hsi : s.1 i = 0 := by simp [hs0]
  rw [hi, hsi] at hδ_eq
  simp only [Fin.val_zero] at hδ_eq
  norm_cast at hδ_eq
  have hδ_or : δ.val = 1 ∨ δ.val = -1 := by
    have := δ.2
    simp only [mem_insert, mem_singleton] at this
    exact this
  omega

-- Lemma: strategyB produces the right state when position is nonzero
lemma strategyB_nonzero {n : ℕ} (s : State n) (h : s.1 ≠ fun _ => 0) :
    strategyB n s = ⟨σ s.1 h, s.2.erase (σ s.1 h)⟩ := by
  simp only [strategyB, h, dite_false]

-- Lemma: if σ(pos) is adjacent to pos, in remaining, etc., then B's move is valid
lemma strategyB_valid {n : ℕ} (s : State n) (h : s.1 ≠ fun _ => 0)
    (hσ_in : σ s.1 h ∈ s.2) : strategyB n s ∈ s.validNext := by
  rw [strategyB_nonzero s h]
  simp only [State.validNext, mem_filter, mem_univ, true_and]
  refine ⟨hσ_in, ?_, trivial⟩
  exact σ_adjacent s.1 h

-- Key lemma: valid move decreases remaining set
lemma valid_move_decreases {n : ℕ} (s s' : State n)
    (hs : s' ∈ s.validNext) : s'.2.card < s.2.card := by
  simp only [State.validNext, mem_filter, mem_univ, true_and] at hs
  obtain ⟨hs'_in, _, hs'_erase⟩ := hs
  have : s'.2 = s.2.erase s'.1 := hs'_erase
  rw [this]
  exact card_erase_lt_of_mem hs'_in

-- The key invariant: σ preserves the property of not being in "erased" positions
-- In a valid rollout with strategyB, if A moves to p (nonzero), then σ(p) ∈ remaining

-- We'll prove this by showing that after B responds to A's move to p,
-- both p and σ(p) are erased, maintaining the invariant

-- Alternative approach: use well-foundedness of (s i).2.card to find first invalid step
-- Then show it must be even

theorem putnam_2025_a3 (n : ℕ) (_hn : 1 ≤ n) :
  ∃ b : Strategy n, ∀ a : Strategy n,
    ∀ s : ℕ → State n, IsRollout a b s →
      ∃ k : ℕ, Even k ∧
        (∀ i < k, s (i + 1) ∈ (s i).validNext) ∧
        s (k + 1) ∉ (s k).validNext := by
  use strategyB n
  intro a seq hrollout

  -- Let's define "all moves valid up to step m"
  let validUpTo := fun m => ∀ i < m, seq (i + 1) ∈ (seq i).validNext

  -- Use classical logic: either all moves are valid forever, or there's a first invalid one
  by_cases hall : ∀ m, validUpTo m
  · -- If all moves are valid forever, derive contradiction (impossible)
    exfalso
    have h0 : seq 0 = State.init n := hrollout.1
    have hcard0 : (seq 0).2.card = 3^n - 1 := by
      rw [h0]
      simp only [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fun,
        Fintype.card_fin]
    -- After k valid moves, remaining has at most 3^n - 1 - k positions
    have hbound : ∀ m, (seq m).2.card ≤ 3^n - 1 - m := by
      intro m
      induction m with
      | zero => simp [hcard0]
      | succ m ih =>
        have hvalid : seq (m + 1) ∈ (seq m).validNext := hall (m + 2) m (by omega)
        have hdec : (seq (m + 1)).2.card < (seq m).2.card := valid_move_decreases _ _ hvalid
        omega
    -- At step 3^n, remaining would have ≤ 3^n - 1 - 3^n = 0 positions (in Nat)
    -- So (seq (3^n)).2.card = 0, meaning remaining is empty
    -- But the (3^n)-th valid move requires (seq (3^n)).1 ∈ (seq (3^n - 1)).2
    -- Let's derive a contradiction from (seq (3^n)).2.card = 0 and the move being valid

    have hpos : 3^n ≥ 1 := Nat.one_le_pow n 3 (by omega)
    have hbound_3n : (seq (3^n)).2.card ≤ 3^n - 1 - 3^n := hbound (3^n)
    have hrhs_zero : 3^n - 1 - 3^n = 0 := by omega
    rw [hrhs_zero] at hbound_3n
    have hempty : (seq (3^n)).2.card = 0 := Nat.le_zero.mp hbound_3n

    -- The valid move from step (3^n - 1) to step 3^n requires
    -- (seq (3^n)).1 ∈ (seq (3^n - 1)).2
    have h3n_eq : 3^n - 1 + 1 = 3^n := by omega
    have hvalid_3n : seq (3^n) ∈ (seq (3^n - 1)).validNext := by
      have := hall (3^n + 1) (3^n - 1) (by omega)
      rwa [h3n_eq] at this
    simp only [State.validNext, mem_filter, mem_univ, true_and] at hvalid_3n
    obtain ⟨hpos_in, _, herase⟩ := hvalid_3n

    -- (seq (3^n)).2 = (seq (3^n - 1)).2.erase (seq (3^n)).1
    -- So (seq (3^n)).2.card = (seq (3^n - 1)).2.card - 1 (assuming (seq (3^n)).1 ∈ (seq (3^n - 1)).2)
    have hcard_erase : (seq (3^n)).2.card = ((seq (3^n - 1)).2.card : ℕ) - 1 := by
      rw [herase]
      exact card_erase_of_mem hpos_in
    -- But we showed (seq (3^n)).2.card = 0
    -- So (seq (3^n - 1)).2.card - 1 = 0, meaning (seq (3^n - 1)).2.card ≤ 1
    rw [hempty] at hcard_erase
    have hcard_prev : (seq (3^n - 1)).2.card ≤ 1 := by omega

    -- Now apply the bound at step 3^n - 1
    have hbound_prev : (seq (3^n - 1)).2.card ≤ 3^n - 1 - (3^n - 1) := hbound (3^n - 1)
    have hrhs_prev : 3^n - 1 - (3^n - 1) = 0 := by omega
    rw [hrhs_prev] at hbound_prev
    have hempty_prev : (seq (3^n - 1)).2.card = 0 := Nat.le_zero.mp hbound_prev

    -- But (seq (3^n)).1 ∈ (seq (3^n - 1)).2, so (seq (3^n - 1)).2 ≠ ∅
    rw [card_eq_zero] at hempty_prev
    rw [hempty_prev] at hpos_in
    exact notMem_empty _ hpos_in
  · -- There exists some step where a move is invalid
    push_neg at hall
    -- hall : ∃ m, ¬validUpTo m, i.e., ∃ m, ∃ i < m, seq (i + 1) ∉ (seq i).validNext
    have hex : ∃ i, seq (i + 1) ∉ (seq i).validNext := by
      obtain ⟨m, hm⟩ := hall
      simp only [validUpTo] at hm
      push_neg at hm
      obtain ⟨i, _, hi⟩ := hm
      exact ⟨i, hi⟩
    -- Use Nat.find to get the smallest invalid step
    let k := Nat.find hex
    have hk_invalid : seq (k + 1) ∉ (seq k).validNext := Nat.find_spec hex
    have hk_valid : ∀ i < k, seq (i + 1) ∈ (seq i).validNext := by
      intro i hi
      by_contra hcontra
      have hle : k ≤ i := Nat.find_le hcontra
      omega
    -- Now show k is even
    by_cases heven : Even k
    · exact ⟨k, heven, hk_valid, hk_invalid⟩
    · -- k is odd, so B moves at step k+1
      exfalso
      have hodd : Odd k := Nat.not_even_iff_odd.mp heven
      have hB_move : seq (k + 1) = strategyB n (seq k) := hrollout.2.2 k hodd

      -- Show position at step k is nonzero
      have hk_pos : k ≥ 1 := by
        rcases k with _ | k'
        · simp [Nat.odd_iff] at hodd
        · omega

      have h0_is_zero : (seq 0).1 = fun _ => 0 := by
        rw [hrollout.1]

      have h1_valid : seq 1 ∈ (seq 0).validNext := hk_valid 0 hk_pos

      have h1_nonzero : (seq 1).1 ≠ fun _ => 0 := valid_move_pos_nonzero _ _ h1_valid h0_is_zero

      -- Claim: at step k (odd), (seq k).1 ≠ 0 and σ((seq k).1) is in (seq k).2
      -- Lemma: remaining never contains 0 (moved outside hk_nonzero so it's accessible later)
      have h_zero_not_in_remaining : ∀ i ≤ k, (fun _ : Fin n => (0 : Fin 3)) ∉ (seq i).2 := by
        intro i hi
        induction i with
        | zero =>
          rw [hrollout.1]
          simp only [mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true]
        | succ i ih =>
          -- seq (i+1) came from a valid move at step i
          have hi' : i < k := by omega
          have hvalid_i : seq (i + 1) ∈ (seq i).validNext := hk_valid i hi'
          simp only [State.validNext, mem_filter, mem_univ, true_and] at hvalid_i
          obtain ⟨_, _, herase⟩ := hvalid_i
          rw [herase]
          intro hmem
          rw [mem_erase] at hmem
          exact ih (by omega) hmem.2

      have hk_nonzero : (seq k).1 ≠ fun _ => 0 := by
        -- Position at any step i ≥ 1 (after valid moves) is never 0
        -- because valid moves require new_pos ∈ remaining, and 0 ∉ remaining
        -- (0 was erased from univ in the initial state and never comes back)

        -- Now use this to show (seq k).1 ≠ 0
        -- Since k ≥ 1, seq k came from a valid move
        have hvalid_k_minus_1 : seq k ∈ (seq (k - 1)).validNext := by
          have : k - 1 < k := by omega
          have := hk_valid (k - 1) this
          simp only [Nat.sub_add_cancel hk_pos] at this
          exact this
        simp only [State.validNext, mem_filter, mem_univ, true_and] at hvalid_k_minus_1
        obtain ⟨hpos_in, _, _⟩ := hvalid_k_minus_1
        -- (seq k).1 ∈ (seq (k-1)).2
        -- But 0 ∉ (seq (k-1)).2 by h_zero_not_in_remaining
        intro hcontra
        rw [hcontra] at hpos_in
        exact h_zero_not_in_remaining (k - 1) (by omega) hpos_in

      have hσ_in_remaining : σ (seq k).1 hk_nonzero ∈ (seq k).2 := by
        -- The key insight: we need to show σ((seq k).1) ∈ remaining
        -- Remaining at step k = initial remaining minus visited positions

        -- We'll use a key lemma about the structure of remaining sets
        -- In a valid rollout, (seq i).2 = (seq 0).2 \ {(seq 1).1, ..., (seq i).1}

        -- First, establish that remaining decreases correctly
        have hremaining_structure : ∀ i ≤ k, ∀ p, p ∈ (seq i).2 ↔
            p ∈ (seq 0).2 ∧ ∀ j, 1 ≤ j → j ≤ i → p ≠ (seq j).1 := by
          intro i hi
          induction i with
          | zero =>
            intro p
            constructor
            · intro hp
              exact ⟨hp, fun j hj_pos hj_le => by omega⟩
            · intro ⟨hp, _⟩
              exact hp
          | succ i ih =>
            intro p
            have hi' : i < k := by omega
            have hvalid_i : seq (i + 1) ∈ (seq i).validNext := hk_valid i hi'
            simp only [State.validNext, mem_filter, mem_univ, true_and] at hvalid_i
            obtain ⟨_, _, herase⟩ := hvalid_i
            rw [herase, mem_erase]
            constructor
            · intro ⟨hne, hmem⟩
              rw [ih (by omega)] at hmem
              obtain ⟨hmem0, hprev⟩ := hmem
              refine ⟨hmem0, ?_⟩
              intro j hj_pos hj_le
              rcases eq_or_lt_of_le hj_le with rfl | hj_lt
              · exact hne
              · exact hprev j hj_pos (by omega)
            · intro ⟨hmem0, hall⟩
              constructor
              · exact hall (i + 1) (by omega) (by omega)
              · rw [ih (by omega)]
                exact ⟨hmem0, fun j hj_pos hj_le => hall j hj_pos (by omega)⟩

        -- Now show σ((seq k).1) satisfies the membership condition
        rw [hremaining_structure k (le_refl k)]
        constructor
        · -- σ((seq k).1) ∈ (seq 0).2 = univ \ {0}
          rw [hrollout.1]
          simp only [mem_erase, ne_eq, mem_univ, and_true]
          exact σ_ne_zero (seq k).1 hk_nonzero
        · -- σ((seq k).1) ≠ (seq j).1 for all 1 ≤ j ≤ k
          intro j hj_pos hj_le

          -- Helper: position at step i ≥ 1 is nonzero
          have hpos_nonzero' : ∀ i, 1 ≤ i → i ≤ k → (seq i).1 ≠ fun _ => 0 := by
            intro i hi_pos hi_le
            have hvalid_i_minus_1 : seq i ∈ (seq (i - 1)).validNext := by
              have : i - 1 < k := by omega
              have := hk_valid (i - 1) this
              simp only [Nat.sub_add_cancel hi_pos] at this
              exact this
            simp only [State.validNext, mem_filter, mem_univ, true_and] at hvalid_i_minus_1
            obtain ⟨hpos_in, _, _⟩ := hvalid_i_minus_1
            intro hcontra
            rw [hcontra] at hpos_in
            exact h_zero_not_in_remaining (i - 1) (by omega) hpos_in

          -- Helper: all positions in rollout are distinct (position i ≠ position m for m < i ≤ k)
          have hpos_distinct : ∀ i m, 1 ≤ m → m < i → i ≤ k → (seq i).1 ≠ (seq m).1 := by
            intro i m hm_pos hm_lt hi_le
            have hvalid_im1 : seq i ∈ (seq (i - 1)).validNext := by
              have := hk_valid (i - 1) (by omega)
              simp only [Nat.sub_add_cancel (by omega : i ≥ 1)] at this
              exact this
            simp only [State.validNext, mem_filter, mem_univ, true_and] at hvalid_im1
            obtain ⟨hi_in, _, _⟩ := hvalid_im1
            rw [hremaining_structure (i - 1) (by omega)] at hi_in
            intro heq
            rw [heq] at hi_in
            obtain ⟨_, hnotin⟩ := hi_in
            exact hnotin m hm_pos (by omega) rfl

          -- Key: at odd steps m with m + 1 ≤ k, B responds with σ
          -- We'll prove: (seq (m+1)).1 = σ (seq m).1 hm_nonzero for some proof hm_nonzero
          have hB_response : ∀ m, Odd m → m + 1 ≤ k →
              ∃ (hm_ne : (seq m).1 ≠ fun _ => 0), (seq (m + 1)).1 = σ (seq m).1 hm_ne := by
            intro m hm_odd hm_le
            have hm_pos : 1 ≤ m := Nat.one_le_of_lt (Odd.pos hm_odd)
            have hm_nonzero : (seq m).1 ≠ fun _ => 0 := hpos_nonzero' m hm_pos (by omega)
            use hm_nonzero
            have hB := hrollout.2.2 m hm_odd
            simp only [hB, strategyB, hm_nonzero, dite_false]

          rcases eq_or_lt_of_le hj_le with rfl | hj_lt
          · -- j = k: σ(seq k).1 ≠ (seq k).1
            exact σ_ne_self (seq k).1 hk_nonzero
          · -- j < k
            intro heq
            rcases Nat.even_or_odd j with hj_even | hj_odd
            · -- j is even and 1 ≤ j < k, so j ≥ 2
              -- j - 1 is odd and j - 1 + 1 = j ≤ k - 1 < k, so j ≤ k
              -- B moved at step j-1, so (seq j).1 = σ(seq (j-1)).1
              have hj_ge_2 : j ≥ 2 := by
                -- j is even with j ≥ 1, so j ≥ 2
                rcases hj_even with ⟨m, hm⟩
                -- j = m + m = 2*m, and j ≥ 1, so m ≥ 1, so j ≥ 2
                omega
              have hj_m1_odd : Odd (j - 1) := by
                rcases hj_even with ⟨m, hm⟩
                use m - 1; omega
              obtain ⟨hjm1_ne, hseq_j⟩ := hB_response (j - 1) hj_m1_odd (by omega)
              simp only [Nat.sub_add_cancel (by omega : j ≥ 1)] at hseq_j
              -- heq: σ(seq k).1 = (seq j).1 = σ(seq (j-1)).1
              rw [hseq_j] at heq
              have hpos_eq : (seq k).1 = (seq (j - 1)).1 := σ_inj _ _ hk_nonzero hjm1_ne heq
              -- But (seq k).1 ≠ (seq (j-1)).1 since j - 1 < k
              exact hpos_distinct k (j - 1) (by omega) (by omega) (le_refl k) hpos_eq

            · -- j is odd, so (seq (j+1)).1 = σ(seq j).1
              -- heq: σ(seq k).1 = (seq j).1
              -- Apply σ: (seq k).1 = σ(σ(seq k).1) = σ(seq j).1 = (seq (j+1)).1
              obtain ⟨hj_ne, hseq_jp1⟩ := hB_response j hj_odd (by omega)
              have hpos_eq : (seq k).1 = (seq (j + 1)).1 := by
                -- heq : σ (seq k).1 hk_nonzero = (seq j).1
                -- So (seq j).1 = σ (seq k).1 hk_nonzero
                -- Applying σ: σ (seq j).1 hj_ne should equal (seq k).1
                -- hseq_jp1: (seq (j+1)).1 = σ (seq j).1 hj_ne
                -- So we need: (seq k).1 = σ (seq j).1 hj_ne
                have heq' : (seq j).1 = σ (seq k).1 hk_nonzero := heq.symm
                -- Use σ_inj: if σ x = σ y, then x = y
                -- We have (seq j).1 = σ (seq k).1, so σ (seq j).1 = σ (σ (seq k).1) = (seq k).1
                -- But the proof terms differ...
                -- Let's use extensionality directly
                have hσj_eq_k : σ (seq j).1 hj_ne = (seq k).1 := by
                  have h_σk_ne := σ_ne_zero (seq k).1 hk_nonzero
                  -- (seq j).1 = σ (seq k).1 hk_nonzero, and σ is involution
                  -- So σ (seq j).1 = σ (σ (seq k).1) = (seq k).1
                  have key : σ (seq j).1 hj_ne = σ (σ (seq k).1 hk_nonzero) h_σk_ne :=
                    σ_congr _ _ _ _ heq'
                  rw [key, σ_invol]
                rw [← hσj_eq_k, hseq_jp1]
              -- j + 1 ≤ k. If j + 1 = k, we get (seq k).1 = (seq k).1 ✓
              -- If j + 1 < k, contradiction with distinctness
              rcases eq_or_lt_of_le (Nat.add_one_le_iff.mpr hj_lt) with hjp1_eq | hjp1_lt
              · -- j + 1 = k: but j is odd and k is odd, so j + 1 is even ≠ k
                have heven_jp1 : Even (j + 1) := Odd.add_one hj_odd
                have hodd_k : Odd k := hodd
                rw [← hjp1_eq] at hodd_k
                -- Even (j + 1) and Odd (j + 1) is a contradiction
                rcases heven_jp1 with ⟨m1, hm1⟩
                rcases hodd_k with ⟨m2, hm2⟩
                omega
              · -- j + 1 < k
                exact hpos_distinct k (j + 1) (by omega) hjp1_lt (le_refl k) hpos_eq

      -- Given these, B's move is valid
      have hB_valid : strategyB n (seq k) ∈ (seq k).validNext :=
        strategyB_valid (seq k) hk_nonzero hσ_in_remaining

      rw [hB_move] at hk_invalid
      exact hk_invalid hB_valid

#print axioms putnam_2025_a3
