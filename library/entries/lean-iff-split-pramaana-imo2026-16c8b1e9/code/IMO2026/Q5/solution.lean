import Mathlib
import Mathlib.Tactic

/-- The answer is a *set* of functions (the complete solution family). -/
abbrev AnswerType := Set (ℝ → ℝ)

/-- The functional inequality condition on `f`:
    for every positive `x, y`,
    `sqrt((x^2 + f(y)^2)/2) ≥ (f(x) + y)/2 ≥ sqrt(x * f(y))`. -/
def Fact_condition (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, 0 < x → 0 < y →
    Real.sqrt ((x^2 + (f y)^2) / 2) ≥ (f x + y) / 2 ∧
    (f x + y) / 2 ≥ Real.sqrt (x * f y)

/-- `f` maps positive reals to positive reals. -/
def Assumption_pos (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → 0 < f x

/-- BEGIN ANSWER -/
def answer : AnswerType := {f | ∃ c : ℝ, 0 ≤ c ∧ ∀ x : ℝ, 0 < x → f x = x + c}
/-- END ANSWER -/

lemma ineqA (f : ℝ → ℝ) (ha : Assumption_pos f) (hf : Fact_condition f)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (f x + y)^2 ≤ 2*x^2 + 2*(f y)^2 := by
  obtain ⟨h1, _⟩ := hf x y hx hy
  have hnn : (0:ℝ) ≤ (x^2 + (f y)^2)/2 := by positivity
  have hs : Real.sqrt ((x^2 + (f y)^2)/2) ^ 2 = (x^2 + (f y)^2)/2 :=
    Real.sq_sqrt hnn
  have hfx := ha x hx
  nlinarith [Real.sqrt_nonneg ((x^2 + (f y)^2)/2), h1]

lemma ineqB (f : ℝ → ℝ) (ha : Assumption_pos f) (hf : Fact_condition f)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    4*(x * f y) ≤ (f x + y)^2 := by
  obtain ⟨_, h2⟩ := hf x y hx hy
  have hfy := ha y hy
  have hnn : (0:ℝ) ≤ x * f y := by positivity
  have hs : Real.sqrt (x * f y) ^ 2 = x * f y := Real.sq_sqrt hnn
  nlinarith [Real.sqrt_nonneg (x * f y), h2]

lemma key_ff (f : ℝ → ℝ) (ha : Assumption_pos f) (hf : Fact_condition f)
    {y : ℝ} (hy : 0 < y) : f (f y) = 2 * f y - y := by
  have hfy := ha y hy
  have hA := ineqA f ha hf hfy hy
  have hB := ineqB f ha hf hfy hy
  have hffy := ha (f y) hfy
  have he : (f (f y) + y)^2 = 4*(f y)^2 :=
    le_antisymm (by nlinarith) (by nlinarith)
  have hz : (f (f y) + y - 2 * f y) * (f (f y) + y + 2 * f y) = 0 := by
    linear_combination he
  rcases mul_eq_zero.mp hz with h | h
  · linarith
  · exfalso; linarith

lemma orbit (f : ℝ → ℝ) (ha : Assumption_pos f) (hf : Fact_condition f)
    {y : ℝ} (hy : 0 < y) (n : ℕ) :
    0 < y + n * (f y - y) ∧
      f (y + n * (f y - y)) = y + n * (f y - y) + (f y - y) := by
  induction n with
  | zero =>
    refine ⟨by simpa using hy, ?_⟩
    norm_num
  | succ n ih =>
    obtain ⟨hpos, hstep⟩ := ih
    have hkey := key_ff f ha hf hpos
    have hfp := ha _ hpos
    have h1 : y + ((n:ℝ)+1)*(f y - y) = f (y + (n:ℝ)*(f y - y)) := by
      rw [hstep]; ring
    constructor
    · rw [hstep] at hfp
      push_cast
      linarith
    · push_cast
      rw [h1, hkey, hstep]
      ring

lemma d_nonneg (f : ℝ → ℝ) (ha : Assumption_pos f) (hf : Fact_condition f)
    {y : ℝ} (hy : 0 < y) : 0 ≤ f y - y := by
  by_contra h
  have h : f y - y < 0 := not_le.mp h
  set d := f y - y with hd
  have hdpos : 0 < -d := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (y / (-d))
  have h2 : y / (-d) * (-d) < n * (-d) := mul_lt_mul_of_pos_right hn hdpos
  rw [div_mul_cancel₀ _ (ne_of_gt hdpos)] at h2
  have hnd : (n:ℝ) * (-d) = -((n:ℝ)*d) := by ring
  rw [hnd] at h2
  have hpos := (orbit f ha hf hy n).1
  linarith

set_option maxHeartbeats 1000000 in
lemma pos_d_le (f : ℝ → ℝ) (ha : Assumption_pos f) (hf : Fact_condition f)
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (hb : 0 < f v - v) :
    f u - u ≤ f v - v := by
  by_contra hab
  have hab : f v - v < f u - u := not_le.mp hab
  have ha0 : 0 < f u - u := lt_trans hb hab
  set a := f u - u with hadef
  set b := f v - v with hbdef
  have hδ : 0 < a - b := by linarith
  set M := max (v - u) (b^2/(a-b)) with hM
  obtain ⟨n, hn⟩ := exists_nat_ge (M / a)
  have hna : M ≤ (n:ℝ) * a := (div_le_iff₀ ha0).mp hn
  have hPv : v ≤ u + (n:ℝ) * a := by
    have := le_max_left (v - u) (b^2/(a-b))
    have := le_trans this hna
    linarith
  obtain ⟨hPpos, hfP⟩ := orbit f ha hf hu n
  set m := ⌈(u + (n:ℝ)*a - v)/b⌉₊ with hmdef
  have hdiv0 : 0 ≤ (u + (n:ℝ)*a - v)/b := div_nonneg (by linarith) hb.le
  have hm1 : (u + (n:ℝ)*a - v)/b ≤ (m:ℝ) := Nat.le_ceil _
  have hm2 : (m:ℝ) < (u + (n:ℝ)*a - v)/b + 1 := Nat.ceil_lt_add_one hdiv0
  have hy1 : u + (n:ℝ)*a ≤ v + (m:ℝ)*b := by
    rw [div_le_iff₀ hb] at hm1
    linarith
  have hy2 : v + (m:ℝ)*b < u + (n:ℝ)*a + b := by
    have h2' := mul_lt_mul_of_pos_right hm2 hb
    have h2'' : ((u + (n:ℝ)*a - v)/b + 1) * b = u + (n:ℝ)*a - v + b := by
      field_simp
    rw [h2''] at h2'
    linarith
  obtain ⟨hympos, hfym⟩ := orbit f ha hf hv m
  have hA := ineqA f ha hf hPpos hympos
  rw [hfP, hfym] at hA
  have hPδ : b^2 < (u + (n:ℝ)*a) * (a - b) := by
    have h := le_trans (le_max_right (v - u) (b^2/(a-b))) hna
    rw [div_le_iff₀ hδ] at h
    nlinarith
  have hsq : (v + (m:ℝ)*b + b - (u + (n:ℝ)*a))^2 < 4*b^2 := by nlinarith
  have hkey2 : (v + (m:ℝ)*b + b - (u + (n:ℝ)*a))^2 ≥
      2*(a-b)*((u + (n:ℝ)*a) + (v + (m:ℝ)*b + b)) + (a-b)^2 := by nlinarith [hA]
  have hprod : 2*(a-b)*((u + (n:ℝ)*a) + b) ≤ 2*(a-b)*(v + (m:ℝ)*b + b) := by
    have : (u + (n:ℝ)*a) + b ≤ v + (m:ℝ)*b + b := by linarith
    exact mul_le_mul_of_nonneg_left this (by linarith)
  nlinarith [hkey2, hsq, hPδ, hprod, hb, hδ]

lemma no_mixed (f : ℝ → ℝ) (ha : Assumption_pos f) (hf : Fact_condition f)
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hfv : f v = v) (hfu : 0 < f u - u) : False := by
  set c := f u - u with hc
  have hcpos : 0 < c := hfu
  -- any non-fixed point has displacement exactly c
  have hdisp : ∀ x : ℝ, 0 < x → f x ≠ x → f x - x = c := by
    intro x hx hne
    have h0 := d_nonneg f ha hf hx
    have hpos : 0 < f x - x := lt_of_le_of_ne h0 (fun h => hne (by linarith))
    exact le_antisymm (pos_d_le f ha hf hx hu hcpos) (pos_d_le f ha hf hu hx hpos)
  -- fixed points are bounded above
  have hbdd : ∀ x : ℝ, 0 < x → f x = x → x ≤ max u (c/4) := by
    intro x hx hfx
    by_contra hgt
    have hgt : max u (c/4) < x := not_le.mp hgt
    have hxu : u < x := lt_of_le_of_lt (le_max_left _ _) hgt
    have hxc : c/4 < x := lt_of_le_of_lt (le_max_right _ _) hgt
    set n := ⌊(x - u)/c⌋₊ with hn
    have hdiv : 0 ≤ (x - u)/c := div_nonneg (by linarith) hcpos.le
    have h1 : (n:ℝ) ≤ (x - u)/c := Nat.floor_le hdiv
    have h2 : (x - u)/c < (n:ℝ) + 1 := Nat.lt_floor_add_one _
    have h1' : (n:ℝ) * c ≤ x - u := (le_div_iff₀ hcpos).mp h1
    have h2' : x - u < ((n:ℝ) + 1) * c := (div_lt_iff₀ hcpos).mp h2
    obtain ⟨hypos, hfy⟩ := orbit f ha hf hu n
    have hB := ineqB f ha hf hx hypos
    rw [hfx, hfy] at hB
    nlinarith [h1', h2', hxc, hcpos, hx, hB]
  -- consider the supremum of the set of fixed points
  set S : Set ℝ := {x : ℝ | 0 < x ∧ f x = x} with hS
  have hne : v ∈ S := ⟨hv, hfv⟩
  have hbddS : BddAbove S := ⟨max u (c/4), fun x hx => hbdd x hx.1 hx.2⟩
  set t := sSup S with ht
  have htv : v ≤ t := le_csSup hbddS hne
  have htpos : 0 < t := lt_of_lt_of_le hv htv
  -- the point just above t is not fixed
  have hx'pos : 0 < t + c/4 := by linarith
  have hx'ne : f (t + c/4) ≠ t + c/4 := by
    intro hfix
    have : t + c/4 ≤ t := le_csSup hbddS ⟨hx'pos, hfix⟩
    linarith
  have hfx' : f (t + c/4) = t + c/4 + c := by
    have := hdisp (t + c/4) hx'pos hx'ne
    linarith
  -- a fixed point just below t
  obtain ⟨y', hy'S, hy'gt⟩ := exists_lt_of_lt_csSup ⟨v, hne⟩
    (show t - c/4 < t by linarith)
  have hy'le : y' ≤ t := le_csSup hbddS hy'S
  obtain ⟨hy'pos, hfy'⟩ := hy'S
  have hA := ineqA f ha hf hx'pos hy'pos
  rw [hfx', hfy'] at hA
  nlinarith [hA, hy'gt, hy'le, hcpos, hx'pos, hy'pos]

lemma g_const (f : ℝ → ℝ) (ha : Assumption_pos f) (hf : Fact_condition f)
    {x : ℝ} (hx : 0 < x) : f x - x = f 1 - 1 := by
  have h1 := d_nonneg f ha hf hx
  have h2 := d_nonneg f ha hf one_pos
  rcases eq_or_lt_of_le h1 with hx0 | hx0
  · rcases eq_or_lt_of_le h2 with h10 | h10
    · rw [← hx0, ← h10]
    · exact (no_mixed f ha hf one_pos hx (by linarith) h10).elim
  · rcases eq_or_lt_of_le h2 with h10 | h10
    · exact (no_mixed f ha hf hx one_pos (by linarith) hx0).elim
    · exact le_antisymm (pos_d_le f ha hf hx one_pos h10)
        (pos_d_le f ha hf one_pos hx hx0)

lemma easy_dir (f : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hfc : ∀ x : ℝ, 0 < x → f x = x + c) : Fact_condition f := by
  intro x y hx hy
  rw [hfc x hx, hfc y hy]
  constructor
  · rw [ge_iff_le]
    have h1 : ((x + c + y)/2)^2 ≤ (x^2 + (y+c)^2)/2 := by
      nlinarith [sq_nonneg (x - y - c)]
    have h2 : (0:ℝ) ≤ (x + c + y)/2 := by positivity
    calc (x + c + y)/2 = Real.sqrt (((x + c + y)/2)^2) := (Real.sqrt_sq h2).symm
      _ ≤ Real.sqrt ((x^2 + (y+c)^2)/2) := Real.sqrt_le_sqrt h1
  · rw [ge_iff_le]
    have h1 : x*(y+c) ≤ ((x + c + y)/2)^2 := by
      nlinarith [sq_nonneg (x - y - c)]
    have h2 : (0:ℝ) ≤ (x + c + y)/2 := by positivity
    calc Real.sqrt (x*(y+c)) ≤ Real.sqrt (((x + c + y)/2)^2) :=
        Real.sqrt_le_sqrt h1
      _ = (x + c + y)/2 := Real.sqrt_sq h2

theorem answer_correctness
    (f : ℝ → ℝ)
    (ha_pos : Assumption_pos f)
    : Fact_condition f ↔ f ∈ answer := by
  constructor
  · intro hf
    refine ⟨f 1 - 1, ?_, ?_⟩
    · have := d_nonneg f ha_pos hf (y := 1) one_pos
      linarith
    · intro x hx
      have := g_const f ha_pos hf hx
      linarith
  · rintro ⟨c, hc, hfc⟩
    exact easy_dir f c hc hfc
