import Mathlib
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace TriangleGame

/-- A triangle, viewed as the multiset of its three interior angles (in degrees):
positive reals summing to `180`. -/
def IsTriangle (s : Multiset ℝ) : Prop :=
  s.card = 3 ∧ (∀ x ∈ s, 0 < x) ∧ s.sum = 180

/-- A triangle `s` has an interior angle equal to `θ`. -/
def HasAngle (θ : ℝ) (s : Multiset ℝ) : Prop := θ ∈ s

/-- One admissible cut of the triangle `s`, producing children `L` and `R`. -/
def IsCut (s L R : Multiset ℝ) : Prop :=
  ∃ α β γ x : ℝ,
    s = {α, β, γ} ∧ γ < x ∧ x < 180 - β ∧
      L = {β, x, 180 - β - x} ∧ R = {γ, 180 - x, x - γ}

inductive MulanWins (θ : ℝ) : Multiset ℝ → Prop
  | win {s : Multiset ℝ} (h : HasAngle θ s) : MulanWins θ s
  | move {s L R : Multiset ℝ} (hcut : IsCut s L R)
      (hL : MulanWins θ L) (hR : MulanWins θ R) : MulanWins θ s

def MulanCanGuarantee (θ : ℝ) : Prop :=
  ∀ s : Multiset ℝ, IsTriangle s → MulanWins θ s

/-- `y` is a positive natural multiple of `θ`. -/
def Marked (θ y : ℝ) : Prop := ∃ m : ℕ, 1 ≤ m ∧ y = (m : ℝ) * θ

/-- `s` is a valid triangle none of whose angles is marked. -/
def Safe (θ : ℝ) (s : Multiset ℝ) : Prop := IsTriangle s ∧ ∀ y ∈ s, ¬ Marked θ y

/-! ## Toolkit: multiset coordinate normalization -/

/-- Membership in a three-element multiset. -/
lemma mem_triple {a b c x : ℝ} :
    x ∈ ({a, b, c} : Multiset ℝ) ↔ x = a ∨ x = b ∨ x = c := by
  simp [Multiset.insert_eq_cons, Multiset.mem_cons]

/-- Constructor: three positive reals summing to 180 form a triangle. -/
lemma isTriangle_triple {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a + b + c = 180) : IsTriangle ({a, b, c} : Multiset ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · intro x hx
    rw [mem_triple] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
    linarith

/-- Destructor: a triangle with a chosen angle `a` can be written `{a,b,c}`. -/
lemma triangle_of_mem {s : Multiset ℝ} (hs : IsTriangle s) {a : ℝ} (ha : a ∈ s) :
    ∃ b c : ℝ, s = ({a, b, c} : Multiset ℝ) ∧ 0 < b ∧ 0 < c ∧ a + b + c = 180 := by
  obtain ⟨x, y, z, hxyz⟩ := Multiset.card_eq_three.mp hs.1
  -- reorder so that `a` is the first coordinate
  have key : ∃ b c : ℝ, s = ({a, b, c} : Multiset ℝ) := by
    rw [hxyz] at ha
    rw [mem_triple] at ha
    rcases ha with h | h | h
    · rw [← h] at hxyz
      exact ⟨y, z, hxyz⟩
    · rw [← h] at hxyz
      refine ⟨x, z, ?_⟩
      rw [hxyz]
      simp only [Multiset.insert_eq_cons]
      rw [Multiset.cons_swap x a]
    · rw [← h] at hxyz
      refine ⟨x, y, ?_⟩
      rw [hxyz]
      show x ::ₘ y ::ₘ a ::ₘ (0 : Multiset ℝ) = a ::ₘ x ::ₘ y ::ₘ 0
      rw [Multiset.cons_swap y a, Multiset.cons_swap x a]
  obtain ⟨b, c, habc⟩ := key
  refine ⟨b, c, habc, ?_, ?_, ?_⟩
  · apply hs.2.1
    rw [habc, mem_triple]; right; left; rfl
  · apply hs.2.1
    rw [habc, mem_triple]; right; right; rfl
  · have := hs.2.2
    rw [habc] at this
    simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at this
    linarith

/-- Cut normalization: extract positive witnesses and both children's validity. -/
lemma cut_witnesses {s L R : Multiset ℝ} (hs : IsTriangle s) (hcut : IsCut s L R) :
    ∃ α β γ x : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 180 ∧
      γ < x ∧ x < 180 - β ∧
      s = {α, β, γ} ∧ L = {β, x, 180 - β - x} ∧ R = {γ, 180 - x, x - γ} ∧
      IsTriangle L ∧ IsTriangle R := by
  obtain ⟨α, β, γ, x, hs_eq, hγx, hx, hL, hR⟩ := hcut
  have hα : 0 < α := by
    apply hs.2.1; rw [hs_eq, mem_triple]; left; rfl
  have hβ : 0 < β := by
    apply hs.2.1; rw [hs_eq, mem_triple]; right; left; rfl
  have hγ : 0 < γ := by
    apply hs.2.1; rw [hs_eq, mem_triple]; right; right; rfl
  have hsum : α + β + γ = 180 := by
    have := hs.2.2
    rw [hs_eq] at this
    simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at this
    linarith
  refine ⟨α, β, γ, x, hα, hβ, hγ, hsum, hγx, hx, hs_eq, hL, hR, ?_, ?_⟩
  · rw [hL]
    apply isTriangle_triple hβ (by linarith) (by linarith)
    ring
  · rw [hR]
    apply isTriangle_triple hγ (by linarith) (by linarith)
    ring

/-! ## Necessity: the obstruction when `180` is unmarked -/

/-- A valid triangle `{a,b,c}` that is not safe, with `a` unmarked, has a marked
    `b` or `c`. -/
private lemma not_safe_triple {θ a b c : ℝ}
    (hval : IsTriangle ({a, b, c} : Multiset ℝ))
    (hunsafe : ¬ Safe θ ({a, b, c} : Multiset ℝ)) (ha : ¬ Marked θ a) :
    Marked θ b ∨ Marked θ c := by
  by_contra h
  push_neg at h
  refine hunsafe ⟨hval, ?_⟩
  intro y hy
  rw [mem_triple] at hy
  rcases hy with rfl | rfl | rfl
  · exact ha
  · exact h.1
  · exact h.2

/-- If the parent is safe and `180` is unmarked, at least one child of any cut is safe. -/
lemma safe_child {θ : ℝ} (hθ : 0 < θ) (hT : ¬ Marked θ 180)
    {s L R : Multiset ℝ} (hsafe : Safe θ s) (hcut : IsCut s L R) :
    Safe θ L ∨ Safe θ R := by
  obtain ⟨α, β, γ, x, hα, hβ, hγ, hsum, hγx, hx, hs, hL, hR, hTL, hTR⟩ :=
    cut_witnesses hsafe.1 hcut
  have huα : ¬ Marked θ α := hsafe.2 α (by rw [hs, mem_triple]; left; rfl)
  have huβ : ¬ Marked θ β := hsafe.2 β (by rw [hs, mem_triple]; right; left; rfl)
  have huγ : ¬ Marked θ γ := hsafe.2 γ (by rw [hs, mem_triple]; right; right; rfl)
  by_contra hcon
  push_neg at hcon
  obtain ⟨hnL, hnR⟩ := hcon
  rw [hL] at hnL hTL
  rw [hR] at hnR hTR
  have hcL := not_safe_triple hTL hnL huβ
  have hcR := not_safe_triple hTR hnR huγ
  rcases hcL with hmx | hmL
  · rcases hcR with hkx | hkR
    · -- x = m·θ, 180-x = k·θ  ⟹  Marked θ 180
      obtain ⟨m, hm, hmx'⟩ := hmx
      obtain ⟨k, hk, hkx'⟩ := hkx
      refine hT ⟨m + k, by omega, ?_⟩
      push_cast
      have h1 : ((m : ℝ) + k) * θ = (m : ℝ) * θ + (k : ℝ) * θ := by ring
      linarith [hmx', hkx', h1]
    · -- x = m·θ, x-γ = k·θ  ⟹  γ = (m-k)·θ, Marked θ γ
      obtain ⟨m, hm, hmx'⟩ := hmx
      obtain ⟨k, hk, hkx'⟩ := hkR
      have hg : γ = ((m : ℝ) - (k : ℝ)) * θ := by
        have h1 : ((m : ℝ) - (k : ℝ)) * θ = (m : ℝ) * θ - (k : ℝ) * θ := by ring
        linarith [hmx', hkx', h1]
      have hkm : (k : ℝ) < (m : ℝ) := by nlinarith [hγ, hθ, hg]
      have hkm_nat : k < m := by exact_mod_cast hkm
      exact huγ ⟨m - k, by omega, by
        rw [Nat.cast_sub (le_of_lt hkm_nat)]; exact hg⟩
  · rcases hcR with hkx | hkR
    · -- 180-β-x = m·θ, 180-x = k·θ  ⟹  β = (k-m)·θ, Marked θ β
      obtain ⟨m, hm, hmL'⟩ := hmL
      obtain ⟨k, hk, hkx'⟩ := hkx
      have hg : β = ((k : ℝ) - (m : ℝ)) * θ := by
        have h1 : ((k : ℝ) - (m : ℝ)) * θ = (k : ℝ) * θ - (m : ℝ) * θ := by ring
        linarith [hmL', hkx', h1]
      have hmk : (m : ℝ) < (k : ℝ) := by nlinarith [hβ, hθ, hg]
      have hmk_nat : m < k := by exact_mod_cast hmk
      exact huβ ⟨k - m, by omega, by
        rw [Nat.cast_sub (le_of_lt hmk_nat)]; exact hg⟩
    · -- 180-β-x = m·θ, x-γ = k·θ  ⟹  α = (m+k)·θ, Marked θ α
      obtain ⟨m, hm, hmL'⟩ := hmL
      obtain ⟨k, hk, hkx'⟩ := hkR
      refine huα ⟨m + k, by omega, ?_⟩
      push_cast
      have h1 : ((m : ℝ) + k) * θ = (m : ℝ) * θ + (k : ℝ) * θ := by ring
      linarith [hmL', hkx', hsum, h1]

/-- Explicit safe starting triangle when `180` is unmarked. -/
lemma safe_start {θ : ℝ} (h0 : 0 < θ) (h180 : θ < 180) (hT : ¬ Marked θ 180) :
    Safe θ ({θ / 2, θ / 2, 180 - θ} : Multiset ℝ) := by
  refine ⟨isTriangle_triple (by linarith) (by linarith) (by linarith) (by ring), ?_⟩
  intro y hy
  rw [mem_triple] at hy
  rcases hy with rfl | rfl | rfl
  · rintro ⟨m, hm, heq⟩
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith [heq, h0, hm1]
  · rintro ⟨m, hm, heq⟩
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith [heq, h0, hm1]
  · rintro ⟨m, hm, heq⟩
    refine hT ⟨m + 1, by omega, ?_⟩
    push_cast
    have h1 : ((m : ℝ) + 1) * θ = (m : ℝ) * θ + θ := by ring
    linarith [heq, h1]

/-- No safe triangle is winning. -/
lemma safe_nonwin {θ : ℝ} (hθ : 0 < θ) (hT : ¬ Marked θ 180)
    {s : Multiset ℝ} (hsafe : Safe θ s) : ¬ MulanWins θ s := by
  suffices h : ∀ t, MulanWins θ t → Safe θ t → False by
    exact fun hwin => h s hwin hsafe
  intro t hwin
  induction hwin with
  | @win t h =>
    intro hsafe'
    exact hsafe'.2 θ h ⟨1, le_refl 1, by push_cast; ring⟩
  | @move t L R hcut hL hR ihL ihR =>
    intro hsafe'
    rcases safe_child hθ hT hsafe' hcut with hsL | hsR
    · exact ihL hsL
    · exact ihR hsR

/-! ## Sufficiency: winning when `180 = n·θ` -/

/-- The peeling cut at apex `a > θ`. -/
lemma peeling_cut {θ : ℝ} (hθ : 0 < θ) {a b c : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hsum : a + b + c = 180) (haθ : θ < a) :
    IsCut ({a, b, c} : Multiset ℝ) ({b, 180 - b - θ, θ} : Multiset ℝ)
      ({c, b + θ, a - θ} : Multiset ℝ) := by
  refine ⟨a, b, c, 180 - b - θ, rfl, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · have e : (180 : ℝ) - b - (180 - b - θ) = θ := by ring
    rw [e]
  · have e1 : (180 : ℝ) - (180 - b - θ) = b + θ := by ring
    have e2 : (180 - b - θ) - c = a - θ := by linear_combination -hsum
    rw [e1, e2]

/-- A valid triangle containing a positive natural multiple `m·θ` is winning. -/
lemma marked_angle_win {θ : ℝ} (hθ : 0 < θ)
    {s : Multiset ℝ} (hs : IsTriangle s) {m : ℕ} (hm : 1 ≤ m)
    (hmem : (m : ℝ) * θ ∈ s) : MulanWins θ s := by
  induction m, hm using Nat.le_induction generalizing s with
  | base =>
    refine MulanWins.win ?_
    show θ ∈ s
    simpa using hmem
  | succ m hm ih =>
    obtain ⟨b, c, hs_eq, hb, hc, hsum⟩ := triangle_of_mem hs hmem
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hmθ : (0 : ℝ) < (m : ℝ) * θ := mul_pos hmpos hθ
    have haθ : θ < ((m + 1 : ℕ) : ℝ) * θ := by push_cast; nlinarith
    have hcut := peeling_cut hθ hb hc hsum haθ
    have hL : MulanWins θ ({b, 180 - b - θ, θ} : Multiset ℝ) :=
      MulanWins.win (mem_triple.mpr (Or.inr (Or.inr rfl)))
    have hRtri : IsTriangle ({c, b + θ, ((m + 1 : ℕ) : ℝ) * θ - θ} : Multiset ℝ) :=
      isTriangle_triple hc (by linarith) (by linarith) (by linarith)
    have hRmem : ((m : ℕ) : ℝ) * θ ∈
        ({c, b + θ, ((m + 1 : ℕ) : ℝ) * θ - θ} : Multiset ℝ) :=
      mem_triple.mpr (Or.inr (Or.inr (by push_cast; ring)))
    have hR : MulanWins θ ({c, b + θ, ((m + 1 : ℕ) : ℝ) * θ - θ} : Multiset ℝ) :=
      ih hRtri hRmem
    rw [hs_eq]
    exact MulanWins.move hcut hL hR

/-- One-move finish from a small angle `0 < c < θ` (with `180 = n·θ`, `n ≥ 2`). -/
lemma small_angle_finish {θ : ℝ} (hθ : 0 < θ) {n : ℕ} (hn : 2 ≤ n)
    (hT : (180 : ℝ) = (n : ℝ) * θ)
    {s : Multiset ℝ} (hs : IsTriangle s) {c : ℝ} (hc0 : 0 < c) (hcθ : c < θ)
    (hmem : c ∈ s) : MulanWins θ s := by
  obtain ⟨y, z, hs_eq, hy, hz, hsum⟩ := triangle_of_mem hs hmem
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hθ90 : θ ≤ 90 := by
    nlinarith [hT, hn2, hθ, mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - 2) hθ.le]
  obtain ⟨a, b, hs_eq2, hab_sum, hθa⟩ :
      ∃ a b : ℝ, s = ({a, b, c} : Multiset ℝ) ∧ a + b + c = 180 ∧ θ < a + c := by
    rcases le_total y z with hyz | hyz
    · refine ⟨z, y, ?_, by linarith, by linarith⟩
      rw [hs_eq]
      ext w
      simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
      ring
    · refine ⟨y, z, ?_, by linarith, by linarith⟩
      rw [hs_eq]
      ext w
      simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
      ring
  have hcut : IsCut s ({b, θ, 180 - b - θ} : Multiset ℝ)
      ({c, 180 - θ, θ - c} : Multiset ℝ) := by
    rw [hs_eq2]
    exact ⟨a, b, c, θ, rfl, hcθ, by linarith, rfl, rfl⟩
  have hL : MulanWins θ ({b, θ, 180 - b - θ} : Multiset ℝ) :=
    MulanWins.win (mem_triple.mpr (Or.inr (Or.inl rfl)))
  have hRtri : IsTriangle ({c, 180 - θ, θ - c} : Multiset ℝ) :=
    isTriangle_triple hc0 (by linarith) (by linarith) (by ring)
  have hn1 : (1 : ℕ) ≤ n := by omega
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn1, Nat.cast_one]
  have hRmem : ((n - 1 : ℕ) : ℝ) * θ ∈ ({c, 180 - θ, θ - c} : Multiset ℝ) := by
    refine mem_triple.mpr (Or.inr (Or.inl ?_))
    rw [hcast, hT]; ring
  have hR : MulanWins θ ({c, 180 - θ, θ - c} : Multiset ℝ) :=
    marked_angle_win hθ hRtri (by omega) hRmem
  exact MulanWins.move hcut hL hR

/-- Every valid triangle is winning when `180 = n·θ` with `n ≥ 2`. -/
lemma universal_win {θ : ℝ} (hθ : 0 < θ) {n : ℕ} (hn : 2 ≤ n)
    (hT : (180 : ℝ) = (n : ℝ) * θ) : MulanCanGuarantee θ := by
  have Pq : ∀ q : ℕ, 1 ≤ q → ∀ (s : Multiset ℝ) (a : ℝ),
      IsTriangle s → a ∈ s → 0 < a → a ≤ (q : ℝ) * θ → MulanWins θ s := by
    intro q hq
    induction q, hq using Nat.le_induction with
    | base =>
      intro s a hs ha ha0 hle
      simp only [Nat.cast_one, one_mul] at hle
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact small_angle_finish hθ hn hT hs ha0 hlt ha
      · exact MulanWins.win (by rw [HasAngle, ← heq]; exact ha)
    | succ q hq ih =>
      intro s a hs ha ha0 hle
      push_cast at hle
      have hexp : ((q : ℝ) + 1) * θ = (q : ℝ) * θ + θ := by ring
      rw [hexp] at hle
      by_cases hcase : a ≤ (q : ℝ) * θ
      · exact ih s a hs ha ha0 hcase
      · push_neg at hcase
        have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
        have hθq : θ ≤ (q : ℝ) * θ := by nlinarith [hθ, hq1]
        have hθa : θ < a := lt_of_le_of_lt hθq hcase
        obtain ⟨b, c, hseq, hb, hc, hsum⟩ := triangle_of_mem hs ha
        have hcut := peeling_cut hθ hb hc hsum hθa
        have hLwin : MulanWins θ ({b, 180 - b - θ, θ} : Multiset ℝ) :=
          MulanWins.win (by rw [HasAngle, mem_triple]; right; right; rfl)
        have haθ0 : 0 < a - θ := by linarith
        have hbθ0 : 0 < b + θ := by linarith
        have hRsum : c + (b + θ) + (a - θ) = 180 := by linarith
        have hRtri : IsTriangle ({c, b + θ, a - θ} : Multiset ℝ) :=
          isTriangle_triple hc hbθ0 haθ0 hRsum
        have haθmem : (a - θ) ∈ ({c, b + θ, a - θ} : Multiset ℝ) :=
          mem_triple.mpr (by right; right; rfl)
        have haθle : a - θ ≤ (q : ℝ) * θ := by linarith
        have hRwin : MulanWins θ ({c, b + θ, a - θ} : Multiset ℝ) :=
          ih _ (a - θ) hRtri haθmem haθ0 haθle
        rw [hseq]
        exact MulanWins.move hcut hLwin hRwin
  intro s hs
  have hcard : s.card = 3 := hs.1
  have hne : s ≠ 0 := by
    intro h; rw [h] at hcard; simp at hcard
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
  have ha0 : 0 < a := hs.2.1 a ha
  obtain ⟨N, hN⟩ := exists_nat_ge (a / θ)
  have haN : a ≤ (N : ℝ) * θ := (div_le_iff₀ hθ).mp hN
  set q := max N 1 with hqdef
  have hq1 : 1 ≤ q := le_max_right N 1
  have hNq : (N : ℝ) ≤ (q : ℝ) := by exact_mod_cast le_max_left N 1
  have haq : a ≤ (q : ℝ) * θ :=
    le_trans haN (mul_le_mul_of_nonneg_right hNq (le_of_lt hθ))
  exact Pq q hq1 s a hs ha ha0 haq

/-! ## Arithmetic bridge and main assembly -/

/-- `180` is marked iff `θ = 180/n` for some `n ≥ 2`. -/
lemma arithmetic_bridge {θ : ℝ} (h0 : 0 < θ) (h180 : θ < 180) :
    Marked θ 180 ↔ ∃ n : ℕ, 2 ≤ n ∧ θ = 180 / (n : ℝ) := by
  constructor
  · rintro ⟨m, hm, heq⟩
    have hmθ : θ < (m : ℝ) * θ := by rw [← heq]; exact h180
    have hm1 : (1 : ℝ) < (m : ℝ) := by
      have h : (1 : ℝ) * θ < (m : ℝ) * θ := by rw [one_mul]; exact hmθ
      exact lt_of_mul_lt_mul_right h (le_of_lt h0)
    have hm1n : 1 < m := by exact_mod_cast hm1
    have hmpos : (0 : ℝ) < (m : ℝ) := by
      have : 0 < m := by omega
      exact_mod_cast this
    refine ⟨m, by omega, ?_⟩
    rw [eq_div_iff (ne_of_gt hmpos)]
    linarith [heq, mul_comm (m : ℝ) θ]
  · rintro ⟨n, hn, heq⟩
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    refine ⟨n, by omega, ?_⟩
    rw [heq]
    field_simp

theorem main_theorem (θ : ℝ) (hθ0 : 0 < θ) (hθ180 : θ < 180) :
    MulanCanGuarantee θ ↔ ∃ n : ℕ, 2 ≤ n ∧ θ = 180 / n := by
  rw [← arithmetic_bridge hθ0 hθ180]
  constructor
  · intro hg
    by_contra hT
    have hsafe := safe_start hθ0 hθ180 hT
    have hwin := hg _ hsafe.1
    exact (safe_nonwin hθ0 hT hsafe) hwin
  · rintro ⟨m, hm, heq⟩
    have hmθ : θ < (m : ℝ) * θ := by rw [← heq]; exact hθ180
    have hm1 : (1 : ℝ) < (m : ℝ) := by
      have h : (1 : ℝ) * θ < (m : ℝ) * θ := by rw [one_mul]; exact hmθ
      exact lt_of_mul_lt_mul_right h (le_of_lt hθ0)
    have hm1n : 1 < m := by exact_mod_cast hm1
    exact universal_win hθ0 (by omega) heq

end TriangleGame

#print axioms TriangleGame.main_theorem
