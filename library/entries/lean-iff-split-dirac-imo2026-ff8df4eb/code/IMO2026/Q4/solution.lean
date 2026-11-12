import Mathlib
set_option backward.isDefEq.respectTransparency false

namespace TriangleGame

/-- A triangle, viewed as the multiset of its three interior angles (in degrees):
positive reals summing to `180`. -/
def IsTriangle (s : Multiset ℝ) : Prop :=
  s.card = 3 ∧ (∀ x ∈ s, 0 < x) ∧ s.sum = 180

/-- A triangle `s` has an interior angle equal to `θ`. -/
def HasAngle (θ : ℝ) (s : Multiset ℝ) : Prop := θ ∈ s

/-- One admissible cut of the triangle `s`, producing children `L` and `R`.

We pick an apex angle `α` and the two base angles `β, γ` (so `s = {α, β, γ}`), and a
cut parameter `x` in the open interval `(γ, 180 - β)`. The resulting two triangles
have angle multisets `L = {β, x, 180 - β - x}` and `R = {γ, 180 - x, x - γ}`.
Ranging over all `α, β, γ` with `s = {α, β, γ}` captures all three apex choices and
both assignments of the two base angles. -/
def IsCut (s L R : Multiset ℝ) : Prop :=
  ∃ α β γ x : ℝ,
    s = {α, β, γ} ∧ γ < x ∧ x < 180 - β ∧
      L = {β, x, 180 - β - x} ∧ R = {γ, 180 - x, x - γ}

/-- The set of triangles from which Mulan can force, in finitely many steps, a
triangle with an interior angle equal to `θ`, no matter how Shan-Yu discards.

This is the least predicate closed under:
* (`win`) if the current triangle already has an angle equal to `θ`, Mulan has won;
* (`move`) if Mulan can make a cut producing children `L` and `R` from *both* of
  which she wins (so whichever one Shan-Yu keeps, she still wins), then she wins
  from the current triangle.

Membership means Mulan wins in finitely many steps. -/
inductive MulanWins (θ : ℝ) : Multiset ℝ → Prop
  | win {s : Multiset ℝ} (h : HasAngle θ s) : MulanWins θ s
  | move {s L R : Multiset ℝ} (hcut : IsCut s L R)
      (hL : MulanWins θ L) (hR : MulanWins θ R) : MulanWins θ s

/-- Mulan can guarantee victory for the value `θ`: from every valid starting
triangle she wins in finitely many steps regardless of Shan-Yu's play. -/
def MulanCanGuarantee (θ : ℝ) : Prop :=
  ∀ s : Multiset ℝ, IsTriangle s → MulanWins θ s

/- ===================================================================
   SECTION 1 — Multiset toolkit
   =================================================================== -/

lemma mem_triple {x a b c : ℝ} :
    x ∈ ({a, b, c} : Multiset ℝ) ↔ x = a ∨ x = b ∨ x = c := by
  simp [Multiset.insert_eq_cons]

lemma card_triple (a b c : ℝ) : ({a, b, c} : Multiset ℝ).card = 3 := by
  simp [Multiset.insert_eq_cons]

lemma sum_triple (a b c : ℝ) : ({a, b, c} : Multiset ℝ).sum = a + b + c := by
  simp [Multiset.insert_eq_cons, add_assoc]

lemma triple_swap₁₂ (a b c : ℝ) : ({a, b, c} : Multiset ℝ) = {b, a, c} := by
  simp only [Multiset.insert_eq_cons]
  exact Multiset.cons_swap a b _

lemma triple_swap₂₃ (a b c : ℝ) : ({a, b, c} : Multiset ℝ) = {a, c, b} := by
  simp only [Multiset.insert_eq_cons]
  exact congrArg (a ::ₘ ·) (Multiset.cons_swap b c 0)

lemma isTriangle_triple {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 180) : IsTriangle ({a, b, c} : Multiset ℝ) := by
  refine ⟨card_triple a b c, ?_, ?_⟩
  · intro x hx
    rcases mem_triple.mp hx with rfl | rfl | rfl <;> assumption
  · rw [sum_triple]; exact h

lemma IsTriangle.exists_repr {s : Multiset ℝ} (hs : IsTriangle s) :
    ∃ a b c : ℝ, s = {a, b, c} ∧ 0 < a ∧ 0 < b ∧ 0 < c ∧ a + b + c = 180 := by
  obtain ⟨hcard, hpos, hsum⟩ := hs
  obtain ⟨a, b, c, rfl⟩ := Multiset.card_eq_three.mp hcard
  refine ⟨a, b, c, rfl, ?_, ?_, ?_, ?_⟩
  · exact hpos a (mem_triple.mpr (Or.inl rfl))
  · exact hpos b (mem_triple.mpr (Or.inr (Or.inl rfl)))
  · exact hpos c (mem_triple.mpr (Or.inr (Or.inr rfl)))
  · rw [sum_triple] at hsum; exact hsum

/-- ★ the WLOG lemma: ANY member can be put in apex position -/
lemma IsTriangle.exists_repr_apex {s : Multiset ℝ} (hs : IsTriangle s) {α : ℝ}
    (hα : α ∈ s) :
    ∃ β γ : ℝ, s = {α, β, γ} ∧ 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 180 := by
  obtain ⟨a, b, c, rfl, ha, hb, hc, hsum⟩ := hs.exists_repr
  rcases mem_triple.mp hα with rfl | rfl | rfl
  · exact ⟨b, c, rfl, ha, hb, hc, hsum⟩
  · exact ⟨a, c, triple_swap₁₂ a α c, hb, ha, hc, by linarith⟩
  · refine ⟨a, b, ?_, hc, ha, hb, by linarith⟩
    rw [triple_swap₂₃ a b α, triple_swap₁₂ a α b]

/- ===================================================================
   SECTION 2 — Elementary facts about θ = 180 / n  (see §5.2, §5.4)
   =================================================================== -/

lemma theta_pos {n : ℕ} (hn : 2 ≤ n) {θ : ℝ} (h : θ = 180 / n) : 0 < θ := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  rw [h]
  exact div_pos (by norm_num) hn0

lemma n_mul_theta {n : ℕ} (hn : 2 ≤ n) {θ : ℝ} (h : θ = 180 / n) :
    (n : ℝ) * θ = 180 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [h]
  field_simp

lemma div_iff_intMul {θ : ℝ} (hθ0 : 0 < θ) (hθ180 : θ < 180) :
    (∃ n : ℕ, 2 ≤ n ∧ θ = 180 / n) ↔ ∃ k : ℤ, (180 : ℝ) = (k : ℝ) * θ := by
  constructor
  · rintro ⟨n, hn, hθ⟩
    refine ⟨(n : ℤ), ?_⟩
    rw [Int.cast_natCast]
    exact (n_mul_theta hn hθ).symm
  · rintro ⟨k, hk⟩
    /- k > 0 since k * θ = 180 > 0 and θ > 0 -/
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      by_contra hc
      push_neg at hc
      nlinarith
    have hk1 : 1 ≤ k := by
      have h0 : (0 : ℤ) < k := by exact_mod_cast hkpos
      omega
    /- θ < 180 forces k ≠ 1, hence k ≥ 2 -/
    have hk2 : 2 ≤ k := by
      by_contra hc
      push_neg at hc
      have hk1' : k = 1 := by omega
      subst hk1'
      norm_num at hk
      linarith
    have h0 : (0 : ℤ) ≤ k := by omega
    refine ⟨k.toNat, by omega, ?_⟩
    have hcast : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg h0)
    rw [hcast, eq_div_iff (ne_of_gt hkpos)]
    linear_combination -hk

/- ===================================================================
   SECTION 3 — Backward direction (⇐)   (see §2, §5.2)
   =================================================================== -/

/-- **Key Lemma A.** A triangle containing a positive integer multiple of `θ` is a win.
Note: NO hypothesis `θ = 180 / n`. -/
lemma mulanWins_of_succ_mul {θ : ℝ} (hθ : 0 < θ) :
    ∀ (k : ℕ) (s : Multiset ℝ), IsTriangle s → ((k : ℝ) + 1) * θ ∈ s → MulanWins θ s := by
  intro k
  induction k with
  | zero =>
      intro s _ hmem
      refine MulanWins.win ?_
      show θ ∈ s
      have h1 : (((0 : ℕ) : ℝ) + 1) * θ = θ := by norm_num
      rwa [h1] at hmem
  | succ k ih =>
      intro s hs hmem
      /- the apex is `α = (k+2)·θ` -/
      have hmem' : ((k : ℝ) + 2) * θ ∈ s := by
        have h1 : ((k : ℝ) + 2) * θ = (((k + 1 : ℕ) : ℝ) + 1) * θ := by push_cast; ring
        rwa [h1]
      obtain ⟨β, γ, hseq, hα, hβ, hγ, hsum⟩ := hs.exists_repr_apex hmem'
      /- positivity of the residual apex `(k+1)·θ` -/
      have hkpos : (0 : ℝ) < ((k : ℝ) + 1) * θ := by
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        have : (0 : ℝ) < (k : ℝ) + 1 := by linarith
        exact mul_pos this hθ
      /- the third entry of `L` is exactly `(k+1)·θ` -/
      have hL3 : (180 : ℝ) - β - (γ + θ) = ((k : ℝ) + 1) * θ := by
        have h2 : ((k : ℝ) + 2) * θ = ((k : ℝ) + 1) * θ + θ := by ring
        rw [h2] at hsum
        linarith
      have hxlt : γ + θ < 180 - β := by linarith
      refine MulanWins.move
        (L := ({β, γ + θ, ((k : ℝ) + 1) * θ} : Multiset ℝ))
        (R := ({γ, 180 - (γ + θ), (γ + θ) - γ} : Multiset ℝ)) ?_ ?_ ?_
      · exact ⟨((k : ℝ) + 2) * θ, β, γ, γ + θ, hseq, by linarith, hxlt, by rw [hL3], rfl⟩
      · refine ih _ (isTriangle_triple hβ (by linarith) hkpos (by linarith)) ?_
        rw [mem_triple]
        exact Or.inr (Or.inr rfl)
      · refine MulanWins.win ?_
        show θ ∈ ({γ, 180 - (γ + θ), (γ + θ) - γ} : Multiset ℝ)
        rw [mem_triple]
        exact Or.inr (Or.inr (by ring))

/-- **Key Lemma B.** The opening move. -/
lemma exists_opening_cut {n : ℕ} (hn : 2 ≤ n) {θ : ℝ} (hθdef : θ = 180 / n)
    {s : Multiset ℝ} (hs : IsTriangle s) (hno : θ ∉ s) :
    ∃ L R : Multiset ℝ, IsCut s L R ∧
      IsTriangle L ∧ IsTriangle R ∧
      (∃ i : ℕ, ((i : ℝ) + 1) * θ ∈ L) ∧ (∃ j : ℕ, ((j : ℝ) + 1) * θ ∈ R) := by
  have hθ0 : 0 < θ := theta_pos hn hθdef
  have hnθ : (n : ℝ) * θ = 180 := n_mul_theta hn hθdef
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hθ90 : θ ≤ 90 := by nlinarith
  by_cases hcase : ∃ a ∈ s, θ < a
  · /- Case B1: some angle exceeds θ; use it as apex. -/
    obtain ⟨a, hamem, hagt⟩ := hcase
    obtain ⟨β, γ, hrepr, hapos, hβ, hγ, hsum⟩ := hs.exists_repr_apex hamem
    obtain ⟨m, hfl1, hfl2⟩ : ∃ m : ℕ, γ / θ < (m : ℝ) + 1 ∧ (m : ℝ) ≤ γ / θ :=
      ⟨⌊γ / θ⌋₊, Nat.lt_floor_add_one _, Nat.floor_le (le_of_lt (div_pos hγ hθ0))⟩
    have hgx : γ < ((m : ℝ) + 1) * θ := (div_lt_iff₀ hθ0).mp hfl1
    have hmθ : (m : ℝ) * θ ≤ γ := (le_div_iff₀ hθ0).mp hfl2
    have hexp : ((m : ℝ) + 1) * θ = (m : ℝ) * θ + θ := by ring
    have hxub : ((m : ℝ) + 1) * θ < 180 - β := by rw [hexp]; linarith
    have hx180 : ((m : ℝ) + 1) * θ < 180 := by linarith
    have hmn : m + 2 ≤ n := by
      have h1 : ((m : ℝ) + 1) * θ < (n : ℝ) * θ := by rw [hnθ]; exact hx180
      have h2 : (m : ℝ) + 1 < (n : ℝ) := lt_of_mul_lt_mul_right h1 hθ0.le
      have h3 : ((m + 1 : ℕ) : ℝ) < ((n : ℕ) : ℝ) := by push_cast; linarith
      have h4 : m + 1 < n := by exact_mod_cast h3
      omega
    have hjcast : ((n - m - 2 : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) - 2 := by
      have h5 : (n - m - 2) + (m + 2) = n := by omega
      have h7 : (((n - m - 2) + (m + 2) : ℕ) : ℝ) = ((n : ℕ) : ℝ) := by rw [h5]
      push_cast at h7
      linarith
    refine ⟨{β, ((m : ℝ) + 1) * θ, 180 - β - ((m : ℝ) + 1) * θ},
            {γ, 180 - ((m : ℝ) + 1) * θ, ((m : ℝ) + 1) * θ - γ}, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨a, β, γ, ((m : ℝ) + 1) * θ, hrepr, hgx, hxub, rfl, rfl⟩
    · exact isTriangle_triple hβ (by linarith) (by linarith) (by ring)
    · exact isTriangle_triple hγ (by linarith) (by linarith) (by ring)
    · exact ⟨m, mem_triple.mpr (Or.inr (Or.inl rfl))⟩
    · refine ⟨n - m - 2, ?_⟩
      have hval : (((n - m - 2 : ℕ) : ℝ) + 1) * θ = 180 - ((m : ℝ) + 1) * θ := by
        rw [hjcast]
        have hring : ((n : ℝ) - (m : ℝ) - 2 + 1) * θ = (n : ℝ) * θ - ((m : ℝ) + 1) * θ := by
          ring
        rw [hring, hnθ]
      rw [hval]
      exact mem_triple.mpr (Or.inr (Or.inl rfl))
  · /- Case B2: every angle is < θ (θ ∉ s rules out equality); cut at x = θ. -/
    push_neg at hcase
    obtain ⟨α, β, γ, hrepr, hα, hβ, hγ, hsum⟩ := hs.exists_repr
    have hβmem : β ∈ s := by rw [hrepr]; exact mem_triple.mpr (Or.inr (Or.inl rfl))
    have hγmem : γ ∈ s := by rw [hrepr]; exact mem_triple.mpr (Or.inr (Or.inr rfl))
    have hβlt : β < θ := by
      rcases lt_or_eq_of_le (hcase β hβmem) with h | h
      · exact h
      · exact absurd (by rw [← h]; exact hβmem) hno
    have hγlt : γ < θ := by
      rcases lt_or_eq_of_le (hcase γ hγmem) with h | h
      · exact h
      · exact absurd (by rw [← h]; exact hγmem) hno
    have hxub : θ < 180 - β := by linarith
    have hncast : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
      have h5 : (n - 2) + 2 = n := by omega
      have h7 : (((n - 2) + 2 : ℕ) : ℝ) = ((n : ℕ) : ℝ) := by rw [h5]
      push_cast at h7
      linarith
    refine ⟨{β, θ, 180 - β - θ}, {γ, 180 - θ, θ - γ}, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨α, β, γ, θ, hrepr, hγlt, hxub, rfl, rfl⟩
    · exact isTriangle_triple hβ hθ0 (by linarith) (by ring)
    · exact isTriangle_triple hγ (by linarith) (by linarith) (by ring)
    · refine ⟨0, ?_⟩
      have hval : (((0 : ℕ) : ℝ) + 1) * θ = θ := by norm_num
      rw [hval]
      exact mem_triple.mpr (Or.inr (Or.inl rfl))
    · refine ⟨n - 2, ?_⟩
      have hval : (((n - 2 : ℕ) : ℝ) + 1) * θ = 180 - θ := by
        rw [hncast]
        have hring : ((n : ℝ) - 2 + 1) * θ = (n : ℝ) * θ - θ := by ring
        rw [hring, hnθ]
      rw [hval]
      exact mem_triple.mpr (Or.inr (Or.inl rfl))

lemma mulanCanGuarantee_of_div {n : ℕ} (hn : 2 ≤ n) {θ : ℝ} (hθdef : θ = 180 / n) :
    MulanCanGuarantee θ := by
  intro s hs
  by_cases h : θ ∈ s
  · exact MulanWins.win h
  · obtain ⟨L, R, hcut, hL, hR, ⟨i, hi⟩, ⟨j, hj⟩⟩ := exists_opening_cut hn hθdef hs h
    exact MulanWins.move hcut
      (mulanWins_of_succ_mul (theta_pos hn hθdef) i L hL hi)
      (mulanWins_of_succ_mul (theta_pos hn hθdef) j R hR hj)

/- ===================================================================
   SECTION 4 — Forward direction (⇒): the invariant   (see §3, §5.3)
   =================================================================== -/

/-- `s` is a triangle none of whose angles is an integer multiple of `θ`. -/
def Good (θ : ℝ) (s : Multiset ℝ) : Prop :=
  IsTriangle s ∧ ∀ a ∈ s, ∀ k : ℤ, a ≠ (k : ℝ) * θ

/-- **KEY** — one child of every cut is always `Good`. -/
lemma good_of_cut {θ : ℝ} (h180 : ∀ k : ℤ, (180 : ℝ) ≠ (k : ℝ) * θ)
    {s L R : Multiset ℝ} (hg : Good θ s) (hcut : IsCut s L R) :
    Good θ L ∨ Good θ R := by
  obtain ⟨hs, hnd⟩ := hg
  obtain ⟨α, β, γ, x, hseq, hγx, hxlt, hLeq, hReq⟩ := hcut
  subst hseq; subst hLeq; subst hReq
  /- positivity and the angle sum of `s` -/
  have hα0 : 0 < α := hs.2.1 α (mem_triple.mpr (Or.inl rfl))
  have hβ0 : 0 < β := hs.2.1 β (mem_triple.mpr (Or.inr (Or.inl rfl)))
  have hγ0 : 0 < γ := hs.2.1 γ (mem_triple.mpr (Or.inr (Or.inr rfl)))
  have hsum : α + β + γ = 180 := by
    have h := hs.2.2; rwa [sum_triple] at h
  /- none of α, β, γ lies in θℤ -/
  have hα : ∀ k : ℤ, α ≠ (k : ℝ) * θ := hnd α (mem_triple.mpr (Or.inl rfl))
  have hβ : ∀ k : ℤ, β ≠ (k : ℝ) * θ := hnd β (mem_triple.mpr (Or.inr (Or.inl rfl)))
  have hγ : ∀ k : ℤ, γ ≠ (k : ℝ) * θ := hnd γ (mem_triple.mpr (Or.inr (Or.inr rfl)))
  /- both children are genuine triangles -/
  have hLtri : IsTriangle ({β, x, 180 - β - x} : Multiset ℝ) :=
    isTriangle_triple hβ0 (by linarith) (by linarith) (by ring)
  have hRtri : IsTriangle ({γ, 180 - x, x - γ} : Multiset ℝ) :=
    isTriangle_triple hγ0 (by linarith) (by linarith) (by ring)
  by_cases hxD : ∃ k : ℤ, x = (k : ℝ) * θ
  · /- sub-case x ∈ θℤ : identities (A) and (B) clean up R -/
    right
    obtain ⟨k, hk⟩ := hxD
    refine ⟨hRtri, ?_⟩
    intro a ha m
    rcases mem_triple.mp ha with rfl | rfl | rfl
    · exact hγ m
    · intro hcon
      exact h180 (m + k) (by push_cast; linear_combination hcon + hk)
    · intro hcon
      exact hγ (k - m) (by push_cast; linear_combination hk - hcon)
  · by_cases hyD : ∃ k : ℤ, 180 - β - x = (k : ℝ) * θ
    · /- sub-case 180-β-x ∈ θℤ : identities (C) and (D) clean up R -/
      right
      obtain ⟨k, hk⟩ := hyD
      refine ⟨hRtri, ?_⟩
      intro a ha m
      rcases mem_triple.mp ha with rfl | rfl | rfl
      · exact hγ m
      · intro hcon
        exact hβ (m - k) (by push_cast; linear_combination hcon - hk)
      · intro hcon
        exact hα (m + k) (by push_cast; linear_combination hcon + hk + hsum)
    · /- otherwise L itself is clean -/
      left
      refine ⟨hLtri, ?_⟩
      intro a ha m
      rcases mem_triple.mp ha with rfl | rfl | rfl
      · exact hβ m
      · exact fun hcon => hxD ⟨m, hcon⟩
      · exact fun hcon => hyD ⟨m, hcon⟩

lemma not_good_of_mulanWins {θ : ℝ} (h180 : ∀ k : ℤ, (180 : ℝ) ≠ (k : ℝ) * θ)
    {s : Multiset ℝ} (hw : MulanWins θ s) : ¬ Good θ s := by
  induction hw with
  | win h =>
    intro hg
    exact hg.2 θ h 1 (by push_cast; ring)
  | move hcut hL hR ihL ihR =>
    intro hg
    rcases good_of_cut h180 hg hcut with h | h
    · exact ihL h
    · exact ihR h

lemma good_equilateral {θ : ℝ} (h180 : ∀ k : ℤ, (180 : ℝ) ≠ (k : ℝ) * θ) :
    Good θ ({60, 60, 60} : Multiset ℝ) := by
  refine ⟨isTriangle_triple (by norm_num) (by norm_num) (by norm_num) (by norm_num), ?_⟩
  intro a ha k
  rcases mem_triple.mp ha with rfl | rfl | rfl <;>
    exact fun hcon => h180 (3 * k) (by push_cast; linear_combination 3 * hcon)

lemma exists_div_of_canGuarantee {θ : ℝ} (hθ0 : 0 < θ) (hθ180 : θ < 180)
    (h : MulanCanGuarantee θ) : ∃ n : ℕ, 2 ≤ n ∧ θ = 180 / n := by
  rw [div_iff_intMul hθ0 hθ180]
  by_contra hc
  push_neg at hc
  have htri : IsTriangle ({60, 60, 60} : Multiset ℝ) := by
    refine isTriangle_triple ?_ ?_ ?_ ?_ <;> norm_num
  exact not_good_of_mulanWins hc (h _ htri) (good_equilateral hc)

/- ===================================================================
   SECTION 5 — Assembly
   =================================================================== -/

/-- **Main theorem.** For `0 < θ < 180`, Mulan can guarantee her victory in finitely
many steps, no matter how Shan-Yu plays, if and only if `θ = 180 / n` for some
integer `n ≥ 2`. -/
theorem main_theorem (θ : ℝ) (hθ0 : 0 < θ) (hθ180 : θ < 180) :
    MulanCanGuarantee θ ↔ ∃ n : ℕ, 2 ≤ n ∧ θ = 180 / n := by
  constructor
  · exact exists_div_of_canGuarantee hθ0 hθ180
  · rintro ⟨n, hn, hθ⟩
    exact mulanCanGuarantee_of_div hn hθ

end TriangleGame
