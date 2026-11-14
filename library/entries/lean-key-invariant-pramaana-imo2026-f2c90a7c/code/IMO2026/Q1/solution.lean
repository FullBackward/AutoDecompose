import Mathlib
import Mathlib.Tactic

open scoped Classical

/-- A blackboard is a multiset of natural numbers (entries, not necessarily distinct). -/
abbrev Board := Multiset ℕ

/-- One legal move: pick two entries `m > 1` and `n > 1` occupying two different
    places, and replace them with `gcd m n` and `lcm m n / gcd m n`. -/
def Move (s t : Board) : Prop :=
  ∃ m n, 1 < m ∧ 1 < n ∧ m ∈ s ∧ n ∈ s.erase m ∧
    t = Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ (s.erase m).erase n

/-- Number of entries on the board that are greater than 1. -/
def bigCount (s : Board) : ℕ := Multiset.card (s.filter (fun x => 1 < x))

/-- A board is terminal when no further move is possible. -/
def IsTerminal (s : Board) : Prop := ∀ t, ¬ Move s t

/-- The multiset of entries greater than 1 (its "> 1 part"). -/
def bigPart (s : Board) : Board := s.filter (fun x => 1 < x)

abbrev AnswerType := Bool

/-- The initial board has exactly 2026 entries. -/
def Fact_card (s₀ : Board) : Prop := Multiset.card s₀ = 2026

/-- Every entry of the initial board is greater than 1. -/
def Fact_all_gt1 (s₀ : Board) : Prop := ∀ x ∈ s₀, 1 < x

/-- BEGIN ANSWER -/
def answer : AnswerType := true
/-- END ANSWER -/

def Pos (s : Board) : Prop := ∀ x ∈ s, 0 < x

lemma move_decomp {s t : Board} (h : Move s t) :
    ∃ m n r, 1 < m ∧ 1 < n ∧ s = m ::ₘ n ::ₘ r ∧
      t = Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ r := by
  obtain ⟨m, n, hm, hn, hms, hns, ht⟩ := h
  refine ⟨m, n, (s.erase m).erase n, hm, hn, ?_, ht⟩
  rw [Multiset.cons_erase hns, Multiset.cons_erase hms]

lemma bigCount_cons_big {x : ℕ} (hx : 1 < x) (s : Board) :
    bigCount (x ::ₘ s) = bigCount s + 1 := by
  simp [bigCount, Multiset.filter_cons_of_pos, hx]

lemma bigCount_cons_small {x : ℕ} (hx : ¬ 1 < x) (s : Board) :
    bigCount (x ::ₘ s) = bigCount s := by
  simp [bigCount, Multiset.filter_cons_of_neg, hx]

lemma bigCount_cons_le (x : ℕ) (s : Board) :
    bigCount (x ::ₘ s) ≤ bigCount s + 1 := by
  by_cases hx : 1 < x
  · rw [bigCount_cons_big hx]
  · rw [bigCount_cons_small hx]; omega

lemma exists_move_of_two_le {s : Board} (h : 2 ≤ bigCount s) : ∃ t, Move s t := by
  have hcard : 2 ≤ Multiset.card (s.filter (fun x => 1 < x)) := h
  have hne : s.filter (fun x => 1 < x) ≠ 0 := by
    intro h0; rw [h0] at hcard; simp at hcard
  obtain ⟨m, hm⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨u, hu⟩ := Multiset.exists_cons_of_mem hm
  have hucard : 0 < Multiset.card u := by
    rw [hu] at hcard; simp at hcard; omega
  obtain ⟨n, hn⟩ := Multiset.card_pos_iff_exists_mem.mp hucard
  have hnf : n ∈ s.filter (fun x => 1 < x) := by
    rw [hu]; exact Multiset.mem_cons_of_mem hn
  have hm1 : 1 < m := (Multiset.mem_filter.mp hm).2
  have hn1 : 1 < n := (Multiset.mem_filter.mp hnf).2
  have hms : m ∈ s := (Multiset.mem_filter.mp hm).1
  have hns : n ∈ s.erase m := by
    have h2 : (s.filter (fun x => 1 < x)).erase m ≤ s.erase m :=
      Multiset.erase_le_erase m (Multiset.filter_le _ s)
    rw [hu, Multiset.erase_cons_head] at h2
    exact Multiset.mem_of_le h2 hn
  exact ⟨_, m, n, hm1, hn1, hms, hns, rfl⟩

lemma isTerminal_iff {s : Board} : IsTerminal s ↔ bigCount s ≤ 1 := by
  constructor
  · intro hT
    by_contra hc
    push Not at hc
    obtain ⟨t, ht⟩ := exists_move_of_two_le (s := s) (by omega)
    exact hT t ht
  · intro h t ht
    obtain ⟨m, n, r, hm, hn, hs, -⟩ := move_decomp ht
    rw [hs, bigCount_cons_big hm, bigCount_cons_big hn] at h
    omega

lemma pos_of_move {s t : Board} (hp : Pos s) (h : Move s t) : Pos t := by
  obtain ⟨m, n, r, hm, hn, hs, ht⟩ := move_decomp h
  have hg : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n (by omega)
  have hl : 0 < Nat.lcm m n := Nat.lcm_pos (by omega) (by omega)
  have hgl : Nat.gcd m n ∣ Nat.lcm m n :=
    dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
  have hd : 0 < Nat.lcm m n / Nat.gcd m n := Nat.div_pos (Nat.le_of_dvd hl hgl) hg
  intro x hx
  rw [ht] at hx
  rcases Multiset.mem_cons.mp hx with rfl | hx
  · exact hg
  rcases Multiset.mem_cons.mp hx with rfl | hx
  · exact hd
  · exact hp x (by rw [hs]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hx))

lemma one_le_bigCount_of_move {s t : Board} (h : Move s t) : 1 ≤ bigCount t := by
  obtain ⟨m, n, r, hm, hn, hs, ht⟩ := move_decomp h
  by_cases hgb : 1 < Nat.gcd m n
  · rw [ht, bigCount_cons_big hgb]; omega
  · have hg : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n (by omega)
    have hg1 : Nat.gcd m n = 1 := by omega
    have hl : 0 < Nat.lcm m n := Nat.lcm_pos (by omega) (by omega)
    have hd : 1 < Nat.lcm m n / Nat.gcd m n := by
      rw [hg1, Nat.div_one]
      exact lt_of_lt_of_le hm (Nat.le_of_dvd hl (Nat.dvd_lcm_left m n))
    rw [ht, bigCount_cons_small hgb, bigCount_cons_big hd]
    omega

lemma prod_pos_of_pos {r : Board} (h : ∀ x ∈ r, 0 < x) : 0 < r.prod :=
  Multiset.prod_pos h

def mu (s : Board) : ℕ := 2 * s.prod + bigCount s

lemma mu_lt_of_move {s t : Board} (hp : Pos s) (h : Move s t) : mu t < mu s := by
  obtain ⟨m, n, r, hm, hn, hs, ht⟩ := move_decomp h
  set g := Nat.gcd m n with hgdef
  set d := Nat.lcm m n / Nat.gcd m n with hddef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left n (by omega)
  have hl0 : 0 < Nat.lcm m n := Nat.lcm_pos (by omega) (by omega)
  have hgl : g ∣ Nat.lcm m n :=
    dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
  have hgd : g * d = Nat.lcm m n := Nat.mul_div_cancel' hgl
  have hglm : g * Nat.lcm m n = m * n := Nat.gcd_mul_lcm m n
  have hrpos : 0 < r.prod := by
    apply prod_pos_of_pos
    intro x hx
    exact hp x (by rw [hs]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hx))
  have hprods : s.prod = m * n * r.prod := by
    rw [hs, Multiset.prod_cons, Multiset.prod_cons, ← mul_assoc]
  have hprodt : t.prod = Nat.lcm m n * r.prod := by
    rw [ht, Multiset.prod_cons, Multiset.prod_cons, ← mul_assoc, hgd]
  have hbcs : bigCount s = bigCount r + 2 := by
    rw [hs, bigCount_cons_big hm, bigCount_cons_big hn]
  by_cases hg1 : g = 1
  · -- coprime case: product unchanged, bigCount drops by one
    have hlmn : Nat.lcm m n = m * n := by
      rw [hg1, one_mul] at hglm; exact hglm
    have hpp : t.prod = s.prod := by rw [hprodt, hprods, hlmn]
    have hd1 : 1 < d := by
      have : d = Nat.lcm m n := by rw [hddef, ← hgdef, hg1, Nat.div_one]
      rw [this, hlmn]
      calc 1 < m := hm
        _ ≤ m * n := Nat.le_mul_of_pos_right m (by omega)
    have hbct : bigCount t = bigCount r + 1 := by
      rw [ht, hg1, bigCount_cons_small (by omega), bigCount_cons_big hd1]
    unfold mu
    omega
  · -- gcd > 1: product strictly decreases
    have hl_lt : Nat.lcm m n < m * n := by
      have h2 : 2 ≤ g := by omega
      calc Nat.lcm m n < 2 * Nat.lcm m n := by omega
        _ ≤ g * Nat.lcm m n := Nat.mul_le_mul_right _ h2
        _ = m * n := hglm
    have hpt_lt : t.prod < s.prod := by
      rw [hprodt, hprods]
      exact (Nat.mul_lt_mul_right hrpos).mpr hl_lt
    have hbct_le : bigCount t ≤ bigCount r + 2 := by
      rw [ht]
      calc bigCount (g ::ₘ d ::ₘ r) ≤ bigCount (d ::ₘ r) + 1 := bigCount_cons_le _ _
        _ ≤ bigCount r + 2 := by have := bigCount_cons_le d r; omega
    unfold mu
    omega

def pinv (p : ℕ) (s : Board) : ℕ := (s.map (fun x => x.factorization p)).gcd

lemma gcd_coe (a b : ℕ) : GCDMonoid.gcd a b = Nat.gcd a b := rfl

lemma gcd_min_sub (a b R : ℕ) :
    Nat.gcd (a ⊓ b) (Nat.gcd ((a ⊔ b) - (a ⊓ b)) R) = Nat.gcd a (Nat.gcd b R) := by
  rw [← Nat.gcd_assoc, ← Nat.gcd_assoc]
  congr 1
  rcases le_total a b with hab | hab
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [inf_of_le_left hab, sup_of_le_right hab, Nat.add_sub_cancel_left,
      Nat.gcd_self_add_right]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [inf_of_le_right hab, sup_of_le_left hab, Nat.add_sub_cancel_left,
      Nat.gcd_comm (b + k) b, Nat.gcd_self_add_right]

lemma pinv_move {p : ℕ} {s t : Board} (h : Move s t) : pinv p t = pinv p s := by
  obtain ⟨m, n, r, hm, hn, hs, ht⟩ := move_decomp h
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  have hg : (Nat.gcd m n).factorization p = m.factorization p ⊓ n.factorization p := by
    rw [Nat.factorization_gcd hm0 hn0, Finsupp.inf_apply]
  have hl : (Nat.lcm m n).factorization p = m.factorization p ⊔ n.factorization p := by
    rw [Nat.factorization_lcm hm0 hn0, Finsupp.sup_apply]
  have hgl : Nat.gcd m n ∣ Nat.lcm m n :=
    dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
  have hd : (Nat.lcm m n / Nat.gcd m n).factorization p
      = (m.factorization p ⊔ n.factorization p) - (m.factorization p ⊓ n.factorization p) := by
    rw [Nat.factorization_div hgl, Finsupp.tsub_apply, hg, hl]
  rw [hs, ht]
  unfold pinv
  simp only [Multiset.map_cons, Multiset.gcd_cons, gcd_coe]
  rw [hg, hd]
  exact gcd_min_sub _ _ _

lemma pos_rtg {s t : Board} (hp : Pos s) (h : Relation.ReflTransGen Move s t) : Pos t := by
  induction h with
  | refl => exact hp
  | tail _ hmv ih => exact pos_of_move ih hmv

lemma pinv_rtg {p : ℕ} {s t : Board}
    (h : Relation.ReflTransGen Move s t) : pinv p t = pinv p s := by
  induction h with
  | refl => rfl
  | tail _ hmv ih => rw [pinv_move hmv, ih]

lemma exists_terminal_aux :
    ∀ N s, mu s ≤ N → Pos s → ∃ t, Relation.ReflTransGen Move s t ∧ IsTerminal t := by
  intro N
  induction N with
  | zero =>
    intro s hs hp
    by_cases hT : IsTerminal s
    · exact ⟨s, Relation.ReflTransGen.refl, hT⟩
    · exfalso
      simp only [IsTerminal, not_forall, not_not] at hT
      obtain ⟨t, ht⟩ := hT
      have := mu_lt_of_move hp ht
      omega
  | succ N ih =>
    intro s hs hp
    by_cases hT : IsTerminal s
    · exact ⟨s, Relation.ReflTransGen.refl, hT⟩
    · simp only [IsTerminal, not_forall, not_not] at hT
      obtain ⟨t, ht⟩ := hT
      have hlt := mu_lt_of_move hp ht
      obtain ⟨u, hu, huT⟩ := ih t (by omega) (pos_of_move hp ht)
      exact ⟨u, Relation.ReflTransGen.head ht hu, huT⟩

lemma exists_terminal {s : Board} (hp : Pos s) :
    ∃ t, Relation.ReflTransGen Move s t ∧ IsTerminal t :=
  exists_terminal_aux (mu s) s le_rfl hp

theorem answer_correctness
    (s₀ : Board)
    (h_card : Fact_card s₀)
    (h_all_gt1 : Fact_all_gt1 s₀)
    : answer = true ↔
        ( (¬ ∃ f : ℕ → Board, f 0 = s₀ ∧ ∀ k, Move (f k) (f (k + 1)))
          ∧ (∃ t, Relation.ReflTransGen Move s₀ t ∧ IsTerminal t)
          ∧ (∀ t, Relation.ReflTransGen Move s₀ t → IsTerminal t → bigCount t = 1)
          ∧ (∀ t₁ t₂, Relation.ReflTransGen Move s₀ t₁ → IsTerminal t₁ →
               Relation.ReflTransGen Move s₀ t₂ → IsTerminal t₂ →
               bigPart t₁ = bigPart t₂) ) := by
  have h_card' : Multiset.card s₀ = 2026 := h_card
  have h_gt1 : ∀ x ∈ s₀, 1 < x := h_all_gt1
  have hpos : Pos s₀ := fun x hx => lt_trans one_pos (h_gt1 x hx)
  have hb0 : bigCount s₀ = 2026 := by
    have h1 : Multiset.filter (fun x => 1 < x) s₀ = s₀ := Multiset.filter_eq_self.mpr h_gt1
    simp only [bigCount, h1]
    exact h_card'
  -- (a-count)
  have hbig1 : ∀ t, Relation.ReflTransGen Move s₀ t → IsTerminal t → bigCount t = 1 := by
    intro t hrt hT
    have hle : bigCount t ≤ 1 := isTerminal_iff.mp hT
    have hge : 1 ≤ bigCount t := by
      rcases Relation.ReflTransGen.cases_tail hrt with heq | ⟨u, hu, hmv⟩
      · rw [heq, hb0]; omega
      · exact one_le_bigCount_of_move hmv
    omega
  -- terminal boards are singletons with determined factorization
  have key : ∀ t, Relation.ReflTransGen Move s₀ t → IsTerminal t →
      ∃ M, bigPart t = {M} ∧ 1 < M ∧ ∀ p, M.factorization p = pinv p s₀ := by
    intro t hrt hT
    have hbc : Multiset.card (t.filter (fun x => 1 < x)) = 1 := hbig1 t hrt hT
    obtain ⟨M, hM⟩ := Multiset.card_eq_one.mp hbc
    have hMmem : M ∈ t.filter (fun x => 1 < x) := by
      rw [hM]; exact Multiset.mem_singleton_self M
    have hM1 : 1 < M := (Multiset.mem_filter.mp hMmem).2
    refine ⟨M, hM, hM1, ?_⟩
    intro p
    have hsplit : t.filter (fun x => 1 < x) + t.filter (fun x => ¬ 1 < x) = t :=
      Multiset.filter_add_not _ t
    have ht' : t = M ::ₘ t.filter (fun x => ¬ 1 < x) := by
      conv_lhs => rw [← hsplit, hM]
      rw [Multiset.singleton_add]
    have hz : ((t.filter (fun x => ¬ 1 < x)).map (fun x => x.factorization p)).gcd = 0 := by
      rw [Multiset.gcd_eq_zero_iff]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
      have hx1 : ¬ 1 < x := (Multiset.mem_filter.mp hx).2
      have hxt : x ∈ t := (Multiset.mem_filter.mp hx).1
      have hxpos : 0 < x := pos_rtg hpos hrt x hxt
      have : x = 1 := by omega
      rw [this]; simp
    have hit : pinv p t = M.factorization p := by
      unfold pinv
      rw [ht']
      simp only [Multiset.map_cons, Multiset.gcd_cons, gcd_coe]
      rw [hz, Nat.gcd_zero_right]
    rw [← hit]
    exact pinv_rtg hrt
  constructor
  · intro _
    refine ⟨?_, exists_terminal hpos, hbig1, ?_⟩
    · -- termination: no infinite play
      rintro ⟨f, hf0, hf⟩
      have hposk : ∀ k, Pos (f k) := by
        intro k
        induction k with
        | zero => rw [hf0]; exact hpos
        | succ k ih => exact pos_of_move ih (hf k)
      have hdec : ∀ k, mu (f k) + k ≤ mu (f 0) := by
        intro k
        induction k with
        | zero => omega
        | succ k ih =>
          have := mu_lt_of_move (hposk k) (hf k)
          omega
      have := hdec (mu (f 0) + 1)
      omega
    · -- uniqueness of the surviving big part
      intro t₁ t₂ hr1 hT1 hr2 hT2
      obtain ⟨M₁, hP1, hM11, hf1⟩ := key t₁ hr1 hT1
      obtain ⟨M₂, hP2, hM21, hf2⟩ := key t₂ hr2 hT2
      have hMM : M₁ = M₂ := by
        have hfeq : M₁.factorization = M₂.factorization :=
          Finsupp.ext fun p => by rw [hf1 p, hf2 p]
        have h10 : (M₁ : ℕ) ≠ 0 := by omega
        have h20 : (M₂ : ℕ) ≠ 0 := by omega
        exact Nat.factorization_inj h10 h20 hfeq
      rw [hP1, hP2, hMM]
  · intro _
    rfl
