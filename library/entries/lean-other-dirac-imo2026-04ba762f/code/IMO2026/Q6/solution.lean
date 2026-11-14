import Mathlib
set_option backward.isDefEq.respectTransparency false

/-- The predicate stating that `a : ℕ → ℕ` (0-indexed) is a sequence satisfying Definition 1:
each term exceeds `1`, and each subsequent term is the smallest integer strictly larger than the
previous one that shares a common factor with every earlier term. -/
def IsValidSeq (a : ℕ → ℕ) : Prop :=
  (∀ n, 1 < a n) ∧
  (∀ n, a n < a (n + 1) ∧
        (∀ i ≤ n, 1 < Nat.gcd (a (n + 1)) (a i)) ∧
        (∀ b, a n < b → b < a (n + 1) → ∃ i ≤ n, Nat.gcd b (a i) = 1))

/- `b` is admissible: it shares a factor with every term of the sequence. -/
def Adm (a : ℕ → ℕ) (b : ℕ) : Prop := ∀ i, 1 < Nat.gcd b (a i)

/- prime-set language for the crux -/
abbrev PS (a : ℕ → ℕ) (n : ℕ) : Finset ℕ := (a n).primeFactors

/- NOTE: the root name `Trans` is already taken by core Lean's `Trans`
   typeclass, so the definition must live in a namespace.  `export` re-publishes it
   under the bare name `Trans`, which then elaborates unambiguously in every use site
   below (the core `Trans` class never fits a `Prop`-valued application to two
   arguments of these types).  All statements below read exactly as in the contract. -/
namespace PSDict
def Trans (a : ℕ → ℕ) (X : Finset ℕ) : Prop := ∀ i, ¬ Disjoint X (PS a i)
end PSDict
export PSDict (Trans)

def Realized (a : ℕ → ℕ) (X : Finset ℕ) : Prop := ∃ n, PS a n = X

def IsMinMem (a : ℕ → ℕ) (S : Finset ℕ) : Prop :=
  Realized a S ∧ ∀ T, Realized a T → T ⊆ S → T = S

theorem seq_lt_succ (a : ℕ → ℕ) (ha : IsValidSeq a) (n : ℕ) : a n < a (n + 1) := by
  exact (ha.2 n).1

theorem seq_strictMono (a : ℕ → ℕ) (ha : IsValidSeq a) : StrictMono a := by
  exact strictMono_nat_of_lt_succ (seq_lt_succ a ha)

theorem seq_add_le (a : ℕ → ℕ) (ha : IsValidSeq a) (n : ℕ) : a 0 + n ≤ a n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hk : a k < a (k + 1) := seq_lt_succ a ha k
    omega

theorem seq_gcd (a : ℕ → ℕ) (ha : IsValidSeq a) (i j : ℕ) : 1 < Nat.gcd (a i) (a j) := by
  /- Handle the strictly-increasing case once; the rest is `Nat.gcd_comm`. -/
  have key : ∀ p q : ℕ, p < q → 1 < Nat.gcd (a p) (a q) := by
    intro p q hpq
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    have h := (ha.2 k).2.1 p (by omega)
    rwa [Nat.gcd_comm] at h
  rcases lt_trichotomy i j with h | h | h
  · exact key i j h
  · subst h
    rw [Nat.gcd_self]
    exact ha.1 i
  · rw [Nat.gcd_comm]
    exact key j i h

theorem adm_seq (a : ℕ → ℕ) (ha : IsValidSeq a) (n : ℕ) : Adm a (a n) := by
  intro i
  exact seq_gcd a ha n i

theorem succ_le_of_adm (a : ℕ → ℕ) (ha : IsValidSeq a) (n b : ℕ) (hb : Adm a b)
    (hlt : a n < b) : a (n + 1) ≤ b := by
  by_contra hcon
  have hcon' : b < a (n + 1) := Nat.lt_of_not_le hcon
  /- Minimality clause supplies an index coprime to `b`, contradicting `Adm`. -/
  obtain ⟨i, _, hgcd⟩ := (ha.2 n).2.2 b hlt hcon'
  have hbi := hb i
  omega

/- item 2 -/
theorem a_ne_zero (a : ℕ → ℕ) (ha : IsValidSeq a) (n : ℕ) : a n ≠ 0 := by
  have := ha.1 n
  omega

/- item 1: the gcd ↔ prime-set dictionary -/
theorem gcd_pos_iff (x y : ℕ) (hx : x ≠ 0) (hy : y ≠ 0) :
    1 < Nat.gcd x y ↔ ¬ Disjoint x.primeFactors y.primeFactors := by
  rw [Nat.disjoint_primeFactors hx hy]
  have hpos : Nat.gcd x y ≠ 0 := fun h => hx (Nat.eq_zero_of_gcd_eq_zero_left h)
  have hcop : Nat.Coprime x y ↔ Nat.gcd x y = 1 := Iff.rfl
  rw [hcop]
  omega

/- item 3 -/
theorem adm_iff_trans (a : ℕ → ℕ) (ha : IsValidSeq a) (b : ℕ) (hb : b ≠ 0) :
    Adm a b ↔ Trans a b.primeFactors := by
  constructor
  · intro h i
    exact (gcd_pos_iff b (a i) hb (a_ne_zero a ha i)).mp (h i)
  · intro h i
    exact (gcd_pos_iff b (a i) hb (a_ne_zero a ha i)).mpr (h i)

/- item 4 -/
theorem primeFactors_prod_pow (X : Finset ℕ) (hX : ∀ p ∈ X, Nat.Prime p) (t : ℕ) (ht : t ≠ 0) :
    ((∏ p ∈ X, p) ^ t).primeFactors = X := by
  rw [Nat.primeFactors_pow _ ht, Nat.primeFactors_prod hX]

/- item 5 -/
theorem prod_subset_le (a : ℕ → ℕ) (ha : IsValidSeq a) (i : ℕ) (S : Finset ℕ)
    (hS : S ⊆ PS a i) : (∏ p ∈ S, p) ≤ a i := by
  have h1 : (∏ p ∈ S, p) ∣ ∏ p ∈ PS a i, p :=
    Finset.prod_dvd_prod_of_subset S (PS a i) (fun p => p) hS
  have h2 : (∏ p ∈ PS a i, p) ∣ a i := Nat.prod_primeFactors_dvd (a i)
  have hpos : 0 < a i := by have := ha.1 i; omega
  exact Nat.le_of_dvd hpos (h1.trans h2)

/- every realized prime set is a transversal (from `seq_gcd`) -/
theorem realized_trans (a : ℕ → ℕ) (ha : IsValidSeq a) (X : Finset ℕ) (hX : Realized a X) :
    Trans a X := by
  obtain ⟨m, hm⟩ := hX
  intro i
  rw [← hm]
  exact (gcd_pos_iff (a m) (a i) (a_ne_zero a ha m) (a_ne_zero a ha i)).mp (seq_gcd a ha m i)

/- item 7 -/
theorem minMem_prime (a : ℕ → ℕ) (ha : IsValidSeq a) (S : Finset ℕ) (hS : IsMinMem a S) :
    (∀ p ∈ S, Nat.Prime p) ∧ S.Nonempty := by
  obtain ⟨m, hm⟩ := hS.1
  subst hm
  refine ⟨fun p hp => Nat.prime_of_mem_primeFactors hp, ?_⟩
  exact Nat.nonempty_primeFactors.mpr (ha.1 m)

/- item 6 -/
theorem exists_minMem_subset (a : ℕ → ℕ) (ha : IsValidSeq a) (n : ℕ) :
    ∃ S, IsMinMem a S ∧ S ⊆ PS a n := by
  classical
  /- minimum-cardinality realized subset of `PS a n` -/
  set C : Finset (Finset ℕ) := (PS a n).powerset.filter (Realized a) with hCdef
  have hmem : PS a n ∈ C := by
    rw [hCdef, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl _, ⟨n, rfl⟩⟩
  obtain ⟨S, hSC, hSmin⟩ := Finset.exists_min_image C Finset.card ⟨_, hmem⟩
  have hS' : S ⊆ PS a n ∧ Realized a S := by
    rw [hCdef, Finset.mem_filter, Finset.mem_powerset] at hSC
    exact hSC
  refine ⟨S, ⟨hS'.2, ?_⟩, hS'.1⟩
  intro T hT hTS
  have hTC : T ∈ C := by
    rw [hCdef, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hTS.trans hS'.1, hT⟩
  exact Finset.eq_of_subset_of_card_le hTS (hSmin T hTC)

/- Every admissible number that is at least `a 0` actually occurs in the sequence. -/
theorem adm_enum (a : ℕ → ℕ) (ha : IsValidSeq a) (b : ℕ) (hb : Adm a b) (h0 : a 0 ≤ b) :
    ∃ n, a n = b := by
  /- `a` is strictly increasing, hence `a 0 + n ≤ a n`. -/
  have hlt : ∀ n, a n < a (n + 1) := fun n => (ha.2 n).1
  have hgrow : ∀ n, a 0 + n ≤ a n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => have := hlt k; omega
  /- any index with `a n ≤ b` is at most `b`. -/
  have hbound : ∀ n, a n ≤ b → n ≤ b := by
    intro n hn
    have h1 := hgrow n
    omega
  /- `N` is the largest index with `a N ≤ b`. -/
  set N := Nat.findGreatest (fun n => a n ≤ b) b with hNdef
  have hNle : a N ≤ b := Nat.findGreatest_spec (P := fun n => a n ≤ b) (Nat.zero_le b) h0
  have hNsucc : b < a (N + 1) := by
    by_contra hcon
    rw [Nat.not_lt] at hcon
    have h1 : N + 1 ≤ b := hbound (N + 1) hcon
    have h2 : ¬ ((fun n => a n ≤ b) (N + 1)) :=
      Nat.findGreatest_is_greatest (P := fun n => a n ≤ b) (Nat.lt_succ_self N) h1
    exact h2 hcon
  refine ⟨N, ?_⟩
  rcases lt_or_eq_of_le hNle with hlt' | heq
  · /- `a N < b < a (N+1)` contradicts the minimality clause. -/
    obtain ⟨i, hiN, hgcd⟩ := (ha.2 N).2.2 b hlt' hNsucc
    have := hb i
    omega
  · exact heq

/- Step 2: a non-admissible number above `a 0` is killed by a strictly SMALLER term. -/
theorem killed_early (a : ℕ → ℕ) (ha : IsValidSeq a) (b : ℕ)
    (hb : a 0 < b) (hnadm : ¬ Adm a b) :
    ∃ i, a i < b ∧ Nat.gcd b (a i) = 1 := by
  /- Any index with `a n < b` is at most `b`, since `a 0 + n ≤ a n`. -/
  have hbound : ∀ n, a n < b → n ≤ b := by
    intro n hn
    have h1 := seq_add_le a ha n
    omega
  /- `N` is the largest index with `a N < b`. -/
  set N := Nat.findGreatest (fun n => a n < b) b with hNdef
  have hNlt : a N < b := Nat.findGreatest_spec (P := fun n => a n < b) (Nat.zero_le b) hb
  have hNsucc : b ≤ a (N + 1) := by
    by_contra hcon
    have hcon' : a (N + 1) < b := Nat.lt_of_not_le hcon
    have h1 : N + 1 ≤ b := hbound (N + 1) hcon'
    have h2 : ¬ ((fun n => a n < b) (N + 1)) :=
      Nat.findGreatest_is_greatest (P := fun n => a n < b) (Nat.lt_succ_self N) h1
    exact h2 hcon'
  /- `b ≠ a (N+1)` since `a (N+1)` is admissible but `b` is not. -/
  have hne : b ≠ a (N + 1) := by
    intro h
    apply hnadm
    rw [h]
    exact adm_seq a ha (N + 1)
  have hNsucc' : b < a (N + 1) := lt_of_le_of_ne hNsucc hne
  /- The minimality clause applies to `a N < b < a (N+1)`. -/
  obtain ⟨i, hiN, hgcd⟩ := (ha.2 N).2.2 b hNlt hNsucc'
  refine ⟨i, ?_, hgcd⟩
  have hmono : a i ≤ a N := (seq_strictMono a ha).monotone hiN
  omega

/- Step 1: a nonempty transversal is realized, by a term of bounded size. -/
theorem trans_realized (a : ℕ → ℕ) (ha : IsValidSeq a) (X : Finset ℕ)
    (hne : X.Nonempty) (hp : ∀ p ∈ X, Nat.Prime p) (hT : Trans a X) :
    ∃ n, PS a n = X ∧ a n ≤ a 0 * ∏ p ∈ X, p := by
  classical
  set P := ∏ p ∈ X, p with hP
  /- `P ≥ 2` since `X` is nonempty and all its members are primes. -/
  obtain ⟨p0, hp0⟩ := hne
  have hP2 : 2 ≤ P := by
    have h1 : p0 ≤ P := by
      rw [hP]
      exact Finset.single_le_prod' (f := fun p => p) (fun i hi => (hp i hi).pos) hp0
    have h2 := (hp p0 hp0).two_le
    omega
  have hPpos : 0 < P := by omega
  /- `P ^ k > k`, so some power of `P` reaches `a 0`. -/
  have hgrow : ∀ k : ℕ, k < P ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      have h1 : 0 < P ^ n := pow_pos hPpos n
      have h2 : P ^ n * 2 ≤ P ^ n * P := Nat.mul_le_mul_left _ hP2
      have h3 : P ^ (n + 1) = P ^ n * P := pow_succ P n
      omega
  have hex : ∃ t, a 0 ≤ P ^ t := ⟨a 0, le_of_lt (hgrow (a 0))⟩
  set t := Nat.find hex with htdef
  have hts : a 0 ≤ P ^ t := Nat.find_spec hex
  have htne : t ≠ 0 := by
    intro h
    rw [h, pow_zero] at hts
    have := ha.1 0
    omega
  obtain ⟨s, hs⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hmin : ¬ (a 0 ≤ P ^ s) := Nat.find_min hex (by omega)
  have hslt : P ^ s < a 0 := by omega
  /- `b := P ^ t` is admissible with prime support exactly `X`. -/
  have hbne : P ^ t ≠ 0 := pow_ne_zero t (by omega)
  have hpf : (P ^ t).primeFactors = X := primeFactors_prod_pow X hp t htne
  have hadm : Adm a (P ^ t) := by
    rw [adm_iff_trans a ha _ hbne, hpf]
    exact hT
  obtain ⟨n, hn⟩ := adm_enum a ha (P ^ t) hadm hts
  refine ⟨n, ?_, ?_⟩
  · rw [show PS a n = (a n).primeFactors from rfl, hn, hpf]
  · /- minimality of `t` gives `P ^ t = P ^ s * P < a 0 * P`. -/
    have e1 : P ^ t = P ^ s * P := by rw [hs, pow_succ]
    have e2 : (P ^ s + 1) * P = P ^ s * P + P := by ring
    have h3 : (P ^ s + 1) * P ≤ a 0 * P := Nat.mul_le_mul_right P (by omega)
    rw [hn]
    omega

/- Corollary 2′: a non-transversal squarefree number above `a 0` is killed by a
   minimal member with strictly smaller product. -/
theorem cheap_killer (a : ℕ → ℕ) (ha : IsValidSeq a)
    (hkill : ∀ b, a 0 < b → ¬ Adm a b → ∃ i, a i < b ∧ Nat.gcd b (a i) = 1)
    (hminsub : ∀ n, ∃ S, IsMinMem a S ∧ S ⊆ PS a n)
    (X : Finset ℕ) (hp : ∀ p ∈ X, Nat.Prime p) (hnT : ¬ Trans a X)
    (hbig : a 0 < ∏ p ∈ X, p) :
    ∃ S, IsMinMem a S ∧ Disjoint S X ∧ (∏ p ∈ S, p) < ∏ p ∈ X, p := by
  classical
  /- routine facts, kept LOCAL (a sibling publishes them top-level) -/
  have hane : ∀ n, a n ≠ 0 := by
    intro n
    have := ha.1 n
    omega
  have hdict : ∀ x y : ℕ, x ≠ 0 → y ≠ 0 →
      (1 < Nat.gcd x y ↔ ¬ Disjoint x.primeFactors y.primeFactors) := by
    intro x y hx hy
    rw [Nat.disjoint_primeFactors hx hy]
    have hpos : Nat.gcd x y ≠ 0 := fun h => hx (Nat.eq_zero_of_gcd_eq_zero_left h)
    have hcop : Nat.Coprime x y ↔ Nat.gcd x y = 1 := Iff.rfl
    rw [hcop]
    omega
  have hprodle : ∀ (i : ℕ) (U : Finset ℕ), U ⊆ PS a i → (∏ p ∈ U, p) ≤ a i := by
    intro i U hU
    have h1 : (∏ p ∈ U, p) ∣ ∏ p ∈ PS a i, p :=
      Finset.prod_dvd_prod_of_subset U (PS a i) (fun p => p) hU
    have h2 : (∏ p ∈ PS a i, p) ∣ a i := Nat.prod_primeFactors_dvd (a i)
    have hpos : 0 < a i := by
      have := ha.1 i
      omega
    exact Nat.le_of_dvd hpos (h1.trans h2)
  have ha0 : 1 < a 0 := ha.1 0
  /- `b := ∏ X` has prime set exactly `X`, hence is not admissible -/
  have hbpos : 0 < ∏ p ∈ X, p := Nat.lt_of_le_of_lt (Nat.zero_le (a 0)) hbig
  have hbne : (∏ p ∈ X, p) ≠ 0 := hbpos.ne'
  have hpfb : (∏ p ∈ X, p).primeFactors = X := Nat.primeFactors_prod hp
  have hnadm : ¬ Adm a (∏ p ∈ X, p) := by
    intro hAdm
    apply hnT
    intro i
    have h := (hdict (∏ p ∈ X, p) (a i) hbne (hane i)).mp (hAdm i)
    rwa [hpfb] at h
  obtain ⟨i, hilt, hgcd⟩ := hkill (∏ p ∈ X, p) hbig hnadm
  have hdisj : Disjoint X (PS a i) := by
    by_contra hcon
    have h : 1 < Nat.gcd (∏ p ∈ X, p) (a i) :=
      (hdict (∏ p ∈ X, p) (a i) hbne (hane i)).mpr (by rw [hpfb]; exact hcon)
    rw [hgcd] at h
    exact absurd h (lt_irrefl 1)
  obtain ⟨S, hSmin, hSsub⟩ := hminsub i
  refine ⟨S, hSmin, hdisj.symm.mono_left hSsub, ?_⟩
  have h1 : (∏ p ∈ S, p) ≤ a i := hprodle i S hSsub
  omega

/- Step 3 (descent): every prime of a minimal member lies in a CHEAP minimal member. -/
theorem descent (a : ℕ → ℕ) (ha : IsValidSeq a)
    (hkill : ∀ b, a 0 < b → ¬ Adm a b → ∃ i, a i < b ∧ Nat.gcd b (a i) = 1)
    (hminsub : ∀ n, ∃ S, IsMinMem a S ∧ S ⊆ PS a n)
    (hreal : ∀ X : Finset ℕ, X.Nonempty → (∀ p ∈ X, Nat.Prime p) → Trans a X →
      ∃ n, PS a n = X ∧ a n ≤ a 0 * ∏ p ∈ X, p) :
    ∀ S : Finset ℕ, IsMinMem a S → ∀ q ∈ S,
      ∃ T : Finset ℕ, IsMinMem a T ∧ q ∈ T ∧ (∏ p ∈ T, p) ≤ a 0 * q := by
  classical
  have hane : ∀ n, a n ≠ 0 := by
    intro n
    have := ha.1 n
    omega
  have hdict : ∀ x y : ℕ, x ≠ 0 → y ≠ 0 →
      (1 < Nat.gcd x y ↔ ¬ Disjoint x.primeFactors y.primeFactors) := by
    intro x y hx hy
    rw [Nat.disjoint_primeFactors hx hy]
    have hpos : Nat.gcd x y ≠ 0 := fun h => hx (Nat.eq_zero_of_gcd_eq_zero_left h)
    have hcop : Nat.Coprime x y ↔ Nat.gcd x y = 1 := Iff.rfl
    rw [hcop]
    omega
  have hminprime : ∀ U : Finset ℕ, IsMinMem a U → (∀ p ∈ U, Nat.Prime p) ∧ U.Nonempty := by
    intro U hU
    obtain ⟨m, hm⟩ := hU.1
    subst hm
    exact ⟨fun p hp => Nat.prime_of_mem_primeFactors hp,
      Nat.nonempty_primeFactors.mpr (ha.1 m)⟩
  /- two realized prime sets always meet — this is `seq_gcd` + the dictionary -/
  have hmeet : ∀ U V : Finset ℕ, Realized a U → Realized a V → ¬ Disjoint U V := by
    intro U V hU hV
    obtain ⟨m, hm⟩ := hU
    obtain ⟨n, hn⟩ := hV
    subst hm
    subst hn
    exact (hdict (a m) (a n) (hane m) (hane n)).mp (seq_gcd a ha m n)
  have ha0 : 1 < a 0 := ha.1 0
  /- strong induction on the product `∏ S` -/
  have key : ∀ N : ℕ, ∀ S : Finset ℕ, (∏ p ∈ S, p) = N → IsMinMem a S → ∀ q ∈ S,
      ∃ T : Finset ℕ, IsMinMem a T ∧ q ∈ T ∧ (∏ p ∈ T, p) ≤ a 0 * q := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro S hSN hS q hq
      by_cases hle : (∏ p ∈ S, p) ≤ a 0 * q
      · exact ⟨S, hS, hq, hle⟩
      rw [not_le] at hle
      have hqprime : Nat.Prime q := (hminprime S hS).1 q hq
      have hq2 : 2 ≤ q := hqprime.two_le
      have hmul : (∏ p ∈ S.erase q, p) * q = ∏ p ∈ S, p :=
        Finset.prod_erase_mul S (fun p => p) hq
      have hXsub : S.erase q ⊆ S := fun x hx => Finset.mem_of_mem_erase hx
      have hqnX : q ∉ S.erase q := Finset.notMem_erase q S
      have hXprime : ∀ p ∈ S.erase q, Nat.Prime p := fun p hpX =>
        (hminprime S hS).1 p (hXsub hpX)
      /- cancel `q`: `∏ S > a 0 * q` forces `∏ (S.erase q) > a 0` -/
      have hbigX : a 0 < ∏ p ∈ S.erase q, p := by
        by_contra hcon
        rw [not_lt] at hcon
        have h1 : (∏ p ∈ S.erase q, p) * q ≤ a 0 * q := Nat.mul_le_mul hcon (le_refl q)
        rw [hmul] at h1
        exact absurd h1 (not_le.mpr hle)
      /- `S.erase q` is not a transversal: else it would be realized, hence `= S` -/
      have hnT : ¬ Trans a (S.erase q) := by
        intro hT
        have hXne : (S.erase q).Nonempty := by
          rcases Finset.eq_empty_or_nonempty (S.erase q) with h | h
          · rw [h] at hbigX
            simp at hbigX
            omega
          · exact h
        obtain ⟨n, hn, -⟩ := hreal (S.erase q) hXne hXprime hT
        have heq : S.erase q = S := hS.2 (S.erase q) ⟨n, hn⟩ hXsub
        have hqX : q ∈ S.erase q := by
          rw [heq]
          exact hq
        exact hqnX hqX
      obtain ⟨T', hT'min, hT'disj, hT'lt⟩ :=
        cheap_killer a ha hkill hminsub (S.erase q) hXprime hnT hbigX
      /- `T'` meets `S` but avoids `S.erase q`, so it must contain `q` -/
      have hqT' : q ∈ T' := by
        have hmt := hmeet T' S hT'min.1 hS.1
        rw [Finset.not_disjoint_iff] at hmt
        obtain ⟨x, hxT, hxS⟩ := hmt
        by_cases hxq : x = q
        · rwa [hxq] at hxT
        · exfalso
          have hxX : x ∈ S.erase q := Finset.mem_erase.mpr ⟨hxq, hxS⟩
          exact Finset.disjoint_left.mp hT'disj hxT hxX
      have hXle : (∏ p ∈ S.erase q, p) ≤ ∏ p ∈ S, p := by
        rw [← hmul]
        have h2 : (∏ p ∈ S.erase q, p) * 1 ≤ (∏ p ∈ S.erase q, p) * q :=
          Nat.mul_le_mul (le_refl _) (by omega)
        simpa using h2
      have hlt : (∏ p ∈ T', p) < N := by omega
      exact ih _ hlt T' rfl hT'min q hqT'
  intro S hS q hq
  exact key _ S rfl hS q hq

/- Step 4: every prime occurring in a minimal member is below `(a 0)^2`. -/
theorem prime_bound (a : ℕ → ℕ) (ha : IsValidSeq a)
    (hkill : ∀ b, a 0 < b → ¬ Adm a b → ∃ i, a i < b ∧ Nat.gcd b (a i) = 1)
    (hminsub : ∀ n, ∃ S, IsMinMem a S ∧ S ⊆ PS a n)
    (hreal : ∀ X : Finset ℕ, X.Nonempty → (∀ p ∈ X, Nat.Prime p) → Trans a X →
      ∃ n, PS a n = X ∧ a n ≤ a 0 * ∏ p ∈ X, p)
    (S : Finset ℕ) (hS : IsMinMem a S) (q : ℕ) (hq : q ∈ S) :
    q < (a 0) ^ 2 := by
  classical
  have hane : ∀ n, a n ≠ 0 := by
    intro n
    have := ha.1 n
    omega
  have hdict : ∀ x y : ℕ, x ≠ 0 → y ≠ 0 →
      (1 < Nat.gcd x y ↔ ¬ Disjoint x.primeFactors y.primeFactors) := by
    intro x y hx hy
    rw [Nat.disjoint_primeFactors hx hy]
    have hpos : Nat.gcd x y ≠ 0 := fun h => hx (Nat.eq_zero_of_gcd_eq_zero_left h)
    have hcop : Nat.Coprime x y ↔ Nat.gcd x y = 1 := Iff.rfl
    rw [hcop]
    omega
  have hminprime : ∀ U : Finset ℕ, IsMinMem a U → (∀ p ∈ U, Nat.Prime p) ∧ U.Nonempty := by
    intro U hU
    obtain ⟨m, hm⟩ := hU.1
    subst hm
    exact ⟨fun p hp => Nat.prime_of_mem_primeFactors hp,
      Nat.nonempty_primeFactors.mpr (ha.1 m)⟩
  have hmeet : ∀ U V : Finset ℕ, Realized a U → Realized a V → ¬ Disjoint U V := by
    intro U V hU hV
    obtain ⟨m, hm⟩ := hU
    obtain ⟨n, hn⟩ := hV
    subst hm
    subst hn
    exact (hdict (a m) (a n) (hane m) (hane n)).mp (seq_gcd a ha m n)
  have ha0 : 1 < a 0 := ha.1 0
  obtain ⟨T, hTmin, hqT, hTle⟩ := descent a ha hkill hminsub hreal S hS q hq
  have hqprime : Nat.Prime q := (hminprime S hS).1 q hq
  have hq2 : 2 ≤ q := hqprime.two_le
  have hmul : (∏ p ∈ T.erase q, p) * q = ∏ p ∈ T, p :=
    Finset.prod_erase_mul T (fun p => p) hqT
  /- cancel `q` in `∏ T ≤ a 0 * q` -/
  have hRle : (∏ p ∈ T.erase q, p) ≤ a 0 := by
    have h1 : (∏ p ∈ T.erase q, p) * q ≤ a 0 * q := by
      rw [hmul]
      exact hTle
    exact Nat.le_of_mul_le_mul_right h1 (by omega)
  have hRsub : T.erase q ⊆ T := fun x hx => Finset.mem_of_mem_erase hx
  have hRprime : ∀ p ∈ T.erase q, Nat.Prime p := fun p hpR =>
    (hminprime T hTmin).1 p (hRsub hpR)
  have hqnR : q ∉ T.erase q := Finset.notMem_erase q T
  rcases Finset.eq_empty_or_nonempty (T.erase q) with hRempty | hRne
  · /- case `R = ∅`, i.e. `T = {q}`: `T` meets `PS a 0`, so `q ∣ a 0` -/
    have hmt := hmeet T (PS a 0) hTmin.1 ⟨0, rfl⟩
    rw [Finset.not_disjoint_iff] at hmt
    obtain ⟨x, hxT, hx0⟩ := hmt
    have hxq : x = q := by
      by_contra hne
      have hxR : x ∈ T.erase q := Finset.mem_erase.mpr ⟨hne, hxT⟩
      rw [hRempty] at hxR
      simp at hxR
    rw [hxq] at hx0
    have hqdvd : q ∣ a 0 := Nat.dvd_of_mem_primeFactors hx0
    have hqle : q ≤ a 0 := Nat.le_of_dvd (by omega) hqdvd
    have hsq : (a 0) ^ 2 = a 0 * a 0 := by ring
    rw [hsq]
    calc q ≤ a 0 := hqle
      _ < a 0 * 2 := by omega
      _ ≤ a 0 * a 0 := Nat.mul_le_mul (le_refl (a 0)) (by omega)
  · /- case `R ≠ ∅`: use the least power of `∏ R` exceeding `a 0` -/
    have hRprod2 : 2 ≤ ∏ p ∈ T.erase q, p := by
      obtain ⟨r, hr⟩ := hRne
      have h1 : r ≤ ∏ p ∈ T.erase q, p :=
        Finset.single_le_prod' (fun j hj => (hRprime j hj).one_lt.le) hr
      have h2 : 2 ≤ r := (hRprime r hr).two_le
      omega
    have hnTR : ¬ Trans a (T.erase q) := by
      intro hT
      obtain ⟨n, hn, -⟩ := hreal (T.erase q) hRne hRprime hT
      have heq : T.erase q = T := hTmin.2 (T.erase q) ⟨n, hn⟩ hRsub
      have hqR : q ∈ T.erase q := by
        rw [heq]
        exact hqT
      exact hqnR hqR
    have hex : ∃ t : ℕ, a 0 < (∏ p ∈ T.erase q, p) ^ t := by
      refine ⟨a 0, ?_⟩
      calc a 0 < 2 ^ (a 0) := Nat.lt_two_pow_self
        _ ≤ (∏ p ∈ T.erase q, p) ^ (a 0) := Nat.pow_le_pow_left hRprod2 _
    have ht0 : Nat.find hex ≠ 0 := by
      intro h
      have hsp := Nat.find_spec hex
      rw [h, pow_zero] at hsp
      omega
    obtain ⟨s, hs⟩ : ∃ s, Nat.find hex = s + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hts : a 0 < (∏ p ∈ T.erase q, p) ^ (s + 1) := by
      rw [← hs]
      exact Nat.find_spec hex
    have hsle : (∏ p ∈ T.erase q, p) ^ s ≤ a 0 := by
      have h := Nat.find_min hex (m := s) (by omega)
      omega
    /- `c := (∏ R)^(s+1)` satisfies `a 0 < c ≤ (a 0)^2` and `P(c) = R` -/
    have hcle : (∏ p ∈ T.erase q, p) ^ (s + 1) ≤ (a 0) ^ 2 := by
      have h1 : (∏ p ∈ T.erase q, p) ^ (s + 1)
          = (∏ p ∈ T.erase q, p) ^ s * (∏ p ∈ T.erase q, p) := by ring
      have h2 : (a 0) ^ 2 = a 0 * a 0 := by ring
      rw [h1, h2]
      exact Nat.mul_le_mul hsle hRle
    have hcpos : 0 < (∏ p ∈ T.erase q, p) ^ (s + 1) :=
      Nat.lt_of_le_of_lt (Nat.zero_le (a 0)) hts
    have hcne : (∏ p ∈ T.erase q, p) ^ (s + 1) ≠ 0 := hcpos.ne'
    have hcpf : ((∏ p ∈ T.erase q, p) ^ (s + 1)).primeFactors = T.erase q := by
      rw [Nat.primeFactors_pow _ (Nat.succ_ne_zero s), Nat.primeFactors_prod hRprime]
    have hcnadm : ¬ Adm a ((∏ p ∈ T.erase q, p) ^ (s + 1)) := by
      intro hAdm
      apply hnTR
      intro i
      have h := (hdict ((∏ p ∈ T.erase q, p) ^ (s + 1)) (a i) hcne (hane i)).mp (hAdm i)
      rwa [hcpf] at h
    obtain ⟨i, hilt, hgcd⟩ := hkill ((∏ p ∈ T.erase q, p) ^ (s + 1)) hts hcnadm
    have hdisjR : Disjoint (T.erase q) (PS a i) := by
      by_contra hcon
      have h : 1 < Nat.gcd ((∏ p ∈ T.erase q, p) ^ (s + 1)) (a i) :=
        (hdict ((∏ p ∈ T.erase q, p) ^ (s + 1)) (a i) hcne (hane i)).mpr
          (by rw [hcpf]; exact hcon)
      rw [hgcd] at h
      exact absurd h (lt_irrefl 1)
    /- `T` meets `PS a i` but `R` does not, so `q ∈ PS a i` -/
    have hmt := hmeet T (PS a i) hTmin.1 ⟨i, rfl⟩
    rw [Finset.not_disjoint_iff] at hmt
    obtain ⟨x, hxT, hxi⟩ := hmt
    have hxq : x = q := by
      by_contra hne
      have hxR : x ∈ T.erase q := Finset.mem_erase.mpr ⟨hne, hxT⟩
      exact Finset.disjoint_left.mp hdisjR hxR hxi
    rw [hxq] at hxi
    have hqdvd : q ∣ a i := Nat.dvd_of_mem_primeFactors hxi
    have hqle : q ≤ a i := Nat.le_of_dvd (by have := ha.1 i; omega) hqdvd
    exact lt_of_le_of_lt hqle (lt_of_lt_of_le hilt hcle)

/- item 14 -/
theorem minMem_prod_le (a : ℕ → ℕ) (ha : IsValidSeq a)
    (hbound : ∀ S, IsMinMem a S → ∀ q ∈ S, q < (a 0) ^ 2)
    (S : Finset ℕ) (hS : IsMinMem a S) :
    (∏ p ∈ S, p) ≤ ∏ p ∈ (Finset.range ((a 0) ^ 2)).filter Nat.Prime, p := by
  classical
  /- every element of `S` is a prime below `(a 0)^2` -/
  have hsub : S ⊆ (Finset.range ((a 0) ^ 2)).filter Nat.Prime := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hbound S hS q hq, (minMem_prime a ha S hS).1 q hq⟩
  refine Finset.prod_le_prod_of_subset_of_one_le' hsub ?_
  intro i hi _
  have hp : Nat.Prime i := (Finset.mem_filter.mp hi).2
  exact hp.one_lt.le

/- Step 5: the crux, modulo the three inputs proved separately. -/
theorem exists_stable_of (a : ℕ → ℕ) (ha : IsValidSeq a)
    (hbound : ∀ S, IsMinMem a S → ∀ q ∈ S, q < (a 0) ^ 2)
    (hreal : ∀ X : Finset ℕ, X.Nonempty → (∀ p ∈ X, Nat.Prime p) → Trans a X →
      ∃ n, PS a n = X ∧ a n ≤ a 0 * ∏ p ∈ X, p)
    (hminsub : ∀ n, ∃ S, IsMinMem a S ∧ S ⊆ PS a n) :
    ∃ N, ∀ n, ∃ i ≤ N, (a i).primeFactors ⊆ (a n).primeFactors := by
  classical
  /- `N := a 0 * L` with `L` the product of all primes below `(a 0)^2` -/
  refine ⟨a 0 * ∏ p ∈ (Finset.range ((a 0) ^ 2)).filter Nat.Prime, p, ?_⟩
  intro n
  obtain ⟨S, hS, hSsub⟩ := hminsub n
  obtain ⟨hprime, hne⟩ := minMem_prime a ha S hS
  have htr : Trans a S := realized_trans a ha S hS.1
  obtain ⟨i, hPSi, hai⟩ := hreal S hne hprime htr
  have hL : (∏ p ∈ S, p) ≤ ∏ p ∈ (Finset.range ((a 0) ^ 2)).filter Nat.Prime, p :=
    minMem_prod_le a ha hbound S hS
  have h1 : a i ≤ a 0 * ∏ p ∈ (Finset.range ((a 0) ^ 2)).filter Nat.Prime, p :=
    le_trans hai (Nat.mul_le_mul_left _ hL)
  have h2 : a 0 + i ≤ a i := seq_add_le a ha i
  refine ⟨i, by omega, ?_⟩
  /- `PS a i = S ⊆ PS a n`, and `PS` unfolds to `primeFactors` -/
  have hfin : PS a i ⊆ PS a n := by
    rw [hPSi]
    exact hSsub
  exact hfin

/- THE CRUX: the family of prime supports has finitely many minimal elements. -/
theorem exists_stable (a : ℕ → ℕ) (ha : IsValidSeq a) :
    ∃ N, ∀ n, ∃ i ≤ N, (a i).primeFactors ⊆ (a n).primeFactors := by
  /- discharge the three hypotheses of `exists_stable_of` from the auxiliary lemmas -/
  have hkill : ∀ b, a 0 < b → ¬ Adm a b → ∃ i, a i < b ∧ Nat.gcd b (a i) = 1 :=
    fun b hb hn => killed_early a ha b hb hn
  have hminsub : ∀ n, ∃ S, IsMinMem a S ∧ S ⊆ PS a n := exists_minMem_subset a ha
  have hreal : ∀ X : Finset ℕ, X.Nonempty → (∀ p ∈ X, Nat.Prime p) → Trans a X →
      ∃ n, PS a n = X ∧ a n ≤ a 0 * ∏ p ∈ X, p :=
    fun X hne hp hT => trans_realized a ha X hne hp hT
  have hbound : ∀ S, IsMinMem a S → ∀ q ∈ S, q < (a 0) ^ 2 :=
    fun S hS q hq => prime_bound a ha hkill hminsub hreal S hS q hq
  exact exists_stable_of a ha hbound hreal hminsub

/- If the family of prime-supports stabilises after index `N`, the admissible set
   is invariant under translation by `L = ∏_{i ≤ N} a i`. -/
theorem exists_period (a : ℕ → ℕ) (ha : IsValidSeq a)
    (hstab : ∃ N, ∀ n, ∃ i ≤ N, (a i).primeFactors ⊆ (a n).primeFactors) :
    ∃ L, 0 < L ∧ ∀ b, (Adm a b ↔ Adm a (b + L)) := by
  obtain ⟨N, hN⟩ := hstab
  have hpos : ∀ i, 0 < a i := fun i => lt_trans Nat.one_pos (ha.1 i)
  have hne : ∀ i, a i ≠ 0 := fun i => (hpos i).ne'
  /- Bridge between `1 < Nat.gcd x y` and a common prime divisor. -/
  have key : ∀ x y : ℕ, y ≠ 0 → (1 < Nat.gcd x y ↔ ∃ p, Nat.Prime p ∧ p ∣ x ∧ p ∣ y) := by
    intro x y hy
    constructor
    · intro h
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := Nat.gcd x y) (by omega)
      exact ⟨p, hp, hpd.trans (Nat.gcd_dvd_left x y), hpd.trans (Nat.gcd_dvd_right x y)⟩
    · rintro ⟨p, hp, hpx, hpy⟩
      have hg : p ∣ Nat.gcd x y := Nat.dvd_gcd hpx hpy
      have hgne : Nat.gcd x y ≠ 0 := fun h => hy (Nat.eq_zero_of_gcd_eq_zero_right h)
      have h2 := hp.two_le
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hgne) hg
      omega
  refine ⟨∏ i ∈ Finset.range (N + 1), a i, ?_, ?_⟩
  · exact Finset.prod_pos fun i _ => hpos i
  /- (★): every `a i` with `i ≤ N` divides `L`. -/
  have hdvdL : ∀ i ≤ N, a i ∣ ∏ j ∈ Finset.range (N + 1), a j := by
    intro i hi
    exact Finset.dvd_prod_of_mem a (Finset.mem_range.mpr (by omega))
  intro b
  constructor
  · intro hb j
    obtain ⟨i, hiN, hsub⟩ := hN j
    obtain ⟨p, hp, hpb, hpai⟩ := (key b (a i) (hne i)).mp (hb i)
    have hmem : p ∈ (a i).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpai, hne i⟩
    have hpaj : p ∣ a j := (Nat.mem_primeFactors.mp (hsub hmem)).2.1
    have hpL : p ∣ ∏ j ∈ Finset.range (N + 1), a j := hpai.trans (hdvdL i hiN)
    exact (key _ (a j) (hne j)).mpr ⟨p, hp, dvd_add hpb hpL, hpaj⟩
  · intro hb j
    obtain ⟨i, hiN, hsub⟩ := hN j
    obtain ⟨p, hp, hpb, hpai⟩ := (key _ (a i) (hne i)).mp (hb i)
    have hmem : p ∈ (a i).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpai, hne i⟩
    have hpaj : p ∣ a j := (Nat.mem_primeFactors.mp (hsub hmem)).2.1
    have hpL : p ∣ ∏ j ∈ Finset.range (N + 1), a j := hpai.trans (hdvdL i hiN)
    have hpb' : p ∣ b := (Nat.dvd_add_iff_right hpL).mpr (by rwa [Nat.add_comm] at hpb)
    exact (key b (a j) (hne j)).mpr ⟨p, hp, hpb', hpaj⟩

/- Pure-periodicity lemma P: shift invariance of the admissible set upgrades to
   pure periodicity of the sequence itself, starting from index `0`.  The period index `T` is
   *defined* as the index at which the value `a 0 + L` occurs, so no counting is required. -/
theorem main_of_period (a : ℕ → ℕ) (ha : IsValidSeq a)
    (hper : ∃ L, 0 < L ∧ ∀ b, (Adm a b ↔ Adm a (b + L))) :
    ∃ T L : ℕ, 0 < T ∧ 0 < L ∧ ∀ n, a (n + T) = a n + L := by
  obtain ⟨L, hL0, hshift⟩ := hper
  /- `a 0` is admissible, hence so is `a 0 + L`; it therefore occurs as some `a T`. -/
  have hadm0 : Adm a (a 0 + L) := (hshift (a 0)).mp (adm_seq a ha 0)
  obtain ⟨T, hT⟩ := adm_enum a ha (a 0 + L) hadm0 (by omega)
  have hT0 : 0 < T := by
    rcases Nat.eq_zero_or_pos T with h | h
    · subst h
      omega
    · exact h
  refine ⟨T, L, hT0, hL0, ?_⟩
  intro n
  induction n with
  | zero => simpa using hT
  | succ n ih =>
    have hidx : n + 1 + T = (n + T) + 1 := by omega
    rw [hidx]
    /- Upper bound: `a (n+1) + L` is admissible and exceeds `a (n+T)`. -/
    have h1 : Adm a (a (n + 1) + L) := (hshift (a (n + 1))).mp (adm_seq a ha (n + 1))
    have hlt1 : a (n + T) < a (n + 1) + L := by
      have := seq_lt_succ a ha n
      omega
    have hle : a ((n + T) + 1) ≤ a (n + 1) + L :=
      succ_le_of_adm a ha (n + T) (a (n + 1) + L) h1 hlt1
    /- Lower bound: shift `c := a ((n+T)+1)` back by `L`. -/
    set c := a ((n + T) + 1) with hc
    have hcgt : a (n + T) < c := seq_lt_succ a ha (n + T)
    have hcL : L ≤ c := by omega
    have hsub : (c - L) + L = c := Nat.sub_add_cancel hcL
    have hadmc : Adm a c := adm_seq a ha ((n + T) + 1)
    have hadmc' : Adm a (c - L) := by
      apply (hshift (c - L)).mpr
      rw [hsub]
      exact hadmc
    have hgt : a n < c - L := by omega
    have hge : a (n + 1) ≤ c - L := succ_le_of_adm a ha n (c - L) hadmc' hgt
    omega

/-- For any sequence satisfying Definition 1, there exist positive integers `T` and `L` such that
`a (n + T) = a n + L` for every `n`. Equivalently, the sequence of consecutive differences is
purely periodic. -/
theorem main_theorem (a : ℕ → ℕ) (ha : IsValidSeq a) :
    ∃ T L : ℕ, 0 < T ∧ 0 < L ∧ ∀ n, a (n + T) = a n + L := by
  exact main_of_period a ha (exists_period a ha (exists_stable a ha))
