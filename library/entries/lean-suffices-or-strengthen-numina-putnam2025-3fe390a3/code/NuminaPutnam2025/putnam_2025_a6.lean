import Mathlib
set_option pp.numericTypes true
set_option pp.funBinderTypes true
set_option maxHeartbeats 0
open Classical

-- Key helper: b n ≥ 0 for all n
lemma b_nonneg (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    ∀ n, 0 ≤ b n := by
  intro n
  induction n with
  | zero => simp [hb0]
  | succ n ih =>
    rw [hb]
    have h1 : 0 ≤ 2 * b n ^ 2 := by positivity
    linarith

-- b 1 = 1
lemma b_one (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    b 1 = 1 := by
  rw [hb, hb0]
  ring

-- b 2 = 4
lemma b_two (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    b 2 = 4 := by
  have h1 := b_one b hb0 hb
  rw [show (2 : ℕ) = 1 + 1 by norm_num, hb, h1]
  ring

-- b n is positive for n ≥ 1
lemma b_pos (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    ∀ n ≥ 1, 0 < b n := by
  intro n hn
  cases n with
  | zero => simp at hn
  | succ n =>
    rw [hb]
    have h := b_nonneg b hb0 hb n
    nlinarith [sq_nonneg (b n)]

-- b n ≠ 0 for n ≥ 1
lemma b_ne_zero (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    ∀ n ≥ 1, b n ≠ 0 := by
  intro n hn
  exact ne_of_gt (b_pos b hb0 hb n hn)

-- 4b_n + 1 is odd for all n
lemma four_b_add_one_odd (b : ℕ → ℤ) :
    ∀ n, Odd (4 * b n + 1) := by
  intro n
  use 2 * b n
  ring

-- Define A_n = ∏_{i=0}^{n-1} (4*b_i + 1)
noncomputable def A (b : ℕ → ℤ) : ℕ → ℤ
| 0 => 1
| n + 1 => A b n * (4 * b n + 1)

-- A n is odd for all n
lemma A_odd (b : ℕ → ℤ) :
    ∀ n, Odd (A b n) := by
  intro n
  induction n with
  | zero => simp only [A]; use 0; ring
  | succ n ih =>
    simp only [A]
    have h1 := four_b_add_one_odd b n
    exact Odd.mul ih h1

-- A n > 0 for all n
lemma A_pos (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    ∀ n, 0 < A b n := by
  intro n
  induction n with
  | zero => simp [A]
  | succ n ih =>
    rw [A]
    have h := b_nonneg b hb0 hb n
    have h1 : 0 < 4 * b n + 1 := by linarith
    exact mul_pos ih h1

-- A n ≠ 0
lemma A_ne_zero (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    ∀ n, A b n ≠ 0 := by
  intro n
  exact ne_of_gt (A_pos b hb0 hb n)

-- A 1 = 1
lemma A_one (b : ℕ → ℤ) (hb0 : b 0 = 0) :
    A b 1 = 1 := by
  simp [A, hb0]

-- A 2 = 5
lemma A_two (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    A b 2 = 5 := by
  have h1 := b_one b hb0 hb
  simp only [A, hb0, h1]
  ring

-- b 3 = 37
lemma b_three (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    b 3 = 37 := by
  have h2 := b_two b hb0 hb
  rw [show (3 : ℕ) = 2 + 1 by norm_num, hb, h2]
  ring

-- b 4 = 2776
lemma b_four (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    b 4 = 2776 := by
  have h3 := b_three b hb0 hb
  rw [show (4 : ℕ) = 3 + 1 by norm_num, hb, h3]
  ring

-- Define the iterated function
noncomputable def f_iter (b : ℕ → ℤ) : ℕ → ℤ → ℤ
| 0, x => x
| n + 1, x => 2 * (f_iter b n x) ^ 2 + f_iter b n x + 1

-- f_iter b m (b n) = b (n + m)
lemma f_iter_b (b : ℕ → ℤ) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    ∀ m n, f_iter b m (b n) = b (n + m) := by
  intro m
  induction m with
  | zero => intro n; simp [f_iter]
  | succ m ih =>
    intro n
    simp only [f_iter]
    rw [ih n, ← hb]
    ring_nf

-- Helper: b_n.natAbs when b_n > 0
lemma b_natAbs (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    ∀ n ≥ 1, (b n).natAbs = b n := by
  intro n hn
  exact Int.natAbs_of_nonneg (le_of_lt (b_pos b hb0 hb n hn))

-- Base case k = 1:
lemma base_case_b (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    padicValInt 2 (b (2^1)) = 1 + 1 := by
  simp only [pow_one]
  rw [b_two b hb0 hb]
  -- Need to prove padicValInt 2 4 = 2
  simp only [padicValInt]
  -- 4 = 2^2, so padicValNat 2 4 = 2
  have h4 : (4 : ℤ).natAbs = 4 := rfl
  rw [h4]
  have h : (4 : ℕ) = 2^2 := by norm_num
  rw [h]
  exact padicValNat.prime_pow 2

lemma base_case_A (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    padicValInt 2 (A b (2^1) - 1) = 1 + 1 := by
  simp only [pow_one]
  rw [A_two b hb0 hb]
  -- Need to prove padicValInt 2 (5 - 1) = 2, i.e., padicValInt 2 4 = 2
  norm_num
  simp only [padicValInt]
  have h4 : (4 : ℤ).natAbs = 4 := rfl
  rw [h4]
  have h : (4 : ℕ) = 2^2 := by norm_num
  rw [h]
  exact padicValNat.prime_pow 2

-- The main approach: prove a combined inductive statement
-- P(k): v_2(b_{2^k}) = k + 1 AND v_2(A_{2^k} - 1) = k + 1 for k ≥ 1

-- A b n ≡ 1 (mod 4) for all n
lemma A_mod_four (b : ℕ → ℤ) : ∀ n, A b n ≡ 1 [ZMOD 4] := by
  intro n
  induction n with
  | zero => simp [A]
  | succ n ih =>
    simp only [A]
    have h1 : 4 * b n + 1 ≡ 1 [ZMOD 4] := by
      show (4 * b n + 1) % 4 = 1 % 4
      rw [Int.add_emod, Int.mul_emod, Int.emod_self, zero_mul, Int.zero_emod]
      norm_num
    calc A b n * (4 * b n + 1) ≡ A b n * 1 [ZMOD 4] := Int.ModEq.mul_left _ h1
      _ = A b n := by ring
      _ ≡ 1 [ZMOD 4] := ih

-- Key lemma: A_n + 1 has exactly one factor of 2 (since A_n is odd and A_n ≡ 1 (mod 4))
lemma A_add_one_val (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    ∀ n, padicValInt 2 (A b n + 1) = 1 := by
  intro n
  have hodd := A_odd b n
  obtain ⟨m, hm⟩ := hodd
  have heq : A b n + 1 = 2 * (m + 1) := by rw [hm]; ring
  have hA_pos := A_pos b hb0 hb n
  rw [hm] at hA_pos
  have hm1_ne : m + 1 ≠ 0 := by linarith
  have hpos : 0 ≤ m + 1 := by linarith
  have h2_ne : (2 : ℤ) ≠ 0 := by norm_num
  rw [heq, padicValInt.mul h2_ne hm1_ne]
  have hv2 : padicValInt 2 (2 : ℤ) = 1 := by
    simp only [padicValInt]
    have h2 : (2 : ℤ).natAbs = 2 := rfl
    rw [h2]
    exact padicValNat.self (by norm_num : 1 < 2)
  rw [hv2]
  -- Need to show v_2(m + 1) = 0, i.e., m + 1 is odd
  have hA_mod4 := A_mod_four b n
  have hm_even : 2 ∣ m := by
    have heq2 : A b n - 1 = 2 * m := by rw [hm]; ring
    have h4' : 4 ∣ A b n - 1 := by
      rw [Int.ModEq] at hA_mod4
      have : A b n % 4 = 1 % 4 := hA_mod4
      have h1 : 1 % (4 : ℤ) = 1 := by norm_num
      rw [h1] at this
      have : (A b n - 1) % 4 = 0 := by omega
      exact Int.dvd_of_emod_eq_zero this
    rw [heq2] at h4'
    have : (4 : ℤ) = 2 * 2 := by norm_num
    rw [this] at h4'
    exact (Int.mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h4'
  obtain ⟨k, hk⟩ := hm_even
  have hm1_odd : ¬(2 : ℤ) ∣ m + 1 := by
    rw [hk]
    intro hdiv
    have : (2 : ℤ) ∣ 2 * k + 1 := hdiv
    have h2div : (2 : ℤ) ∣ 2 * k := ⟨k, rfl⟩
    have : (2 : ℤ) ∣ 1 := (Int.dvd_add_right h2div).mp this
    omega
  simp only [padicValInt]
  have hm1_odd' : ¬(2 : ℕ) ∣ (m + 1).natAbs := by
    intro hdiv
    have h2nat : (2 : ℤ) ∣ (((m + 1).natAbs : ℕ) : ℤ) := by
      obtain ⟨d, hd⟩ := hdiv
      use d
      simp [hd]
    have : ((m + 1).natAbs : ℤ) = m + 1 := Int.natAbs_of_nonneg hpos
    rw [this] at h2nat
    exact hm1_odd h2nat
  have hvm1 : padicValNat 2 (m + 1).natAbs = 0 := padicValNat.eq_zero_of_not_dvd hm1_odd'
  omega

-- Let's take a more computational approach for the proof

-- Define c2 recursively
noncomputable def c2 (b : ℕ → ℤ) : ℕ → ℤ
| 0 => 0
| n + 1 => c2 b n * (4 * b n + 1) + 2 * (A b n) ^ 2

-- c2 n ≡ 2n (mod 4)
lemma c2_mod_four (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    ∀ n, c2 b n ≡ 2 * n [ZMOD 4] := by
  intro n
  induction n with
  | zero => simp [c2]
  | succ n ih =>
    simp only [c2]
    -- c2 (n+1) = c2 n * (4*b_n + 1) + 2 * A_n^2
    -- ≡ c2 n * 1 + 2 * 1 (mod 4)  since 4*b_n ≡ 0 (mod 4) and A_n is odd
    -- ≡ c2 n + 2 (mod 4)
    -- ≡ 2n + 2 (mod 4) by IH
    -- ≡ 2(n+1) (mod 4)
    have h1 : 4 * b n + 1 ≡ 1 [ZMOD 4] := by
      show (4 * b n + 1) % 4 = 1 % 4
      rw [Int.add_emod]
      have : (4 : ℤ) * b n % 4 = 0 := by
        rw [Int.mul_emod, Int.emod_self, zero_mul, Int.zero_emod]
      rw [this]
      norm_num
    have h2 : (A b n) ^ 2 ≡ 1 [ZMOD 4] := by
      have hodd := A_odd b n
      -- A_n is odd, so A_n = 2m + 1 for some m
      obtain ⟨m, hm⟩ := hodd
      show (A b n) ^ 2 % 4 = 1 % 4
      rw [hm]
      have heq : (2 * m + 1) ^ 2 = 4 * m * (m + 1) + 1 := by ring
      rw [heq, Int.add_emod]
      have h4div : (4 : ℤ) ∣ 4 * m * (m + 1) := by use m * (m + 1); ring
      rw [Int.emod_eq_zero_of_dvd h4div]
      norm_num
    have h3 : 2 * (A b n) ^ 2 ≡ 2 [ZMOD 4] := by
      calc 2 * (A b n) ^ 2 ≡ 2 * 1 [ZMOD 4] := Int.ModEq.mul_left 2 h2
        _ = 2 := by ring
    have h4 : c2 b n * (4 * b n + 1) ≡ c2 b n * 1 [ZMOD 4] := Int.ModEq.mul_left (c2 b n) h1
    have h5 : c2 b n * 1 = c2 b n := by ring
    calc c2 b n * (4 * b n + 1) + 2 * (A b n) ^ 2
        ≡ c2 b n + 2 [ZMOD 4] := Int.ModEq.add (h4.trans (by rw [h5])) h3
      _ ≡ 2 * n + 2 [ZMOD 4] := Int.ModEq.add ih rfl
      _ = 2 * (n + 1) := by ring

-- For n = 2^k with k ≥ 1, 4 | c2(n)
lemma c2_div_four (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    ∀ k ≥ 1, (4 : ℤ) ∣ c2 b (2^k) := by
  intro k hk
  have h := c2_mod_four b hb0 hb (2^k)
  -- c2 b (2^k) ≡ 2 * 2^k (mod 4)
  -- Since k ≥ 1, 2 * 2^k = 2^{k+1} is divisible by 4
  have h2 : (4 : ℤ) ∣ 2 * (2^k : ℕ) := by
    have hk2 : k + 1 ≥ 2 := by omega
    have heq : (2 : ℤ) * (2^k : ℕ) = (2 : ℤ)^(k+1) := by
      push_cast
      rw [pow_succ]
      ring
    rw [heq]
    have : (4 : ℤ) = 2^2 := by norm_num
    rw [this]
    exact pow_dvd_pow 2 hk2
  -- From h: c2 b (2^k) ≡ 2 * (2^k : ℕ) [ZMOD 4]
  -- From h2: 4 | 2 * (2^k : ℕ)
  -- Therefore 4 | c2 b (2^k)
  have h3 : (2 : ℤ) * (2^k : ℕ) ≡ 0 [ZMOD 4] := Int.modEq_zero_iff_dvd.mpr h2
  exact Int.modEq_zero_iff_dvd.mp (h.trans h3)

-- The key expansion lemma:
-- f^m(x) = b_m + A_m * x + c2(m) * x^2 + (higher order terms divisible by x^3)
-- This means: f^m(b_n) = b_m + A_m * b_n + c2(m) * b_n^2 + (terms with b_n^3)

-- For the iteration, b_{n+m} = f^m(b_n), so:
-- b_{n+m} = b_m + A_m * b_n + c2(m) * b_n^2 + O(b_n^3)

-- Taking n = m:
-- b_{2m} = b_m + A_m * b_m + c2(m) * b_m^2 + O(b_m^3)
--        = b_m * (1 + A_m) + c2(m) * b_m^2 + O(b_m^3)

-- Therefore:
-- b_{2m} - 2*b_m = b_m * (A_m - 1) + c2(m) * b_m^2 + O(b_m^3)

-- To make this rigorous, we need to work with the polynomial expansion explicitly

-- Alternative approach: prove the main theorem computationally for small k,
-- then use the algebraic structure for general k

-- Let me first check k = 1 (base case):
-- b(2^2) - 2*b(2^1) = b(4) - 2*b(2) = 2776 - 2*4 = 2776 - 8 = 2768
-- v_2(2768) = v_2(16 * 173) = 4 = 2*1 + 2 ✓

example : padicValInt 2 (2776 - 8) = 2 * 1 + 2 := by
  -- 2776 - 8 = 2768 = 16 * 173 = 2^4 * 173
  norm_num only
  simp only [padicValInt]
  have h : (2768 : ℤ).natAbs = 2768 := rfl
  rw [h]
  -- padicValNat 2 2768 = 4
  have h2768 : (2768 : ℕ) = 2^4 * 173 := by norm_num
  rw [h2768]
  rw [padicValNat.mul (by norm_num : (2 : ℕ) ^ 4 ≠ 0) (by norm_num : (173 : ℕ) ≠ 0)]
  simp only [padicValNat.prime_pow 4]
  have h173 : padicValNat 2 173 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hdvd
    have : 173 % 2 = 1 := by norm_num
    have : 173 % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    omega
  omega

-- For k = 2:
-- b(2^3) - 2*b(2^2) = b(8) - 2*b(4) = b(8) - 2*2776 = b(8) - 5552
-- We need to compute b(5), b(6), b(7), b(8)

-- This is getting complex. Let me try a different approach using the structure
-- of the proof more directly.

-- The key expansion identity: b_{n+m} ≡ b_m + A_m * b_n (mod b_n^2)
-- More precisely: b_{n+m} - b_m - A_m * b_n is divisible by b_n^2

-- This is the crucial relationship that comes from the Taylor-like expansion of f^m(x)
-- f^m(x) = b_m + A_m * x + c_2(m) * x^2 + ...

-- The proof strategy:
-- 1. Show that b_{2^k} divides b_{2^{k+1}} - b_{2^k} * (1 + A_{2^k})
-- 2. Show that v_2(b_{2^k}) = k + 1 and v_2(A_{2^k} - 1) = k + 1
-- 3. Use these to show v_2(b_{2^{k+1}} - 2*b_{2^k}) = 2k + 2

-- Key lemma: The "remainder" term when expanding b_{2n}
-- b_{2n} = b_n * (1 + A_n) + R_n where R_n has high divisibility by b_n

-- For now, let's prove this using strong induction with a combined statement
-- that captures both v_2(b_{2^k}) = k+1 and v_2(A_{2^k} - 1) = k+1

-- Combined inductive hypothesis for the proof
-- P(k): For k ≥ 1, v_2(b_{2^k}) = k + 1 AND v_2(A_{2^k} - 1) = k + 1

-- We need to define what it means for the expansion to work correctly
-- The key is: b_{n+m} = b_m + A_m * b_n + (stuff divisible by b_n^2)

-- Let's define the "expansion error" E_m(x) = f^m(x) - b_m - A_m * x
-- This should be divisible by x^2

-- For the main theorem, we can use the following approach:
-- The result b_{2^{k+1}} - 2*b_{2^k} = b_{2^k} * (A_{2^k} - 1) + (error terms)
-- where the error terms have valuation > 2k + 2

-- Since this is very complex to formalize fully, let me try a direct computational
-- approach for small k, combined with the structural argument

-- First, let's verify the result computationally for k = 1
lemma base_case_main (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    padicValInt 2 (b (2 ^ (1 + 1)) - 2 * b (2 ^ 1)) = 2 * 1 + 2 := by
  have h4 : b 4 = 2776 := b_four b hb0 hb
  have h2 : b 2 = 4 := b_two b hb0 hb
  have heq1 : (2 : ℕ) ^ (1 + 1) = 4 := by norm_num
  have heq2 : (2 : ℕ) ^ 1 = 2 := by norm_num
  rw [heq1, heq2, h4, h2]
  -- Need to prove padicValInt 2 (2776 - 2*4) = 4, i.e., padicValInt 2 2768 = 4
  norm_num only
  simp only [padicValInt]
  have h : (2768 : ℤ).natAbs = 2768 := rfl
  rw [h]
  -- 2768 = 2^4 * 173
  have h2768 : (2768 : ℕ) = 2^4 * 173 := by norm_num
  rw [h2768]
  rw [padicValNat.mul (by norm_num : (2 : ℕ) ^ 4 ≠ 0) (by norm_num : (173 : ℕ) ≠ 0)]
  simp only [padicValNat.prime_pow 4]
  have h173 : padicValNat 2 173 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hdvd
    have : 173 % 2 = 1 := by norm_num
    have : 173 % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    omega
  omega

-- For the general case, we need the structural argument
-- The main observation is:
-- b_{2n} = f^n(b_n) where f(x) = 2x^2 + x + 1
-- And f^n(x) = b_n + A_n * x + O(x^2)

-- Therefore b_{2n} = b_n + A_n * b_n + O(b_n^2) = b_n * (1 + A_n) + O(b_n^2)
-- So b_{2n} - 2*b_n = b_n * (A_n - 1) + O(b_n^2)

-- The O(b_n^2) term is c2(n) * b_n^2 + higher order terms

-- For n = 2^k with k ≥ 1:
-- v_2(b_n * (A_n - 1)) = v_2(b_n) + v_2(A_n - 1) = (k+1) + (k+1) = 2k+2
-- v_2(c2(n) * b_n^2) ≥ v_2(b_n^2) = 2(k+1) = 2k+2
-- But we need v_2(c2(n) * b_n^2) > 2k+2 for the dominant term to be b_n * (A_n - 1)

-- This is where the fact that 4 | c2(n) for n = 2^k, k ≥ 1 comes in:
-- v_2(c2(n) * b_n^2) ≥ 2 + 2(k+1) = 2k+4 > 2k+2 ✓

-- Now I need to formalize the expansion identity
-- The key lemma: for any m ≥ 0 and starting value x,
-- f^m(x) - b_m - A_m * x is divisible by x^2

-- This can be proven by induction on m

-- For f = 2x^2 + x + 1:
-- f(x) - b_1 - A_1 * x = 2x^2 + x + 1 - 1 - 1*x = 2x^2 (which is divisible by x^2) ✓

-- For the inductive step, if P_m(x) = f^m(x) - b_m - A_m * x is divisible by x^2,
-- then P_{m+1}(x) = f^{m+1}(x) - b_{m+1} - A_{m+1} * x
--                = f(f^m(x)) - b_{m+1} - A_{m+1} * x
--                = 2*(f^m(x))^2 + f^m(x) + 1 - b_{m+1} - A_{m+1} * x

-- Since f^m(x) = b_m + A_m * x + Q(x)*x^2 for some polynomial Q,
-- we have (f^m(x))^2 = b_m^2 + 2*b_m*A_m*x + (A_m*x)^2 + 2*b_m*Q(x)*x^2 + ...
--                   = b_m^2 + 2*b_m*A_m*x + (terms with x^2)

-- So f(f^m(x)) = 2*(b_m^2 + 2*b_m*A_m*x + ...) + (b_m + A_m*x + ...) + 1
--              = 2*b_m^2 + b_m + 1 + (4*b_m*A_m + A_m)*x + O(x^2)
--              = b_{m+1} + A_m*(4*b_m + 1)*x + O(x^2)
--              = b_{m+1} + A_{m+1}*x + O(x^2)

-- This confirms the expansion holds at each step!

-- Let me define this more formally and use it in the proof

-- The expansion error term
noncomputable def ExpErr (b : ℕ → ℤ) (m : ℕ) (x : ℤ) : ℤ :=
  f_iter b m x - b m - A b m * x

-- Key lemma: x^2 divides ExpErr b m x for all m
lemma x_sq_dvd_exp_err (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    ∀ m x, x^2 ∣ ExpErr b m x := by
  intro m
  induction m with
  | zero =>
    intro x
    simp only [ExpErr, f_iter, A, hb0]
    use 0
    ring
  | succ m ih =>
    intro x
    simp only [ExpErr, f_iter, A]
    -- f_iter b (m+1) x = 2 * (f_iter b m x)^2 + (f_iter b m x) + 1
    -- We need to show: 2*(f_iter b m x)^2 + f_iter b m x + 1 - b(m+1) - A(m+1)*x ≡ 0 (mod x^2)
    -- Using f_iter b m x = b m + A m * x + ExpErr b m x
    -- and ExpErr b m x = q * x^2 for some q (by ih)
    have hih := ih x
    obtain ⟨q, hq⟩ := hih
    -- f_iter b m x = b m + A b m * x + q * x^2
    -- ExpErr b m x = f_iter b m x - b m - A b m * x = q * x^2
    -- So f_iter b m x = b m + A b m * x + q * x^2
    have hfm : f_iter b m x = b m + A b m * x + q * x^2 := by
      have : ExpErr b m x = f_iter b m x - b m - A b m * x := rfl
      rw [this] at hq
      linarith
    -- Now expand 2*(b m + A b m * x + q * x^2)^2 + (b m + A b m * x + q * x^2) + 1
    -- - b(m+1) - A(m+1)*x

    have hbm1 : b (m + 1) = 2 * b m ^ 2 + b m + 1 := hb m

    -- The goal after simplification is:
    -- 2*(b m + A b m * x + q * x^2)^2 + (b m + A b m * x + q * x^2) + 1
    --   - (2*b m^2 + b m + 1) - (A b m * (4*b m + 1)) * x
    -- = x^2 * (some coefficient)

    -- Let's expand: 2*(b m + A b m * x + q * x^2)^2
    -- = 2*(b m^2 + 2*b m*A b m*x + 2*b m*q*x^2 + (A b m)^2*x^2 + 2*A b m*q*x^3 + q^2*x^4)
    -- = 2*b m^2 + 4*b m*A b m*x + 4*b m*q*x^2 + 2*(A b m)^2*x^2 + 4*A b m*q*x^3 + 2*q^2*x^4

    -- Adding (b m + A b m * x + q * x^2) + 1:
    -- = 2*b m^2 + b m + 1 + (4*b m*A b m + A b m)*x + (4*b m*q + 2*(A b m)^2 + q)*x^2 + ...

    -- Subtracting (2*b m^2 + b m + 1) and (A b m*(4*b m + 1))*x:
    -- The constant term: 2*b m^2 + b m + 1 - (2*b m^2 + b m + 1) = 0 ✓
    -- The x term: (4*b m*A b m + A b m) - A b m*(4*b m + 1) = 4*b m*A b m + A b m - 4*b m*A b m - A b m = 0 ✓
    -- The x^2 term: 4*b m*q + 2*(A b m)^2 + q = (4*b m + 1)*q + 2*(A b m)^2
    -- But wait, we need to check this is the correct coefficient

    -- Actually let me just compute more carefully
    -- Looking at the expanded terms, the coefficient should be:
    -- 2*(A b m)^2 + (4*b m + 1)*q + 4*A b m*q*x + 2*q^2*x^2
    use 2 * (A b m)^2 + (4 * b m + 1) * q + 4 * A b m * q * x + 2 * q^2 * x^2
    simp only [hfm, hbm1]
    ring

-- Now we can express b_{2n} - b_n - A_n * b_n in terms of the expansion error
lemma b_double_expansion (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    ∀ n, b (2 * n) - b n - A b n * b n = ExpErr b n (b n) := by
  intro n
  simp only [ExpErr]
  have h := f_iter_b b hb n n
  rw [h, Nat.add_comm n n, Nat.two_mul]

-- Therefore b_{2n} = b_n * (1 + A_n) + ExpErr b n (b_n)
-- and b_{2n} - 2*b_n = b_n * (A_n - 1) + ExpErr b n (b_n)

-- Since (b_n)^2 | ExpErr b n (b_n), we have:
-- b_{2n} - 2*b_n = b_n * (A_n - 1) + (b_n)^2 * (some integer)

-- Key lemma: When dividing ExpErr b n (b n) by (b n)^2, the quotient q satisfies 2 | q
-- This follows from the expansion structure
-- Note: The proof requires tracking coefficients through the recursion in x_sq_dvd_exp_err
-- For the purposes of this theorem, we admit this technical fact
lemma two_dvd_exp_err_quotient (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1)
    (n : ℕ) (hn : n ≥ 1) (hbn_ne : b n ≠ 0) :
    ∀ q, ExpErr b n (b n) = (b n)^2 * q → (2 : ℤ) ∣ q := by
  -- The expansion shows: ExpErr b m x = x^2 * Q where Q has specific structure
  -- We prove by induction on n that 2 | Q when evaluating at x = b n
  intro q hq
  -- Use induction on n
  induction n with
  | zero =>
    -- n = 0: ExpErr b 0 (b 0) = f_iter b 0 (b 0) - b 0 - A b 0 * b 0
    --                        = b 0 - 0 - 1 * 0 = 0
    simp only [ExpErr, f_iter, A, hb0] at hq
    -- hq : 0 = 0^2 * q = 0
    simp at hq
    -- So q can be anything, but we need 2 | q
    -- Actually, 0 = 0 * q is satisfied for any q
    -- But from hbn_ne, we have b 0 ≠ 0, but hb0 says b 0 = 0, contradiction
    exfalso
    exact hbn_ne hb0
  | succ m ih =>
    -- For n = m + 1, we use the structure of ExpErr
    -- ExpErr b (m+1) (b (m+1)) = f_iter b (m+1) (b (m+1)) - b (m+1) - A b (m+1) * b (m+1)
    -- By f_iter_b: f_iter b (m+1) (b (m+1)) = b (m+1 + m+1) = b (2m+2) = b (2*(m+1))
    -- So ExpErr b (m+1) (b (m+1)) = b (2*(m+1)) - b (m+1) - A b (m+1) * b (m+1)
    --                             = b (2*(m+1)) - b (m+1) * (1 + A b (m+1))
    -- Now use b_double_eq: b (2*(m+1)) = b (m+1) * (1 + A b (m+1)) + ExpErr b (m+1) (b (m+1))
    -- This is circular!

    -- Alternative: Use the expansion from x_sq_dvd_exp_err
    -- The key is that ExpErr b (m+1) x = x^2 * (2*(A b m)^2 + (4*b m + 1)*q_m + ...)
    -- where q_m is the quotient from the previous step

    -- For the successor case, we need to show that the coefficient is even
    -- This follows from the structure but requires careful tracking

    -- Use the explicit formula from x_sq_dvd_exp_err
    have h_exp := x_sq_dvd_exp_err b hb0 hb (m + 1) (b (m + 1))
    obtain ⟨q', hq'⟩ := h_exp
    -- hq' : ExpErr b (m+1) (b (m+1)) = (b (m+1))^2 * q'
    -- We need to show 2 | q' (and q = q')

    -- From hq and hq', we have (b (m+1))^2 * q = (b (m+1))^2 * q'
    -- Since b (m+1) ≠ 0 (by hbn_ne), we get q = q'
    have hq_eq : q = q' := by
      have hbsq_ne : (b (m + 1))^2 ≠ 0 := pow_ne_zero 2 hbn_ne
      have h : (b (m + 1))^2 * q = (b (m + 1))^2 * q' := by rw [← hq, ← hq']
      exact mul_left_cancel₀ hbsq_ne h
    rw [hq_eq]

    -- Now show 2 | q' using the structure from the proof
    -- From the proof of x_sq_dvd_exp_err (successor case):
    -- q' = 2 * (A b m)^2 + (4 * b m + 1) * q_prev + 4 * A b m * q_prev * (b (m+1)) + 2 * q_prev^2 * (b (m+1))^2
    -- where q_prev is the quotient for ExpErr b m (b (m+1))

    -- Since the first term 2 * (A b m)^2 is even, and the other terms either have factor 2 or factor 4,
    -- the entire expression is even

    -- But we need to establish this formally. The challenge is that the induction in x_sq_dvd_exp_err
    -- is on m (the number of iterations), not on the evaluation point.

    -- For a clean proof, let's use divisibility by 2 directly from the structure
    -- Note: The coefficient q' = 2*(A)^2 + (4b+1)*q_prev + 4*A*q_prev*x + 2*q_prev^2*x^2
    -- All terms except (4b+1)*q_prev have explicit factor 2
    -- For (4b+1)*q_prev: since 4b+1 is odd, the parity equals parity of q_prev
    -- At the base (m=0), q_prev = 0 which is even
    -- So by induction, q_prev is even, hence the whole expression is even

    -- We prove that the quotient in x_sq_dvd_exp_err is always even
    -- by showing a combined statement: ∃ q, ExpErr b m x = x^2 * q ∧ 2 | q

    -- First, establish that q' has the explicit form from x_sq_dvd_exp_err
    -- Then show this form implies 2 | q'

    -- Key insight: From x_sq_dvd_exp_err proof, we have:
    -- For m = 0: ExpErr b 0 x = 0 = x^2 * 0, and 2 | 0 ✓
    -- For m + 1: The quotient is 2*(A)^2 + (4b+1)*q_prev + 4*A*q_prev*x + 2*q_prev^2*x^2
    --           = 2*((A)^2 + 2*A*q_prev*x + q_prev^2*x^2) + (4b+1)*q_prev
    --           = 2*(something) + (4b+1)*q_prev
    -- Since 2 | q_prev (by IH), and the first term has factor 2, we get 2 | q_new

    -- We formalize this as follows:
    have h_dvd : ∀ m x, ∃ q, ExpErr b m x = x^2 * q ∧ (2 : ℤ) ∣ q := by
      intro m
      induction m with
      | zero =>
        intro x
        use 0
        simp only [ExpErr, f_iter, A, hb0]
        constructor
        · ring
        · exact dvd_zero 2
      | succ m' ihm' =>
        intro x
        obtain ⟨q_prev, hq_prev_eq, hq_prev_dvd⟩ := ihm' x
        -- From x_sq_dvd_exp_err proof:
        -- ExpErr b (m'+1) x = x^2 * (2*(A b m')^2 + (4*b m'+1)*q_prev + 4*A b m'*q_prev*x + 2*q_prev^2*x^2)
        have hfm : f_iter b m' x = b m' + A b m' * x + q_prev * x^2 := by
          have : ExpErr b m' x = f_iter b m' x - b m' - A b m' * x := rfl
          rw [this] at hq_prev_eq
          linarith
        let q_new := 2 * (A b m')^2 + (4 * b m' + 1) * q_prev + 4 * A b m' * q_prev * x + 2 * q_prev^2 * x^2
        use q_new
        constructor
        · simp only [ExpErr, f_iter]
          simp only [hfm, hb m']
          have hA_succ : A b (m' + 1) = A b m' * (4 * b m' + 1) := rfl
          rw [hA_succ]
          ring
        · -- Show 2 | q_new
          have h1 : (2 : ℤ) ∣ 2 * (A b m')^2 := dvd_mul_right 2 _
          obtain ⟨k, hk⟩ := hq_prev_dvd
          have h2 : (2 : ℤ) ∣ (4 * b m' + 1) * q_prev := by
            rw [hk]
            use (4 * b m' + 1) * k
            ring
          have h3 : (2 : ℤ) ∣ 4 * A b m' * q_prev * x := by
            use 2 * A b m' * q_prev * x
            ring
          have h4 : (2 : ℤ) ∣ 2 * q_prev^2 * x^2 := dvd_mul_of_dvd_left (dvd_mul_right 2 _) _
          exact dvd_add (dvd_add (dvd_add h1 h2) h3) h4

    -- Now apply h_dvd to get 2 | q'
    obtain ⟨q'', hq''_eq, hq''_dvd⟩ := h_dvd (m + 1) (b (m + 1))
    -- q'' is the quotient with 2 | q''
    -- We have q' = q'' since both are unique quotients
    have hq'_eq_q'' : q' = q'' := by
      have hbsq_ne : (b (m + 1))^2 ≠ 0 := pow_ne_zero 2 hbn_ne
      have h : (b (m + 1))^2 * q' = (b (m + 1))^2 * q'' := by rw [← hq', ← hq''_eq]
      exact mul_left_cancel₀ hbsq_ne h
    rw [hq'_eq_q'']
    exact hq''_dvd

-- For n = 2^k with k ≥ 1:
-- v_2(b_n * (A_n - 1)) = v_2(b_n) + v_2(A_n - 1) = (k+1) + (k+1) = 2k+2
-- v_2((b_n)^2) = 2*v_2(b_n) = 2(k+1) = 2k+2

-- So v_2(b_{2n} - 2*b_n) ≥ min(2k+2, 2k+2) = 2k+2

-- For equality, we need to show that v_2(b_n * (A_n - 1) + something divisible by b_n^2) = 2k+2

-- The key is that b_n * (A_n - 1) and the error term both have valuation exactly 2k+2
-- (or the error term has strictly higher valuation)

-- Actually, for the error term:
-- ExpErr b n (b_n) = c2(n) * (b_n)^2 + (higher order terms)
-- For n = 2^k, 4 | c2(n), so v_2(c2(n)) ≥ 2
-- Therefore v_2(c2(n) * (b_n)^2) ≥ 2 + 2(k+1) = 2k+4 > 2k+2

-- So the dominant term is b_n * (A_n - 1), and v_2(b_{2n} - 2*b_n) = 2k+2

-- To make this rigorous, I need to prove:
-- 1. v_2(b_{2^k}) = k+1 for k ≥ 1
-- 2. v_2(A_{2^k} - 1) = k+1 for k ≥ 1
-- And then use these with the expansion

-- Key expansion: b_{2n} = b_n * (1 + A_n) + ExpErr b n (b_n)
lemma b_double_eq (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    ∀ n, b (2 * n) = b n * (1 + A b n) + ExpErr b n (b n) := by
  intro n
  have h := b_double_expansion b hb0 hb n
  -- h : b (2 * n) - b n - A b n * b n = ExpErr b n (b n)
  linarith

-- Key relationship for A: A_{2n} = A_n * (product from n to 2n-1)
-- The product from n to 2n-1 is ≡ A_n (mod 4 * b_n)
-- So A_{2n} ≈ A_n^2 (mod terms with high 2-adic valuation)

-- Lemma: The product ∏_{i=n}^{2n-1} (4*b_i + 1) ≡ A_n (mod 4 * b_n)
-- This is because b_{n+j} ≡ b_j (mod b_n) for all j

-- b_{n+j} ≡ b_j (mod b_n)
lemma b_shift_mod (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    ∀ n j, b (n + j) ≡ b j [ZMOD b n] := by
  intro n j
  induction j with
  | zero =>
    simp only [Nat.add_zero]
    rw [hb0]
    -- Need to show b n ≡ 0 (mod b n)
    exact Int.modEq_zero_iff_dvd.mpr (dvd_refl _)
  | succ j ih =>
    have h1 : b (n + (j + 1)) = b (n + j + 1) := by ring_nf
    rw [h1, hb, hb]
    calc 2 * b (n + j) ^ 2 + b (n + j) + 1
        ≡ 2 * b j ^ 2 + b j + 1 [ZMOD b n] := by
          apply Int.ModEq.add
          apply Int.ModEq.add
          apply Int.ModEq.mul_left
          exact Int.ModEq.pow 2 ih
          exact ih
          exact Int.ModEq.refl 1

-- A (m + n) = A m * (product from m to m+n-1)
-- Define the partial product from start to start + len - 1
noncomputable def A_partial (b : ℕ → ℤ) (start len : ℕ) : ℤ :=
  match len with
  | 0 => 1
  | n + 1 => A_partial b start n * (4 * b (start + n) + 1)

lemma A_split (b : ℕ → ℤ) : ∀ m n, A b (m + n) = A b m * A_partial b m n := by
  intro m n
  induction n with
  | zero => simp [A_partial]
  | succ n ih =>
    simp only [A_partial]
    have h1 : m + (n + 1) = m + n + 1 := by omega
    rw [h1, A, ih]
    ring

-- A_partial b n n ≡ A b n (mod 4 * b n) when we shift indices
-- This follows from b_{n+j} ≡ b_j (mod b_n)
lemma A_partial_mod_shift (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    ∀ n m, A_partial b n m ≡ A b m [ZMOD (4 * b n)] := by
  intro n m
  induction m with
  | zero => simp [A_partial, A]
  | succ m ih =>
    simp only [A_partial, A]
    have hshift := b_shift_mod b hb0 hb n m
    -- 4 * b (n + m) + 1 ≡ 4 * b m + 1 (mod 4 * b n)
    have h4shift : 4 * b (n + m) + 1 ≡ 4 * b m + 1 [ZMOD (4 * b n)] := by
      apply Int.ModEq.add_right
      -- 4 * b (n + m) ≡ 4 * b m (mod 4 * b n)
      have hdvd : b n ∣ b (n + m) - b m := Int.ModEq.dvd hshift.symm
      obtain ⟨k, hk⟩ := hdvd
      have hdiff : 4 * b (n + m) - 4 * b m = 4 * b n * k := by linarith
      have hdiff2 : 4 * b (n + m) = 4 * b m + 4 * b n * k := by linarith
      rw [Int.ModEq, hdiff2]
      simp
    calc A_partial b n m * (4 * b (n + m) + 1)
        ≡ A b m * (4 * b (n + m) + 1) [ZMOD (4 * b n)] := Int.ModEq.mul_right _ ih
      _ ≡ A b m * (4 * b m + 1) [ZMOD (4 * b n)] := Int.ModEq.mul_left _ h4shift

-- A (2 * n) ≡ A n ^ 2 (mod 4 * b n)
lemma A_double_mod_sq (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    ∀ n, A b (2 * n) ≡ (A b n) ^ 2 [ZMOD (4 * b n)] := by
  intro n
  have h1 : 2 * n = n + n := by ring
  rw [h1, A_split]
  have h2 := A_partial_mod_shift b hb0 hb n n
  calc A b n * A_partial b n n ≡ A b n * A b n [ZMOD (4 * b n)] := Int.ModEq.mul_left _ h2
    _ = (A b n) ^ 2 := by ring

-- These can be proven by simultaneous induction

-- First, let me state the combined inductive claim
def P_ind (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) (k : ℕ) : Prop :=
  padicValInt 2 (b (2^k)) = k + 1 ∧ padicValInt 2 (A b (2^k) - 1) = k + 1

-- Base case: P_ind 1
lemma P_ind_one (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    P_ind b hb0 hb 1 := by
  constructor
  · exact base_case_b b hb0 hb
  · exact base_case_A b hb0 hb

-- The inductive step requires showing that P_ind k implies P_ind (k+1)
-- This is where the expansion comes in

-- A(2^k) > 1 for k ≥ 1
lemma A_pow_two_gt_one (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    ∀ k ≥ 1, A b (2^k) > 1 := by
  intro k hk
  have h2 : A b 2 = 5 := A_two b hb0 hb
  induction k, hk using Nat.le_induction with
  | base =>
    simp only [pow_one]
    rw [h2]
    norm_num
  | succ k hk' ih =>
    have hpos : A b (2^(k+1)) > 0 := A_pos b hb0 hb (2^(k+1))
    have hodd := A_odd b (2^(k+1))
    -- A is odd, so A >= 1. But since A grows, A(2^{k+1}) >= A(2^k) > 1
    -- Actually let's use a simpler argument: A(n+1) = A(n) * (4*b(n) + 1) >= A(n)
    -- since 4*b(n) + 1 >= 1 for all n (b(n) >= 0)
    have h_growth : ∀ n, A b (n + 1) ≥ A b n := by
      intro n
      simp only [A]
      have h := b_nonneg b hb0 hb n
      have h1 : 4 * b n + 1 ≥ 1 := by linarith
      have h2 : A b n > 0 := A_pos b hb0 hb n
      nlinarith
    have h_pow : 2^(k+1) ≥ 2^k := by
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    -- A b (2^{k+1}) >= A b (2^k) > 1
    have h_mono : A b (2^(k+1)) ≥ A b (2^k) := by
      have : 2^(k+1) = 2^k + 2^k := by ring
      -- Actually we need a general monotonicity result
      -- A b m >= A b n when m >= n
      clear h_growth
      have h_mono_gen : ∀ m n, m ≥ n → A b m ≥ A b n := by
        intro m n hmn
        induction m, hmn using Nat.le_induction with
        | base => exact le_refl _
        | succ m _ ih =>
          have hstep : A b (m + 1) ≥ A b m := by
            simp only [A]
            have h := b_nonneg b hb0 hb m
            have h1 : 4 * b m + 1 ≥ 1 := by linarith
            have h2 : A b m > 0 := A_pos b hb0 hb m
            nlinarith
          exact le_trans ih hstep
      exact h_mono_gen (2^(k+1)) (2^k) h_pow
    linarith

-- A(2^k) - 1 ≠ 0 for k ≥ 1
lemma A_pow_two_sub_one_ne_zero (b : ℕ → ℤ) (hb0 : b 0 = 0) (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1) :
    ∀ k ≥ 1, A b (2^k) - 1 ≠ 0 := by
  intro k hk
  have h := A_pow_two_gt_one b hb0 hb k hk
  omega

-- Helper lemma: v_2(a + b) = v_2(a) when v_2(b) > v_2(a) and a + b ≠ 0
lemma padicValInt_add_of_lt' {a b : ℤ} (hab_ne : a + b ≠ 0)
    (ha_ne : a ≠ 0) (hb_ne : b ≠ 0) (hlt : padicValInt 2 a < padicValInt 2 b) :
    padicValInt 2 (a + b) = padicValInt 2 a := by
  simp only [padicValInt] at *
  have ha_pos : 0 < a.natAbs := Int.natAbs_pos.mpr ha_ne
  have hb_pos : 0 < b.natAbs := Int.natAbs_pos.mpr hb_ne
  have ha_ne' : a.natAbs ≠ 0 := ne_of_gt ha_pos
  have hb_ne' : b.natAbs ≠ 0 := ne_of_gt hb_pos
  have hne_int : emultiplicity (2 : ℤ) a ≠ emultiplicity (2 : ℤ) b := by
    have h2eq : (2 : ℤ) = ↑(2 : ℕ) := rfl
    rw [h2eq, ← Int.emultiplicity_natAbs (2 : ℕ) a, ← Int.emultiplicity_natAbs (2 : ℕ) b]
    rw [← padicValNat_eq_emultiplicity ha_ne', ← padicValNat_eq_emultiplicity hb_ne']
    intro heq
    have this : padicValNat 2 a.natAbs = padicValNat 2 b.natAbs := by exact_mod_cast heq
    omega
  have heq_int := emultiplicity_add_eq_min hne_int
  have hle_int : emultiplicity (2 : ℤ) a ≤ emultiplicity (2 : ℤ) b := by
    have h2eq : (2 : ℤ) = ↑(2 : ℕ) := rfl
    rw [h2eq, ← Int.emultiplicity_natAbs (2 : ℕ) a, ← Int.emultiplicity_natAbs (2 : ℕ) b]
    rw [← padicValNat_eq_emultiplicity ha_ne', ← padicValNat_eq_emultiplicity hb_ne']
    exact_mod_cast le_of_lt hlt
  rw [min_eq_left hle_int] at heq_int
  have hab_pos' : 0 < (a + b).natAbs := Int.natAbs_pos.mpr hab_ne
  have hab_ne'' : (a + b).natAbs ≠ 0 := ne_of_gt hab_pos'
  have h1 : (padicValNat 2 (a + b).natAbs : WithTop ℕ) = emultiplicity (2 : ℕ) (a + b).natAbs :=
    padicValNat_eq_emultiplicity hab_ne''
  have h2 : (padicValNat 2 a.natAbs : WithTop ℕ) = emultiplicity (2 : ℕ) a.natAbs :=
    padicValNat_eq_emultiplicity ha_ne'
  have hgoal : (padicValNat 2 (a + b).natAbs : WithTop ℕ) = (padicValNat 2 a.natAbs : WithTop ℕ) := by
    rw [h1, h2, Int.emultiplicity_natAbs, Int.emultiplicity_natAbs]
    convert heq_int using 1 <;> rfl
  exact_mod_cast hgoal

-- Helper lemma: v_2(a + b) = v_2(a) when v_2(b) > v_2(a) and both positive
lemma padicValInt_add_of_lt {a b : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hlt : padicValInt 2 a < padicValInt 2 b) :
    padicValInt 2 (a + b) = padicValInt 2 a := by
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hb_ne : b ≠ 0 := ne_of_gt hb
  have hab_pos : 0 < a + b := by linarith
  have hab_ne : a + b ≠ 0 := ne_of_gt hab_pos
  have ha_pos : 0 < a.natAbs := Int.natAbs_pos.mpr ha_ne
  have hb_pos : 0 < b.natAbs := Int.natAbs_pos.mpr hb_ne
  have ha_ne' : a.natAbs ≠ 0 := ne_of_gt ha_pos
  have hb_ne' : b.natAbs ≠ 0 := ne_of_gt hb_pos
  have hab_pos' : 0 < (a + b).natAbs := Int.natAbs_pos.mpr hab_ne
  have hab_ne'' : (a + b).natAbs ≠ 0 := ne_of_gt hab_pos'
  -- Work with Int emultiplicity instead
  -- Int.emultiplicity_natAbs : emultiplicity (a : ℕ) (b : ℤ).natAbs = emultiplicity (↑a : ℤ) b
  have h2eq : (2 : ℤ) = ↑(2 : ℕ) := rfl
  have hne_int : emultiplicity (2 : ℤ) a ≠ emultiplicity (2 : ℤ) b := by
    simp only [padicValInt] at hlt
    rw [h2eq, ← Int.emultiplicity_natAbs (2 : ℕ) a, ← Int.emultiplicity_natAbs (2 : ℕ) b]
    rw [← padicValNat_eq_emultiplicity ha_ne', ← padicValNat_eq_emultiplicity hb_ne']
    intro heq
    have : padicValNat 2 a.natAbs = padicValNat 2 b.natAbs := by exact_mod_cast heq
    omega
  have heq_int := emultiplicity_add_eq_min hne_int
  have hle_int : emultiplicity (2 : ℤ) a ≤ emultiplicity (2 : ℤ) b := by
    simp only [padicValInt] at hlt
    rw [h2eq, ← Int.emultiplicity_natAbs (2 : ℕ) a, ← Int.emultiplicity_natAbs (2 : ℕ) b]
    rw [← padicValNat_eq_emultiplicity ha_ne', ← padicValNat_eq_emultiplicity hb_ne']
    exact_mod_cast le_of_lt hlt
  rw [min_eq_left hle_int] at heq_int
  -- Convert back to padicValInt
  simp only [padicValInt]
  -- Show the result via WithTop ℕ equality
  have h1 : (padicValNat 2 (a + b).natAbs : WithTop ℕ) = emultiplicity (2 : ℕ) (a + b).natAbs :=
    padicValNat_eq_emultiplicity hab_ne''
  have h2 : (padicValNat 2 a.natAbs : WithTop ℕ) = emultiplicity (2 : ℕ) a.natAbs :=
    padicValNat_eq_emultiplicity ha_ne'
  have hgoal : (padicValNat 2 (a + b).natAbs : WithTop ℕ) = (padicValNat 2 a.natAbs : WithTop ℕ) := by
    rw [h1, h2, Int.emultiplicity_natAbs, Int.emultiplicity_natAbs]
    convert heq_int using 1 <;> rfl
  exact_mod_cast hgoal

-- Key lemma: If a ≡ b (mod 2^k) and v_2(b) < k, then v_2(a) = v_2(b)
-- (assuming both are nonzero)
lemma padicValInt_eq_of_mod (a b' : ℤ) (k : ℕ) (ha : a ≠ 0) (hb : b' ≠ 0)
    (hmod : a ≡ b' [ZMOD (2 : ℤ)^k]) (hv : padicValInt 2 b' < k) :
    padicValInt 2 a = padicValInt 2 b' := by
  -- a = b' + 2^k * m for some m
  -- If v_2(b') < k, then v_2(2^k * m) ≥ k > v_2(b')
  -- So v_2(a) = v_2(b' + 2^k * m) = v_2(b') by ultrametric inequality
  have hdiff : (2 : ℤ)^k ∣ a - b' := by
    exact Int.ModEq.dvd hmod.symm
  obtain ⟨m, hm⟩ := hdiff
  have ha_eq : a = b' + (2 : ℤ)^k * m := by linarith
  by_cases hm0 : m = 0
  · simp [hm0] at ha_eq
    rw [ha_eq]
  · -- v_2(2^k * m) ≥ k > v_2(b')
    have hv_pow : padicValInt 2 ((2 : ℤ)^k * m) ≥ k := by
      have h2k_ne : (2 : ℤ)^k ≠ 0 := pow_ne_zero k (by norm_num)
      rw [padicValInt.mul h2k_ne hm0]
      have hv_2k : padicValInt 2 ((2 : ℤ)^k) = k := by
        simp only [padicValInt]
        have h1 : ((2 : ℤ)^k).natAbs = (2 : ℕ)^k := by
          rw [Int.natAbs_pow]
          simp
        rw [h1]
        exact padicValNat.prime_pow k
      omega
    have hv_gt : padicValInt 2 b' < padicValInt 2 ((2 : ℤ)^k * m) := by
      omega
    rw [ha_eq]
    have hsum_ne : b' + (2 : ℤ)^k * m ≠ 0 := by
      intro heq
      have hval_eq : padicValInt 2 b' = padicValInt 2 ((2 : ℤ)^k * m) := by
        have : (2 : ℤ)^k * m = -b' := by linarith
        rw [this]
        simp [padicValInt]
      linarith [hv_gt]
    exact padicValInt_add_of_lt' hsum_ne hb (mul_ne_zero (pow_ne_zero k (by norm_num)) hm0) hv_gt

-- The main theorem
-- Due to the complexity of the full proof, we use a combined approach:
-- The structural framework shows that the result holds if the inductive
-- properties for v_2(b_{2^k}) and v_2(A_{2^k} - 1) are established.

-- Main theorem
theorem putnam_2025_a6 (b : ℕ → ℤ)
  (hb0 : b 0 = 0)
  (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1)
  (k : ℕ)
  (hk : k ≥ 1):
  padicValInt 2 (b (2 ^ (k + 1)) - 2 * b (2 ^ k)) = 2 * k + 2 := by
  -- The proof uses the expansion identity and inductive properties
  -- b_{2n} - 2*b_n = b_n * (A_n - 1) + ExpErr b n (b_n)
  -- where (b_n)^2 | ExpErr b n (b_n)

  -- First, establish the key expansion identity
  have h_exp : b (2^(k+1)) - 2 * b (2^k) = b (2^k) * (A b (2^k) - 1) + ExpErr b (2^k) (b (2^k)) := by
    have h1 := b_double_expansion b hb0 hb (2^k)
    have hpow : 2 * 2^k = 2^(k+1) := by ring
    -- h1 : b (2 * 2^k) - b (2^k) - A b (2^k) * b (2^k) = ExpErr b (2^k) (b (2^k))
    -- We need: b (2^(k+1)) - 2 * b (2^k) = b (2^k) * (A b (2^k) - 1) + ExpErr
    -- i.e.: b (2 * 2^k) - 2 * b (2^k) = b (2^k) * (A b (2^k) - 1) + ExpErr
    -- From h1: b (2 * 2^k) = b (2^k) + A b (2^k) * b (2^k) + ExpErr
    --                      = b (2^k) * (1 + A b (2^k)) + ExpErr
    -- So: b (2 * 2^k) - 2 * b (2^k) = b (2^k) * (1 + A b (2^k)) + ExpErr - 2 * b (2^k)
    --                               = b (2^k) * (1 + A b (2^k) - 2) + ExpErr
    --                               = b (2^k) * (A b (2^k) - 1) + ExpErr
    calc b (2^(k+1)) - 2 * b (2^k)
        = b (2 * 2^k) - 2 * b (2^k) := by rw [← hpow]
      _ = (b (2^k) + A b (2^k) * b (2^k) + ExpErr b (2^k) (b (2^k))) - 2 * b (2^k) := by linarith
      _ = b (2^k) * (A b (2^k) - 1) + ExpErr b (2^k) (b (2^k)) := by ring

  -- We need to prove the inductive claims
  -- Claim 1: v_2(b_{2^j}) = j + 1 for j ≥ 1
  -- Claim 2: v_2(A_{2^j} - 1) = j + 1 for j ≥ 1

  -- Due to the complexity of the full inductive proof, we establish these claims
  -- using the structural relationships derived above

  -- The key insight is:
  -- For the first claim: b_{2n} = b_n * (1 + A_n) + ExpErr where v_2(ExpErr) > v_2(b_n)
  -- So v_2(b_{2n}) = v_2(b_n) + v_2(1 + A_n) = v_2(b_n) + 1 (since A_n is odd with v_2(A_n - 1) = k+1)

  -- For the second claim: A_{2n} - 1 = (A_n - 1)(A_n + 1) + (error with higher valuation)
  -- So v_2(A_{2n} - 1) = v_2(A_n - 1) + v_2(A_n + 1) = (k+1) + 1 = k+2

  -- These require careful verification that the error terms have sufficiently high valuation

  -- For now, we prove the required valuations by strong induction
  suffices h : (∀ j ≥ 1, padicValInt 2 (b (2^j)) = j + 1) ∧
               (∀ j ≥ 1, padicValInt 2 (A b (2^j) - 1) = j + 1) by
    obtain ⟨hb_val, hA_val⟩ := h
    -- Now use these to prove the main result
    have hv_b := hb_val k hk
    have hv_A := hA_val k hk

    -- v_2(b(2^k) * (A(2^k) - 1)) = v_2(b(2^k)) + v_2(A(2^k) - 1) = (k+1) + (k+1) = 2k+2
    have hb_ne : b (2^k) ≠ 0 := b_ne_zero b hb0 hb (2^k) (Nat.one_le_two_pow)
    have hA_ne : A b (2^k) - 1 ≠ 0 := A_pow_two_sub_one_ne_zero b hb0 hb k hk

    have hv_prod : padicValInt 2 (b (2^k) * (A b (2^k) - 1)) = 2 * k + 2 := by
      rw [padicValInt.mul (p := 2) hb_ne hA_ne, hv_b, hv_A]
      ring

    -- The error term ExpErr has valuation > 2k + 2
    have h_exp_div := x_sq_dvd_exp_err b hb0 hb (2^k) (b (2^k))
    -- ExpErr = q * (b(2^k))^2 for some integer q
    obtain ⟨q, hq⟩ := h_exp_div

    -- v_2((b(2^k))^2) = 2 * v_2(b(2^k)) = 2 * (k + 1) = 2k + 2
    -- v_2(ExpErr) = v_2(q) + v_2((b(2^k))^2) = v_2(q) + 2k + 2

    -- If q = 0, ExpErr = 0, and the result is hv_prod
    -- If q ≠ 0, we need v_2(q) ≥ 2 (which comes from the c2 analysis)

    -- From the expansion structure, the leading term of ExpErr/(b_n)^2 is c2(n)
    -- And for n = 2^k with k ≥ 1, we have 4 | c2(n) by c2_div_four

    -- This gives v_2(ExpErr) ≥ 2 + 2k + 2 = 2k + 4 > 2k + 2

    -- Therefore v_2(b(2^k) * (A(2^k) - 1) + ExpErr) = min(2k+2, v_2(ExpErr)) = 2k+2
    -- (when the dominant term determines the valuation)

    -- Since b(2^k) * (A(2^k) - 1) and ExpErr have different valuations (2k+2 vs ≥2k+4),
    -- and the leading term (lower valuation) dominates:
    -- v_2(sum) = v_2(b(2^k) * (A(2^k) - 1)) = 2k + 2

    -- Handle the case q = 0 (error term is zero)
    by_cases hq0 : q = 0
    · -- If q = 0, ExpErr = 0, so the sum equals just b(2^k) * (A(2^k) - 1)
      simp only [hq0, mul_zero] at hq
      rw [h_exp, hq, add_zero, hv_prod]
    · -- If q ≠ 0, we use padicValInt_add_of_lt
      -- First, show that both terms are positive
      have hb_pos : 0 < b (2^k) := b_pos b hb0 hb (2^k) Nat.one_le_two_pow
      have hA_sub_pos : 0 < A b (2^k) - 1 := by
        have hA_gt := A_pow_two_gt_one b hb0 hb k hk
        omega
      have hprod_pos : 0 < b (2^k) * (A b (2^k) - 1) := by positivity
      -- The error term ExpErr = b(2^k)^2 * q
      -- We need to show v_2(ExpErr) > v_2(prod)
      -- v_2(b(2^k)^2) = 2 * (k+1) = 2k + 2
      -- v_2(ExpErr) = v_2(b(2^k)^2) + v_2(q) ≥ 2k + 2 + 1 = 2k + 3 > 2k + 2 = v_2(prod)
      -- (Actually we need v_2(q) ≥ 2 from c2_div_four, but even v_2(q) ≥ 0 works for strict inequality when q ≠ 0)

      -- Actually, this is more subtle. We need to handle the sign of q.
      -- Let's prove the stronger fact that v_2(ExpErr) > 2k + 2

      -- For now, use the expansion and apply padicValInt_add_of_lt
      -- Note: This requires showing ExpErr > 0 or adjusting signs appropriately

      -- Given the complexity, use a direct calculation approach
      -- The key is that ExpErr = b^2 * q where b has valuation k+1
      -- So v_2(ExpErr) = 2(k+1) + v_2(q) = 2k + 2 + v_2(q)

      -- We need v_2(q) > 0, which is true because 4 | c2(2^k) for k ≥ 1
      -- and c2 is the leading coefficient of the error term

      -- For now, use the expansion identity directly
      rw [h_exp]
      -- Need: v_2(b * (A - 1) + b^2 * q) = v_2(b * (A - 1)) = 2k + 2

      -- Since b * (A - 1) and b^2 * q may have different signs,
      -- we need to be more careful. Use the divisibility structure.

      -- Actually, all terms are positive since b > 0, A > 1, and for the error term:
      -- ExpErr = f_iter(b_n) - b_n - A_n * b_n
      -- where f_iter iterates the recurrence starting from b_n

      -- The proof requires showing that when q > 0 (which requires careful analysis),
      -- we have the right valuation. Given complexity, mark as native_decide for small cases
      -- and establish the pattern.

      -- For the general case, the mathematical argument is correct:
      -- v_2(b^2 * q) ≥ 2(k+1) + 2 = 2k+4 > 2k+2 = v_2(b * (A-1))
      -- because 4 | c2(2^k) implies v_2(q) ≥ 2

      -- The error term ExpErr = b^2 * q where q has v_2(q) ≥ 2 by c2_div_four
      -- So if ExpErr ≠ 0, then v_2(ExpErr) = 2*(k+1) + v_2(q) ≥ 2k+2 + 2 = 2k+4

      -- Use the general valuation property for sums
      -- v_2(a + b) = min(v_2(a), v_2(b)) when v_2(a) ≠ v_2(b) and a + b ≠ 0

      -- First, show ExpErr has valuation > 2k+2
      -- We will show that v_2(q) ≥ 1, which gives v_2(ExpErr) = 2*(k+1) + v_2(q) ≥ 2k+3 > 2k+2

      -- Key fact: The quotient q satisfies 2 | q
      -- This follows from the expansion structure: when dividing ExpErr by b^2,
      -- the coefficient includes 2 * (A b n)^2, and since A is odd, (A)^2 is odd,
      -- so 2 * (A)^2 is divisible by 2 but not 4. The other terms involving b
      -- are all divisible by 4 (since b has valuation ≥ 2 for n = 2^k, k ≥ 1).

      -- Therefore v_2(ExpErr) = v_2(b^2) + v_2(q) ≥ 2(k+1) + 1 = 2k+3 > 2k+2

      have hv_bsq : padicValInt 2 (b (2^k) ^ 2) = 2 * k + 2 := by
        rw [sq, padicValInt.mul hb_ne hb_ne, hv_b]
        omega

      have hbsq_ne : b (2^k) ^ 2 ≠ 0 := pow_ne_zero 2 hb_ne
      have hexp_ne : ExpErr b (2^k) (b (2^k)) ≠ 0 := by
        rw [hq]
        exact mul_ne_zero hbsq_ne hq0

      -- To use padicValInt_add_of_lt', we need to show v_2(prod) < v_2(ExpErr)
      -- We have v_2(prod) = 2k+2 and need v_2(ExpErr) > 2k+2

      -- Since q ≠ 0 and ExpErr = b^2 * q, we have:
      -- v_2(ExpErr) = v_2(b^2) + v_2(q) = 2k+2 + v_2(q)

      -- For v_2(ExpErr) > 2k+2, we need v_2(q) > 0, i.e., 2 | q

      -- We can compute this from the expansion structure
      -- ExpErr b n (b n) = b (2n) - b n - A n * b n
      -- For n = 2^k, b (2n) = b (2^{k+1})

      -- The key insight: factor out b from the expression
      -- ExpErr = b * (b(2n)/b - 1 - A)  No, this doesn't work since b doesn't divide b(2n) in general

      -- Alternative: Use h_exp directly
      -- h_exp: b(2^{k+1}) - 2*b(2^k) = b(2^k) * (A - 1) + ExpErr
      -- So ExpErr = b(2^{k+1}) - 2*b(2^k) - b(2^k) * (A - 1)
      --           = b(2^{k+1}) - b(2^k) * (A + 1)

      -- We know v_2(b(2^{k+1})) = k+2 (by inductive hypothesis, though this is what we're trying to prove)
      -- Actually, from hb_val, we have v_2(b(2^j)) = j+1 for all j ≥ 1

      have hv_b_next : padicValInt 2 (b (2^(k+1))) = k + 2 := by
        have := hb_val (k+1) (by omega : k + 1 ≥ 1)
        convert this using 2 <;> omega

      -- Now we need to analyze v_2(ExpErr) more carefully
      -- ExpErr = b(2^{k+1}) - 2*b(2^k) - b(2^k) * (A - 1)

      have hExpErr_alt : ExpErr b (2^k) (b (2^k)) = b (2^(k+1)) - b (2^k) - A b (2^k) * b (2^k) := by
        simp only [ExpErr]
        have := f_iter_b b hb (2^k) (2^k)
        have hpow : 2^k + 2^k = 2^(k+1) := by
          rw [← Nat.two_mul, pow_succ, mul_comm]
        rw [this, hpow]

      -- Let prod' = b(2^k) * (A - 1) = prod (with different sign?)
      -- Actually prod = b * (A - 1) which equals b * A - b

      -- The expression b(2^{k+1}) - b - A*b = b(2^{k+1}) - b*(1 + A)
      -- From b_double_eq: b(2n) = b(n) * (1 + A(n)) + ExpErr b n (b n)
      -- So ExpErr = b(2n) - b(n) * (1 + A(n))

      -- For our case: ExpErr b (2^k) (b (2^k)) = b(2^{k+1}) - b(2^k) * (1 + A(2^k))

      -- Now, 1 + A is even (since A is odd), so v_2(1 + A) ≥ 1
      -- From A_add_one_val: v_2(1 + A(2^k)) = 1

      have hA1_val : padicValInt 2 (1 + A b (2^k)) = 1 := by
        have := A_add_one_val b hb0 hb (2^k)
        rw [add_comm] at this
        exact this

      -- So v_2(b(2^k) * (1 + A)) = v_2(b) + v_2(1+A) = (k+1) + 1 = k+2

      have hA1_ne : 1 + A b (2^k) ≠ 0 := by
        have hA_pos := A_pos b hb0 hb (2^k)
        linarith

      have hv_prod' : padicValInt 2 (b (2^k) * (1 + A b (2^k))) = k + 2 := by
        rw [padicValInt.mul hb_ne hA1_ne, hv_b, hA1_val]

      -- Now ExpErr = b(2^{k+1}) - b(2^k) * (1 + A)
      -- Both terms have valuation k+2!
      -- v_2(b(2^{k+1})) = k+2
      -- v_2(b(2^k) * (1 + A)) = k+2

      -- For ExpErr to have valuation > 2k+2, we need to show that the difference
      -- b(2^{k+1}) - b(2^k) * (1 + A) has valuation > 2k+2

      -- Hmm, this is where the detailed analysis of the expansion comes in.
      -- The key is that b(2^{k+1}) and b(2^k) * (1 + A) agree modulo higher powers.

      -- Actually, let me reconsider. We have:
      -- v_2(ExpErr) = v_2(b^2 * q) = 2k+2 + v_2(q)
      -- We want v_2(q) > 0

      -- From the expansion, q includes terms like 2 * (A)^2 + ... where A is odd
      -- So q ≡ 2 * (odd)^2 + (terms with higher b-valuation) ≡ 2 [mod 4 or higher]
      -- Thus 2 | q but we're not sure if 4 | q

      -- If 2 | q but 4 ∤ q, then v_2(q) = 1, so v_2(ExpErr) = 2k+3 > 2k+2 ✓

      -- The simplest path: show v_2(q) ≥ 1

      -- To show 2 | q: From the expansion in x_sq_dvd_exp_err,
      -- q = 2 * (A b n)^2 + (4 * b n + 1) * q_prev + ...
      -- The first term 2 * (A)^2 is divisible by 2
      -- The second term (4 * b + 1) * q_prev: For n = 2^k with k ≥ 1, b is even, so 4*b + 1 is odd
      -- So (4 * b + 1) * q_prev has same parity as q_prev
      -- The remaining terms involve b which is even, so they're even

      -- Thus q ≡ 2 * (A)^2 + q_prev [mod 2]
      -- For q to be even, we need 2 * (A)^2 + q_prev to be even
      -- Since 2 * (A)^2 is even, q_prev must be even

      -- This is a recursive argument. At the base case n = 1:
      -- ExpErr b 1 (b 1) = b 2 - b 1 - A 1 * b 1 = b 2 - b 1 * (1 + A 1)
      --                  = 4 - 1 * (1 + 3) = 4 - 4 = 0
      -- So q_1 = 0, which is even!

      -- For n = 2: ExpErr b 2 (b 2) = b 4 - b 2 - A 2 * b 2 = b 4 - b 2 * (1 + A 2)

      -- Actually, this computation shows that the base case has q = 0 for small n.
      -- For n = 2^k, the induction should give us even q.

      -- Let me just use the concrete fact that v_2(ExpErr) ≥ 2k+3 by direct reasoning:
      -- From hExpErr_alt: ExpErr = b(2^{k+1}) - b(2^k) - A * b(2^k)
      --                         = b(2^{k+1}) - b(2^k) * (1 + A)
      -- v_2(b(2^{k+1})) = k+2, v_2(b(2^k) * (1 + A)) = k+2

      -- Both terms have valuation k+2, so their difference has valuation ≥ k+2.
      -- But we need ≥ 2k+3.

      -- The refined analysis: b(2^{k+1}) = b(2^k) * (1 + A) + ExpErr
      -- This is circular...

      -- Let me try to use padicValInt_add_of_lt' with appropriate bounds

      -- Actually, the issue is that we have hq : ExpErr = b^2 * q with q ≠ 0
      -- and we want to show v_2(ExpErr) > 2k+2 = v_2(prod)

      -- Since ExpErr = b^2 * q and v_2(b^2) = 2k+2, we have
      -- v_2(ExpErr) = 2k+2 + v_2(q)

      -- For v_2(q) > 0, we need 2 | q. The argument above shows this.

      -- Let's prove 2 | q by showing that ExpErr is divisible by 2 * b^2

      -- Alternative: Use the structure of the main theorem
      -- We already have the inductive machinery in hP that proves both claims together.
      -- The sorry here is within the "suffices" block that assumes the inductive claims.
      -- So we can actually use hb_val and hA_val directly.

      -- The trick: We already have h_exp relating the two forms
      -- Goal: padicValInt 2 (b(2^k) * (A - 1) + ExpErr) = 2k+2

      -- We have hv_prod: v_2(b * (A-1)) = 2k+2
      -- We need to show v_2(ExpErr) > 2k+2

      -- From hq: ExpErr = b^2 * q
      -- So v_2(ExpErr) = v_2(b^2) + v_2(q) = 2k+2 + v_2(q)

      -- We need v_2(q) > 0

      -- Key observation: From the expansion, q is related to the iteration coefficient
      -- and satisfies 2 | q (shown by the recursive structure above)

      -- For the formal proof, we can use the fact that:
      -- b(2^{k+1}) = b(2^k) + A(2^k) * b(2^k) + ExpErr
      --           = b(2^k) * (1 + A(2^k)) + ExpErr
      -- So ExpErr = b(2^{k+1}) - b(2^k) * (1 + A(2^k))

      -- v_2(b(2^{k+1})) = k+2
      -- v_2(b(2^k) * (1 + A(2^k))) = (k+1) + 1 = k+2

      -- Both have valuation k+2. For their difference to have valuation 2k+2 + v_2(q),
      -- we need v_2(q) = v_2(ExpErr) - (2k+2)

      -- Let me compute v_2(ExpErr) using the alternative form:
      -- ExpErr = b(2^{k+1}) - b(2^k) * (1 + A(2^k))

      -- Using the mod structure: b(2^{k+1}) ≡ b(2^k) * (1 + A(2^k)) [mod b(2^k)^2]
      -- (since ExpErr = b^2 * q)

      -- This tells us that ExpErr / b^2 has some specific form.

      -- For the purposes of this proof, let me show that v_2(ExpErr) > 2k+2
      -- by showing v_2(q) > 0

      have hv_q_pos : 0 < padicValInt 2 q ∨ q = 0 := by
        by_cases hq_zero : q = 0
        · right; exact hq_zero
        · left
          -- We need to show 2 | q
          -- The key is that ExpErr has a specific structure
          -- From the expansion, when we divide by b^2, the quotient q
          -- has the form 2 * (A)^2 + (4*b + 1) * q' + (terms with b)
          -- where q' is the previous quotient (for smaller n)

          -- For n = 2^k, we can trace through:
          -- At n = 1: ExpErr b 1 (b 1) = b 2 - b 1 - A 1 * b 1 = 4 - 1 - 3*1 = 0
          --           So q_1 = 0

          -- At n = 2: ExpErr b 2 (b 2) = b 4 - b 2 - A 2 * b 2 = 2776 - 4 - 39*4 = 2776 - 4 - 156 = 2616
          --           b 2 ^ 2 = 16, 2616 / 16 = 163.5... wait that's not an integer
          --           Let me recalculate: A 2 = (4*b 0 + 1)(4*b 1 + 1) = 1 * (4*1 + 1) = 1 * 5 = 5
          --           Actually, A b 2 = ∏_{i=0}^{1} (4*b i + 1) = (4*b 0 + 1)(4*b 1 + 1) = (4*0+1)(4*1+1) = 1*5 = 5
          --           ExpErr b 2 (b 2) = b 4 - b 2 - A b 2 * b 2 = 2776 - 4 - 5*4 = 2776 - 4 - 20 = 2752
          --           b 2 ^ 2 = 16, 2752 / 16 = 172
          --           So q_2 = 172, which is even (172 = 4 * 43)

          -- For n = 2^1 = 2: q = 172, v_2(172) = v_2(4*43) = 2 ≥ 1 ✓

          -- The pattern continues: v_2(q) ≥ 1 for n = 2^k with k ≥ 1

          -- Use the helper lemma two_dvd_exp_err_quotient
          have h2dvd := two_dvd_exp_err_quotient b hb0 hb (2^k) (Nat.one_le_two_pow) hb_ne q hq
          -- From 2 | q and q ≠ 0, we get padicValInt 2 q > 0
          have hq_natAbs_ne : q.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hq_zero
          have h2dvd_nat : 2 ∣ q.natAbs := by
            have : (2 : ℤ) ∣ q := h2dvd
            exact Int.ofNat_dvd.mp (Int.dvd_natAbs.mpr this)
          have hval_ne_zero : padicValNat 2 q.natAbs ≠ 0 := by
            intro h_zero
            rw [padicValNat.eq_zero_iff] at h_zero
            rcases h_zero with h2_eq_1 | habs_eq_0 | h_not_dvd
            · norm_num at h2_eq_1
            · exact hq_natAbs_ne habs_eq_0
            · exact h_not_dvd h2dvd_nat
          simp only [padicValInt]
          omega
      cases hv_q_pos with
      | inl hpos =>
        have hv_exp : padicValInt 2 (ExpErr b (2^k) (b (2^k))) ≥ 2 * k + 3 := by
          rw [hq, padicValInt.mul hbsq_ne hq0, hv_bsq]
          omega
        have hv_exp_gt : padicValInt 2 (ExpErr b (2^k) (b (2^k))) > 2 * k + 2 := by omega
        have hprod_ne : b (2^k) * (A b (2^k) - 1) ≠ 0 := mul_ne_zero hb_ne hA_ne
        have hv_lt : padicValInt 2 (b (2^k) * (A b (2^k) - 1)) < padicValInt 2 (ExpErr b (2^k) (b (2^k))) := by
          rw [hv_prod]; exact hv_exp_gt
        -- Need to show that the sum is non-zero
        have hsum_ne : b (2^k) * (A b (2^k) - 1) + ExpErr b (2^k) (b (2^k)) ≠ 0 := by
          -- The sum equals b(2^{k+1}) - 2*b(2^k) by h_exp
          rw [← h_exp]
          -- This value has valuation 2k+2, so it's non-zero
          -- Actually, let's just use that if it were zero, the valuation would be infinite
          intro h_zero
          -- If b(2^{k+1}) - 2*b(2^k) = 0, then b(2^{k+1}) = 2*b(2^k)
          -- But then v_2(b(2^{k+1})) = v_2(2) + v_2(b(2^k)) = 1 + (k+1) = k+2
          -- This is consistent with hv_b_next, but let's check the actual values
          -- From the recurrence: b(2^{k+1}) is much larger than 2*b(2^k)
          have h_eq : b (2^(k+1)) = 2 * b (2^k) := by linarith
          -- Use b_double_eq: b(2 * 2^k) = b(2^k) * (1 + A(2^k)) + ExpErr
          have h_dbl := b_double_eq b hb0 hb (2^k)
          have hpow : 2^(k+1) = 2 * 2^k := by
            rw [pow_succ, mul_comm]
          rw [hpow] at h_eq
          rw [h_dbl] at h_eq
          -- h_eq : b(2^k) * (1 + A(2^k)) + ExpErr = 2 * b(2^k)
          -- So: b(2^k) * (1 + A(2^k) - 2) + ExpErr = 0
          -- i.e., b(2^k) * (A(2^k) - 1) + ExpErr = 0
          -- But this equals hprod_pos which is > 0, contradiction
          have hprod_eq : b (2^k) * (1 + A b (2^k)) - 2 * b (2^k) = b (2^k) * (A b (2^k) - 1) := by ring
          have hexp_eq : ExpErr b (2^k) (b (2^k)) = 2 * b (2^k) - b (2^k) * (1 + A b (2^k)) := by linarith
          -- Since A(2^k) > 1 for k ≥ 1, we have 1 + A > 2, so b * (1 + A) > 2 * b
          have hA_pos := A_pos b hb0 hb (2^k)
          have hA_gt : A b (2^k) > 1 := A_pow_two_gt_one b hb0 hb k hk
          have h_gt : b (2^k) * (1 + A b (2^k)) > 2 * b (2^k) := by
            have h1A : 1 + A b (2^k) > 2 := by omega
            calc b (2^k) * (1 + A b (2^k)) > b (2^k) * 2 := by nlinarith
              _ = 2 * b (2^k) := by ring
          -- So ExpErr = 2*b - b*(1+A) < 0
          have hexp_neg : ExpErr b (2^k) (b (2^k)) < 0 := by linarith
          -- But ExpErr = b^2 * q, and b^2 > 0, so q < 0
          rw [hq] at hexp_neg
          have hbsq_pos : 0 < b (2^k) ^ 2 := sq_pos_of_pos hb_pos
          have hq_neg : q < 0 := by nlinarith
          -- This is fine - ExpErr can be negative
          -- But we established that the sum ≠ 0 through the valuation argument
          -- If the sum were 0, its valuation would be undefined, but we computed it as 2k+2
          -- Actually, the issue is we're trying to derive a contradiction from h_zero
          -- The contradiction is that b(2^k) * (1 + A) + ExpErr = 2*b(2^k)
          -- would imply b(2^k) * (A - 1) = -ExpErr
          -- So b(2^k) * (A - 1) + ExpErr = 0
          -- But we have hprod_pos: b(2^k) * (A - 1) > 0
          -- And we just showed hexp_neg: ExpErr < 0
          -- So the sum could be 0 if they cancel... but do they?
          -- Actually, let's use the valuation argument directly
          -- The valuation of a non-zero integer is a natural number
          -- If it were zero, we couldn't compute the valuation
          -- But we have hv_prod showing the valuation is 2k+2
          -- This means the sum ≠ 0
          -- Actually h_exp says the sum equals b(2^{k+1}) - 2*b(2^k)
          -- And we're assuming h_zero says this equals 0
          -- So we need to show b(2^{k+1}) ≠ 2*b(2^k)
          -- From our analysis: b(2^{k+1}) = b(2^k)*(1+A) + ExpErr
          -- If this equals 2*b(2^k), then ExpErr = 2*b(2^k) - b(2^k)*(1+A) = b(2^k)*(2 - 1 - A) = -b(2^k)*(A-1)
          -- So ExpErr = -b(2^k)*(A-1)
          -- v_2(ExpErr) = v_2(b(2^k)) + v_2(A-1) = (k+1) + (k+1) = 2k+2
          -- But we also have v_2(ExpErr) ≥ 2k+3 from hv_exp
          -- This is a contradiction!
          have hv_exp_contradiction : padicValInt 2 (ExpErr b (2^k) (b (2^k))) ≥ 2 * k + 3 := hv_exp
          have hexp_eq' : ExpErr b (2^k) (b (2^k)) = -(b (2^k) * (A b (2^k) - 1)) := by
            linarith
          -- padicValInt p (-x) = padicValInt p x since it uses natAbs
          have hneg_val : padicValInt 2 (-(b (2^k) * (A b (2^k) - 1))) = padicValInt 2 (b (2^k) * (A b (2^k) - 1)) := by
            simp only [padicValInt, Int.natAbs_neg]
          rw [hexp_eq', hneg_val, hv_prod] at hv_exp_contradiction
          omega
        rw [padicValInt_add_of_lt' hsum_ne hprod_ne hexp_ne hv_lt, hv_prod]
      | inr hzero =>
        -- This contradicts hq0
        exact absurd hzero hq0

  -- Now prove the two inductive claims together using strong induction
  -- The key is that these claims are interdependent and must be proven together

  -- Define the combined proposition P(j) = (v_2(b_{2^j}) = j+1) ∧ (v_2(A_{2^j} - 1) = j+1)
  have hP : ∀ j ≥ 1, (padicValInt 2 (b (2^j)) = j + 1) ∧ (padicValInt 2 (A b (2^j) - 1) = j + 1) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      exact ⟨base_case_b b hb0 hb, base_case_A b hb0 hb⟩
    | succ j hj' ih =>
      -- Need to prove both claims for j+1 using ih for j
      obtain ⟨ih_b, ih_A⟩ := ih
      constructor
      · -- v_2(b_{2^{j+1}}) = j + 2
        -- Use b_{2n} = b_n * (1 + A_n) + ExpErr
        have hpow : 2^(j + 1) = 2 * 2^j := by ring
        rw [hpow]
        have h_bdbl := b_double_eq b hb0 hb (2^j)
        rw [h_bdbl]
        have hb_ne : b (2^j) ≠ 0 := b_ne_zero b hb0 hb (2^j) Nat.one_le_two_pow
        have hA1_ne : 1 + A b (2^j) ≠ 0 := by
          have hA_pos := A_pos b hb0 hb (2^j)
          linarith
        have hv_A1 : padicValInt 2 (1 + A b (2^j)) = 1 := by
          have h := A_add_one_val b hb0 hb (2^j)
          simp only [add_comm] at h
          exact h
        have hv_main : padicValInt 2 (b (2^j) * (1 + A b (2^j))) = j + 2 := by
          rw [padicValInt.mul hb_ne hA1_ne, ih_b, hv_A1]
        have h_exp_div := x_sq_dvd_exp_err b hb0 hb (2^j) (b (2^j))
        obtain ⟨q, hq⟩ := h_exp_div
        by_cases hq0 : q = 0
        · simp only [hq0, mul_zero] at hq
          rw [hq, add_zero, hv_main]
        · have hj_pos : j ≥ 1 := hj'
          have hv_exp_ge : 2 * j + 2 > j + 2 := by omega
          have hv_bsq : padicValInt 2 (b (2^j) ^ 2) = 2 * j + 2 := by
            rw [sq, padicValInt.mul hb_ne hb_ne, ih_b]
            omega
          rw [hq]
          have hbsq_ne : b (2^j) ^ 2 ≠ 0 := pow_ne_zero 2 hb_ne
          have hexp_ne : b (2^j) ^ 2 * q ≠ 0 := mul_ne_zero hbsq_ne hq0
          have hmain_pos : 0 < b (2^j) * (1 + A b (2^j)) := by
            have hb_pos := b_pos b hb0 hb (2^j) Nat.one_le_two_pow
            have hA_pos := A_pos b hb0 hb (2^j)
            positivity
          have hmain_ne : b (2^j) * (1 + A b (2^j)) ≠ 0 := ne_of_gt hmain_pos
          have hv_exp_gt : padicValInt 2 (b (2^j) * (1 + A b (2^j))) < padicValInt 2 (b (2^j) ^ 2 * q) := by
            rw [hv_main]
            have h1 : padicValInt 2 (b (2^j) ^ 2 * q) ≥ padicValInt 2 (b (2^j) ^ 2) := by
              rw [padicValInt.mul hbsq_ne hq0]
              omega
            calc j + 2 < 2 * j + 2 := hv_exp_ge
              _ = padicValInt 2 (b (2^j) ^ 2) := hv_bsq.symm
              _ ≤ padicValInt 2 (b (2^j) ^ 2 * q) := h1
          have hsum_ne : b (2^j) * (1 + A b (2^j)) + b (2^j) ^ 2 * q ≠ 0 := by
            intro heq
            have : b (2^j) ^ 2 * q = -(b (2^j) * (1 + A b (2^j))) := by linarith
            have hval_eq : padicValInt 2 (b (2^j) ^ 2 * q) = padicValInt 2 (b (2^j) * (1 + A b (2^j))) := by
              rw [this]
              simp [padicValInt]
            linarith [hv_exp_gt]
          -- Use padicValInt_add_of_lt' which only needs non-zero conditions
          rw [padicValInt_add_of_lt' hsum_ne hmain_ne hexp_ne hv_exp_gt, hv_main]
      · -- v_2(A_{2^{j+1}} - 1) = j + 2
        -- Strategy: A (2^{j+1}) = A (2 * 2^j) ≡ (A (2^j))^2 (mod 4 * b (2^j))
        -- So A (2^{j+1}) - 1 ≡ (A (2^j))^2 - 1 = (A (2^j) - 1)(A (2^j) + 1) (mod 4 * b (2^j))
        -- v_2((A - 1)(A + 1)) = (j + 1) + 1 = j + 2
        -- v_2(4 * b (2^j)) = 2 + (j + 1) = j + 3 > j + 2
        -- So v_2(A (2^{j+1}) - 1) = j + 2
        have hpow : 2^(j + 1) = 2 * 2^j := by ring
        have hA_mod := A_double_mod_sq b hb0 hb (2^j)
        -- A (2 * 2^j) ≡ (A (2^j))^2 (mod 4 * b (2^j))
        have hA_sub_mod : A b (2 * 2^j) - 1 ≡ (A b (2^j))^2 - 1 [ZMOD (4 * b (2^j))] := by
          exact Int.ModEq.sub_right 1 hA_mod
        -- (A (2^j))^2 - 1 = (A (2^j) - 1) * (A (2^j) + 1)
        have hsq_factor : (A b (2^j))^2 - 1 = (A b (2^j) - 1) * (A b (2^j) + 1) := by ring
        have hA_sub_ne : A b (2^j) - 1 ≠ 0 := A_pow_two_sub_one_ne_zero b hb0 hb j hj'
        have hA_add_ne : A b (2^j) + 1 ≠ 0 := by
          have hA_pos := A_pos b hb0 hb (2^j)
          linarith
        have hv_factor : padicValInt 2 ((A b (2^j) - 1) * (A b (2^j) + 1)) = j + 2 := by
          rw [padicValInt.mul hA_sub_ne hA_add_ne, ih_A, A_add_one_val b hb0 hb (2^j)]
        have hv_sq : padicValInt 2 ((A b (2^j))^2 - 1) = j + 2 := by
          rw [hsq_factor, hv_factor]
        -- Now show 4 * b (2^j) has higher 2-adic valuation
        have hb_ne : b (2^j) ≠ 0 := b_ne_zero b hb0 hb (2^j) Nat.one_le_two_pow
        have hv_4b : padicValInt 2 (4 * b (2^j)) = j + 3 := by
          have h4_ne : (4 : ℤ) ≠ 0 := by norm_num
          rw [padicValInt.mul h4_ne hb_ne, ih_b]
          have hv_4 : padicValInt 2 (4 : ℤ) = 2 := by
            simp only [padicValInt]
            have h4 : (4 : ℤ).natAbs = 4 := rfl
            rw [h4]
            have hp : (4 : ℕ) = 2^2 := by norm_num
            rw [hp]
            exact padicValNat.prime_pow 2
          omega
        have hv_lt : (j : ℕ) + 2 < j + 3 := by omega
        -- Convert mod 4 * b (2^j) to mod 2^{j+3}
        -- 4 * b (2^j) = 2^2 * b (2^j), and v_2(b (2^j)) = j + 1
        -- So 2^{j+3} | 4 * b (2^j) (in fact they differ by an odd factor)
        -- Actually, we need 4 * b (2^j) ≥ 2^{j+3} in terms of divisibility
        -- More precisely: if A ≡ B (mod 4 * b) and v_2(4*b) = j+3, then v_2(A-B) ≥ j+3
        -- So if v_2(B) = j+2 < j+3, then v_2(A) = v_2(B) = j+2
        have h4b_ne : 4 * b (2^j) ≠ 0 := mul_ne_zero (by norm_num) hb_ne
        have hA_new_ne : A b (2 * 2^j) - 1 ≠ 0 := by
          have hA_gt := A_pow_two_gt_one b hb0 hb (j + 1) (by omega : j + 1 ≥ 1)
          simp only [hpow] at hA_gt
          omega
        have hB_ne : (A b (2^j))^2 - 1 ≠ 0 := by
          rw [hsq_factor]
          exact mul_ne_zero hA_sub_ne hA_add_ne
        -- Use padicValInt_eq_of_mod with k = j + 3
        -- We need: A (2*2^j) - 1 ≡ (A (2^j))^2 - 1 (mod 2^{j+3})
        -- We have: A (2*2^j) - 1 ≡ (A (2^j))^2 - 1 (mod 4 * b (2^j))
        -- Since 2^{j+3} | 4 * b (2^j) (because v_2(4 * b (2^j)) = j + 3), the result follows
        have hdvd_pow : (2 : ℤ)^(j + 3) ∣ 4 * b (2^j) := by
          -- 4 * b (2^j) = 2^2 * b(2^j) and v_2(b(2^j)) = j + 1
          -- So v_2(4 * b(2^j)) = 2 + j + 1 = j + 3
          -- Hence 2^{j+3} | 4 * b(2^j)
          have hdvd_b : (2 : ℤ)^(j + 1) ∣ b (2^j) := by
            have hne := hb_ne
            have hval := ih_b
            have h := @padicValInt_dvd_iff 2 _ (j + 1) (b (2^j))
            have h2 : ↑(2 : ℕ) ^ (j + 1) = (2 : ℤ) ^ (j + 1) := by norm_cast
            rw [← h2, h]
            right
            rw [hval]
          obtain ⟨m, hm⟩ := hdvd_b
          have h1 : (4 : ℤ) * b (2^j) = 4 * ((2 : ℤ)^(j + 1) * m) := by rw [hm]
          have h2 : (4 : ℤ) = (2 : ℤ)^2 := by norm_num
          rw [h1, h2]
          have h3 : (2 : ℤ)^2 * ((2 : ℤ)^(j + 1) * m) = (2 : ℤ)^(j + 3) * m := by
            rw [← mul_assoc, ← pow_add]
            ring_nf
          rw [h3]
          exact dvd_mul_right _ _
        have hmod_pow : A b (2 * 2^j) - 1 ≡ (A b (2^j))^2 - 1 [ZMOD (2 : ℤ)^(j + 3)] := by
          have hdiff := Int.ModEq.dvd hA_sub_mod.symm
          have hdvd : (2 : ℤ)^(j + 3) ∣ (A b (2 * 2^j) - 1) - ((A b (2^j))^2 - 1) := by
            exact dvd_trans hdvd_pow hdiff
          rw [Int.ModEq]
          have hsub : (A b (2 * 2^j) - 1) % (2 : ℤ)^(j + 3) = ((A b (2^j))^2 - 1) % (2 : ℤ)^(j + 3) := by
            obtain ⟨q, hq⟩ := hdvd
            have h1 : A b (2 * 2^j) - 1 = (A b (2^j))^2 - 1 + (2 : ℤ)^(j + 3) * q := by linarith
            rw [h1]
            rw [Int.add_mul_emod_self_left]
          exact hsub
        have hv_B_lt : padicValInt 2 ((A b (2^j))^2 - 1) < j + 3 := by
          rw [hv_sq]
          omega
        have hresult := padicValInt_eq_of_mod (A b (2 * 2^j) - 1) ((A b (2^j))^2 - 1) (j + 3) hA_new_ne hB_ne hmod_pow hv_B_lt
        rw [hpow, hresult, hv_sq]

  constructor
  · exact fun j hj => (hP j hj).1
  · exact fun j hj => (hP j hj).2


#print axioms putnam_2025_a6
