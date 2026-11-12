# Witness introduction for the IMO 2025 P4 counterexample sequence

| | |
|---|---|
| Kind | instance |
| Move | witness |
| Language | lean |
| Status | draft |
| Source | [seed-prover](../../sources/seed-prover/SOURCE.md) at `38c59cebaf96` |
| Licence | `Apache-2.0` |

## Intent

The theorem proves that any starting value `a0 = 6 * 12^k * n` with `n`
coprime to 10 begins an infinite sequence of positive integers whose successor
is the sum of its three largest proper divisors (the IMO 2025 P4 counterexample
sequence). The proof introduces a closed-form witness for the sequence, then
closes the three conjuncts of the existential each by a single named lemma.

## The decomposition

### parent `imo2025_p4_right`: [`SeedProver/imo2025/IMO2025/P4.lean` lines 3900-3926](https://github.com/ByteDance-Seed/Seed-Prover/blob/38c59cebaf969ac259196eb091757518d5b54c67/SeedProver/imo2025/IMO2025/P4.lean#L3900-L3926) ([local copy](code/SeedProver/imo2025/IMO2025/P4.lean))

```lean
theorem imo2025_p4_right (a0 k n : ℕ)
  (hn : Nat.Coprime n 10)
  (ha0 : a0 = 6 * 12 ^ k * n) :
  ∃ a : ℕ → ℕ, (∀ n : ℕ, a n > 0) ∧ (∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d) ∧ (a 0 = a0)
  /- A \emph{proper divisor} of a positive integer $N$ is a positive divisor of $N$ other than $N$ itself. The infinite sequence $a_1, a_2, \ldots$ consists of positive integers, each of which has at least three proper divisors. For each $n \geqslant 1$, the integer $a_{n+1}$  is the sum of the three **largest** proper divisors of~$a_n$.
  When $a_1$ is $6 * 12^k * m$, where m is coprime to 10. Please prove that a_n exists. -/
  := by
  have h1 : n ≥ 1 := imo2025_p4_right8_h1 a0 k n hn ha0
  have h2 : ∀ m : ℕ, (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) > 0 := imo2025_p4_right8_h2 a0 k n hn ha0 h1
  have h3 : ∀ m : ℕ, (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) > 3 := imo2025_p4_right8_h3 a0 k n hn ha0 h1 h2
  have h4 : ∀ (m : ℕ), ∃ b c d : ℕ, b < c ∧ c < d ∧ d < (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) ∧ b ∣ (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) ∧ c ∣ (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) ∧ d ∣ (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) ∧ (∀ e : ℕ, e < (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) → e ∣ (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) → e ≤ b ∨ e = c ∨ e = d) ∧ (if (m + 1) ≤ k then 6 * 12 ^ (k - (m + 1)) * 13 ^ (m + 1) * n else 6 * 13 ^ k * n) = b + c + d := imo2025_p4_right1_main  a0 k n hn ha0 h1 h2 h3

  use (fun m => if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n)

  constructor
  · -- Prove ∀ n, a n > 0
    intro n
    exact h2 n

  constructor
  · -- Prove ∀ n, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d
    intro n
    exact h4 n

  · -- Prove a 0 = a0
    simp only [ha0]
    <;> aesop
```

### child `imo2025_p4_right8_h1`: [`SeedProver/imo2025/IMO2025/P4.lean` lines 3389-3397](https://github.com/ByteDance-Seed/Seed-Prover/blob/38c59cebaf969ac259196eb091757518d5b54c67/SeedProver/imo2025/IMO2025/P4.lean#L3389-L3397) ([local copy](code/SeedProver/imo2025/IMO2025/P4.lean))

```lean
lemma imo2025_p4_right8_h1 (a0 k n : ℕ)
  (hn : Nat.Coprime n 10)
  (ha0 : a0 = 6 * 12 ^ k * n):
  n ≥ 1 := by
  by_contra h
  have h2 : n = 0 := by omega
  rw [h2] at hn
  norm_num at hn
  <;> contradiction
```

### child `imo2025_p4_right8_h2`: [`SeedProver/imo2025/IMO2025/P4.lean` lines 3400-3435](https://github.com/ByteDance-Seed/Seed-Prover/blob/38c59cebaf969ac259196eb091757518d5b54c67/SeedProver/imo2025/IMO2025/P4.lean#L3400-L3435) ([local copy](code/SeedProver/imo2025/IMO2025/P4.lean))

```lean
lemma imo2025_p4_right8_h2 (a0 k n : ℕ)
  (hn : Nat.Coprime n 10)
  (ha0 : a0 = 6 * 12 ^ k * n)
  (h1 : n ≥ 1):
  ∀ m : ℕ, (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) > 0 := by
  intro m
  by_cases h3 : m ≤ k
  · -- Case m ≤ k
    have h4 : 6 * 12 ^ (k - m) * 13 ^ m * n > 0 := by
      have h5 : n ≥ 1 := h1
      have h6 : 12 ^ (k - m) ≥ 1 := by
        apply Nat.one_le_pow
        <;> norm_num
      have h7 : 13 ^ m ≥ 1 := by
        apply Nat.one_le_pow
        <;> norm_num
      have h8 : 6 * 12 ^ (k - m) * 13 ^ m > 0 := by positivity
      have h9 : 6 * 12 ^ (k - m) * 13 ^ m * n > 0 := by
        have h10 : n > 0 := by linarith
        have h11 : 6 * 12 ^ (k - m) * 13 ^ m > 0 := h8
        positivity
      linarith
    simp [h3]
    <;> linarith
  · -- Case ¬(m ≤ k)
    have h4 : ¬(m ≤ k) := h3
    have h5 : 6 * 13 ^ k * n > 0 := by
      have h6 : n ≥ 1 := h1
      have h7 : 13 ^ k ≥ 1 := by
        apply Nat.one_le_pow
        <;> norm_num
      have h8 : 6 * 13 ^ k > 0 := by positivity
      have h9 : 6 * 13 ^ k * n > 0 := by positivity
      linarith
    simp [h3]
    <;> linarith
```

### child `imo2025_p4_right8_h3`: [`SeedProver/imo2025/IMO2025/P4.lean` lines 3438-3478](https://github.com/ByteDance-Seed/Seed-Prover/blob/38c59cebaf969ac259196eb091757518d5b54c67/SeedProver/imo2025/IMO2025/P4.lean#L3438-L3478) ([local copy](code/SeedProver/imo2025/IMO2025/P4.lean))

```lean
lemma imo2025_p4_right8_h3 (a0 k n : ℕ)
  (hn : Nat.Coprime n 10)
  (ha0 : a0 = 6 * 12 ^ k * n)
  (h1 : n ≥ 1)
  (h2 : ∀ m : ℕ, (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) > 0):
  ∀ m : ℕ, (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) > 3 := by
  intro m
  by_cases h3 : m ≤ k
  · -- Case m ≤ k
    have h5 : m ≤ k := h3
    have h6 : 6 * 12 ^ (k - m) * 13 ^ m * n > 3 := by
      have h7 : n ≥ 1 := h1
      have h102 : 13 ^ m ≥ 1 := by
        apply Nat.one_le_pow
        <;> norm_num
      have h103 : 12 ^ (k - m) ≥ 1 := by
        apply Nat.one_le_pow
        <;> norm_num
      have h104 : 6 * 12 ^ (k - m) * 13 ^ m ≥ 6 * 1 * 1 := by
        have h105 : 12 ^ (k - m) ≥ 1 := h103
        have h106 : 13 ^ m ≥ 1 := h102
        have h107 : 6 * 12 ^ (k - m) ≥ 6 * 1 := by nlinarith
        have h108 : 6 * 12 ^ (k - m) * 13 ^ m ≥ 6 * 1 * 1 := by nlinarith
        linarith
      have h109 : 6 * 12 ^ (k - m) * 13 ^ m * n ≥ 6 * 1 * 1 * 1 := by
        nlinarith
      linarith
    simp [h3]
    <;> linarith
  · -- Case ¬(m ≤ k)
    have h5 : ¬(m ≤ k) := h3
    have h6 : 6 * 13 ^ k * n > 3 := by
      have h7 : n ≥ 1 := h1
      have h8 : 13 ^ k ≥ 1 := by
        apply Nat.one_le_pow
        <;> norm_num
      have h9 : 6 * 13 ^ k ≥ 6 := by nlinarith
      have h10 : 6 * 13 ^ k * n ≥ 6 * 1 := by nlinarith
      linarith
    simp [h3]
    <;> linarith
```

### child `imo2025_p4_right1_main`: [`SeedProver/imo2025/IMO2025/P4.lean` lines 3481-3897](https://github.com/ByteDance-Seed/Seed-Prover/blob/38c59cebaf969ac259196eb091757518d5b54c67/SeedProver/imo2025/IMO2025/P4.lean#L3481-L3897) ([local copy](code/SeedProver/imo2025/IMO2025/P4.lean))

```lean
lemma imo2025_p4_right1_main (a0 k n : ℕ)
  (hn : Nat.Coprime n 10)
  (ha0 : a0 = 6 * 12 ^ k * n)
  (h1 : n ≥ 1)
  (h2 : ∀ m : ℕ, (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) > 0)
  (h3 : ∀ m : ℕ, (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) > 3):
  ∀ m : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) ∧
    b ∣ (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) ∧
    c ∣ (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) ∧
    d ∣ (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) ∧
    (∀ e : ℕ, e < (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) →
      e ∣ (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) →
      e ≤ b ∨ e = c ∨ e = d) ∧
    (if (m + 1) ≤ k then 6 * 12 ^ (k - (m + 1)) * 13 ^ (m + 1) * n else 6 * 13 ^ k * n) =
    b + c + d := by
  intro m
  set X := (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) with hX
  set X' := (if (m + 1) ≤ k then 6 * 12 ^ (k - (m + 1)) * 13 ^ (m + 1) * n else 6 * 13 ^ k * n) with hX'
  have h31 : X > 3 := h3 m
  by_cases h4 : m ≥ k
  · -- Case 1: m ≥ k
    have h41 : X > 0 := by
      have h411 := h2 m
      simpa [hX] using h411
    have h5 : X' = X := by
      by_cases h6 : m = k
      · -- Subcase 1.1: m = k
        subst h6
        simp [hX, hX'] <;> ring_nf <;> aesop
      · -- Subcase 1.2: m ≠ k
        have h7 : m > k := by omega
        have h8 : ¬(m + 1 ≤ k) := by omega
        have h9 : ¬(m ≤ k) := by omega
        simp [hX, hX', h8, h9] <;> aesop
    have h10 : 6 ∣ X := by
      rw [hX]
      by_cases h101 : m ≤ k
      · -- Case m ≤ k
        simp [h101]
        <;>
        (try { use 12 ^ (k - m) * 13 ^ m * n <;> ring_nf <;> omega })
      · -- Case ¬(m ≤ k)
        simp [h101]
        <;>
        (try { use 13 ^ k * n <;> ring_nf <;> omega })
    have h102 : ∃ s, X = 6 * s := by
      rcases h10 with ⟨s, hs⟩
      refine ⟨s,?_⟩
      <;> linarith
    rcases h102 with ⟨s, hs⟩
    have h11 : s ≥ 1 := by
      omega
    have h19 : X = 6 * 13 ^ k * n := by
      by_cases h20 : m ≤ k
      · -- Case m ≤ k. Since m ≥ k (from h4) and m ≤ k, then m = k
        have h21 : m = k := by omega
        subst h21
        simp [hX]
        <;> ring
      · -- Case ¬(m ≤ k)
        simp [hX, h20]
        <;> ring
    have h22 : s = 13 ^ k * n := by
      linarith
    have h231 : Nat.Coprime n 10 := hn
    have h232 : ¬(2 ∣ n) := by
      by_contra h233
      have h235 : 2 ∣ Nat.gcd n 10 := Nat.dvd_gcd h233 (by norm_num)
      have h236 : Nat.gcd n 10 = 1 := by simpa [Nat.coprime_iff_gcd_eq_one] using h231
      rw [h236] at h235
      norm_num at h235 <;> contradiction
    have h241 : ¬(5 ∣ n) := by
      by_contra h242
      have h243 : 5 ∣ Nat.gcd n 10 := Nat.dvd_gcd h242 (by norm_num)
      have h244 : Nat.gcd n 10 = 1 := by simpa [Nat.coprime_iff_gcd_eq_one] using h231
      rw [h244] at h243
      norm_num at h243 <;> contradiction
    have h25 : ¬(2 ∣ s) := by
      by_contra h251
      have h2511 : 2 ∣ s := h251
      have h2512 : s = 13 ^ k * n := h22
      rw [h2512] at h2511
      have h252 : 2 ∣ 13 ^ k * n := h2511
      have h253 : 2 ∣ 13 ^ k ∨ 2 ∣ n := (Nat.Prime.dvd_mul (by norm_num)).mp h252
      have h254 : ¬(2 ∣ 13 ^ k) := by
        intro h2541
        have h2542 : 2 ∣ 13 ^ k := h2541
        have h2543 : 2 ∣ 13 := by
          exact Nat.Prime.dvd_of_dvd_pow (by norm_num) h2542
        norm_num at h2543 <;> contradiction
      have h255 : 2 ∣ n := by tauto
      contradiction
    have h26 : ¬(5 ∣ s) := by
      by_contra h261
      have h2611 : 5 ∣ s := h261
      have h2612 : s = 13 ^ k * n := h22
      rw [h2612] at h2611
      have h262 : 5 ∣ 13 ^ k * n := h2611
      have h263 : 5 ∣ 13 ^ k ∨ 5 ∣ n := (Nat.Prime.dvd_mul (by norm_num)).mp h262
      have h264 : ¬(5 ∣ 13 ^ k) := by
        intro h2641
        have h2642 : 5 ∣ 13 ^ k := h2641
        have h2643 : 5 ∣ 13 := by
          exact Nat.Prime.dvd_of_dvd_pow (by norm_num) h2642
        norm_num at h2643 <;> contradiction
      have h265 : 5 ∣ n := by tauto
      contradiction
    have h27 : ∀ e : ℕ, e < X → e ∣ X → e ≤ s ∨ e = 2 * s ∨ e = 3 * s := by
      intro e he1 he2
      have h271 : e ∣ 6 * s := by
        have h2711 : X = 6 * s := by linarith
        rw [h2711] at he2
        simpa using he2
      have h272 : e < 6 * s := by
        have h2721 : X = 6 * s := by linarith
        linarith
      by_cases h273 : e ≤ s
      · -- Case 1: e ≤ s
        exact Or.inl h273
      · -- Case 2: ¬(e ≤ s)
        have h274 : e > s := by linarith
        by_cases h275 : e = 2 * s ∨ e = 3 * s
        · -- Subcase 2.1: e = 2 * s ∨ e = 3 * s
          exact Or.inr h275
        · -- Subcase 2.2: ¬(e = 2 * s ∨ e = 3 * s)
          have h2751 : e ≠ 2 * s := by tauto
          have h2752 : e ≠ 3 * s := by tauto
          have h276 : ∃ t, 6 * s = e * t := by
            have h2761 : e ∣ 6 * s := h271
            rcases h2761 with ⟨t, ht⟩
            refine ⟨t,?_⟩
            <;> linarith
          rcases h276 with ⟨t, ht⟩
          have h277 : 0 < e := by
            by_contra h2771
            have h2772 : e = 0 := by linarith
            rw [h2772] at h272
            linarith
          have h278 : 0 < t := by
            by_contra h2781
            have h2782 : t = 0 := by linarith
            rw [h2782] at ht
            nlinarith
          have h279 : t < 6 := by
            nlinarith
          have h2710 : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by omega
          rcases h2710 with (h2710 | h2710 | h2710 | h2710 | h2710)
          · -- t = 1
            have h2711 : t = 1 := h2710
            rw [h2711] at ht
            nlinarith
          · -- t = 2
            have h2711 : t = 2 := h2710
            rw [h2711] at ht
            have h2712 : e = 3 * s := by nlinarith
            contradiction
          · -- t = 3
            have h2711 : t = 3 := h2710
            rw [h2711] at ht
            have h2712 : e = 2 * s := by nlinarith
            contradiction
          · -- t = 4
            have h2711 : t = 4 := h2710
            rw [h2711] at ht
            have h2713 : 3 * s = 2 * e := by nlinarith
            have h2714 : 2 ∣ 3 * s := by
              omega
            have h2715 : 2 ∣ s := by
              have h27151 : 2 ∣ 3 * s := h2714
              have h27152 : 2 ∣ 3 ∨ 2 ∣ s := (Nat.Prime.dvd_mul (by norm_num)).mp h27151
              tauto
            contradiction
          · -- t = 5
            have h2711 : t = 5 := h2710
            rw [h2711] at ht
            have h2712 : 6 * s = e * 5 := by nlinarith
            have h2713 : 5 ∣ 6 * s := by
              use e
              <;> linarith
            have h2716 : 5 ∣ s := by
              have h27161 : 5 ∣ 6 * s := h2713
              have h27162 : 5 ∣ 6 ∨ 5 ∣ s := (Nat.Prime.dvd_mul (by norm_num)).mp h27161
              tauto
            contradiction
    refine ⟨s, 2 * s, 3 * s, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- Prove `s < 2 * s`
      nlinarith
    · -- Prove `2 * s < 3 * s`
      nlinarith
    · -- Prove `3 * s < X`
      have h2714 : X = 6 * s := by linarith
      nlinarith
    · -- Prove `s ∣ X`
      have h2714 : X = 6 * s := by linarith
      rw [h2714]
      use 6
      <;> ring
    · -- Prove `2 * s ∣ X`
      have h2714 : X = 6 * s := by linarith
      rw [h2714]
      use 3
      <;> ring
    · -- Prove `3 * s ∣ X`
      have h2714 : X = 6 * s := by linarith
      rw [h2714]
      use 2
      <;> ring
    · -- Prove the complicated condition
      intro e he1 he2
      have h2714 : X = 6 * s := by linarith
      have h2715 := h27 e he1 he2
      simp [h2714] at *
      <;> tauto
    · -- Prove `X' = s + 2 * s + 3 * s`
      have h2714 : X = 6 * s := by linarith
      have h2716 : X' = X := h5
      linarith
  · -- Case 2: m < k
    have h42 : m < k := by omega
    have h12 : m ≤ k := by omega
    have h13 : m + 1 ≤ k := by omega
    have h14 : 12 * (if (m + 1) ≤ k then 6 * 12 ^ (k - (m + 1)) * 13 ^ (m + 1) * n else 6 * 13 ^ k * n) = 13 * (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) := by
      have h141 : m + 1 ≤ k := h13
      have h1411 : m ≤ k := h12
      simp [h141, h1411]
      have h142 : k ≥ m + 1 := by omega
      have h1421 : 12 ^ (k - m) = 12 * 12 ^ (k - (m + 1)) := by
        have h14211 : k - m = (k - (m + 1)) + 1 := by omega
        rw [h14211]
        simp [pow_succ]
        <;> ring
      have h143 : 13 ^ (m + 1) = 13 * 13 ^ m := by
        simp [pow_succ]
        <;> ring
      rw [h1421, h143]
      <;> ring
    have h15 : 12 ∣ (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) := by
      have h151 : m ≤ k := h12
      have h1511 : k ≥ m + 1 := by omega
      have h152 : 12 ∣ 12 ^ (k - m) := by
        have h1521 : k - m ≥ 1 := by omega
        have h1522 : 12 ^ (k - m) = 12 * 12 ^ (k - m - 1) := by
          have h15221 : k - m ≥ 1 := by omega
          have h : ∃ t, k - m = t + 1 := by
            use (k - m) - 1
            omega
          rcases h with ⟨t, ht⟩
          simp [ht, pow_succ]
          <;> ring
        rw [h1522]
        <;> use 12 ^ (k - m - 1)
        <;> ring
      have h153 : 12 ∣ 6 * 12 ^ (k - m) * 13 ^ m * n := by
        rcases h152 with ⟨u, hu⟩
        use 6 * u * 13 ^ m * n
        rw [hu]
        <;> ring
      simp [if_pos h151]
      <;> tauto
    have h155 : ∃ t, (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) = 12 * t := by
      obtain ⟨t, ht⟩ := h15
      refine ⟨t,?_⟩
      <;> linarith
    rcases h155 with ⟨t, ht⟩
    have h16 : t ≥ 1 := by
      have h161 : (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) > 3 := h3 m
      linarith
    have h17 : (if (m + 1) ≤ k then 6 * 12 ^ (k - (m + 1)) * 13 ^ (m + 1) * n else 6 * 13 ^ k * n) = 13 * t := by
      have h141 : 12 * (if (m + 1) ≤ k then 6 * 12 ^ (k - (m + 1)) * 13 ^ (m + 1) * n else 6 * 13 ^ k * n) = 13 * (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) := by linarith
      have h172 : (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) = 12 * t := by linarith
      rw [h172] at h141
      linarith
    have h27 : ∀ e : ℕ, e < 12 * t → e ∣ 12 * t → e ≤ 3 * t ∨ e = 4 * t ∨ e = 6 * t := by
      intro e he1 he2
      have h271 : ∃ k : ℕ, 12 * t = e * k := by
        obtain ⟨k, hk⟩ := he2
        refine ⟨k,?_⟩
        <;> linarith
      rcases h271 with ⟨k, hk⟩
      have h2711 : 0 < e := by
        by_contra h27111
        have h27112 : e = 0 := by linarith
        rw [h27112] at hk
        linarith
      have h2712 : 0 < k := by
        by_contra h27121
        have h27122 : k = 0 := by linarith
        rw [h27122] at hk
        nlinarith
      have h2713 : k ≥ 2 := by
        by_contra h27131
        have h27132 : k ≤ 1 := by linarith
        by_cases h27133 : k = 0
        · -- Case k = 0
          rw [h27133] at hk
          nlinarith
        · -- Case k ≠ 0
          have h27134 : k = 1 := by omega
          rw [h27134] at hk
          nlinarith
      by_cases h2714 : e ≤ 3 * t
      · -- Case 1: e ≤ 3 * t
        left
        exact h2714
      · -- Case 2: ¬(e ≤ 3 * t)
        have h27141 : e > 3 * t := by linarith
        have h2715 : k < 4 := by
          by_contra h27151
          have h27152 : k ≥ 4 := by linarith
          nlinarith
        have h2716 : k = 2 ∨ k = 3 := by omega
        rcases h2716 with (h27161 | h27162)
        · -- Subcase 2.1: k = 2
          have h271611 : k = 2 := h27161
          have h271612 : 12 * t = e * 2 := by
            rw [h271611] at hk
            <;> linarith
          have h271613 : e = 6 * t := by nlinarith
          right
          right
          linarith
        · -- Subcase 2.2: k = 3
          have h271621 : k = 3 := h27162
          have h271622 : 12 * t = e * 3 := by
            rw [h271621] at hk
            <;> linarith
          have h271623 : e = 4 * t := by nlinarith
          right
          left
          linarith
    have hX_eq_simplified : 6 * 12 ^ (k - m) * 13 ^ m * n = 12 * t := by
      have h151 : m ≤ k := h12
      have h1511 : (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) = 6 * 12 ^ (k - m) * 13 ^ m * n := by
        simp [h151]
      have h1512 : (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) = 12 * t := ht
      linarith
    have hX'_eq_simplified : 6 * 12 ^ (k - (m + 1)) * 13 ^ (m + 1) * n = 13 * t := by
      have h131 : m + 1 ≤ k := h13
      have h132 : (if (m + 1) ≤ k then 6 * 12 ^ (k - (m + 1)) * 13 ^ (m + 1) * n else 6 * 13 ^ k * n) = 6 * 12 ^ (k - (m + 1)) * 13 ^ (m + 1) * n := by
        simp [h131]
      have h133 : (if (m + 1) ≤ k then 6 * 12 ^ (k - (m + 1)) * 13 ^ (m + 1) * n else 6 * 13 ^ k * n) = 13 * t := h17
      linarith
    have h1 : 3 * t ∣ (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) := by
      have h121 : m ≤ k := h12
      have h122 : (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) = 6 * 12 ^ (k - m) * 13 ^ m * n := by
        simp [h121]
      have h123 : 6 * 12 ^ (k - m) * 13 ^ m * n = 12 * t := hX_eq_simplified
      have h124 : (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) = 12 * t := by linarith
      have h125 : 3 * t ∣ 12 * t := by
        use 4
        <;> ring
      rw [h124]
      exact h125
    have h2 : 4 * t ∣ (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) := by
      have h121 : m ≤ k := h12
      have h122 : (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) = 6 * 12 ^ (k - m) * 13 ^ m * n := by
        simp [h121]
      have h123 : 6 * 12 ^ (k - m) * 13 ^ m * n = 12 * t := hX_eq_simplified
      have h124 : (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) = 12 * t := by linarith
      have h125 : 4 * t ∣ 12 * t := by
        use 3
        <;> ring
      rw [h124]
      exact h125
    have h3 : 6 * t ∣ (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) := by
      have h121 : m ≤ k := h12
      have h122 : (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) = 6 * 12 ^ (k - m) * 13 ^ m * n := by
        simp [h121]
      have h123 : 6 * 12 ^ (k - m) * 13 ^ m * n = 12 * t := hX_eq_simplified
      have h124 : (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) = 12 * t := by linarith
      have h125 : 6 * t ∣ 12 * t := by
        use 2
        <;> ring
      rw [h124]
      exact h125
    refine ⟨3 * t, 4 * t, 6 * t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- Prove `3 * t < 4 * t`
      nlinarith
    · -- Prove `4 * t < 6 * t`
      nlinarith
    · -- Prove `6 * t < (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n)`
      have h2726 : 6 * t < 12 * t := by nlinarith
      have h2727 : (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) = 6 * 12 ^ (k - m) * 13 ^ m * n := by
        simp [h12]
      have h2728 : 6 * 12 ^ (k - m) * 13 ^ m * n = 12 * t := hX_eq_simplified
      linarith
    · -- Prove `3 * t ∣ (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n)`
      exact h1
    · -- Prove `4 * t ∣ (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n)`
      exact h2
    · -- Prove `6 * t ∣ (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n)`
      exact h3
    · -- Prove the complicated condition
      intro e he1 he2
      have h2727 : (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) = 6 * 12 ^ (k - m) * 13 ^ m * n := by
        simp [h12]
      have h2728 : 6 * 12 ^ (k - m) * 13 ^ m * n = 12 * t := hX_eq_simplified
      have he11 : e < 12 * t := by
        have h1 : e < (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) := he1
        have h2 : (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) = 6 * 12 ^ (k - m) * 13 ^ m * n := by simp [h12]
        have h3 : 6 * 12 ^ (k - m) * 13 ^ m * n = 12 * t := hX_eq_simplified
        linarith
      have he22 : e ∣ 12 * t := by
        have h1 : e ∣ (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) := he2
        have h2 : (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) = 6 * 12 ^ (k - m) * 13 ^ m * n := by simp [h12]
        have h3 : 6 * 12 ^ (k - m) * 13 ^ m * n = 12 * t := hX_eq_simplified
        rw [h2, h3] at h1
        simpa using h1
      have h2717 := h27 e he11 he22
      have h2718 : e ≤ 3 * t ∨ e = 4 * t ∨ e = 6 * t := h2717
      aesop
    · -- Prove `(if (m + 1) ≤ k then 6 * 12 ^ (k - (m + 1)) * 13 ^ (m + 1) * n else 6 * 13 ^ k * n) = 3 * t + 4 * t + 6 * t`
      have h27171 : (if (m + 1) ≤ k then 6 * 12 ^ (k - (m + 1)) * 13 ^ (m + 1) * n else 6 * 13 ^ k * n) = 6 * 12 ^ (k - (m + 1)) * 13 ^ (m + 1) * n := by
        simp [h13]
      have h27172 : 6 * 12 ^ (k - (m + 1)) * 13 ^ (m + 1) * n = 13 * t := hX'_eq_simplified
      have h27173 : (if (m + 1) ≤ k then 6 * 12 ^ (k - (m + 1)) * 13 ^ (m + 1) * n else 6 * 13 ^ k * n) = 13 * t := by linarith
      linarith
```

How the parts fit. The parent `imo2025_p4_right` is the glue: it assembles
four `have`s from the four named children, in dependency order, then packages
the witness.

1. `have h1 : n ≥ 1 := imo2025_p4_right8_h1 a0 k n hn ha0` (line 3907). This
   child closes by `by_contra`: if `n = 0`, then `Nat.Coprime n 10` reduces to
   `Nat.Coprime 0 10`, which `norm_num` turns into `False`.
2. `have h2 : ∀ m, (if m ≤ k then … else …) > 0 := imo2025_p4_right8_h2 …`
   (line 3908). This child splits on `m ≤ k` and in each branch shows the
   product is positive using `Nat.one_le_pow` (each of `12 ^ …`, `13 ^ …` is at
   least 1) and `positivity`; it is the "all terms are positive" conjunct.
3. `have h3 : ∀ m, (if m ≤ k then … else …) > 3 := imo2025_p4_right8_h3 …`
   (line 3909). This child again splits on `m ≤ k` and lowers the product to
   `≥ 6` with `Nat.one_le_pow` and `nlinarith`; it supplies the `> 3` bound the
   divisor lemma needs to guarantee three distinct proper divisors.
4. `have h4 : ∀ m, ∃ b c d, … := imo2025_p4_right1_main …` (line 3910). This
   child is the real content: for each term `X = 6·12^(k−m)·13^m·n` (or
   `6·13^k·n` after index `k`) it exhibits the three largest proper divisors and
   shows their sum equals the next term. In the `m ≥ k` branch it writes
   `X = 6·s` with `s = 13^k·n` and returns `⟨s, 2s, 3s⟩`; in the `m < k` branch
   it writes `X = 12·t` and returns `⟨3t, 4t, 6t⟩`, summing to `13t`.

With these four facts in hand the glue names the witness
`fun m => if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n`
with `use` (line 3912) and closes the three conjuncts by two `constructor`s:
positivity is `exact h2 n` (line 3917), the divisor decomposition is
`exact h4 n` (line 3922), and `a 0 = a0` is `simp only [ha0]; aesop` (lines
3924-3926).

The lemma graph is a single layer: `imo2025_p4_right` → {`imo2025_p4_right8_h1`,
`imo2025_p4_right8_h2`, `imo2025_p4_right8_h3`, `imo2025_p4_right1_main`}. Each
child is a leaf: its statement is self-contained and its proof closes on its own
with `omega`/`nlinarith`/`norm_num`/`positivity`/`ring`/`aesop`, using only the
hypotheses passed in and no further project lemma, so none of the four children
depends on another.

## Why it is good

1. (*check*) The parent `imo2025_p4_right` (lines 3900-3926) introduces the
   witness `fun m => if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else
   6 * 13 ^ k * n` with `use` (line 3912), then closes the three conjuncts of
   the existential from exactly four same-file lemmas — `imo2025_p4_right8_h1`
   (line 3907, `n ≥ 1`), `imo2025_p4_right8_h2` (line 3908, positivity),
   `imo2025_p4_right8_h3` (line 3909, `> 3`), `imo2025_p4_right1_main`
   (line 3910, the proper-divisor decomposition) — and the `a 0 = a0` conjunct
   closes by `simp only [ha0]; aesop` (lines 3924-3926).
2. (*check*) The copied file `P4.lean` contains no `sorry`, `admit`, `Admitted`
   or `axiom` declaration that closes a goal: the only occurrences of the string
   "axiom" are the diagnostic commands `#print axioms …` (lines 1544, 2470,
   2731, 3033, 3139, 3387, 3928) and the variable name `h_axiom1` (line 3335).
3. (*author-statement*) The authors state the informal problem as a doc comment
   directly above the theorem: "The infinite sequence a_1, a_2, … consists of
   positive integers … For each n ≥ 1, the integer a_{n+1} is the sum of the
   three largest proper divisors of a_n. When a_1 is 6 * 12^k * m, where m is
   coprime to 10. Please prove that a_n exists." (lines 3904-3905).
4. (*measurement*) The glue is 27 lines (3900-3926) and the four children span
   9, 36, 41 and 417 lines respectively (3389-3397, 3400-3435, 3438-3478,
   3481-3897); all four children close without invoking any further project
   lemma (depth 1), and `imo2025_p4_right8_h1` closes by `by_contra` plus
   `norm_num` alone.

In my opinion the detail worth copying is the factoring of the witness's three
obligations into four named lemmas ordered by dependency (`n ≥ 1` → positivity →
`> 3` → the divisor decomposition): the glue then reads as four `have`s, one
`use`, and three one-liner constructors, so each bounded prover gets a
self-contained leaf whose hypotheses are exactly the earlier lemmas.

## When to use it, and when not

Use it for an existential goal `∃ a, P a` whose body is a conjunction of
properties of the witness, when the witness is one closed-form term and each of
its properties is already factored into a named lemma (a bound, positivity, a
lower bound, the main decomposition). Each conjunct then closes by one lemma
application plus `use`/`constructor` packaging, so the proof has no free
arithmetic left in the glue.

Avoid it when the witness must be assembled interactively from several choices
rather than written as one term; when the conjuncts must be proved jointly
rather than one per lemma; or when the candidate's properties are not already
named, so the glue would have to re-derive them inline and the lemma split
bought nothing.

## Consequences

The ∃-goal becomes a `use ⟨witness⟩` plus three `constructor` obligations, one
per conjunct, each discharged by a pre-packaged lemma, so a missing conjunct is
a missing lemma rather than a partial proof. The obligations are coupled through
the lemmas' hypotheses: `h2` needs `h1` (`n ≥ 1`), `h3` needs `h2` (positivity),
and `right1_main` needs all three, so the glue must assemble the `have`s in
order and re-state each exact type. The witness is a closed-form term with an
`if m ≤ k` branch, so any later step that computes the witness at a specific
index must simplify the `if` first; the `a 0 = a0` conjunct is discharged by
`simp only [ha0]; aesop` rather than by a named lemma, so if `ha0` were stated
differently that branch would need its own fact.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/ByteDance-Seed/Seed-Prover at commit `38c59cebaf969ac259196eb091757518d5b54c67`, under `Apache-2.0`; see the [source note](../../sources/seed-prover/SOURCE.md) for the licence text and attribution.
