import Mathlib
set_option pp.numericTypes true
set_option pp.funBinderTypes true
set_option maxHeartbeats 0
open Classical Set Real

-- Helper lemma: sin 1 > 0.78
lemma sin_one_lower : (0.78 : ℝ) < sin 1 := by
  have habs : |(1:ℝ)| ≤ 1 := by norm_num
  have bound := sin_bound habs
  have h := abs_sub_le_iff.1 bound
  simp only [abs_one, one_pow, one_mul] at h
  have lower : sin 1 ≥ 1 - 1/6 - 5/96 := by linarith [h.2]
  -- 1 - 1/6 - 5/96 = 96/96 - 16/96 - 5/96 = 75/96 > 0.78
  have calc1 : (1:ℝ) - 1/6 - 5/96 = 75/96 := by norm_num
  have calc2 : (0.78:ℝ) < 75/96 := by norm_num
  linarith

-- Lemma 1: The lower bound inequality holds
lemma sin_ge_inv_pi_mul_quad : ∀ x ∈ Icc (0:ℝ) π, (1 / π) * x * (π - x) ≤ sin x := by
  intro x ⟨hx_lo, hx_hi⟩
  rcases eq_or_lt_of_le hx_lo with rfl | hx_pos
  · simp
  rcases eq_or_lt_of_le hx_hi with rfl | hx_lt_pi
  · simp
  -- Use symmetry: sin(π - x) = sin x and the parabola is symmetric
  -- So we can assume x ≤ π/2
  by_cases hx_half : x ≤ π / 2
  · -- x ∈ (0, π/2]
    -- We need (1/π) * x * (π - x) ≤ sin x
    -- Equivalently: x * (π - x) ≤ π * sin x
    have rw1 : (1 / π) * x * (π - x) = x * (π - x) / π := by ring
    rw [rw1, div_le_iff₀ pi_pos]
    -- Use Jordan's inequality: (2/π) * x ≤ sin x for x ∈ [0, π/2]
    -- We need x * (π - x) ≤ π * sin x
    by_cases hx_large : x ≥ π - 2
    · -- x ∈ [π - 2, π/2], use Jordan's inequality
      have jordan := mul_le_sin (le_of_lt hx_pos) hx_half
      have h1 : x * (π - x) ≤ 2 * x := by nlinarith [pi_pos]
      have h2 : 2 * x = π * (2 / π * x) := by field_simp
      have h3 : π * (2 / π * x) ≤ π * sin x := by nlinarith [jordan, pi_pos]
      linarith
    · -- x ∈ (0, π - 2), use direct bound
      push_neg at hx_large
      -- For small x, we use the Taylor bound sin x ≥ x - x³/6 - x⁴ * 5/96
      -- And show x(π-x) ≤ π * (x - x³/6 - x⁴ * 5/96)
      by_cases hx_small : x ≤ 1
      · -- x ∈ (0, 1]
        have habs : |x| ≤ 1 := by rw [abs_of_nonneg (le_of_lt hx_pos)]; exact hx_small
        have bound := sin_bound habs
        have h := abs_sub_le_iff.1 bound
        rw [abs_of_nonneg (le_of_lt hx_pos)] at h
        have taylor : x - x^3/6 - x^4 * (5/96) ≤ sin x := by linarith [h.2]
        -- Need x * (π - x) ≤ π * (x - x³/6 - x⁴ * 5/96)
        have expand1 : x * (π - x) = π * x - x^2 := by ring
        have ineq : π * x^3/6 + π * x^4 * (5/96) ≤ x^2 := by
          have h1 : π * x^3/6 ≤ π * x^2/6 := by
            have := mul_le_mul_of_nonneg_left hx_small (mul_nonneg (le_of_lt pi_pos) (sq_nonneg x))
            calc π * x^3/6 = (π * x^2 * x) / 6 := by ring
              _ ≤ (π * x^2 * 1) / 6 := by nlinarith
              _ = π * x^2/6 := by ring
          have h2 : π * x^4 * (5/96) ≤ π * x^2 * (5/96) := by
            have hx2 : x^2 ≤ 1 := by nlinarith
            have := mul_le_mul_of_nonneg_left hx2 (mul_nonneg (le_of_lt pi_pos) (sq_nonneg x))
            nlinarith [sq_nonneg x, pi_pos]
          have h4 : π/6 + π * 5/96 < 1 := by nlinarith [pi_lt_four]
          nlinarith [sq_nonneg x]
        have step1 : x * (π - x) = π * x - x^2 := expand1
        have step2 : π * x - x^2 ≤ π * x - (π * x^3/6 + π * x^4 * (5/96)) := by linarith
        have step3 : π * x - (π * x^3/6 + π * x^4 * (5/96)) = π * (x - x^3/6 - x^4 * (5/96)) := by ring
        have step4 : π * (x - x^3/6 - x^4 * (5/96)) ≤ π * sin x := by nlinarith [taylor, pi_pos]
        linarith
      · -- x ∈ (1, π - 2)
        -- This interval is (1, ~1.14), quite small
        -- Use sin x ≥ sin 1 (sin is increasing on [0, π/2])
        push_neg at hx_small
        have sin_incr : sin 1 ≤ sin x := by
          apply sin_le_sin_of_le_of_le_pi_div_two
          · linarith [pi_pos]
          · exact hx_half
          · exact le_of_lt hx_small
        -- x * (π - x) < (π - 2) * 2 = 2π - 4 since x < π - 2 and π - x > 2
        -- We need to show x(π-x) < π * sin 1
        -- x < π - 2 and x > 1, so π - x > 2, giving x(π-x) < (π-2) * π = π² - 2π
        -- But we also have x > 1 and π - x > 2 doesn't hold... let me reconsider
        -- If x < π - 2 ≈ 1.14, and x > 1, then x ∈ (1, 1.14)
        -- And π - x ∈ (2, 2.14)
        -- So x(π-x) < 1.14 * 2.14 ≈ 2.44
        -- We need π * sin 1 ≈ 3.14 * 0.84 ≈ 2.64 > 2.44 ✓
        have hpi_hi : π < 3.15 := pi_lt_d2
        have upper : x * (π - x) < (π - 2) * (π - 1) := by nlinarith [pi_pos]
        -- Need (π - 2)(π - 1) < π * sin 1
        -- (π - 2)(π - 1) = π² - 3π + 2 < 3.15² - 3*3.14 + 2 = 9.92 - 9.42 + 2 = 2.5
        -- π * sin 1 > 3.14 * 0.78 = 2.45...
        -- Actually we need a tighter bound
        -- We have x ∈ (1, π - 2) which is (1, ~1.14)
        -- sin(x) ≥ sin(1) > 0.78 by sin_incr and sin_one_lower
        -- x(π - x) < max when x in middle, but x < π - 2
        -- Need x(π-x) < π * sin x
        -- For x = 1: 1 * (π - 1) ≈ 2.14 and π * sin(1) ≈ 3.14 * 0.84 ≈ 2.64
        -- For x = π - 2 ≈ 1.14: 1.14 * 2 = 2.28 and π * sin(1.14) > π * sin(1) ≈ 2.64
        -- So we're safe
        have key : x * (π - x) < π * sin x := by
          -- Since x < π - 2, we have π - x > 2
          -- But also x > 1, so x(π - x) < x * (π - 1) < (π - 2)(π - 1)
          -- Wait, that's not right. If x > 1 and π - x < π - 1, then x(π-x) < x(π-1)
          -- But we need an upper bound for x(π-x)
          -- For x ∈ (1, π-2), the max of x(π-x) is at the boundary
          -- At x = 1: 1 * (π - 1) ≈ 2.14
          -- At x = π - 2: (π-2) * 2 = 2π - 4 ≈ 2.28
          -- So the max is at x = π - 2
          have h_bound : x * (π - x) < (π - 2) * 2 := by
            -- x < π - 2 and π - x < π - 1 < 2 + something
            -- Actually π - x > 2 for x < π - 2
            -- And x(π-x) is increasing on (0, π/2)
            -- Since x < π - 2 < π/2, we have x(π-x) < (π-2)(π-(π-2)) = (π-2)*2
            nlinarith [pi_pos]
          have h_target : (π - 2) * 2 < π * sin 1 := by
            -- (π - 2) * 2 = 2π - 4 ≈ 2.28
            -- π * sin 1 > 3.14 * 0.78 = 2.4492 > 2.28 ✓
            have hpi_lo : π > 3.14 := pi_gt_d2
            have h1 : (π - 2) * 2 = 2 * π - 4 := by ring
            have h2 : (2:ℝ) * π - 4 < 2 * 3.15 - 4 := by linarith [pi_lt_d2]
            have h3 : (2:ℝ) * 3.15 - 4 = 2.3 := by norm_num
            have h4 : (2.3:ℝ) < 0.78 * 3.14 := by norm_num
            have h5 : (0.78:ℝ) * 3.14 < 0.78 * π := by nlinarith
            have h6 : (0.78:ℝ) * π < sin 1 * π := by nlinarith [sin_one_lower, pi_pos]
            linarith
          have h_sin : sin 1 ≤ sin x := sin_incr
          nlinarith [pi_pos]
        linarith [key]
  · -- x > π/2, use symmetry
    push_neg at hx_half
    have hx'_pos : 0 < π - x := by linarith
    have hx'_half : π - x ≤ π / 2 := by linarith
    -- sin x = sin(π - x) and the parabola is symmetric
    have sin_sym : sin x = sin (π - x) := by rw [sin_pi_sub]
    have parab_sym : (1 / π) * x * (π - x) = (1 / π) * (π - x) * x := by ring
    -- Apply the first half case to π - x
    have rw1 : (1 / π) * (π - x) * x = (π - x) * x / π := by ring
    rw [sin_sym, parab_sym, rw1, div_le_iff₀ pi_pos]
    by_cases hx'_large : π - x ≥ π - 2
    · have jordan := mul_le_sin (le_of_lt hx'_pos) hx'_half
      have h1 : (π - x) * x ≤ 2 * (π - x) := by nlinarith [pi_pos]
      have h2 : 2 * (π - x) = π * (2 / π * (π - x)) := by field_simp
      have h3 : π * (2 / π * (π - x)) ≤ π * sin (π - x) := by nlinarith [jordan, pi_pos]
      linarith
    · push_neg at hx'_large
      by_cases hx'_small : π - x ≤ 1
      · have habs : |π - x| ≤ 1 := by rw [abs_of_nonneg (le_of_lt hx'_pos)]; exact hx'_small
        have bound := sin_bound habs
        have h := abs_sub_le_iff.1 bound
        rw [abs_of_nonneg (le_of_lt hx'_pos)] at h
        have taylor : (π - x) - (π - x)^3/6 - (π - x)^4 * (5/96) ≤ sin (π - x) := by linarith [h.2]
        have ineq : π * (π - x)^3/6 + π * (π - x)^4 * (5/96) ≤ (π - x)^2 := by
          have h1 : π * (π - x)^3/6 ≤ π * (π - x)^2/6 := by
            have := mul_le_mul_of_nonneg_left hx'_small (mul_nonneg (le_of_lt pi_pos) (sq_nonneg (π - x)))
            calc π * (π - x)^3/6 = (π * (π - x)^2 * (π - x)) / 6 := by ring
              _ ≤ (π * (π - x)^2 * 1) / 6 := by nlinarith
              _ = π * (π - x)^2/6 := by ring
          have h2 : π * (π - x)^4 * (5/96) ≤ π * (π - x)^2 * (5/96) := by
            have hx2 : (π - x)^2 ≤ 1 := by nlinarith
            nlinarith [sq_nonneg (π - x), pi_pos]
          have h4 : π/6 + π * 5/96 < 1 := by nlinarith [pi_lt_four]
          nlinarith [sq_nonneg (π - x)]
        have step1 : (π - x) * x = π * (π - x) - (π - x)^2 := by ring
        have step2 : π * (π - x) - (π - x)^2 ≤ π * (π - x) - (π * (π - x)^3/6 + π * (π - x)^4 * (5/96)) := by linarith
        have step3 : π * (π - x) - (π * (π - x)^3/6 + π * (π - x)^4 * (5/96)) = π * ((π - x) - (π - x)^3/6 - (π - x)^4 * (5/96)) := by ring
        have step4 : π * ((π - x) - (π - x)^3/6 - (π - x)^4 * (5/96)) ≤ π * sin (π - x) := by nlinarith [taylor, pi_pos]
        linarith
      · push_neg at hx'_small
        have sin_incr : sin 1 ≤ sin (π - x) := by
          apply sin_le_sin_of_le_of_le_pi_div_two
          · linarith [pi_pos]
          · exact hx'_half
          · exact le_of_lt hx'_small
        have hpi_hi : π < 3.15 := pi_lt_d2
        have upper : (π - x) * x < (π - 2) * (π - 1) := by nlinarith [pi_pos]
        have key : (π - x) * x < π * sin (π - x) := by
          have h_bound : (π - x) * x < (π - 2) * 2 := by nlinarith [pi_pos]
          have h_target : (π - 2) * 2 < π * sin 1 := by
            have hpi_lo : π > 3.14 := pi_gt_d2
            have h1 : (π - 2) * 2 = 2 * π - 4 := by ring
            have h2 : (2:ℝ) * π - 4 < 2 * 3.15 - 4 := by linarith [pi_lt_d2]
            have h3 : (2:ℝ) * 3.15 - 4 = 2.3 := by norm_num
            have h4 : (2.3:ℝ) < 0.78 * 3.14 := by norm_num
            have h5 : (0.78:ℝ) * 3.14 < 0.78 * π := by nlinarith
            have h6 : (0.78:ℝ) * π < sin 1 * π := by nlinarith [sin_one_lower, pi_pos]
            linarith
          have h_sin : sin 1 ≤ sin (π - x) := sin_incr
          nlinarith [pi_pos]
        linarith [key]

-- Lemma 2: The constant 1/π is the greatest lower bound
lemma inv_pi_is_greatest_lower_bound (a : ℝ) (h : ∀ x ∈ Icc (0:ℝ) π, a * x * (π - x) ≤ sin x) :
    a ≤ 1 / π := by
  by_contra hc
  push_neg at hc
  have ha_pos : 0 < a := by linarith [one_div_pos.mpr pi_pos]
  -- For small x > 0, sin x ≈ x, so sin x / (x(π-x)) ≈ 1/π
  -- If a > 1/π, then a * x * (π - x) > sin x for small x
  set x := min (min ((a - 1/π) / (2 * a)) (1/2)) (π/2) with hx_def
  have hx_pos : 0 < x := by
    rw [hx_def]
    apply lt_min
    apply lt_min
    · apply div_pos (by linarith) (by linarith)
    · norm_num
    · linarith [pi_pos]
  have hx_in : x ∈ Icc (0:ℝ) π := ⟨le_of_lt hx_pos, by
    calc x ≤ π / 2 := min_le_right _ _
      _ ≤ π := by linarith [pi_pos]⟩
  have hbound := h x hx_in
  -- x ≤ ε where ε = (a - 1/π) / (2a)
  have hx_le_eps : x ≤ (a - 1/π) / (2 * a) := by
    calc x ≤ min ((a - 1/π) / (2 * a)) (1/2) := min_le_left _ _
      _ ≤ (a - 1/π) / (2 * a) := min_le_left _ _
  -- ε < π - 1/a
  have heps_lt : (a - 1/π) / (2 * a) < π - 1/a := by
    have h2a_pos : 0 < 2 * a := by linarith
    rw [div_lt_iff₀ h2a_pos]
    -- Need (a - 1/π) < (π - 1/a) * (2 * a) = 2aπ - 2
    have expand : (π - 1/a) * (2 * a) = 2 * a * π - 2 := by field_simp
    rw [expand]
    -- Need a - 1/π < 2aπ - 2
    -- i.e., a - 2aπ < -2 + 1/π
    -- i.e., a(1 - 2π) < 1/π - 2
    -- Since 1 - 2π < 0, we need a > (1/π - 2)/(1 - 2π) = (2 - 1/π)/(2π - 1)
    -- Let's verify: (2 - 1/π)/(2π - 1) = (2π - 1)/(π(2π - 1)) = 1/π
    -- So we need a > 1/π, which is hc ✓
    have h1 : 2 * π - 1 > 0 := by
      have : π > 3 := pi_gt_three
      linarith
    have h2 : a * (2 * π - 1) > (1/π) * (2 * π - 1) := by
      apply mul_lt_mul_of_pos_right hc h1
    have h3 : (1/π) * (2 * π - 1) = 2 - 1/π := by field_simp
    linarith
  -- x < π - 1/a
  have hx_lt : x < π - 1/a := lt_of_le_of_lt hx_le_eps heps_lt
  -- a * (π - x) > 1
  have key : a * (π - x) > 1 := by
    have h1 : π - x > 1/a := by linarith
    have h2 : a * (1/a) = 1 := by field_simp
    nlinarith
  -- a * x * (π - x) > x ≥ sin x
  have h1 : a * x * (π - x) > x := by
    have eq1 : a * x * (π - x) = x * (a * (π - x)) := by ring
    nlinarith [hx_pos]
  have h2 : sin x ≤ x := sin_le (le_of_lt hx_pos)
  linarith

-- Lemma 3: The upper bound inequality holds
lemma sin_le_four_div_pi_sq_mul_quad : ∀ x ∈ Icc (0:ℝ) π, sin x ≤ (4 / π ^ 2) * x * (π - x) := by
  intro x ⟨hx_lo, hx_hi⟩
  rcases eq_or_lt_of_le hx_lo with rfl | hx_pos
  · simp
  rcases eq_or_lt_of_le hx_hi with rfl | hx_lt_pi
  · simp
  -- Use symmetry
  by_cases hx_half : x ≤ π / 2
  · -- x ∈ (0, π/2]
    by_cases hx_small : x ≤ 0.6
    · -- For small x, sin x ≤ x and x ≤ (4/π²) x (π-x) when (4/π²)(π-x) ≥ 1
      have h1 : sin x ≤ x := sin_le (le_of_lt hx_pos)
      have h2 : (4 / π^2) * (π - x) ≥ 1 := by
        have hpi_lo : π > 3.14 := pi_gt_d2
        have hpi_hi : π < 3.15 := pi_lt_d2
        have h3 : π - x ≥ π - 0.6 := by linarith
        have h4 : π - 0.6 > 2.5 := by linarith
        have h5 : π^2 < 10 := by nlinarith
        have h6 : 4 / π^2 > 4 / 10 := by
          apply div_lt_div_of_pos_left (by norm_num : (0:ℝ) < 4) (by positivity) h5
        nlinarith
      have step1 : x = x * 1 := by ring
      have step2 : x * 1 ≤ x * ((4 / π^2) * (π - x)) := by nlinarith [hx_pos]
      have step3 : x * ((4 / π^2) * (π - x)) = (4 / π^2) * x * (π - x) := by ring
      linarith
    · -- For x ∈ (0.6, π/2]
      push_neg at hx_small
      -- At x = π/2: sin(π/2) = 1 = (4/π²)(π/2)(π/2)
      have h_at_pi_half : (4 / π^2) * (π/2) * (π - π/2) = 1 := by
        have eq1 : π - π/2 = π/2 := by ring
        rw [eq1]
        field_simp
        ring
      rcases eq_or_lt_of_le hx_half with rfl | hx_lt_half
      · -- x = π/2
        simp [sin_pi_div_two, h_at_pi_half]
      · -- x < π/2
        -- For x ∈ (0.6, π/2), use two cases based on where x is
        by_cases hx_mid : x ≤ π - π^2/4
        · -- x ∈ (0.6, π - π²/4] ≈ (0.6, 0.67]
          -- Here sin x ≤ x and 1 ≤ (4/π²)(π-x)
          have h1 : sin x ≤ x := sin_le (le_of_lt hx_pos)
          have h2 : 1 ≤ (4 / π^2) * (π - x) := by
            -- Need π - x ≥ π²/4
            have hkey : π - x ≥ π^2/4 := by linarith
            have h_pi2_pos : (0:ℝ) < π^2 := by positivity
            have h_rw : (4 / π^2) * (π^2/4) = 1 := by field_simp
            have h_mono : (4 / π^2) * (π - x) ≥ (4 / π^2) * (π^2/4) := by
              apply mul_le_mul_of_nonneg_left hkey
              positivity
            linarith
          have step1 : x = x * 1 := by ring
          have step2 : x * 1 ≤ x * ((4 / π^2) * (π - x)) := by nlinarith [hx_pos]
          have step3 : x * ((4 / π^2) * (π - x)) = (4 / π^2) * x * (π - x) := by ring
          linarith
        · -- x ∈ (π - π²/4, π/2)
          push_neg at hx_mid
          -- Use Taylor expansion around π/2
          -- sin x = cos(π/2 - x) and parabola = 1 - 4(π/2-x)²/π²
          set y := π/2 - x with hy_def
          have hy_pos : 0 < y := by linarith
          -- y < π/2 - (π - π²/4) = π²/4 - π/2 ≈ 2.47 - 1.57 = 0.9
          have hy_small : y < π^2/4 - π/2 := by linarith
          have hpi_hi : π < 3.15 := pi_lt_d2
          have hpi_lo : π > 3.14 := pi_gt_d2
          -- π²/4 - π/2 < 3.15²/4 - 3.14/2 = 2.48 - 1.57 = 0.91
          have hy_bound : y < 0.91 := by nlinarith
          have hy_le_1 : y ≤ 1 := by linarith
          have habs_y : |y| ≤ 1 := by rw [abs_of_nonneg (le_of_lt hy_pos)]; linarith

          -- sin x = sin(π/2 - y) = cos y
          have sin_eq : sin x = cos y := by
            have hx_eq : x = π/2 - y := by linarith
            rw [hx_eq, sin_pi_div_two_sub]

          -- cos y ≤ 1 - y²/2 + y⁴/24 using Taylor bound
          have cos_bound' := cos_bound habs_y
          have hcos := abs_sub_le_iff.1 cos_bound'
          rw [abs_of_nonneg (le_of_lt hy_pos)] at hcos
          -- |cos y - (1 - y²/2)| ≤ y⁴ * (5/96)
          -- So cos y ≤ 1 - y²/2 + y⁴ * (5/96)
          have cos_upper : cos y ≤ 1 - y^2/2 + y^4 * (5/96) := by linarith [hcos.1]

          -- The parabola at x
          have parab_eq : (4 / π^2) * x * (π - x) = 1 - 4 * y^2 / π^2 := by
            have h1 : π - x = π/2 + y := by linarith
            have h2 : x = π/2 - y := by linarith
            rw [h1, h2]
            field_simp
            ring

          -- Need to show cos y ≤ 1 - 4y²/π²
          -- cos y ≤ 1 - y²/2 + y⁴ * (5/96)
          -- Need: 1 - y²/2 + y⁴ * (5/96) ≤ 1 - 4y²/π²
          -- i.e., y⁴ * (5/96) ≤ y²/2 - 4y²/π²
          -- i.e., y⁴ * (5/96) ≤ y²(1/2 - 4/π²)
          -- For y > 0: y² * (5/96) ≤ 1/2 - 4/π²
          -- 1/2 - 4/π² > 1/2 - 4/3.14² > 1/2 - 0.406 = 0.094
          -- y² * (5/96) < 0.91² * (5/96) < 0.83 * 0.053 < 0.044 < 0.094 ✓
          have key : cos y ≤ 1 - 4 * y^2 / π^2 := by
            have h1 : 4 / π^2 < 4 / 3.14^2 := by
              apply div_lt_div_of_pos_left (by norm_num : (0:ℝ) < 4)
              · norm_num
              · nlinarith
            have h2 : (4:ℝ) / 3.14^2 < 0.406 := by norm_num
            have h3 : (1:ℝ)/2 - 4/π^2 > 1/2 - 0.406 := by linarith
            have h4 : (1:ℝ)/2 - 0.406 = 0.094 := by norm_num
            have h5 : y^2 * (5/96) < 0.91^2 * (5/96) := by nlinarith [sq_nonneg y]
            have h6 : (0.91:ℝ)^2 * (5/96) < 0.044 := by norm_num
            have ineq1 : y^2 * (5/96) < 1/2 - 4/π^2 := by linarith
            -- Now: cos y ≤ 1 - y²/2 + y⁴ * (5/96)
            --     = 1 - y²/2 + y² * (y² * (5/96))
            -- Need: 1 - y²/2 + y² * (y² * (5/96)) ≤ 1 - 4y²/π²
            -- i.e., y² * (y² * (5/96)) ≤ y²/2 - 4y²/π²
            -- i.e., y² * (y² * (5/96)) ≤ y² * (1/2 - 4/π²)
            -- i.e., y² * (5/96) ≤ 1/2 - 4/π² (for y ≠ 0)
            have h7 : y^4 * (5/96) = y^2 * (y^2 * (5/96)) := by ring
            have h8 : y^2 * (y^2 * (5/96)) ≤ y^2 * (1/2 - 4/π^2) := by
              apply mul_le_mul_of_nonneg_left (le_of_lt ineq1)
              exact sq_nonneg y
            have h9 : 1 - y^2/2 + y^4 * (5/96) ≤ 1 - 4*y^2/π^2 := by
              have eq1 : 1 - y^2/2 + y^4 * (5/96) - (1 - 4*y^2/π^2) = y^4 * (5/96) - y^2/2 + 4*y^2/π^2 := by ring
              have eq2 : y^4 * (5/96) - y^2/2 + 4*y^2/π^2 = y^4 * (5/96) - y^2 * (1/2 - 4/π^2) := by ring
              nlinarith [sq_nonneg y]
            linarith

          rw [sin_eq, parab_eq]
          exact key
  · -- x > π/2, use symmetry
    push_neg at hx_half
    have hx'_pos : 0 < π - x := by linarith
    have hx'_half : π - x ≤ π / 2 := by linarith
    -- sin x = sin(π - x) and the parabola is symmetric
    have sin_sym : sin x = sin (π - x) := by rw [sin_pi_sub]
    have parab_sym : (4 / π^2) * x * (π - x) = (4 / π^2) * (π - x) * x := by ring
    rw [sin_sym, parab_sym]
    -- Now apply the first half case to π - x
    by_cases hx'_small : π - x ≤ 0.6
    · have h1 : sin (π - x) ≤ π - x := sin_le (le_of_lt hx'_pos)
      have h2 : (4 / π^2) * x ≥ 1 := by
        have hpi_lo : π > 3.14 := pi_gt_d2
        have hpi_hi : π < 3.15 := pi_lt_d2
        have h3 : x > π / 2 := hx_half
        have h4 : x > 1.5 := by linarith
        have h5 : π^2 < 10 := by nlinarith
        have h6 : 4 / π^2 > 4 / 10 := by
          apply div_lt_div_of_pos_left (by norm_num : (0:ℝ) < 4) (by positivity) h5
        nlinarith
      have step1 : (π - x) = (π - x) * 1 := by ring
      have step2 : (π - x) * 1 ≤ (π - x) * ((4 / π^2) * x) := by nlinarith [hx'_pos]
      have step3 : (π - x) * ((4 / π^2) * x) = (4 / π^2) * (π - x) * x := by ring
      linarith
    · push_neg at hx'_small
      have h_at_pi_half : (4 / π^2) * (π/2) * (π - π/2) = 1 := by
        have eq1 : π - π/2 = π/2 := by ring
        rw [eq1]
        field_simp
        ring
      rcases eq_or_lt_of_le hx'_half with hx'_eq | hx'_lt_half
      · -- π - x = π/2, i.e., x = π/2
        have : x = π / 2 := by linarith
        linarith
      · -- π - x < π/2
        by_cases hx'_mid : π - x ≤ π - π^2/4
        · have h1 : sin (π - x) ≤ π - x := sin_le (le_of_lt hx'_pos)
          have h2 : 1 ≤ (4 / π^2) * x := by
            have hkey : x ≥ π^2/4 := by linarith
            have h_rw : (4 / π^2) * (π^2/4) = 1 := by field_simp
            have h_mono : (4 / π^2) * x ≥ (4 / π^2) * (π^2/4) := by
              apply mul_le_mul_of_nonneg_left hkey
              positivity
            linarith
          have step1 : (π - x) = (π - x) * 1 := by ring
          have step2 : (π - x) * 1 ≤ (π - x) * ((4 / π^2) * x) := by nlinarith [hx'_pos]
          have step3 : (π - x) * ((4 / π^2) * x) = (4 / π^2) * (π - x) * x := by ring
          linarith
        · push_neg at hx'_mid
          -- π - x ∈ (π - π²/4, π/2)
          set y := π/2 - (π - x) with hy_def
          have hy_pos : 0 < y := by linarith
          have hy_small : y < π^2/4 - π/2 := by linarith
          have hpi_hi : π < 3.15 := pi_lt_d2
          have hpi_lo : π > 3.14 := pi_gt_d2
          have hy_bound : y < 0.91 := by nlinarith
          have hy_le_1 : y ≤ 1 := by linarith
          have habs_y : |y| ≤ 1 := by rw [abs_of_nonneg (le_of_lt hy_pos)]; linarith

          have sin_eq : sin (π - x) = cos y := by
            have h1 : π - x = π/2 - y := by linarith
            rw [h1, sin_pi_div_two_sub]

          have cos_bound' := cos_bound habs_y
          have hcos := abs_sub_le_iff.1 cos_bound'
          rw [abs_of_nonneg (le_of_lt hy_pos)] at hcos
          have cos_upper : cos y ≤ 1 - y^2/2 + y^4 * (5/96) := by linarith [hcos.1]

          have parab_eq : (4 / π^2) * (π - x) * x = 1 - 4 * y^2 / π^2 := by
            have h1 : π - x = π/2 - y := by linarith
            have h2 : x = π/2 + y := by linarith
            rw [h1, h2]
            field_simp
            ring

          have key : cos y ≤ 1 - 4 * y^2 / π^2 := by
            have h1 : 4 / π^2 < 4 / 3.14^2 := by
              apply div_lt_div_of_pos_left (by norm_num : (0:ℝ) < 4)
              · norm_num
              · nlinarith
            have h2 : (4:ℝ) / 3.14^2 < 0.406 := by norm_num
            have h3 : (1:ℝ)/2 - 4/π^2 > 1/2 - 0.406 := by linarith
            have h5 : y^2 * (5/96) < 0.91^2 * (5/96) := by nlinarith [sq_nonneg y]
            have h6 : (0.91:ℝ)^2 * (5/96) < 0.044 := by norm_num
            have ineq1 : y^2 * (5/96) < 1/2 - 4/π^2 := by linarith
            have h8 : y^2 * (y^2 * (5/96)) ≤ y^2 * (1/2 - 4/π^2) := by
              apply mul_le_mul_of_nonneg_left (le_of_lt ineq1)
              exact sq_nonneg y
            -- Need to show: 1 - y²/2 + y⁴ * (5/96) ≤ 1 - 4y²/π²
            -- Equivalent: y⁴ * (5/96) - y²/2 + 4y²/π² ≤ 0
            -- y²(y² * (5/96) - 1/2 + 4/π²) ≤ 0
            -- Since y² ≥ 0, need y² * (5/96) - 1/2 + 4/π² ≤ 0
            -- i.e., y² * (5/96) ≤ 1/2 - 4/π² which is ineq1
            have h9 : y^4 * (5/96) ≤ y^2 * (1/2 - 4/π^2) := by
              have eq1 : y^4 * (5/96) = y^2 * (y^2 * (5/96)) := by ring
              rw [eq1]
              exact h8
            have h10 : 1 - y^2/2 + y^4 * (5/96) ≤ 1 - 4*y^2/π^2 := by
              have rhs_expand : 1 - 4*y^2/π^2 = 1 - y^2/2 + y^2 * (1/2 - 4/π^2) := by ring
              rw [rhs_expand]
              linarith [h9]
            linarith [h10]

          rw [sin_eq, parab_eq]
          exact key

-- Lemma 4: The constant 4/π² is the least upper bound
lemma four_div_pi_sq_is_least_upper_bound (b : ℝ) (h : ∀ x ∈ Icc (0:ℝ) π, b * x * (π - x) ≥ sin x) :
    4 / π ^ 2 ≤ b := by
  -- At x = π/2: b * (π/2) * (π/2) ≥ sin(π/2) = 1
  -- b * π²/4 ≥ 1
  -- b ≥ 4/π²
  have hx : (π / 2 : ℝ) ∈ Icc (0:ℝ) π := ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have key := h (π / 2) hx
  have h1 : b * (π / 2) * (π - π / 2) ≥ 1 := by
    calc b * (π / 2) * (π - π / 2) ≥ sin (π / 2) := key
      _ = 1 := sin_pi_div_two
  have h2 : π - π / 2 = π / 2 := by ring
  rw [h2] at h1
  have h3 : b * (π / 2) * (π / 2) = b * (π^2 / 4) := by ring
  rw [h3] at h1
  have hpi2 : π^2 / 4 > 0 := by positivity
  -- b * (π²/4) ≥ 1 implies b ≥ 4/π²
  have h4 : 4 / π^2 ≤ b := by
    have eq1 : (4 : ℝ) / π^2 * (π^2 / 4) = 1 := by field_simp
    have h5 : (4 / π^2) * (π^2 / 4) ≤ b * (π^2 / 4) := by linarith
    have h6 : (4 / π^2) * (π^2 / 4) = 4 / π^2 * (π^2 / 4) := by ring
    nlinarith [hpi2]
  exact h4

theorem putnam_2025_a2 :
  IsGreatest {a : ℝ | ∀ x ∈ Icc 0 π, a * x * (π - x) ≤ sin x} (1 / π) ∧
  IsLeast {b : ℝ | ∀ x ∈ Icc 0 π, b * x * (π - x) ≥ sin x} (4 / π ^ 2) := by
  constructor
  · constructor
    · exact sin_ge_inv_pi_mul_quad
    · intro a ha
      exact inv_pi_is_greatest_lower_bound a ha
  · constructor
    · exact sin_le_four_div_pi_sq_mul_quad
    · intro b hb
      exact four_div_pi_sq_is_least_upper_bound b hb

#print axioms putnam_2025_a2
