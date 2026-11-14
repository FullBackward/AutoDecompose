import Mathlib
set_option backward.isDefEq.respectTransparency false

open EuclideanGeometry Complex

-- We work in the Euclidean plane `ℝ²` with the standard `L²` (Euclidean) norm.
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A point `P` lies in the open interior of the triangle `X Y Z`: it is a
strictly convex combination `P = α • X + β • Y + γ • Z` with `α, β, γ > 0` and
`α + β + γ = 1`. -/
def InsideTriangle (X Y Z P : Plane) : Prop :=
  ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧
    P = α • X + β • Y + γ • Z

/-- A point `P` lies inside the (proper) angle at vertex `Y` spanned by the rays
`Y X` and `Y Z`: writing `P - Y = s • (X - Y) + t • (Z - Y)`, one has `s > 0`
and `t > 0`. -/
def InsideAngle (X Y Z P : Plane) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ P - Y = s • (X - Y) + t • (Z - Y)

/-- `O` is the circumcentre of triangle `A K L`: it is equidistant from the three
vertices. (For a nondegenerate triangle such a point exists and is unique.) -/
def IsCircumcentre (A K L O : Plane) : Prop :=
  dist O A = dist O K ∧ dist O A = dist O L

/-- Fixed real-linear isometry `Plane ≃ₗᵢ[ℝ] ℂ`. -/
noncomputable def g := Complex.orthonormalBasisOneI.repr.symm

/-! ## Small algebra helpers. -/

/-- From `‖z‖ = ‖z - w‖` one gets `2 Re(conj z · w) = |w|²`. -/
theorem re_of_norm_eq (z w : ℂ) (h : ‖z‖ = ‖z - w‖) :
    2 * (starRingEnd ℂ z * w).re = Complex.normSq w := by
  have hsq : Complex.normSq z = Complex.normSq (z - w) := by
    rw [← Complex.sq_norm, ← Complex.sq_norm, h]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im] at hsq ⊢
  nlinarith [hsq]

/-- Real/imaginary coefficient matching for `↑A + ↑B·c = ↑A' + ↑B'·c` when
`c ∉ ℝ`. -/
theorem coeff_match (A B A' B' : ℝ) (c : ℂ) (hc : c.im ≠ 0)
    (h : (↑A + ↑B * c : ℂ) = ↑A' + ↑B' * c) : A = A' ∧ B = B' := by
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, zero_add, add_zero,
    zero_sub, sub_zero] at him hre
  have hB : B = B' := by
    have hz : (B - B') * c.im = 0 := by linear_combination him
    rcases mul_eq_zero.mp hz with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hc
  refine ⟨?_, hB⟩
  rw [hB] at hre
  linarith [hre]

/-- (F1) ⇒ the two normalized midpoint distances are equal.
Proof pasted from `scratch/distance_bridge.lean`. -/
theorem distance_bridge (c o : ℂ)
    (hF1 : 2 * (starRingEnd ℂ o * (c - 1)).re = (Complex.normSq c - 1) / 2) :
    dist o (1/2 : ℂ) = dist o (c/2) := by
  have hsq : Complex.normSq (o - 1/2) = Complex.normSq (o - c/2) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.div_re, Complex.div_im, Complex.one_re, Complex.one_im,
      Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_apply] at *
    nlinarith [hF1]
  rw [Complex.dist_eq, Complex.dist_eq, Complex.norm_def, Complex.norm_def, hsq]

/-- Determinant nonvanishing: from the two strict cone inequalities, the 2x2
determinant of (K-A, L-A) in the affine basis is nonzero.
Proof pasted from `scratch/akl_noncollinear.lean`. -/
theorem akl_noncollinear
    (x g0 p y : ℝ)
    (hx : 0 < x) (hg : 0 < g0) (hp : 0 < p) (hy : 0 < y)
    (hB : (1 - x) * y > g0 * (1 - p))
    (hC : x * (1 - y) > p * (1 - g0)) :
    x * y - g0 * p ≠ 0 := by
  intro h
  have hx' := hx
  have hg' := hg
  have hxy : x * y = g0 * p := by linarith
  have hyg : y > g0 := by nlinarith [hB, hxy]
  have hxp : x > p := by nlinarith [hC, hxy]
  nlinarith [mul_pos (sub_pos.mpr hxp) hy, mul_pos hp (sub_pos.mpr hyg), hxy, hx', hg']

/-- (F1): from the circumcentre equations (hOk,hOl), the algebra certificate (hC),
and Δ = [k,l] ≠ 0, derive 2 Re(ō(c-1)) = (|c|²-1)/2. Here [u,v] := (conj u * v).im.
Proof pasted from `scratch/circumcenter_determinant.lean`. -/
theorem circumcenter_determinant
    (c k l o : ℂ)
    (hΔ : (starRingEnd ℂ k * l).im ≠ 0)
    (hC : 2 * ((starRingEnd ℂ (c-1) * l).im) * Complex.normSq k
        + 2 * ((starRingEnd ℂ k * (c-1)).im) * Complex.normSq l
        - (Complex.normSq c - 1) * (starRingEnd ℂ k * l).im = 0)
    (hOk : 2 * (starRingEnd ℂ o * k).re = Complex.normSq k)
    (hOl : 2 * (starRingEnd ℂ o * l).re = Complex.normSq l) :
    2 * (starRingEnd ℂ o * (c-1)).re = (Complex.normSq c - 1) / 2 := by
  have key : 2 * (starRingEnd ℂ o * (c-1)).re * (starRingEnd ℂ k * l).im
      = ((Complex.normSq c - 1) / 2) * (starRingEnd ℂ k * l).im := by
    obtain ⟨cr, ci⟩ := c
    obtain ⟨kr, ki⟩ := k
    obtain ⟨lr, li⟩ := l
    obtain ⟨oR, oI⟩ := o
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, map_sub] at *
    linear_combination (1/2) * hC
      + ((cr - 1) * li - ci * lr) * hOk
      + (kr * ci - ki * (cr - 1)) * hOl
  have := mul_right_cancel₀ hΔ key
  linarith [this]

/-! ## The algebra certificate (proven). -/

set_option maxHeartbeats 4000000 in
set_option linter.unusedVariables false in
theorem algebra_certificate
    (a b γ r s lam rho : ℝ) (c k l ℓ : ℂ)
    (hab : a + b < Real.pi) (hag : a + γ < Real.pi) (ha : 0 < a) (hb : 0 < b) (hg : 0 < γ)
    (hr : 2 * r * Real.sin (a + γ) = Real.sin γ) (hs : 2 * s * Real.sin (a + b) = Real.sin b)
    (hℓ : ℓ = 1 - s * Complex.exp (a * Complex.I))
    (hk : k = 1 - r * Complex.exp (-a * Complex.I))
    (hlc : l = ℓ * c)
    (hl2 : l = 1 - lam * Complex.exp (-(a + b) * Complex.I))
    (hk2 : k = c * (1 - rho * Complex.exp ((a + γ) * Complex.I))) :
    2 * ((starRingEnd ℂ (c - 1) * l).im) * Complex.normSq k
    + 2 * ((starRingEnd ℂ k * (c - 1)).im) * Complex.normSq l
    - (Complex.normSq c - 1) * (starRingEnd ℂ k * l).im = 0 := by
  set X := Complex.exp (a * Complex.I) with hXdef
  set Y := Complex.exp (b * Complex.I) with hYdef
  set Z := Complex.exp (γ * Complex.I) with hZdef
  -- sine bridge
  have hsin : ∀ θ : ℝ, Complex.exp (θ * Complex.I) - Complex.exp (-(θ * Complex.I))
      = 2 * Complex.I * (Real.sin θ : ℂ) := by
    intro θ
    have hc : Complex.exp (-(θ * Complex.I)) = starRingEnd ℂ (Complex.exp (θ * Complex.I)) := by
      rw [← Complex.exp_conj]; congr 1
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
    rw [hc, Complex.sub_conj, Complex.exp_ofReal_mul_I_im]; push_cast; ring
  -- conjugates of the unit roots
  have hXc : starRingEnd ℂ X = Complex.exp (-a * Complex.I) := by
    rw [hXdef, ← Complex.exp_conj]; congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  have hYc : starRingEnd ℂ Y = Complex.exp (-(b * Complex.I)) := by
    rw [hYdef, ← Complex.exp_conj]; congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  have hZc : starRingEnd ℂ Z = Complex.exp (-(γ * Complex.I)) := by
    rw [hZdef, ← Complex.exp_conj]; congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  -- products of unit roots
  have hXZ : Complex.exp ((a + γ) * Complex.I) = X * Z := by
    rw [hXdef, hZdef, ← Complex.exp_add]; congr 1; ring
  have hXY : Complex.exp ((a + b) * Complex.I) = X * Y := by
    rw [hXdef, hYdef, ← Complex.exp_add]; congr 1; ring
  have hXYc : Complex.exp (-(a + b) * Complex.I) = starRingEnd ℂ X * starRingEnd ℂ Y := by
    rw [hXc, hYc, ← Complex.exp_add]; congr 1; ring
  have hXZi : starRingEnd ℂ X * starRingEnd ℂ Z = Complex.exp (-((a + γ) * Complex.I)) := by
    rw [hXc, hZc, ← Complex.exp_add]; congr 1; ring
  have hXYi : starRingEnd ℂ X * starRingEnd ℂ Y = Complex.exp (-((a + b) * Complex.I)) := by
    rw [hXc, hYc, ← Complex.exp_add]; congr 1; ring
  -- unit relation
  have huX : X * starRingEnd ℂ X = 1 := by
    rw [hXc, hXdef, ← Complex.exp_add,
        show (a * Complex.I + -a * Complex.I : ℂ) = 0 by ring, Complex.exp_zero]
  -- normalise hypotheses to the unit-root atoms
  rw [← hXc] at hk
  rw [hXZ] at hk2
  rw [hXYc] at hl2
  -- coordinate relations
  have hg1 : (1 - (r:ℂ)*(starRingEnd ℂ X)) = c*(1 - (rho:ℂ)*(X*Z)) := by
    rw [← hk]; exact hk2
  have hg2 : (1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y))) = c*(1 - (s:ℂ)*X) := by
    rw [← hl2, hlc, hℓ]; ring
  have hg3 : (1 - (r:ℂ)*X) = (starRingEnd ℂ c)*(1 - (rho:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Z))) := by
    have h := congrArg (starRingEnd ℂ) hg1
    simpa only [map_sub, map_mul, map_one, Complex.conj_ofReal, Complex.conj_conj] using h
  have hg4 : (1 - (lam:ℂ)*(X*Y)) = (starRingEnd ℂ c)*(1 - (s:ℂ)*(starRingEnd ℂ X)) := by
    have h := congrArg (starRingEnd ℂ) hg2
    simpa only [map_sub, map_mul, map_one, Complex.conj_ofReal, Complex.conj_conj] using h
  -- sine residuals
  have keyg : X*Z - (starRingEnd ℂ X)*(starRingEnd ℂ Z) = 2*Complex.I*(Real.sin (a+γ):ℂ) := by
    have h := hsin (a+γ); simp only [Complex.ofReal_add] at h; rw [hXZ, ← hXZi] at h; exact h
  have keyb : X*Y - (starRingEnd ℂ X)*(starRingEnd ℂ Y) = 2*Complex.I*(Real.sin (a+b):ℂ) := by
    have h := hsin (a+b); simp only [Complex.ofReal_add] at h; rw [hXY, ← hXYi] at h; exact h
  have hZsin : Z - (starRingEnd ℂ Z) = 2*Complex.I*(Real.sin γ:ℂ) := by
    have h := hsin γ; rw [← hZdef, ← hZc] at h; exact h
  have hYsin : Y - (starRingEnd ℂ Y) = 2*Complex.I*(Real.sin b:ℂ) := by
    have h := hsin b; rw [← hYdef, ← hYc] at h; exact h
  have hRg : 2*(r:ℂ)*(X*Z - (starRingEnd ℂ X)*(starRingEnd ℂ Z)) = Z - (starRingEnd ℂ Z) := by
    rw [keyg, hZsin]
    have hr' : 2*(r:ℂ)*(Real.sin (a+γ):ℂ) = (Real.sin γ:ℂ) := by exact_mod_cast hr
    linear_combination (2*Complex.I) * hr'
  have hRb : 2*(s:ℂ)*(X*Y - (starRingEnd ℂ X)*(starRingEnd ℂ Y)) = Y - (starRingEnd ℂ Y) := by
    rw [keyb, hYsin]
    have hs' : 2*(s:ℂ)*(Real.sin (a+b):ℂ) = (Real.sin b:ℂ) := by exact_mod_cast hs
    linear_combination (2*Complex.I) * hs'
  -- THE certificate identity
  have KEY : (1 - (rho:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Z)))*(1 - (rho:ℂ)*(X*Z))*((2*((starRingEnd ℂ c)-1)*(1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))*((1 - (r:ℂ)*(starRingEnd ℂ X))*(1 - (r:ℂ)*X)) + 2*(1 - (r:ℂ)*X)*(c-1)*((1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))*(1 - (lam:ℂ)*(X*Y))) - (c*(starRingEnd ℂ c)-1)*((1 - (r:ℂ)*X)*(1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y))))) - (2*(c-1)*(1 - (lam:ℂ)*(X*Y))*((1 - (r:ℂ)*(starRingEnd ℂ X))*(1 - (r:ℂ)*X)) + 2*(1 - (r:ℂ)*(starRingEnd ℂ X))*((starRingEnd ℂ c)-1)*((1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))*(1 - (lam:ℂ)*(X*Y))) - (c*(starRingEnd ℂ c)-1)*((1 - (r:ℂ)*(starRingEnd ℂ X))*(1 - (lam:ℂ)*(X*Y))))) = 0 := by
    linear_combination (-2*(lam:ℂ)^2*(rho:ℂ)*(r:ℂ)*X^2*(starRingEnd ℂ X)^2*Y*(starRingEnd ℂ Y)*(starRingEnd ℂ Z) + 2*(lam:ℂ)^2*(rho:ℂ)*X*(starRingEnd ℂ X)^2*Y*(starRingEnd ℂ Y)*(starRingEnd ℂ Z) + 2*(lam:ℂ)^2*(r:ℂ)*X^2*(starRingEnd ℂ X)*Y*(starRingEnd ℂ Y) - 2*(lam:ℂ)^2*X*(starRingEnd ℂ X)*Y*(starRingEnd ℂ Y) + 4*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^2*(s:ℂ)*X*Y*(starRingEnd ℂ Z) + 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^2*X^2*(starRingEnd ℂ X)^2*Y*(starRingEnd ℂ Z) - 4*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^2*Y*(starRingEnd ℂ Z) - 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)*(s:ℂ)*X^2*Y*(starRingEnd ℂ Z) - 4*(lam:ℂ)*(rho:ℂ)*(r:ℂ)*(s:ℂ)*X*(starRingEnd ℂ X)*Y*(starRingEnd ℂ Z) + (lam:ℂ)*(rho:ℂ)*(r:ℂ)*X*(starRingEnd ℂ X)^2*Y*(starRingEnd ℂ Z)*(starRingEnd ℂ c) - 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)*X*(starRingEnd ℂ X)^2*Y*(starRingEnd ℂ Z) - (lam:ℂ)*(rho:ℂ)*(r:ℂ)*X*(starRingEnd ℂ X)^2*(starRingEnd ℂ Y)*(starRingEnd ℂ Z)*(starRingEnd ℂ c) + 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)*X*(starRingEnd ℂ X)^2*(starRingEnd ℂ Y)*(starRingEnd ℂ Z) + 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)*X*Y*(starRingEnd ℂ Z) + 4*(lam:ℂ)*(rho:ℂ)*(r:ℂ)*(starRingEnd ℂ X)*Y*(starRingEnd ℂ Z) + 2*(lam:ℂ)*(rho:ℂ)*(s:ℂ)*X*Y*(starRingEnd ℂ Z) - (lam:ℂ)*(rho:ℂ)*X*(starRingEnd ℂ X)*Y*(starRingEnd ℂ Z)*(starRingEnd ℂ c) + (lam:ℂ)*(rho:ℂ)*(starRingEnd ℂ X)^2*(starRingEnd ℂ Y)*(starRingEnd ℂ Z)*(starRingEnd ℂ c) - 2*(lam:ℂ)*(rho:ℂ)*(starRingEnd ℂ X)^2*(starRingEnd ℂ Y)*(starRingEnd ℂ Z) - 2*(lam:ℂ)*(rho:ℂ)*Y*(starRingEnd ℂ Z) - 2*(lam:ℂ)*(r:ℂ)^2*(s:ℂ)*X^2*Y - 2*(lam:ℂ)*(r:ℂ)^2*X^2*(starRingEnd ℂ X)*Y + 2*(lam:ℂ)*(r:ℂ)^2*X*Y + 2*(lam:ℂ)*(r:ℂ)*(s:ℂ)*X*Y - (lam:ℂ)*(r:ℂ)*X*(starRingEnd ℂ X)*Y*(starRingEnd ℂ c) + 2*(lam:ℂ)*(r:ℂ)*X*(starRingEnd ℂ X)*Y + (lam:ℂ)*(r:ℂ)*X*(starRingEnd ℂ X)*(starRingEnd ℂ Y)*(starRingEnd ℂ c) - 2*(lam:ℂ)*(r:ℂ)*X*(starRingEnd ℂ X)*(starRingEnd ℂ Y) - 2*(lam:ℂ)*(r:ℂ)*Y + (lam:ℂ)*X*Y*(starRingEnd ℂ c) - (lam:ℂ)*(starRingEnd ℂ X)*(starRingEnd ℂ Y)*(starRingEnd ℂ c) + 2*(lam:ℂ)*(starRingEnd ℂ X)*(starRingEnd ℂ Y) - 2*(rho:ℂ)*(r:ℂ)^2*(s:ℂ)*X*(starRingEnd ℂ X)*(starRingEnd ℂ Z) - 2*(rho:ℂ)*(r:ℂ)^2*X*(starRingEnd ℂ X)^2*(starRingEnd ℂ Z) + 2*(rho:ℂ)*(r:ℂ)^2*(starRingEnd ℂ X)*(starRingEnd ℂ Z) + 2*(rho:ℂ)*(r:ℂ)*(s:ℂ)*X*(starRingEnd ℂ X)^2*(starRingEnd ℂ Z) + (rho:ℂ)*(r:ℂ)*(s:ℂ)*X*(starRingEnd ℂ Z) + (rho:ℂ)*(r:ℂ)*X*(starRingEnd ℂ X)*(starRingEnd ℂ Z)*(starRingEnd ℂ c) - (rho:ℂ)*(r:ℂ)*(starRingEnd ℂ X)^2*(starRingEnd ℂ Z)*(starRingEnd ℂ c) - (rho:ℂ)*(r:ℂ)*(starRingEnd ℂ Z) - (rho:ℂ)*(s:ℂ)*X*(starRingEnd ℂ X)*(starRingEnd ℂ Z) + (rho:ℂ)*(starRingEnd ℂ X)*(starRingEnd ℂ Z) + (r:ℂ)^2*(s:ℂ)*X + 2*(r:ℂ)^2*X*(starRingEnd ℂ X) - (r:ℂ)^2 - (r:ℂ)*(s:ℂ)*X*(starRingEnd ℂ X) - (r:ℂ)*X*(starRingEnd ℂ c) + (r:ℂ)*(starRingEnd ℂ X)*(starRingEnd ℂ c) - (r:ℂ)*(starRingEnd ℂ X)) * hg1 + (-4*(lam:ℂ)*(rho:ℂ)^2*(r:ℂ)^2*X*Y*Z*(starRingEnd ℂ Z) + 2*(lam:ℂ)*(rho:ℂ)^2*(r:ℂ)*X^2*Y*Z*(starRingEnd ℂ Z) + 4*(lam:ℂ)*(rho:ℂ)^2*(r:ℂ)*X*(starRingEnd ℂ X)*Y*Z*(starRingEnd ℂ Z) - 2*(lam:ℂ)*(rho:ℂ)^2*X*Y*Z*(starRingEnd ℂ Z) + 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^2*X^2*Y*Z + 4*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^2*Y*(starRingEnd ℂ Z) - 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)*X*Y*Z - 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)*X*Y*(starRingEnd ℂ Z) - 4*(lam:ℂ)*(rho:ℂ)*(r:ℂ)*(starRingEnd ℂ X)*Y*(starRingEnd ℂ Z) + 2*(lam:ℂ)*(rho:ℂ)*Y*(starRingEnd ℂ Z) - 2*(lam:ℂ)*(r:ℂ)^2*X*Y + 2*(lam:ℂ)*(r:ℂ)*Y + 2*(rho:ℂ)^2*(r:ℂ)^2*X*(starRingEnd ℂ X)*Z*(starRingEnd ℂ Z) - 2*(rho:ℂ)^2*(r:ℂ)*X*(starRingEnd ℂ X)^2*Z*(starRingEnd ℂ Z) - (rho:ℂ)^2*(r:ℂ)*X*Z*(starRingEnd ℂ Z) + (rho:ℂ)^2*X*(starRingEnd ℂ X)*Z*(starRingEnd ℂ Z) - (rho:ℂ)*(r:ℂ)^2*X*Z - 2*(rho:ℂ)*(r:ℂ)^2*(starRingEnd ℂ X)*(starRingEnd ℂ Z) + (rho:ℂ)*(r:ℂ)*X*(starRingEnd ℂ X)*Z + 2*(rho:ℂ)*(r:ℂ)*(starRingEnd ℂ X)^2*(starRingEnd ℂ Z) + (rho:ℂ)*(r:ℂ)*(starRingEnd ℂ Z) - (rho:ℂ)*(starRingEnd ℂ X)*(starRingEnd ℂ Z) + (r:ℂ)^2 - (r:ℂ)*(starRingEnd ℂ X)) * hg2 + (2*(lam:ℂ)^2*(rho:ℂ)*(r:ℂ)*X^2*(starRingEnd ℂ X)^2*Y*(starRingEnd ℂ Y)*Z - 2*(lam:ℂ)^2*(rho:ℂ)*X^2*(starRingEnd ℂ X)*Y*(starRingEnd ℂ Y)*Z - 2*(lam:ℂ)^2*(r:ℂ)*X*(starRingEnd ℂ X)^2*Y*(starRingEnd ℂ Y) + 2*(lam:ℂ)^2*X*(starRingEnd ℂ X)*Y*(starRingEnd ℂ Y) - 4*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^2*(s:ℂ)*(starRingEnd ℂ X)*(starRingEnd ℂ Y)*Z - 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^2*X^2*(starRingEnd ℂ X)^2*(starRingEnd ℂ Y)*Z + 4*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^2*(starRingEnd ℂ Y)*Z + 4*(lam:ℂ)*(rho:ℂ)*(r:ℂ)*(s:ℂ)*X*(starRingEnd ℂ X)*(starRingEnd ℂ Y)*Z + 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)*(s:ℂ)*(starRingEnd ℂ X)^2*(starRingEnd ℂ Y)*Z - 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)*X^2*(starRingEnd ℂ X)*Y*Z + 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)*X^2*(starRingEnd ℂ X)*(starRingEnd ℂ Y)*Z - 4*(lam:ℂ)*(rho:ℂ)*(r:ℂ)*X*(starRingEnd ℂ Y)*Z - 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)*(starRingEnd ℂ X)*(starRingEnd ℂ Y)*Z - 2*(lam:ℂ)*(rho:ℂ)*(s:ℂ)*(starRingEnd ℂ X)*(starRingEnd ℂ Y)*Z + 2*(lam:ℂ)*(rho:ℂ)*X^2*Y*Z + 2*(lam:ℂ)*(rho:ℂ)*(starRingEnd ℂ Y)*Z + 2*(lam:ℂ)*(r:ℂ)^2*(s:ℂ)*(starRingEnd ℂ X)^2*(starRingEnd ℂ Y) + (lam:ℂ)*(r:ℂ)^2*X*(starRingEnd ℂ X)^2*Y + (lam:ℂ)*(r:ℂ)^2*X*(starRingEnd ℂ X)^2*(starRingEnd ℂ Y) - 2*(lam:ℂ)*(r:ℂ)^2*(starRingEnd ℂ X)*(starRingEnd ℂ Y) - 2*(lam:ℂ)*(r:ℂ)*(s:ℂ)*(starRingEnd ℂ X)*(starRingEnd ℂ Y) - (lam:ℂ)*(r:ℂ)*X*(starRingEnd ℂ X)*(starRingEnd ℂ Y) + (lam:ℂ)*(r:ℂ)*(starRingEnd ℂ X)^2*(starRingEnd ℂ Y) + 2*(lam:ℂ)*(r:ℂ)*(starRingEnd ℂ Y) - (lam:ℂ)*X*Y - (lam:ℂ)*(starRingEnd ℂ X)*(starRingEnd ℂ Y) + 2*(rho:ℂ)*(r:ℂ)^2*(s:ℂ)*X*(starRingEnd ℂ X)*Z + 2*(rho:ℂ)*(r:ℂ)^2*X^2*(starRingEnd ℂ X)*Z - 2*(rho:ℂ)*(r:ℂ)^2*X*Z - 2*(rho:ℂ)*(r:ℂ)*(s:ℂ)*X^2*(starRingEnd ℂ X)*Z - (rho:ℂ)*(r:ℂ)*(s:ℂ)*(starRingEnd ℂ X)*Z + (rho:ℂ)*(r:ℂ)*Z + (rho:ℂ)*(s:ℂ)*X*(starRingEnd ℂ X)*Z - (rho:ℂ)*X*Z - (r:ℂ)^2*(s:ℂ)*(starRingEnd ℂ X) - (r:ℂ)^2*X*(starRingEnd ℂ X) - (r:ℂ)^2*(starRingEnd ℂ X)^2 + (r:ℂ)^2 + (r:ℂ)*(s:ℂ)*X*(starRingEnd ℂ X) + (r:ℂ)*(starRingEnd ℂ X)) * hg3 + (4*(lam:ℂ)*(rho:ℂ)^2*(r:ℂ)^2*(starRingEnd ℂ X)*(starRingEnd ℂ Y)*Z*(starRingEnd ℂ Z) - 4*(lam:ℂ)*(rho:ℂ)^2*(r:ℂ)*X*(starRingEnd ℂ X)*(starRingEnd ℂ Y)*Z*(starRingEnd ℂ Z) - 2*(lam:ℂ)*(rho:ℂ)^2*(r:ℂ)*(starRingEnd ℂ X)^2*(starRingEnd ℂ Y)*Z*(starRingEnd ℂ Z) + 2*(lam:ℂ)*(rho:ℂ)^2*(starRingEnd ℂ X)*(starRingEnd ℂ Y)*Z*(starRingEnd ℂ Z) - 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^2*(starRingEnd ℂ X)^2*(starRingEnd ℂ Y)*(starRingEnd ℂ Z) - 4*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^2*(starRingEnd ℂ Y)*Z + 4*(lam:ℂ)*(rho:ℂ)*(r:ℂ)*X*(starRingEnd ℂ Y)*Z + 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)*(starRingEnd ℂ X)*(starRingEnd ℂ Y)*Z + 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)*(starRingEnd ℂ X)*(starRingEnd ℂ Y)*(starRingEnd ℂ Z) - 2*(lam:ℂ)*(rho:ℂ)*(starRingEnd ℂ Y)*Z + 2*(lam:ℂ)*(r:ℂ)^2*(starRingEnd ℂ X)*(starRingEnd ℂ Y) - 2*(lam:ℂ)*(r:ℂ)*(starRingEnd ℂ Y) - 2*(rho:ℂ)^2*(r:ℂ)^2*X*(starRingEnd ℂ X)*Z*(starRingEnd ℂ Z) + 2*(rho:ℂ)^2*(r:ℂ)*X^2*(starRingEnd ℂ X)*Z*(starRingEnd ℂ Z) + (rho:ℂ)^2*(r:ℂ)*(starRingEnd ℂ X)*Z*(starRingEnd ℂ Z) - (rho:ℂ)^2*X*(starRingEnd ℂ X)*Z*(starRingEnd ℂ Z) + 2*(rho:ℂ)*(r:ℂ)^2*X*Z + (rho:ℂ)*(r:ℂ)^2*(starRingEnd ℂ X)*(starRingEnd ℂ Z) - 2*(rho:ℂ)*(r:ℂ)*X^2*Z - (rho:ℂ)*(r:ℂ)*X*(starRingEnd ℂ X)*(starRingEnd ℂ Z) - (rho:ℂ)*(r:ℂ)*Z + (rho:ℂ)*X*Z - (r:ℂ)^2 + (r:ℂ)*X) * hg4 + (-2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^2*(s:ℂ)*(starRingEnd ℂ X)*(starRingEnd ℂ Y) + (lam:ℂ)*(rho:ℂ)*(r:ℂ)^2*(starRingEnd ℂ Y) + 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)*(s:ℂ)*(starRingEnd ℂ X)^2*(starRingEnd ℂ Y) + 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)*(s:ℂ)*(starRingEnd ℂ Y) - (lam:ℂ)*(rho:ℂ)*(r:ℂ)*X*(starRingEnd ℂ Y) - (lam:ℂ)*(rho:ℂ)*(r:ℂ)*(starRingEnd ℂ X)*(starRingEnd ℂ Y) - 2*(lam:ℂ)*(rho:ℂ)*(s:ℂ)*(starRingEnd ℂ X)*(starRingEnd ℂ Y) + (lam:ℂ)*(rho:ℂ)*(starRingEnd ℂ Y) + (rho:ℂ)*(r:ℂ)^2*(s:ℂ) - (rho:ℂ)*(r:ℂ)*(s:ℂ)*X - (rho:ℂ)*(r:ℂ)*(s:ℂ)*(starRingEnd ℂ X) + (rho:ℂ)*(s:ℂ)) * hRg + (2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^3*(starRingEnd ℂ X)*(starRingEnd ℂ Z) - 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^2*(starRingEnd ℂ X)^2*(starRingEnd ℂ Z) - 3*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^2*(starRingEnd ℂ Z) + (lam:ℂ)*(rho:ℂ)*(r:ℂ)*X*(starRingEnd ℂ Z) + 3*(lam:ℂ)*(rho:ℂ)*(r:ℂ)*(starRingEnd ℂ X)*(starRingEnd ℂ Z) - (lam:ℂ)*(rho:ℂ)*(starRingEnd ℂ Z) - (lam:ℂ)*(r:ℂ)^3 + (lam:ℂ)*(r:ℂ)^2*X + (lam:ℂ)*(r:ℂ)^2*(starRingEnd ℂ X) - (lam:ℂ)*(r:ℂ)) * hRb + (2*(lam:ℂ)^2*(rho:ℂ)^2*(r:ℂ)*X^2*(starRingEnd ℂ X)*Y*(starRingEnd ℂ Y)*Z*(starRingEnd ℂ Z) - 2*(lam:ℂ)^2*(rho:ℂ)^2*(r:ℂ)*X*(starRingEnd ℂ X)^2*Y*(starRingEnd ℂ Y)*Z*(starRingEnd ℂ Z) + 2*(lam:ℂ)^2*(rho:ℂ)*(r:ℂ)^2*X^2*(starRingEnd ℂ X)*Y*(starRingEnd ℂ Y)*Z - 2*(lam:ℂ)^2*(rho:ℂ)*(r:ℂ)^2*X*(starRingEnd ℂ X)^2*Y*(starRingEnd ℂ Y)*(starRingEnd ℂ Z) + 4*(lam:ℂ)^2*(rho:ℂ)*(r:ℂ)^2*X*Y*(starRingEnd ℂ Y)*Z - 4*(lam:ℂ)^2*(rho:ℂ)*(r:ℂ)^2*(starRingEnd ℂ X)*Y*(starRingEnd ℂ Y)*(starRingEnd ℂ Z) - 4*(lam:ℂ)^2*(rho:ℂ)*(r:ℂ)*X^2*Y*(starRingEnd ℂ Y)*Z + 4*(lam:ℂ)^2*(rho:ℂ)*(r:ℂ)*(starRingEnd ℂ X)^2*Y*(starRingEnd ℂ Y)*(starRingEnd ℂ Z) + 2*(lam:ℂ)^2*(rho:ℂ)*X*Y*(starRingEnd ℂ Y)*Z - 2*(lam:ℂ)^2*(rho:ℂ)*(starRingEnd ℂ X)*Y*(starRingEnd ℂ Y)*(starRingEnd ℂ Z) + 2*(lam:ℂ)^2*(r:ℂ)*X*Y*(starRingEnd ℂ Y) - 2*(lam:ℂ)^2*(r:ℂ)*(starRingEnd ℂ X)*Y*(starRingEnd ℂ Y) - 2*(lam:ℂ)*(rho:ℂ)^2*(r:ℂ)^2*X^2*(starRingEnd ℂ X)*Y*Z*(starRingEnd ℂ Z) + 2*(lam:ℂ)*(rho:ℂ)^2*(r:ℂ)^2*X*(starRingEnd ℂ X)^2*(starRingEnd ℂ Y)*Z*(starRingEnd ℂ Z) - 4*(lam:ℂ)*(rho:ℂ)^2*(r:ℂ)^2*X*Y*Z*(starRingEnd ℂ Z) + 4*(lam:ℂ)*(rho:ℂ)^2*(r:ℂ)^2*(starRingEnd ℂ X)*(starRingEnd ℂ Y)*Z*(starRingEnd ℂ Z) + 2*(lam:ℂ)*(rho:ℂ)^2*(r:ℂ)*X^2*Y*Z*(starRingEnd ℂ Z) + 3*(lam:ℂ)*(rho:ℂ)^2*(r:ℂ)*X*(starRingEnd ℂ X)*Y*Z*(starRingEnd ℂ Z) - 3*(lam:ℂ)*(rho:ℂ)^2*(r:ℂ)*X*(starRingEnd ℂ X)*(starRingEnd ℂ Y)*Z*(starRingEnd ℂ Z) - 2*(lam:ℂ)*(rho:ℂ)^2*(r:ℂ)*(starRingEnd ℂ X)^2*(starRingEnd ℂ Y)*Z*(starRingEnd ℂ Z) - 2*(lam:ℂ)*(rho:ℂ)^2*X*Y*Z*(starRingEnd ℂ Z) + 2*(lam:ℂ)*(rho:ℂ)^2*(starRingEnd ℂ X)*(starRingEnd ℂ Y)*Z*(starRingEnd ℂ Z) - 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^3*X^2*(starRingEnd ℂ X)*(starRingEnd ℂ Y)*Z + 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^3*X*(starRingEnd ℂ X)^2*Y*(starRingEnd ℂ Z) - 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^3*X*(starRingEnd ℂ Y)*Z + 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^3*(starRingEnd ℂ X)*Y*(starRingEnd ℂ Z) - 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^2*(s:ℂ)*X*Y*(starRingEnd ℂ Z) + 4*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^2*(s:ℂ)*X*(starRingEnd ℂ Y)*Z - 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^2*(s:ℂ)*(starRingEnd ℂ X)*(starRingEnd ℂ Y)*Z + 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^2*X^2*(starRingEnd ℂ Y)*Z - 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^2*(starRingEnd ℂ X)^2*Y*(starRingEnd ℂ Z) + 3*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^2*Y*(starRingEnd ℂ Z) - (lam:ℂ)*(rho:ℂ)*(r:ℂ)^2*(starRingEnd ℂ Y)*Z - 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)^2*(starRingEnd ℂ Y)*(starRingEnd ℂ Z) - 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)*(s:ℂ)*(starRingEnd ℂ Y)*Z + 2*(lam:ℂ)*(rho:ℂ)*(r:ℂ)*(s:ℂ)*(starRingEnd ℂ Y)*(starRingEnd ℂ Z) - (lam:ℂ)*(rho:ℂ)*(r:ℂ)*X*Y*Z - (lam:ℂ)*(rho:ℂ)*(r:ℂ)*X*Y*(starRingEnd ℂ Z) + (lam:ℂ)*(rho:ℂ)*(r:ℂ)*X*(starRingEnd ℂ Y)*Z - (lam:ℂ)*(rho:ℂ)*(r:ℂ)*(starRingEnd ℂ X)*Y*(starRingEnd ℂ Z) + (lam:ℂ)*(rho:ℂ)*(r:ℂ)*(starRingEnd ℂ X)*(starRingEnd ℂ Y)*Z + (lam:ℂ)*(rho:ℂ)*(r:ℂ)*(starRingEnd ℂ X)*(starRingEnd ℂ Y)*(starRingEnd ℂ Z) + (lam:ℂ)*(rho:ℂ)*Y*(starRingEnd ℂ Z) - (lam:ℂ)*(rho:ℂ)*(starRingEnd ℂ Y)*Z - 2*(lam:ℂ)*(r:ℂ)^3*(s:ℂ)*X*Y + 2*(lam:ℂ)*(r:ℂ)^3*(s:ℂ)*(starRingEnd ℂ X)*(starRingEnd ℂ Y) - (lam:ℂ)*(r:ℂ)^3*X*(starRingEnd ℂ X)*Y + (lam:ℂ)*(r:ℂ)^3*X*(starRingEnd ℂ X)*(starRingEnd ℂ Y) + (lam:ℂ)*(r:ℂ)^3*Y - (lam:ℂ)*(r:ℂ)^3*(starRingEnd ℂ Y) - (lam:ℂ)*(r:ℂ)^2*X*(starRingEnd ℂ Y) + (lam:ℂ)*(r:ℂ)^2*(starRingEnd ℂ X)*Y + (lam:ℂ)*(r:ℂ)*Y - (lam:ℂ)*(r:ℂ)*(starRingEnd ℂ Y) - (rho:ℂ)^2*(r:ℂ)*X*Z*(starRingEnd ℂ Z) + (rho:ℂ)^2*(r:ℂ)*(starRingEnd ℂ X)*Z*(starRingEnd ℂ Z) + 2*(rho:ℂ)*(r:ℂ)^3*(s:ℂ)*X*Z - 2*(rho:ℂ)*(r:ℂ)^3*(s:ℂ)*(starRingEnd ℂ X)*(starRingEnd ℂ Z) + 2*(rho:ℂ)*(r:ℂ)^3*X^2*Z - 2*(rho:ℂ)*(r:ℂ)^3*(starRingEnd ℂ X)^2*(starRingEnd ℂ Z) - 2*(rho:ℂ)*(r:ℂ)^2*(s:ℂ)*X^2*Z + 2*(rho:ℂ)*(r:ℂ)^2*(s:ℂ)*(starRingEnd ℂ X)^2*(starRingEnd ℂ Z) - (rho:ℂ)*(r:ℂ)^2*(s:ℂ)*Z + (rho:ℂ)*(r:ℂ)^2*(s:ℂ)*(starRingEnd ℂ Z) - 2*(rho:ℂ)*(r:ℂ)^2*X*Z + 2*(rho:ℂ)*(r:ℂ)^2*(starRingEnd ℂ X)*(starRingEnd ℂ Z) + 3*(rho:ℂ)*(r:ℂ)*(s:ℂ)*X*Z - 3*(rho:ℂ)*(r:ℂ)*(s:ℂ)*(starRingEnd ℂ X)*(starRingEnd ℂ Z) - (rho:ℂ)*(s:ℂ)*Z + (rho:ℂ)*(s:ℂ)*(starRingEnd ℂ Z) - (r:ℂ)^3*X + (r:ℂ)^3*(starRingEnd ℂ X) + (r:ℂ)^2*(s:ℂ)*X - (r:ℂ)^2*(s:ℂ)*(starRingEnd ℂ X)) * huX
  -- conjugation of k,l for the bridge
  have hCkC : starRingEnd ℂ k = 1 - (r:ℂ)*X := by
    rw [hk]; simp only [map_sub, map_mul, map_one, Complex.conj_ofReal, Complex.conj_conj]
  have hClC : starRingEnd ℂ l = 1 - (lam:ℂ)*(X*Y) := by
    rw [hl2]; simp only [map_sub, map_mul, map_one, Complex.conj_ofReal, Complex.conj_conj]
  -- bridge:  Tc = TAx
  have hbridge : (↑(2 * Complex.normSq k) * (starRingEnd ℂ (c - 1) * l) + ↑(2 * Complex.normSq l) * (starRingEnd ℂ k * (c - 1)) - ↑(Complex.normSq c - 1) * (starRingEnd ℂ k * l)) = (2*((starRingEnd ℂ c)-1)*(1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))*((1 - (r:ℂ)*(starRingEnd ℂ X))*(1 - (r:ℂ)*X)) + 2*(1 - (r:ℂ)*X)*(c-1)*((1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))*(1 - (lam:ℂ)*(X*Y))) - (c*(starRingEnd ℂ c)-1)*((1 - (r:ℂ)*X)*(1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y))))) := by
    simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_ofNat,
               ← Complex.mul_conj]
    rw [hCkC, hClC, hk, hl2, map_sub, map_one]; ring
  -- goal LHS equals Tc.im
  have him_eq : ((↑(2 * Complex.normSq k) * (starRingEnd ℂ (c - 1) * l) + ↑(2 * Complex.normSq l) * (starRingEnd ℂ k * (c - 1)) - ↑(Complex.normSq c - 1) * (starRingEnd ℂ k * l))).im
      = 2 * ((starRingEnd ℂ (c - 1) * l).im) * Complex.normSq k
        + 2 * ((starRingEnd ℂ k * (c - 1)).im) * Complex.normSq l
        - (Complex.normSq c - 1) * (starRingEnd ℂ k * l).im := by
    simp only [Complex.add_im, Complex.sub_im, Complex.im_ofReal_mul]; ring
  -- so goal LHS = TAx.im
  have hbr : 2 * ((starRingEnd ℂ (c - 1) * l).im) * Complex.normSq k
        + 2 * ((starRingEnd ℂ k * (c - 1)).im) * Complex.normSq l
        - (Complex.normSq c - 1) * (starRingEnd ℂ k * l).im = ((2*((starRingEnd ℂ c)-1)*(1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))*((1 - (r:ℂ)*(starRingEnd ℂ X))*(1 - (r:ℂ)*X)) + 2*(1 - (r:ℂ)*X)*(c-1)*((1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))*(1 - (lam:ℂ)*(X*Y))) - (c*(starRingEnd ℂ c)-1)*((1 - (r:ℂ)*X)*(1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))))).im := by
    rw [← him_eq, hbridge]
  -- conj of TAx = cTAx, hence  TAx - cTAx = 2 I (TAx.im)
  have hsub : (2*((starRingEnd ℂ c)-1)*(1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))*((1 - (r:ℂ)*(starRingEnd ℂ X))*(1 - (r:ℂ)*X)) + 2*(1 - (r:ℂ)*X)*(c-1)*((1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))*(1 - (lam:ℂ)*(X*Y))) - (c*(starRingEnd ℂ c)-1)*((1 - (r:ℂ)*X)*(1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y))))) - (2*(c-1)*(1 - (lam:ℂ)*(X*Y))*((1 - (r:ℂ)*(starRingEnd ℂ X))*(1 - (r:ℂ)*X)) + 2*(1 - (r:ℂ)*(starRingEnd ℂ X))*((starRingEnd ℂ c)-1)*((1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))*(1 - (lam:ℂ)*(X*Y))) - (c*(starRingEnd ℂ c)-1)*((1 - (r:ℂ)*(starRingEnd ℂ X))*(1 - (lam:ℂ)*(X*Y)))) = 2*Complex.I*(((2*((starRingEnd ℂ c)-1)*(1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))*((1 - (r:ℂ)*(starRingEnd ℂ X))*(1 - (r:ℂ)*X)) + 2*(1 - (r:ℂ)*X)*(c-1)*((1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))*(1 - (lam:ℂ)*(X*Y))) - (c*(starRingEnd ℂ c)-1)*((1 - (r:ℂ)*X)*(1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))))).im : ℂ) := by
    have hconj : starRingEnd ℂ (2*((starRingEnd ℂ c)-1)*(1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))*((1 - (r:ℂ)*(starRingEnd ℂ X))*(1 - (r:ℂ)*X)) + 2*(1 - (r:ℂ)*X)*(c-1)*((1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))*(1 - (lam:ℂ)*(X*Y))) - (c*(starRingEnd ℂ c)-1)*((1 - (r:ℂ)*X)*(1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y))))) = (2*(c-1)*(1 - (lam:ℂ)*(X*Y))*((1 - (r:ℂ)*(starRingEnd ℂ X))*(1 - (r:ℂ)*X)) + 2*(1 - (r:ℂ)*(starRingEnd ℂ X))*((starRingEnd ℂ c)-1)*((1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))*(1 - (lam:ℂ)*(X*Y))) - (c*(starRingEnd ℂ c)-1)*((1 - (r:ℂ)*(starRingEnd ℂ X))*(1 - (lam:ℂ)*(X*Y)))) := by
      simp only [map_sub, map_add, map_mul, map_one, map_ofNat, Complex.conj_conj,
                 Complex.conj_ofReal]; ring
    rw [← hconj, Complex.sub_conj]; push_cast; ring
  -- FA * fA = normSq fA
  have hFAfA : (1 - (rho:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Z))) * (1 - (rho:ℂ)*(X*Z)) = (Complex.normSq (1 - (rho:ℂ)*(X*Z)) : ℂ) := by
    have hcf : starRingEnd ℂ (1 - (rho:ℂ)*(X*Z)) = (1 - (rho:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Z))) := by
      simp only [map_sub, map_mul, map_one, Complex.conj_ofReal]
    rw [← hcf, mul_comm]; exact Complex.mul_conj (1 - (rho:ℂ)*(X*Z))
  -- extract the real equation  normSq fA * TAx.im = 0
  have h0 : (Complex.normSq (1 - (rho:ℂ)*(X*Z)) : ℂ) * (2*Complex.I*(((2*((starRingEnd ℂ c)-1)*(1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))*((1 - (r:ℂ)*(starRingEnd ℂ X))*(1 - (r:ℂ)*X)) + 2*(1 - (r:ℂ)*X)*(c-1)*((1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))*(1 - (lam:ℂ)*(X*Y))) - (c*(starRingEnd ℂ c)-1)*((1 - (r:ℂ)*X)*(1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))))).im : ℂ)) = 0 := by
    rw [← hFAfA, ← hsub]; exact KEY
  have h2 : ((Complex.normSq (1 - (rho:ℂ)*(X*Z)) * ((2*((starRingEnd ℂ c)-1)*(1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))*((1 - (r:ℂ)*(starRingEnd ℂ X))*(1 - (r:ℂ)*X)) + 2*(1 - (r:ℂ)*X)*(c-1)*((1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))*(1 - (lam:ℂ)*(X*Y))) - (c*(starRingEnd ℂ c)-1)*((1 - (r:ℂ)*X)*(1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))))).im : ℝ) : ℂ) * (2*Complex.I) = 0 := by
    rw [← h0]; push_cast; ring
  have hxeq : Complex.normSq (1 - (rho:ℂ)*(X*Z)) * ((2*((starRingEnd ℂ c)-1)*(1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))*((1 - (r:ℂ)*(starRingEnd ℂ X))*(1 - (r:ℂ)*X)) + 2*(1 - (r:ℂ)*X)*(c-1)*((1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))*(1 - (lam:ℂ)*(X*Y))) - (c*(starRingEnd ℂ c)-1)*((1 - (r:ℂ)*X)*(1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))))).im = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact_mod_cast h
    · exact absurd h (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  -- finish
  by_cases hfz : Complex.normSq (1 - (rho:ℂ)*(X*Z)) = 0
  · have hf0 : ((1 - (rho:ℂ)*(X*Z)) : ℂ) = 0 := Complex.normSq_eq_zero.mp hfz
    have hk0 : k = 0 := by rw [hk, hg1, hf0, mul_zero]
    rw [hk0]; simp
  · have hTim : ((2*((starRingEnd ℂ c)-1)*(1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))*((1 - (r:ℂ)*(starRingEnd ℂ X))*(1 - (r:ℂ)*X)) + 2*(1 - (r:ℂ)*X)*(c-1)*((1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))*(1 - (lam:ℂ)*(X*Y))) - (c*(starRingEnd ℂ c)-1)*((1 - (r:ℂ)*X)*(1 - (lam:ℂ)*((starRingEnd ℂ X)*(starRingEnd ℂ Y)))))).im = 0 := by
      rcases mul_eq_zero.mp hxeq with h | h
      · exact absurd h hfz
      · exact h
    rw [hbr]; exact hTim

/-! ## The crux lemma. -/

/-- Global reflection `ρ : Plane ≃ₗᵢ[ℝ] Plane` with `g (ρ X) = conj (g X)`,
used to reduce the `c.im < 0` orientation to the positive branch. -/
noncomputable def ρ : Plane ≃ₗᵢ[ℝ] Plane := g.trans (Complex.conjLIE.trans g.symm)

theorem certificate_pos
    (A B C K L O : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    (hK : InsideTriangle B M C K) (hL : InsideTriangle B N C L)
    (hKangle : InsideAngle L B A K) (hLangle : InsideAngle A C K L)
    (h1 : ∠ K B A = ∠ A C L) (h2 : ∠ L B K = ∠ L N C) (h3 : ∠ L C K = ∠ B M K)
    (hO : IsCircumcentre A K L O)
    (c k l : ℂ)
    (hcdef : c = (g C - g A) / (g B - g A))
    (hkdef : k = (g K - g A) / (g B - g A))
    (hldef : l = (g L - g A) / (g B - g A))
    (hpos : 0 < c.im) :
    2 * ((starRingEnd ℂ (c - 1) * l).im) * Complex.normSq k
      + 2 * ((starRingEnd ℂ k * (c - 1)).im) * Complex.normSq l
      - (Complex.normSq c - 1) * (starRingEnd ℂ k * l).im = 0 := by
    -- Step B — the three principal unsigned angles.
    set a : ℝ := ∠ K B A with ha_def
    set b : ℝ := ∠ L B K with hb_def
    set γ : ℝ := ∠ L C K with hγ_def
    -- ===== Foundation: normalized complex coordinates via the isometry `g`. =====
    have hAB : A ≠ B := ne₁₂_of_not_collinear hABC
    have hBA : (g B - g A : ℂ) ≠ 0 := by
      rw [sub_ne_zero]; exact fun h => hAB (g.injective h).symm
    have cancelD : ∀ z w : ℂ, (g B - g A) * z = (g B - g A) * w → z = w :=
      fun z w h => mul_left_cancel₀ hBA h
    -- e-forms `g X - g A = (g B - g A) * (value X)`.
    have eK : g K - g A = (g B - g A) * k := by
      have h := (eq_div_iff hBA).mp hkdef; rw [← h]; ring
    have eL : g L - g A = (g B - g A) * l := by
      have h := (eq_div_iff hBA).mp hldef; rw [← h]; ring
    have eC : g C - g A = (g B - g A) * c := by
      have h := (eq_div_iff hBA).mp hcdef; rw [← h]; ring
    have eM : g M - g A = (g B - g A) * ((1/2 : ℝ) : ℂ) := by
      have h1 : (M - A : Plane) = (⅟(2:ℝ)) • (B - A) := by
        have h := midpoint_vsub_left (R := ℝ) A B
        rw [hM]; simpa [vsub_eq_sub] using h
      have h2 := congrArg (fun p : Plane => g p) h1
      simp only [map_sub, map_smul, Complex.real_smul, invOf_eq_inv] at h2
      rw [h2]; push_cast; ring
    have eN : g N - g A = (g B - g A) * (c/2) := by
      have h1 : (N - A : Plane) = (⅟(2:ℝ)) • (C - A) := by
        have h := midpoint_vsub_left (R := ℝ) A C
        rw [hN]; simpa [vsub_eq_sub] using h
      have h2 := congrArg (fun p : Plane => g p) h1
      simp only [map_sub, map_smul, Complex.real_smul, invOf_eq_inv] at h2
      rw [h2, eC]; push_cast; ring
    -- Barycentric form of `k` (from `hK`).
    obtain ⟨α, β, δ, hα, hβ, hδ, hsum, hKeq⟩ := hK
    have hsumC : (α : ℂ) + β + δ = 1 := by exact_mod_cast hsum
    have hgK : g K = (α:ℂ) * g B + (β:ℂ) * g M + (δ:ℂ) * g C := by
      have h := congrArg (fun p : Plane => g p) hKeq
      simpa only [map_add, map_smul, Complex.real_smul] using h
    have gKA : g K - g A = (g B - g A) * (((α + β/2 : ℝ):ℂ) + ((δ:ℝ):ℂ) * c) := by
      have hM' : g M = g A + (g B - g A) * ((1/2:ℝ):ℂ) := by linear_combination eM
      have hC' : g C = g A + (g B - g A) * c := by linear_combination eC
      rw [hgK, hM', hC']; push_cast; linear_combination (g A) * hsumC
    have hkval : k = ((α + β/2 : ℝ):ℂ) + ((δ:ℝ):ℂ) * c := by
      apply cancelD; rw [← eK]; exact gKA
    have hImk : 0 < k.im := by
      have hkim : k.im = δ * c.im := by
        rw [hkval, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add]
      rw [hkim]; exact mul_pos hδ hpos
    -- Barycentric form of `l` (from `hL`).
    obtain ⟨α', β', δ', hα', hβ', hδ', hsum', hLeq⟩ := hL
    have hsumC' : (α' : ℂ) + β' + δ' = 1 := by exact_mod_cast hsum'
    have hgL : g L = (α':ℂ) * g B + (β':ℂ) * g N + (δ':ℂ) * g C := by
      have h := congrArg (fun p : Plane => g p) hLeq
      simpa only [map_add, map_smul, Complex.real_smul] using h
    have gLA : g L - g A = (g B - g A) * (((α':ℝ):ℂ) + ((β'/2 + δ' : ℝ):ℂ) * c) := by
      have hN' : g N = g A + (g B - g A) * (c/2) := by linear_combination eN
      have hC' : g C = g A + (g B - g A) * c := by linear_combination eC
      rw [hgL, hN', hC']; push_cast; linear_combination (g A) * hsumC'
    have hlval : l = ((α':ℝ):ℂ) + ((β'/2 + δ' : ℝ):ℂ) * c := by
      apply cancelD; rw [← eL]; exact gLA
    have hIml : 0 < l.im := by
      have hlim : l.im = (β'/2 + δ') * c.im := by
        rw [hlval, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add]
      rw [hlim]; exact mul_pos (by linarith) hpos
    -- Cone (angle) witnesses pushed to complex coordinates.
    obtain ⟨s1, t1, hs1, ht1, hcone1⟩ := hKangle
    have hcone1c : k - 1 = (s1:ℂ) * (l - 1) - (t1:ℂ) := by
      have h := congrArg (fun p : Plane => g p) hcone1
      simp only [map_sub, map_add, map_smul, Complex.real_smul] at h
      apply cancelD
      have e1 : g K - g B = (g B - g A) * (k - 1) := by linear_combination eK
      have e2 : g L - g B = (g B - g A) * (l - 1) := by linear_combination eL
      have e3 : g A - g B = (g B - g A) * (-1) := by ring
      rw [← e1, h, e2, e3]; ring
    obtain ⟨s2, t2, hs2, ht2, hcone2⟩ := hLangle
    have hcone2c : l - c = -(s2:ℂ) * c + (t2:ℂ) * (k - c) := by
      have h := congrArg (fun p : Plane => g p) hcone2
      simp only [map_sub, map_add, map_smul, Complex.real_smul] at h
      apply cancelD
      have e1 : g L - g C = (g B - g A) * (l - c) := by linear_combination eL - eC
      have e2 : g A - g C = (g B - g A) * (-c) := by linear_combination -eC
      have e3 : g K - g C = (g B - g A) * (k - c) := by linear_combination eK - eC
      rw [← e1, h, e2, e3]; ring
    -- Nondegeneracy: `K ≠ B` (since `Im k > 0`), and `{1, c}` independence.
    have hKB : (K - B : Plane) ≠ 0 := by
      intro hh
      have hKeqB : K = B := sub_eq_zero.mp hh
      have hk1 : k = 1 := by apply cancelD; rw [← eK, hKeqB]; ring
      rw [hk1] at hImk; simp at hImk
    have hKneB : K ≠ B := fun hh => hKB (sub_eq_zero.mpr hh)
    have hBK : B ≠ K := hKneB.symm
    have indep : ∀ P Q : ℝ, ((P:ℂ) + (Q:ℂ) * c = 0) → P = 0 ∧ Q = 0 := by
      intro P Q h
      have hQ : Q = 0 := by
        have h2 := congrArg Complex.im h
        rw [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add,
            Complex.zero_im] at h2
        exact (mul_eq_zero.mp h2).resolve_right (ne_of_gt hpos)
      refine ⟨?_, hQ⟩
      have h2 := congrArg Complex.re h
      rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.zero_re, hQ,
          zero_mul, add_zero] at h2
      exact h2
    -- Unfolding lemma for `EuclideanGeometry.angle`.
    have angle_eq : ∀ P Q R : Plane,
        EuclideanGeometry.angle P Q R = InnerProductGeometry.angle (P - Q) (R - Q) := by
      intro P Q R; simp only [EuclideanGeometry.angle, vsub_eq_sub]
    -- ===== ray_order: strict positivity of the three principal angles. =====
    have ha : 0 < a := by
      have hz : ∠ K B A ≠ 0 := by
        rw [angle_eq]
        intro hh
        rw [InnerProductGeometry.angle_eq_zero_iff] at hh
        obtain ⟨hne, r, hr, hrel⟩ := hh
        have hpush : (-1 : ℂ) = (r:ℂ) * (k - 1) := by
          have h := congrArg (fun p : Plane => g p) hrel
          simp only [map_smul, map_sub, Complex.real_smul] at h
          apply cancelD
          have ek : g K - g B = (g B - g A) * (k - 1) := by linear_combination eK
          rw [show (g B - g A) * (-1:ℂ) = g A - g B from by ring, h, ek]; ring
        have himeq := congrArg Complex.im hpush
        simp only [Complex.im_ofReal_mul, Complex.sub_im, Complex.one_im, Complex.neg_im,
          neg_zero, sub_zero] at himeq
        linarith [mul_pos hr hImk, himeq]
      rw [ha_def]; exact (EuclideanGeometry.angle_nonneg K B A).lt_of_ne (Ne.symm hz)
    have hb : 0 < b := by
      have hz : ∠ L B K ≠ 0 := by
        rw [angle_eq]
        intro hh
        rw [InnerProductGeometry.angle_eq_zero_iff] at hh
        obtain ⟨hne, r, hr, hrel⟩ := hh
        have hpush : (k - 1 : ℂ) = (r:ℂ) * (l - 1) := by
          have h := congrArg (fun p : Plane => g p) hrel
          simp only [map_smul, map_sub, Complex.real_smul] at h
          apply cancelD
          have ek : g K - g B = (g B - g A) * (k - 1) := by linear_combination eK
          have el : g L - g B = (g B - g A) * (l - 1) := by linear_combination eL
          rw [← ek, h, el]; ring
        have hcomb : ((r:ℂ) - s1) * (l - 1) = -(t1:ℂ) := by
          linear_combination hcone1c - hpush
        have him := congrArg Complex.im hcomb
        rw [show ((r:ℂ) - (s1:ℂ)) = (((r - s1 : ℝ)):ℂ) from by push_cast; ring] at him
        simp only [Complex.im_ofReal_mul, Complex.sub_im, Complex.one_im, Complex.neg_im,
          Complex.ofReal_im, sub_zero, neg_zero] at him
        have hrs : r = s1 := by
          rcases mul_eq_zero.mp him with h | h
          · linarith
          · exact absurd h (ne_of_gt hIml)
        rw [hrs, sub_self, zero_mul] at hcomb
        have ht0 : (t1:ℂ) = 0 := by linear_combination hcomb
        have : t1 = 0 := by exact_mod_cast ht0
        linarith
      rw [hb_def]; exact (EuclideanGeometry.angle_nonneg L B K).lt_of_ne (Ne.symm hz)
    have hg : 0 < γ := by
      have hz : ∠ L C K ≠ 0 := by
        rw [angle_eq]
        intro hh
        rw [InnerProductGeometry.angle_eq_zero_iff] at hh
        obtain ⟨hne, r, hr, hrel⟩ := hh
        have hpush : (k - c : ℂ) = (r:ℂ) * (l - c) := by
          have h := congrArg (fun p : Plane => g p) hrel
          simp only [map_smul, map_sub, Complex.real_smul] at h
          apply cancelD
          have ek : g K - g C = (g B - g A) * (k - c) := by linear_combination eK - eC
          have el : g L - g C = (g B - g A) * (l - c) := by linear_combination eL - eC
          rw [← ek, h, el]; ring
        have hcomb : (k - c) * (1 - (r:ℂ) * t2) = -((r:ℂ) * (s2:ℂ)) * c := by
          linear_combination hpush + (r:ℂ) * hcone2c
        rw [hkval] at hcomb
        have hE : ((((α + β/2) * (1 - r*t2) : ℝ)):ℂ)
            + (((((δ - 1) * (1 - r*t2) + r*s2) : ℝ)):ℂ) * c = 0 := by
          push_cast; push_cast at hcomb; linear_combination hcomb
        obtain ⟨hP, hQ⟩ := indep _ _ hE
        have h10 : 1 - r*t2 = 0 := by
          rcases mul_eq_zero.mp hP with h | h
          · linarith
          · exact h
        rw [h10, mul_zero, zero_add] at hQ
        linarith [mul_pos hr hs2]
      rw [hγ_def]; exact (EuclideanGeometry.angle_nonneg L C K).lt_of_ne (Ne.symm hz)
    -- ===== ray_order: the two `< π` sums. =====
    have hab : a + b < Real.pi := by
      have hmem : (K - B : Plane) ∈ Submodule.span NNReal ({A - B, L - B} : Set Plane) := by
        rw [Submodule.mem_span_pair]
        refine ⟨⟨t1, ht1.le⟩, ⟨s1, hs1.le⟩, ?_⟩
        rw [NNReal.smul_def, NNReal.smul_def, NNReal.coe_mk, NNReal.coe_mk, hcone1]; abel
      have hchas := InnerProductGeometry.angle_eq_angle_add_add_angle_add_of_mem_span hKB hmem
      have hE1 : InnerProductGeometry.angle (A - B) (L - B) = a + b := by
        rw [hchas, ha_def, hb_def, angle_eq K B A, angle_eq L B K,
            InnerProductGeometry.angle_comm (K - B) (A - B),
            InnerProductGeometry.angle_comm (L - B) (K - B)]
      have hle : InnerProductGeometry.angle (A - B) (L - B) ≤ Real.pi :=
        InnerProductGeometry.angle_le_pi _ _
      have hne : InnerProductGeometry.angle (A - B) (L - B) ≠ Real.pi := by
        intro hpi
        rw [InnerProductGeometry.angle_eq_pi_iff] at hpi
        obtain ⟨hx0, r, hr, hrel⟩ := hpi
        have hpush : (l - 1 : ℂ) = -(r:ℂ) := by
          have h := congrArg (fun p : Plane => g p) hrel
          simp only [map_smul, map_sub, Complex.real_smul] at h
          apply cancelD
          have el : g L - g B = (g B - g A) * (l - 1) := by linear_combination eL
          have ea : g A - g B = (g B - g A) * (-1) := by ring
          rw [← el, h, ea]; ring
        have him := congrArg Complex.im hpush
        simp only [Complex.sub_im, Complex.one_im, Complex.neg_im, Complex.ofReal_im,
          sub_zero, neg_zero] at him
        linarith [hIml]
      have hlt := hle.lt_of_ne hne
      rw [hE1] at hlt; exact hlt
    have hag : a + γ < Real.pi := by
      have haM : a = ∠ K B M := by
        rw [ha_def, angle_eq K B A, angle_eq K B M]
        have hMB : (M - B : Plane) = (⅟(2:ℝ)) • (A - B) := by
          have h := midpoint_vsub_right (R := ℝ) A B
          rw [hM]; simpa [vsub_eq_sub] using h
        rw [hMB, InnerProductGeometry.angle_smul_right_of_pos _ _
              (by rw [invOf_eq_inv]; norm_num : (0:ℝ) < ⅟(2:ℝ))]
      have hgM : γ = ∠ B M K := h3
      have hMKB : 0 < ∠ M K B := by
        have hz : ∠ M K B ≠ 0 := by
          rw [angle_eq]
          intro hh
          rw [InnerProductGeometry.angle_eq_zero_iff] at hh
          obtain ⟨hne, r, hr, hrel⟩ := hh
          have hpush : (1 - k : ℂ) = (r:ℂ) * (((1/2:ℝ):ℂ) - k) := by
            have h := congrArg (fun p : Plane => g p) hrel
            simp only [map_smul, map_sub, Complex.real_smul] at h
            apply cancelD
            have eBK : g B - g K = (g B - g A) * (1 - k) := by linear_combination -eK
            have eMK : g M - g K = (g B - g A) * (((1/2:ℝ):ℂ) - k) := by
              linear_combination eM - eK
            rw [← eBK, h, eMK]; ring
          have him := congrArg Complex.im hpush
          simp only [Complex.im_ofReal_mul, Complex.sub_im, Complex.one_im, Complex.ofReal_im,
            sub_zero, zero_sub] at him
          have hz2 : k.im * (r - 1) = 0 := by linear_combination him
          have hr1 : r = 1 := by
            rcases mul_eq_zero.mp hz2 with h | h
            · exact absurd h (ne_of_gt hImk)
            · linarith
          rw [hr1] at hpush
          simp only [Complex.ofReal_one, one_mul] at hpush
          have h12 : ((1:ℝ):ℂ) = ((1/2:ℝ):ℂ) := by
            push_cast at hpush ⊢; linear_combination hpush
          have hcontra : (1:ℝ) = (1/2:ℝ) := by exact_mod_cast h12
          norm_num at hcontra
        exact (EuclideanGeometry.angle_nonneg M K B).lt_of_ne (Ne.symm hz)
      have htri := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (p₁ := K) (p₂ := B) M hBK
      rw [← haM, ← hgM] at htri
      linarith [hMKB, htri]
    -- Positive sine denominators (genuine: `0 < x < π ⇒ sin x > 0`).
    have hsab : 0 < Real.sin (a + b) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) hab
    have hsag : 0 < Real.sin (a + γ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) hag
    -- The two ray-length ratios and the auxiliary point `ℓ`.
    set r : ℝ := Real.sin γ / (2 * Real.sin (a + γ)) with hr_def
    set s : ℝ := Real.sin b / (2 * Real.sin (a + b)) with hs_def
    set ℓ : ℂ := 1 - s * Complex.exp (a * Complex.I) with hℓ_def
    -- The scalar sine relations (genuine, from the definitions of `r`, `s`).
    have hr : 2 * r * Real.sin (a + γ) = Real.sin γ := by
      have hne : (2 : ℝ) * Real.sin (a + γ) ≠ 0 := (mul_pos two_pos hsag).ne'
      rw [hr_def, show 2 * (Real.sin γ / (2 * Real.sin (a + γ))) * Real.sin (a + γ)
            = Real.sin γ / (2 * Real.sin (a + γ)) * (2 * Real.sin (a + γ)) from by ring,
          div_mul_cancel₀ (Real.sin γ) hne]
    have hs : 2 * s * Real.sin (a + b) = Real.sin b := by
      have hne : (2 : ℝ) * Real.sin (a + b) ≠ 0 := (mul_pos two_pos hsab).ne'
      rw [hs_def, show 2 * (Real.sin b / (2 * Real.sin (a + b))) * Real.sin (a + b)
            = Real.sin b / (2 * Real.sin (a + b)) * (2 * Real.sin (a + b)) from by ring,
          div_mul_cancel₀ (Real.sin b) hne]
    -- ===== Shared foundation for the exponential coordinates. =====
    set D : ℝ := ‖g B - g A‖ with hD_def
    have hDpos : 0 < D := by rw [hD_def]; exact norm_pos_iff.mpr hBA
    have hcne : c ≠ 0 := by
      intro h; rw [h, Complex.zero_im] at hpos; exact lt_irrefl 0 hpos
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hcne
    have hdist : ∀ X Y : Plane, dist X Y = ‖g X - g Y‖ := by
      intro X Y; rw [← g.dist_map X Y, dist_eq_norm]
    -- positivity of the relevant sines.
    have hsina : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha (by linarith)
    have hsinb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb (by linarith)
    have hsing : 0 < Real.sin γ := Real.sin_pos_of_pos_of_lt_pi hg (by linarith)
    have hrpos : 0 < r := by rw [hr_def]; exact div_pos hsing (mul_pos two_pos hsag)
    have hs_pos : 0 < s := by rw [hs_def]; exact div_pos hsinb (mul_pos two_pos hsab)
    -- Exponential-form assembler (negative exponent).
    have hExpNeg : ∀ (z : ℂ) (ρ θ : ℝ), 0 ≤ ρ → 0 < Real.sin θ →
        ‖1 - z‖ = ρ → ‖z‖ ^ 2 = ρ ^ 2 + 1 - 2 * ρ * Real.cos θ → (1 - z).im < 0 →
        z = 1 - ρ * Complex.exp (-θ * Complex.I) := by
      intro z ρ θ hρ hsinθ hlen hcosid himneg
      have hnz : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
        rw [Complex.sq_norm, Complex.normSq_apply]
      have hn1z : ‖1 - z‖ ^ 2 = (1 - z.re) * (1 - z.re) + z.im * z.im := by
        rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
          Complex.one_re, Complex.one_im]; ring
      have eq1 : z.re * z.re + z.im * z.im = ρ ^ 2 + 1 - 2 * ρ * Real.cos θ := by
        rw [← hnz]; exact hcosid
      have eq2 : (1 - z.re) * (1 - z.re) + z.im * z.im = ρ ^ 2 := by rw [← hn1z, hlen]
      have hzre : z.re = 1 - ρ * Real.cos θ := by
        linear_combination (1 / 2 : ℝ) * eq1 - (1 / 2 : ℝ) * eq2
      have h1z : 1 - z.re = ρ * Real.cos θ := by linarith [hzre]
      have hsq : z.im * z.im = (ρ * Real.sin θ) * (ρ * Real.sin θ) := by
        linear_combination eq2 - ρ ^ 2 * Real.sin_sq_add_cos_sq θ
          - ((1 - z.re) + ρ * Real.cos θ) * h1z
      have hzimpos : 0 < z.im := by
        have h := himneg
        simp only [Complex.sub_im, Complex.one_im, zero_sub] at h; linarith
      have hρsin : 0 ≤ ρ * Real.sin θ := mul_nonneg hρ hsinθ.le
      have hzim : z.im = ρ * Real.sin θ := by
        have hfac : (z.im - ρ * Real.sin θ) * (z.im + ρ * Real.sin θ) = 0 := by
          linear_combination hsq
        rcases mul_eq_zero.mp hfac with h | h
        · linarith
        · linarith [hzimpos, hρsin]
      have hEre : (Complex.exp (-(θ : ℂ) * Complex.I)).re = Real.cos θ := by
        rw [← Complex.ofReal_neg, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
      have hEim : (Complex.exp (-(θ : ℂ) * Complex.I)).im = -Real.sin θ := by
        rw [← Complex.ofReal_neg, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
      apply Complex.ext
      · rw [hzre, Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul, hEre]
      · rw [hzim, Complex.sub_im, Complex.one_im, Complex.im_ofReal_mul, hEim]; ring
    -- Exponential-form assembler (positive exponent).
    have hExpPos : ∀ (z : ℂ) (ρ θ : ℝ), 0 ≤ ρ → 0 < Real.sin θ →
        ‖1 - z‖ = ρ → ‖z‖ ^ 2 = ρ ^ 2 + 1 - 2 * ρ * Real.cos θ → 0 < (1 - z).im →
        z = 1 - ρ * Complex.exp (θ * Complex.I) := by
      intro z ρ θ hρ hsinθ hlen hcosid himpos
      have hnz : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
        rw [Complex.sq_norm, Complex.normSq_apply]
      have hn1z : ‖1 - z‖ ^ 2 = (1 - z.re) * (1 - z.re) + z.im * z.im := by
        rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
          Complex.one_re, Complex.one_im]; ring
      have eq1 : z.re * z.re + z.im * z.im = ρ ^ 2 + 1 - 2 * ρ * Real.cos θ := by
        rw [← hnz]; exact hcosid
      have eq2 : (1 - z.re) * (1 - z.re) + z.im * z.im = ρ ^ 2 := by rw [← hn1z, hlen]
      have hzre : z.re = 1 - ρ * Real.cos θ := by
        linear_combination (1 / 2 : ℝ) * eq1 - (1 / 2 : ℝ) * eq2
      have h1z : 1 - z.re = ρ * Real.cos θ := by linarith [hzre]
      have hsq : z.im * z.im = (ρ * Real.sin θ) * (ρ * Real.sin θ) := by
        linear_combination eq2 - ρ ^ 2 * Real.sin_sq_add_cos_sq θ
          - ((1 - z.re) + ρ * Real.cos θ) * h1z
      have hzimneg : z.im < 0 := by
        have h := himpos
        simp only [Complex.sub_im, Complex.one_im, zero_sub] at h; linarith
      have hρsin : 0 ≤ ρ * Real.sin θ := mul_nonneg hρ hsinθ.le
      have hzim : z.im = -(ρ * Real.sin θ) := by
        have hfac : (z.im - ρ * Real.sin θ) * (z.im + ρ * Real.sin θ) = 0 := by
          linear_combination hsq
        rcases mul_eq_zero.mp hfac with h | h
        · linarith [hzimneg, hρsin]
        · linarith
      have hEre : (Complex.exp ((θ : ℂ) * Complex.I)).re = Real.cos θ := by
        rw [Complex.exp_ofReal_mul_I_re]
      have hEim : (Complex.exp ((θ : ℂ) * Complex.I)).im = Real.sin θ := by
        rw [Complex.exp_ofReal_mul_I_im]
      apply Complex.ext
      · rw [hzre, Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul, hEre]
      · rw [hzim, Complex.sub_im, Complex.one_im, Complex.im_ofReal_mul, hEim]; ring
    -- Imaginary-part positivity in the `c`-frame (points on the same side as `B`).
    have imDivPos : ∀ (z : ℂ) (u v : ℝ), 0 < u → z = (u : ℂ) + (v : ℂ) * c →
        0 < (1 - z / c).im := by
      intro z u v hu hz
      have hc2 : 0 < Complex.normSq c := Complex.normSq_pos.mpr hcne
      have hval : (1 - z / c).im = u * c.im / Complex.normSq c := by
        rw [show (1 : ℂ) - z / c = (c - z) / c from by rw [sub_div, div_self hcne],
          Complex.div_im, hz]
        simp only [Complex.sub_im, Complex.sub_re, Complex.add_im, Complex.add_re,
          Complex.ofReal_im, Complex.ofReal_re, Complex.im_ofReal_mul, Complex.re_ofReal_mul]
        rw [div_sub_div_same]
        congr 1
        ring
      rw [hval]; exact div_pos (mul_pos hu hpos) hc2
    -- The principal angle sums used by the `law_cos` calls.
    have hLBA : ∠ L B A = a + b := by
      have hmem : (K - B : Plane) ∈ Submodule.span NNReal ({A - B, L - B} : Set Plane) := by
        rw [Submodule.mem_span_pair]
        refine ⟨⟨t1, ht1.le⟩, ⟨s1, hs1.le⟩, ?_⟩
        rw [NNReal.smul_def, NNReal.smul_def, NNReal.coe_mk, NNReal.coe_mk, hcone1]; abel
      have hchas := InnerProductGeometry.angle_eq_angle_add_add_angle_add_of_mem_span hKB hmem
      have hE1 : InnerProductGeometry.angle (A - B) (L - B) = a + b := by
        rw [hchas, ha_def, hb_def, angle_eq K B A, angle_eq L B K,
            InnerProductGeometry.angle_comm (K - B) (A - B),
            InnerProductGeometry.angle_comm (L - B) (K - B)]
      rw [angle_eq L B A, InnerProductGeometry.angle_comm (L - B) (A - B)]; exact hE1
    have haCL : a = ∠ A C L := h1
    have hbNC : b = ∠ L N C := h2
    have haLC : a = ∠ L C A := by rw [haCL, EuclideanGeometry.angle_comm A C L]
    -- `L ≠ C` (needed for the angle-chasing at `C`).
    have hlc_im : (l - c).im < 0 := by
      have hval : (l - c).im = (β' / 2 + δ' - 1) * c.im := by
        rw [hlval]; simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
          Complex.im_ofReal_mul, zero_add]; ring
      rw [hval]; apply mul_neg_of_neg_of_pos _ hpos; linarith [hα', hβ', hsum']
    have hLC0 : (L - C : Plane) ≠ 0 := by
      intro h
      have hg0 : g L - g C = 0 := by rw [sub_eq_zero.mp h]; exact sub_self _
      have heq : g L - g C = (g B - g A) * (l - c) := by linear_combination eL - eC
      rw [heq] at hg0
      rcases mul_eq_zero.mp hg0 with h1' | h1'
      · exact hBA h1'
      · rw [h1'] at hlc_im; simp at hlc_im
    have hKCA : ∠ K C A = a + γ := by
      have hmem : (L - C : Plane) ∈ Submodule.span NNReal ({A - C, K - C} : Set Plane) := by
        rw [Submodule.mem_span_pair]
        refine ⟨⟨s2, hs2.le⟩, ⟨t2, ht2.le⟩, ?_⟩
        rw [NNReal.smul_def, NNReal.smul_def, NNReal.coe_mk, NNReal.coe_mk, hcone2]
      have hchas := InnerProductGeometry.angle_eq_angle_add_add_angle_add_of_mem_span hLC0 hmem
      rw [EuclideanGeometry.angle_comm K C A, angle_eq A C K, hchas,
          ← angle_eq A C L, ← angle_eq L C K, ← haCL, ← hγ_def]
    -- Step C — sine_coordinates (proof.tex Step 5).  The exponential-form
    -- coordinates.  With `0 < c.im` these are honestly true; they package the
    -- Euclidean sine law (`EuclideanGeometry.law_sin`) and the signed directions
    -- from ray_order on the noncollinear triangles `BMK` (side `BM=1/2`) and
    -- `CNL` (side `CN=|c|/2`), for which there is no direct Mathlib support.
    -- Shared norm identities (base `B = 1`).
    have nAB : ‖g A - g B‖ = D := by
      rw [show g A - g B = -(g B - g A) from by ring, norm_neg, ← hD_def]
    have hk : k = 1 - r * Complex.exp (-a * Complex.I) := by
      have nKA : ‖g K - g A‖ = D * ‖k‖ := by rw [eK, norm_mul, ← hD_def]
      have nKB : ‖g K - g B‖ = D * ‖k - 1‖ := by
        rw [show g K - g B = (g B - g A) * (k - 1) from by linear_combination eK, norm_mul,
          ← hD_def]
      have nBM : ‖g B - g M‖ = D * (1 / 2 : ℝ) := by
        rw [show g B - g M = (g B - g A) * ((1 / 2 : ℝ) : ℂ) from by
              have h := eM; push_cast at h ⊢; linear_combination -h,
          norm_mul, ← hD_def, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
      -- Angle facts for the sine law on triangle `B M K`.
      have haM : a = ∠ K B M := by
        rw [ha_def, angle_eq K B A, angle_eq K B M]
        have hMB : (M - B : Plane) = (⅟(2 : ℝ)) • (A - B) := by
          have h := midpoint_vsub_right (R := ℝ) A B
          rw [hM]; simpa [vsub_eq_sub] using h
        rw [hMB, InnerProductGeometry.angle_smul_right_of_pos _ _
              (by rw [invOf_eq_inv]; norm_num : (0 : ℝ) < ⅟(2 : ℝ))]
      have hgM : γ = ∠ B M K := h3
      have hMKB : ∠ M K B = Real.pi - (a + γ) := by
        have htri := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (p₁ := K) (p₂ := B) M hBK
        rw [← haM, ← hgM] at htri; linarith
      -- Length via the law of sines.
      have hlen : ‖1 - k‖ = r := by
        have hlaw := EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist M K B
        rw [hMKB, Real.sin_pi_sub, ← hgM, hdist K B, hdist B M, nKB, nBM] at hlaw
        have hcancel : Real.sin (a + γ) * ‖k - 1‖ = Real.sin γ * (1 / 2 : ℝ) := by
          have h2 : D * (Real.sin (a + γ) * ‖k - 1‖) = D * (Real.sin γ * (1 / 2 : ℝ)) := by
            linear_combination hlaw
          exact mul_left_cancel₀ hDpos.ne' h2
        have h2 : Real.sin (a + γ) * ‖1 - k‖ = Real.sin γ * (1 / 2 : ℝ) := by
          rw [show ‖1 - k‖ = ‖k - 1‖ from norm_sub_rev 1 k]; exact hcancel
        rw [hr_def, eq_div_iff (mul_pos two_pos hsag).ne']
        linear_combination 2 * h2
      have hk1r : ‖k - 1‖ = r := by rw [norm_sub_rev]; exact hlen
      -- Real part via the law of cosines.
      have hcosid : ‖k‖ ^ 2 = r ^ 2 + 1 - 2 * r * Real.cos a := by
        have hlaw := EuclideanGeometry.law_cos K B A
        rw [← ha_def, hdist K A, hdist K B, hdist A B, nKA, nKB, nAB] at hlaw
        have hbase : ‖k‖ ^ 2 = ‖k - 1‖ ^ 2 + 1 - 2 * ‖k - 1‖ * Real.cos a := by
          apply mul_left_cancel₀ (mul_pos hDpos hDpos).ne'
          linear_combination hlaw
        rw [hk1r] at hbase; exact hbase
      have himneg : (1 - k).im < 0 := by
        simp only [Complex.sub_im, Complex.one_im, zero_sub]; linarith [hImk]
      exact hExpNeg k r a hrpos.le hsina hlen hcosid himneg
    have hlc : l = ℓ * c := by
      -- C-frame norm identities.
      have nLA : ‖g L - g A‖ = D * ‖l‖ := by rw [eL, norm_mul, ← hD_def]
      have nLC : ‖g L - g C‖ = D * ‖l - c‖ := by
        rw [show g L - g C = (g B - g A) * (l - c) from by linear_combination eL - eC, norm_mul,
          ← hD_def]
      have nAC : ‖g A - g C‖ = D * ‖c‖ := by
        rw [show g A - g C = (g B - g A) * (-c) from by linear_combination -eC, norm_mul,
          ← hD_def, norm_neg]
      have nCN : ‖g C - g N‖ = D * (‖c‖ / 2) := by
        rw [show g C - g N = (g B - g A) * c * ((1 / 2 : ℝ) : ℂ) from by
              push_cast; linear_combination eC - eN,
          norm_mul, norm_mul, ← hD_def, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]; ring
      -- The `c`-frame norm rewrites.
      have hwn : ‖l / c‖ = ‖l‖ / ‖c‖ := Complex.norm_div l c
      have hwn1 : ‖1 - l / c‖ = ‖l - c‖ / ‖c‖ := by
        rw [show (1 : ℂ) - l / c = (c - l) / c from by rw [sub_div, div_self hcne],
          Complex.norm_div, norm_sub_rev c l]
      -- Length via the law of sines on triangle `C N L`.
      have hCN : C ≠ N := by
        intro h
        have hg0 : g C - g N = 0 := by rw [h]; exact sub_self _
        have heq : g C - g N = (g B - g A) * (c / 2) := by linear_combination eC - eN
        rw [heq] at hg0
        rcases mul_eq_zero.mp hg0 with h1' | h1'
        · exact hBA h1'
        · exact hcne (by linear_combination 2 * h1')
      have hNCL : a = ∠ N C L := by
        rw [haLC, angle_eq L C A, angle_eq N C L]
        have hNC : (N - C : Plane) = (⅟(2 : ℝ)) • (A - C) := by
          have h := midpoint_vsub_right (R := ℝ) A C
          rw [hN]; simpa [vsub_eq_sub] using h
        rw [hNC, InnerProductGeometry.angle_smul_left_of_pos _ _
              (by rw [invOf_eq_inv]; norm_num : (0 : ℝ) < ⅟(2 : ℝ)),
          InnerProductGeometry.angle_comm (A - C) (L - C)]
      have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (p₃ := L) hCN
      rw [← hNCL, ← hbNC] at hsum
      have hNLC : ∠ N L C = Real.pi - (a + b) := by
        rw [EuclideanGeometry.angle_comm N L C]; linarith [hsum]
      have hlenC : ‖1 - l / c‖ = s := by
        have hlaw := EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist N L C
        rw [hNLC, Real.sin_pi_sub, EuclideanGeometry.angle_comm C N L, ← hbNC,
          hdist L C, hdist C N, nLC, nCN] at hlaw
        -- hlaw : sin (a+b) * (D * ‖l-c‖) = sin b * (D * (‖c‖/2))
        have hcancel : Real.sin (a + b) * ‖l - c‖ = Real.sin b * (‖c‖ / 2) := by
          have h2 : D * (Real.sin (a + b) * ‖l - c‖) = D * (Real.sin b * (‖c‖ / 2)) := by
            linear_combination hlaw
          exact mul_left_cancel₀ hDpos.ne' h2
        rw [hwn1, hs_def, div_eq_iff hcpos.ne', div_mul_eq_mul_div,
          eq_div_iff (mul_pos two_pos hsab).ne']
        linear_combination 2 * hcancel
      -- Real part via the law of cosines on triangle `L C A`.
      have hcosid : ‖l / c‖ ^ 2 = s ^ 2 + 1 - 2 * s * Real.cos a := by
        have hlaw := EuclideanGeometry.law_cos L C A
        rw [← haLC, hdist L A, hdist L C, hdist A C, nLA, nLC, nAC] at hlaw
        have hlawN : ‖l‖ ^ 2 = ‖l - c‖ ^ 2 + ‖c‖ ^ 2 - 2 * ‖l - c‖ * ‖c‖ * Real.cos a := by
          apply mul_left_cancel₀ (mul_pos hDpos hDpos).ne'
          linear_combination hlaw
        have hslc : s = ‖l - c‖ / ‖c‖ := by rw [← hlenC, hwn1]
        rw [hwn, hslc]
        rw [div_pow, div_pow]
        field_simp [hcpos.ne']
        linear_combination hlawN
      have himpos : 0 < (1 - l / c).im := imDivPos l α' (β' / 2 + δ') hα' hlval
      have hz : l / c = 1 - s * Complex.exp (a * Complex.I) :=
        hExpPos (l / c) s a hs_pos.le hsina hlenC hcosid himpos
      rw [hℓ_def]; exact (div_eq_iff hcne).mp hz
    obtain ⟨lam, rho, hl2, hk2⟩ :
        ∃ lam rho : ℝ,
          l = 1 - lam * Complex.exp (-(a + b) * Complex.I) ∧
          k = c * (1 - rho * Complex.exp ((a + γ) * Complex.I)) := by
      refine ⟨‖1 - l‖, ‖1 - k / c‖, ?_, ?_⟩
      · -- hl2 : l = 1 - ‖1-l‖ e^{-i(a+b)}
        have nLA : ‖g L - g A‖ = D * ‖l‖ := by rw [eL, norm_mul, ← hD_def]
        have nLB : ‖g L - g B‖ = D * ‖l - 1‖ := by
          rw [show g L - g B = (g B - g A) * (l - 1) from by linear_combination eL, norm_mul,
            ← hD_def]
        have hcosid : ‖l‖ ^ 2 = ‖1 - l‖ ^ 2 + 1 - 2 * ‖1 - l‖ * Real.cos (a + b) := by
          have hlaw := EuclideanGeometry.law_cos L B A
          rw [hLBA, hdist L A, hdist L B, hdist A B, nLA, nLB, nAB] at hlaw
          have hbase : ‖l‖ ^ 2 = ‖l - 1‖ ^ 2 + 1 - 2 * ‖l - 1‖ * Real.cos (a + b) := by
            apply mul_left_cancel₀ (mul_pos hDpos hDpos).ne'
            linear_combination hlaw
          rw [show ‖1 - l‖ = ‖l - 1‖ from norm_sub_rev 1 l]; exact hbase
        have himneg : (1 - l).im < 0 := by
          simp only [Complex.sub_im, Complex.one_im, zero_sub]; linarith [hIml]
        have h := hExpNeg l ‖1 - l‖ (a + b) (norm_nonneg _) hsab rfl hcosid himneg
        rw [Complex.ofReal_add] at h; exact h
      · -- hk2 : k = c (1 - ‖1-k/c‖ e^{i(a+γ)})
        have nKA : ‖g K - g A‖ = D * ‖k‖ := by rw [eK, norm_mul, ← hD_def]
        have nKC : ‖g K - g C‖ = D * ‖k - c‖ := by
          rw [show g K - g C = (g B - g A) * (k - c) from by linear_combination eK - eC, norm_mul,
            ← hD_def]
        have nAC : ‖g A - g C‖ = D * ‖c‖ := by
          rw [show g A - g C = (g B - g A) * (-c) from by linear_combination -eC, norm_mul,
            ← hD_def, norm_neg]
        have hwn : ‖k / c‖ = ‖k‖ / ‖c‖ := Complex.norm_div k c
        have hwn1 : ‖1 - k / c‖ = ‖k - c‖ / ‖c‖ := by
          rw [show (1 : ℂ) - k / c = (c - k) / c from by rw [sub_div, div_self hcne],
            Complex.norm_div, norm_sub_rev c k]
        have hcosid : ‖k / c‖ ^ 2 = ‖1 - k / c‖ ^ 2 + 1 - 2 * ‖1 - k / c‖ * Real.cos (a + γ) := by
          have hlaw := EuclideanGeometry.law_cos K C A
          rw [hKCA, hdist K A, hdist K C, hdist A C, nKA, nKC, nAC] at hlaw
          have hlawN : ‖k‖ ^ 2 = ‖k - c‖ ^ 2 + ‖c‖ ^ 2 - 2 * ‖k - c‖ * ‖c‖ * Real.cos (a + γ) := by
            apply mul_left_cancel₀ (mul_pos hDpos hDpos).ne'
            linear_combination hlaw
          rw [hwn, hwn1, div_pow, div_pow]
          field_simp [hcpos.ne']
          linear_combination hlawN
        have himpos : 0 < (1 - k / c).im :=
          imDivPos k (α + β / 2) δ (by linarith [hα, hβ]) hkval
        have hz := hExpPos (k / c) ‖1 - k / c‖ (a + γ) (norm_nonneg _) hsag rfl hcosid himpos
        rw [Complex.ofReal_add] at hz
        rw [mul_comm]; exact (div_eq_iff hcne).mp hz
    -- Step D — invoke the (separately-proven) algebra certificate.
    exact algebra_certificate a b γ r s lam rho c k l ℓ
      hab hag ha hb hg hr hs hℓ_def hk hlc hl2 hk2

theorem certificate_from_angles
    (A B C K L O : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    (hK : InsideTriangle B M C K) (hL : InsideTriangle B N C L)
    (hKangle : InsideAngle L B A K) (hLangle : InsideAngle A C K L)
    (h1 : ∠ K B A = ∠ A C L) (h2 : ∠ L B K = ∠ L N C) (h3 : ∠ L C K = ∠ B M K)
    (hO : IsCircumcentre A K L O)
    (c k l : ℂ)
    (hcdef : c = (g C - g A) / (g B - g A))
    (hkdef : k = (g K - g A) / (g B - g A))
    (hldef : l = (g L - g A) / (g B - g A))
    (hcim : c.im ≠ 0) :
    2 * ((starRingEnd ℂ (c - 1) * l).im) * Complex.normSq k
      + 2 * ((starRingEnd ℂ k * (c - 1)).im) * Complex.normSq l
      - (Complex.normSq c - 1) * (starRingEnd ℂ k * l).im = 0 := by
  rcases lt_or_gt_of_ne hcim with hneg | hpos
  · -- ===== `c.im < 0`: reduce to the positive branch by the global reflection
    -- `ρ : Plane ≃ₗᵢ[ℝ] Plane` with `g (ρ X) = conj (g X)`.  The reflected
    -- configuration satisfies all hypotheses (angles, midpoints, membership,
    -- circumcentre are preserved) and its normalized coordinates are the
    -- conjugates `(conj c, conj k, conj l)` with `0 < (conj c).im`.  The goal
    -- `G` is sign-covariant: `G(conj c, conj k, conj l) = -G(c,k,l)`. =====
    have hgρ : ∀ X : Plane, g (ρ X) = starRingEnd ℂ (g X) := by
      intro X
      simp only [ρ, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply,
        Complex.conjLIE_apply]
    set e : Plane ≃ᵃ[ℝ] Plane := ρ.toAffineIsometryEquiv.toAffineEquiv with he_def
    have heρ : ∀ X : Plane, e X = ρ X := by intro X; rfl
    have hABC' : ¬ Collinear ℝ ({ρ A, ρ B, ρ C} : Set Plane) := by
      rw [← affineIndependent_iff_not_collinear_set] at hABC ⊢
      have hcomp : (![ρ A, ρ B, ρ C] : Fin 3 → Plane) = e ∘ ![A, B, C] := by
        funext i; fin_cases i <;> simp [heρ]
      rw [hcomp]
      exact (AffineEquiv.affineIndependent_iff e).mpr hABC
    have hM' : ρ M = midpoint ℝ (ρ A) (ρ B) := by
      rw [hM, ← heρ, ← heρ, ← heρ, AffineEquiv.map_midpoint]
    have hN' : ρ N = midpoint ℝ (ρ A) (ρ C) := by
      rw [hN, ← heρ, ← heρ, ← heρ, AffineEquiv.map_midpoint]
    have hK' : InsideTriangle (ρ B) (ρ M) (ρ C) (ρ K) := by
      obtain ⟨α, β, δ, hα, hβ, hδ, hs, he⟩ := hK
      exact ⟨α, β, δ, hα, hβ, hδ, hs, by rw [he]; simp [map_add, map_smul]⟩
    have hL' : InsideTriangle (ρ B) (ρ N) (ρ C) (ρ L) := by
      obtain ⟨α, β, δ, hα, hβ, hδ, hs, he⟩ := hL
      exact ⟨α, β, δ, hα, hβ, hδ, hs, by rw [he]; simp [map_add, map_smul]⟩
    have hKangle' : InsideAngle (ρ L) (ρ B) (ρ A) (ρ K) := by
      obtain ⟨s, t, hs, ht, he⟩ := hKangle
      refine ⟨s, t, hs, ht, ?_⟩
      have h2 := congrArg (fun p : Plane => ρ p) he
      simp only [map_sub, map_add, map_smul] at h2
      exact h2
    have hLangle' : InsideAngle (ρ A) (ρ C) (ρ K) (ρ L) := by
      obtain ⟨s, t, hs, ht, he⟩ := hLangle
      refine ⟨s, t, hs, ht, ?_⟩
      have h2 := congrArg (fun p : Plane => ρ p) he
      simp only [map_sub, map_add, map_smul] at h2
      exact h2
    have hAI : ∀ p q r : Plane, ∠ (ρ p) (ρ q) (ρ r) = ∠ p q r := by
      intro p q r
      have := AffineIsometry.angle_map ρ.toAffineIsometryEquiv.toAffineIsometry p q r
      simpa using this
    have h1' : ∠ (ρ K) (ρ B) (ρ A) = ∠ (ρ A) (ρ C) (ρ L) := by rw [hAI, hAI]; exact h1
    have h2' : ∠ (ρ L) (ρ B) (ρ K) = ∠ (ρ L) (ρ N) (ρ C) := by rw [hAI, hAI]; exact h2
    have h3' : ∠ (ρ L) (ρ C) (ρ K) = ∠ (ρ B) (ρ M) (ρ K) := by rw [hAI, hAI]; exact h3
    have hO' : IsCircumcentre (ρ A) (ρ K) (ρ L) (ρ O) := by
      refine ⟨?_, ?_⟩
      · rw [ρ.dist_map, ρ.dist_map]; exact hO.1
      · rw [ρ.dist_map, ρ.dist_map]; exact hO.2
    have hcdef' : starRingEnd ℂ c = (g (ρ C) - g (ρ A)) / (g (ρ B) - g (ρ A)) := by
      rw [hgρ C, hgρ A, hgρ B, ← map_sub (starRingEnd ℂ), ← map_sub (starRingEnd ℂ),
        ← map_div₀, ← hcdef]
    have hkdef' : starRingEnd ℂ k = (g (ρ K) - g (ρ A)) / (g (ρ B) - g (ρ A)) := by
      rw [hgρ K, hgρ A, hgρ B, ← map_sub (starRingEnd ℂ), ← map_sub (starRingEnd ℂ),
        ← map_div₀, ← hkdef]
    have hldef' : starRingEnd ℂ l = (g (ρ L) - g (ρ A)) / (g (ρ B) - g (ρ A)) := by
      rw [hgρ L, hgρ A, hgρ B, ← map_sub (starRingEnd ℂ), ← map_sub (starRingEnd ℂ),
        ← map_div₀, ← hldef]
    have hpos' : 0 < (starRingEnd ℂ c).im := by rw [Complex.conj_im]; linarith
    have hG' := certificate_pos (ρ A) (ρ B) (ρ C) (ρ K) (ρ L) (ρ O) hABC'
      (ρ M) (ρ N) hM' hN' hK' hL' hKangle' hLangle' h1' h2' h3' hO'
      (starRingEnd ℂ c) (starRingEnd ℂ k) (starRingEnd ℂ l) hcdef' hkdef' hldef' hpos'
    have hsign :
        2 * ((starRingEnd ℂ (starRingEnd ℂ c - 1) * starRingEnd ℂ l).im)
            * Complex.normSq (starRingEnd ℂ k)
          + 2 * ((starRingEnd ℂ (starRingEnd ℂ k) * (starRingEnd ℂ c - 1)).im)
            * Complex.normSq (starRingEnd ℂ l)
          - (Complex.normSq (starRingEnd ℂ c) - 1)
            * (starRingEnd ℂ (starRingEnd ℂ k) * starRingEnd ℂ l).im
        = -(2 * ((starRingEnd ℂ (c - 1) * l).im) * Complex.normSq k
          + 2 * ((starRingEnd ℂ k * (c - 1)).im) * Complex.normSq l
          - (Complex.normSq c - 1) * (starRingEnd ℂ k * l).im) := by
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.normSq_apply]
      ring
    linarith [hG', hsign]
  · exact certificate_pos A B C K L O hABC M N hM hN hK hL hKangle hLangle h1 h2 h3 hO
      c k l hcdef hkdef hldef hpos
/-! ## The reduction lemma. -/

set_option maxHeartbeats 1200000 in
theorem normalized_reduction
    (A B C K L O : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    (hK : InsideTriangle B M C K)
    (hL : InsideTriangle B N C L)
    (hKangle : InsideAngle L B A K)
    (hLangle : InsideAngle A C K L)
    (h1 : ∠ K B A = ∠ A C L)
    (h2 : ∠ L B K = ∠ L N C)
    (h3 : ∠ L C K = ∠ B M K)
    (hO : IsCircumcentre A K L O) :
    ∃ c k l o : ℂ,
      (2 * (starRingEnd ℂ o * k).re = Complex.normSq k)
    ∧ (2 * (starRingEnd ℂ o * l).re = Complex.normSq l)
    ∧ (starRingEnd ℂ k * l).im ≠ 0
    ∧ (2 * ((starRingEnd ℂ (c - 1) * l).im) * Complex.normSq k
        + 2 * ((starRingEnd ℂ k * (c - 1)).im) * Complex.normSq l
        - (Complex.normSq c - 1) * (starRingEnd ℂ k * l).im = 0)
    ∧ (dist O M = dist O N ↔ dist o (1/2 : ℂ) = dist o (c/2)) := by
  -- `A ≠ B` from non-collinearity.
  have hAB : A ≠ B := by
    rintro rfl
    apply hABC
    rw [Set.insert_idem]
    exact collinear_pair ℝ _ _
  -- The normalization data.
  set d := g B - g A with hd_def
  have hd : d ≠ 0 := by
    rw [hd_def, sub_ne_zero]; exact fun h => hAB (g.injective h).symm
  set c := (g C - g A) / d with hc_def
  set k := (g K - g A) / d with hk_def
  set l := (g L - g A) / d with hl_def
  set o := (g O - g A) / d with ho_def
  clear_value o l k c d
  have hdnorm : (0 : ℝ) < ‖d‖ := norm_pos_iff.mpr hd
  -- `φ` scales all distances by `1 / ‖d‖`.
  have hscale : ∀ X Y : Plane,
      ‖(g X - g A) / d - (g Y - g A) / d‖ = dist X Y / ‖d‖ := by
    intro X Y
    have hnum : (g X - g A) - (g Y - g A) = g X - g Y := by ring
    rw [div_sub_div_same, hnum, norm_div, ← Complex.dist_eq, g.dist_map]
  -- The three affine identifications: `φB = 1`, `φM = 1/2`, `φN = c/2`.
  have hB1 : (g B - g A) / d = 1 := by rw [← hd_def]; exact div_self hd
  have hgM : g M - g A = (2⁻¹ : ℝ) • (g B - g A) := by
    rw [hM, midpoint_eq_smul_add, map_smul, map_add, invOf_eq_inv]; module
  have hgN : g N - g A = (2⁻¹ : ℝ) • (g C - g A) := by
    rw [hN, midpoint_eq_smul_add, map_smul, map_add, invOf_eq_inv]; module
  have hM_half : (g M - g A) / d = (1/2 : ℂ) := by
    rw [hgM, Complex.real_smul, mul_div_assoc, hB1]; push_cast; norm_num
  have hN_half : (g N - g A) / d = c / 2 := by
    rw [hgN, Complex.real_smul, mul_div_assoc, ← hc_def]; push_cast; ring
  -- `φ`-difference identity.
  have hdiff : ∀ P Q : Plane,
      (g P - g A) / d - (g Q - g A) / d = (g P - g Q) / d := by
    intro P Q; rw [div_sub_div_same]; congr 1; ring
  ------------------------------------------------------------------
  -- (i) circumcentre equations `hOk`, `hOl`.
  ------------------------------------------------------------------
  have honorm : ‖o‖ = dist O A / ‖d‖ := by
    have h := hscale O A
    simp only [sub_self, zero_div, sub_zero] at h
    rw [ho_def]; exact h
  have hOk : 2 * (starRingEnd ℂ o * k).re = Complex.normSq k := by
    have hnorm : ‖o‖ = ‖o - k‖ := by
      have hoknorm : ‖o - k‖ = dist O K / ‖d‖ := by
        rw [ho_def, hk_def]; exact hscale O K
      rw [honorm, hoknorm, hO.1]
    exact re_of_norm_eq o k hnorm
  have hOl : 2 * (starRingEnd ℂ o * l).re = Complex.normSq l := by
    have hnorm : ‖o‖ = ‖o - l‖ := by
      have holnorm : ‖o - l‖ = dist O L / ‖d‖ := by
        rw [ho_def, hl_def]; exact hscale O L
      rw [honorm, holnorm, hO.2]
    exact re_of_norm_eq o l hnorm
  ------------------------------------------------------------------
  -- `c.im ≠ 0` from non-collinearity of `A, B, C`.
  ------------------------------------------------------------------
  have hcim : c.im ≠ 0 := by
    intro h0
    apply hABC
    rw [collinear_iff_of_mem (Set.mem_insert A {B, C})]
    refine ⟨B - A, ?_⟩
    have hc0 : c = (c.re : ℂ) := by apply Complex.ext <;> simp [h0]
    have hcd : g C - g A = c * d := by rw [hc_def]; exact (div_mul_cancel₀ _ hd).symm
    have hCA : C - A = c.re • (B - A) := by
      apply g.injective
      rw [map_sub, map_smul, map_sub, hcd, hd_def, Complex.real_smul, ← hc0]
    intro P hP
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
    rcases hP with h | h | h
    · exact ⟨0, by rw [h]; simp [vadd_eq_add]⟩
    · exact ⟨1, by rw [h]; simp [vadd_eq_add]⟩
    · exact ⟨c.re, by rw [h, vadd_eq_add, ← hCA]; abel⟩
  ------------------------------------------------------------------
  -- (iv) the distance iff.
  ------------------------------------------------------------------
  have hdistOM : dist o (1/2 : ℂ) = dist O M / ‖d‖ := by
    rw [Complex.dist_eq, ho_def, ← hM_half]; exact hscale O M
  have hdistON : dist o (c/2) = dist O N / ‖d‖ := by
    rw [Complex.dist_eq, ho_def, ← hN_half]; exact hscale O N
  have hiff : dist O M = dist O N ↔ dist o (1/2 : ℂ) = dist o (c/2) := by
    rw [hdistOM, hdistON]
    constructor
    · intro h; rw [h]
    · intro h
      have h2 : dist O M / ‖d‖ * ‖d‖ = dist O N / ‖d‖ * ‖d‖ := by rw [h]
      rwa [div_mul_cancel₀ _ hdnorm.ne', div_mul_cancel₀ _ hdnorm.ne'] at h2
  ------------------------------------------------------------------
  -- (ii) `Δ = [k,l] ≠ 0` (non-collinearity of `A, K, L`).
  ------------------------------------------------------------------
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hKeq⟩ := hK
  obtain ⟨α', β', γ', hα', hβ', hγ', hsum', hLeq⟩ := hL
  -- barycentric forms `k = ↑x + ↑y·c`, `l = ↑p + ↑q·c`.
  have hnum : g K - g A = α • (g B - g A) + β • (g M - g A) + γ • (g C - g A) := by
    have hgK : g K = α • g B + β • g M + γ • g C := by
      rw [hKeq]; simp only [map_add, map_smul]
    rw [hgK, show γ = 1 - α - β from by linarith]; module
  have hnumL : g L - g A = α' • (g B - g A) + β' • (g N - g A) + γ' • (g C - g A) := by
    have hgL : g L = α' • g B + β' • g N + γ' • g C := by
      rw [hLeq]; simp only [map_add, map_smul]
    rw [hgL, show γ' = 1 - α' - β' from by linarith]; module
  have hkform : k = ↑(α + β/2) + ↑γ * c := by
    rw [hk_def, hnum, add_div, add_div, smul_div_assoc, smul_div_assoc, smul_div_assoc,
      hB1, hM_half, ← hc_def, Complex.real_smul, Complex.real_smul, Complex.real_smul]
    push_cast; ring
  have hlform : l = ↑α' + ↑(β'/2 + γ') * c := by
    rw [hl_def, hnumL, add_div, add_div, smul_div_assoc, smul_div_assoc, smul_div_assoc,
      hB1, hN_half, ← hc_def, Complex.real_smul, Complex.real_smul, Complex.real_smul]
    push_cast; ring
  -- positivity of the barycentric coordinates.
  have hx : (0:ℝ) < α + β/2 := by linarith
  have hq : (0:ℝ) < β'/2 + γ' := by linarith
  -- `[k,l] = (x q - y p)·Im c`.
  have hbra : (starRingEnd ℂ k * l).im
      = ((α + β/2) * (β'/2 + γ') - γ * α') * c.im := by
    rw [hkform, hlform]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.add_im, Complex.add_re,
      Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im]
    ring
  -- cone relations at `B` and `C` transported through `φ`.
  obtain ⟨s, t, hs, ht, hcone⟩ := hKangle
  obtain ⟨s', t', hs', ht', hconeL⟩ := hLangle
  have hgcone : g K - g B = s • (g L - g B) + t • (g A - g B) := by
    have := congrArg g hcone
    simpa only [map_sub, map_add, map_smul] using this
  have hgconeL : g L - g C = s' • (g A - g C) + t' • (g K - g C) := by
    have := congrArg g hconeL
    simpa only [map_sub, map_add, map_smul] using this
  have hk1 : k - 1 = (g K - g B) / d := by rw [hk_def, ← hB1, hdiff K B]
  have hl1 : l - 1 = (g L - g B) / d := by rw [hl_def, ← hB1, hdiff L B]
  have hlc : l - c = (g L - g C) / d := by rw [hl_def, hc_def, hdiff L C]
  have hkc : k - c = (g K - g C) / d := by rw [hk_def, hc_def, hdiff K C]
  have hab : (g A - g B) / d = -1 := by
    have hh := hdiff A B
    rw [sub_self, zero_div, hB1] at hh
    rw [← hh]; ring
  have hac : (g A - g C) / d = -c := by
    have hh := hdiff A C
    rw [sub_self, zero_div, ← hc_def] at hh
    rw [← hh]; ring
  have hconek : k - 1 = s • (l - 1) + t • (-1 : ℂ) := by
    rw [hk1, hgcone, add_div, smul_div_assoc, smul_div_assoc, ← hl1, hab]
  have hconeL' : l - c = s' • (-c) + t' • (k - c) := by
    rw [hlc, hgconeL, add_div, smul_div_assoc, smul_div_assoc, hac, ← hkc]
  -- extract real coefficient equations.
  have hconek3 : ((↑((α + β/2) - 1) : ℂ) + ↑γ * c)
      = ↑(s * (α' - 1) - t) + ↑(s * (β'/2 + γ')) * c := by
    have hh := hconek
    rw [hkform, hlform, Complex.real_smul, Complex.real_smul] at hh
    push_cast at hh ⊢
    linear_combination hh
  have hconeL2 : ((↑α' : ℂ) + ↑((β'/2 + γ') - 1) * c)
      = ↑(t' * (α + β/2)) + ↑(-s' + t' * (γ - 1)) * c := by
    have hh := hconeL'
    rw [hkform, hlform, Complex.real_smul, Complex.real_smul] at hh
    push_cast at hh ⊢
    linear_combination hh
  obtain ⟨hA1, hB1'⟩ := coeff_match ((α + β/2) - 1) γ (s * (α' - 1) - t)
      (s * (β'/2 + γ')) c hcim hconek3
  obtain ⟨hA2, hB2⟩ := coeff_match α' ((β'/2 + γ') - 1) (t' * (α + β/2))
      (-s' + t' * (γ - 1)) c hcim hconeL2
  -- the two strict cone inequalities.
  have hBineq : (1 - (α + β/2)) * (β'/2 + γ') > γ * (1 - α') := by
    have hBeq : (1 - (α + β/2)) * (β'/2 + γ') - γ * (1 - α') = (β'/2 + γ') * t := by
      linear_combination (-(β'/2 + γ')) * hA1 - (1 - α') * hB1'
    nlinarith [hBeq, mul_pos hq ht]
  have hCineq : (α + β/2) * (1 - (β'/2 + γ')) > α' * (1 - γ) := by
    have hCeq : (α + β/2) * (1 - (β'/2 + γ')) - α' * (1 - γ) = (α + β/2) * s' := by
      linear_combination (-(1 - γ)) * hA2 - (α + β/2) * hB2
    nlinarith [hCeq, mul_pos hx hs']
  have hxqyp : (α + β/2) * (β'/2 + γ') - γ * α' ≠ 0 :=
    akl_noncollinear (α + β/2) γ α' (β'/2 + γ') hx hγ hα' hq hBineq hCineq
  have hΔ : (starRingEnd ℂ k * l).im ≠ 0 := by
    rw [hbra]; exact mul_ne_zero hxqyp hcim
  ------------------------------------------------------------------
  -- (iii) the certificate, from the isolated helper.
  ------------------------------------------------------------------
  have hC := certificate_from_angles A B C K L O hABC M N hM hN
    ⟨α, β, γ, hα, hβ, hγ, hsum, hKeq⟩ ⟨α', β', γ', hα', hβ', hγ', hsum', hLeq⟩
    ⟨s, t, hs, ht, hcone⟩ ⟨s', t', hs', ht', hconeL⟩ h1 h2 h3 hO c k l
    (by rw [hc_def, hd_def]) (by rw [hk_def, hd_def]) (by rw [hl_def, hd_def]) hcim
  exact ⟨c, k, l, o, hOk, hOl, hΔ, hC, hiff⟩

/-! ## Assembly of `main_theorem`. -/

/-- With the configuration described above, the circumcentre
`O` of triangle `AKL` satisfies `OM = ON`, where `M`, `N` are the midpoints of
`AB`, `AC`. -/
theorem main_theorem
    (A B C K L O : Plane)
    -- `ABC` is a nondegenerate triangle.
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    -- `M`, `N` are the midpoints of `AB`, `AC`.
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    -- `K` is inside triangle `BMC`; `L` is inside triangle `BNC`.
    (hK : InsideTriangle B M C K)
    (hL : InsideTriangle B N C L)
    -- `K` inside angle `∠ L B A`; `L` inside angle `∠ A C K`.
    (hKangle : InsideAngle L B A K)
    (hLangle : InsideAngle A C K L)
    -- The three angle equalities.
    (h1 : ∠ K B A = ∠ A C L)
    (h2 : ∠ L B K = ∠ L N C)
    (h3 : ∠ L C K = ∠ B M K)
    -- `O` is the circumcentre of triangle `AKL`.
    (hO : IsCircumcentre A K L O) :
    dist O M = dist O N := by
  obtain ⟨c, k, l, o, hOk, hOl, hΔ, hC, hiff⟩ :=
    normalized_reduction A B C K L O hABC M N hM hN hK hL hKangle hLangle h1 h2 h3 hO
  have hF1 : 2 * (starRingEnd ℂ o * (c - 1)).re = (Complex.normSq c - 1) / 2 :=
    circumcenter_determinant c k l o hΔ hC hOk hOl
  have hbridge : dist o (1/2 : ℂ) = dist o (c/2) := distance_bridge c o hF1
  exact hiff.mpr hbridge

#print axioms main_theorem
