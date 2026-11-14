# Reduce-then-evaluate: dist O M = dist O N for MechMath IMO 2026 Q2

| | |
|---|---|
| Kind | instance |
| Move | other |
| Language | lean |
| Status | draft |
| Source | [mechmath-imo2026](../../sources/mechmath-imo2026/SOURCE.md) at `47ff510110dd` |
| Licence | `LicenseRef-unknown` |
| Licence recorded | 2026-11-14T09:39:12Z |

## Intent

This is a theorem-scale assembly: the competition goal `dist O M = dist O N`
is proved by reducing it, through one normalisation lemma, to an equivalent
statement in normalised complex coordinates, then closing that statement with
two algebra lemmas chained through a real-part identity, and pulling the
result back through the iff. The main theorem's proof (the glue) is seven
lines that only apply the three named lemmas; all the geometry lives below
them.

## The decomposition

### parent `main_theorem`: [`IMO2026/Q2/solution.lean` lines 1167-1191](https://github.com/MechMath/IMO2026/blob/47ff510110dd400c98aee2ead3be0f53f7b8ba04/IMO2026/Q2/solution.lean#L1167-L1191) ([local copy](code/IMO2026/Q2/solution.lean))

```lean
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
```

### child `normalized_reduction`: [`IMO2026/Q2/solution.lean` lines 957-1160](https://github.com/MechMath/IMO2026/blob/47ff510110dd400c98aee2ead3be0f53f7b8ba04/IMO2026/Q2/solution.lean#L957-L1160) ([local copy](code/IMO2026/Q2/solution.lean))

```lean
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
```

### child `circumcenter_determinant`: [`IMO2026/Q2/solution.lean` lines 92-114](https://github.com/MechMath/IMO2026/blob/47ff510110dd400c98aee2ead3be0f53f7b8ba04/IMO2026/Q2/solution.lean#L92-L114) ([local copy](code/IMO2026/Q2/solution.lean))

```lean
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
```

### child `distance_bridge`: [`IMO2026/Q2/solution.lean` lines 61-70](https://github.com/MechMath/IMO2026/blob/47ff510110dd400c98aee2ead3be0f53f7b8ba04/IMO2026/Q2/solution.lean#L61-L70) ([local copy](code/IMO2026/Q2/solution.lean))

```lean
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
```

### How the parts fit

The glue is a three-step chain, one step per child:

```
main_theorem
├── normalized_reduction       → c, k, l, o, hOk, hOl, hΔ, hC, hiff
│     ├── re_of_norm_eq        (hOk, hOl)
│     ├── coeff_match          (hA1/hB1, hA2/hB2)
│     ├── akl_noncollinear     (hΔ)
│     └── certificate_from_angles  (hC)
│           └── certificate_pos
│                 └── algebra_certificate
├── circumcenter_determinant   → hF1 from hOk, hOl, hC, hΔ
└── distance_bridge            → hbridge from hF1
```

`main_theorem` first calls `normalized_reduction` (line 1187) and destructures
its result into `c, k, l, o` and four facts: `hOk`, `hOl` (the circumcentre
equations in the normalised frame), `hΔ` (the determinant nonvanishing), `hC`
(the algebra certificate), and `hiff : dist O M = dist O N ↔ dist o (1/2) =
dist o (c/2)`. It then calls `circumcenter_determinant c k l o hΔ hC hOk hOl`
(line 1189) to get the real-part identity `hF1`, feeds that to
`distance_bridge c o hF1` (line 1190) to get the normalised distance equality
`hbridge`, and finishes with `exact hiff.mpr hbridge` (line 1191), pulling the
normalised equality back to the original goal.

Why each child is a good leaf:

- `normalized_reduction` is a self-contained statement — an `∃ c k l o` with
  the four facts and the iff — whose proof closes on its own from named
  siblings and library lemmas, with no sorry. It is the heavy leaf: it
  performs the whole coordinate normalisation (A ↦ 0, B ↦ 1, M ↦ 1/2,
  N ↦ c/2) and chains `certificate_from_angles → certificate_pos →
  algebra_certificate` (depth 4 below the main theorem).
- `circumcenter_determinant` is self-contained: it derives `hF1` by a
  `linear_combination` of `hC`, `hOk`, `hOl` and then cancels the nonzero
  determinant `hΔ` with `mul_right_cancel₀`.
- `distance_bridge` is self-contained: it expands both sides to `Complex.normSq`
  and closes by `nlinarith`.

So the main theorem carries no geometry of its own: reduce, evaluate, pull
back.

## Why it is good

1. The glue applies three named lemmas and nothing else — `normalized_reduction`
   (line 1187), `circumcenter_determinant` (1189), `distance_bridge` (1190) —
   then `exact hiff.mpr hbridge` (check: `normalized_reduction` occurs in the
   parent site, [lines 1167-1191](https://github.com/MechMath/IMO2026/blob/47ff510110dd400c98aee2ead3be0f53f7b8ba04/IMO2026/Q2/solution.lean#L1167-L1191)).
2. None of the three children nor the parent closes by `sorry`/`admit`/`axiom`:
   the range 61-1191 of the copied file is clean (check:
   [lines 61-1191](https://github.com/MechMath/IMO2026/blob/47ff510110dd400c98aee2ead3be0f53f7b8ba04/IMO2026/Q2/solution.lean#L61-L1191)).
3. The glue is 7 proof lines (1185-1191) driving 237 lines of child proof
   (204 + 23 + 10), so the reduction concentrates the difficulty in the
   leaves (measurement, from the copied file).
4. The authors stage the file for exactly this decomposition: section headers
   "The algebra certificate (proven)", "The crux lemma", "The reduction
   lemma", "Assembly of `main_theorem`", and two of the three children carry a
   docstring recording its scratch origin ("Proof pasted from
   `scratch/distance_bridge.lean`", "Proof pasted from
   `scratch/circumcenter_determinant.lean`")
   (author-statement, [lines 116, 255, 954, 1162, 60, 91](https://github.com/MechMath/IMO2026/blob/47ff510110dd400c98aee2ead3be0f53f7b8ba04/IMO2026/Q2/solution.lean#L116)).

In my opinion the reusable detail is the *reduction-iff* shape: a whole
coordinate transformation is packaged as one named lemma returning an iff
plus the few facts the later steps need, so the final proof is a short chain
"reduce → evaluate → pull back" that a planner could target directly.

## When to use it, and when not

Use it when the goal is a geometric equality (distances, angles) that becomes
a simple algebraic identity after an explicit coordinate normalisation; when
the geometry admits an isometry into coordinates (here `g : Plane ≃ₗᵢ[ℝ] ℂ`);
when the normalisation returns an iff, so the reduced goal is equivalent; and
when each step of the evaluation — the certificate, the determinant identity,
the distance bridge — can be stated as its own named lemma whose hypotheses
the reduction supplies exactly.

Avoid it when the reduction is only one direction (the pull-back at the end
needs an iff, or at least a suffices direction); when the normalisation itself
carries most of the difficulty, so the reduction lemma is really the theorem
rather than a leaf; or when the reduced algebra statement still needs a
certificate too large to state and prove as its own lemma.

## Consequences

The move creates an obligation for the reduction lemma to return an iff (or
at least the pull-back direction used at the end) and for the certificate to
be discharged under exactly the hypotheses the reduction supplies (hOk, hOl,
hΔ, hC). It pushes depth down rather than away: `normalized_reduction` is
itself 204 lines and chains `certificate_from_angles → certificate_pos →
algebra_certificate`. Failure modes: a reduction that drops a hypothesis the
algebra step later needs; an iff that is only one-way so `hiff.mpr` fails; a
certificate whose `linear_combination` (the `KEY` identity at line 201) is too
unwieldy to reproduce.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: normalized_reduction@IMO2026/Q2/solution.lean:1187, circumcenter_determinant@IMO2026/Q2/solution.lean:1189, distance_bridge@IMO2026/Q2/solution.lean:1190; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, normalized_reduction) -> cites: normalized_reduction occurs at IMO2026/Q2/solution.lean:1187 | check_claims.py |
| 2 | verified | no_sorry(IMO2026/Q2/solution.lean, 61-1191) -> no_sorry: none of sorry, admit, axiom in IMO2026/Q2/solution.lean:61-1191 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/MechMath/IMO2026 at commit `47ff510110dd400c98aee2ead3be0f53f7b8ba04`, under `LicenseRef-unknown`; see the [source note](../../sources/mechmath-imo2026/SOURCE.md) for the licence text and attribution.
