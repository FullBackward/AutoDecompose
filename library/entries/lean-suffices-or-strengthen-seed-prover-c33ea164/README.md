# Strengthen to pairwise non-distinctness, then convert to the card bound (IMO 2025 P1)

| | |
|---|---|
| Kind | instance |
| Move | suffices-or-strengthen |
| Language | lean |
| Status | draft |
| Source | [seed-prover](../../sources/seed-prover/SOURCE.md) at `38c59cebaf96` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T09:46:53Z |

## Intent

A non-sunny line (slope `l.1 ≠ 0` and `≠ −1`) is shown to meet the boundary of
the triangular lattice-point set in at most two points, by first strengthening
the goal to the pairwise statement "any three points of the filtered set have
two equal" (`h_main`) and then converting that to the cardinality bound `≤ 2`
(`h_final`). The file is Seed-Prover's own generated solution to IMO 2025 P1,
so the strengthen-then-convert split is a decomposition the prover produced.

## The decomposition

### parent `non_sunny_lines_cover_at_most_2_points_on_boundary`: [`SeedProver/imo2025/IMO2025/P1.lean` lines 3432-3439](https://github.com/ByteDance-Seed/Seed-Prover/blob/38c59cebaf969ac259196eb091757518d5b54c67/SeedProver/imo2025/IMO2025/P1.lean#L3432-L3439) ([local copy](code/SeedProver/imo2025/IMO2025/P1.lean))

```lean
theorem non_sunny_lines_cover_at_most_2_points_on_boundary (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hn : 3 ≤ n) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) (l : ℝ × ℝ) (h_non_sunny : l.1 ≠ 0 ∧ l.1 ≠ -1) :
  (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧
    (l.1 * p.1 + l.2 = p.2)) points).card ≤ 2   := by

  have h_main : ∀ (x y z : ℕ × ℕ), x ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → y ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → z ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → x = y ∨ x = z ∨ y = z := by
    exact non_sunny_lines_cover_at_most_2_points_on_boundary_h_main n k verts lines points hn hcard hallpoints hmain hk l h_non_sunny

  exact non_sunny_lines_cover_at_most_2_points_on_boundary_h_final n k verts lines points hn hcard hallpoints hmain hk l h_non_sunny h_main
```

### child `non_sunny_lines_cover_at_most_2_points_on_boundary_h_main`: [`SeedProver/imo2025/IMO2025/P1.lean` lines 3285-3430](https://github.com/ByteDance-Seed/Seed-Prover/blob/38c59cebaf969ac259196eb091757518d5b54c67/SeedProver/imo2025/IMO2025/P1.lean#L3285-L3430) ([local copy](code/SeedProver/imo2025/IMO2025/P1.lean))

```lean
lemma non_sunny_lines_cover_at_most_2_points_on_boundary_h_main (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hn : 3 ≤ n)
  (hcard : lines.card + verts.card = n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x))
  (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k)
  (l : ℝ × ℝ)
  (h_non_sunny : l.1 ≠ 0 ∧ l.1 ≠ -1):
  ∀ (x y z : ℕ × ℕ), x ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → y ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → z ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → x = y ∨ x = z ∨ y = z := by
  intros x y z hx hy hz
  by_cases h1 : x = y
  · tauto
  by_cases h2 : x = z
  · tauto
  by_cases h3 : y = z
  · tauto
  have h1' : x ≠ y := by tauto
  have h2' : x ≠ z := by tauto
  have h3' : y ≠ z := by tauto
  have hx_prop : (x.1 = 1 ∨ x.2 = 1 ∨ x.1 + x.2 = n + 1) ∧ (l.1 * (x.1 : ℝ) + l.2 = (x.2 : ℝ)) := by
    simp only [Finset.mem_filter] at hx
    tauto
  have hy_prop : (y.1 = 1 ∨ y.2 = 1 ∨ y.1 + y.2 = n + 1) ∧ (l.1 * (y.1 : ℝ) + l.2 = (y.2 : ℝ)) := by
    simp only [Finset.mem_filter] at hy
    tauto
  have hz_prop : (z.1 = 1 ∨ z.2 = 1 ∨ z.1 + z.2 = n + 1) ∧ (l.1 * (z.1 : ℝ) + l.2 = (z.2 : ℝ)) := by
    simp only [Finset.mem_filter] at hz
    tauto
  have hx_cond : x.1 = 1 ∨ x.2 = 1 ∨ x.1 + x.2 = n + 1 := hx_prop.1
  have hy_cond : y.1 = 1 ∨ y.2 = 1 ∨ y.1 + y.2 = n + 1 := hy_prop.1
  have hz_cond : z.1 = 1 ∨ z.2 = 1 ∨ z.1 + z.2 = n + 1 := hz_prop.1
  rcases hx_cond with (hx1 | hx2 | hx3)
  · -- Case x.1 = 1
    rcases hy_cond with (hy1 | hy2 | hy3)
    · -- Subcase y.1 = 1
      have h_x_eq_y : x = y := by
        apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny x y hx_prop hy_prop
        tauto
      tauto
    · -- Subcase y.2 = 1
      rcases hz_cond with (hz1 | hz2 | hz3)
      · -- Sub-subcase z.1 = 1
        have h_z_eq_x : z = x := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny z x hz_prop hx_prop
          tauto
        tauto
      · -- Sub-subcase z.2 = 1
        have h_y_eq_z : y = z := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny y z hy_prop hz_prop
          tauto
        tauto
      · -- Sub-subcase z.1 + z.2 = n + 1
        exfalso
        exact non_sunny_lines_cover_at_most_2_points_on_boundary_contradiction_from_conditions n k verts lines points l h_non_sunny x y z hx hy hz hx1 hy2 hz3 h1' (by tauto) (by tauto) hn hallpoints
    · -- Subcase y.1 + y.2 = n + 1
      rcases hz_cond with (hz1 | hz2 | hz3)
      · -- Sub-subcase z.1 = 1
        have h_z_eq_x : z = x := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny z x hz_prop hx_prop
          tauto
        tauto
      · -- Sub-subcase z.2 = 1
        exfalso
        exact non_sunny_lines_cover_at_most_2_points_on_boundary_contradiction_from_conditions n k verts lines points l h_non_sunny x z y hx hz hy hx1 hz2 hy3 (by tauto) (by tauto) (by tauto) hn hallpoints
      · -- Sub-subcase z.1 + z.2 = n + 1
        have h_y_eq_z : y = z := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny y z hy_prop hz_prop
          tauto
        tauto
  · -- Case x.2 = 1
    rcases hy_cond with (hy1 | hy2 | hy3)
    · -- Subcase y.1 = 1
      rcases hz_cond with (hz1 | hz2 | hz3)
      · -- Sub-subcase z.1 = 1
        have h_y_eq_z : y = z := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny y z hy_prop hz_prop
          tauto
        tauto
      · -- Sub-subcase z.2 = 1
        have h_x_eq_z : x = z := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny x z hx_prop hz_prop
          tauto
        tauto
      · -- Sub-subcase z.1 + z.2 = n + 1
        exfalso
        exact non_sunny_lines_cover_at_most_2_points_on_boundary_contradiction_from_conditions n k verts lines points l h_non_sunny y x z hy hx hz hy1 hx2 hz3 (by tauto) (by tauto) (by tauto) hn hallpoints
    · -- Subcase y.2 = 1
      have h_x_eq_y : x = y := by
        apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny x y hx_prop hy_prop
        tauto
      tauto
    · -- Subcase y.1 + y.2 = n + 1
      rcases hz_cond with (hz1 | hz2 | hz3)
      · -- Sub-subcase z.1 = 1
        exfalso
        exact non_sunny_lines_cover_at_most_2_points_on_boundary_contradiction_from_conditions n k verts lines points l h_non_sunny z x y hz hx hy hz1 hx2 hy3 (by tauto) (by tauto) (by tauto) hn hallpoints
      · -- Sub-subcase z.2 = 1
        have h_x_eq_z : x = z := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny x z hx_prop hz_prop
          tauto
        tauto
      · -- Sub-subcase z.1 + z.2 = n + 1
        have h_y_eq_z : y = z := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny y z hy_prop hz_prop
          tauto
        tauto
  · -- Case x.1 + x.2 = n + 1
    rcases hy_cond with (hy1 | hy2 | hy3)
    · -- Subcase y.1 = 1
      rcases hz_cond with (hz1 | hz2 | hz3)
      · -- Sub-subcase z.1 = 1
        have h_y_eq_z : y = z := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny y z hy_prop hz_prop
          tauto
        tauto
      · -- Sub-subcase z.2 = 1
        exfalso
        exact non_sunny_lines_cover_at_most_2_points_on_boundary_contradiction_from_conditions n k verts lines points l h_non_sunny y z x hy hz hx hy1 hz2 hx3 (by tauto) (by tauto) (by tauto) hn hallpoints
      · -- Sub-subcase z.1 + z.2 = n + 1
        have h_x_eq_z : x = z := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny x z hx_prop hz_prop
          tauto
        tauto
    · -- Subcase y.2 = 1
      rcases hz_cond with (hz1 | hz2 | hz3)
      · -- Sub-subcase z.1 = 1
        exfalso
        exact non_sunny_lines_cover_at_most_2_points_on_boundary_contradiction_from_conditions n k verts lines points l h_non_sunny z y x hz hy hx hz1 hy2 hx3 (by tauto) (by tauto) (by tauto) hn hallpoints
      · -- Sub-subcase z.2 = 1
        have h_y_eq_z : y = z := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny y z hy_prop hz_prop
          tauto
        tauto
      · -- Sub-subcase z.1 + z.2 = n + 1
        have h_x_eq_z : x = z := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny x z hx_prop hz_prop
          tauto
        tauto
    · -- Subcase y.1 + y.2 = n + 1
      have h_x_eq_y : x = y := by
        apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny x y hx_prop hy_prop
        tauto
      tauto
```

### child `non_sunny_lines_cover_at_most_2_points_on_boundary_h_final`: [`SeedProver/imo2025/IMO2025/P1.lean` lines 3261-3283](https://github.com/ByteDance-Seed/Seed-Prover/blob/38c59cebaf969ac259196eb091757518d5b54c67/SeedProver/imo2025/IMO2025/P1.lean#L3261-L3283) ([local copy](code/SeedProver/imo2025/IMO2025/P1.lean))

```lean
lemma non_sunny_lines_cover_at_most_2_points_on_boundary_h_final (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hn : 3 ≤ n)
  (hcard : lines.card + verts.card = n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x))
  (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k)
  (l : ℝ × ℝ)
  (h_non_sunny : l.1 ≠ 0 ∧ l.1 ≠ -1)
  (h_main : ∀ (x y z : ℕ × ℕ), x ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → y ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → z ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → x = y ∨ x = z ∨ y = z):
  (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points).card ≤ 2 := by
  by_contra h
  have h₁ : (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points).card > 2 := by linarith
  have h₂ : ∃ (x y z : ℕ × ℕ), x ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) ∧ y ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) ∧ z ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
    have h₃ : (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points).card > 2 := h₁
    have h₄ : ∃ (x y z : ℕ × ℕ), x ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) ∧ y ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) ∧ z ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
      exact?
    exact h₄
  rcases h₂ with ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩
  have h₃ := h_main x y z hx hy hz
  tauto
```

How the parts fit. The parent's proof (the 8-line glue) does two things: it
proves the strengthened statement with `have h_main : (any three points of the
filtered set have two equal) := by exact …h_main…` (line 3437), then converts
that to the target with `exact …h_final … h_main` (line 3439). The cardinality
bound is obtained by strengthen-then-convert, and the glue is nothing but the
two citations.

Lemma graph (each arrow is a citation, found by reading the file):

```
non_sunny_lines_cover_at_most_2_points_on_boundary   (parent, 3432-3439)
├─ h_main   (child, 3285-3430)  — the strengthened pairwise statement
│   ├─ same_boundary_condition_implies_eq   (2898-2972)  — leaf
│   └─ contradiction_from_conditions        (3235-3258)
│        └─ final                           (3214-3233)
│             └─ main                       (2975-3212)  — leaf
└─ h_final  (child, 3261-3283)  — the conversion
```

`h_main` closes by a 3×3×3 case analysis: for each of `x`, `y`, `z` the point
satisfies one of the three boundary conditions (`p.1 = 1`, `p.2 = 1`,
`p.1 + p.2 = n + 1`). When two points share a boundary,
`same_boundary_condition_implies_eq` shows they are equal (a line of slope
`l.1 ≠ 0`, `≠ −1` meets one boundary in at most one point); when the three
points sit on the three distinct boundaries, `contradiction_from_conditions`
derives a contradiction. `h_final` closes by `by_contra`: if the cardinality
exceeded 2, a finite set of more than two elements has three distinct elements
(the `have h₄ … exact?` step), which `h_main` forbids.

Why each lemma is a good leaf:

- `h_main` is not itself a leaf — it is the strengthened statement that carries
  the argument, and it calls two helpers.
- `same_boundary_condition_implies_eq` (2898-2972) is a self-contained leaf:
  it closes by linear algebra alone (`linarith`, `mul_left_cancel₀`, `omega`)
  on the equation `l.1 · p.1 + l.2 = p.2`, using only `h_non_sunny` and the two
  points' shared boundary condition.
- `main` (2975-3212) is a self-contained leaf: it derives `False` by
  arithmetic/`nlinarith` on the line equation, citing no project lemma.
- `h_final` is a self-contained leaf at the top: the conversion is generic
  finite-set reasoning, closed by `exact?` and `tauto` against `h_main`.

## Why it is good

1. The parent site is 8 lines long (check, `lines(parent, 8)`): the whole
   theorem is two citations — one `have` proving the strengthened statement and
   one `exact` applying the conversion (lines 3432-3439).
2. The glue cites the strengthened child
   `non_sunny_lines_cover_at_most_2_points_on_boundary_h_main` (check,
   `cites(parent, …_h_main)`), at line 3437.
3. The glue cites the conversion child
   `non_sunny_lines_cover_at_most_2_points_on_boundary_h_final` (check,
   `cites(parent, …_h_final)`), at line 3439.
4. No `sorry`/`admit`/`axiom` closes any goal in the decomposition — the two
   children and the parent, lines 3261-3439 (check, `no_sorry(...)`).
5. The theorem-scale shape is `direct_lemmas=2`, `glue_lines=8`,
   `child_lines=[146, 23]`, and the deepest checked chain of project lemmas
   below the parent has depth 4 — `parent → h_main →
   contradiction_from_conditions → final → main` (measurement).

In my opinion the move to copy is not the specific geometry but the
strengthen-then-convert split itself: the cardinality bound is left unproved
until the pairwise statement is proved, and the conversion (`h_final`) is
generic — it would convert "no three distinct elements" to `card ≤ 2` for any
predicate `P`, not just this line-and-boundary condition.

## When to use it, and when not

Use it when a finite-set cardinality bound `(Finset.filter P s).card ≤ 2` is
hard to reach by counting the filter directly, but the equivalent "no three
distinct elements" statement is exactly what a case analysis on the predicate
can show, and the conversion from "no three distinct" to `card ≤ 2` is a
generic finite-set fact. Here the predicate is a disjunctive boundary condition
conjoined with a line-membership equation, and the boundary disjunction gives
finitely many cases, each a linear equation in the slope `l.1`.

Avoid it when the target cardinality is not equivalent to pairwise
non-distinctness (a bound of 1, or a bound over an infinite set or a multiset),
or when the pairwise statement does not split more cleanly than the original —
the strengthening only pays off if the case analysis it enables is simpler than
counting directly.

## Consequences

The move splits the goal into a strengthened statement (`h_main`, the hard case
analysis) and a generic conversion (`h_final`, from pairwise non-distinctness
to `card ≤ 2`). The two halves must meet exactly: `h_final`'s hypothesis
`h_main` is verbatim `h_main`'s conclusion, and the glue passes it unchanged.
The equivalence relies on the set being finite (a `Finset`), so that "no three
distinct elements" is exactly `card ≤ 2`. Failure modes: the strengthened
statement is not actually equivalent to the target; or the case analysis in
`h_main` branches on conditions that do not cover the strengthened statement
(here the 3×3×3 cases come from `p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1` for
each of `x`, `y`, `z`).

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: non_sunny_lines_cover_at_most_2_points_on_boundary_h_main@SeedProver/imo2025/IMO2025/P1.lean:3437, non_sunny_lines_cover_at_most_2_points_on_boundary_h_final@SeedProver/imo2025/IMO2025/P1.lean:3439; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(parent, 8) -> lines: site parent has 8 lines | check_claims.py |
| 2 | verified | cites(parent, non_sunny_lines_cover_at_most_2_points_on_boundary_h_main) -> cites: non_sunny_lines_cover_at_most_2_points_on_boundary_h_main occurs at SeedProver/imo2025/IMO2025/P1.lean:3437 | check_claims.py |
| 3 | verified | cites(parent, non_sunny_lines_cover_at_most_2_points_on_boundary_h_final) -> cites: non_sunny_lines_cover_at_most_2_points_on_boundary_h_final occurs at SeedProver/imo2025/IMO2025/P1.lean:3439 | check_claims.py |
| 4 | verified | no_sorry(SeedProver/imo2025/IMO2025/P1.lean, 3261-3439) -> no_sorry: none of sorry, admit, axiom in SeedProver/imo2025/IMO2025/P1.lean:3261-3439 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/ByteDance-Seed/Seed-Prover at commit `38c59cebaf969ac259196eb091757518d5b54c67`, under `Apache-2.0`; see the [source note](../../sources/seed-prover/SOURCE.md) for the licence text and attribution.
