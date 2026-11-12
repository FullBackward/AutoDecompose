# Iff-split of the IMO 2026 P5 answer: admissible f are x ↦ x + c

| | |
|---|---|
| Kind | instance |
| Move | iff-split |
| Language | lean |
| Status | draft |
| Source | [pramaana-imo2026](../../sources/pramaana-imo2026/SOURCE.md) at `788fddc53c46` |
| Licence | `MIT` |

## Intent

Characterise the functions satisfying the IMO 2026 P5 inequality as exactly the
affine family `x ↦ x + c` with `c ≥ 0`. The proof is an `iff` split: `constructor`
turns `Fact_condition f ↔ f ∈ answer` into a forward direction that exhibits the
witness `c = f 1 - 1` (closed by `d_nonneg` and `g_const`) and a backward
direction that is exactly the verification lemma `easy_dir`.

## The decomposition

### parent `answer_correctness`: [`IMO2026/Q5/solution.lean` lines 223-236](https://github.com/pramaana-labs/imo2026-lean/blob/788fddc53c463d5d40d4680fb9bfd7b0f96f1063/IMO2026/Q5/solution.lean#L223-L236) ([local copy](code/IMO2026/Q5/solution.lean))

```lean
theorem answer_correctness
    (f : ℝ → ℝ)
    (ha_pos : Assumption_pos f)
    : Fact_condition f ↔ f ∈ answer := by
  constructor
  · intro hf
    refine ⟨f 1 - 1, ?_, ?_⟩
    · have := d_nonneg f ha_pos hf (y := 1) one_pos
      linarith
    · intro x hx
      have := g_const f ha_pos hf hx
      linarith
  · rintro ⟨c, hc, hfc⟩
    exact easy_dir f c hc hfc
```

### child `d_nonneg`: [`IMO2026/Q5/solution.lean` lines 78-90](https://github.com/pramaana-labs/imo2026-lean/blob/788fddc53c463d5d40d4680fb9bfd7b0f96f1063/IMO2026/Q5/solution.lean#L78-L90) ([local copy](code/IMO2026/Q5/solution.lean))

```lean
lemma d_nonneg (f : ℝ → ℝ) (ha : Assumption_pos f) (hf : Fact_condition f)
    {y : ℝ} (hy : 0 < y) : 0 ≤ f y - y := by
  by_contra h
  have h : f y - y < 0 := not_le.mp h
  set d := f y - y with hd
  have hdpos : 0 < -d := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (y / (-d))
  have h2 : y / (-d) * (-d) < n * (-d) := mul_lt_mul_of_pos_right hn hdpos
  rw [div_mul_cancel₀ _ (ne_of_gt hdpos)] at h2
  have hnd : (n:ℝ) * (-d) = -((n:ℝ)*d) := by ring
  rw [hnd] at h2
  have hpos := (orbit f ha hf hy n).1
  linarith
```

### child `g_const`: [`IMO2026/Q5/solution.lean` lines 191-202](https://github.com/pramaana-labs/imo2026-lean/blob/788fddc53c463d5d40d4680fb9bfd7b0f96f1063/IMO2026/Q5/solution.lean#L191-L202) ([local copy](code/IMO2026/Q5/solution.lean))

```lean
lemma g_const (f : ℝ → ℝ) (ha : Assumption_pos f) (hf : Fact_condition f)
    {x : ℝ} (hx : 0 < x) : f x - x = f 1 - 1 := by
  have h1 := d_nonneg f ha hf hx
  have h2 := d_nonneg f ha hf one_pos
  rcases eq_or_lt_of_le h1 with hx0 | hx0
  · rcases eq_or_lt_of_le h2 with h10 | h10
    · rw [← hx0, ← h10]
    · exact (no_mixed f ha hf one_pos hx (by linarith) h10).elim
  · rcases eq_or_lt_of_le h2 with h10 | h10
    · exact (no_mixed f ha hf hx one_pos (by linarith) hx0).elim
    · exact le_antisymm (pos_d_le f ha hf hx one_pos h10)
        (pos_d_le f ha hf one_pos hx hx0)
```

### child `easy_dir`: [`IMO2026/Q5/solution.lean` lines 204-221](https://github.com/pramaana-labs/imo2026-lean/blob/788fddc53c463d5d40d4680fb9bfd7b0f96f1063/IMO2026/Q5/solution.lean#L204-L221) ([local copy](code/IMO2026/Q5/solution.lean))

```lean
lemma easy_dir (f : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hfc : ∀ x : ℝ, 0 < x → f x = x + c) : Fact_condition f := by
  intro x y hx hy
  rw [hfc x hx, hfc y hy]
  constructor
  · rw [ge_iff_le]
    have h1 : ((x + c + y)/2)^2 ≤ (x^2 + (y+c)^2)/2 := by
      nlinarith [sq_nonneg (x - y - c)]
    have h2 : (0:ℝ) ≤ (x + c + y)/2 := by positivity
    calc (x + c + y)/2 = Real.sqrt (((x + c + y)/2)^2) := (Real.sqrt_sq h2).symm
      _ ≤ Real.sqrt ((x^2 + (y+c)^2)/2) := Real.sqrt_le_sqrt h1
  · rw [ge_iff_le]
    have h1 : x*(y+c) ≤ ((x + c + y)/2)^2 := by
      nlinarith [sq_nonneg (x - y - c)]
    have h2 : (0:ℝ) ≤ (x + c + y)/2 := by positivity
    calc Real.sqrt (x*(y+c)) ≤ Real.sqrt (((x + c + y)/2)^2) :=
        Real.sqrt_le_sqrt h1
      _ = (x + c + y)/2 := Real.sqrt_sq h2
```

How the parts fit. The parent `answer_correctness` (lines 223-236) is a 14-line
glue whose only structural step is `constructor` (line 227), splitting the
biconditional into its two directions. The forward direction (`intro hf`)
exhibits the witness `c = f 1 - 1` via `refine ⟨f 1 - 1, ?_, ?_⟩` and closes its
two obligations from named lemmas: `0 ≤ f 1 - 1` from `d_nonneg` at `y = 1`
(line 230), and `f x = x + (f 1 - 1)` from `g_const` (line 233). The backward
direction (`rintro ⟨c, hc, hfc⟩`) is the one-liner `exact easy_dir f c hc hfc`
(line 236).

The lemma graph below the theorem (project lemmas only; each edge is a use in
the proof body):

    answer_correctness
      ├─ forward ─ d_nonneg ── orbit ── key_ff ── ineqA
      ├─ forward ─ g_const ── d_nonneg, no_mixed, pos_d_le
      │              ├─ no_mixed ── d_nonneg, pos_d_le, orbit, ineqA, ineqB
      │              └─ pos_d_le ── orbit, ineqA
      └─ backward ─ easy_dir   (leaf: calc + nlinarith only)

The three direct children are good leaves:

- `d_nonneg` (78-90) states one fact alone: every positive point has non-negative
  displacement. Its proof closes by contradiction against the named sibling
  `orbit` (`have hpos := (orbit f ha hf hy n).1`, line 89) and `linarith`.
- `g_const` (191-202) states the constancy of the displacement,
  `f x - x = f 1 - 1`, and closes from the named siblings `d_nonneg` (lines
  193-194), `no_mixed` (lines 198, 200) and `pos_d_le` (lines 201-202); the
  `rcases` on `eq_or_lt_of_le` separates the fixed from the non-fixed cases.
- `easy_dir` (204-221) is the self-contained verification that any `x ↦ x + c`
  with `c ≥ 0` satisfies `Fact_condition`; it closes entirely by `nlinarith`,
  `positivity` and two `calc` chains, importing nothing from the rest of the file.

The longest chain of project lemmas below the theorem that I checked has depth 6:
`answer_correctness → g_const → no_mixed → d_nonneg → orbit → key_ff → ineqA`
(edges at lines 233, 198, 146, 89, 66, 45). `ineqA` and `ineqB` are leaves,
closed by `nlinarith` alone.

## Why it is good

1. The parent `answer_correctness` closes from the three direct children:
   `constructor` splits the iff (line 227); the forward direction is closed by
   `d_nonneg` (line 230) and `g_const` (line 233); the backward direction by
   `easy_dir` (line 236). *(check; permalink lines 223-236.)*
2. The file has no `sorry`, `admit` or `axiom`: all ten lemmas/theorems close.
   *(check; read of the whole copied file.)*
3. The glue is 14 lines (223-236) using exactly 3 direct project lemmas, and the
   longest chain of project lemmas below the theorem has depth 6:
   `answer_correctness → g_const → no_mixed → d_nonneg → orbit → key_ff → ineqA`.
   *(measurement; counted on the copied file.)*
4. The code documents the answer as the complete solution family: the `AnswerType`
   doc says "The answer is a *set* of functions (the complete solution family)."
   (line 4), and `def answer` is wrapped in a `BEGIN ANSWER` / `END ANSWER` block
   (lines 19-21). *(author-statement; permalinks below.)*

## When to use it, and when not

Use the iff-split when the goal is a characterisation `P f ↔ f ∈ answer` where
`answer` is a closed family of the form `∃ c, side_condition c ∧ ∀ x, f x = g x c`:
the backward direction ("every member of the family works") is a verification
lemma independent of the uniqueness argument, and the forward direction reduces
to choosing the parameter from a single evaluation (here `f 1 - 1`) plus a
constancy lemma. Avoid it when the two directions share a deep argument (the
split duplicates it), when the family is not given in closed form (then the
forward direction has no single witness to exhibit), or when the parameter is not
determined by one evaluation (then the forward direction needs an extra
uniqueness lemma).

## Consequences

The split creates exactly two goals, one per direction of the iff. The forward
direction additionally creates a witness obligation: `refine ⟨f 1 - 1, ?_, ?_⟩`
must prove `0 ≤ f 1 - 1` (discharged by `d_nonneg`) and `f x = x + (f 1 - 1)`
(discharged by `g_const`). If `g_const` were missing or too weak, the forward
direction would not close; if `answer` were not defined as a plain `∃` family,
the backward `rintro ⟨c, hc, hfc⟩` would not be a one-liner. The two directions
are otherwise independent, so this is exactly the skeleton AutoDecompose would
produce: three lemma holes with the glue only choosing the witness.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/pramaana-labs/imo2026-lean at commit `788fddc53c463d5d40d4680fb9bfd7b0f96f1063`, under `MIT`; see the [source note](../../sources/pramaana-imo2026/SOURCE.md) for the licence text and attribution.
