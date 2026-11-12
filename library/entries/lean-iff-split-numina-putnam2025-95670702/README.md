# Optimal-constant iff-split for Putnam 2025 A2

| | |
|---|---|
| Kind | instance |
| Move | iff-split |
| Language | lean |
| Status | accepted |
| Source | [numina-putnam2025](../../sources/numina-putnam2025/SOURCE.md) at `60d33c8ba19a` |
| Licence | `MIT` |

## Intent

Putnam 2025 A2 asks for the two optimal constants sandwiching `sin x` between
quadratic bounds on `[0, π]`. The answer is the pair `1/π` (greatest lower
bound) and `4/π²` (least upper bound). The main theorem is stated directly as
that pair, and its proof splits the conjunction, then each optimal-constant
half into two further halves — membership (the inequality holds) and
optimality (every competing constant is worse) — closing each of the four
halves with one named lemma proved earlier in the file.

## The decomposition

### parent `putnam_2025_a2`: [`NuminaPutnam2025/putnam_2025_a2.lean` lines 511-522](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a2.lean#L511-L522) ([local copy](code/NuminaPutnam2025/putnam_2025_a2.lean))

```lean
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
```

### child `sin_ge_inv_pi_mul_quad`: [`NuminaPutnam2025/putnam_2025_a2.lean` lines 20-20](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a2.lean#L20-L20) ([local copy](code/NuminaPutnam2025/putnam_2025_a2.lean))

```lean
lemma sin_ge_inv_pi_mul_quad : ∀ x ∈ Icc (0:ℝ) π, (1 / π) * x * (π - x) ≤ sin x := by
```

### child `inv_pi_is_greatest_lower_bound`: [`NuminaPutnam2025/putnam_2025_a2.lean` lines 195-196](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a2.lean#L195-L196) ([local copy](code/NuminaPutnam2025/putnam_2025_a2.lean))

```lean
lemma inv_pi_is_greatest_lower_bound (a : ℝ) (h : ∀ x ∈ Icc (0:ℝ) π, a * x * (π - x) ≤ sin x) :
    a ≤ 1 / π := by
```

### child `sin_le_four_div_pi_sq_mul_quad`: [`NuminaPutnam2025/putnam_2025_a2.lean` lines 253-253](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a2.lean#L253-L253) ([local copy](code/NuminaPutnam2025/putnam_2025_a2.lean))

```lean
lemma sin_le_four_div_pi_sq_mul_quad : ∀ x ∈ Icc (0:ℝ) π, sin x ≤ (4 / π ^ 2) * x * (π - x) := by
```

### child `four_div_pi_sq_is_least_upper_bound`: [`NuminaPutnam2025/putnam_2025_a2.lean` lines 488-489](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a2.lean#L488-L489) ([local copy](code/NuminaPutnam2025/putnam_2025_a2.lean))

```lean
lemma four_div_pi_sq_is_least_upper_bound (b : ℝ) (h : ∀ x ∈ Icc (0:ℝ) π, b * x * (π - x) ≥ sin x) :
    4 / π ^ 2 ≤ b := by
```

How the parts fit. `IsGreatest s c` unfolds to `c ∈ s ∧ ∀ y ∈ s, y ≤ c`, and
`IsLeast s c` to `c ∈ s ∧ ∀ y ∈ s, c ≤ y`. So the parent's first `constructor`
(line 514) splits the top-level `∧` into the lower and upper halves; the second
`constructor` (line 515) splits the lower half into membership and optimality,
and the third (line 519) does the same for the upper half. Four leaves result,
one per named lemma:

```text
putnam_2025_a2 : IsGreatest {a | ∀ x, a·x·(π−x) ≤ sin x} (1/π) ∧ IsLeast {b | ∀ x, b·x·(π−x) ≥ sin x} (4/π²)
├─ lower half (constructor, line 515)
│   ├─ sin_ge_inv_pi_mul_quad           (1/π is a lower bound: (1/π)·x·(π−x) ≤ sin x)
│   │   └─ sin_one_lower                (sin 1 > 0.78; used inside at lines 127, 188)
│   └─ inv_pi_is_greatest_lower_bound   (every lower-bound constant a ≤ 1/π)
└─ upper half (constructor, line 519)
    ├─ sin_le_four_div_pi_sq_mul_quad    (4/π² is an upper bound: sin x ≤ (4/π²)·x·(π−x))
    └─ four_div_pi_sq_is_least_upper_bound (every upper-bound constant b ≥ 4/π²)
```

Each leaf is a good leaf because its statement is self-contained and its proof
closes on its own, from Mathlib facts plus at most one named sibling:

- `sin_ge_inv_pi_mul_quad` (proof lines 21-192) is a case tree: `x = 0` and
  `x = π` close by `simp`; for `x ≤ π/2` it splits further on `x ≥ π - 2`
  (Jordan's inequality `mul_le_sin`), then on `x ≤ 1` (the Taylor bound
  `sin_bound`); the strip `1 < x < π - 2` uses the sibling `sin_one_lower`; the
  `x > π/2` half is folded onto the first by symmetry `sin x = sin (π - x)`
  (`sin_pi_sub`). Every leaf closes by `nlinarith`/`linarith`.
- `inv_pi_is_greatest_lower_bound` (proof lines 197-250) closes by
  contradiction: assume `a > 1/π`, set
  `x := min (min ((a - 1/π) / (2 * a)) (1/2)) (π/2)`, apply the hypothesis `h`
  there, and contradict `sin x ≤ x` (`sin_le`) with `nlinarith`. It uses no
  other project lemma.
- `sin_le_four_div_pi_sq_mul_quad` (proof lines 254-485) mirrors the lower-bound
  tree with a finer split near `π/2` (`x ≤ 0.6`, `x ≤ π - π^2/4`, and a Taylor
  expansion of `cos` around `0` in the last strip), closing each leaf by
  `nlinarith`/`linarith` from `sin_le` and `cos_bound`.
- `four_div_pi_sq_is_least_upper_bound` (proof lines 490-509) closes from the
  single probe `x = π/2`: `sin (π/2) = 1` turns the hypothesis into
  `b * (π/2) * (π/2) ≥ 1`, i.e. `b * (π²/4) ≥ 1`, and `nlinarith [hpi2]` gives
  `4 / π² ≤ b`.

So the skeleton is four lemma holes — two inequalities and two optimality
arguments — and the glue is nothing but `constructor` splits followed by
`exact`/`intro; exact` of the named lemmas. The only project-lemma dependency
below the direct children is `sin_ge_inv_pi_mul_quad` → `sin_one_lower` (depth
2).

## Why it is good

1. Three `constructor` applications (lines 514, 515, 519) split the conjunction
   into four leaves, each closed by exactly one named lemma, in 9 lines
   (514-522) — a `check` against the permalink.
2. The glue is 9 lines against 478 lines of child proofs (172 + 54 + 232 + 20)
   in a 524-line file, so the theorem-level argument is stated in the glue
   alone — a `measurement` of the `shape` field.
3. The file has no `sorry`, `admit`, `Admitted` or `axiom`; the only match for
   "axiom" is the diagnostic `#print axioms` on line 524 — a `check` by grep.
4. The same two-half split (inequality, then optimality) is applied twice inside
   the parent, once per constant (lines 515-518 and 519-522), so the move is
   reused within the single theorem — a `known-use`.

In my opinion the detail worth copying is the *statement shape*: each
optimal-constant half is itself a conjunction of "the constant works" and "every
other constant is worse", and each conjunct is a separate named lemma, so the
theorem's proof is a pure `constructor`/`exact` skeleton with no arithmetic in
the glue.

## When to use it, and when not

Use it when a goal is an optimal-constant claim `IsGreatest S c ∧ IsLeast T d`
(or a single `IsGreatest`/`IsLeast`), and the two halves of each constant — the
inequality and the comparison against every competing constant — are already
proved as named lemmas. Then the main theorem is assembled by `constructor` and
`exact` with no further reasoning. Avoid it when the membership and optimality
arguments are entangled or need a shared case analysis that cannot be split into
independent lemmas, when only one direction holds, or when either half is not
yet isolated as a self-contained lemma (then the glue would have to contain the
arithmetic, and the split buys nothing).

## Consequences

The move creates exactly four obligations — the four conjuncts — and no
exhaustiveness obligation, because `constructor` on `∧` and on
`IsGreatest`/`IsLeast` produces precisely the two halves of each conjunction. It
relies on the four lemmas being already proved and in scope; a missing lemma
leaves a `sorry`-able hole whose statement is exactly the leaf. Failure mode:
the membership and optimality halves are both inequalities about the same
expression `a * x * (π - x)`, so the wrong lemma can be supplied to the wrong
half; the split shape is still right, but `exact` fails on the constant's type
(`1/π` versus `4/π²`).

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/lean_action_ci.yml uses leanprover/lean-action@v1 which builds the default target NuminaPutnam2025; that lean_lib builds NuminaPutnam2025/putnam_2025_a2.lean via the root NuminaPutnam2025.lean import; pinned commit 60d33c8ba19af905bd731e938ebde1c5b8c76519 is HEAD of default branch main | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 60d33c8ba19af905bd731e938ebde1c5b8c76519 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read copied file putnam_2025_a2.lean: constructor at lines 514, 515, 519; leaves closed by sin_ge_inv_pi_mul_quad (516), inv_pi_is_greatest_lower_bound (518), sin_le_four_div_pi_sq_mul_quad (520), four_div_pi_sq_is_least_upper_bound (522); 9 glue lines 514-522 | verifier |
| 2 | verified | Copied file: glue lines 514-522 (9); child bodies 21-192=172, 197-250=54, 254-485=232, 490-509=20, sum 478; wc -l = 524 lines | verifier |
| 3 | verified | grep -nE 'sorry|admit|Admitted|axiom' on copied file returns only line 524 '#print axioms putnam_2025_a2', a diagnostic; no sorry/admit/Admitted/axiom declarations | verifier |
| 4 | verified | Copied file lines 515-518 (lower constant 1/pi: constructor then exact sin_ge_inv_pi_mul_quad, intro a ha; exact inv_pi_is_greatest_lower_bound a ha) and 519-522 (upper constant 4/pi^2: constructor then exact sin_le_four_div_pi_sq_mul_quad, intro b hb; exact four_div_pi_sq_is_least_upper_bound b hb) — same two-half split applied twice | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Read local copy code/NuminaPutnam2025/putnam_2025_a2.lean in full. Parent (511-513) and proof (514-522) match entry; three constructors (514,515,519) split the conjunction into four leaves closed by exactly the four named lemmas: sin_ge_inv_pi_mul_quad (516), inv_pi_is_greatest_lower_bound (518), sin_le_four_div_pi_sq_mul_quad (520), four_div_pi_sq_is_least_upper_bound (522). Child statements at lines 20, 195-196, 253, 488-489 match entry.json children verbatim; closed_by descriptions match the code (case trees via mul_le_sin/sin_bound/sin_one_lower/sin_pi_sub; by_contra+set min probe; sin_le/cos_bound/sin_pi_div_two; probe x=pi/2 + nlinarith [hpi2]). IsGreatest/IsLeast unfold to membership+optimality, so constructor produces the four leaves the entry claims. Shape numbers correct: direct_lemmas=4, depth=2 (putnam_2025_a2 -> sin_ge_inv_pi_mul_quad -> sin_one_lower, used at lines 127 and 188), glue_lines=9 (514-522), child_lines=[172,54,232,20] = bodies 21-192, 197-250, 254-485, 490-509. grep shows no sorry/admit/Admitted/axiom except the diagnostic #print axioms at line 524, so it closes. | reviewer-correctness |
| generality | accept | Move is abstracted beyond the example: applicability.goal_shape generalises to any optimal-constant claim IsGreatest S c ∧ IsLeast T d (or a single IsGreatest/IsLeast), and the README's 'When to use it'/'avoid_when' give a reusable trigger (halves already isolated as named lemmas) and honest exclusions (entangled halves, shared case analysis, one-sided, or unisolated halves). Consequences are specific and match the code: exactly four constructor obligations, no exhaustiveness obligation, reliance on pre-proved lemmas, and the concrete failure mode (wrong lemma to wrong half -> exact fails on 1/π vs 4/π²). Leaf quality for a bounded prover is answered: each leaf is self-contained and closes on its own from Mathlib facts plus at most one named sibling (sin_one_lower), with per-leaf closing methods spelled out. Verified against the copied file at the pinned commit. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note all consistent and traceable. check_provenance.py passes: copied file putnam_2025_a2.lean byte-identical at pinned commit 60d33c8ba19af905bd731e938ebde1c5b8c76519; entry.json files.sha256 (15bc6302...) matches local file, bytes 25823 and 524 lines match. Commit is identical across entry.json, source.json, SOURCE.md and every permalink (blob URL + #L ranges); site line ranges (parent 511-522; children 20, 195-196, 253, 488-489) match the local copy. Licence MIT is consistent across entry.json, source.json, SOURCE.md and the repo LICENSE fetched at the pinned commit (byte-identical to sources/numina-putnam2025/upstream-LICENSE, standard MIT text, 'Copyright (c) 2025 Numina'). SOURCE.md records repo URL, pinned commit (pinned_at 2026-11-12T10:24:03Z), browse URL, licence and links the LICENSE file. Nothing to fix. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/project-numina/Numina-Putnam2025 at commit `60d33c8ba19af905bd731e938ebde1c5b8c76519`, under `MIT`; see the [source note](../../sources/numina-putnam2025/SOURCE.md) for the licence text and attribution.
