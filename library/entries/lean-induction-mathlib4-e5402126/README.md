# Diagonal induction on (p, q) for the ballot problem

| | |
|---|---|
| Kind | instance |
| Move | induction |
| Language | lean |
| Status | verified |
| Source | [mathlib4](../../sources/mathlib4/SOURCE.md) at `e1545ebed975` |
| Licence | `Apache-2.0` |

## Intent

Reduce the ballot problem — the probability that candidate A (p votes) is
strictly ahead of B (q votes, q < p) throughout the count equals
(p − q)/(p + q) — to a diagonal induction on the pair (q, p) with two base
cases and one two-induction-hypothesis step, then discharge each case with a
named lemma written for it.

## The decomposition

### parent `ballot_problem'`: [`Archive/Wiedijk100Theorems/BallotProblem.lean` lines 309-344](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/BallotProblem.lean#L309-L344) ([local copy](code/Archive/Wiedijk100Theorems/BallotProblem.lean))

```lean
theorem ballot_problem' :
    ∀ q p, q < p → (uniformOn (countedSequence p q) staysPositive).toReal = (p - q) / (p + q) := by
  apply Nat.diag_induction
  · intro p
    rw [ballot_same]
    simp
  · intro p
    rw [ballot_edge]
    simp only [ENNReal.toReal_one, Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero, add_zero]
    rw [div_self]
    exact Nat.cast_add_one_ne_zero p
  · intro q p qp h₁ h₂
    have := isProbabilityMeasure_uniformOn
      (countedSequence_finite p (q + 1)) (countedSequence_nonempty _ _)
    have := isProbabilityMeasure_uniformOn
      (countedSequence_finite (p + 1) q) (countedSequence_nonempty _ _)
    have h₃ : 0 < p + 1 + (q + 1) := Nat.add_pos_left (Nat.succ_pos _) _
    rw [← uniformOn_add_compl_eq {l : List ℤ | l.headI = 1} _ (countedSequence_finite _ _),
      first_vote_pos _ _ h₃, first_vote_neg _ _ h₃, ballot_pos, ballot_neg _ _ qp]
    rw [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_mul, ← Nat.cast_add,
      ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast, h₁, h₂]
    · have h₄ : (p + 1 : ℝ) + (q + 1 : ℝ) ≠ (0 : ℝ) := by
        apply ne_of_gt
        assumption_mod_cast
      have h₅ : (p + 1 : ℝ) + ↑q ≠ (0 : ℝ) := by
        apply ne_of_gt
        norm_cast
        linarith
      have h₆ : ↑p + (q + 1 : ℝ) ≠ (0 : ℝ) := by
        apply ne_of_gt
        norm_cast
        linarith
      simp [field, h₄, h₅, h₆] at *
      ring
    all_goals exact ENNReal.mul_ne_top (by finiteness) (by simp [Ne, ENNReal.div_eq_top])
```

### child `ballot_same`: [`Archive/Wiedijk100Theorems/BallotProblem.lean` lines 239-246](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/BallotProblem.lean#L239-L246) ([local copy](code/Archive/Wiedijk100Theorems/BallotProblem.lean))

```lean
theorem ballot_same (p : ℕ) : uniformOn (countedSequence (p + 1) (p + 1)) staysPositive = 0 := by
  rw [uniformOn_eq_zero_iff (countedSequence_finite _ _), eq_empty_iff_forall_notMem]
  rintro x ⟨hx, t⟩
  apply ne_of_gt (t x _ x.suffix_refl)
  · simpa using sum_of_mem_countedSequence hx
  · refine List.ne_nil_of_length_pos ?_
    rw [length_of_mem_countedSequence hx]
    exact Nat.add_pos_left (Nat.succ_pos _) _
```

### child `ballot_edge`: [`Archive/Wiedijk100Theorems/BallotProblem.lean` lines 248-253](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/BallotProblem.lean#L248-L253) ([local copy](code/Archive/Wiedijk100Theorems/BallotProblem.lean))

```lean
theorem ballot_edge (p : ℕ) : uniformOn (countedSequence (p + 1) 0) staysPositive = 1 := by
  rw [counted_right_zero]
  refine uniformOn_eq_one_of (finite_singleton _) (singleton_nonempty _) ?_
  refine singleton_subset_iff.2 fun l hl₁ hl₂ => List.sum_pos _ (fun x hx => ?_) hl₁
  rw [List.eq_of_mem_replicate (hl₂.mem hx)]
  norm_num
```

### child `ballot_pos`: [`Archive/Wiedijk100Theorems/BallotProblem.lean` lines 266-279](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/BallotProblem.lean#L266-L279) ([local copy](code/Archive/Wiedijk100Theorems/BallotProblem.lean))

```lean
theorem ballot_pos (p q : ℕ) :
    uniformOn (countedSequence (p + 1) (q + 1) ∩ {l | l.headI = 1}) staysPositive =
      uniformOn (countedSequence p (q + 1)) staysPositive := by
  rw [countedSequence_int_pos_counted_succ_succ, uniformOn, uniformOn,
    cond_apply list_int_measurableSet, cond_apply list_int_measurableSet,
    count_injective_image List.cons_injective]
  congr 1
  have : (1 :: ·) '' countedSequence p (q + 1) ∩ staysPositive =
      (1 :: ·) '' (countedSequence p (q + 1) ∩ staysPositive) := by
    simp only [image_inter List.cons_injective, Set.ext_iff, mem_inter_iff, and_congr_right_iff,
      forall_mem_image, List.cons_injective.mem_set_image, staysPositive_cons_pos _ one_pos]
    exact fun _ _ ↦ trivial
  rw [this, count_injective_image]
  exact List.cons_injective
```

### child `ballot_neg`: [`Archive/Wiedijk100Theorems/BallotProblem.lean` lines 293-307](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/BallotProblem.lean#L293-L307) ([local copy](code/Archive/Wiedijk100Theorems/BallotProblem.lean))

```lean
theorem ballot_neg (p q : ℕ) (qp : q < p) :
    uniformOn (countedSequence (p + 1) (q + 1) ∩ {l | l.headI = 1}ᶜ) staysPositive =
      uniformOn (countedSequence (p + 1) q) staysPositive := by
  rw [countedSequence_int_neg_counted_succ_succ, uniformOn, uniformOn,
    cond_apply list_int_measurableSet, cond_apply list_int_measurableSet,
    count_injective_image List.cons_injective]
  congr 1
  have : List.cons (-1) '' countedSequence (p + 1) q ∩ staysPositive =
      List.cons (-1) '' (countedSequence (p + 1) q ∩ staysPositive) := by
    simp only [image_inter List.cons_injective, Set.ext_iff, mem_inter_iff, and_congr_right_iff,
      forall_mem_image, List.cons_injective.mem_set_image, staysPositive_cons, and_iff_left_iff_imp]
    intro l hl _
    simp [sum_of_mem_countedSequence hl, lt_sub_iff_add_lt', qp]
  rw [this, count_injective_image]
  exact List.cons_injective
```

### child `first_vote_pos`: [`Archive/Wiedijk100Theorems/BallotProblem.lean` lines 188-223](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/BallotProblem.lean#L188-L223) ([local copy](code/Archive/Wiedijk100Theorems/BallotProblem.lean))

```lean
theorem first_vote_pos :
    ∀ p q,
      0 < p + q → uniformOn (countedSequence p q : Set (List ℤ)) {l | l.headI = 1} = p / (p + q)
  | p + 1, 0, _ => by
    rw [counted_right_zero, uniformOn_singleton]
    simp [ENNReal.div_self _ _, List.replicate_succ]
  | 0, q + 1, _ => by
    rw [counted_left_zero, uniformOn_singleton]
    simp [List.replicate]
  | p + 1, q + 1, _ => by
    simp_rw [counted_succ_succ]
    rw [← uniformOn_disjoint_union ((countedSequence_finite _ _).image _)
        ((countedSequence_finite _ _).image _) (disjoint_bits _ _),
      ← counted_succ_succ,
      uniformOn_eq_one_of ((countedSequence_finite p (q + 1)).image _)
        ((countedSequence_nonempty _ _).image _)]
    · have : List.cons (-1) '' countedSequence (p + 1) q ∩ {l : List ℤ | l.headI = 1} = ∅ := by
        ext
        simp only [mem_inter_iff, mem_image, mem_ofPred_eq, mem_empty_iff_false, iff_false,
          not_and, forall_exists_index, and_imp]
        rintro l _ rfl
        norm_num
      have hint :
        countedSequence (p + 1) (q + 1) ∩ List.cons 1 '' countedSequence p (q + 1) =
          List.cons 1 '' countedSequence p (q + 1) := by
        rw [inter_eq_right, counted_succ_succ]
        exact subset_union_left
      rw [(uniformOn_eq_zero_iff <| (countedSequence_finite _ _).image _).2 this, uniformOn,
        cond_apply list_int_measurableSet, hint, count_injective_image List.cons_injective,
        count_countedSequence, count_countedSequence, one_mul, zero_mul, add_zero,
        Nat.cast_add, Nat.cast_one, mul_comm, ← div_eq_mul_inv, ENNReal.div_eq_div_iff]
      · norm_cast
        rw [mul_comm _ (p + 1), add_right_comm, Nat.add_one_mul_choose_eq,
          mul_comm]
      all_goals simp [(Nat.choose_pos <| le_add_of_nonneg_right zero_le).ne']
    · simp
```

### child `first_vote_neg`: [`Archive/Wiedijk100Theorems/BallotProblem.lean` lines 229-237](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/BallotProblem.lean#L229-L237) ([local copy](code/Archive/Wiedijk100Theorems/BallotProblem.lean))

```lean
theorem first_vote_neg (p q : ℕ) (h : 0 < p + q) :
    uniformOn (countedSequence p q) {l | l.headI = 1}ᶜ = q / (p + q) := by
  have h' : (p + q : ℝ≥0∞) ≠ 0 := mod_cast h.ne'
  have := uniformOn_compl
    {l : List ℤ | l.headI = 1}ᶜ (countedSequence_finite p q) (countedSequence_nonempty p q)
  rw [compl_compl, first_vote_pos _ _ h] at this
  rw [ENNReal.eq_sub_of_add_eq _ this, ENNReal.eq_div_iff, ENNReal.mul_sub, mul_one,
    ENNReal.mul_div_cancel, ENNReal.add_sub_cancel_left]
  all_goals simp_all [ENNReal.div_eq_top]
```

How the parts fit. `ballot_problem'` is proved by `apply Nat.diag_induction`
(line 311), a double induction principle whose three obligations become the
three bullets of the proof:

- **diagonal base** `motive (p + 1) (p + 1)` (lines 312-314): the tie case
  q = p, where A is never strictly ahead, so the answer is 0. Closed by
  `ballot_same`, which proves `uniformOn (countedSequence (p+1) (p+1))
  staysPositive = 0` by showing the set is empty (a sequence with as many +1s
  as −1s has sum 0, so no suffix sum is positive).
- **edge base** `motive 0 (p + 1)` (lines 315-319): the unanimous case q = 0,
  where A is always ahead, so the answer is 1. Closed by `ballot_edge`.
- **step** `motive (q+1) (p+1)` from `motive (q+1) p` and `motive q (p+1)`
  under `q < p` (lines 320-344): split the count on the first vote. The first
  vote is A with probability `(p+1)/((p+1)+(q+1))` (`first_vote_pos`) or B
  with probability `(q+1)/((p+1)+(q+1))` (`first_vote_neg`). Conditioning on
  the first vote, `ballot_pos` turns the A-branch
  `countedSequence (p+1) (q+1) ∩ {l | l.headI = 1}` into
  `countedSequence p (q+1)` and `ballot_neg` turns the B-branch into
  `countedSequence (p+1) q`; the two induction hypotheses `h₁, h₂` rewrite
  those two to their closed forms, and the residual non-zero denominators
  (`h₄, h₅, h₆`) are discharged by positivity, then `simp [field, …]` + `ring`
  finish the arithmetic.

The lemma graph, read top-down:

```
ballot_problem'
├─ ballot_same        diagonal base q = p (answer 0)
├─ ballot_edge        edge base q = 0 (answer 1)
└─ step, on the first vote:
   ├─ first_vote_pos  P(first vote = A) = (p+1)/((p+1)+(q+1))
   ├─ first_vote_neg  P(first vote = B) = (q+1)/((p+1)+(q+1))   (uses first_vote_pos)
   ├─ ballot_pos      A-branch ≅ countedSequence p (q+1)        (uses countedSequence_int_pos_counted_succ_succ → counted_succ_succ)
   └─ ballot_neg      B-branch ≅ countedSequence (p+1) q        (uses countedSequence_int_neg_counted_succ_succ → counted_succ_succ)
```

Each leaf is a self-contained statement whose proof closes on its own or from
named siblings in the same file:

- `ballot_same` and `ballot_edge` close by the emptiness / singleness of the
  relevant `countedSequence`, using `sum_of_mem_countedSequence` and
  `length_of_mem_countedSequence`.
- `ballot_pos` closes by an image/count rewrite
  (`countedSequence_int_pos_counted_succ_succ`, `count_injective_image`) plus
  `staysPositive_cons_pos` (prepending `+1` preserves `staysPositive`); it
  needs no `q < p` hypothesis.
- `ballot_neg` is the mirror: it needs `qp : q < p` (prepending `−1` only
  preserves positivity when the remaining count is still strictly positive),
  via `staysPositive_cons` and `sum_of_mem_countedSequence`.
- `first_vote_pos` is the real counting computation, closed by a small
  recursion on `p, q` using `counted_succ_succ`, `uniformOn_disjoint_union`
  and `count_countedSequence`.
- `first_vote_neg` closes by complementing: `uniformOn_compl` reduces the B
  probability to `1 − first_vote_pos`.

The headline theorem `ballot_problem` (lines 347-364 of the same file) is a
thin wrapper that lifts this `.toReal` equality to an `ℝ≥0∞` equality, so the
diagonal induction is the whole content of the move.

## Why it is good

1. (check) The parent `ballot_problem'` closes from its six children: the two
   base cases close by `ballot_same` and `ballot_edge` alone, and the step
   closes by `first_vote_pos`, `first_vote_neg`, `ballot_pos`, `ballot_neg`
   followed by `ring` (lines 309-344).
2. (check) The induction principle the proof relies on, `Nat.diag_induction`,
   has exactly the two-base-cases-plus-step shape the proof instantiates:
   premises `diag` (`∀ a, motive (a+1) (a+1)`) and `zero_succ`
   (`∀ b, motive 0 (b+1)`) and step `ind` (`∀ a b, a < b → motive (a+1) b →
   motive a (b+1) → motive (a+1) (b+1)`)
   ([`Mathlib/Data/Nat/Init.lean` lines 358-366](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Mathlib/Data/Nat/Init.lean#L358-L366)).
3. (measurement) The glue is 36 lines (309-344) assembling 6 direct lemmas,
   and the longest chain of file-local lemmas below the main theorem has depth
   4: `ballot_problem' → first_vote_neg → first_vote_pos →
   count_countedSequence → counted_succ_succ` (edges at lines 234, 154/217 and
   182 of `BallotProblem.lean`).
4. (author-statement) The mathlib authors document the principle in the
   docstring: "Given a predicate on two naturals `motive : ℕ → ℕ → Prop`,
   `motive a b` is true for all `a < b` if `motive (a + 1) (a + 1)` is true
   for all `a`, `motive 0 (b + 1)` is true for all `b` and for all `a < b`,
   `motive (a + 1) b` is true and `motive a (b + 1)` is true implies
   `motive (a + 1) (b + 1)` is true" ([`Mathlib/Data/Nat/Init.lean` lines
   358-361](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Mathlib/Data/Nat/Init.lean#L358-L361)).

## When to use it, and when not

Use diagonal (double) induction when the goal is `∀ a b, a < b → P a b` for a
recurrence on a pair that steps down both coordinates together — here the
ballot count, whose step `(p+1, q+1) ↦ (p, q+1) or (p+1, q)` mirrors the
binomial-coefficient / Pascal-triangle recurrence. It pays off when both base
cases (the diagonal `a = b` and the edge `a = 0`) are easy, and the step
factorises into one independent lemma per first-move choice. Avoid it when the
pair has no natural diagonal/edge closure, when only one of the two induction
hypotheses is actually needed (then ordinary single-coordinate induction is
simpler), or when the strict ordering `q < p` is not the ordering the
recurrence respects.

## Consequences

The move creates three obligations: a diagonal base, an edge base, and a step
carrying two induction hypotheses. Both bases must close with no induction
hypothesis, and the step must produce the two smaller pairs `(a+1, b)` and
`(a, b+1)` from `(a+1, b+1)` — here the "condition on the first vote" split.
Side conditions accumulate in the step: the finiteness / non-emptiness of the
count spaces (`countedSequence_finite`, `countedSequence_nonempty`), positivity
of the vote count (`h₃`), non-zero denominators (`h₄, h₅, h₆`) and `≠ ∞`
conditions for the `ENNReal.toReal_*` rewrites; one missing side condition
breaks the final `ring`. The asymmetry that `ballot_neg` needs `q < p` while
`ballot_pos` does not is a real obligation to keep track of.

## Verification

<!-- verification:start -->
Status: **verified**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml triggers on push to master (default branch) and calls build_template.yml; build_template.yml line 252 runs 'lake-build-with-retry.sh Archive Counterexamples Wanted' and line 297 gates on 'lake build --no-build --wfail Archive'. Archive.lean line 79 'public import Archive.Wiedijk100Theorems.BallotProblem' puts this file in the Archive target, so CI builds it. Pinned commit e1545ebed97594477bbd88b2fe948ffce56e5af2 is the default-branch HEAD (source.json ref=HEAD, pinned via git ls-remote HEAD). | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 2 file(s) byte-identical at e1545ebed97594477bbd88b2fe948ffce56e5af2 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Opened copied code/Archive/Wiedijk100Theorems/BallotProblem.lean lines 309-344: line 311 'apply Nat.diag_induction'; diagonal base lines 312-314 'rw [ballot_same]; simp'; edge base lines 315-319 'rw [ballot_edge]; simp only [...]; rw [div_self]; exact Nat.cast_add_one_ne_zero p'; step lines 320-344, line 327 cites 'first_vote_pos, first_vote_neg, ballot_pos, ballot_neg' then lines 342-343 'simp [field, h4, h5, h6] at *; ring'. All six named children (ballot_same, ballot_edge, first_vote_pos, first_vote_neg, ballot_pos, ballot_neg) are cited and match the entry's children list. | verifier |
| 2 | verified | Opened copied code/Mathlib/Data/Nat/Init.lean lines 358-366: 'theorem diag_induction (motive : Nat -> Nat -> Prop) (diag : forall a, motive (a + 1) (a + 1)) (zero_succ : forall b, motive 0 (b + 1)) (ind : forall a b, a < b -> motive (a + 1) b -> motive a (b + 1) -> motive (a + 1) (b + 1)) : forall a b, a < b -> motive a b'. Premises diag, zero_succ, ind match the claim exactly (two base cases plus one two-IH step). | verifier |
| 3 | verified | Opened copied BallotProblem.lean: parent block 309-344 is 36 lines (344-309+1). Six direct lemmas cited by the parent's rw at lines 313 (ballot_same), 316 (ballot_edge), 327 (first_vote_pos, first_vote_neg, ballot_pos, ballot_neg). Chain edges verified: ballot_problem' uses first_vote_neg/first_vote_pos at line 327; first_vote_neg uses first_vote_pos at line 234 'rw [compl_compl, first_vote_pos _ _ h] at this'; first_vote_pos uses count_countedSequence at line 217 'count_countedSequence, count_countedSequence'; count_countedSequence uses counted_succ_succ at line 182 'rw [counted_succ_succ, ...]'. So the 4-edge chain ballot_problem' -> first_vote_neg -> first_vote_pos -> count_countedSequence -> counted_succ_succ is real. Note: the claim's evidence locator 'lines 154/217' is slightly off -- line 154 shows first_vote_pos using counted_succ_succ, not count_countedSequence; the correct locator is line 217, which does not change the measured depth. | verifier |
| 4 | verified | Opened copied Mathlib/Data/Nat/Init.lean lines 358-361: the docstring states "Given a predicate on two naturals motive : Nat -> Nat -> Prop, motive a b is true for all a < b if motive (a + 1) (a + 1) is true for all a, motive 0 (b + 1) is true for all b and for all a < b, motive (a + 1) b is true and motive a (b + 1) is true implies motive (a + 1) (b + 1) is true." This matches the claim quoted text verbatim. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | object | Parent and children are verbatim-correct against the copied code: ballot_problem' (309-310) matches; all six children (ballot_same 239, ballot_edge 248, ballot_pos 266, ballot_neg 293, first_vote_pos 188, first_vote_neg 229) match their statements and closed_by; the parent closes via apply Nat.diag_induction, bases by ballot_same/ballot_edge (312-319), step by first_vote_pos/first_vote_neg/ballot_pos/ballot_neg then ring (320-344); diag_induction premise shape (Init.lean 363-366) matches claim 2, docstring 358-361 matches claim 4; glue_lines=36 and child_lines=[8,6,14,15,36,9] match line ranges. OBJECTION (correctness, shape numbers): shape.depth=4 (and metrics.depth, claim 3) is wrong. The longest chain of file-local lemmas below ballot_problem' is ballot_problem' -> first_vote_neg (234) -> first_vote_pos (217) -> count_countedSequence (182) -> counted_succ_succ (115, uses counted_ne_nil_left) -> counted_ne_nil_left (103, uses counted_eq_nil_iff) -> counted_eq_nil_iff (100, uses length_of_mem_countedSequence) -> length_of_mem_countedSequence (96, uses mem_countedSequence_iff_perm) -> mem_countedSequence_iff_perm (78), i.e. depth 8, not 4. Fix: recompute depth=8 and correct shape.depth, metrics.depth and claim 3 (or restate claim 3 as the chain actually checked). Secondary: direct_lemmas=6 omits countedSequence_finite and countedSequence_nonempty, which ballot_problem' also cites directly (322-323, 326); either include them (direct_lemmas=8) or state the scoping in how_counted. | reviewer-correctness |
| generality | accept | Move is stated beyond the example: applicability.use_when abstracts to a recurrence on a pair (a,b) stepping both coordinates from (a+1,b+1) with diagonal (a=b) and edge (a=0) bases, and the README names Nat.diag_induction (two bases + one two-IH step) and maps the recurrence to Pascal/binomial. 'when not to use' gives three concrete conditions (no diagonal/edge closure; only one IH needed -> single-coordinate induction; ordering mismatch) and consequences are honest and specific (three obligations, accumulating side conditions h3-h6/ne-inf, and the ballot_neg-needs-q<p vs ballot_pos-doesn't asymmetry). Good-leaf criterion is conveyed descriptively: each leaf is a self-contained statement closing on its own or from named siblings, hypothesis-minimal (ballot_pos takes no q<p), with short bounded closures (image/count rewrites, complementing) - verified against the copied code in the README. Minor gap: 'bounded prover' is never named and the leaf criterion is descriptive rather than a prescriptive rule, but this does not break the lens. | reviewer-generality |
| provenance-licence | accept | Provenance pass: check_provenance.py reports 2 file(s) byte-identical at e1545ebed97594477bbd88b2fe948ffce56e5af2. SHA-256 in entry.json files[] match the copied files exactly (BallotProblem.lean a90aa888…, Init.lean 2537d5b0…). Commit is recorded consistently across entry.json source.commit, README, sources/mathlib4/SOURCE.md and source.json (e1545ebed97594477bbd88b2fe948ffce56e5af2, pinned via HEAD). Licence Apache-2.0 recorded in entry.json, README and source.json; upstream-LICENSE is genuine Apache-2.0 text. All permalinks (entry.json files[] and sites[], README links) use the same commit hash and correct repo/file paths; spot-checked line anchors match the copied files (parent 309-344, ballot_same 239-246, diag_induction 358-366). Everything traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover-community/mathlib4 at commit `e1545ebed97594477bbd88b2fe948ffce56e5af2`, under `Apache-2.0`; see the [source note](../../sources/mathlib4/SOURCE.md) for the licence text and attribution.
