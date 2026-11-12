# Descending induction on a strengthened invariant for UK BMO 2024 R1 P2

| | |
|---|---|
| Kind | instance |
| Move | induction |
| Language | lean |
| Status | accepted |
| Source | [compfiles](../../sources/compfiles/SOURCE.md) at `1745e6ced3e6` |
| Licence | `Apache-2.0` |

## Intent

Prove that the first two terms `a 0`, `a 1` of a sequence obeying the two-term
recurrence are consecutive (`|a 0 - a 1| = 1`), given only that the far terms
`a 2023`, `a 2024` are consecutive, by strengthening the goal to "every
adjacent pair up to index 2023 differs by 1" and descending by induction from
`k = 2023` down to `k = 0`.

## The decomposition

### parent `uk2024_r1_p2`: [`Compfiles/UK2024R1P2.lean` lines 28-45](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/UK2024R1P2.lean#L28-L45) ([local copy](code/Compfiles/UK2024R1P2.lean))

```lean
problem uk2024_r1_p2 (a : ℕ → ℤ)
    (ha : ∀ i ≥ 2, a i = 2 * a (i - 1) - a (i - 2) ∨ a i = 2 * a (i - 2) - a (i - 1))
    (ha' : |a 2023 - a 2024| = 1) :
    |a 0 - a 1| = 1 :=  by
  suffices H : ∀ k ≤ 2023, |a k - a (k + 1)| = 1 from H 0 (Nat.zero_le _)
  intro k hk
  induction hk using Nat.decreasingInduction with
  | self => exact ha'
  | of_succ i _ hP =>
    specialize ha (i + 1 + 1) (by norm_num)
    simp only [add_tsub_cancel_right, Nat.reduceSubDiff] at ha
    obtain ha | ha := ha <;> rw [ha] at hP
    · rwa [two_mul, ← sub_add, sub_add_cancel_right, neg_add_eq_sub] at hP
    -- This branch is invalid because the difference between the terms we know are
    -- consecutive is both 1 and a multiple of 2, which is a contradiction
    · rw [← sub_add, sub_add_eq_add_sub, ← two_mul, ← mul_sub_left_distrib, abs_mul,
          Int.mul_eq_one_iff_eq_one_or_neg_one] at hP
      obtain hP | hP := hP <;> replace hP := hP.1 <;> norm_num at hP
```

How the parts fit. The `suffices` replaces the single pair `(0, 1)` with the
whole invariant `H : ∀ k ≤ 2023, |a k - a (k + 1)| = 1`, and the original goal
is recovered at once as `H 0 (Nat.zero_le _)`. `H` is then proved by
`Nat.decreasingInduction` on the bound `hk : k ≤ 2023`, which reads the
quantifier as descending induction from the top. The `self` case is `k = 2023`
and is exactly the hypothesis `ha' : |a 2023 - a 2024| = 1`, closed by
`exact ha'`. The `of_succ` case steps from `i + 1` down to `i` with induction
hypothesis `hP : |a (i+1) - a (i+2)| = 1`; it specialises the recurrence `ha`
at index `i + 2`, simplifies the indices, and splits the disjunction with
`obtain ha | ha`. In the first branch the recurrence says
`a (i+2) = 2 * a (i+1) - a i`, so `hP` rewrites to the goal
`|a i - a (i+1)| = 1` and `rwa` closes it. In the second branch the recurrence
says `a (i+2) = 2 * a i - a (i+1)`, which rewrites `hP` to
`2 * |a (i+1) - a i| = 1`; `Int.mul_eq_one_iff_eq_one_or_neg_one` turns this
into `2 = 1 ∨ 2 = -1`, and `norm_num` closes both by contradiction. So one
disjunct carries the invariant downward and the other is impossible.

## Why it is good

1. The parent closes from the strengthened goal `H` by a decreasing induction
   whose `self` case is `exact ha'` and whose `of_succ` case closes both
   branches (lines 32-45); the file is built by the project's CI (`lake build`
   in `.github/workflows/push-main.yaml`). (`check`)
2. The `of_succ` step splits the recurrence with
   `obtain ha | ha <;> rw [ha] at hP` (line 39): the forward branch closes by
   the single rewrite chain on line 40, and the backward branch closes by
   contradiction through `Int.mul_eq_one_iff_eq_one_or_neg_one` then `norm_num`
   (lines 43-45). (`check`)
3. The author records why the backward branch is impossible: "This branch is
   invalid because the difference between the terms we know are consecutive is
   both 1 and a multiple of 2, which is a contradiction" (lines 41-42).
   (`author-statement`)
4. The whole parent proof is 14 lines (32-45) and states no auxiliary lemma:
   the only local statement is the `suffices` goal `H`, proved in place by the
   induction. (`measurement`)

In my opinion the detail worth copying is the two-sided role of the recurrence
in the step: the same `obtain` split yields one branch that carries the
invariant and one that is outright contradictory, so no separate lemma is
needed to rule out the "wrong" direction.

## When to use it, and when not

Use it when a relation between consecutive sequence terms is known at a high
index and must be shown at a low one, and the defining recurrence propagates
the relation downward in one direction while forcing a contradiction in the
other — the pattern of a "consecutive" or "unit gap" invariant under a
two-term recurrence. The strengthening `∀ k ≤ N, P k` should be stated as a
`suffices` and instantiated at the target index. Avoid it when the recurrence's
"wrong" branch is not contradictory (then the step needs a genuine argument
and this split will not close), when the hypothesis is not exactly the top
case of the induction, or when the strengthened invariant is false or too weak
to propagate.

## Consequences

The `suffices` creates a stronger obligation `∀ k ≤ 2023, ...` that must be
discharged at `k = 0` (done by `H 0 (Nat.zero_le _)`). Decreasing induction on
the bound splits into a top case, which must coincide with the hypothesis, and
a step from `i + 1` to `i`. The step splits the recurrence disjunctively; one
branch must reduce the induction hypothesis to the goal, the other must be
contradictory (here via `Int.mul_eq_one_iff_eq_one_or_neg_one` plus `norm_num`).
Failure modes: if the "wrong" recurrence branch is not contradictory, or the
strengthened invariant does not propagate downward, the `of_succ` case does not
close; if the bound `2023` is wrong, the `self` case no longer matches `ha'`.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/.github/workflows/push-main.yaml runs 'lake build' on push to main (default branch); the file Compfiles/UK2024R1P2.lean is part of the lake build | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 1745e6ced3e671bd74417548494b034eb2c87da8 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Lines 32-45 of the copied file show suffices H (l.32), induction hk using Nat.decreasingInduction (l.34), self => exact ha' (l.35), of_succ closes both obtain branches (l.36-45), and H 0 (Nat.zero_le _) at l.32; CI workflow push-main.yaml runs lake build on push to main | verifier |
| 2 | verified | l.39 obtain ha | ha := ha <;> rw [ha] at hP; l.40 forward branch rwa [two_mul, ← sub_add, sub_add_cancel_right, neg_add_eq_sub] at hP; l.43-45 backward branch rw [... abs_mul, Int.mul_eq_one_iff_eq_one_or_neg_one] at hP then obtain hP | hP <;> norm_num at hP | verifier |
| 3 | verified | l.41-42 comment reads 'This branch is invalid because the difference between the terms we know are consecutive is both 1 and a multiple of 2, which is a contradiction' | verifier |
| 4 | verified | Parent excerpt is lines 32-45 = 14 lines; the only local declaration is the suffices goal H (l.32), no auxiliary lemma/have/let in the excerpt | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Decomposition matches code: parent (lines 28-45) strengthens to H : forall k <= 2023, |a k - a (k+1)| = 1 and closes via H 0 (Nat.zero_le _); induction on hk with Nat.decreasingInduction has self = exact ha' (line 35) and of_succ splitting the recurrence with obtain ha | ha <;> rw [ha] at hP (line 39). Children match: self closes by 'exact ha''; forward branch by rwa [two_mul, ...] (line 40); backward branch by rw [..., abs_mul, Int.mul_eq_one_iff_eq_one_or_neg_one] then obtain/norm_num (lines 43-45), giving 2 * |a (i+1) - a i| = 1 then 2=1 / 2=-1 contradiction. Closes: no sorry/axiom in file, CI (push-main.yaml) runs lake build over the repo. Author comment (lines 41-42) and 14-line count (32-45) verified. | reviewer-correctness |
| generality | accept | Move stated transferably: applicability.use_when abstracts the example to 'relation P propagates downward through the recurrence in one direction and forces a contradiction in the other; decreasing induction from a known-high index reaches the low one; state the strengthened invariant ∀ k ≤ N, P k as a suffices', and also_known_as covers descending/decreasing induction, Nat.decreasingInduction, induction on a bound. avoid_when and consequences are honest and specific: each failure mode traces to a concrete structure (wrong recurrence branch not contradictory -> of_succ does not close; hypothesis not the exact top case / wrong bound 2023 -> self case no longer matches ha'; invariant false or too weak to propagate). The transferable insight (the two-sided role of the disjunction: one branch carries the invariant, the other is contradictory) is named in the opinion paragraph and echoed in the consequences. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are consistent. check_provenance.py passes (file byte-identical at 1745e6ced3e671bd74417548494b034eb2c87da8). Commit 1745e6ced3e671bd74417548494b034eb2c87da8 is identical in entry.json, source.json and SOURCE.md. Licence Apache-2.0 is recorded in entry.json and README and matches the LICENSE at the pinned commit (Apache License Version 2.0, fetched and diff-identical to sources/compfiles/upstream-LICENSE). Copied file's header states 'Released under Apache 2.0 license as described in the file LICENSE'. File permalink and site permalink (#L28-L45) use the correct commit and path, and lines 28-45 match the problem statement and proof in the copied file. SOURCE.md records repo, pinned commit, licence and attribution; copied code is verbatim under the source. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/dwrensha/compfiles at commit `1745e6ced3e671bd74417548494b034eb2c87da8`, under `Apache-2.0`; see the [source note](../../sources/compfiles/SOURCE.md) for the licence text and attribution.
