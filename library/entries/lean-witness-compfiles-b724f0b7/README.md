# Witness assignment a=b=c=d=6/5 for USAMO 1978 P1

| | |
|---|---|
| Kind | instance |
| Move | witness |
| Language | lean |
| Status | accepted |
| Source | [compfiles](../../sources/compfiles/SOURCE.md) at `1745e6ced3e6` |
| Licence | `Apache-2.0` |

## Intent

To prove `max_e = 16/5` is the greatest value of `e` in the set, the membership
half is closed by naming the maximising assignment directly: four `use (6 / 5)`
tactics fix `a = b = c = d = 6/5` (with `e` already bound to `max_e = 16/5`),
and one `constructor <;> norm_num` discharges the two equations that define
`IsGood`. No lemma is stated; the witness and its two defining equations are
the whole existence proof.

## The decomposition

### parent `usa1978_p1`: [`Compfiles/Usa1978P1.lean` lines 35-46](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Usa1978P1.lean#L35-L46) ([local copy](code/Compfiles/Usa1978P1.lean))

```lean
problem usa1978_p1 :
    IsGreatest { e : ℝ | ∃ a b c d : ℝ, IsGood a b c d e } max_e := by
  -- solution 3 from
  -- https://artofproblemsolving.com/wiki/index.php/1978_USAMO_Problems/Problem_1
  unfold IsGreatest IsGood max_e upperBounds
  constructor
  · simp only [Set.mem_ofPred_eq]
    use (6 / 5)
    use (6 / 5)
    use (6 / 5)
    use (6 / 5)
    constructor <;> norm_num
```

### context `usa1978_p1_upper_bound`: [`Compfiles/Usa1978P1.lean` lines 47-67](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Usa1978P1.lean#L47-L67) ([local copy](code/Compfiles/Usa1978P1.lean))

```lean
  · simp only [Set.mem_ofPred_eq]
    intro e
    contrapose!
    intro he a b c d h1 h2
    apply not_le_of_gt he
    have h11 : (a + b + c + d) ^ 2 = (8 - e) ^ 2 := by
      rw [(by rw [← h1]; simp only [add_sub_cancel_right] : a + b + c + d = 8 - e)]
    have h12 :  a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 16 - e ^ 2 := by
      rw [← h2]; simp only [add_sub_cancel_right]
    have h3 : (a - b)^2 + (a - c)^2 + (a - d)^2 +
              (b - c)^2 + (b - d)^2 + (c - d)^2 = 4 * (16 - e^2) - (8 - e)^2 := by
      linear_combination 4 * h12 - h11
    have h4 : 4 * (16 - e ^ 2) - (8 - e) ^ 2 ≥ 0 := by rw [← h3]; positivity
    revert h4
    rw [(by ring_nf : 4 * (16 - e ^ 2) - (8 - e) ^ 2 = e * (16 - 5 * e))]
    contrapose!
    intro _
    rw [mul_comm]
    apply mul_neg_of_neg_of_pos
    · linarith
    · positivity
```

How the parts fit. `IsGreatest s a` unfolds to `a ∈ s ∧ a ∈ upperBounds s`, so
`unfold IsGreatest IsGood max_e upperBounds` followed by `constructor` splits
the goal into two branches. The first (lines 41-46) is the *membership* branch:
`max_e` is in `{e | ∃ a b c d, IsGood a b c d e}`, i.e. the value `16/5` is
actually attained. `simp only [Set.mem_ofPred_eq]` reduces it to
`∃ a b c d : ℝ, IsGood a b c d max_e`. The four `use (6 / 5)` tactics introduce
the witness `a = b = c = d = 6/5` (there is no `use` for `e`; `e` is the bound
variable of the set, fixed at `max_e = 16/5`). That leaves the predicate
`IsGood (6/5) (6/5) (6/5) (6/5) (16/5)`, and `constructor <;> norm_num` closes
both of its conjuncts — `a+b+c+d+e = 8` and `a²+b²+c²+d²+e² = 16` — by
computing on the concrete fractions.

The second branch (lines 47-67, shown as context) is a different move: it proves
`max_e ∈ upperBounds …`, i.e. every admissible `e` is `≤ 16/5`, by a
Cauchy–Schwarz / `linear_combination` argument. It is included so the reader sees
that the witness move carries only the *attained* half of `IsGreatest`; the
*upper-bound* half is a separate suffices-style proof.

The finder's brief described this site as "the maximising assignment e = 6/5
… establishing the IsGreatest upper bound branch". In the code the four
`use (6 / 5)` witnesses are `a, b, c, d`, not `e` (`e = max_e = 16/5`), and they
close the membership branch, not the upper-bound branch.

## Why it is good

1. The membership branch closes in six lines — four `use (6 / 5)` and one
   `constructor <;> norm_num` — with no named lemma and no manual rewriting
   (lines 41-46). *check*: the file is built by `lake build` in
   `.github/workflows/push-main.yaml` (lines 49-56), which runs on pushes to
   `main`.
2. The authors name the informal source in a comment — "solution 3 from
   https://artofproblemsolving.com/wiki/index.php/1978_USAMO_Problems/Problem_1"
   (lines 37-38) — and the formal `use (6 / 5)` reproduces that solution's
   maximising assignment `a = b = c = d = 6/5`, `e = 16/5`. *author-statement*.
3. The witness move carries the entire "`max_e` is attained" direction in 6
   lines (41-46) against 21 lines (47-67) for the upper-bound direction.
   *measurement*, counted on the copied file (70 lines total).

## When to use it, and when not

Use it when the witness for an existential is a concrete, closed-form value —
typically a maximising or minimising assignment you can compute or read off
(here `a = b = c = d = 6/5` from the two constraints, with the four variables
equal by symmetry). Then `use w` fixes the value and the remaining goal is only
the witness's defining equations, which `norm_num`/`linarith` close. This is the
Lean form of "exhibit the object and check it satisfies the predicate".

Avoid it when the object's existence needs a theorem (intermediate value, a
fixed point, a choice function) rather than an explicit value, or when checking
that the candidate satisfies the predicate is itself substantial; `use w` then
merely defers the real difficulty, and a named `have`/lemma about the witness
belongs before it.

## Consequences

The move replaces `∃ x, P x` by `P w` for the chosen `w`, so a wrong witness
value makes the remaining goal unprovable and must be fixed before anything
else; here `6/5` is forced by `e = 16/5` and the two equations, and the four
equalities rely on the solution's symmetry. The witness must satisfy every
conjunct of the predicate: `IsGood`'s two equations close together under
`constructor <;> norm_num`, and if either were not `norm_num`-solvable the
shared `<;>` would leave a goal behind. Finally, `use` only handles the
attained half of `IsGreatest`; the upper-bound half is a separate argument and
must not be forgotten.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push-main.yaml triggers on push to main (default branch) and runs 'lake build' at lines 49-56; fetched at pinned commit 1745e6c; the lake build compiles all Compfiles modules including Compfiles/Usa1978P1.lean | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 1745e6ced3e671bd74417548494b034eb2c87da8 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Copied file code/Compfiles/Usa1978P1.lean L41-L46: simp only, four use (6/5), constructor <;> norm_num = 6 lines, no named lemma, no rw; workflow push-main.yaml L49-56 runs lake build on main | verifier |
| 2 | verified | Copied file L37-L38 comment 'solution 3 from https://artofproblemsolving.com/wiki/index.php/1978_USAMO_Problems/Problem_1'; L30 max_e=(16:ℝ)/5 and L42-45 four use (6/5) reproduce assignment a=b=c=d=6/5, e=16/5 | verifier |
| 3 | verified | Copied file: membership branch L41-46 = 6 lines, upper-bound branch L47-67 = 21 lines, file ends L70 (end Usa1978P1) | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent statement matches code L35-36 (IsGreatest {e | exists a b c d, IsGood a b c d e} max_e). Children match: witness a=b=c=d=6/5 via four 'use (6/5)' at L42-45 (e fixed to max_e=16/5, L30); IsGood-at-witness closed by 'constructor <;> norm_num' at L46 splitting IsGood's two conjuncts (L32-33). Closes: 4*(6/5)+16/5=8 and 4*(36/25)+256/25=16, so norm_num discharges both equations. No named lemma, no rw. Decomposition is exactly what the entry says and closes. | reviewer-correctness |
| generality | accept | Move is stated generally, not as a one-off: applicability.goal_shape names the generic exists-shape (∃ a b c d, IsGood a b c d max_e reached via unfold+constructor+simp), and use_when gives the portable recipe 'concrete closed-form witness known -> use w fixes the value, leaves only the defining equations, norm_num/linarith close'; the maximising/minimising framing is marked 'often'/'typically', not exhaustive, and the README states the general principle as 'exhibit the object and check it satisfies the predicate'. avoid_when is honest and specific: existence needing a theorem (intermediate value, fixed point, choice) rather than an explicit value, or a residual predicate that is itself substantial - in which case use w merely defers the difficulty and a named have/lemma belongs first. Consequences are honest and specific: a wrong witness makes the goal unprovable and must be fixed first; the witness must satisfy every conjunct; the shared '<;>' leaves a goal if one conjunct is not norm_num-solvable; and use covers only the attained half of IsGreatest, the upper-bound half being a separate argument. | reviewer-generality |
| provenance-licence | accept | check_provenance passed: 1 file byte-identical at pinned commit 1745e6ced3e671bd74417548494b034eb2c87da8. Commit is consistent across entry.json source.commit, files/sites permalinks, source.json, and SOURCE.md (pinned 2026-11-12T10:23:49Z). Licence Apache-2.0 is consistent across entry.json, README, source.json, SOURCE.md, the copied file header ('Released under Apache 2.0 license') and upstream-LICENSE (Apache 2.0 text). All permalinks use the blob/commit form and resolve to Compfiles/Usa1978P1.lean. Traceable end to end. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/dwrensha/compfiles at commit `1745e6ced3e671bd74417548494b034eb2c87da8`, under `Apache-2.0`; see the [source note](../../sources/compfiles/SOURCE.md) for the licence text and attribution.
