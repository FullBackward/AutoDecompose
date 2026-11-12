# Witness n = 4000 for IMO 1982 Q3(a)

| | |
|---|---|
| Kind | instance |
| Move | witness |
| Language | lean |
| Status | verified |
| Source | [mathlib4](../../sources/mathlib4/SOURCE.md) at `e1545ebed975` |
| Licence | `Apache-2.0` |

## Intent

A statement that *some* index makes a sum at least `3.999` is reduced to a
single, fully explicit choice: `n = 4000`. The choice is not magic — it is the
index at which the already-proved general bound `4n/(n+1) ≤ …` (lemma `ineq`)
equals `3.999` exactly, so after fixing the witness only a numerical comparison
remains.

## The decomposition

### parent `imo1982_q3a`: [`Archive/Imo/Imo1982Q3.lean` lines 78-83](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Imo/Imo1982Q3.lean#L78-L83) ([local copy](code/Archive/Imo/Imo1982Q3.lean))

```lean
/-- Part a of the problem is solved by `n = 4000`. -/
theorem imo1982_q3a (hx : Antitone x) (h0 : x 0 = 1) (hp : ∀ k, 0 < x k) :
    ∃ n : ℕ, 3.999 ≤ ∑ k ∈ range n, (x k) ^ 2 / x (k + 1) := by
  use 4000
  convert! Imo1982Q3.ineq (Nat.succ_ne_zero 3998) hx h0 hp
  norm_num
```

### context `ineq`: [`Archive/Imo/Imo1982Q3.lean` lines 53-74](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Imo/Imo1982Q3.lean#L53-L74) ([local copy](code/Archive/Imo/Imo1982Q3.lean))

```lean
/-- The main inequality used for part a. -/
lemma ineq (h0 : x 0 = 1) (hp : ∀ k, 0 < x k) :
    4 * n / (n + 1) ≤ ∑ k ∈ range (n + 1), x k ^ 2 / x (k + 1) := by
  calc
    -- We first use AM-GM.
    _ ≤ (∑ k ∈ range n, x (k + 1) + 1) ^ 2 / (∑ k ∈ range n, x (k + 1)) * n / (n + 1) := by
      gcongr
      rw [le_div_iff₀]
      · simpa using four_mul_le_sq_add (∑ k ∈ range n, x (k + 1)) 1
      · exact sum_pos (fun k _ ↦ hp _) (nonempty_range_iff.2 hn)
    -- We move the fraction into the denominator.
    _ = (∑ k ∈ range n, x (k + 1) + 1) ^ 2 / ((∑ k ∈ range n, x (k + 1)) * (1 + 1 / n)) := by
      field
    -- We make use of the `le_avg` lemma.
    _ ≤ (∑ k ∈ range (n + 1), x k) ^ 2 / ∑ k ∈ range (n + 1), x (k + 1) := by
      gcongr
      · exact sum_pos (fun k _ ↦ hp _) nonempty_range_add_one
      · exact add_nonneg (sum_nonneg fun k _ ↦ (hp _).le) zero_le_one
      · rw [sum_range_succ', h0]
      · exact le_avg hn (hx.comp_monotone @Nat.succ_le_succ)
    -- We conclude by Sedrakyan.
    _ ≤ _ := sq_sum_div_le_sum_sq_div _ x fun k _ ↦ hp (k + 1)
```

How the parts fit. The parent is an existential `∃ n : ℕ, 3.999 ≤ ∑ k ∈ range n,
(x k) ^ 2 / x (k + 1)`. The proof has two parts:

1. **Choose the witness** — `use 4000` (line 81) fixes `n = 4000`, turning the
   existential into the single goal `3.999 ≤ ∑ k ∈ range 4000, (x k) ^ 2 /
   x (k + 1)`.
2. **Prove the property at the witness** — this is done by *transferring* the
   general bound `ineq` and finishing numerically.

The transfer relies on an off-by-one: `ineq` (context excerpt, line 55) bounds a
sum over `range (n + 1)` by `4 * n / (n + 1)`, so to bound the sum over
`range 4000` one instantiates `ineq` at `n = 3999`. The call
`convert! Imo1982Q3.ineq (Nat.succ_ne_zero 3998) hx h0 hp` (line 82) supplies
`3999 ≠ 0` (that is `Nat.succ_ne_zero 3998`) as `ineq`'s `hn` hypothesis, so the
conclusion becomes `4 * 3999 / 4000 ≤ ∑ k ∈ range 4000, …`. Because
`4 * 3999 / 4000 = 3.999` exactly, `convert!` changes the goal's left side to
that expression and `norm_num` (line 83) closes the residual comparison. No new
lemma is stated for the witness: the only named parts are the already-proved
`ineq` and the arithmetic.

The doc comment on the parent (line 78) records the choice the reader would
otherwise have to reverse-engineer.

## Why it is good

1. *(check)* The file is compiled by mathlib's CI, which builds `Archive` and
   then re-checks it with `lake build --no-build --wfail Archive`
   ([build_template.yml lines 247-253 and 291-297](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/.github/workflows/build_template.yml#L247-L253),
   triggered by
   [build.yml's `on: push` trigger and build job](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/.github/workflows/build.yml#L3-L35)).
2. *(check)* The parent is closed from its parts in three tactic lines with no
   further step, and the witness is exact: `use 4000` fixes the witness, `ineq`
   is instantiated at `n = 3999` so its `range (n + 1)` is `range 4000` and its
   bound `4·3999/4000` equals `3.999`, and `norm_num` closes the residual
   ([lines 79-83 and 54-55](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Imo/Imo1982Q3.lean#L79-L83)).
3. *(author-statement)* The authors record the witness choice in the doc
   comment: "Part a of the problem is solved by `n = 4000`."
   ([line 78](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Imo/Imo1982Q3.lean#L78)).
4. *(author-statement)* The module doc comment states the strategy the witness
   instantiates: "For part a, we use Sedrakyan's lemma to show the sum is
   bounded below by 4n/(n+1), which can be made arbitrarily close to 4 by
   taking large n."
   ([lines 28-30](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Imo/Imo1982Q3.lean#L28-L30)).
5. *(known-use)* The same witness move closes part (b) in the same file:
   `refine ⟨fun k ↦ 2⁻¹ ^ k, …⟩` introduces the witness sequence for the
   existential `∃ x : ℕ → ℝ, …`.
   ([lines 86-88](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Imo/Imo1982Q3.lean#L86-L88)).

In my opinion the detail worth copying is the *exact* choice of witness: `4000`
is `3999 + 1`, the one index at which the general bound `4n/(n+1)` lands exactly
on the target `3.999`, so the only residual is arithmetic.

## When to use it, and when not

Use it when the goal is an existential `∃ n, c ≤ S n` and a general lower bound
`B n ≤ S n` has already been proved for all `n` (or all `n ≠ 0`), so the
witness is found by solving `c ≤ B n` for a concrete `n` — ideally one where
`B n = c` exactly, so the residual is a bare `norm_num` comparison. Avoid it
when no closed-form bound exists (the witness would then carry its own proof
burden), when the target constant is not attained by the bound at any finite
index (e.g. the bound only approaches `4` in the limit — an exact `3.999` at a
finite `n` is then impossible and the comparison will not close), or when the
witness is not a numeral or closed term that `use` can fix.

## Consequences

The move replaces "some `n` works" with two obligations: the witness must be
supplied, and the property must hold at it. Because the witness is a numeral,
the property proof reduces to transferring a general bound and closing a
numerical comparison. It creates obligations of its own: the witness must be
concrete (so `use` can fix it), the general bound's hypotheses must be met at
that value (`ineq` needs `n ≠ 0`, hence `Nat.succ_ne_zero 3998`), and the bound
must actually reach the target — if the chosen index made `B n < c`, `convert!`
would leave an unprovable inequality. The off-by-one between the goal's `range
n` and the bound's `range (n + 1)` is a recurring failure mode: the witness for
the goal is one more than the bound's parameter.

## Verification

<!-- verification:start -->
Status: **verified**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build_template.yml builds Archive (step 'build archive, counterexamples and wanted' runs 'lake-build-with-retry.sh Archive Counterexamples Wanted' at line 252, and step 'check that Archive built' gates on 'lake build --no-build --wfail Archive' at line 297); invoked by .github/workflows/build.yml on: push (lines 3-4). Pinned commit e1545ebed97594477bbd88b2fe948ffce56e5af2 is on master (default branch), confirmed via GitHub compare API: master is ahead_by 1, behind_by 0. | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at e1545ebed97594477bbd88b2fe948ffce56e5af2 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Fetched .github/workflows/build_template.yml and build.yml at e1545ebed97594477bbd88b2fe948ffce56e5af2 via fetch_file.py. build_template.yml line 252 runs '../tools-branch/scripts/lake-build-with-retry.sh Archive Counterexamples Wanted' and line 297 runs 'lake build --no-build --wfail Archive'; build.yml lines 3-4 are 'on: push:' (with branches-ignore), and line 35 'uses: ./.github/workflows/build_template.yml'. | verifier |
| 2 | verified | Copied code Archive/Imo/Imo1982Q3.lean: line 81 'use 4000', line 82 'convert! Imo1982Q3.ineq (Nat.succ_ne_zero 3998) hx h0 hp', line 83 'norm_num' (three tactic lines). ineq (lines 54-55) is '4 * n / (n + 1) <= sum k in range (n+1), x k ^ 2 / x (k+1)', with hypothesis hn : n != 0 from line 37. Nat.succ_ne_zero 3998 : 3998 + 1 != 0 instantiates n = 3999, so range (n+1) = range 4000 and bound 4*3999/4000 = 3.999. | verifier |
| 3 | verified | Copied code Archive/Imo/Imo1982Q3.lean line 78 reads: /-- Part a of the problem is solved by n = 4000. -/ — matches the quoted doc comment verbatim. | verifier |
| 4 | verified | Copied code Archive/Imo/Imo1982Q3.lean lines 28-29 (module doc comment) read: 'For part a, we use Sedrakyan's lemma to show the sum is bounded below by 4n/(n+1), which can be made arbitrarily close to 4 by taking large n.' — matches the quoted claim verbatim. | verifier |
| 5 | verified | Copied code Archive/Imo/Imo1982Q3.lean lines 86-88: theorem imo1982_q3b has goal 'exists x : N -> R, ...', and line 88 'refine <fun k => 2^-1 ^ k, ?_, pow_zero _, ?_, fun n => ?_>' introduces the witness sequence 2^-1 ^ k for the existential — the witness move closing part (b). | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Read copied code Archive/Imo/Imo1982Q3.lean: parent imo1982_q3a (L78-83) states exists n, 3.999 <= sum k in range n, (x k)^2 / x(k+1); proof is use 4000 (L81), convert! Imo1982Q3.ineq (Nat.succ_ne_zero 3998) hx h0 hp (L82), norm_num (L83). ineq (L54-55) bounds sum over range(n+1) by 4n/(n+1); Nat.succ_ne_zero 3998 : 3999 != 0 instantiates n=3999 so range(n+1)=range 4000 and 4*3999/4000=3.999 exactly. Children match the code: witness n=4000 closed by 'use 4000'; property at witness closed by the convert!/norm_num transfer. Decomposition is what the entry says and closes. | reviewer-correctness |
| generality | object | Move is stated generally (goal shape ∃ n, c ≤ S n with a general lower bound B n ≤ S n; witness found by inverting the bound), and consequences are honest and grounded. But the 'when not to use' clause contains a factually wrong illustration: it says 'the bound only approaches 4 in the limit — an exact 3.999 at a finite n is then impossible', yet the entry's own point is that 4·3999/4000 = 3.999 exactly, i.e. 3.999 IS attained at finite n (n=4000). This directly contradicts the entry and would mislead a reader about when the move applies. Fix: reword the example to a target the bound genuinely never reaches, e.g. 'the bound 4n/(n+1) only approaches 4 from below, so a target of 4 itself is never attained at any finite n and the comparison will not close'. | reviewer-generality |
| provenance-licence | accept | Provenance-licence lens: check_provenance.py passes (1 file byte-identical at e1545ebed97594477bbd88b2fe948ffce56e5af2); copied file Archive/Imo/Imo1982Q3.lean has bytes 4087 and sha256 35c72bb4...29187b, both matching entry.json files[0]. Commit e1545ebed...56e5af2 is used consistently in source.commit, files.permalink, both sites.permalink, and all claim evidence URLs. Site line ranges are correct against the copied code (parent L78-83: doc comment, two-line statement, three tactic lines; context L53-74: doc comment + lemma). Licence Apache-2.0 is recorded in entry.json and SOURCE.md (detected), matches the file header 'Released under Apache 2.0 license' and the copied upstream-LICENSE (Apache License 2.0). SOURCE.md records repo, pinned commit, browse link, licence and attribution, consistent with the entry. Everything traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover-community/mathlib4 at commit `e1545ebed97594477bbd88b2fe948ffce56e5af2`, under `Apache-2.0`; see the [source note](../../sources/mathlib4/SOURCE.md) for the licence text and attribution.
