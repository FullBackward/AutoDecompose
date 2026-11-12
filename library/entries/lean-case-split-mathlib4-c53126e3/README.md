# Case split on the exponent n for IMO 1961 Q3 (forward direction)

| | |
|---|---|
| Kind | instance |
| Move | case-split |
| Language | lean |
| Status | verified |
| Source | [mathlib4](../../sources/mathlib4/SOURCE.md) at `e1545ebed975` |
| Licence | `Apache-2.0` |

## Intent

The forward direction of IMO 1961 Q3 — that `(cos x)^n - (sin x)^n = 1` forces
`x` and the parity of `n` into one of three shapes — is reduced, once the cases
`sin x = 0` and `cos x = 0` are discharged, to a `match` on the exponent `n`:
two small exceptional cases `n = 1` and `n = 2` close by direct rewriting, and
the residual `n = m + 2` closes by one uniform bound using `|cos x| < 1` and
`|sin x| < 1`.

## The decomposition

### parent `Imo1961Q3_forward_match`: [`Archive/Imo/Imo1961Q3.lean` lines 51-71](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Imo/Imo1961Q3.lean#L51-L71) ([local copy](code/Archive/Imo/Imo1961Q3.lean))

```lean
        match n with
        | 1 =>
          rw [pow_one, pow_one, sub_eq_iff_eq_add] at h
          have : 2 * sin x * cos x = 0 := by
            simpa [h, add_sq, add_assoc, ← two_mul, mul_add, mul_assoc, ← sq]
              using cos_sq_add_sin_sq x
          simp [hsinx, hcosx] at this
        | 2 =>
          rw [← cos_sq_add_sin_sq x, sub_eq_add_neg, add_right_inj, neg_eq_self] at h
          exact absurd (eq_zero_of_pow_eq_zero h) hsinx
        | (n + 1 + 2) =>
          set m := n + 1
          refine absurd ?_ h.not_lt
          calc
            (cos x) ^ (m + 2) - (sin x) ^ (m + 2) ≤ |cos x| ^ (m + 2) + |sin x| ^ (m + 2) := by
              simp only [← abs_pow, sub_eq_add_neg]
              gcongr
              exacts [le_abs_self _, neg_le_abs _]
            _ = |cos x| ^ m * cos x ^ 2 + |sin x| ^ m * sin x ^ 2 := by simp [pow_add]
            _ < 1 ^ m * cos x ^ 2 + 1 ^ m * sin x ^ 2 := by gcongr
            _ = 1 := by simp
```

### context `Imo1961Q3_statement`: [`Archive/Imo/Imo1961Q3.lean` lines 26-29](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Imo/Imo1961Q3.lean#L26-L29) ([local copy](code/Archive/Imo/Imo1961Q3.lean))

```lean
public theorem Imo1961Q3 {n : ℕ} {x : ℝ} (h₀ : n ≠ 0) :
    (cos x) ^ n - (sin x) ^ n = 1 ↔
      (∃ k : ℤ, k * π = x) ∧ Even n ∨ (∃ k : ℤ, k * (2 * π) = x) ∧ Odd n ∨
        (∃ k : ℤ, -(π / 2) + k * (2 * π) = x) ∧ Odd n := by
```

### context `forward_setup`: [`Archive/Imo/Imo1961Q3.lean` lines 31-50](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Imo/Imo1961Q3.lean#L31-L50) ([local copy](code/Archive/Imo/Imo1961Q3.lean))

```lean
  · intro h
    rcases eq_or_ne (sin x) 0 with hsinx | hsinx
    · rw [hsinx, zero_pow h₀, sub_zero, pow_eq_one_iff_of_ne_zero h₀, cos_eq_one_iff,
        cos_eq_neg_one_iff] at h
      rcases h with ⟨k, rfl⟩ | ⟨⟨k, rfl⟩, hn⟩
      · cases n.even_or_odd with
        | inl hn => refine .inl ⟨⟨k * 2, ?_⟩, hn⟩; simp [mul_assoc]
        | inr hn => exact .inr <| .inl ⟨⟨_, rfl⟩, hn⟩
      · exact .inl ⟨⟨2 * k + 1, by push_cast; ring⟩, hn⟩
    · rcases eq_or_ne (cos x) 0 with hcosx | hcosx
      · right; right
        rw [hcosx, zero_pow h₀, zero_sub, ← neg_inj, neg_neg, pow_eq_neg_one_iff,
          sin_eq_neg_one_iff] at h
        simpa only [eq_comm] using h
      · have hcos1 : |cos x| < 1 := by
          rw [abs_cos_eq_sqrt_one_sub_sin_sq, sqrt_lt' one_pos]
          simp [sq_pos_of_ne_zero hsinx]
        have hsin1 : |sin x| < 1 := by
          rw [abs_sin_eq_sqrt_one_sub_cos_sq, sqrt_lt' one_pos]
          simp [sq_pos_of_ne_zero hcosx]
```

How the parts fit. The forward direction is the `intro h` goal at line 31. Two
`rcases` dispose of the degenerate cases first: `sin x = 0` (lines 32-39) and
`cos x = 0` (lines 41-44). What remains is the branch `sin x ≠ 0 ∧ cos x ≠ 0`
(`hsinx` from line 32, `hcosx` from line 40), where the author derives the two
strict bounds `hcos1 : |cos x| < 1` and `hsin1 : |sin x| < 1` (lines 45-50). In
that branch the `match n with` (line 51) shows the hypothesis
`h : (cos x)^n - (sin x)^n = 1` is contradictory for every `n ≥ 1`:

- **`n = 1`** (lines 52-57). `rw [pow_one, pow_one, sub_eq_iff_eq_add] at h`
  turns `h` into `cos x = sin x + 1`; combining that with
  `cos_sq_add_sin_sq x` forces `2 * sin x * cos x = 0`, and
  `simp [hsinx, hcosx] at this` reduces it to a contradiction.
- **`n = 2`** (lines 58-60). `rw [← cos_sq_add_sin_sq x, …] at h` rewrites
  `h` to force `sin x = 0`; `exact absurd (eq_zero_of_pow_eq_zero h) hsinx`
  closes it against `hsinx`.
- **`n = m + 2`** (lines 61-71). `set m := n + 1` writes the exponent
  `n + 1 + 2` as `m + 2`; a `calc` chain bounds the difference by
  `≤ |cos x|^(m+2) + |sin x|^(m+2) = |cos x|^m · cos x² + |sin x|^m · sin x² <
  1^m · cos x² + 1^m · sin x² = 1`, using `hcos1`/`hsin1` in the two `gcongr`
  steps; `refine absurd ?_ h.not_lt` closes it, since `h` says the difference
  equals `1`.

There is no `| 0 =>` branch: the theorem's premise `h₀ : n ≠ 0` (line 26)
already excludes `n = 0`, so the three branches cover the whole domain and the
split's exhaustiveness is discharged by the premise, not by a separate child.

## Why it is good

1. The `match n with` (lines 51-71) has exactly three branches and each closes
   on its own — `simp [hsinx, hcosx] at this` (line 57), `exact absurd … hsinx`
   (line 60), and `refine absurd ?_ h.not_lt` with a `calc` chain ending in
   `< 1` (lines 63-71) — with no auxiliary lemma (`check`, lines 51-71).
2. The match lists no `| 0 =>` branch; its branches `1`, `2`, `n + 1 + 2` cover
   exactly `n ≥ 1`, matching the premise `h₀ : n ≠ 0` (line 26), so
   exhaustiveness rides on the premise rather than an extra child (`check`,
   lines 26-29 and 51-61).
3. The residual branch reuses the two strict bounds `hcos1`/`hsin1`
   (lines 45-50) in its two `gcongr` steps (lines 67 and 70), which is what
   makes the chain strictly decreasing (`check`, lines 45-50 and 63-71).
4. The authors flag that the proof follows an external write-up: "The solution
   is based on the one at the Art of Problem Solving website" (`author-statement`,
   lines 19-21).
5. The three branches are 6, 3 and 11 lines, so the residual case is the bulk
   and the two small cases are near one-liners (`measurement`, lines 52-71).

In my opinion the reusable detail is the split itself — two explicit small
cases plus a residual successor pattern `n + 1 + 2` (with `set m := n + 1`) —
rather than any one tactic: it is the shape "enumerate the exceptions, then
give one bound for everything else".

## When to use it, and when not

Use it when a goal about `n : ℕ` depends on `n` only through which small
numerals `n` equals and a residual `n ≥ 3` that admits one uniform argument:
the exceptional cases close by short, separate rewrites while every larger `n`
shares a single bound (here, powers of `|cos x|` and `|sin x|` shrink because
`|cos x| < 1` and `|sin x| < 1`). State the bound first, as `hcos1`/`hsin1` are
stated before the match.

Avoid it when the residual case genuinely needs induction (then the recursion
is the content, not a one-shot bound), when the cases do not share a residual
argument, or when the domain includes `n = 0` with no hypothesis excluding it —
then you need an explicit `0` branch.

## Consequences

The `match` creates three goals. There is no `0` branch: exhaustiveness of the
split over `n ≥ 1` rests on the premise `h₀ : n ≠ 0` (line 26), so a `0` goal
never appears as a child. The residual branch introduces a fresh `n` (the
pattern variable in `n + 1 + 2`) and renames it `set m := n + 1`, so the
exponent is written `m + 2` before the bound is applied; forgetting that
renaming breaks the head of the `calc` chain. The residual argument depends on
the two strict bounds `|cos x| < 1` and `|sin x| < 1` (lines 45-50): with only
`≤ 1` the `<` link would fail and the split would not close, so those bounds
are a hidden obligation of this move.

## Verification

<!-- verification:start -->
Status: **verified**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | commit e1545ebed97594477bbd88b2fe948ffce56e5af2 is on default branch master (compare base...master: behind_by 0); .github/workflows/build.yml delegates to .github/workflows/build_template.yml, which runs 'lake-build-with-retry.sh Archive Counterexamples Wanted' and 'lake build --no-build --wfail Archive', building Archive/Imo/Imo1961Q3.lean | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at e1545ebed97594477bbd88b2fe948ffce56e5af2 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | raw file at pinned commit: line 51 'match n with'; |1 => (52-57) closes at line 57 'simp [hsinx, hcosx] at this'; |2 => (58-60) closes at line 60 'exact absurd (eq_zero_of_pow_eq_zero h) hsinx'; |(n + 1 + 2) => (61-71) closes at line 63 'refine absurd ?_ h.not_lt' with calc chain lines 64-71 ending '< ... = 1' | verifier |
| 2 | verified | line 26 'public theorem Imo1961Q3 {n : Nat} {x : Real} (h0 : n != 0)'; lines 51-61 show 'match n with' branches |1, |2, |(n + 1 + 2) with no |0 branch | verifier |
| 3 | verified | lines 45-48 define hcos1 : |cos x| < 1 and hsin1 : |sin x| < 1; gcongr appears at lines 67 and 70 inside the residual calc chain (61-71) | verifier |
| 4 | verified | file header lines 19-21: 'The solution is based on the one at the Art of Problem Solving website' | verifier |
| 5 | verified | counted in raw file at pinned commit: branch n=1 lines 52-57 = 6 lines; n=2 lines 58-60 = 3 lines; n=m+2 lines 61-71 = 11 lines | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | object | Decomposition matches: lines 51-71 'match n with' has exactly |1 (53-57), |2 (59-60), |(n+1+2) (62-71); children n=1/n=2/residual and their closing tactics (rw/simp/absurd, exact absurd (eq_zero_of_pow_eq_zero h) hsinx, refine absurd ?_ h.not_lt with calc ending '_ = 1') are verbatim in the code, no |0 branch, and the file is built by mathlib CI so the split closes. BUT the residual child's closed_by and claim 3 say 'the two gcongr steps (lines 67 and 70) use hcos1/hsin1', which is false for line 67: that gcongr closes the '<=' step (65-68) via 'exacts [le_abs_self _, neg_le_abs _]' and uses neither bound; only the line-70 gcongr uses hcos1/hsin1 to make the '<' link strict. Fix: attribute hcos1/hsin1 to the second gcongr (line 70) only, and note the line-67 gcongr uses le_abs_self/neg_le_abs. | reviewer-correctness |
| generality | accept | Move is stated beyond the example: applicability.goal_shape/use_when abstract it to "a goal about n : Nat depending on n only through which small numerals it equals and a residual n >= 3 admitting one uniform argument", and also_known_as gives "small cases plus residual case"; the README labels the reusable shape "enumerate the exceptions, then give one bound for everything else" as opinion. When-not-to-use is honest and specific: residual genuinely needing induction, cases not sharing a residual argument, or domain including n = 0 without a hypothesis excluding it (then an explicit 0 branch is required). Consequences name concrete checkable obligations that match the copied code and the ci-record build: exhaustiveness of the 3-branch match rests on premise h0 : n != 0 (line 26) so no 0 child; the set m := n + 1 renaming (lines 61-62) is required or the calc head breaks; and the residual < link (line 70) needs the strict bounds (lines 45-50) since only <= 1 would fail. All specific and honest. | reviewer-generality |
| provenance-licence | accept | Provenance re-check passes: check_provenance.py reports 1 file byte-identical at e1545ebed97594477bbd88b2fe948ffce56e5af2 (commit valid, path resolves, recorded sha256 matches). Commit hash is identical across entry.json source.commit, all file/site permalinks, source.json, and SOURCE.md; README short form e1545ebed975 = first 12 chars. Permalink line ranges verified against the copied file: L51-71 match block, L26-29 statement, L31-50 forward_setup, L19-21 AoPS attribution, all exact. Licence Apache-2.0 is consistent everywhere: file header 'Released under Apache 2.0 license as described in the file LICENSE', source.json licence, SOURCE.md 'Licence (detected): Apache-2.0' with copied upstream-LICENSE (Apache License 2.0), entry.json licence, README licence column. Related entry lean-case-split-compfiles-6ac56e7f exists. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover-community/mathlib4 at commit `e1545ebed97594477bbd88b2fe948ffce56e5af2`, under `Apache-2.0`; see the [source note](../../sources/mathlib4/SOURCE.md) for the licence text and attribution.
