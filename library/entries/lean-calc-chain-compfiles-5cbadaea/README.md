# Calc chains bound b at the min and max of a for EGMO 2023 P1

| | |
|---|---|
| Kind | instance |
| Move | calc-chain |
| Language | lean |
| Status | verified |
| Source | [compfiles](../../sources/compfiles/SOURCE.md) at `1745e6ced3e6` |
| Licence | `Apache-2.0` |

## Intent

Reduce the goal `∀ i j, a i = a j` to the single fact `∀ i, b i = 2`, obtained
by bounding `b` from below at a minimum index `m` of `a` (`b m ≥ 2`) and from
above at a maximum index `M` (`b M ≤ 2`). Each bound is a two-link `calc`
chain, and the proof closes by antisymmetry (`eq_of_le_of_ge`).

## The decomposition

### parent `egmo2023_p1`: [`Compfiles/Egmo2023P1.lean` lines 28-63](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Egmo2023P1.lean#L28-L63) ([local copy](code/Compfiles/Egmo2023P1.lean))

```lean
problem egmo2023_p1 (n : ℕ) [NeZero n] (_ : n ≥ 3) (a : Fin n → ℝ) (ha : ∀ i, a i > 0)
    (b : Fin n → ℝ) (hb : ∀ i, b i = (a (i - 1) + a (i + 1)) / (a i))
    (h : ∀ i j, a i ≤ a j ↔ b i ≤ b j) : ∀ i j, a i = a j := by
  -- The solution was adapted from here: https://www.youtube.com/watch?v=PNFh789P31E.
  -- Note that indexing starts from 0 in the formalized statement.
  obtain ⟨m, hm⟩ := Finite.exists_min a
  obtain ⟨M, hM⟩ := Finite.exists_max a
  have h1 : b m ≥ 2 := calc b m
    _ ≥ (a m + a m) / (a m) := by
      rw [hb m]
      gcongr
      · exact le_of_lt (ha m)
      · exact hm (m - 1)
      · exact hm (m + 1)
    _ ≥ 2 := by
      rw [← two_mul, mul_div_cancel_right₀]
      positivity [ha m]
  have h2 : b M ≤ 2 := calc b M
    _ ≤ (a M + a M) / (a M) := by
      rw [hb M]
      gcongr
      · exact le_of_lt (ha M)
      · exact hM (M - 1)
      · exact hM (M + 1)
    _ ≤ 2 := by
      rw [← two_mul, mul_div_cancel_right₀]
      positivity [ha M]
  have h3 : ∀ i, b i = 2 := by
    intro i
    apply eq_of_le_of_ge
    · exact le_trans ((h i M).mp (hM i)) h2
    · exact le_trans h1 ((h m i).mp (hm i))
  intro i j
  apply eq_of_le_of_ge
  · rw [h i j, h3 i, h3 j]
  · rw [h j i, h3 j, h3 i]
```

### child `h1`: [`Compfiles/Egmo2023P1.lean` lines 35-44](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Egmo2023P1.lean#L35-L44) ([local copy](code/Compfiles/Egmo2023P1.lean))

```lean
  have h1 : b m ≥ 2 := calc b m
    _ ≥ (a m + a m) / (a m) := by
      rw [hb m]
      gcongr
      · exact le_of_lt (ha m)
      · exact hm (m - 1)
      · exact hm (m + 1)
    _ ≥ 2 := by
      rw [← two_mul, mul_div_cancel_right₀]
      positivity [ha m]
```

### child `h2`: [`Compfiles/Egmo2023P1.lean` lines 45-54](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Egmo2023P1.lean#L45-L54) ([local copy](code/Compfiles/Egmo2023P1.lean))

```lean
  have h2 : b M ≤ 2 := calc b M
    _ ≤ (a M + a M) / (a M) := by
      rw [hb M]
      gcongr
      · exact le_of_lt (ha M)
      · exact hM (M - 1)
      · exact hM (M + 1)
    _ ≤ 2 := by
      rw [← two_mul, mul_div_cancel_right₀]
      positivity [ha M]
```

### context `h3`: [`Compfiles/Egmo2023P1.lean` lines 55-63](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Egmo2023P1.lean#L55-L63) ([local copy](code/Compfiles/Egmo2023P1.lean))

```lean
  have h3 : ∀ i, b i = 2 := by
    intro i
    apply eq_of_le_of_ge
    · exact le_trans ((h i M).mp (hM i)) h2
    · exact le_trans h1 ((h m i).mp (hm i))
  intro i j
  apply eq_of_le_of_ge
  · rw [h i j, h3 i, h3 j]
  · rw [h j i, h3 j, h3 i]
```

How the parts fit. The parent first fixes a minimum index `m` and a maximum
index `M` of the finite sequence `a` (`obtain ⟨m, hm⟩ := Finite.exists_min a`,
`obtain ⟨M, hM⟩ := Finite.exists_max a`). Child `h1` uses the minimum property
`hm` to bound `b m` from below: expanding by `hb m` gives
`(a (m - 1) + a (m + 1)) / (a m)`, and since both `a (m - 1)` and `a (m + 1)`
are at least `a m`, `gcongr` lowers the ratio to `(a m + a m) / (a m)`, which
`rw [← two_mul, mul_div_cancel_right₀]` then `positivity [ha m]` reduces to `2`.
Child `h2` is the mirror image at the maximum `M`, bounding `b M ≤ 2`. Then
`h3` closes `∀ i, b i = 2` by `eq_of_le_of_ge`: the upper direction is
`b i ≤ b M ≤ 2` via `(h i M).mp (hM i)` (using `h : a i ≤ a j ↔ b i ≤ b j`) and
`h2`; the lower direction is `2 ≤ b m ≤ b i` via `h1` and `(h m i).mp (hm i)`.
The final goal `∀ i j, a i = a j` closes by the same antisymmetry, rewriting
`a i ≤ a j` and `a j ≤ a i` with `h` and the now-known `h3`.

## Why it is good

1. Both bound children are two-link `calc` chains with no auxiliary lemma: each
   link is a one-tactic block (`gcongr` for the monotonicity step, then
   `rw … ; positivity` for the algebra step) (lines 35-54); the file is built
   by the project's CI (`lake build` in `.github/workflows/push-main.yaml`).
2. The parent closes from the two bounds alone: `h3 : ∀ i, b i = 2` by
   `apply eq_of_le_of_ge` from `h2` and `h1` (lines 55-59), and the goal by the
   same `eq_of_le_of_ge` plus rewriting (lines 60-63).
3. The two chains are 20 of the 36 lines of the proof body, so the bounding
   argument is the bulk of the proof (count of the copied file, lines 28-63).
4. The author states the proof follows a human solution rather than an
   automated search: "The solution was adapted from here:
   https://www.youtube.com/watch?v=PNFh789P31E." (line 31).

In my opinion the detail worth copying is that `h2` is the exact mirror of `h1`
— only `m`/`hm` versus `M`/`hM` and `≥` versus `≤` differ — so the bounding
argument is written once and instantiated twice, and the antisymmetry close is
uniform too.

## When to use it, and when not

Use it when a goal reduces to pinning a quantity between a lower and an upper
bound, each reachable by a short monotonicity step (`gcongr` on the min/max or
on known ≤/≥ facts) followed by an exact algebra step (`rw` to a numeral plus
`positivity`). The two bounds being symmetric lets one chain template serve
both, and the enclosing proof closes them by antisymmetry. Avoid it when a link
is not monotone in its arguments (so `gcongr` cannot close it), when a link
needs its own substantial proof (state it as a separate lemma instead), when
the chain is long with each link a real lemma, or when the bounds are strict
and the exactness of the constant matters.

## Consequences

Each chain creates one obligation per link; transitivity of `≥`/`≤` is
discharged by the chain itself (Lean's `calc` composes `≥` as well as `≤`).
Every link must stay a one-tactic block: the monotonicity link depends on
`gcongr` finding the right ≤/≥ facts from `hm`/`hM`, and the algebra link
depends on `positivity [ha i]`, i.e. on `a i > 0`. The final close needs both
directions — a lower bound `b m ≥ 2` and an upper bound `b M ≤ 2` — because
`eq_of_le_of_ge` (antisymmetry) will not fire with only one side.

## Verification

<!-- verification:start -->
Status: **verified**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push-main.yaml runs lake build on push to main; pinned commit 1745e6ced3e671bd74417548494b034eb2c87da8 is HEAD of main (compare identical) | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 1745e6ced3e671bd74417548494b034eb2c87da8 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Copied file Compfiles/Egmo2023P1.lean (byte-identical to pinned commit): h1 lines 35-44 = calc b m with two links (_ ≥ (a m+a m)/(a m) via rw[hb m];gcongr, _ ≥ 2 via rw[←two_mul,mul_div_cancel_right₀];positivity[ha m]); h2 lines 45-54 = calc b M with two links (≤). No auxiliary lemma. | verifier |
| 2 | verified | Copied file lines 55-59: have h3 : ∀ i, b i = 2 by apply eq_of_le_of_ge with le_trans h2 (upper) and le_trans h1 (lower); lines 60-63: intro i j, apply eq_of_le_of_ge, rw [h i j, h3 i, h3 j] and rw [h j i, h3 j, h3 i]. | verifier |
| 3 | verified | Copied file: proof body lines 28-63 = 36 lines (63-28+1); calc chains lines 35-44 (10) and 45-54 (10) = 20 lines. | verifier |
| 4 | verified | Copied file line 31 is exactly the comment '-- The solution was adapted from here: https://www.youtube.com/watch?v=PNFh789P31E.' (line 32 is the indexing note). Quote is verbatim. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | object | Decomposition matches the code and closes: parent egmo2023_p1 fixes min m / max M (lines 33-34), children h1 (lines 35-44) and h2 (lines 45-54) are two-link calc chains bounding b m >= 2 and b M <= 2, and the proof closes via h3 (eq_of_le_of_ge, lines 55-59) then the goal (lines 60-63); provenance passes (byte-identical at 1745e6c) and CI push-main.yaml runs lake build. However the children's closed_by fields misdescribe the gcongr subgoals. In h1 the first gcongr goal is the denominator-positivity 0 <= a m, closed by le_of_lt (ha m) (from ha, not hm) - the entry writes 'a m <= a m ... from hm'. In h2 the corresponding 0 <= a M goal (le_of_lt (ha M)) is omitted entirely. Fix: correct the parentheticals to '0 <= a m (le_of_lt (ha m)), a m <= a (m-1), a m <= a (m+1) from hm' and '0 <= a M (le_of_lt (ha M)), a (M-1) <= a M, a (M+1) <= a M from hM'. | reviewer-correctness |
| generality | accept | Generality holds. The move is stated beyond the example: applicability.goal_shape abstracts the domain to 'an inequality E >= c or E <= c over an ordered ring', the expression to 'a ratio or sum', and the closing tactics to 'rewriting plus positivity/norm_num' (entry.json:90-91), and use_when factors the pattern into a monotonicity link (gcongr) + an algebra link (rw/positivity) + an antisymmetry close (entry.json:92) — a reusable 'bound a derived quantity at min/max, then eq_of_le_of_ge' template, not EGMO-specific. Consequences are honest and specific: one obligation per link; transitivity discharged by calc itself; the monotonicity link needs gcongr to find hm/hM facts and the algebra link needs a i > 0 for positivity [ha i]; the close needs BOTH directions because eq_of_le_of_ge won't fire with one side (entry.json:128; README:152-160). When-not-to-use is largely specific (non-monotone link; link needing its own lemma; long chains of real lemmas). Minor imprecision only: the clause 'the bounds are strict (<) and the exactness of the constant matters' (entry.json:93) is loosely worded — it does not harm the move's general statement (the antisymmetry close genuinely requires non-strict >= / <= bounds), but could be sharpened to say 'the close needs non-strict bounds; strict-only bounds cannot feed eq_of_le_of_ge'. Not a standing objection. | reviewer-generality |
| provenance-licence | accept | check_provenance passes: 1 file byte-identical at pinned commit 1745e6ced3e671bd74417548494b034eb2c87da8. Commit is consistent across entry.json, README.md, sources/compfiles/source.json and SOURCE.md (all 1745e6ced3e6). Licence Apache-2.0 is recorded in entry.json, README, source.json and SOURCE.md, matches the file header 'Released under Apache 2.0 license' and the copied upstream-LICENSE (Apache License Version 2.0). Permalinks all point to the same pinned commit and correct line anchors (L28-63 parent, L35-44 h1, L45-54 h2, L55-63 h3), matching the byte-identical copied file. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/dwrensha/compfiles at commit `1745e6ced3e671bd74417548494b034eb2c87da8`, under `Apache-2.0`; see the [source note](../../sources/compfiles/SOURCE.md) for the licence text and attribution.
