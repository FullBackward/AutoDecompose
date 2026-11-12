# Three-way membership split proves a cut yields valid triangles (IMO 2026 Q4)

| | |
|---|---|
| Kind | instance |
| Move | case-split |
| Language | lean |
| Status | draft |
| Source | [axiom-imo2026](../../sources/axiom-imo2026/SOURCE.md) at `c5a6a089d06d` |
| Licence | `MIT` |

## Intent

`cut_preserves` shows that an admissible cut of a valid triangle produces two
valid triangles. The proof reduces the goal `IsTriangle L ∧ IsTriangle R` to six
elementary goals by unfolding each side's positivity conjunct
`∀ y ∈ {a, b, c}, 0 < y` into a three-way disjunction via `mem_triple` and
splitting it with `rcases hy with h | h | h`, so every branch closes from the
cut's interval bounds alone.

## The decomposition

### parent `cut_preserves`: [`IMO2026/Q4/solution.lean` lines 61-90](https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q4/solution.lean#L61-L90) ([local copy](code/IMO2026/Q4/solution.lean))

```lean
/-- **Lemma 2 (cut preserves validity).** An admissible cut of a valid triangle yields
two valid triangles. -/
theorem cut_preserves {s L R : Multiset ℝ} (hs : IsTriangle s) (hcut : IsCut s L R) :
    IsTriangle L ∧ IsTriangle R := by
  obtain ⟨α, β, γ, x, hs_eq, hγx, hxβ, hL, hR⟩ := hcut
  obtain ⟨hcard, hpos, hsum⟩ := hs
  rw [hs_eq] at hpos hsum
  rw [sum_triple] at hsum
  have hα : 0 < α := hpos α (by rw [mem_triple]; tauto)
  have hβ : 0 < β := hpos β (by rw [mem_triple]; tauto)
  have hγ : 0 < γ := hpos γ (by rw [mem_triple]; tauto)
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · rw [hL]; exact card_triple _ _ _
    · intro y hy
      rw [hL, mem_triple] at hy
      rcases hy with h | h | h
      · rw [h]; exact hβ
      · rw [h]; linarith
      · rw [h]; linarith
    · rw [hL, sum_triple]; ring
  · refine ⟨?_, ?_, ?_⟩
    · rw [hR]; exact card_triple _ _ _
    · intro y hy
      rw [hR, mem_triple] at hy
      rcases hy with h | h | h
      · rw [h]; exact hγ
      · rw [h]; linarith
      · rw [h]; linarith
    · rw [hR, sum_triple]; ring
```

### context `IsTriangle`: [`IMO2026/Q4/solution.lean` lines 5-8](https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q4/solution.lean#L5-L8) ([local copy](code/IMO2026/Q4/solution.lean))

```lean
/-- A triangle, viewed as the multiset of its three interior angles (in degrees):
positive reals summing to `180`. -/
def IsTriangle (s : Multiset ℝ) : Prop :=
  s.card = 3 ∧ (∀ x ∈ s, 0 < x) ∧ s.sum = 180
```

### context `IsCut`: [`IMO2026/Q4/solution.lean` lines 13-23](https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q4/solution.lean#L13-L23) ([local copy](code/IMO2026/Q4/solution.lean))

```lean
/-- One admissible cut of the triangle `s`, producing children `L` and `R`.

We pick an apex angle `α` and the two base angles `β, γ` (so `s = {α, β, γ}`), and a
cut parameter `x` in the open interval `(γ, 180 - β)`. The resulting two triangles
have angle multisets `L = {β, x, 180 - β - x}` and `R = {γ, 180 - x, x - γ}`.
Ranging over all `α, β, γ` with `s = {α, β, γ}` captures all three apex choices and
both assignments of the two base angles. -/
def IsCut (s L R : Multiset ℝ) : Prop :=
  ∃ α β γ x : ℝ,
    s = {α, β, γ} ∧ γ < x ∧ x < 180 - β ∧
      L = {β, x, 180 - β - x} ∧ R = {γ, 180 - x, x - γ}
```

### context `mem_triple`: [`IMO2026/Q4/solution.lean` lines 47-50](https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q4/solution.lean#L47-L50) ([local copy](code/IMO2026/Q4/solution.lean))

```lean
/-- Membership in the three-element multiset `{a, b, c}`. -/
theorem mem_triple {a b c y : ℝ} :
    y ∈ ({a, b, c} : Multiset ℝ) ↔ y = a ∨ y = b ∨ y = c := by
  simp [Multiset.insert_eq_cons]
```

How the parts fit. The parent is a conjunction, split by `constructor` into
`IsTriangle L` and `IsTriangle R`. Each side is a three-way conjunction
(`s.card = 3 ∧ (∀ x ∈ s, 0 < x) ∧ s.sum = 180`, see `IsTriangle`), split by
`refine ⟨?_, ?_, ?_⟩`. The card conjunct closes by `card_triple` and the sum
conjunct by `sum_triple` + `ring`. The positivity conjunct is the interesting
one: after `rw [hL, mem_triple]` (or `hR`), the hypothesis `hy : y ∈ {β, x, 180 -
β - x}` becomes `hy : y = β ∨ y = x ∨ y = 180 - β - x`, and `rcases hy with h | h
| h` produces one goal per element. The first branch (`y = β`) closes by the
already-derived positivity `hβ`; the other two close by `linarith`, which
derives `0 < x` from `γ < x` and `0 < γ`, and `0 < 180 - β - x` from
`x < 180 - β` (both interval bounds come from destructuring `IsCut` at the top
of the proof). The `R` side is identical, with `hγ` for the first branch and
`linarith` from the same interval bounds for the other two.

## Why it is good

1. The parent closes from its six case-split branches plus the card and sum
   conjuncts, with no auxiliary lemma stated: `constructor`, two `refine
   ⟨?_, ?_, ?_⟩`, and two `rcases hy with h | h | h` where each branch closes by
   `exact hβ`/`exact hγ` or `linarith` (lines 63-90). *Evidence: check* — read of
   the copied file.
2. The file containing `cut_preserves` is verified: `formalization.yaml` records
   `TriangleGame.main_theorem` as `proved` with `sorry_count: 0`, and the README
   documents `verify.py` (Axle `verify_proof`) returning `Q4: okay=True (passed)`.
   *Evidence: check* — `formalization.yaml` lines 73-77 and 301-304, README lines
   40-51.
3. The authors state the intent in the doc comment: "Lemma 2 (cut preserves
   validity). An admissible cut of a valid triangle yields two valid triangles."
   (lines 61-62). *Evidence: author-statement* — the comment quoted with its
   location.
4. The same `mem_triple`-then-`rcases ... with h | h | h` membership split is
   reused elsewhere in the file — `safe_child` (lines 394-398) and
   `equilateral_counterexample` (lines 452, 456-457) — so the move is a recurring
   pattern, not a one-off. *Evidence: known-use* — the two further sites.

In my opinion the detail worth copying is the pairing of an iff-lemma
(`mem_triple`) with a plain `rcases`: the exhaustiveness of the split is carried
by the lemma's `↔`, so the case analysis needs no separate disjunction child.

## When to use it, and when not

Use it when the goal is a finitely-bounded positivity or normality property over
a small, fixed multiset or list, membership unfolds to a finite disjunction via
an iff-lemma (`mem_triple`), and each element's property is either already a
hypothesis or follows from interval bounds by `linarith`. Avoid it when the
multiset is large or only described by a general predicate (the split becomes
huge or impossible), when the disjunction `y = a ∨ ... ∨ y = c` needs its own
proof (then state that disjunction as a separate child before splitting), or
when the branches need genuinely different arguments, in which case a uniform
`rcases` will not close them.

## Consequences

The move creates one goal per element of the multiset (six here: three for `L`,
three for `R`). Exhaustiveness is free only because `mem_triple` is an iff that
already unfolds membership to the full disjunction; without such a lemma the
writer must first prove `y = a ∨ y = b ∨ y = c`. Each branch must substitute the
element it landed on (`rw [h]`) before the known bounds apply. The `linarith`
branches depend on the cut's interval hypotheses `γ < x` and `x < 180 - β`
(destructured from `IsCut`) and the derived positivity `hβ`/`hγ`; if those are
not in scope, or the multiset is not exactly three elements, the branches will
not close.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | not-run | No GitHub CI workflow builds this file: list_files.py at commit c5a6a089d06d shows no .github/workflows/ directory; verification is via the external Axle verify_proof service invoked by verify.py, documented in README.md, not a CI build on the default branch. | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read copied code/IMO2026/Q4/solution.lean lines 63-90 (byte-identical at c5a6a089d06d per provenance): constructor (L72) yields IsTriangle L and R; two refine ⟨?_,?_,?_⟩ (L73,L82); card closed by card_triple (L74,L83); positivity closed by rcases hy with h | h | h (L77,L86) with branches rw[h];exact hβ/hγ and two linarith; sum closed by sum_triple + ring (L81,L90). | verifier |
| 2 | verified | Fetched formalization.yaml at c5a6a089d06d: L74-76 declaration TriangleGame.main_theorem, file IMO2026/Q4/solution.lean, sorry_count: 0; L301-304 source 'IMO 2026 Problem 4' lean TriangleGame.main_theorem status: proved. Fetched README.md L43-51: verify.py (Axle verify_proof) output includes 'Q4: okay=True (passed)'. | verifier |
| 3 | verified | Read copied code/IMO2026/Q4/solution.lean lines 61-62: doc comment '/-- **Lemma 2 (cut preserves validity).** An admissible cut of a valid triangle yields / two valid triangles. -/' verbatim as claimed. | verifier |
| 4 | verified | Read copied code/IMO2026/Q4/solution.lean: safe_child L394-396 rw [hL, mem_triple] at haLmem; rw [hR, mem_triple] at haRmem; rcases haLmem with h | h | h (and L398 all_goals rcases haRmem with h' | h' | h'); equilateral_counterexample L452 rw [he, mem_triple] at hy; rcases hy with h | h | h; L456-457 rw [he, mem_triple] at ha; rcases ha with h | h | h. Same mem_triple-then-rcases h|h|h pattern in all three sites. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Read copied code/IMO2026/Q4/solution.lean (provenance pass, byte-identical at c5a6a089d06d). Parent cut_preserves (L63-90) matches entry: constructor (L72) then two refine <_,_,_> (L73,L82) split IsTriangle L/R into card, positivity, sum; card closed by card_triple (L74,L83), sum by sum_triple+ring (L81,L90), positivity by intro y hy; rw [hL/hR, mem_triple] at hy; rcases hy with h|h|h (L77,L86). All six children match the code and their closing methods exactly: L y=beta -> rw[h];exact hbeta (L78), L y=x -> rw[h];linarith (L79, from gamma<x and 0<gamma), L y=180-beta-x -> rw[h];linarith (L80, from x<180-beta), R y=gamma -> rw[h];exact hgamma (L87), R y=180-x -> rw[h];linarith (L88, from x<180-beta and 0<beta), R y=x-gamma -> rw[h];linarith (L89, from gamma<x). Each linarith branch's needed bound is in scope from the IsCut/hcut destructure (L65) and derived hbeta/hgamma (L70-71); every branch closes. Metrics verified: 28 lines, 6 branches, 4 linarith, 2 hypothesis, 0 aux lemmas. Card/sum conjuncts are non-case-split structural closings correctly excluded from the children list. | reviewer-correctness |
| generality | accept | Move is stated beyond the example: applicability/use_when frame it as '∀ y ∈ {a,b,c}, P y over a small fixed multiset/list, membership rewritten by an iff-lemma to a finite disjunction y=a∨y=b∨y=c, split with rcases h with h|h|h', not tied to the triangle specifics; the iff-lemma pairing (mem_triple) is named as the generality carrier. 'When not to use' is specific and honest: large/unbounded multiset (split huge/impossible), disjunction needing its own proof (state as separate child), non-uniform branches (uniform rcases won't close). Consequences are honest: one goal per element (6), exhaustiveness free only because mem_triple is an iff (else prove the disjunction first), each branch must rw[h] before bounds apply, and linarith branches depend on IsCut interval hypotheses hγx/hxβ plus hβ/hγ being in scope. Verified against local code: mem_triple is an iff (L48-50), pattern recurs at L394-398 and L452/456-457 supporting generality. | reviewer-generality |
| provenance-licence | accept | check_provenance passes (1 file byte-identical at c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2); entry.json sha256/bytes match the local copy; permalinks, entry.json source, source.json and SOURCE.md all pin the same commit; licence MIT recorded consistently in entry.json/source.json/README/SOURCE.md and upstream-LICENSE is the MIT text; site line ranges (5-8, 13-23, 47-50, 61-90) match the copied solution.lean. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/AxiomMath/IMO2026 at commit `c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2`, under `MIT`; see the [source note](../../sources/axiom-imo2026/SOURCE.md) for the licence text and attribution.
