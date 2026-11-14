# Iff-split of IMO 1959 P2(a): IsGood x (sqrt 2) iff x in [1/2, 1]

| | |
|---|---|
| Kind | instance |
| Move | iff-split |
| Language | lean |
| Status | accepted |
| Source | [compfiles](../../sources/compfiles/SOURCE.md) at `1745e6ced3e6` |
| Licence | `Apache-2.0` |

## Intent

Part (a) of IMO 1959 P2 asks for the real `x` with `IsGood x (sqrt 2)`. The
answer is the interval `[1/2, 1]`, stated as an iff `IsGood x (sqrt 2) ↔
x ∈ solution_set_sqrt2` and proved by splitting it into its two directions with
`refine ⟨_, _⟩`. Both directions were already packaged as named lemmas, so the
3-line glue is pure assembly: the forward direction cites `IsGood.one_half_le`
(lower bound) and `IsGood.sqrt_two_lt_of_one_lt` (upper bound), and the reverse
direction cites `isGood_iff_eq_sqrt_two`.

## The decomposition

### parent `imo1959_p2a`: [`Compfiles/Imo1959P2.lean` lines 123-125](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Imo1959P2.lean#L123-L125) ([local copy](code/Compfiles/Imo1959P2.lean))

```lean
problem imo1959_p2a : IsGood x (sqrt 2) ↔ x ∈ solution_set_sqrt2 := by
  refine ⟨fun h ↦ ?_, fun h ↦ (isGood_iff_eq_sqrt_two h).2 rfl⟩
  exact ⟨h.one_half_le, not_lt.1 fun h₁ ↦ (h.sqrt_two_lt_of_one_lt h₁).false⟩
```

### child `IsGood.one_half_le`: [`Compfiles/Imo1959P2.lean` lines 71-71](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Imo1959P2.lean#L71-L71) ([local copy](code/Compfiles/Imo1959P2.lean))

```lean
theorem IsGood.one_half_le (h : IsGood x A) : 1 / 2 ≤ x := (isGood_iff.1 h).2
```

### child `isGood_iff_eq_sqrt_two`: [`Compfiles/Imo1959P2.lean` lines 76-81](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Imo1959P2.lean#L76-L81) ([local copy](code/Compfiles/Imo1959P2.lean))

```lean
theorem isGood_iff_eq_sqrt_two (hx : x ∈ Icc (1 / 2) 1) : IsGood x A ↔ A = sqrt 2 := by
  have : sqrt (2 * x - 1) ≤ 1 := sqrt_two_mul_sub_one_le_one.2 hx.2
  simp only [isGood_iff, hx.1, abs_sub_comm _ (1 : ℝ), abs_of_nonneg (sub_nonneg.2 this), and_true]
  suffices 2 = A * sqrt 2 ↔ A = sqrt 2 by convert this using 2; ring
  rw [← div_eq_iff, div_sqrt, eq_comm]
  positivity
```

### child `IsGood.sqrt_two_lt_of_one_lt`: [`Compfiles/Imo1959P2.lean` lines 91-94](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Imo1959P2.lean#L91-L94) ([local copy](code/Compfiles/Imo1959P2.lean))

```lean
theorem IsGood.sqrt_two_lt_of_one_lt (h : IsGood x A) (hx : 1 < x) : sqrt 2 < A := by
  rw [(isGood_iff_eq_sqrt hx).1 h]
  refine sqrt_lt_sqrt zero_le_two ?_
  linarith
```

### context `IsGood`: [`Compfiles/Imo1959P2.lean` lines 38-40](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Imo1959P2.lean#L38-L40) ([local copy](code/Compfiles/Imo1959P2.lean))

```lean
def IsGood (x A : ℝ) : Prop :=
  sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) = A ∧ 0 ≤ 2 * x - 1 ∧
    0 ≤ x + sqrt (2 * x - 1) ∧ 0 ≤ x - sqrt (2 * x - 1)
```

### context `isGood_iff`: [`Compfiles/Imo1959P2.lean` lines 54-69](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Imo1959P2.lean#L54-L69) ([local copy](code/Compfiles/Imo1959P2.lean))

```lean
theorem isGood_iff : IsGood x A ↔
    sqrt (2 * x - 1) + 1 + |sqrt (2 * x - 1) - 1| = A * sqrt 2 ∧ 1 / 2 ≤ x := by
  cases le_or_gt (1 / 2) x with
  | inl hx =>
    have hx' : 0 ≤ 2 * x - 1 := by linarith
    have h₁ : x + sqrt (2 * x - 1) = (sqrt (2 * x - 1) + 1) ^ 2 / 2 := by
      rw [add_sq, sq_sqrt hx']; field_simp; ring
    have h₂ : x - sqrt (2 * x - 1) = (sqrt (2 * x - 1) - 1) ^ 2 / 2 := by
      rw [sub_sq, sq_sqrt hx']; field_simp; ring
    simp only [IsGood, *, div_nonneg (sq_nonneg _) (zero_le_two (α := ℝ)), sqrt_div (sq_nonneg _),
      and_true]
    rw [sqrt_sq, sqrt_sq_eq_abs] <;> [skip; positivity]
    field_simp
  | inr hx =>
    have : 2 * x - 1 < 0 := by linarith
    simp only [IsGood, this.not_ge, hx.not_ge]; simp
```

### context `sqrt_two_mul_sub_one_le_one`: [`Compfiles/Imo1959P2.lean` lines 73-74](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Imo1959P2.lean#L73-L74) ([local copy](code/Compfiles/Imo1959P2.lean))

```lean
theorem sqrt_two_mul_sub_one_le_one : sqrt (2 * x - 1) ≤ 1 ↔ x ≤ 1 := by
  simp [sqrt_le_iff, ← two_mul]
```

### context `isGood_iff_eq_sqrt`: [`Compfiles/Imo1959P2.lean` lines 83-89](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Imo1959P2.lean#L83-L89) ([local copy](code/Compfiles/Imo1959P2.lean))

```lean
theorem isGood_iff_eq_sqrt (hx : 1 < x) : IsGood x A ↔ A = sqrt (4 * x - 2) := by
  have h₁ : 1 < sqrt (2 * x - 1) := by simpa only [← not_le, sqrt_two_mul_sub_one_le_one] using hx
  have h₂ : 1 / 2 ≤ x := by linarith
  simp only [isGood_iff, h₂, abs_of_pos (sub_pos.2 h₁), add_add_sub_cancel, and_true]
  rw [← mul_two, ← div_eq_iff (by positivity), mul_div_assoc, div_sqrt, ← sqrt_mul' _ zero_le_two,
    eq_comm]
  ring_nf
```

### context `solution_set_sqrt2`: [`Compfiles/Imo1959P2.lean` lines 121-121](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Imo1959P2.lean#L121-L121) ([local copy](code/Compfiles/Imo1959P2.lean))

```lean
determine solution_set_sqrt2 : Set ℝ := Icc (1 / 2) 1
```

How the parts fit. The parent `imo1959_p2a` states the answer as an iff, where
`solution_set_sqrt2` is `Icc (1 / 2) 1` (line 121). `refine ⟨fun h ↦ ?_, fun h ↦
...⟩` splits it into two directions, and each direction closes by citing a named
lemma already proved in the file:

- **Forward** `IsGood x (sqrt 2) → x ∈ Icc (1 / 2) 1` (line 125): membership in
  the interval is a pair of bounds, each of which is a lemma — `h.one_half_le`
  gives `1 / 2 ≤ x`, and `h.sqrt_two_lt_of_one_lt h₁` (under `not_lt.1`) refutes
  `1 < x`, giving `x ≤ 1`.
- **Reverse** `x ∈ Icc (1 / 2) 1 → IsGood x (sqrt 2)` (line 124):
  `isGood_iff_eq_sqrt_two h` turns `IsGood x A` into `A = sqrt 2`, and `rfl`
  closes `sqrt 2 = sqrt 2`.

Lemma graph (which lemma uses which):

```
imo1959_p2a (parent, lines 123-125)
├─ forward  ─ IsGood.one_half_le           (line 71)      ─ uses isGood_iff
│          ─ IsGood.sqrt_two_lt_of_one_lt  (lines 91-94)  ─ uses isGood_iff_eq_sqrt
└─ reverse ─ isGood_iff_eq_sqrt_two        (lines 76-81)  ─ uses isGood_iff, sqrt_two_mul_sub_one_le_one

below the children:
  isGood_iff_eq_sqrt          (lines 83-89)  ─ uses isGood_iff, sqrt_two_mul_sub_one_le_one
  sqrt_two_mul_sub_one_le_one (lines 73-74)  ─ simp only (a leaf)
  isGood_iff                  (lines 54-69)  ─ cases + simp/ring (a leaf)
```

Why each child is a good leaf — a self-contained statement whose proof closes on
its own or from named siblings:

- `IsGood.one_half_le` is a one-line consequence of `isGood_iff` with the
  self-contained statement `IsGood x A → 1 / 2 ≤ x`; its proof is the single
  term `(isGood_iff.1 h).2`.
- `IsGood.sqrt_two_lt_of_one_lt` closes from the named sibling
  `isGood_iff_eq_sqrt` (rewriting the hypothesis to `A = sqrt (4 * x - 2)`),
  then `sqrt_lt_sqrt` and `linarith`. It is what turns the upper bound into a
  single citation.
- `isGood_iff_eq_sqrt_two` closes from `isGood_iff` and
  `sqrt_two_mul_sub_one_le_one`, reducing `IsGood x A` to `A = sqrt 2` by a
  `suffices … convert … ring` and `positivity`.

All three proofs close without `sorry`; the depth-2/3 lemmas below them
(`isGood_iff_eq_sqrt`, `sqrt_two_mul_sub_one_le_one`, `isGood_iff`) likewise end
in `simp`/`ring`/`linarith`/`positivity`.

## Why it is good

1. The parent proof (lines 123-125) contains no `sorry`, `admit` or `axiom`
   token — the split closes by citing lemmas, not by holes (`check`,
   lines 123-125).
2. `isGood_iff_eq_sqrt_two` occurs in the parent site, closing the reverse
   direction (`check`, line 124).
3. `one_half_le` occurs in the parent site, giving the lower bound of the
   forward direction (`check`, line 125).
4. `sqrt_two_lt_of_one_lt` occurs in the parent site, giving the upper bound of
   the forward direction (`check`, line 125).
5. The theorem is assembled from 3 named lemmas in a 3-line glue, and the
   longest chain of project lemmas below it is 3 deep:
   `imo1959_p2a → IsGood.sqrt_two_lt_of_one_lt → isGood_iff_eq_sqrt →
   sqrt_two_mul_sub_one_le_one` (`measurement`, lines 71, 76-81, 91-94, 123-125,
   with the chain links at lines 125, 92 and 84).

In my opinion the detail worth copying is the *asymmetry* of the split: the
forward direction is a pair (lower bound + upper bound, two lemmas) while the
reverse direction is a single characterisation lemma, so the iff-split here is
not two mirror-image sub-proofs but an assembly of three pre-existing named
facts. This is the theorem-scale form of the move — a skeleton whose holes are
already-filled lemma names rather than inline sub-proofs.

## When to use it, and when not

Use it when both directions of an equivalence have already been stated as named
lemmas in the same file or project, so the split reduces to citing them — and
when the two directions want different lemmas (a construction for one, a
refutation-by-inequality for the other), which is what makes a single
`refine ⟨_, _⟩` read cleanly. Avoid it when the directions are not yet
lemma-sized and would need new arguments written inline — then the subgoals are
the real content and the entry is tactic-scale, not theorem-scale — or when one
direction is definitional or follows by symmetry, where the split buys nothing.

## Consequences

The split creates exactly two obligations, one per implication; here each is
closed by citing a named lemma, so the glue carries no new proof burden. The
forward direction must discharge two membership conditions (the lower and upper
bounds of the interval `Icc (1 / 2) 1`), which is why it cites two lemmas while
the reverse cites one. Failure mode: if those lemmas were not already available,
the 3-line glue would have to grow their sub-proofs inline, defeating the
theorem-scale assembly and turning the entry back into a tactic-scale split.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push-main.yaml runs 'lake build' (steps 'lake build' L49-56) on push to default branch main; pinned commit 1745e6ced3e671bd74417548494b034eb2c87da8 is HEAD of main (commits/main shows latest = 1745e6c). lake build compiles all Compfiles modules including Compfiles/Imo1959P2.lean. | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: IsGood.one_half_le@Compfiles/Imo1959P2.lean:125, isGood_iff_eq_sqrt_two@Compfiles/Imo1959P2.lean:124, IsGood.sqrt_two_lt_of_one_lt@Compfiles/Imo1959P2.lean:125; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 1745e6ced3e671bd74417548494b034eb2c87da8 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | no_sorry(Compfiles/Imo1959P2.lean, 123-125) -> no_sorry: none of sorry, admit, axiom in Compfiles/Imo1959P2.lean:123-125 | check_claims.py |
| 2 | verified | cites(parent, isGood_iff_eq_sqrt_two) -> cites: isGood_iff_eq_sqrt_two occurs at Compfiles/Imo1959P2.lean:124 | check_claims.py |
| 3 | verified | cites(parent, one_half_le) -> cites: one_half_le occurs at Compfiles/Imo1959P2.lean:125 | check_claims.py |
| 4 | verified | cites(parent, sqrt_two_lt_of_one_lt) -> cites: sqrt_two_lt_of_one_lt occurs at Compfiles/Imo1959P2.lean:125 | check_claims.py |
| 5 | verified | Read code/Compfiles/Imo1959P2.lean: IsGood.one_half_le at L71, isGood_iff_eq_sqrt_two at L76-81, IsGood.sqrt_two_lt_of_one_lt at L91-94; glue is L123-125 (3 lines). Chain imo1959_p2a -> sqrt_two_lt_of_one_lt (L125 cites h.sqrt_two_lt_of_one_lt) -> isGood_iff_eq_sqrt (L92 cites isGood_iff_eq_sqrt) -> sqrt_two_mul_sub_one_le_one (L84 cites it), which stops at the simp-only lemma L73-74. No longer chain: isGood_iff (L54-69) and sqrt_two_mul_sub_one_le_one cite no project lemma; the L96-118 lemmas are not cited by imo1959_p2a. Depth 3 confirmed. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent imo1959_p2a (lines 123-125) refines the iff into two directions; forward cites IsGood.one_half_le (lower bound) and IsGood.sqrt_two_lt_of_one_lt (upper bound via not_lt.1), reverse cites isGood_iff_eq_sqrt_two with rfl. All three children are exactly the lemmas the glue cites, their statements and closed_by strings match the copied code verbatim (lines 71, 76-81, 91-94). Shape numbers check out: direct_lemmas=3, glue_lines=3 (123-125), child_lines=[1,6,4] matching the three child site ranges, depth=3 via imo1959_p2a -> sqrt_two_lt_of_one_lt -> isGood_iff_eq_sqrt -> sqrt_two_mul_sub_one_le_one (lines 125, 92, 84; leaf at 73-74). Decomposition closes without sorry. | reviewer-correctness |
| generality | accept | Move stated beyond the example: entry.json applicability/use_when/avoid_when give a general goal_shape (P iff Q with Q a set membership and both directions already named lemmas), and README 'When to use it' states general conditions (both directions already lemma-sized; the two directions want different lemmas). When-not-to-use is honest and specific: three concrete avoid conditions (directions not lemma-sized so tactic-scale; one direction definitional or symmetric; same hypothesis reproved per direction). Consequences name the concrete failure mode: if the lemmas were absent the 3-line glue would inline their sub-proofs, defeating the theorem-scale assembly. Leaves: README 'Why each child is a good leaf' answers it -- each leaf is a self-contained statement whose proof closes on its own or from named siblings, with per-leaf closure (single term isGood_iff.1 h .2; rewrite plus sibling plus sqrt_lt_sqrt plus linarith; suffices convert ring plus positivity) and all close without sorry ending in simp/ring/linarith/positivity. Minor nit, not blocking: 'bounded prover' is not named literally, but the substance (self-contained leaf closing via a named sibling or small automation) is stated. Code at the cited line ranges matches the description. | reviewer-generality |
| provenance-licence | accept | check_provenance.py passes (1 file byte-identical at 1745e6ced3e671bd74417548494b034eb2c87da8). Commit, URL and licence (Apache-2.0) in entry.json match source.json and sources/compfiles/SOURCE.md; upstream-LICENSE is Apache-2.0 text. All 9 permalinks use the pinned commit and path Compfiles/Imo1959P2.lean; sed of the copied file confirms each cited line range (38-40, 54-69, 71, 73-74, 76-81, 83-89, 91-94, 121, 123-125) contains exactly the excerpt/statement claimed. Fully traceable and consistent. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/dwrensha/compfiles at commit `1745e6ced3e671bd74417548494b034eb2c87da8`, under `Apache-2.0`; see the [source note](../../sources/compfiles/SOURCE.md) for the licence text and attribution.
