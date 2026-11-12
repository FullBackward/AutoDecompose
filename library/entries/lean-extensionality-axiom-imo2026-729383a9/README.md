# Extensionality of prime-factor sets for Mval move-invariance (IMO 2026 Q1)

| | |
|---|---|
| Kind | instance |
| Move | extensionality |
| Language | lean |
| Status | draft |
| Source | [axiom-imo2026](../../sources/axiom-imo2026/SOURCE.md) at `c5a6a089d06d` |
| Licence | `MIT` |

## Intent

Prove the invariant `Mval B = Mval B'` for a single move `B → B'`, where
`Mval B = ∏ p ∈ B.prod.primeFactors, p ^ gExp p B`. The proof first shows the two
index finsets `B.prod.primeFactors` and `B'.prod.primeFactors` are equal by
extensionality (`ext p`), then matches the two products termwise with
`Finset.prod_congr`, which reduces the goal to the stated invariant `gExp_move`.

## The decomposition

### parent `Mval_move`: [`IMO2026/Q1/solution.lean` lines 329-343](https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q1/solution.lean#L329-L343) ([local copy](code/IMO2026/Q1/solution.lean))

```lean
/-- `Mval` is invariant under a single move (both boards positive). -/
theorem Mval_move {B B' : Board} (h : Move B B')
    (hB : ∀ a ∈ B, 0 < a) (hB' : ∀ a ∈ B', 0 < a) : Mval B = Mval B' := by
  have hset : B.prod.primeFactors = B'.prod.primeFactors := by
    ext p
    rw [mem_primeFactors_iff_gExp hB, mem_primeFactors_iff_gExp hB']
    constructor
    · rintro ⟨hp, hg⟩; exact ⟨hp, by rw [← gExp_move hp h]; exact hg⟩
    · rintro ⟨hp, hg⟩; exact ⟨hp, by rw [gExp_move hp h]; exact hg⟩
  unfold Mval
  rw [hset]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := (Nat.mem_primeFactors_of_ne_zero (prod_ne_zero hB')).mp hp |>.1
  rw [gExp_move hpp h]
```

### child `hset`: [`IMO2026/Q1/solution.lean` lines 332-337](https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q1/solution.lean#L332-L337) ([local copy](code/IMO2026/Q1/solution.lean))

```lean
  have hset : B.prod.primeFactors = B'.prod.primeFactors := by
    ext p
    rw [mem_primeFactors_iff_gExp hB, mem_primeFactors_iff_gExp hB']
    constructor
    · rintro ⟨hp, hg⟩; exact ⟨hp, by rw [← gExp_move hp h]; exact hg⟩
    · rintro ⟨hp, hg⟩; exact ⟨hp, by rw [gExp_move hp h]; exact hg⟩
```

### child `Mval_termwise`: [`IMO2026/Q1/solution.lean` lines 338-343](https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q1/solution.lean#L338-L343) ([local copy](code/IMO2026/Q1/solution.lean))

```lean
  unfold Mval
  rw [hset]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := (Nat.mem_primeFactors_of_ne_zero (prod_ne_zero hB')).mp hp |>.1
  rw [gExp_move hpp h]
```

How the parts fit. The parent `Mval_move` splits into two obligations. The
first, the named `have hset : B.prod.primeFactors = B'.prod.primeFactors`, is a
finset equality: `ext p` turns it into the pointwise membership equivalence
`p ∈ B.prod.primeFactors ↔ p ∈ B'.prod.primeFactors`, and rewriting both sides
with `mem_primeFactors_iff_gExp` reduces it to
`(p.Prime ∧ gExp p B ≠ 0) ↔ (p.Prime ∧ gExp p B' ≠ 0)`. `constructor` splits
the iff, and each direction closes with `gExp_move hp h`, the key invariant
that a move preserves `gExp p`.

The second obligation is the main goal. After `unfold Mval; rw [hset]` the goal
is a product over the single finset `B'.prod.primeFactors`,
`∏ p ∈ B'.prod.primeFactors, p ^ gExp p B = ∏ p ∈ B'.prod.primeFactors, p ^ gExp p B'`.
`Finset.prod_congr rfl` reduces it to a per-`p` term equality; `intro p hp`
introduces the index, `hpp : p.Prime` is recovered from `hp`, and
`rw [gExp_move hpp h]` closes the term. So both children ultimately rest on the
single fact `gExp_move`, and the extensionality move `ext p` is what lets the
two index sets be identified before the product is compared.

## Why it is good

1. The parent `Mval_move` closes in 14 lines (330-343) from its two children:
   the finset equality `hset` (by `ext p` and `gExp_move`) and the termwise
   product equality (by `Finset.prod_congr` and `gExp_move`) (`check`; lines
   330-343).
2. The copied file `IMO2026/Q1/solution.lean` contains no `sorry`, `axiom`,
   `admit` or `Admitted` (grep of the local copy), and the project's
   `formalization.yaml` records `sorry_count: 0` for the solutions
   (`check`; `formalization.yaml` line 30).
3. The authors label `gExp` the "key invariant" — "a single move preserves
   `gExp p`, for any prime `p`" (line 85) — and state the membership
   characterisation that makes the `ext` step work: "the primes dividing the
   product are exactly the primes with a nonzero valuation gcd" (lines
   301-302) (`author-statement`).
4. The extensionality step is one line (`ext p`, line 333), and both directions
   of the resulting membership equivalence close in one line each (336-337);
   the product-congruence step is 6 lines (338-343) (`measurement`).

In my opinion the detail worth copying is the two-stage reduction: the finset
is identified by extensionality *before* the product is compared, so the
`prod_congr` step only has to compare terms over one index set. This is what
keeps both obligations trivial given `gExp_move`.

## When to use it, and when not

Use it when the goal is an equality of products (or sums) whose index set
depends on the state, and both of these hold: the index sets can be identified
by a shared membership characterisation (so `ext` reduces to an iff you already
have), and the summed quantity is invariant under the step. It also applies
directly to set/function equalities, where `ext` gives the pointwise goal.

Avoid it when the index-set equality is not literally true (a bijection or a
cardinality-preserving map is not enough for `rw [hset]`), when the membership
characterisation is itself the hard part, or when the summed term depends on
the index set in a way a pointwise invariant does not cover.

## Consequences

`ext p` on a finset equality creates a two-way membership obligation (an iff);
here both directions close by the same `gExp_move`, but in general they may
need different arguments. The product step needs a plain equality of index
sets so that `rw [hset]` applies, and the summed function must be pointwise
invariant (`p ^ gExp p B = p ^ gExp p B'` at each `p`). A known failure mode is
reaching for `Finset.prod_congr` before the index sets are identified, which
leaves a goal over two different finsets that `prod_congr` cannot compare.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | not-run | No CI workflow present: list_files.py on axiom-imo2026 shows no .github/workflows and no *.yml; README documents lake build + verify.py (external Axle service), not a CI file | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read copied file IMO2026/Q1/solution.lean lines 330-343: theorem Mval_move (330-331), have hset (332-337) via ext p / mem_primeFactors_iff_gExp / constructor / gExp_move, then unfold Mval; rw [hset]; apply Finset.prod_congr rfl; intro p hp; rw [gExp_move hpp h] (338-343) closes the parent | verifier |
| 2 | verified | grep -nE 'sorry|axiom|admit|Admitted' on copied solution.lean returned no match; fetched formalization.yaml (cache/axiom-imo2026/files/formalization.yaml) line 30 reads 'sorry_count: 0' | verifier |
| 3 | verified | Read copied file line 85: '/-- The key invariant: a single move preserves gExp p, for any prime p. -/' and lines 301-302: '/-- For a board with positive entries, the primes dividing the product are exactly the primes with a nonzero valuation gcd. -/' | verifier |
| 4 | verified | Read copied file: line 333 is 'ext p' (one line); lines 336-337 are the two rintro/exact directions (one line each); lines 338-343 (unfold Mval, rw [hset], apply Finset.prod_congr rfl, intro p hp, have hpp, rw [gExp_move hpp h]) are 6 lines | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Read code/IMO2026/Q1/solution.lean in full. Parent Mval_move (L330-331) matches entry.json parent statement exactly. Child hset (L332) states B.prod.primeFactors = B'.prod.primeFactors, closed by ext p (333), rw [mem_primeFactors_iff_gExp hB, mem_primeFactors_iff_gExp hB'] (334), constructor (335), both directions by gExp_move hp h (336-337). Child Mval_termwise is the main goal after unfold Mval (338)+rw [hset] (339), giving the stated termwise product equality, closed by apply Finset.prod_congr rfl (340), intro p hp (341), recover hpp:p.Prime (342), rw [gExp_move hpp h] (343). Children and closing methods match the code exactly, and the proof closes (each direction rewrites by the correct orientation of gExp_move). No discrepancy found. | reviewer-correctness |
| generality | accept | Generality: the move is stated in portable terms (equality of a product/sum whose index finset depends on the state, closed by (1) identifying the index sets via ext + a shared membership characterisation, then (2) termwise prod_congr), and the two preconditions are named (a shared iff the ext step reduces to, and pointwise invariance of the summed term). 'When not to use' is specific and honest: rw [hset] needs literal equality so a bijection or cardinality-preserving map is insufficient; the membership characterisation being the hard part; and a summed term depending on the index set beyond the index variable. Consequences are accurate against the copied code: ext p creates an iff obligation (lines 333-337, closed here by the same gExp_move but noting they may differ in general), the product step needs a plain equality for rw [hset] (line 339), and the named failure mode (prod_congr before the index sets are identified leaves a goal over two finsets) matches Lean semantics. No overreach found: the prose correctly scopes the valuable part as the two-stage reduction rather than extensionality itself. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit and licence all consistent. entry.json/README/SOURCE.md/source.json agree on commit c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2 and licence MIT; upstream-LICENSE is the MIT text. check_provenance passes (1 file byte-identical at pinned commit); local code/IMO2026/Q1/solution.lean sha256 d9d7519d... matches entry.json and is 23769 bytes. Permalink line ranges correct against copied file (Mval_move L329-343, hset L332-337, Mval_termwise L338-343; ext p at L333). Source note correctly states code copied verbatim under MIT. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/AxiomMath/IMO2026 at commit `c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2`, under `MIT`; see the [source note](../../sources/axiom-imo2026/SOURCE.md) for the licence text and attribution.
