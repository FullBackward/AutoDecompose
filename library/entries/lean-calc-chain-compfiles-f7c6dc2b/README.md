# Three-step calc chain over a product partition for USA 2020 P3

| | |
|---|---|
| Kind | instance |
| Move | calc-chain |
| Language | lean |
| Status | accepted |
| Source | [compfiles](../../sources/compfiles/SOURCE.md) at `1745e6ced3e6` |
| Licence | `Apache-2.0` |

## Intent

Reduce the goal `∏A = 2` (the product over `a : 1 ≤ a < p` with both `a` and
`4 − a` quadratic non-residues) to a three-step `calc` chain: rewrite `∏A`
through the partition `C = A ∪ B`, erase the element `2`, and re-index the
erased product onto `B`, then cancel the common non-zero factor `∏B`. Each of
the three links and the cancellation hypothesis is a named lemma proved earlier
in the same file.

## The decomposition

### parent `usa2020_p3`: [`Compfiles/Usa2020P3.lean` lines 138-148](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Usa2020P3.lean#L138-L148) ([local copy](code/Compfiles/Usa2020P3.lean))

```lean
problem usa2020_p3 (p : ℕ) [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    ∏ a ∈ Finset.univ.filter (fun (a : ZMod p) => a ≠ 0 ∧ ¬IsSquare a ∧ ¬IsSquare (4 - a)), a = (solution_val : ZMod p) := by
  apply mul_left_cancel₀ (prod_B_ne_zero p)
  calc (∏ b ∈ setB' p, b) * ∏ a ∈ setA' p, a
      = ∏ n ∈ setC' p, n := by
        rw [setC_eq_union p, Finset.prod_union (disjoint_AB p), mul_comm]
    _ = 2 * ∏ n ∈ (setC' p).erase 2, n :=
        (Finset.mul_prod_erase _ _ (two_mem_setC p hp2)).symm
    _ = (∏ b ∈ setB' p, b) * (solution_val : ZMod p) := by
        rw [prod_C_erase_eq_prod_B p hp2, mul_comm]
        norm_num [solution_val]
```

### child `setC_eq_union`: [`Compfiles/Usa2020P3.lean` lines 65-73](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Usa2020P3.lean#L65-L73) ([local copy](code/Compfiles/Usa2020P3.lean))

```lean
private lemma setC_eq_union : setC' p = setA' p ∪ setB' p := by
  ext a
  simp only [setA', setB', setC', Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases ha : a = 0
  · simp [ha]
  by_cases ha4 : a = 4
  · simp [ha4]
  · rw [isSquare_mul_iff_same p ha (sub_ne_zero_of_ne (Ne.symm ha4))]
    tauto
```

### child `disjoint_AB`: [`Compfiles/Usa2020P3.lean` lines 75-76](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Usa2020P3.lean#L75-L76) ([local copy](code/Compfiles/Usa2020P3.lean))

```lean
private lemma disjoint_AB : Disjoint (setA' p) (setB' p) :=
  Finset.disjoint_filter.mpr fun _ _ _ _ => by aesop
```

### child `two_mem_setC`: [`Compfiles/Usa2020P3.lean` lines 87-88](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Usa2020P3.lean#L87-L88) ([local copy](code/Compfiles/Usa2020P3.lean))

```lean
private lemma two_mem_setC : (2 : ZMod p) ∈ setC' p :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, p_two_ne_zero p hp2, p_two_ne_four p hp2, 2, by ring⟩
```

### child `prod_C_erase_eq_prod_B`: [`Compfiles/Usa2020P3.lean` lines 124-129](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Usa2020P3.lean#L124-L129) ([local copy](code/Compfiles/Usa2020P3.lean))

```lean
private lemma prod_C_erase_eq_prod_B :
    ∏ n ∈ (setC' p).erase 2, n = ∏ b ∈ setB' p, b := by
  rw [← Finset.prod_fiberwise_of_maps_to
    (fun n hn => map_mem_setB p (Finset.mem_of_mem_erase hn) (Finset.ne_of_mem_erase hn))
    (fun n => n)]
  exact Finset.prod_congr rfl fun _ hb => fiber_prod p hp2 hb
```

### child `prod_B_ne_zero`: [`Compfiles/Usa2020P3.lean` lines 131-132](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Usa2020P3.lean#L131-L132) ([local copy](code/Compfiles/Usa2020P3.lean))

```lean
private lemma prod_B_ne_zero : ∏ b ∈ setB' p, b ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hb => (Finset.mem_filter.mp hb).2.1
```

### context `definitions`: [`Compfiles/Usa2020P3.lean` lines 44-55](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Usa2020P3.lean#L44-L55) ([local copy](code/Compfiles/Usa2020P3.lean))

```lean
section

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2)

private abbrev setA' : Finset (ZMod p) :=
  Finset.univ.filter (fun a => a ≠ 0 ∧ ¬IsSquare a ∧ ¬IsSquare (4 - a))

private abbrev setB' : Finset (ZMod p) :=
  Finset.univ.filter (fun b => b ≠ 0 ∧ b ≠ 4 ∧ IsSquare b ∧ IsSquare (4 - b))

private abbrev setC' : Finset (ZMod p) :=
  Finset.univ.filter (fun n => n ≠ 0 ∧ n ≠ 4 ∧ IsSquare (n * (4 - n)))
```

How the parts fit. The glue first applies `mul_left_cancel₀ (prod_B_ne_zero p)`,
so the whole chain is an equality between products and the common factor `∏B`
never needs to be evaluated, only proved non-zero. Then a three-link `calc`
carries the argument; each link is closed by a `rw` naming the lemma(s) written
for it:

- Link 1 (`(∏B)·(∏A) = ∏C`): `setC_eq_union` rewrites `setC'` as `setA' ∪ setB'`,
  and `disjoint_AB` is exactly the hypothesis `Finset.prod_union` needs to split
  the product; `mul_comm` then puts the factors in the stated order.
- Link 2 (`∏C = 2 · ∏ C\{2}`): `two_mem_setC` is the membership hypothesis of
  `Finset.mul_prod_erase`, which factors out the erased element `2`.
- Link 3 (`2 · ∏ C\{2} = (∏B)·2`): `prod_C_erase_eq_prod_B` identifies the erased
  product with `∏B`, and `norm_num [solution_val]` finishes the constant `2`.

The lemma graph (which project lemma uses which), below the main theorem:

```
usa2020_p3 (138-148)
├── prod_B_ne_zero (131-132)                        leaf: prod_ne_zero_iff
├── setC_eq_union (65-73) ── isSquare_mul_iff_same (57-63)
├── disjoint_AB (75-76)                             leaf: aesop
├── two_mem_setC (87-88) ── p_two_ne_zero (79-80), p_two_ne_four (83-84)
│                            └─ p_two_ne_four ── p_two_ne_zero
└── prod_C_erase_eq_prod_B (124-129)
    ├── map_mem_setB (90-96)                        leaf
    └── fiber_prod (99-121) ── p_two_ne_zero (79-80)
```

Each of the five children is a good leaf — a self-contained statement whose proof
closes on its own or from named siblings:

- `setC_eq_union` is an extensionality + two `by_cases` case splits; the one hard
  fact (multiplicativity of the quadratic character) is a named sibling
  `isSquare_mul_iff_same`, so the partition lemma itself is just `tauto` after that
  rewrite.
- `disjoint_AB` closes in one line by `aesop` because `setA'` demands `¬IsSquare a`
  and `setB'` demands `IsSquare a`.
- `two_mem_setC` closes by `Finset.mem_filter` with witnesses `p_two_ne_zero` and
  `p_two_ne_four` (the "2 ≠ 0, 2 ≠ 4" facts, each a sibling) and `2` as the square
  root, `by ring`.
- `prod_C_erase_eq_prod_B` re-indexes with `Finset.prod_fiberwise_of_maps_to`; its
  two sub-facts — the map lands in `B` (`map_mem_setB`) and each fiber has product
  `b` (`fiber_prod`) — are named siblings, so the lemma is two lines.
- `prod_B_ne_zero` is a pure leaf: `Finset.prod_ne_zero_iff` from the `b ≠ 0` clause
  already in the `setB'` filter.

## Why it is good

1. The parent closes from the five named lemmas and nothing else project-specific:
   `apply mul_left_cancel₀ (prod_B_ne_zero p)` discharges the cancellation, and the
   three `calc` links are closed by `setC_eq_union` + `disjoint_AB`, `two_mem_setC`,
   and `prod_C_erase_eq_prod_B` (lines 140-148). *check*, see claim 1.
2. The shape is measurable: 5 direct lemmas, a 9-line glue, child proofs of
   8/1/1/4/1 lines, and a longest project-lemma chain of depth 3
   (`usa2020_p3 → prod_C_erase_eq_prod_B → fiber_prod → p_two_ne_zero`). *measurement*,
   see claim 2.
3. The authors state the same plan in a comment above the code, and the Lean proof
   follows it step for step: "C is the disjoint union of A and B … Hence
   ∏ C \ {2} = ∏ B, and cancelling ∏ B ≠ 0 … gives ∏ A = 2" (lines 36-42).
   *author-statement*, see claim 3.
4. The file has no `sorry`, `admit`, or `axiom`: all five children and the five
   supporting lemmas (`isSquare_mul_iff_same`, `p_two_ne_zero`, `p_two_ne_four`,
   `map_mem_setB`, `fiber_prod`) are fully proved, and the file is compiled by
   `lake build` in the project's CI on push to main. *check*, see claim 4.

In my opinion the detail worth copying is the up-front cancellation: by applying
`mul_left_cancel₀ (prod_B_ne_zero p)` before the `calc`, the author never has to
evaluate `∏B` — the chain only needs the erased-product identity and the constant,
and `∏B ≠ 0` becomes a trivial leaf from the `b ≠ 0` clause of the filter.

## When to use it, and when not

Use a calc-chain-with-named-lemmas when a product (or sum) over a filtered set must
be shown equal to a small constant, and the argument decomposes into a partition
step, an erase step and a re-indexing step that can each be stated as a self-contained
lemma with a short proof. Stating the non-zero / membership / disjointness facts first,
each as its own sibling, is what keeps the links one-line.

Avoid it when the re-indexing or fiber argument cannot be factored into a named
sibling (that is the deep part here, `fiber_prod`), when the common factor is not
provably non-zero so the cancellation does not apply, or when a single link mixes
several independent facts and forcing one lemma per link obscures rather than
organises the proof.

## Consequences

The move creates one rewrite obligation per `calc` link (three here) plus a
cancellation obligation, discharged up front by `mul_left_cancel₀ (prod_B_ne_zero p)`,
so the rest of the chain is an equality between products. The first link is the only
one needing two lemmas at once: `setC_eq_union` rewrites `C` as `A ∪ B` and
`disjoint_AB` is the hypothesis of `Finset.prod_union`, so forgetting disjointness
stalls the one-line `rw`. The erase step depends on `two_mem_setC`, which in turn
needs `p_two_ne_zero` and `p_two_ne_four`; the re-indexing step hides a depth-3 spine
through `map_mem_setB` and `fiber_prod`. Failure modes: an unproved non-zero or
membership fact collapses a link, and a calc chain that looks flat may still need a
non-trivial fiber lemma below the surface.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push-main.yaml at commit 1745e6ced3e671bd74417548494b034eb2c87da8 (pinned; on default branch main): the 'lake build' step compiles the whole project, which includes Compfiles/Usa2020P3.lean; fetched this session via fetch_file.py | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 1745e6ced3e671bd74417548494b034eb2c87da8 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read the copied parent site (Usa2020P3.lean lines 138-148): line 140 'apply mul_left_cancel₀ (prod_B_ne_zero p)' discharges the cancellation; link 1 (line 143) rw setC_eq_union p + Finset.prod_union (disjoint_AB p); link 2 (line 145) Finset.mul_prod_erase _ _ (two_mem_setC p hp2); link 3 (line 147) rw prod_C_erase_eq_prod_B p hp2. No other project-specific lemma is cited; only Mathlib tactics and same-file solution_val | verifier |
| 2 | verified | Counted in the copied file: glue = lines 140-148 (9 lines: apply + calc); child proofs setC_eq_union 66-73 (8), disjoint_AB 76 (1), two_mem_setC 88 (1), prod_C_erase_eq_prod_B 126-129 (4), prod_B_ne_zero 132 (1); depth chain usa2020_p3(138) -> prod_C_erase_eq_prod_B(129 calls fiber_prod) -> fiber_prod(119 uses p_two_ne_zero) -> p_two_ne_zero(79-80). All 5 named children; direct_lemmas=5, child_lines=[8,1,1,4,1], depth=3 match | verifier |
| 3 | verified | Read the comment block at lines 35-42 of the copied file: it states 'By multiplicativity of the quadratic character, C is the disjoint union of A and B. The map n to n*(4-n) sends C minus {2} to B ... Hence prod C-minus-{2} = prod B, and cancelling prod B != 0 from prod A * prod B = prod C = 2 * prod C-minus-{2} gives prod A = 2.' The quoted sentences match the comment (elision marked by ...), which is the same three-step plan | verifier |
| 4 | verified | Read the whole copied file (150 lines); grep for sorry|admit|axiom|Admitted returns no matches. All five children (setC_eq_union, disjoint_AB, two_mem_setC, prod_C_erase_eq_prod_B, prod_B_ne_zero) and five supporting lemmas (isSquare_mul_iff_same 57-63, p_two_ne_zero 79-80, p_two_ne_four 83-84, map_mem_setB 90-96, fiber_prod 99-121) are private lemmas with full proofs, no sorry. CI .github/workflows/push-main.yaml (fetched this session) runs 'lake build' on push to main (default branch), which compiles the project including this file | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Read the copied code (Compfiles/Usa2020P3.lean) against entry.json. Parent usa2020_p3 (138-149) closes: apply mul_left_cancel₀ (prod_B_ne_zero p) then a 3-link calc using exactly five named lemmas and nothing else project-specific — setC_eq_union+disjoint_AB (link 1, L143), two_mem_setC (link 2, L145), prod_C_erase_eq_prod_B (link 3, L147). All five child statements and closed_by methods match the code verbatim (setC_eq_union 65-73, disjoint_AB 75-76, two_mem_setC 87-88, prod_C_erase_eq_prod_B 124-129, prod_B_ne_zero 131-132). Shape is right: direct_lemmas=5, glue_lines=9 (140-148), child_lines=[8,1,1,4,1] (66-73,76,88,126-129,132), depth=3 via usa2020_p3→prod_C_erase_eq_prod_B(L147)→fiber_prod(L129)→p_two_ne_zero(L119), 3 project lemmas below the theorem. No sorry/admit/axiom in the 150-line file; author comment (35-42) states the same plan. | reviewer-correctness |
| generality | accept | Generality: goal_shape and use_when abstract beyond USA 2020 P3 to any product/sum over a filtered set shown equal to a small constant via a partition, erase and re-index step each stated as a self-contained lemma; avoid_when is specific and honest (deep fiber/re-index not factorable into a named sibling, common factor not provably non-zero, or a link mixing independent facts). Consequences honestly flags that link 1 needs two lemmas at once and that the re-indexing hides a depth-3 spine through map_mem_setB/fiber_prod, so a flat-looking calc may still need a non-trivial fiber lemma. It does say what makes the children good leaves: 'a self-contained statement whose proof closes on its own or from named siblings', with per-child bullets explaining the short proofs (extensionality+by_cases+tauto, one-line aesop, mem_filter with witnesses, two-line prod_fiberwise via named siblings, pure prod_ne_zero_iff leaf); 'stating the non-zero/membership/disjointness facts first, each as its own sibling, is what keeps the links one-line'. I verified the copied code matches (children at lines 65-73, 75-76, 87-88, 124-129, 131-132; parent 138-148). | reviewer-generality |
| provenance-licence | accept | check_provenance passes (1 file byte-identical at 1745e6ced3e671bd74417548494b034eb2c87da8); commit 1745e6ced3e671bd74417548494b034eb2c87da8 is identical across entry.json, README (short form 1745e6ced3e6), sources/compfiles/SOURCE.md and source.json; licence Apache-2.0 matches the upstream-LICENSE (Apache License 2.0 text); the single copied file code/Compfiles/Usa2020P3.lean (6019 bytes, sha256 6266f959...) matches the entry.json files/sha256 and all permalinks resolve to valid line ranges within the 150-line file. Source note is consistent and traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/dwrensha/compfiles at commit `1745e6ced3e671bd74417548494b034eb2c87da8`, under `Apache-2.0`; see the [source note](../../sources/compfiles/SOURCE.md) for the licence text and attribution.
