# Suffices to a two-claim valuation package for Putnam 2025 A6

| | |
|---|---|
| Kind | instance |
| Move | suffices-or-strengthen |
| Language | lean |
| Status | accepted |
| Source | [numina-putnam2025](../../sources/numina-putnam2025/SOURCE.md) at `60d33c8ba19a` |
| Licence | `MIT` |

## Intent

The main theorem proves a valuation of `b (2^(k+1)) - 2*b(2^k)` for one
index `k`. Instead of proving it directly for `k`, the proof `suffices` to a
stronger package: two claims that hold for *every* `j ≥ 1` — the 2-adic
valuations of `b(2^j)` and of `A b (2^j) - 1`. The package is proved once by
simultaneous induction, and the single case `k` is recovered by instantiating
`j := k` and combining the two valuations with `padicValInt.mul`.

## The decomposition

### parent `putnam_2025_a6`: [`NuminaPutnam2025/putnam_2025_a6.lean` lines 974-979](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a6.lean#L974-L979) ([local copy](code/NuminaPutnam2025/putnam_2025_a6.lean))

```lean
theorem putnam_2025_a6 (b : ℕ → ℤ)
  (hb0 : b 0 = 0)
  (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1)
  (k : ℕ)
  (hk : k ≥ 1):
  padicValInt 2 (b (2 ^ (k + 1)) - 2 * b (2 ^ k)) = 2 * k + 2 := by
```

### skeleton `putnam_2025_a6.suffices`: [`NuminaPutnam2025/putnam_2025_a6.lean` lines 1017-1031](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a6.lean#L1017-L1031) ([local copy](code/NuminaPutnam2025/putnam_2025_a6.lean))

```lean
  -- For now, we prove the required valuations by strong induction
  suffices h : (∀ j ≥ 1, padicValInt 2 (b (2^j)) = j + 1) ∧
               (∀ j ≥ 1, padicValInt 2 (A b (2^j) - 1) = j + 1) by
    obtain ⟨hb_val, hA_val⟩ := h
    -- Now use these to prove the main result
    have hv_b := hb_val k hk
    have hv_A := hA_val k hk

    -- v_2(b(2^k) * (A(2^k) - 1)) = v_2(b(2^k)) + v_2(A(2^k) - 1) = (k+1) + (k+1) = 2k+2
    have hb_ne : b (2^k) ≠ 0 := b_ne_zero b hb0 hb (2^k) (Nat.one_le_two_pow)
    have hA_ne : A b (2^k) - 1 ≠ 0 := A_pow_two_sub_one_ne_zero b hb0 hb k hk

    have hv_prod : padicValInt 2 (b (2^k) * (A b (2^k) - 1)) = 2 * k + 2 := by
      rw [padicValInt.mul (p := 2) hb_ne hA_ne, hv_b, hv_A]
      ring
```

### child `putnam_2025_a6.hP`: [`NuminaPutnam2025/putnam_2025_a6.lean` lines 1428-1440](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a6.lean#L1428-L1440) ([local copy](code/NuminaPutnam2025/putnam_2025_a6.lean))

```lean
  -- Now prove the two inductive claims together using strong induction
  -- The key is that these claims are interdependent and must be proven together

  -- Define the combined proposition P(j) = (v_2(b_{2^j}) = j+1) ∧ (v_2(A_{2^j} - 1) = j+1)
  have hP : ∀ j ≥ 1, (padicValInt 2 (b (2^j)) = j + 1) ∧ (padicValInt 2 (A b (2^j) - 1) = j + 1) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      exact ⟨base_case_b b hb0 hb, base_case_A b hb0 hb⟩
    | succ j hj' ih =>
      -- Need to prove both claims for j+1 using ih for j
      obtain ⟨ih_b, ih_A⟩ := ih
      constructor
```

How the parts fit. The parent `putnam_2025_a6` is reduced by the `suffices`
(skeleton) to the package `h`, a conjunction of two `∀ j ≥ 1` claims. The
skeleton's `by` block then shows the parent follows from the package: `obtain
⟨hb_val, hA_val⟩ := h` splits the package into its two claims; `hv_b` and
`hv_A` instantiate them at `j := k` using `hk : k ≥ 1`; and `hv_prod` combines
the two factor valuations with `padicValInt.mul` (lines 1029-1031) to get
`2*k+2`. The rest of the skeleton block (lines 1033-1426) handles the error
term `ExpErr`, so this excerpt stops at the cleanest part of the reduction.
The package `h` itself is then closed by the child: `hP` (lines 1432-1581)
proves the conjunction by `Nat.le_induction`, with base cases `base_case_b`
and `base_case_A` (line 1436) and a `succ` step that carries both halves of
the induction hypothesis together (`obtain ⟨ih_b, ih_A⟩ := ih`, line 1439).
The closing `constructor` with two projections (lines 1583-1585) turns `hP`
into the two conjuncts of `h`.

## Why it is good

1. The reduction from the package back to the parent is small: assuming `h`,
   `hv_prod` (the product valuation) is derived in three lines (1029-1031) by
   `padicValInt.mul` and `ring`, after two one-line instantiations `hv_b`,
   `hv_A` (1022-1023). The file is built by the project's CI
   (`.github/workflows/lean_action_ci.yml` runs `leanprover/lean-action@v1`,
   i.e. `lake build`, on push and pull request). (*check*)
2. The package `h` closes by simultaneous induction: `hP` is proved by
   `Nat.le_induction` (line 1434), and `constructor` with the two projections
   (lines 1583-1585) recovers the two conjuncts of `h`. (*check*)
3. The authors say why the two claims are bundled into one `suffices`:
   "The key is that these claims are interdependent and must be proven
   together" (lines 1428-1429). (*author-statement*)
4. The `suffices` step separates a short reduction from a long induction: the
   reduction is 14 lines (1018-1031) and the induction is 154 lines
   (1432-1585). (*measurement*)

In my opinion the detail worth copying is that the two claims are *not*
strengthened and proved separately: they are one conjunction so that a single
`Nat.le_induction` can exchange both halves of the induction hypothesis at
every step.

## When to use it, and when not

Use it when the goal fixes one index `k` but the proof's natural statement is
a universal claim over all indices, or when two claims are mutually dependent
so each induction step needs the other (then they must be stated together as
one conjunction). The `suffices` isolates the strengthened statement from the
short reduction back to the original goal.

Avoid it when the strengthened statement is false or harder to prove than the
original (a strengthening must still be provable); when the reduction back is
not routine — here the skeleton still needs the error-term argument at lines
1033-1426, so the `suffices` only buys a clean split, not a trivial finish; or
when the strengthened claim should be a standalone named lemma used elsewhere,
where `extract-have` is the better move.

## Consequences

The move creates one new obligation (the package `h`) plus the reduction
obligation in the `suffices` `by` block (that `h` implies the parent). The
strengthened statement quantifies over all `j ≥ 1`, so it must hold at every
index, not just `k`; a false strengthened claim makes the whole proof
unprovable. The two conjuncts are coupled — each `succ` step of `hP` uses both
halves of the IH (`obtain ⟨ih_b, ih_A⟩ := ih`), so they cannot be separated
into two independent inductions. Failure mode: a too-strong `suffices` is a
silent dead-end that surfaces only when the package goal is attacked.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/lean_action_ci.yml runs leanprover/lean-action@v1 (lake build) on push and pull_request; commit 60d33c8ba19af905bd731e938ebde1c5b8c76519 confirmed on default branch main via branches-where-head API | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 60d33c8ba19af905bd731e938ebde1c5b8c76519 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | copied file (byte-identical at pinned commit): lines 1022-1023 have hv_b := hb_val k hk and hv_A := hA_val k hk; lines 1029-1031 derive hv_prod via rw [padicValInt.mul ...] then ring | verifier |
| 2 | verified | copied file: line 1432 have hP, line 1434 induction j, hj using Nat.le_induction, line 1436 base cases base_case_b/base_case_A, lines 1583-1585 constructor with projections (hP j hj).1/.2 | verifier |
| 3 | verified | copied file line 1429 comment reads exactly '-- The key is that these claims are interdependent and must be proven together' | verifier |
| 4 | verified | arithmetic on copied file: span 1018-1031 = 14 lines; span 1432-1585 = 154 lines (1585-1432+1); both correct | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Read the copied file code/NuminaPutnam2025/putnam_2025_a6.lean. Parent putnam_2025_a6 at 974-979 matches entry.json verbatim. Skeleton 1017-1031: 'suffices h : (forall j>=1, v2(b(2^j))=j+1) & (forall j>=1, v2(A b(2^j)-1)=j+1) by' (1018-1019) then obtain<hb_val,hA_val> and instantiate at j:=k (1022-1023) and hv_prod via padicValInt.mul+ring (1029-1031) - matches claim 1 and the strengthened package. Child hP at 1432-1581 proved by 'induction j,hj using Nat.le_induction' (1434) with base base_case_b/base_case_A (1436) and succ step 'obtain <ih_b,ih_A> := ih' (1439) carrying both halves - matches child.closed_by and claim 2. Closing: 'constructor' with two projections (1583-1585) recovers the two conjuncts of h, and the suffices 'by' block closes the parent via padicValInt_add_of_lt' (1423). No sorry/admit/axiom in the file (only comments at 539/1264 mention them). Author quote 'interdependent and must be proven together' at 1429, line spans 1018-1031=14 and 1432-1585=154 verified. Decomposition is what the entry says and it closes. | reviewer-correctness |
| generality | accept | Move is stated generally: applicability names two reusable patterns (single-index goal whose proof needs the property at every index -> universal strengthening; mutually dependent claims bundled into one conjunction for a single simultaneous induction) and cross-references extract-have for the standalone-lemma case. When-not-to-use is honest and specific: it explicitly admits that in this example the reduction is NOT routine (error-term argument at lines 1033-1426, verified in the copied file), so the suffices only buys a clean split, plus a false strengthening is a dead end. Consequences are honest and specific: new package obligation + reduction obligation, all-indices quantification risk, coupled conjuncts, silent-dead-end failure mode. Minor caveat, not enough to object: the coupling is one-directional in the proof (the A-claim step uses ih_b at line 1517, but the b-claim step does not use ih_A), so 'each induction step uses both halves' overstates slightly; the general lesson (bundle coupled claims to share hypotheses in one induction) still holds. | reviewer-generality |
| provenance-licence | accept | Provenance and licence are consistent and traceable. check_provenance.py passes: the copied file code/NuminaPutnam2025/putnam_2025_a6.lean is byte-identical at commit 60d33c8ba19af905bd731e938ebde1c5b8c76519. Commit 60d33c8ba19af905bd731e938ebde1c5b8c76519 is identical across entry.json source.commit, files/sites permalinks, sources/numina-putnam2025/SOURCE.md, source.json and ledger/sources.jsonl. Licence MIT is consistent across entry.json, README, source.json, SOURCE.md, ledger, and the source note's upstream-LICENSE, which is the upstream MIT License (Copyright (c) 2025 Numina). Source URL project-numina/Numina-Putnam2025 and file path NuminaPutnam2025/putnam_2025_a6.lean match the local code path. No discrepancy found. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/project-numina/Numina-Putnam2025 at commit `60d33c8ba19af905bd731e938ebde1c5b8c76519`, under `MIT`; see the [source note](../../sources/numina-putnam2025/SOURCE.md) for the licence text and attribution.
