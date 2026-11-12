# Suffices to a two-claim valuation package for Putnam 2025 A6

| | |
|---|---|
| Kind | instance |
| Move | suffices-or-strengthen |
| Language | lean |
| Status | draft |
| Source | [numina-putnam2025](../../sources/numina-putnam2025/SOURCE.md) at `60d33c8ba19a` |
| Licence | `MIT` |

## Intent

TODO: one or two sentences on what this decomposition achieves.

## The decomposition

### parent `putnam_2025_a6`: [`NuminaPutnam2025/putnam_2025_a6.lean` lines 974-978](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a6.lean#L974-L978) ([local copy](code/NuminaPutnam2025/putnam_2025_a6.lean))

```lean
theorem putnam_2025_a6 (b : ℕ → ℤ)
  (hb0 : b 0 = 0)
  (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1)
  (k : ℕ)
  (hk : k ≥ 1):
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

### child `putnam_2025_a6.hP`: [`NuminaPutnam2025/putnam_2025_a6.lean` lines 1431-1440](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a6.lean#L1431-L1440) ([local copy](code/NuminaPutnam2025/putnam_2025_a6.lean))

```lean
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

TODO: explain how the parts fit: which child closes which obligation, and how each child was closed.

## Why it is good

TODO: numbered claims, each matching one entry of `claims` in entry.json, with its kind of evidence and a pointer.

## When to use it, and when not

TODO

## Consequences

TODO: obligations created, failure modes.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/project-numina/Numina-Putnam2025 at commit `60d33c8ba19af905bd731e938ebde1c5b8c76519`, under `MIT`; see the [source note](../../sources/numina-putnam2025/SOURCE.md) for the licence text and attribution.
