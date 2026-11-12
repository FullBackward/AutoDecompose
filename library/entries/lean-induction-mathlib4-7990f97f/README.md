# Lower-bound induction on k for IMO 1985 Q2

| | |
|---|---|
| Kind | instance |
| Move | induction |
| Language | lean |
| Status | accepted |
| Source | [mathlib4](../../sources/mathlib4/SOURCE.md) at `e1545ebed975` |
| Licence | `Apache-2.0` |

## Intent

Prove that every number `k * j % n` (for `1 ≤ k < n`) has the same color as `j`
by induction on `k` over the lower bound `1 ≤ k`, so that the base is `k = 1`
and the step inherits the strengthened bound `1 ≤ k < n` that the induction
hypothesis needs.

## The decomposition

### parent `C_mul_mod`: [`Archive/Imo/Imo1985Q2.lean` lines 48-77](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Imo/Imo1985Q2.lean#L48-L77) ([local copy](code/Archive/Imo/Imo1985Q2.lean))

```lean
/-- For `1 ≤ k < n`, `k * j % n` has the same color as `j`. -/
lemma C_mul_mod {n j : ℕ} (hn : 3 ≤ n) (hj : j ∈ Set.Ico 1 n) (cpj : Nat.Coprime n j)
    {C : ℕ → Fin 2} (hC : Condition n j C) {k : ℕ} (hk : k ∈ Set.Ico 1 n) :
    C (k * j % n) = C j := by
  induction k, hk.1 using Nat.le_induction with
  | base => rw [one_mul, Nat.mod_eq_of_lt hj.2]
  | succ k hk₁ ih =>
    have nej : (k + 1) * j % n ≠ j := by
      by_contra h; nth_rw 2 [← Nat.mod_eq_of_lt hj.2, ← one_mul j] at h
      replace h : (k + 1) % n = 1 % n := Nat.ModEq.cancel_right_of_coprime cpj h
      rw [Nat.mod_eq_of_lt hk.2, Nat.mod_eq_of_lt (by lia)] at h
      lia
    have b₁ : (k + 1) * j % n ∈ Set.Ico 1 n := by
      refine ⟨?_, Nat.mod_lt _ (by lia)⟩
      by_contra! h; rw [Nat.lt_one_iff, ← Nat.dvd_iff_mod_eq_zero] at h
      have ek := Nat.eq_zero_of_dvd_of_lt (cpj.dvd_of_dvd_mul_right h) hk.2
      lia
    rw [← ih ⟨hk₁, Nat.lt_of_succ_lt hk.2⟩, hC.2 _ b₁ nej]
    rcases nej.lt_or_gt with h | h
    · rw [Int.natAbs_natCast_sub_natCast_of_ge h.le]
      have b₂ : j - (k + 1) * j % n ∈ Set.Ico 1 n :=
        ⟨Nat.sub_pos_iff_lt.mpr h, (Nat.sub_le ..).trans_lt hj.2⟩
      have q : n - (j - (k + 1) * j % n) = (k + 1) * j % n + (n - j) % n := by
        rw [tsub_tsub_eq_add_tsub_of_le h.le, add_comm, Nat.add_sub_assoc hj.2.le,
          Nat.mod_eq_of_lt (show n - j < n by lia)]
      rw [hC.1 _ b₂, q, ← Nat.add_mod_of_add_mod_lt (by lia), ← Nat.add_sub_assoc hj.2.le,
        add_comm, Nat.add_sub_assoc (Nat.le_mul_of_pos_left _ hk.1), ← tsub_one_mul,
        Nat.add_mod_left, add_tsub_cancel_right]
    · rw [Int.natAbs_natCast_sub_natCast_of_le h.le, Nat.mod_sub_of_le h.le]
      rw [add_mul, one_mul, add_tsub_cancel_right]
```

### context `Condition`: [`Archive/Imo/Imo1985Q2.lean` lines 43-46](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Imo/Imo1985Q2.lean#L43-L46) ([local copy](code/Archive/Imo/Imo1985Q2.lean))

```lean
/-- The conditions on the problem's coloring `C`.
Although its domain is all of `ℕ`, we only care about its values in `Set.Ico 1 n`. -/
def Condition (n j : ℕ) (C : ℕ → Fin 2) : Prop :=
  (∀ i ∈ Set.Ico 1 n, C i = C (n - i)) ∧ (∀ i ∈ Set.Ico 1 n, i ≠ j → C i = C (j - i : ℤ).natAbs)
```

### context `result`: [`Archive/Imo/Imo1985Q2.lean` lines 79-92](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Imo/Imo1985Q2.lean#L79-L92) ([local copy](code/Archive/Imo/Imo1985Q2.lean))

```lean
theorem result {n j : ℕ} (hn : 3 ≤ n) (hj : j ∈ Set.Ico 1 n) (cpj : Coprime n j)
    {C : ℕ → Fin 2} (hC : Condition n j C) {i : ℕ} (hi : i ∈ Set.Ico 1 n) :
    C i = C j := by
  obtain ⟨v, -, hv⟩ := exists_mul_mod_eq_one_of_coprime cpj.symm (by lia)
  have hvi : i = (v * i % n) * j % n := by
    rw [mod_mul_mod, ← mul_rotate, ← mod_mul_mod, hv, one_mul, mod_eq_of_lt hi.2]
  have vib : v * i % n ∈ Set.Ico 1 n := by
    refine ⟨(?_ : 0 < _), mod_lt _ (by lia)⟩
    by_contra! h; rw [le_zero, ← dvd_iff_mod_eq_zero] at h
    rw [mul_comm, ← mod_eq_of_lt (show 1 < n by lia)] at hv
    have i0 := eq_zero_of_dvd_of_lt
      ((coprime_of_mul_modEq_one _ hv).symm.dvd_of_dvd_mul_left h) hi.2
    subst i; simp at hi
  rw [hvi, C_mul_mod hn hj cpj hC vib]
```

How the parts fit. `Condition n j C` (the context excerpt) packages the two
coloring rules: `hC.1` (rule 1, `i` and `n - i` have the same color) and `hC.2`
(rule 2, `i` and `|j - i|` have the same color when `i ≠ j`). The parent
`C_mul_mod` is proved by `induction k, hk.1 using Nat.le_induction`: it induces
on `k` with the lower-bound proof `hk.1 : 1 ≤ k` as the index, using the
lower-bound induction principle `Nat.le_induction`. This sets the base at
`k = 1` (not `k = 0`) and makes the step `k → k + 1`.

- **base `k = 1`**: goal `C (1 * j % n) = C j`, closed by `rw [one_mul,
  Nat.mod_eq_of_lt hj.2]`, using `hj.2 : j < n`.
- **step `k → k + 1`**: goal `C ((k + 1) * j % n) = C j` with `hk₁ : 1 ≤ k`
  and (generalised) `hk.2 : k + 1 < n`. It first proves two facts: `nej :
  (k + 1) * j % n ≠ j` (if it were equal, coprimality would force `(k + 1) % n
  = 1 % n` and hence `k + 1 = n`, contradicting `hk.2`), and `b₁ : (k + 1) * j
  % n ∈ Set.Ico 1 n`. Then it rewrites the goal with the induction hypothesis
  instantiated at the strengthened index `⟨hk₁, Nat.lt_of_succ_lt hk.2⟩ : k ∈
  Set.Ico 1 n` and with rule 2 `hC.2 _ b₁ nej`, turning the left-hand side into
  `|j − (k + 1) * j % n|` and the right-hand side into the IH's `C (k * j %
  n)`. Finally `rcases nej.lt_or_gt with h | h` splits on whether `(k + 1) * j
  % n` lies below or above `j` — the two cases the module doc comment names —
  and each branch reduces the absolute value to `k * j % n` by a rewrite chain.

The context `result` shows the reuse: it writes an arbitrary `i` as `(v * i %
n) * j % n` (using coprimality) and then closes with `C_mul_mod` at `vib : v *
i % n ∈ Set.Ico 1 n`.

## Why it is good

1. The parent is closed entirely by the induction: the base closes in one
   rewrite (line 53) and the step closes inline (lines 54-77), with no
   auxiliary lemma stated (`check`, lines 48-77; the file is built by mathlib4
   CI).
2. The authors state the informal plan the induction follows: "it suffices to
   show that `kj mod n ∼ (k−1)j mod n` for `1 < k < n`", with the two cases "if
   `kj mod n > j`" and "if `kj mod n < j`" (lines 29-34), and the lemma's doc
   comment states "For `1 ≤ k < n`, `k * j % n` has the same color as `j`"
   (line 48) (`author-statement`).
3. `C_mul_mod` is used exactly once, in `result` at line 92, to close the main
   theorem (`known-use`, line 92).
4. The step's two arithmetic branches are asymmetric: the `(k+1)*j % n < j`
   branch is 9 lines (67-75) while the `j < (k+1)*j % n` branch is 2 lines
   (76-77) (`measurement`, lines 66-77).

In my opinion the transferable detail is the choice of induction principle:
inducing on the lower bound `hk.1` with `Nat.le_induction` rather than on `k`
moves the base from `0` to `1` and, crucially, delivers `1 ≤ k` and `k < n` to
the step for free, so the IH can be applied exactly where it is stated.

## When to use it, and when not

Use it when the statement must be shown for `k` in a half-open interval
`[m, n)` with a nonzero lower bound `m`, and the step needs to apply the
induction hypothesis at the previous value `k` (which still satisfies
`m ≤ k < n`). `Nat.le_induction` sets the base at `m` and carries the bound
`m ≤ k` into the step. Avoid it when the lower bound is `0` (plain `induction
k` suffices), when the step needs the IH at an index outside `[m, n)` so the
carried bound does not reach, or when the step's own case analysis dominates
the induction — then factor that case analysis into a separate lemma first.

## Consequences

Induction on `hk.1` with `Nat.le_induction` sets the base at the lower bound
(`k = 1`, not `k = 0`) and carries `1 ≤ k` into the step, so the step must be
stated for `k + 1`; the upper bound is generalised (the step sees `hk.2 : k +
1 < n`), which is what lets the IH be applied at `⟨hk₁, Nat.lt_of_succ_lt
hk.2⟩`. The step then has to establish `nej : (k+1)*j % n ≠ j` (from
coprimality) and `b₁ : (k+1)*j % n ∈ Set.Ico 1 n` before rule 2 can apply, and
finally split on `nej.lt_or_gt`; each branch does a different arithmetic
reduction of `|j − (k+1)*j % n|` to `k*j % n`. Failure modes: if the step needs
the IH at an index outside `[1, n)` the strengthened bound does not reach; if
`j` is not coprime the `nej` step fails; the two branches need separate,
non-uniform rewrite work.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build_template.yml builds Archive via 'lake-build-with-retry.sh Archive Counterexamples Wanted' (line 252) and gates on 'lake build --no-build --wfail Archive' (line 297); Archive/Imo/Imo1985Q2.lean is part of the Archive target. Pinned commit e1545ebed97594477bbd88b2fe948ffce56e5af2 is on the default branch master (GitHub compare API e1545ebed...master: behind_by 0, ahead_by 1). | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at e1545ebed97594477bbd88b2fe948ffce56e5af2 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Opened copied code/Archive/Imo/Imo1985Q2.lean: line 52 'induction k, hk.1 using Nat.le_induction with'; base closes in one rewrite at line 53 'rw [one_mul, Nat.mod_eq_of_lt hj.2]'; step closes inline lines 54-77; no auxiliary top-level lemma (only inline have b1/nej/b2/q). | verifier |
| 2 | verified | Opened copied file lines 28-34: 'so it suffices to show that kj mod n ~ (k-1)j mod n for 1 < k < n' and the two cases 'if kj mod n > j' / 'if kj mod n < j'; line 48 doc comment 'For 1 ≤ k < n, k * j % n has the same color as j'. | verifier |
| 3 | verified | Opened copied file lines 79-92: C_mul_mod appears only at its definition (line 49) and at line 92 'rw [hvi, C_mul_mod hn hj cpj hC vib]' which closes theorem result; no other use in the file. | verifier |
| 4 | verified | Opened copied file lines 66-77: after 'rcases nej.lt_or_gt with h | h' the (k+1)*j % n < j branch spans lines 67-75 (9 lines) and the j < (k+1)*j % n branch spans lines 76-77 (2 lines). | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent statement matches code lines 49-51 verbatim; base child = line 53 'rw [one_mul, Nat.mod_eq_of_lt hj.2]' matches; step child = lines 54-77 matches (succ k hk1 ih, rw [<- ih <hk1, Nat.lt_of_succ_lt hk.2>, hC.2 _ b1 nej], rcases nej.lt_or_gt). hk.2 in step is k+1 < n (forced by Nat.mod_eq_of_lt hk.2 at line 57 and Nat.eq_zero_of_dvd_of_lt at line 63), confirming the upper bound is generalised as the entry states. No sorry/admit/axiom in the copied file; proof closes and is CI-built (Archive target). | reviewer-correctness |
| generality | accept | Applicability states a generic goal shape (forall k, k in Set.Ico m n -> P (f k)) and use/avoid conditions parameterised by m and n, so the move is described beyond this example; also_known_as lists synonyms. 'When not to use' is honest and specific: lower bound 0 (plain induction suffices), step needing IH outside [m,n) (carried bound does not reach), and step case analysis dominating the induction (factor into a separate lemma). Consequences accurately describe the mechanism (Nat.le_induction sets base at the lower bound, step stated for k+1, upper bound generalised so the IH applies at <hk1, Nat.lt_of_succ_lt hk.2>) and give honest, specific failure modes (nej fails if j not coprime; the two arithmetic branches need non-uniform rewrite work). No overclaim of reuse: known_uses is only the one file. | reviewer-generality |
| provenance-licence | accept | Commit e1545ebed97594477bbd88b2fe948ffce56e5af2 is consistent across entry.json (source.commit, files/sites/claims permalinks, known_uses), README, sources/mathlib4/source.json and SOURCE.md; raw fetch at that commit succeeded and the copied code/Archive/Imo/Imo1985Q2.lean is byte-identical (sha256 7f66b1ae..., 4204 bytes, matches entry.json). Permalink line ranges match the copied file (parent 48-77, Condition 43-46, result 79-92). Licence Apache-2.0 is consistent in entry.json, README, source.json, SOURCE.md, and the file header ('Released under Apache 2.0 license'); sources/mathlib4/upstream-LICENSE holds the Apache-2.0 text. Everything traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover-community/mathlib4 at commit `e1545ebed97594477bbd88b2fe948ffce56e5af2`, under `Apache-2.0`; see the [source note](../../sources/mathlib4/SOURCE.md) for the licence text and attribution.
