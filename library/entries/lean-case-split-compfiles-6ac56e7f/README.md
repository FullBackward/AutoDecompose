# Residue split mod 3 for IMO 1964 P1(b)

| | |
|---|---|
| Kind | instance |
| Move | case-split |
| Language | lean |
| Status | draft |
| Source | [compfiles](../../sources/compfiles/SOURCE.md) at `1745e6ced3e6` |
| Licence | `Apache-2.0` |

## Intent

A statement about every natural number `n` is reduced to three closed
computations by splitting on the residue `n % 3`, because `2 ^ 3 % 7 = 1`
makes `2 ^ n % 7` depend only on that residue. Each case then closes by
rewriting alone.

## The decomposition

### parent `imo1964_p1b`: [`Compfiles/Imo1964P1.lean` lines 49-69](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Imo1964P1.lean#L49-L69) ([local copy](code/Compfiles/Imo1964P1.lean))

```lean
problem imo1964_p1b (n : ℕ) : ¬ 7 ∣ (2^n + 1) := by
  /-
  Following https://prase.cz/kalva/imo/isoln/isoln641.html:
  Let n = 3m + k; k = 0, 1, or 2.
  2^3 = 1 (mod 7).
  Hence
  2^3m + 1 = 2 (mod 7),
  2^(3m+1) + 1 = 3 (mod 7), and
  2^(3m + 2) + 1 = 5 (mod 7).
  -/
  intro h
  apply Nat.mod_eq_zero_of_dvd at h
  have h1: 2 ^ 3 % 7 = 1 := by rfl
  mod_cases h2 : n % 3 <;> rw [← Nat.div_add_mod n 3, h2] at h
  · rw [Nat.zero_mod, add_zero, Nat.add_mod, Nat.pow_mod, pow_mul,
        Nat.pow_mod, h1, one_pow (M := ℕ)] at h
    contradiction
  · rw [Nat.add_mod, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, h1, one_pow (M := ℕ)] at h
    contradiction
  · rw [Nat.add_mod, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, h1, one_pow (M := ℕ)] at h
    contradiction
```

### context `imo_1964_p1b'`: [`Compfiles/Imo1964P1.lean` lines 75-79](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Imo1964P1.lean#L75-L79) ([local copy](code/Compfiles/Imo1964P1.lean))

```lean
theorem imo_1964_p1b' : ∀ (n : ℕ), (2 ^ n + 1) % 7 ≠ 0
    | 0 | 1 | 2 => by decide
    | n + 3 => by
      rw [pow_add, Nat.add_mod, Nat.mul_mod, show 2 ^ 3 % 7 = 1 by rfl]
      simp [imo_1964_p1b' n]
```

How the parts fit. The parent `imo1964_p1b` first states the period as a
fact, `h1 : 2 ^ 3 % 7 = 1`. Then `mod_cases h2 : n % 3` produces one goal per
residue 0, 1, 2, and the combinator `<;>` applies the same rewrite of `n` as
`n / 3 * 3 + n % 3` to all three at once. Each child is closed by one `rw`
chain that reduces the hypothesis to a false numeral equation, followed by
`contradiction`. No auxiliary lemma is stated: the children are the three
goals the tactic creates.

The second excerpt, from the same file, proves a slightly different statement
by recursion on `n + 3` with the three base cases `0 | 1 | 2` checked by
`decide`. It is the same split, organised as well-founded recursion with step
three instead of as a residue case analysis.

## Why it is good

1. The universally quantified goal becomes three goals with no free
   arithmetic left, each closed by one rewrite chain and `contradiction`
   (lines 62-69); the file is built by the project's CI.
2. The authors state the informal plan in a comment beside the proof, and the
   Lean proof follows it step for step: "Let n = 3m + k; k = 0, 1, or 2.
   2^3 = 1 (mod 7)" (lines 50-58).
3. The same split, on the same residue, also proves part (a) in the same file
   (`mod_cases H : n % 3`, line 44), so one move serves both directions of the
   problem.
4. The exhaustiveness of the split costs nothing: `mod_cases` creates exactly
   the residues `0, 1, 2` itself, so no separate lemma `n % 3 = 0 ∨ n % 3 = 1 ∨
   n % 3 = 2` appears in the file.

In my opinion the shared rewrite under `<;>` is the detail worth copying: the
case split and the normalisation of `n` are stated once for all cases.

## When to use it, and when not

Use it when the goal's truth depends on `n` only through `n % k` for a small,
known `k`, typically because some power or recurrence is periodic modulo a
fixed number; the period should be stated first as its own fact (`h1` here).
Avoid it when `k` is large or unknown, when the periodicity itself needs a
proof by induction (then that lemma is the real content and belongs before
the split), or when the cases need different arguments, where a shared `<;>`
step will not fit.

## Consequences

The move creates `k` goals and an exhaustiveness obligation, which `mod_cases`
discharges itself; with plain `rcases` on a disjunction the obligation would
be a separate child. The proof depends on rewriting `n` as `n / 3 * 3 + n % 3`
in every case; if the residue enters the goal in a different form, each case
needs its own normalisation and the shared step breaks.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 1745e6ced3e671bd74417548494b034eb2c87da8 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/dwrensha/compfiles at commit `1745e6ced3e671bd74417548494b034eb2c87da8`, under `Apache-2.0`; see the [source note](../../sources/compfiles/SOURCE.md) for the licence text and attribution.
