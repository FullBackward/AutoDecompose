# Strong induction on the conductor level down to a divisor of 2

| | |
|---|---|
| Kind | instance |
| Move | induction |
| Language | lean |
| Status | draft |
| Source | [flt-anthropic](../../sources/flt-anthropic/SOURCE.md) at `6e837e753555` |
| Licence | `Apache-2.0` |

## Intent

Lower the conductor level of a Frey representation to a divisor of 2 by
strong induction on the level `N`. Each induction step removes one prime
factor of `N` through a named level-lowering lemma, until only the prime 2
can divide `N`, where a squarefree argument closes the base case.

## The decomposition

### parent `exists_modularRepOfLevel_dvd_two_of_conductorLevel₁₆`: [`P2M/Sol/S_FreyPackage_level_lowering_to_two_of_conductorLevel.lean` lines 113-148](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_level_lowering_to_two_of_conductorLevel.lean#L113-L148) ([local copy](code/P2M/Sol/S_FreyPackage_level_lowering_to_two_of_conductorLevel.lean))

```lean
private theorem _root_.FreyPackage.exists_modularRepOfLevel_dvd_two_of_conductorLevel₁₆ (P : FreyPackage)
    (hirr : GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p) :
    ∀ N : ℕ, P.IsConductorLevel N → P.ModularRepOfLevel N →
      ∃ M : ℕ, 0 < M ∧ M ∣ 2 ∧ P.ModularRepOfLevel M := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hcond hmod
    by_cases hodd : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ≠ P.p ∧ q ∣ N
    ·
      obtain ⟨q, hq, hq2, hqp, hqN⟩ := hodd
      obtain ⟨M, hMN, hqM, hmodM⟩ :=
        P.level_lowering_odd_prime_of_conductorLevel hcond hq hq2 hqp hqN hirr hmod
          (P.freyGaloisRep_isUnramifiedAt hq hq2 hqp)
      have hM0 : 0 < M := Nat.pos_of_ne_zero fun h => by
        subst h; exact hcond.pos.ne' (Nat.eq_zero_of_zero_dvd hMN)
      have hMlt : M < N :=
        lt_of_le_of_ne (Nat.le_of_dvd hcond.pos hMN) fun h => hqM (h ▸ hqN)
      exact ih M hMlt (hcond.of_dvd hMN hM0) hmodM
    · by_cases hpN : P.p ∣ N
      ·
        obtain ⟨M, hMN, hpM, hmodM⟩ := P.level_lowering_at_p_of_conductorLevel hcond hpN hirr hmod
        have hM0 : 0 < M := Nat.pos_of_ne_zero fun h => by
          subst h; exact hcond.pos.ne' (Nat.eq_zero_of_zero_dvd hMN)
        have hMlt : M < N :=
          lt_of_le_of_ne (Nat.le_of_dvd hcond.pos hMN) fun h => hpM (h ▸ hpN)
        exact ih M hMlt (hcond.of_dvd hMN hM0) hmodM
      ·

        refine ⟨N, hcond.pos,
          dvd_two_of_squarefree_of_forall_prime_eq_two₁₆ hcond.squarefree ?_, hmod⟩
        intro q hq hqN
        by_contra hq2
        rcases eq_or_ne q P.p with rfl | hqp
        · exact hpN hqN
        · exact hodd ⟨q, hq, hq2, hqp, hqN⟩
```

### child `level_lowering_odd_prime_of_conductorLevel`: [`Theorems/Thm_FreyPackage_level_lowering_odd_prime_of_conductorLevel.lean` lines 90-90](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_FreyPackage_level_lowering_odd_prime_of_conductorLevel.lean#L90-L90) ([local copy](code/Theorems/Thm_FreyPackage_level_lowering_odd_prime_of_conductorLevel.lean))

```lean
theorem FreyPackage.level_lowering_odd_prime_of_conductorLevel (P : FreyPackage) {N q : ℕ} (hcond : P.IsConductorLevel N) (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ P.p) (hqN : q ∣ N) (hirr : GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p) (hmod : P.ModularRepOfLevel N) (hunr : P.GaloisRepUnramifiedAt q) : ∃ M : ℕ, M ∣ N ∧ ¬ q ∣ M ∧ P.ModularRepOfLevel M := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_level_lowering_odd_prime_of_conductorLevel.solution
```

### child `level_lowering_at_p_of_conductorLevel`: [`Theorems/Thm_FreyPackage_level_lowering_at_p_of_conductorLevel.lean` lines 70-70](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_FreyPackage_level_lowering_at_p_of_conductorLevel.lean#L70-L70) ([local copy](code/Theorems/Thm_FreyPackage_level_lowering_at_p_of_conductorLevel.lean))

```lean
theorem FreyPackage.level_lowering_at_p_of_conductorLevel (P : FreyPackage) {N : ℕ} (hcond : P.IsConductorLevel N) (hpN : P.p ∣ N) (hirr : GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p) (hmod : P.ModularRepOfLevel N) : ∃ M : ℕ, M ∣ N ∧ ¬ P.p ∣ M ∧ P.ModularRepOfLevel M := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_level_lowering_at_p_of_conductorLevel.solution
```

### child `dvd_two_of_squarefree_of_forall_prime_eq_two₁₆`: [`P2M/Sol/S_FreyPackage_level_lowering_to_two_of_conductorLevel.lean` lines 98-111](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_level_lowering_to_two_of_conductorLevel.lean#L98-L111) ([local copy](code/P2M/Sol/S_FreyPackage_level_lowering_to_two_of_conductorLevel.lean))

```lean
lemma dvd_two_of_squarefree_of_forall_prime_eq_two₁₆ {N : ℕ} (hsq : Squarefree N)
    (h : ∀ q : ℕ, q.Prime → q ∣ N → q = 2) : N ∣ 2 := by
  rcases eq_or_ne N 1 with rfl | hN1
  · exact one_dvd 2
  obtain ⟨q, hq, hqN⟩ := Nat.exists_prime_and_dvd hN1
  obtain rfl := h q hq hqN
  obtain ⟨N', rfl⟩ := hqN
  rcases eq_or_ne N' 1 with rfl | hN'1
  · norm_num
  · exfalso
    obtain ⟨r, hr, hrN'⟩ := Nat.exists_prime_and_dvd hN'1
    obtain rfl := h r hr (Dvd.dvd.mul_left hrN' 2)
    exact Nat.squarefree_iff_prime_squarefree.mp hsq 2 Nat.prime_two
      (mul_dvd_mul_left 2 hrN')
```

### context `solution`: [`P2M/Sol/S_FreyPackage_level_lowering_to_two_of_conductorLevel.lean` lines 163-170](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_level_lowering_to_two_of_conductorLevel.lean#L163-L170) ([local copy](code/P2M/Sol/S_FreyPackage_level_lowering_to_two_of_conductorLevel.lean))

```lean
theorem solution (P : FreyPackage)
    (hirr : GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p)
    {N : ℕ} (hcond : P.IsConductorLevel N) (hmod : P.ModularRepOfLevel N) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 2) 2, f ≠ 0 := by
  obtain ⟨M, hM0, hM2, hmodM⟩ :=
    P.exists_modularRepOfLevel_dvd_two_of_conductorLevel₁₆ hirr N hcond hmod
  obtain ⟨f, W, 𝔪, hf, -⟩ := hmodM
  exact absurd (ModularForm.S2_Gamma0_eq_zero_of_dvd_two₁₆ hM0 hM2 f) hf.ne_zero
```

How the parts fit. The parent `exists_modularRepOfLevel_dvd_two_of_conductorLevel₁₆`
introduces the level `N`, then runs `induction N using Nat.strong_induction_on`
(line 118), so the induction hypothesis `ih` applies to any strictly smaller
level. The induction step is the decomposition: two case splits peel off one
prime factor at a time, and each leaf is a named lemma.

```text
exists_modularRepOfLevel_dvd_two_of_conductorLevel₁₆  (strong induction on N)
├── ∃ odd prime q ≠ 2, q ≠ p, q ∣ N
│     └─ level_lowering_odd_prime_of_conductorLevel  →  M < N, recurse via ih
├── p ∣ N
│     └─ level_lowering_at_p_of_conductorLevel        →  M < N, recurse via ih
└── (no such q, and p ∤ N) every prime dividing N is 2
      └─ dvd_two_of_squarefree_of_forall_prime_eq_two₁₆  →  N ∣ 2
```

- `level_lowering_odd_prime_of_conductorLevel` (line 125) is the Ribet step:
  an odd prime `q ≠ 2, q ≠ P.p` dividing `N`, at which the representation is
  unramified, yields a proper divisor `M` with `M ∣ N`, `¬ q ∣ M` and a modular
  representation of level `M`. The parent then shows `M < N` (lines 129-130)
  and recurses `ih M hMlt (hcond.of_dvd hMN hM0) hmodM`.
- `level_lowering_at_p_of_conductorLevel` (line 134) is the Mazur-Ribet step:
  when `P.p ∣ N` it produces the same `M ∣ N ∧ ¬ P.p ∣ M ∧ ModularRepOfLevel M`,
  and the parent recurses the same way (lines 137-139).
- `dvd_two_of_squarefree_of_forall_prime_eq_two₁₆` (line 143) closes the base
  branch: with no odd prime `≠ p` left and `p ∤ N`, every prime dividing `N`
  is 2, so the squarefree level `N` divides 2, and the parent returns `M = N`
  itself (lines 142-143).

Each child is a good leaf: `level_lowering_odd_prime_of_conductorLevel` and
`level_lowering_at_p_of_conductorLevel` are self-contained statements (each a
one-line theorem) closed by `p2m_exact_reverting` delegating to a `solution`
proved elsewhere in the `P2MW` namespace, so the parent never unfolds them.
`dvd_two_of_squarefree_of_forall_prime_eq_two₁₆` is pure number theory closed
by its own short proof (`rcases`/`obtain` case analysis, `norm_num`, and
`Nat.squarefree_iff_prime_squarefree.mp` to rule out a second odd prime factor).
The only other fact the glue uses is `P.freyGaloisRep_isUnramifiedAt` (line 126),
an imported lemma feeding the odd-prime child its `hunr` hypothesis.

The `solution` context below (lines 163-170) shows the parent consumed as a
single `obtain` step, and finishes with `ModularForm.S2_Gamma0_eq_zero_of_dvd_two₁₆`
(lines 156-161, a separate lemma in the same file, downstream of this decomposition).

## Why it is good

1. The parent is closed by strong induction on `N` (line 118) whose three
   branches apply exactly the three named lemmas (lines 125, 134, 143), with no
   other sub-proof in the glue beyond the `M < N` descent and the induction
   hypothesis (`check`; parent permalink).
2. The project's blueprint says the same thing in words: "Then primes are
   removed one at a time … an odd q ≠ p … by
   `FreyPackage.level_lowering_odd_prime_of_conductorLevel` … p itself by
   `FreyPackage.level_lowering_at_p_of_conductorLevel`" (`author-statement`;
   PROOF-PATH.md, lines 71-74).
3. The glue is 33 lines, but the heavy lifting is pushed into leaves: two of
   the children are one-line theorems and the third is a 12-line self-contained
   proof, so the induction step is exactly the decomposition, not buried proof
   (`measurement`; see `shape` in entry.json).
4. The parent is a reusable interface: the public `solution` theorem consumes it
   as a single `obtain` step (lines 167-168) (`known-use`).
5. None of the three copied files contains `sorry`, `admit` or `axiom`, so the
   skeleton has no unclosed holes (`check`; grep at the pinned commit).

In my opinion the detail worth copying is that the induction *step* is stated
as a finite set of named lemmas, one per kind of prime factor, so the glue is
pure plumbing (`have`/`obtain` + `exact ih` + `by_cases`). That is precisely the
shape AutoDecompose should emit: a skeleton whose holes are the named lemmas.

## When to use it, and when not

Use a strong induction on the level (or any measure) when, for every kind of
prime that can divide the measure, you already have a lemma that lowers the
measure past that prime to a strictly smaller proper divisor (`M ∣ N` and
`M < N`). The induction then composes the lemmas for free, and the last case is
handled by a self-contained base lemma. This fits "remove one factor at a time
until a small set of allowed factors remains" arguments.

Avoid it when some removable prime has no covering lemma (the induction step
leaves a hole), when the lowering does not guarantee a strict decrease (the
induction hypothesis would not fire), or when the base case is entangled with
the induction step instead of being a separate statement. Note that here the
two level-lowering children are deep theorems (Ribet, Mazur-Ribet); the
induction only orchestrates them — it does not make the hard work go away.

## Consequences

The strong induction creates an obligation that every recursive call is on a
strictly smaller level, discharged in both recursive branches by `hMlt : M < N`
derived from `M ∣ N` and `M ≠ N` (lines 129-130 and 137-138). The two
`by_cases` splits create an exhaustiveness obligation over the prime divisors of
`N`, discharged only in the final branch by `by_contra`/`eq_or_ne` and the
`dvd_two_of_squarefree_of_forall_prime_eq_two₁₆` lemma (lines 144-148). If a
level-lowering lemma returned a divisor that was not strictly smaller, the
induction hypothesis would not apply and the recursion would not terminate; if
a prime kind were left uncovered, the last branch would be unprovable.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/anthropics/fermats-last-theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, under `Apache-2.0`; see the [source note](../../sources/flt-anthropic/SOURCE.md) for the licence text and attribution.
