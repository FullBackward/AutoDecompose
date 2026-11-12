# Calc-chain assembly of the invariant terminal value for IMO 2026 Q1

| | |
|---|---|
| Kind | instance |
| Move | calc-chain |
| Language | lean |
| Status | accepted |
| Source | [humanfia-hoa-qed](../../sources/humanfia-hoa-qed/SOURCE.md) at `1c918ec9a96c` |
| Licence | `Apache-2.0 AND CC-BY-4.0` |

## Intent

The headline statement of IMO 2026 Q1 — that the invariant `Mval B₀`, the
product over the primes dividing some entry of `p ^ gExp p B₀`, equals the
unique large entry `M` of any terminal board reachable from `B₀` — is proved
not by direct computation but by assembling seven already-proved lemmas
through two `calc` chains. The first chain matches the prime factors of
`B₀.prod` to those of `M`; the second rewrites the invariant product, prime by
prime, into `M`'s prime factorization.

## The decomposition

### parent `terminal_value_eq_Mval`: [`imo2026/gpt-5.6-solution/IMO2026Q1.lean` lines 419-451](https://github.com/humanfia/hoa-qed/blob/1c918ec9a96c7751ce9c283304e1aebd7ffb19a3/imo2026/gpt-5.6-solution/IMO2026Q1.lean#L419-L451) ([local copy](code/imo2026/gpt-5.6-solution/IMO2026Q1.lean))

```lean
theorem terminal_value_eq_Mval (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B')
    (M : ℕ) (hM : 1 < M) (hMem : M ∈ B') :
    M = Mval B₀ := by
  have hp₀ := initial_allPositive hB₀
  have hp' := reachable_allPositive hp₀ hreach
  have hu := statement_a_unique_large B₀ hB₀ B' hreach hterm
  have hprod := terminal_prod_eq_large hp' hu hM hMem
  have hpf : B₀.prod.primeFactors = M.primeFactors := by
    calc
      B₀.prod.primeFactors = B'.prod.primeFactors :=
        (reachable_prod_primeFactors hp₀ hreach).symm
      _ = M.primeFactors := by rw [hprod]
  unfold Mval
  rw [hpf]
  symm
  calc
    (∏ p ∈ M.primeFactors, p ^ gExp p B₀) =
        ∏ p ∈ M.primeFactors, p ^ padicValNat p M := by
      apply Finset.prod_congr rfl
      intro p hpMem
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
      congr 1
      calc
        gExp p B₀ = gExp p B' := (reachable_gExp hreach p hp).symm
        _ = padicValNat p M := terminal_gExp_eq_padicValNat hp' hu hM hMem
    _ = ∏ p ∈ M.primeFactors, p ^ M.factorization p := by
      apply Finset.prod_congr rfl
      intro p hpMem
      rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hpMem)]
    _ = M.factorization.prod (fun p e => p ^ e) :=
      (Nat.prod_factorization_eq_prod_primeFactors (n := M) (fun p e => p ^ e)).symm
    _ = M := Nat.prod_factorization_pow_eq_self (by omega)
```

### child `initial_allPositive`: [`imo2026/gpt-5.6-solution/IMO2026Q1.lean` lines 138-140](https://github.com/humanfia/hoa-qed/blob/1c918ec9a96c7751ce9c283304e1aebd7ffb19a3/imo2026/gpt-5.6-solution/IMO2026Q1.lean#L138-L140) ([local copy](code/imo2026/gpt-5.6-solution/IMO2026Q1.lean))

```lean
lemma initial_allPositive {B : Board} (hB : IsInitial B) : AllPositive B := by
  intro a ha
  exact (hB.2 a ha).trans' Nat.zero_lt_one
```

### child `reachable_allPositive`: [`imo2026/gpt-5.6-solution/IMO2026Q1.lean` lines 209-213](https://github.com/humanfia/hoa-qed/blob/1c918ec9a96c7751ce9c283304e1aebd7ffb19a3/imo2026/gpt-5.6-solution/IMO2026Q1.lean#L209-L213) ([local copy](code/imo2026/gpt-5.6-solution/IMO2026Q1.lean))

```lean
lemma reachable_allPositive {B B' : Board} (hB : AllPositive B)
    (hreach : Reachable B B') : AllPositive B' := by
  induction hreach with
  | refl => exact hB
  | tail _ hmove ih => exact move_allPositive ih hmove
```

### child `statement_a_unique_large`: [`imo2026/gpt-5.6-solution/IMO2026Q1.lean` lines 373-382](https://github.com/humanfia/hoa-qed/blob/1c918ec9a96c7751ce9c283304e1aebd7ffb19a3/imo2026/gpt-5.6-solution/IMO2026Q1.lean#L373-L382) ([local copy](code/imo2026/gpt-5.6-solution/IMO2026Q1.lean))

```lean
theorem statement_a_unique_large (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B') :
    HasUniqueLarge B' := by
  obtain ⟨a, ha, ha1⟩ := reachable_hasLarge hB₀ hreach
  have hmem : a ∈ B'.filter (fun x => 1 < x) := Multiset.mem_filter.mpr ⟨ha, ha1⟩
  have hpos : 0 < Multiset.card (B'.filter (fun x => 1 < x)) :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨a, hmem⟩
  exact Nat.eq_one_of_dvd_one (by
    rw [Nat.dvd_one]
    exact Nat.le_antisymm hterm hpos)
```

### child `terminal_prod_eq_large`: [`imo2026/gpt-5.6-solution/IMO2026Q1.lean` lines 363-369](https://github.com/humanfia/hoa-qed/blob/1c918ec9a96c7751ce9c283304e1aebd7ffb19a3/imo2026/gpt-5.6-solution/IMO2026Q1.lean#L363-L369) ([local copy](code/imo2026/gpt-5.6-solution/IMO2026Q1.lean))

```lean
lemma terminal_prod_eq_large {B : Board} (hpos : AllPositive B)
    (huniq : HasUniqueLarge B) {M : ℕ} (hM : 1 < M) (hMem : M ∈ B) :
    B.prod = M := by
  have hone := terminal_erase_all_one hpos huniq hM hMem
  have htail : (B.erase M).prod = 1 := Multiset.prod_eq_one hone
  rw [← Multiset.cons_erase hMem]
  simp [htail]
```

### child `reachable_prod_primeFactors`: [`imo2026/gpt-5.6-solution/IMO2026Q1.lean` lines 354-361](https://github.com/humanfia/hoa-qed/blob/1c918ec9a96c7751ce9c283304e1aebd7ffb19a3/imo2026/gpt-5.6-solution/IMO2026Q1.lean#L354-L361) ([local copy](code/imo2026/gpt-5.6-solution/IMO2026Q1.lean))

```lean
lemma reachable_prod_primeFactors {B B' : Board} (hB : AllPositive B)
    (hreach : Reachable B B') : B'.prod.primeFactors = B.prod.primeFactors := by
  have hpair : AllPositive B' ∧ B'.prod.primeFactors = B.prod.primeFactors := by
    induction hreach with
    | refl => exact ⟨hB, rfl⟩
    | tail _ hmove ih =>
        exact ⟨move_allPositive ih.1 hmove, (move_prod_primeFactors ih.1 hmove).trans ih.2⟩
  exact hpair.2
```

### child `reachable_gExp`: [`imo2026/gpt-5.6-solution/IMO2026Q1.lean` lines 272-276](https://github.com/humanfia/hoa-qed/blob/1c918ec9a96c7751ce9c283304e1aebd7ffb19a3/imo2026/gpt-5.6-solution/IMO2026Q1.lean#L272-L276) ([local copy](code/imo2026/gpt-5.6-solution/IMO2026Q1.lean))

```lean
lemma reachable_gExp {B B' : Board} (hreach : Reachable B B') (p : ℕ) (hp : p.Prime) :
    gExp p B' = gExp p B := by
  induction hreach with
  | refl => rfl
  | tail _ hmove ih => exact (move_gExp hmove p hp).trans ih
```

### child `terminal_gExp_eq_padicValNat`: [`imo2026/gpt-5.6-solution/IMO2026Q1.lean` lines 305-317](https://github.com/humanfia/hoa-qed/blob/1c918ec9a96c7751ce9c283304e1aebd7ffb19a3/imo2026/gpt-5.6-solution/IMO2026Q1.lean#L305-L317) ([local copy](code/imo2026/gpt-5.6-solution/IMO2026Q1.lean))

```lean
lemma terminal_gExp_eq_padicValNat {B : Board} (hpos : AllPositive B)
    (huniq : HasUniqueLarge B) {M p : ℕ} (hM : 1 < M) (hMem : M ∈ B) :
    gExp p B = padicValNat p M := by
  have hone := terminal_erase_all_one hpos huniq hM hMem
  have htail : ((B.erase M).map fun x => padicValNat p x).gcd = 0 := by
    apply (Multiset.gcd_eq_zero_iff _).mpr
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
    rw [hone a ha]
    exact padicValNat_one_right p
  unfold gExp
  rw [← Multiset.cons_erase hMem]
  simp [htail]
```

How the parts fit. The glue `terminal_value_eq_Mval` first fixes its four
witness facts by `have` (lines 423-426): `initial_allPositive hB₀` gives that
`B₀` is all-positive, `reachable_allPositive` lifts that to `B'`,
`statement_a_unique_large` gives that `B'` has a unique large entry, and
`terminal_prod_eq_large` combines those to conclude `B'.prod = M`. Then two
`calc` chains do the real work:

- the first (lines 429-433) proves `hpf : B₀.prod.primeFactors =
  M.primeFactors`, linking `reachable_prod_primeFactors` (prime factors are
  invariant along a reach) with `terminal_prod_eq_large` (the product equals
  `M`);
- the second (lines 435-451) proves `Mval B₀ = M`. After `unfold Mval` and
  `rw [hpf]`, its first link is a `Finset.prod_congr` whose per-prime
  justification is an inner `calc` (lines 442-444) closing `gExp p B₀ =
  padicValNat p M` from `reachable_gExp` (gExp is invariant along a reach) and
  `terminal_gExp_eq_padicValNat` (at a terminal board gExp equals the
  valuation of the unique large entry). The remaining links are the definition
  of `Nat.factorization` and the reconstruction
  `Nat.prod_factorization_pow_eq_self (by omega)`.

Lemma graph (each child and the project lemmas it names):

```
terminal_value_eq_Mval
  ├─ initial_allPositive            (leaf: hB.2 .trans' zero_lt_one)
  ├─ reachable_allPositive          → move_allPositive
  ├─ statement_a_unique_large       → reachable_hasLarge → {initial_hasLarge, move_hasLarge}
  ├─ terminal_prod_eq_large         → terminal_erase_all_one → terminal_filter_eq_singleton
  ├─ reachable_prod_primeFactors    → {move_allPositive, move_prod_primeFactors}
  ├─ reachable_gExp                 → move_gExp → padicValNat_lcm_div_gcd → padicValNat_lcm / padicValNat_gcd
  └─ terminal_gExp_eq_padicValNat   → terminal_erase_all_one → terminal_filter_eq_singleton
```

Why each child is a good leaf:

- `initial_allPositive` is a one-liner that unfolds `IsInitial` and
  `AllPositive`; it closes on its own with no named lemma.
- `reachable_allPositive`, `reachable_prod_primeFactors` and `reachable_gExp`
  are each a one-step induction over `Reachable`; the step is exactly the
  matching single-move lemma (`move_allPositive`, `move_prod_primeFactors`,
  `move_gExp`), so the reach closure is trivial once the one-move fact is
  proved. Each closes from named siblings only.
- `statement_a_unique_large` is the second half of problem statement (a),
  closed from `reachable_hasLarge` plus the arithmetic of `card`/`filter`.
- `terminal_prod_eq_large` and `terminal_gExp_eq_padicValNat` are the two
  "collapse a terminal board to its one large entry" lemmas; each reduces the
  whole board to `M` via `terminal_erase_all_one` (every erased entry is `1`),
  then `simp`. Each reads on its own and closes from one sibling.

## Why it is good

1. The parent closes from exactly the seven named project lemmas plus two
   `calc` chains, and the file contains no `sorry`, `admit` or `axiom` — the
   proof is complete (check; `grep` over the copied file returns nothing, and
   the `have`/`calc` assembly is lines 419-451).
2. The file is built by the project's CI on pushes to main
   (`.github/workflows/lean.yml`, step "Check IMO 2026 solutions" runs
   `lake env lean` on each `../gpt-5.6-solution/*.lean`) — check.
3. The shape: 7 direct lemmas, glue of 33 lines, and the longest checked chain
   of project lemmas below the main theorem has depth 4
   (`terminal_value_eq_Mval → reachable_gExp → move_gExp →
   padicValNat_lcm_div_gcd → padicValNat_lcm`) — measurement.
4. The authors state the intent in a doc comment: "For any terminal board `B'`
   reachable from an initial board `B₀`, the unique entry `M > 1` of `B'`
   equals the invariant `Mval B₀`" (author-statement, lines 416-418).
5. The same `calc`-over-`gExp` move is reused in `statement_b_invariance`
   (lines 399-404), chaining `padicValNat p M = gExp p B₁ = gExp p B₀ =
   gExp p B₂ = padicValNat p N` from the same two lemmas (known-use).

In my opinion the detail worth copying is the inner `calc` under
`Finset.prod_congr`: the per-prime equality is itself a two-link chain, so
every obligation of the whole proof is either a named lemma or a single
transitivity step.

## When to use it, and when not

Use it when a goal is an equality between a "structural" invariant (a product
over prime factors, a sum over a basis, a norm) and a value already
characterised by two lemmas, and each link of the chain is an already-proved
named lemma, so transitivity is checked by the chain itself. It is the natural
form when the invariant is defined as a product over `primeFactors` and the
target is recovered through `Nat.prod_factorization_pow_eq_self`.

Avoid it when a link is not already a lemma and must be proved inline with a
nontrivial argument — that step is the real content and should be extracted as
its own child before the chain is written. Avoid it too when a single
`rw`/`simp` closes the goal, or when the two sides have different types and
the `calc` cannot type-check a chain of `=`.

## Consequences

The move creates no new goals of its own: every `calc` link is a transitive
step justified by a named lemma or by a `congr 1` / `Finset.prod_congr` under a
product, so the obligations are pushed onto the lemmas (prime factors
invariant along a reach; a terminal board collapses to its one large entry).
The final link `M.factorization.prod (fun p e => p ^ e) = M` needs
`Nat.prod_factorization_pow_eq_self (by omega)`, and that `omega` obligation
consumes `hM : 1 < M`; without `M > 1` the chain's last link does not close.
If a per-prime link is not already a lemma, the inner `calc` under
`prod_congr` must carry the whole argument and the "each link is a named
lemma" property breaks.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/lean.yml, step 'Check IMO 2026 solutions', runs 'lake env lean' over ../gpt-5.6-solution/*.lean on push to main; pinned commit 1c918ec is on default branch main | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 1c918ec9a96c7751ce9c283304e1aebd7ffb19a3 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | grep over the copied file for sorry/admit/axiom/Admitted/sorryAx returned no matches; parent proof L419-L451 uses exactly the 7 project lemmas (initial_allPositive L423, reachable_allPositive L424, statement_a_unique_large L425, terminal_prod_eq_large L426, reachable_prod_primeFactors L430, reachable_gExp L443, terminal_gExp_eq_padicValNat L444) and two top-level calc blocks (L428 and L435) | verifier |
| 2 | verified | fetched .github/workflows/lean.yml this session: on push, branches [main]; step 'Check IMO 2026 solutions' (working-directory imo2026/base) runs 'lake env lean' over every ../gpt-5.6-solution/*.lean and ../kimi-solution/*.lean, covering IMO2026Q1.lean | verifier |
| 3 | verified | counted 7 direct lemma applications at lines 423,424,425,426,430,443,444; glue lines 419-451 inclusive = 33; longest project-lemma chain has 4 links: terminal_value_eq_Mval(419) -> reachable_gExp(443) -> move_gExp(276) -> padicValNat_lcm_div_gcd(263) -> padicValNat_lcm(248) | verifier |
| 4 | verified | doc comment L416-L418 reads: 'For any terminal board B' reachable from an initial board B0, the unique entry M > 1 of B' equals the invariant Mval B0.' | verifier |
| 5 | verified | statement_b_invariance L399-L404 calc chains padicValNat p M = gExp p B1 = gExp p B0 = gExp p B2 = padicValNat p N via terminal_gExp_eq_padicValNat and reachable_gExp (same two lemmas) | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent terminal_value_eq_Mval (L419-451) is a calc-chain assembly closing from exactly the 7 named project lemmas listed as children: initial_allPositive (L423), reachable_allPositive (L424), statement_a_unique_large (L425), terminal_prod_eq_large (L426), reachable_prod_primeFactors (L430), reachable_gExp (L443), terminal_gExp_eq_padicValNat (L444); no sorry/admit/axiom in the copied file so it closes. Each child's statement and closed_by match the copied code verbatim (site line ranges match: 138-140, 209-213, 373-382, 363-369, 354-361, 272-276, 305-317). Shape numbers are right: direct_lemmas=7, glue_lines=33 (419-451), child_lines=[3,5,10,7,8,5,13] matching each site span, and depth=4 confirmed by the chain terminal_value_eq_Mval->reachable_gExp(L443)->move_gExp(L276)->padicValNat_lcm_div_gcd(L263)->padicValNat_lcm(L248). | reviewer-correctness |
| generality | accept | Move generalises beyond the example: README 'When to use' frames it as an equality between a structural invariant (product over prime factors, a sum over a basis, a norm) and a value already characterised by two lemmas, and the general shape (value M = product/valuation characterised by one prime-factor lemma and one gExp/valuation lemma) is stated in applicability.use_when with a genuine known-use (statement_b_invariance, lines 399-404, reusing reachable_gExp and terminal_gExp_eq_padicValNat). 'When not to use' is honest and specific (inline nontrivial link -> extract as child first; single rw/simp suffices; mismatched types break the = chain). Consequences are honest and specific: the final link needs Nat.prod_factorization_pow_eq_self (by omega) consuming hM : 1 < M, and the stated failure mode that a non-lemma per-prime link collapses the 'each link is a named lemma' property. 'Why each child is a good leaf' explicitly answers the bounded-prover question: one-liner unfolding, one-step induction with trivial step matching a single-move lemma, closes from named siblings only, or collapses to one entry via terminal_erase_all_one then simp. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are mutually consistent and traceable. Commit 1c918ec9a96c7751ce9c283304e1aebd7ffb19a3 is recorded identically in entry.json (source, files, sites), README, SOURCE.md and source.json, and is on the default branch main; check_provenance.py re-run this session confirms the copied file is byte-identical at that commit. The copied file's sha256 (7e296f9f...) and 21031 bytes match entry.json files[]. Licence Apache-2.0 AND CC-BY-4.0 matches source.json, SOURCE.md and the upstream NOTICE (code/Lean proofs under Apache-2.0, natural-language write-ups under CC-BY-4.0); upstream-LICENSE (Apache 2.0), upstream-LICENSE-CC-BY-4.0 (CC BY Attribution 4.0 International) and upstream-NOTICE are present and match the recorded licence files. Every permalink uses the same commit and path imo2026/gpt-5.6-solution/IMO2026Q1.lean, and the README 'Source and licence' note links the source note correctly. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/humanfia/hoa-qed at commit `1c918ec9a96c7751ce9c283304e1aebd7ffb19a3`, under `Apache-2.0 AND CC-BY-4.0`; see the [source note](../../sources/humanfia-hoa-qed/SOURCE.md) for the licence text and attribution.
