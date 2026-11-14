# Abel-Ruffini: instantiate the general non-solvability statement at the quintic Φ 4 2

| | |
|---|---|
| Kind | instance |
| Move | generalise-then-instantiate |
| Language | lean |
| Status | accepted |
| Source | [mathlib4](../../sources/mathlib4/SOURCE.md) at `e1545ebed975` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T10:53:38Z |

## Intent

The Abel-Ruffini theorem — there is an algebraic complex number not solvable by
radicals — is proved by *instantiating* a general non-solvability statement
`not_solvable_by_rad`, already proved for any `p, a, b` under the Eisenstein
conditions, at the concrete quintic `Φ ℚ 4 2`. The parent proof does no new
mathematics: it finds a root (using `degree_Phi`), transfers it across the base
change `ℚ → ℂ` (using `map_Phi`), makes it algebraic (using `monic_Phi`), and
calls the instantiation lemma `not_solvable_by_rad'`.

## The decomposition

### parent `exists_not_solvable_by_rad`: [`Archive/Wiedijk100Theorems/AbelRuffini.lean` lines 169-173](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/AbelRuffini.lean#L169-L173) ([local copy](code/Archive/Wiedijk100Theorems/AbelRuffini.lean))

```lean
/-- **Abel-Ruffini Theorem** -/
theorem exists_not_solvable_by_rad : ∃ x : ℂ, IsAlgebraic ℚ x ∧ x ∉ solvableByRad ℚ ℂ := by
  obtain ⟨x, hx⟩ := (IsAlgClosed.splits (Φ ℂ 4 2)).exists_eval_eq_zero (by simp [degree_Phi])
  rw [← map_Phi 4 2 (algebraMap ℚ ℂ), eval_map] at hx
  exact ⟨x, ⟨Φ ℚ 4 2, (monic_Phi 4 2).ne_zero, hx⟩, not_solvable_by_rad' x hx⟩
```

### child `not_solvable_by_rad'`: [`Archive/Wiedijk100Theorems/AbelRuffini.lean` lines 166-167](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/AbelRuffini.lean#L166-L167) ([local copy](code/Archive/Wiedijk100Theorems/AbelRuffini.lean))

```lean
theorem not_solvable_by_rad' (x : ℂ) (hx : aeval x (Φ ℚ 4 2) = 0) : x ∉ solvableByRad ℚ ℂ := by
  apply not_solvable_by_rad 4 2 2 x hx <;> decide
```

### child `map_Phi`: [`Archive/Wiedijk100Theorems/AbelRuffini.lean` lines 47-48](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/AbelRuffini.lean#L47-L48) ([local copy](code/Archive/Wiedijk100Theorems/AbelRuffini.lean))

```lean
@[simp]
theorem map_Phi {S : Type*} [CommRing S] (f : R →+* S) : (Φ R a b).map f = Φ S a b := by simp [Φ]
```

### child `monic_Phi`: [`Archive/Wiedijk100Theorems/AbelRuffini.lean` lines 72-73](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/AbelRuffini.lean#L72-L73) ([local copy](code/Archive/Wiedijk100Theorems/AbelRuffini.lean))

```lean
theorem monic_Phi : (Φ R a b).Monic :=
  leadingCoeff_Phi a b
```

### child `degree_Phi`: [`Archive/Wiedijk100Theorems/AbelRuffini.lean` lines 59-64](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/AbelRuffini.lean#L59-L64) ([local copy](code/Archive/Wiedijk100Theorems/AbelRuffini.lean))

```lean
theorem degree_Phi : (Φ R a b).degree = ((5 : ℕ) : WithBot ℕ) := by
  suffices degree (X ^ 5 - C (a : R) * X) = ((5 : ℕ) : WithBot ℕ) by
    rwa [Φ, degree_add_eq_left_of_degree_lt]
    convert! (degree_C_le (R := R)).trans_lt (WithBot.coe_lt_coe.mpr (show 0 < 5 by simp))
  rw [degree_sub_eq_left_of_degree_lt] <;> rw [degree_X_pow]
  exact (degree_C_mul_X_le (a : R)).trans_lt (WithBot.coe_lt_coe.mpr (show 1 < 5 by simp))
```

### context `not_solvable_by_rad`: [`Archive/Wiedijk100Theorems/AbelRuffini.lean` lines 157-164](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/AbelRuffini.lean#L157-L164) ([local copy](code/Archive/Wiedijk100Theorems/AbelRuffini.lean))

```lean
theorem not_solvable_by_rad (p : ℕ) (x : ℂ) (hx : aeval x (Φ ℚ a b) = 0) (hab : b < a)
    (hp : p.Prime) (hpa : p ∣ a) (hpb : p ∣ b) (hp2b : ¬p ^ 2 ∣ b) : x ∉ solvableByRad ℚ ℂ := by
  have h_irred := irreducible_Phi a b p hp hpa hpb hp2b
  apply mt (isSolvable_gal_of_irreducible · h_irred hx)
  intro h
  refine Equiv.Perm.not_isSolvable _ (le_of_eq ?_)
    (Group.isSolvable_of_surjective (gal_Phi a b hab h_irred).2)
  rw_mod_cast [Cardinal.mk_fintype, complex_roots_Phi a b h_irred.separable]
```

How the parts fit. The headline theorem `exists_not_solvable_by_rad` assembles
four named lemmas, each closing one obligation of the existential goal:

```
exists_not_solvable_by_rad  (parent, the glue: 3 tactic lines)
├── degree_Phi         — degree 5, so Φ ℂ 4 2 is non-constant and has a root
├── map_Phi           — base change ℚ → ℂ, so the complex root is a root of Φ ℚ 4 2
├── monic_Phi         — (Φ ℚ 4 2).ne_zero, making the witness algebraic
└── not_solvable_by_rad'   — the non-solvability, by instantiating the general statement
    └── not_solvable_by_rad   (context) — the general statement over p, a, b
        ├── irreducible_Phi     — Eisenstein irreducibility of Φ ℚ a b
        │   ├── map_Phi, leadingCoeff_Phi, degree_Phi, coeff_zero_Phi, monic_Phi
        └── gal_Phi             — full Galois group, via complex_roots_Phi,
            └── complex_roots_Phi   real_roots_Phi_le/ge
                └── natDegree_Phi
                    └── degree_Phi
```

The move is *generalise-then-instantiate* in two steps. The general statement
`not_solvable_by_rad` is proved once for any `p, a, b` satisfying the Eisenstein
conditions; `not_solvable_by_rad'` then specialises it to `p = 2, a = 4, b = 2`
and closes the side conditions (`2.Prime`, `2 ∣ 4`, `2 ∣ 2`, `¬4 ∣ 2`, `2 < 4`)
with a single `<;> decide`. The parent specialises once more, at a specific root
`x` of `Φ ℚ 4 2`.

Why each child is a good leaf. `map_Phi` and `monic_Phi` close on their own
(`by simp [Φ]`, and `leadingCoeff_Phi a b` — a one-line sibling fact). `degree_Phi`
is the only child whose proof is more than a line, but it is still a
self-contained degree computation (`suffices` plus two `rw`). `not_solvable_by_rad'`
closes because the general statement and `decide` exist; it is the one child that
carries the instantiation itself, and it is the child the parent actually cites
for the non-solvability conclusion.

## Why it is good

1. The glue cites the instantiation lemma: `not_solvable_by_rad'` occurs in the
   parent site (line 173) — the non-solvability conclusion is imported, not
   re-proved (`check`, `cites(parent, not_solvable_by_rad')`).
2. The glue is 5 lines long, of which 3 are tactic lines (lines 171-173); the
   whole argument lives in the lemmas it cites (`check`, `lines(parent, 5)`).
3. The largest child, `degree_Phi`, is 6 lines including its declaration
   (`check`, `lines(degree_Phi, 6)`).
4. Below the main theorem the longest chain of project lemmas is 7 links:
   `exists_not_solvable_by_rad → not_solvable_by_rad' → not_solvable_by_rad →
   irreducible_Phi → monic_Phi → leadingCoeff_Phi → natDegree_Phi → degree_Phi`,
   each link a use in the copied file (`measurement`, lines 173, 167, 159, 94,
   73, 70, 67).
5. The module comment states the same plan: three general ingredients
   (`isSolvable_gal_of_irreducible`, `galActionHom_bijective_of_prime_degree'`,
   `Equiv.Perm.not_solvable`), then "all that remains is the construction of a
   specific polynomial satisfying the conditions of
   `galActionHom_bijective_of_prime_degree'`, which is done in this file"
   (`author-statement`, lines 20-28).

In my opinion the two-level instantiation is the detail worth copying: the
general statement is not instantiated directly at the concrete root, but through
a thin named lemma `not_solvable_by_rad'` whose whole job is to fix `p, a, b` and
let `decide` discharge the side conditions, so the headline proof stays at three
lines.

## When to use it, and when not

Use it when the general statement is already proved for a parameterised family
with side conditions, and the concrete case only needs (a) an instantiation
lemma that closes the side conditions by computation (`decide`, `norm_num`) and
(b) coefficient lemmas establishing degree, monicity and base change — so the
parent proof is pure instantiation. Avoid it when the side conditions cannot be
discharged by computation (then the instantiation lemma is itself substantial
work), when the concrete object is not literally an instance of the general
statement (then the connecting lemmas stop being `simp`/`rw`), or when the
general statement is not already proved — in that case proving it is the real
content, not the instantiation.

## Consequences

The instantiation creates four obligations beyond the headline statement: (1) a
complex root of `Φ ℂ 4 2` exists, discharged by `IsAlgClosed.splits` together
with `degree_Phi` (degree 5, so non-constant); (2) that root is algebraic over
`ℚ`, discharged by `monic_Phi` giving `(Φ ℚ 4 2).ne_zero`; (3) the root is
rational-coefficient, transferred through `map_Phi` across the base change
`ℚ → ℂ`; (4) the non-solvability comes from `not_solvable_by_rad'`, which must
discharge the general statement's Eisenstein side conditions at `p = 2, a = 4,
b = 2` by `decide`. Failure modes: if the concrete `a, b` fail a side condition,
`decide` fails and the instantiation lemma needs a real argument; if the
polynomial is not monic, the `IsAlgebraic` witness loses its `.ne_zero`; if the
base change is in the wrong direction, `map_Phi` does not apply.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml (delegates to build_template.yml) builds the Archive target via 'lake-build-with-retry.sh Archive Counterexamples Wanted'; commit e1545ebed97594477bbd88b2fe948ffce56e5af2 is on default branch master (compare master...e1545ebed: behind_by 34, ahead_by 0) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: not_solvable_by_rad'@Archive/Wiedijk100Theorems/AbelRuffini.lean:173, map_Phi@Archive/Wiedijk100Theorems/AbelRuffini.lean:172, monic_Phi@Archive/Wiedijk100Theorems/AbelRuffini.lean:173, degree_Phi@Archive/Wiedijk100Theorems/AbelRuffini.lean:171; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at e1545ebed97594477bbd88b2fe948ffce56e5af2 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, not_solvable_by_rad') -> cites: not_solvable_by_rad' occurs at Archive/Wiedijk100Theorems/AbelRuffini.lean:173 | check_claims.py |
| 2 | verified | lines(parent, 5) -> lines: site parent has 5 lines | check_claims.py |
| 3 | verified | lines(degree_Phi, 6) -> lines: site degree_Phi has 6 lines | check_claims.py |
| 4 | verified | Read copied Archive/Wiedijk100Theorems/AbelRuffini.lean: chain of 7 links confirmed at cited lines: 173 'not_solvable_by_rad' x hx' in exists_not_solvable_by_rad; 167 'apply not_solvable_by_rad 4 2 2 x hx'; 159 'have h_irred := irreducible_Phi ...'; 94 'all_goals exact Monic.isPrimitive (monic_Phi a b)'; 73 'leadingCoeff_Phi a b' (body of monic_Phi); 70 'rw [Polynomial.leadingCoeff, natDegree_Phi, coeff_five_Phi]' (body of leadingCoeff_Phi); 67 'natDegree_eq_of_degree_eq_some (degree_Phi a b)' (body of natDegree_Phi) | verifier |
| 5 | verified | Read module comment lines 15-28 of copied Archive/Wiedijk100Theorems/AbelRuffini.lean: it lists the three ingredients isSolvable_gal_of_irreducible, galActionHom_bijective_of_prime_degree', Equiv.Perm.not_solvable and states 'Then all that remains is the construction of a specific polynomial satisfying the conditions of galActionHom_bijective_of_prime_degree', which is done in this file' | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent exists_not_solvable_by_rad (lines 169-173) cites exactly the four children: degree_Phi (L171), map_Phi (L172), monic_Phi (L173), not_solvable_by_rad' (L173); no other project lemma is used directly. Each child's statement and closed_by match the copied file verbatim (not_solvable_by_rad'=apply not_solvable_by_rad 4 2 2 x hx <;> decide; map_Phi=by simp [Φ]; monic_Phi=leadingCoeff_Phi a b; degree_Phi=suffices+rwa/rw, paraphrase of a 6-line proof). The parent's exact term closes ∃x: witness x with ⟨Φ ℚ 4 2, (monic_Phi 4 2).ne_zero, hx⟩ for IsAlgebraic and not_solvable_by_rad' x hx for non-solvability. Shape numbers correct: direct_lemmas=4, glue_lines=5 (site 169-173), child_lines=[2,2,2,6] (not_solvable_by_rad' 166-167, map_Phi 47-48, monic_Phi 72-73, degree_Phi 59-64), depth=7 (chain exists_not_solvable_by_rad→not_solvable_by_rad'→not_solvable_by_rad→irreducible_Phi→monic_Phi→leadingCoeff_Phi→natDegree_Phi→degree_Phi, uses at L173/167/159/94/73/70/67 all present). | reviewer-correctness |
| generality | accept | Move is stated beyond the example: applicability/goal_shape abstracts to 'general statement already proved over a parameterised family + instantiation lemma closing side conditions by computation + connecting (degree/monicity/base-change) facts', and use_when restates it role-neutrally. 'When not to use' is honest and specific (side conditions not decidable -> instantiation becomes substantial; concrete object not literally an instance -> connecting lemmas stop being simp/rw; general statement unproved -> real content is the proof). Consequences list 4 obligations, each verified against parent lines 171-173, plus concrete failure modes (decide fails, .ne_zero lost if non-monic, map_Phi wrong direction). 'Why each child is a good leaf' says what makes them good bounded-prover leaves: one-line closable by simp/leadingCoeff_Phi, degree_Phi self-contained, not_solvable_by_rad' closes via existing general statement + decide. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are consistent and traceable: every permalink in entry.json uses commit e1545ebed97594477bbd88b2fe948ffce56e5af2, which matches entry.json source.commit, sources/mathlib4/source.json commit, and SOURCE.md pinned commit; licence Apache-2.0 is recorded identically in entry.json source.licence, SOURCE.md, and the upstream-LICENSE file (Apache 2.0 text). check_provenance.py reports 1 file byte-identical at the commit; the copied AbelRuffini.lean is 8284 bytes and sha256 89347cbe..., both matching entry.json. README 'Source and licence' points to SOURCE.md which carries the licence text and attribution. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover-community/mathlib4 at commit `e1545ebed97594477bbd88b2fe948ffce56e5af2`, under `Apache-2.0`; see the [source note](../../sources/mathlib4/SOURCE.md) for the licence text and attribution.
