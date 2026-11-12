# Case split on p dividing a*b*c combines caseI and caseII into FLT for regular primes

| | |
|---|---|
| Kind | instance |
| Move | case-split |
| Language | lean |
| Status | accepted |
| Source | [flt-regular](../../sources/flt-regular/SOURCE.md) at `83f477ccc8ce` |
| Licence | `Apache-2.0` |

## Intent

Prove Fermat's Last Theorem at every odd regular prime exponent by reducing
the goal to a coprime integer solution and splitting on whether the prime `p`
divides `a * b * c`; each branch closes by one application of a project theorem
(`caseII` for the divisible case, `caseI` for the non-divisible case).

## The decomposition

### parent `flt_regular`: [`FltRegular/FltRegular.lean` lines 21-28](https://github.com/leanprover-community/flt-regular/blob/83f477ccc8cef9fd9a022b90d87aed49368e7bbd/FltRegular/FltRegular.lean#L21-L28) ([local copy](code/FltRegular/FltRegular.lean))

```lean
theorem flt_regular {p : ℕ} [Fact p.Prime] (hreg : IsRegularPrime p) (hodd : p ≠ 2) :
    FermatLastTheoremFor p := by
  rw [fermatLastTheoremFor_iff_int]
  apply fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
  intro a b c ha hb hc hgcd
  by_cases hcase : ↑p ∣ a * b * c
  · exact caseII hreg hodd (mul_ne_zero (mul_ne_zero ha hb) hc) hgcd hcase
  · exact caseI hreg hcase
```

### child `caseII`: [`FltRegular/CaseII/Statement.lean` lines 78-100](https://github.com/leanprover-community/flt-regular/blob/83f477ccc8cef9fd9a022b90d87aed49368e7bbd/FltRegular/CaseII/Statement.lean#L78-L100) ([local copy](code/FltRegular/CaseII/Statement.lean))

```lean
theorem caseII {a b c : ℤ} {p : ℕ} [hpri : Fact p.Prime] (hreg : IsRegularPrime p)
    (hodd : p ≠ 2) (hprod : a * b * c ≠ 0)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) (caseII : ↑p ∣ a * b * c) :
    a ^ p + b ^ p ≠ c ^ p := by
  intro e
  simp only [ne_eq, mul_eq_zero, not_or] at hprod
  obtain ⟨⟨a0, b0⟩, c0⟩ := hprod
  have hodd' := Nat.Prime.odd_of_ne_two hpri.out hodd
  obtain hab | hc := (Nat.prime_iff_prime_int.mp hpri.out).dvd_or_dvd caseII
  · obtain ha | hb := (Nat.prime_iff_prime_int.mp hpri.out).dvd_or_dvd hab
    · refine not_exists_Int_solution' hreg hodd ⟨b, -c, -a, ?_, ?_, ?_, ?_⟩
      · simp only [← hgcd, Finset.gcd_insert, id_eq, ← Int.coe_gcd, Int.neg_gcd,
          ← LawfulSingleton.insert_empty_eq, Finset.gcd_empty, Int.gcd_left_comm _ a]
      · rwa [dvd_neg]
      · rwa [ne_eq, neg_eq_zero]
      · simp [hodd'.neg_pow, ← e]
    · refine not_exists_Int_solution' hreg hodd ⟨-c, a, -b, ?_, ?_, ?_, ?_⟩
      · simp only [← hgcd, Finset.gcd_insert, id_eq, ← Int.coe_gcd, Int.neg_gcd,
          ← LawfulSingleton.insert_empty_eq, Finset.gcd_empty, Int.gcd_left_comm _ c]
      · rwa [dvd_neg]
      · rwa [ne_eq, neg_eq_zero]
      · simp [hodd'.neg_pow, ← e]
  · exact not_exists_Int_solution' hreg hodd ⟨a, b, c, hgcd, hc, c0, e⟩
```

### child `caseI`: [`FltRegular/CaseI/Statement.lean` lines 260-263](https://github.com/leanprover-community/flt-regular/blob/83f477ccc8cef9fd9a022b90d87aed49368e7bbd/FltRegular/CaseI/Statement.lean#L260-L263) ([local copy](code/FltRegular/CaseI/Statement.lean))

```lean
theorem caseI {a b c : ℤ} {p : ℕ} [Fact p.Prime] (hreg : IsRegularPrime p)
    (caseI : ¬↑p ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p :=
  FltRegular.CaseI.may_assume
    (fun _ _ _ _ _ hreg hp5 hunit hxy hI h ↦ caseI_easier hreg hp5 hunit hxy hI h) hreg caseI
```

How the parts fit. The parent first normalises the goal with two Mathlib
lemmas: `rw [fermatLastTheoremFor_iff_int]` rewrites `FermatLastTheoremFor p`
into the equivalent statement over the integers, and `apply
fermatLastTheoremWith_of_fermatLastTheoremWith_coprime` further reduces it to
`a ^ p + b ^ p ≠ c ^ p` for a coprime integer triple, which `intro a b c ha hb
hc hgcd` binds (lines 23-25). Only then does the split happen: `by_cases hcase :
↑p ∣ a * b * c` (line 26) creates two goals, each closed by a single `exact`
naming a project theorem written for this purpose — `caseII` when `p` divides
the product (line 27), `caseI` when it does not (line 28). The two branches
carry different hypotheses: `caseII` needs `a * b * c ≠ 0` and the coprime-gcd
condition, so line 27 supplies `mul_ne_zero (mul_ne_zero ha hb) hc` and `hgcd`,
while line 28 passes only `hreg` and the non-divisibility fact.

Lemma graph (which lemma uses which):

```
flt_regular  (FltRegular.lean:21-28)
├── caseII   (CaseII/Statement.lean:78)          p ∣ a*b*c branch
│   └── not_exists_Int_solution' (:63)
│       └── not_exists_Int_solution  (:48)
│           └── not_exists_solution' (:34)
│               └── not_exists_solution (:22)
│                   └── one_le_m, exists_solution' (CaseII/InductionStep.lean)
└── caseI    (CaseI/Statement.lean:260)          ¬ p ∣ a*b*c branch
    ├── may_assume   (:41)    normalise to 5 ≤ p, gcd = 1, ¬a ≡ b, ¬p ∣ a*b*c
    └── caseI_easier (:225)   the strengthened statement
```

Each child is a good leaf because its statement is self-contained (every
hypothesis is explicit in the theorem header) and its proof closes from named
siblings in the same file, not from the parent's local context. `caseII`
(19-line proof) reduces its proof to the sibling `not_exists_Int_solution'`
after an internal three-way split on which of `a, b, c` is divisible by `p`.
`caseI` (2-line proof) applies the sibling `may_assume` and discharges its
strengthened hypothesis with the sibling `caseI_easier`.

## Why it is good

1. The parent closes in eight lines: two normalising steps, one `by_cases`, and
   one `exact` per branch (lines 21-28), and none of the four copied files
   contains `sorry`, `admit` or `axiom` (grep over `code/`). *(check)*
2. The authors state the plan in the file docstring: "This file combines the
   first and second cases to prove Fermat's Last Theorem at every odd regular
   prime exponent." (lines 9-14). *(author-statement)*
3. The glue is thin relative to what it names: 7 proof lines in the parent
   versus 19 proof lines for `caseII` and 2 for `caseI`; the longest chain of
   project lemmas below `flt_regular` that I checked is 5 deep (`flt_regular` →
   `caseII` → `not_exists_Int_solution'` → `not_exists_Int_solution` →
   `not_exists_solution'` → `not_exists_solution`). *(measurement)*
4. `by_cases` discharges the exhaustiveness obligation itself: the two branches
   are exactly `↑p ∣ a * b * c` and `¬↑p ∣ a * b * c` (line 26), and no separate
   `(p ∣ a*b*c) ∨ ¬(p ∣ a*b*c)` lemma appears in the file. *(check)*

In my opinion the detail worth copying is the *disjoint hypotheses* of the two
children: `caseII` and `caseI` take different assumptions, so the glue is not a
uniform `<;>` but two explicit `exact` lines, one per branch, each handing its
branch exactly the hypotheses it asks for.

This entry supports survey F §10 rule 5 ("Case split with an exhaustiveness
obligation"): the split is one `by_cases` on a decidable hypothesis and its
exhaustiveness is discharged automatically, matching how residue splits close
their exhaustiveness without a separate disjunction child.

## When to use it, and when not

Use a thin `by_cases` glue when a headline goal reduces, by a few normalising
lemmas, to a single decidable hypothesis `Q`, and each side of `Q` is already a
named theorem in the project — so the glue is one split with one `exact` per
branch and the parent is a skeleton of holes over disjoint, self-contained
lemmas. Avoid it when the two sides need different normalisation of the goal
before their theorem applies (here the reduction to coprime integer solutions
must happen first, since `caseII` needs the gcd and nonzero hypotheses that
`caseI` does not take); when `Q` is not decidable without extra classical
assumptions; or when one side is not a single theorem but a family of subgoals
that must be developed inline.

## Consequences

The move creates two obligations (the two branches) plus an exhaustiveness
obligation, which `by_cases` closes itself by classical decidability, so no
separate `∨` child is needed. Because the two children take different
hypotheses, the glue must hand each branch exactly what it asks for: line 27
supplies `mul_ne_zero (mul_ne_zero ha hb) hc` and `hgcd` to `caseII`, while
line 28 passes only `hreg` and `hcase` to `caseI`. The failure mode is a
mismatch between the normalised goal and a child's hypotheses: if the reduction
lemmas drop a hypothesis a child needs (the gcd or nonzeroness), the `exact`
for that branch will not apply and the glue has to re-establish it.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push.yml triggers on push to master (default branch) and runs 'lake -R -Kenv=dev build FltRegular', which compiles FltRegular/FltRegular.lean (the parent theorem file); pinned commit 83f477ccc8cef9fd9a022b90d87aed49368e7bbd is on master (GitHub API branches-where-head) | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 4 file(s) byte-identical at 83f477ccc8cef9fd9a022b90d87aed49368e7bbd | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Local copy (byte-identical per provenance) FltRegular.lean lines 21-28: rw (23), apply (24), by_cases (26), exact caseII (27), exact caseI (28); grep -i over code/ for sorry|admit|axiom returns nothing across the 4 files | verifier |
| 2 | verified | FltRegular.lean docstring lines 12-13 read 'This file combines the first and second cases to prove Fermat's Last Theorem at every odd regular prime exponent.' | verifier |
| 3 | verified | Parent proof lines 22-28 (7), caseII 82-100 (19), caseI 262-263 (2); chain confirmed: caseII calls not_exists_Int_solution' at 88/94/100, which calls not_exists_Int_solution at 68, which calls not_exists_solution' at 57, which calls not_exists_solution at 45 -> 5 lemmas below flt_regular | verifier |
| 4 | verified | FltRegular.lean line 26 'by_cases hcase : ↑p ∣ a * b * c' yields the two branches closed at 27 (caseII, positive) and 28 (caseI, negative); no separate (p ∣ a*b*c) ∨ ¬(p ∣ a*b*c) lemma appears anywhere in the file | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent, children and shape all check out. Parent statement verbatim matches code/FltRegular/FltRegular.lean:21-22; children caseII (CaseII/Statement.lean:78-81) and caseI (CaseI/Statement.lean:260-261) are verbatim in entry.json, and are exactly the two lemmas the parent proof uses (caseII at line 27, caseI at line 28). Closing methods match the code: caseII closes via intro e then dvd_or_dvd splits into three branches each ending in not_exists_Int_solution' hreg hodd <...> (lines 82-100); caseI closes via FltRegular.CaseI.may_assume (fun ... => caseI_easier ...) hreg caseI (lines 262-263). Both by_cases branches hand each child exactly its hypotheses (line 27: hreg hodd (mul_ne_zero (mul_ne_zero ha hb) hc) hgcd hcase; line 28: hreg hcase). Shape numbers are right: direct_lemmas=2, glue_lines=7 (lines 22-28), child_lines=[19,2] (82-100 and 262-263), depth=5 confirmed as flt_regular->caseII->not_exists_Int_solution' (:88,94,100->:68->:57->:45). grep -i for sorry/admit/axiom/Admitted over the four copied files finds nothing. | reviewer-correctness |
| generality | accept | Generality lens: (1) The move is stated beyond the example — applicability.use_when/avoid_when and the README 'When to use it, and when not' name the general condition (a goal reduced by a few normalising lemmas to one decidable hypothesis Q whose two sides are each a named project theorem, with self-contained disjoint children), not FLT-specifics. (2) 'When not to use' is honest and specific: three concrete failure conditions (per-side differing normalisation; Q not decidable without classical assumptions; one side a family of subgoals), and consequences name the exhaustiveness obligation, the per-branch hypothesis mismatch, and a concrete failure mode (a reduction dropping a hypothesis a child needs). (3) It says what makes the leaves good for a bounded prover: 'Each child is a good leaf because its statement is self-contained (every hypothesis explicit in the header) and its proof closes from named siblings, not the parent's local context.' The copied code confirms all three: parent is 7 proof lines with one by_cases and one exact per branch (FltRegular.lean:26-28), and both children carry fully explicit hypotheses in their headers. | reviewer-generality |
| provenance-licence | accept | Commit, licence, permalinks and source note are mutually consistent and traceable. entry.json source.commit 83f477ccc8cef9fd9a022b90d87aed49368e7bbd equals source.json commit and sources/flt-regular/SOURCE.md pinned commit. Licence is Apache-2.0 in entry.json, source.json and SOURCE.md, and sources/flt-regular/upstream-LICENSE is the Apache License 2.0 text. All four file permalinks and three site permalinks use github.com/leanprover-community/flt-regular/blob/83f477c.../<path>, matching repo, commit and path. check_provenance.py reports 4 file(s) byte-identical at 83f477c..., confirming the copied files match the permalinks. README 'Source and licence' section correctly states whole-and-unmodified copy at 83f477c under Apache-2.0 and links the source note. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover-community/flt-regular at commit `83f477ccc8cef9fd9a022b90d87aed49368e7bbd`, under `Apache-2.0`; see the [source note](../../sources/flt-regular/SOURCE.md) for the licence text and attribution.
