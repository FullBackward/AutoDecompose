# Witness pair (E, Q) closes linsolve_always_some_berlekamp_welch

| | |
|---|---|
| Kind | instance |
| Move | witness |
| Language | lean |
| Status | accepted |
| Source | [arklib](../../sources/arklib/SOURCE.md) at `6f9884a95ae7` |
| Licence | `Apache-2.0` |

## Intent

The theorem `linsolve_always_some_berlekamp_welch` says the Berlekamp-Welch
linear-system solver cannot return `none` when the received word `f` is within
`e` errors of the message polynomial `p`. Its proof proceeds by contradiction
and exhibits the polynomial pair `(E, Q)` as a concrete witness solution,
discharging each property of that witness by one named lemma.

## The decomposition

### parent `linsolve_always_some_berlekamp_welch`: [`ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean` lines 151-165](https://github.com/Verified-zkEVM/ArkLib/blob/6f9884a95ae7ee5109a06af95fd95fbf4f8b3bc6/ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean#L151-L165) ([local copy](code/ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean))

```lean
lemma linsolve_always_some_berlekamp_welch
    (hp_deg : p.natDegree < k)
  (h_ham : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e) :
  linsolve (BerlekampWelchMatrix e k ωs f) (Rhs e ωs f) ≠ none := fun contr ↦ by
    by_cases hn : n = 0
    · subst n
      exact linsolve_none contr ⟨0, Subsingleton.elim _ _⟩
    have : NeZero n := ⟨hn⟩
    refine linsolve_none contr ⟨E_and_Q_to_a_solution e (E ωs f p e) (Q ωs f p e), ?p₁⟩
    rw [←IsBerlekampWelchSolution_def]
    simp [
      BerlekampWelchCondition_iff_Solution,
      solutionToQ_from_Q hp_deg h_ham,
      solutionToE_from_E hp_deg h_ham,
      E_and_Q_BerlekampWelch_condition hp_deg h_ham]
```

### child `solutionToQ_from_Q`: [`ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean` lines 72-87](https://github.com/Verified-zkEVM/ArkLib/blob/6f9884a95ae7ee5109a06af95fd95fbf4f8b3bc6/ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean#L72-L87) ([local copy](code/ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean))

```lean
private lemma solutionToQ_from_Q
  (h_p_deg : p.natDegree < k)
  (h_dist : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e) :
  solutionToQ e k (E_and_Q_to_a_solution e (E ωs f p e) (Q ωs f p e)) = Q ωs f p e := by
  refine Polynomial.ext fun i ↦ ?p₁
  simp only [solutionToQ_coeff, Fin.liftF, E_and_Q_to_a_solution_coeff, add_lt_iff_neg_left,
    not_lt_zero, ↓reduceIte, add_tsub_cancel_left, dite_eq_ite]
  split_ifs <;>
  · by_cases hne : p = 0
    · simp [Q, hne]
    · by_contra hq
      have hdeg := Polynomial.le_degree_of_ne_zero (n := i) (p := Q ωs f p e) (by aesop)
      aesop
        (add safe forward (natDegree_Q h_dist))
        (add simp [Q_ne_zero, Polynomial.degree_eq_natDegree])
        (add safe (by omega))
```

### child `solutionToE_from_E`: [`ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean` lines 89-105](https://github.com/Verified-zkEVM/ArkLib/blob/6f9884a95ae7ee5109a06af95fd95fbf4f8b3bc6/ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean#L89-L105) ([local copy](code/ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean))

```lean
private lemma solutionToE_from_E
  (h_p_deg : p.natDegree < k)
  (h_dist : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e) :
  solutionToE e k (E_and_Q_to_a_solution e (E ωs f p e) (Q ωs f p e)) = E ωs f p e := by
  apply Polynomial.ext
  intro i
  simp only [coeff_solutionToE]
  split_ifs <;>
    try aesop (config := {warnOnNonterminal := false})
              (add simp [Fin.liftF, leadingCoeff_E'])
              (add safe (by omega))
  by_contra he
  have hdeg := Polynomial.le_degree_of_ne_zero (n := i) (p := E ωs f p e) (by aesop)
  aesop
    (add safe forward natDegree_E)
    (add simp [E_ne_zero, Polynomial.degree_eq_natDegree])
    (add safe (by omega))
```

### child `E_and_Q_BerlekampWelch_condition`: [`ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean` lines 107-123](https://github.com/Verified-zkEVM/ArkLib/blob/6f9884a95ae7ee5109a06af95fd95fbf4f8b3bc6/ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean#L107-L123) ([local copy](code/ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean))

```lean
private lemma E_and_Q_BerlekampWelch_condition
  (h_p_deg : p.natDegree < k)
  (h_dist : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e) :
  BerlekampWelchCondition e k ωs f (E ωs f p e) (Q ωs f p e) := by
  exact ⟨
  by {
    intro i
    by_cases hi : f i = p.eval (ωs i)
      <;>
      aesop
        (erase simp BerlekampWelch.elocPolyF_eq_elocPoly')
        (add simp [E, Q, BerlekampWelch.errors_are_roots_of_elocPolyF])
  },
  by simp [natDegree_E h_dist],
  by simp [leadingCoeff_E' h_dist],
  by exact le_trans (natDegree_Q h_dist) (by omega)
  ⟩
```

### child `E_and_Q_to_a_solution`: [`ArkLib/Data/CodingTheory/BerlekampWelch/Condition.lean` lines 101-102](https://github.com/Verified-zkEVM/ArkLib/blob/6f9884a95ae7ee5109a06af95fd95fbf4f8b3bc6/ArkLib/Data/CodingTheory/BerlekampWelch/Condition.lean#L101-L102) ([local copy](code/ArkLib/Data/CodingTheory/BerlekampWelch/Condition.lean))

```lean
noncomputable def E_and_Q_to_a_solution (e : ℕ) (E Q : Polynomial F) (i : Fin n) : F :=
  if i < e then E.coeff i else Q.coeff (i - e)
```

How the parts fit. The glue (`linsolve_always_some_berlekamp_welch`) proves
`linsolve … ≠ none` by contradiction. It splits on `n = 0`; in the non-zero
case it applies the contrapositive `linsolve_none` to the hypothesis
`contr : linsolve … = none`, which turns the goal into "no solution exists",
and then exhibits a solution. The solution is the vector
`E_and_Q_to_a_solution e (E ωs f p e) (Q ωs f p e)`, built from the two
polynomials `E` (the error-locator) and `Q = p * E`. The rest of the glue is a
single `simp` that rewrites the remaining obligation through the three property
lemmas:

```
linsolve_always_some_berlekamp_welch
├── E_and_Q_to_a_solution          (build the witness vector from E, Q)
├── solutionToQ_from_Q             (witness projects back to Q)
├── solutionToE_from_E             (witness projects back to E)
└── E_and_Q_BerlekampWelch_condition (witness satisfies the BW condition)
```

`E_and_Q_to_a_solution` is a `def` with no proof obligation, so it is a trivial
leaf. `solutionToQ_from_Q` and `solutionToE_from_E` each close by polynomial
extensionality (`Polynomial.ext`), unfolding the two coefficient definitions,
and then a `by_contra` branch that contradicts the in-file degree bounds
`natDegree_Q h_dist` / `natDegree_E`. `E_and_Q_BerlekampWelch_condition` closes
the structure `BerlekampWelchCondition` field by field: the pointwise equation
via `errors_are_roots_of_elocPolyF`, and the three degree/coefficient bounds
via the in-file lemmas `natDegree_E`, `leadingCoeff_E'`, `natDegree_Q`.

The glue also names two library facts that are *not* part of the witness
decomposition but carry the goal shape: `linsolve_none` (the contrapositive
that `= none` means "no solution") and `BerlekampWelchCondition_iff_Solution`
(the bridge from the solution predicate to the condition). They live in
`Sorries.lean` and `Condition.lean`, which are copied here for context.

Why each lemma is a good leaf: each child is a self-contained statement whose
proof closes on its own from the in-file degree lemmas (which are themselves
`aesop`/`omega` one-liners) or from named siblings in `ElocPoly.lean`. No child
re-proves another child's argument; the degree bound `natDegree_Q` is shared by
`solutionToQ_from_Q` and `E_and_Q_BerlekampWelch_condition` as a sibling lemma,
not duplicated.

## Why it is good

1. The parent proof names the witness constructor `E_and_Q_to_a_solution` to
   build the solution (line 159); the glue cites every child
   (`solutionToQ_from_Q`, `solutionToE_from_E`,
   `E_and_Q_BerlekampWelch_condition` on lines 163-165, and
   `E_and_Q_to_a_solution` on line 159). — *check*, `cites(parent, E_and_Q_to_a_solution)`.
2. Lines 72-165 of `Existence.lean` — the three in-file children and the
   parent — contain no `sorry`, `admit` or `axiom`. — *check*,
   `no_sorry(ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean, 72-165)`.
3. `E_and_Q_BerlekampWelch_condition` is declared at line 107 of
   `Existence.lean`. — *check*,
   `declared(E_and_Q_BerlekampWelch_condition, ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean, 107-107)`.
4. The theorem's shape: the glue is 15 lines (151-165) against four direct
   lemmas of 2, 16, 17 and 17 lines, and the longest checked chain of project
   lemmas below the theorem is 3 deep (`solutionToE_from_E` → `natDegree_E` →
   `elocPolyF_eq_elocPoly'`). — *measurement* (line counts at
   `Condition.lean` 101-102, `Existence.lean` 72-87/89-105/107-123/151-165, and
   `ElocPoly.lean` 140-141).
5. The decoder correctness theorem `decoder_eq_some` closes its `none`-case
   with `exact linsolve_always_some_berlekamp_welch h_deg h_dist hlinsolve`
   (`BerlekampWelch.lean` line 113), and `not_exists_of_decoder_eq_none` does
   the same at line 147. — *known-use*.

In my opinion the detail worth copying is that the witness is *defined* (the
`def E_and_Q_to_a_solution`) rather than left as an existential, so the glue
can close with a plain `simp` over three named lemmas instead of a nested
construction.

## When to use it, and when not

Use it for an existence goal — here a solver's `≠ none`, i.e.
`¬ ¬ ∃ x, A.mulVec x = b` — when the witness is a concrete computable object
whose defining property decomposes into a small number of named lemmas, one per
field of a structure (`BerlekampWelchCondition`) or per projection
(`solutionToE`/`solutionToQ`). Defining the witness first (a `def`) keeps the
glue short and lets the final `simp` unfold everything.

Avoid it when the witness is only available non-constructively and no candidate
is in hand, when the success goal can be discharged by `simp`/`split_ifs` alone,
or when the witness's properties do not separate into independent lemmas and
would instead need one large argument.

## Consequences

The move creates one obligation per property of the witness: here the four
fields of `BerlekampWelchCondition` (the pointwise equation, `E.natDegree = e`,
`E.coeff e = 1`, `Q.natDegree ≤ e + k - 1`) plus the two projection identities
`solutionToE = E` and `solutionToQ = Q`. The glue also leans on two library
facts outside the witness lemmas — `linsolve_none` (the contrapositive) and
`BerlekampWelchCondition_iff_Solution` — so the witness is usable only once
the solver API and the condition⇔solution bridge are in place. Failure mode:
introducing the witness as a bare `def` without the per-field lemmas leaves the
final `simp` unable to unfold the properties, and the goal does not close.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/ci.yml build job runs 'lake build' on push to main (default branch); pinned commit 6f9884a95ae7ee5109a06af95fd95fbf4f8b3bc6 is the tip of main (compare main...6f9884a = identical); lake build compiles the ArkLib library including ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: solutionToQ_from_Q@ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean:163, solutionToE_from_E@ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean:164, E_and_Q_BerlekampWelch_condition@ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean:165, E_and_Q_to_a_solution@ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean:159; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 5 file(s) byte-identical at 6f9884a95ae7ee5109a06af95fd95fbf4f8b3bc6 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, E_and_Q_to_a_solution) -> cites: E_and_Q_to_a_solution occurs at ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean:159 | check_claims.py |
| 2 | verified | no_sorry(ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean, 72-165) -> no_sorry: none of sorry, admit, axiom in ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean:72-165 | check_claims.py |
| 3 | verified | declared(E_and_Q_BerlekampWelch_condition, ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean, 107-107) -> declared: E_and_Q_BerlekampWelch_condition is declared at ArkLib/Data/CodingTheory/BerlekampWelch/Existence.lean:107 | check_claims.py |
| 4 | verified | Line counts read from code/: glue Existence.lean 151-165 = 15 lines (sed -n 151,165p); E_and_Q_to_a_solution Condition.lean 101-102 = 2 lines; solutionToQ_from_Q Existence.lean 72-87 = 16 lines; solutionToE_from_E 89-105 = 17 lines; E_and_Q_BerlekampWelch_condition 107-123 = 17 lines. Depth chain: solutionToE_from_E cites natDegree_E (add safe forward natDegree_E at 89-105); natDegree_E declared at Existence.lean 27-35 and cites BerlekampWelch.elocPolyF_eq_elocPoly' (erase simp ...elocPolyF_eq_elocPoly'); elocPolyF_eq_elocPoly' declared at ElocPoly.lean 140-141. Chain is 3 deep as claimed. | verifier |
| 5 | verified | BerlekampWelch.lean:99 declares theorem decoder_eq_some; its none-case at line 113 reads 'simp only [reduceCtorEq]; exact linsolve_always_some_berlekamp_welch h_deg h_dist hlinsolve' (sed -n 108,120p), matching the claim exactly. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent (Existence.lean 151-165) is a witness proof: by_cases n=0, then refine linsolve_none contr <witness, ?p1> and closes ?p1 via rw [<-IsBerlekampWelchSolution_def] + simp over the three named lemmas solutionToQ_from_Q, solutionToE_from_E, E_and_Q_BerlekampWelch_condition. The glue cites exactly the four children (E_and_Q_to_a_solution at 159, the three property lemmas at 163-165); linsolve_none and BerlekampWelchCondition_iff_Solution are correctly noted as library facts outside the witness decomposition. Each child's closing method matches the code: solutionToQ_from_Q closes by Polynomial.ext + solutionToQ_coeff + split_ifs + by_contra/natDegree_Q (72-87); solutionToE_from_E by Polynomial.ext + coeff_solutionToE + split_ifs + by_contra/natDegree_E (89-105); E_and_Q_BerlekampWelch_condition by constructor over four BerlekampWelchCondition fields using errors_are_roots_of_elocPolyF, natDegree_E, leadingCoeff_E', natDegree_Q (107-123); E_and_Q_to_a_solution is a 2-line noncomputable def with no obligation (Condition.lean 101-102). Shape numbers are right: glue_lines 15 = 151-165, child_lines [16,17,17,2] = 72-87/89-105/107-123/101-102, direct_lemmas 4, depth 3 = solutionToE_from_E -> natDegree_E (27-35) -> elocPolyF_eq_elocPoly' (ElocPoly.lean 140-141). | reviewer-correctness |
| generality | accept | Move abstracted to 'concrete computable witness whose defining property decomposes into one named lemma per structure field or projection'; goal_shape generalizes to any Option-valued solver success proved by contradiction. when-not-to-use honest and specific (non-constructive witness with no candidate, trivial goal, non-factorable properties). Consequences verified against code: the four BerlekampWelchCondition fields map to the four constructor branches (pointwise equation, natDegree_E, leadingCoeff_E', natDegree_Q plus omega); the stated dependency on linsolve_none and BerlekampWelchCondition_iff_Solution is visible in glue lines 151-165; failure mode (bare def without per-field lemmas leaves simp unable to close) is concrete. Good-leaf reasoning present and confirmed: each child self-contained, closes from in-file aesop/omega one-liners (natDegree_E, natDegree_Q, leadingCoeff_E' at lines 27-60), natDegree_Q shared by two children rather than duplicated. | reviewer-generality |
| provenance-licence | accept | provenance pass (5 files byte-identical at 6f9884a95ae7ee5109a06af95fd95fbf4f8b3bc6); commit consistent across entry.json, README (abbr 6f9884a95ae7), source.json and SOURCE.md; licence Apache-2.0 in entry/README/source.json/source note matches upstream-LICENSE (Apache 2.0 text); all permalinks use the pinned commit and correct file paths; cited line ranges verified (parent 151-165, children 72-87/89-105/107-123, def Condition.lean 101-102, uses BerlekampWelch.lean 113/147) against the byte-identical local copy. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/Verified-zkEVM/ArkLib at commit `6f9884a95ae7ee5109a06af95fd95fbf4f8b3bc6`, under `Apache-2.0`; see the [source note](../../sources/arklib/SOURCE.md) for the licence text and attribution.
