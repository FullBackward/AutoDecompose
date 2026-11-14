# Blueprint node for Hilbert 94 part 1: a norm-one unit (Hilbert 92) feeds the capitulating-ideal lemma

| | |
|---|---|
| Kind | instance |
| Move | blueprint-node |
| Language | lean |
| Status | accepted |
| Source | [flt-regular](../../sources/flt-regular/SOURCE.md) at `83f477ccc8ce` |
| Licence | `Apache-2.0` |

## Intent

The first part of Hilbert Theorem 94 — that an unramified cyclic extension `L/K`
of number fields of odd prime degree has an ideal that capitulates — is stated
as a node (with its `/- ... -/` doc comment), then proved by a three-line glue
that forwards to two project lemmas: `Hilbert92`, which supplies the norm-one
unit `η` that is not of the form `ε / σ ε`, and
`exists_not_isPrincipal_and_isPrincipal_map_aux`, which turns such a unit into
the non-principal-but-capitulating ideal. The parent does no algebra itself; it
only unpacks cyclicity and discharges the children's hypotheses.

## The decomposition

### parent `exists_not_isPrincipal_and_isPrincipal_map`: [`FltRegular/NumberTheory/Hilbert94.lean` lines 94-105](https://github.com/leanprover-community/flt-regular/blob/83f477ccc8cef9fd9a022b90d87aed49368e7bbd/FltRegular/NumberTheory/Hilbert94.lean#L94-L105) ([local copy](code/FltRegular/NumberTheory/Hilbert94.lean))

```lean
/-- This is the first part of **Hilbert Theorem 94**, which states that if `L/K` is an unramified
  cyclic finite extension of number fields of odd prime degree,
  then there is an ideal that capitulates in `K`. -/
theorem exists_not_isPrincipal_and_isPrincipal_map (K L : Type)
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Algebra.Unramified (𝓞 K) (𝓞 L)]
    [h : IsCyclic (L ≃ₐ[K] L)] (hKL : Nat.Prime (finrank K L)) (hKL' : finrank K L ≠ 2) :
    ∃ I : Ideal (𝓞 K), ¬I.IsPrincipal ∧
      (I.map (algebraMap (𝓞 K) (𝓞 L))).IsPrincipal := by
  obtain ⟨⟨σ, hσ⟩⟩ := h
  obtain ⟨η, hη, hη'⟩ := Hilbert92 hKL hKL' σ hσ
  exact exists_not_isPrincipal_and_isPrincipal_map_aux σ hσ η hη (not_exists.mpr hη')
```

### child `exists_not_isPrincipal_and_isPrincipal_map_aux`: [`FltRegular/NumberTheory/Hilbert94.lean` lines 51-80](https://github.com/leanprover-community/flt-regular/blob/83f477ccc8cef9fd9a022b90d87aed49368e7bbd/FltRegular/NumberTheory/Hilbert94.lean#L51-L80) ([local copy](code/FltRegular/NumberTheory/Hilbert94.lean))

```lean
theorem exists_not_isPrincipal_and_isPrincipal_map_aux
    [IsDedekindDomain A] [Algebra.Unramified A B] (η : Bˣ)
    (hη : Algebra.norm K (algebraMap B L η) = 1)
    (hη' : ¬∃ α : Bˣ, algebraMap B L η = (algebraMap B L α) / σ (algebraMap B L α)) :
    ∃ I : Ideal A, ¬I.IsPrincipal ∧ (I.map (algebraMap A B)).IsPrincipal := by
  have := isCyclic_iff_exists_zpowers_eq_top.2 ⟨σ, (Subgroup.eq_top_iff' _).2 hσ⟩
  obtain ⟨β, hβ_zero, hβ⟩ := groupCohomology.exists_mul_galRestrict_of_norm_eq_one (A := A)
    (B := B) hσ hη
  have : IsDomain B := Function.Injective.isDomain _ (IsIntegralClosure.algebraMap_injective B A L)
  have hβ' := comap_map_eq_of_unramified K L _
    (comap_span_galRestrict_eq_of_cyclic σ hσ (A := A) (B := B) β η hβ)
  refine ⟨(Ideal.span {β}).comap (algebraMap A B), ?_, ?_⟩
  · rintro ⟨⟨γ, hγ : _ = Ideal.span _⟩⟩
    rw [hγ, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_span_singleton] at hβ'
    obtain ⟨a, rfl⟩ := hβ'
    rw [map_mul, AlgEquiv.commutes, mul_left_comm, (mul_right_injective₀ _).eq_iff] at hβ
    · apply hη'
      use a
      conv_rhs =>
        enter [1]
        rw [← hβ]
      rw [map_mul, ← algebraMap_galRestrict_apply A]
      refine (mul_div_cancel_right₀ _ ?_).symm
      · rw [ne_eq,
          (injective_iff_map_eq_zero' _).mp (IsIntegralClosure.algebraMap_injective B A L),
          (injective_iff_map_eq_zero' _).mp (galRestrict A K L B σ).injective]
        exact a.isUnit.ne_zero
    · exact (mul_ne_zero_iff.mp hβ_zero).1
  · rw [hβ']
    exact ⟨⟨_, rfl⟩⟩
```

### child `Hilbert92`: [`FltRegular/NumberTheory/Hilbert92.lean` lines 726-733](https://github.com/leanprover-community/flt-regular/blob/83f477ccc8cef9fd9a022b90d87aed49368e7bbd/FltRegular/NumberTheory/Hilbert92.lean#L726-L733) ([local copy](code/FltRegular/NumberTheory/Hilbert92.lean))

```lean
lemma Hilbert92 [Algebra k K] [IsGalois k K] [NumberField k] [NumberField K]
    (hKL : Nat.Prime (finrank k K)) (hpodd : finrank k K ≠ 2)
    (σ : K ≃ₐ[k] K) (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    ∃ η : (𝓞 K)ˣ, Algebra.norm k (η : K) = 1 ∧
      ∀ ε : (𝓞 K)ˣ, (η : K) ≠ ε / (σ ε : K) :=
  have := IsUnramifiedAtInfinitePlaces_of_odd_finrank (hKL.odd_of_ne_two hpodd)
  have : IsCyclic (K ≃ₐ[k] K) := ⟨σ, hσ⟩
  almostHilbert92 (finrank k K) hKL rfl σ hσ hpodd
```

How the parts fit. The parent's proof (the glue, lines 103-105) has three steps:

1. `obtain ⟨⟨σ, hσ⟩⟩ := h` unpacks the cyclicity hypothesis
   `h : IsCyclic (L ≃ₐ[K] L)` into a generator `σ` and a proof `hσ` that it generates.
2. `obtain ⟨η, hη, hη'⟩ := Hilbert92 hKL hKL' σ hσ` applies `Hilbert92` to get the
   norm-one unit `η` (`hη : norm = 1`) and the "not a quotient" property (`hη'`).
3. `exact exists_not_isPrincipal_and_isPrincipal_map_aux σ hσ η hη (not_exists.mpr hη')`
   feeds `η` and its two properties to the aux lemma, which returns the ideal.

The lemma graph (which lemma uses which, in text):

```
exists_not_isPrincipal_and_isPrincipal_map (parent, Hilbert94.lean:97)
├── Hilbert92 (Hilbert92.lean:726)               supplies η, the norm-one unit
│   └── almostHilbert92 (Hilbert92.lean:619)     the substance of Hilbert's Satz 92
└── exists_not_isPrincipal_and_isPrincipal_map_aux (Hilbert94.lean:51)   builds the ideal
    ├── comap_span_galRestrict_eq_of_cyclic (Hilbert94.lean:25)   span invariance under the Galois restriction
    └── comap_map_eq_of_unramified (Unramified.lean:40)           unramifiedness lifts the comap
```

Each child is a good leaf because its statement is self-contained and its proof
closes on its own or from named siblings:

- `Hilbert92` is a self-contained statement (there is a unit `η` of norm 1 that
  is not of the form `ε / σ ε`); its proof is two `have`s plus one application of
  the sibling `almostHilbert92` (`almostHilbert92 (finrank k K) hKL rfl σ hσ hpodd`).
  Its hypotheses (prime degree, odd `≠ 2`, generator `σ`) are exactly what the
  parent already has, so the glue discharges them by forwarding `hKL hKL' σ hσ`.
- `exists_not_isPrincipal_and_isPrincipal_map_aux` is a self-contained statement
  (there is an ideal non-principal in `A` and principal in `B`); its proof
  obtains `β` from the cohomology lemma `groupCohomology.exists_mul_galRestrict_of_norm_eq_one`,
  builds the candidate `(Ideal.span {β}).comap (algebraMap A B)` through
  `refine ⟨_, ?_, ?_⟩`, and closes the two goals from the named siblings
  `comap_span_galRestrict_eq_of_cyclic` and `comap_map_eq_of_unramified` plus the
  hypothesis `hη'`.

Note the one place the glue does real work: `not_exists.mpr hη'` flips `Hilbert92`'s
conclusion `∀ ε, η ≠ ε / σ ε` into the aux lemma's hypothesis
`¬∃ α, η = (α) / σ (α)`.

## Why it is good

1. The parent theorem `exists_not_isPrincipal_and_isPrincipal_map` is declared in
   `FltRegular/NumberTheory/Hilbert94.lean`, lines 94-105 (`check`, permalink).
2. The parent proof cites `Hilbert92` (`check`, line 104).
3. The parent proof cites `exists_not_isPrincipal_and_isPrincipal_map_aux`
   (`check`, line 105).
4. The source documents the node as the first part of Hilbert Theorem 94:
   "This is the first part of Hilbert Theorem 94, which states that if L/K is an
   unramified cyclic finite extension of number fields of odd prime degree, then
   there is an ideal that capitulates in K." (`author-statement`, doc comment,
   lines 94-96).
5. The main theorem assembles 2 direct project lemmas and the longest checked
   chain of project lemmas below it is 2 deep
   (`measurement`, parent lines 103-105 and aux lines 51-80).

## When to use it, and when not

Use it when the theorem is one node of a published result (here Hilbert's
Satz 94, with part 2 `dvd_card_classGroup_of_unramified_isCyclic` depending on
this node at lines 107-119), and the proof splits cleanly into two named project
lemmas with self-contained statements — one that produces an object with a
property (the norm-one unit), one that consumes it (the ideal construction) — so
the main proof is a short forward of hypotheses. Avoid it when the two
obligations cannot be stated independently, when the child lemmas are not
reusable elsewhere, or when there is no documented dependency graph: then the
split is a plain `suffices`, not a blueprint node, and the "node" label overstates
the structure.

## Consequences

The move creates two obligations: (1) produce a norm-one unit `η` with the "not
a quotient" property (discharged by `Hilbert92`, which itself needs the
odd/prime-degree hypotheses), and (2) turn such a unit into the ideal
(discharged by the aux lemma). The glue must discharge every hypothesis of the
aux lemma (`IsDedekindDomain`, unramified, norm-one, not-a-quotient), which it
does by forwarding `hσ`, `hη`, and `not_exists.mpr hη'` — the last flips the
`∀` into a `¬∃`. Failure mode: if `Hilbert92`'s statement changes (for example a
different quotient condition on the unit), the `not_exists.mpr` flip in the glue
breaks, since the two children are coupled exactly at that condition.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push.yml runs on push to master (the default branch) and builds the whole FltRegular package (lake -R -Kenv=dev build FltRegular), which includes FltRegular/NumberTheory/Hilbert94.lean; commit 83f477ccc8cef9fd9a022b90d87aed49368e7bbd is pinned at ref HEAD (the default branch) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: Hilbert92@FltRegular/NumberTheory/Hilbert94.lean:104, exists_not_isPrincipal_and_isPrincipal_map_aux@FltRegular/NumberTheory/Hilbert94.lean:105; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at 83f477ccc8cef9fd9a022b90d87aed49368e7bbd | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(exists_not_isPrincipal_and_isPrincipal_map, FltRegular/NumberTheory/Hilbert94.lean, 94-105) -> declared: exists_not_isPrincipal_and_isPrincipal_map is declared at FltRegular/NumberTheory/Hilbert94.lean:97 | check_claims.py |
| 2 | verified | cites(parent, Hilbert92) -> cites: Hilbert92 occurs at FltRegular/NumberTheory/Hilbert94.lean:104 | check_claims.py |
| 3 | verified | cites(parent, exists_not_isPrincipal_and_isPrincipal_map_aux) -> cites: exists_not_isPrincipal_and_isPrincipal_map_aux occurs at FltRegular/NumberTheory/Hilbert94.lean:105 | check_claims.py |
| 4 | verified | doc comment at Hilbert94.lean:94-96 reads: /-- This is the first part of **Hilbert Theorem 94**, which states that if L/K is an unramified cyclic finite extension of number fields of odd prime degree, then there is an ideal that capitulates in K. -/ — matches the quoted claim (markdown markup stripped) | verifier |
| 5 | verified | parent proof lines 103-105 names exactly Hilbert92 (line 104) and exists_not_isPrincipal_and_isPrincipal_map_aux (line 105); aux proof line 61 cites comap_span_galRestrict_eq_of_cyclic; that lemma is declared at Hilbert94.lean:25. Chain parent->aux->comap_span_galRestrict_eq_of_cyclic is 2 project lemmas deep | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Correctness verified against the copied code. Parent exists_not_isPrincipal_and_isPrincipal_map is declared at Hilbert94.lean:97 (site 94-105, doc comment 94-96, proof 103-105) and its statement matches entry.json verbatim. Glue lines 103-105 cite exactly Hilbert92 (line 104) and exists_not_isPrincipal_and_isPrincipal_map_aux (line 105): obtain ⟨⟨σ,hσ⟩⟩:=h; obtain ⟨η,hη,hη'⟩:=Hilbert92 hKL hKL' σ hσ; exact exists_not_isPrincipal_and_isPrincipal_map_aux σ hσ η hη (not_exists.mpr hη'). Both children are the only project lemmas the proof uses. Hilbert92 (Hilbert92.lean:726-733) statement matches verbatim and closes by almostHilbert92 (finrank k K) hKL rfl σ hσ hpodd (line 733); almostHilbert92 is declared at 619. The aux child (Hilbert94.lean:51-80) statement matches verbatim, builds (Ideal.span {β}).comap (algebraMap A B), and closes its two goals from comap_map_eq_of_unramified (line 61) and comap_span_galRestrict_eq_of_cyclic (line 62, declared at line 25) plus hη'. Shape numbers are right: glue_lines 12 = parent site 94-105; child_lines [30,8] = aux site 51-80 (30) and Hilbert92 site 726-733 (8); direct_lemmas 2; depth 2 (parent→aux→comap_span_galRestrict_eq_of_cyclic and parent→Hilbert92→almostHilbert92). Decomposition matches the entry, children and closing methods match the code, and it closes. | reviewer-correctness |
| generality | accept | Generality is handled honestly. use_when abstracts the example into a reusable pattern: a theorem that is one node of a published dependency graph whose proof splits into named, self-contained lemmas (a producer-of-an-object-with-a-property plus a consumer), so the main proof is a short forward of hypotheses. avoid_when gives concrete, honest conditions (obligations not independently statable, children not reused elsewhere, no documented graph -> plain suffices, and it admits the 'node' label would then overstate). consequences name a specific coupling point: the glue's not_exists.mpr flip of Hilbert92's forall conclusion into the aux lemma's neg-exists hypothesis, and the failure mode if that quotient condition changes (verified against Hilbert94.lean:105 and Hilbert92.lean:726-733). The 'bounded prover' question is answered in substance though not in that exact wording: the README's 'Each child is a good leaf because its statement is self-contained and its proof closes on its own or from named siblings' plus the note that Hilbert92's hypotheses are exactly what the parent forwards, and that the aux closes its two goals from named siblings, is precisely what makes each leaf dispatchable in isolation. | reviewer-generality |
| provenance-licence | accept | provenance pass (2 files byte-identical at 83f477ccc8cef9fd9a022b90d87aed49368e7bbd); entry.json files match copied code (Hilbert94.lean 5887B, Hilbert92.lean 34828B); permalink site anchors verified against local copies (parent 94-105, aux 51-80, Hilbert92 726-733); commit 83f477... consistent across entry.json, source.json, SOURCE.md; licence Apache-2.0 consistent across entry.json, README, source.json, SOURCE.md, and upstream-LICENSE is the Apache-2.0 text; source note records repo, commit, licence and attribution. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover-community/flt-regular at commit `83f477ccc8cef9fd9a022b90d87aed49368e7bbd`, under `Apache-2.0`; see the [source note](../../sources/flt-regular/SOURCE.md) for the licence text and attribution.
