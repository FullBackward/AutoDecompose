# Case split on Nontrivial G and p divides |G| for Dickson's classification of finite PGL2 subgroups

| | |
|---|---|
| Kind | instance |
| Move | case-split |
| Language | lean |
| Status | accepted |
| Source | [flt-imperial](../../sources/flt-imperial/SOURCE.md) at `a3210204ad88` |
| Licence | `Apache-2.0` |

## Intent

A statement about every finite subgroup `G` of `PGL₂(𝔽̄_p)`, phrased as an
8-way disjunction of group-isomorphism cases, is reduced to two named lemmas —
one for the *wild* case (`p ∣ |G|`), one for the *tame* case (`p ∤ |G|`) — plus
a trivial subsingleton case, each re-indexed into the goal by a chain of
`Or.inl`/`Or.inr`.

## The decomposition

### parent `Dickson.dickson_classification`: [`FLT/Slop/PGL2/FiniteSubgroups/DicksonClassification.lean` lines 54-83](https://github.com/ImperialCollegeLondon/FLT/blob/a3210204ad8876e851e32f73dd97d882bf1ccd0a/FLT/Slop/PGL2/FiniteSubgroups/DicksonClassification.lean#L54-L83) ([local copy](code/FLT/Slop/PGL2/FiniteSubgroups/DicksonClassification.lean))

```lean
theorem dickson_classification (G : Subgroup (PGLOf (K p))) [Finite G] :
    (IsCyclic G) ∨
    (∃ n : ℕ, n ≥ 2 ∧ Nonempty (G ≃* DihedralGroup n)) ∨
    (Nonempty (G ≃* alternatingGroup (Fin 4))) ∨
    (Nonempty (G ≃* Equiv.Perm (Fin 4))) ∨
    (Nonempty (G ≃* alternatingGroup (Fin 5))) ∨
    (∃ (m t : ℕ) (_ : m ≥ 1) (_ : Nat.Coprime t p) (_ : t ∣ p ^ m - 1)
      (φ : Multiplicative (ZMod t) →* MulAut (Multiplicative (Fin m → ZMod p))),
      Nonempty (G ≃* (Multiplicative (Fin m → ZMod p)) ⋊[φ] Multiplicative (ZMod t))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* (GL (Fin 2) (GaloisField p m) ⧸
        Subgroup.center (GL (Fin 2) (GaloisField p m))))) := by
  by_cases hG_nontrivial : Nontrivial G
  · by_cases h_div : p ∣ Nat.card G
    · rcases classification_wild_slop p G h_div with h1 | h2 | h3 | ⟨_, h4⟩
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h1
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h2
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr h3
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h4
    · have : Fintype G := Fintype.ofFinite G
      rcases classification_tame_slop p G h_div hG_nontrivial with h1 | h2 | h3 | h4 | h5
      · exact Or.inl h1
      · exact Or.inr <| Or.inl h2
      · exact Or.inr <| Or.inr <| Or.inl h3
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl h4
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h5
  · have : Subsingleton G := not_nontrivial_iff_subsingleton.mp hG_nontrivial
    exact Or.inl ⟨⟨1, fun x ↦ by rw [Subsingleton.elim x 1]; exact Subgroup.mem_zpowers 1⟩⟩
```

### child `Dickson.classification_wild_slop`: [`FLT/Slop/PGL2/FiniteSubgroups/WildClassification.lean` lines 694-715](https://github.com/ImperialCollegeLondon/FLT/blob/a3210204ad8876e851e32f73dd97d882bf1ccd0a/FLT/Slop/PGL2/FiniteSubgroups/WildClassification.lean#L694-L715) ([local copy](code/FLT/Slop/PGL2/FiniteSubgroups/WildClassification.lean))

```lean
theorem classification_wild_slop (G : Subgroup (PGLOf (K p))) [Finite G]
    (hG_p : p ∣ Nat.card G) :
    (∃ (m t : ℕ) (_ : m ≥ 1) (_ : Nat.Coprime t p) (_ : t ∣ p ^ m - 1)
      (φ : Multiplicative (ZMod t) →* MulAut (Multiplicative (Fin m → ZMod p))),
      Nonempty (G ≃* (Multiplicative (Fin m → ZMod p)) ⋊[φ] Multiplicative (ZMod t))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* (GL (Fin 2) (GaloisField p m) ⧸
        Subgroup.center (GL (Fin 2) (GaloisField p m))))) ∨
    (p = 3 ∧ Nonempty (G ≃* alternatingGroup (Fin 5))) := by
  have ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  by_cases h_sylow : Fintype.card (Sylow p G) = 1
  · have : Subsingleton (Sylow p G) := Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h_sylow)
    exact Or.inl <| branch1_semidirect p G P (Sylow.normal_of_subsingleton P) hG_p
  · have hn_p_gt1 : Fintype.card (Sylow p G) > 1 :=
      lt_of_le_of_ne (Fintype.card_pos_iff.mpr inferInstance) (Ne.symm h_sylow)
    obtain ⟨pm, z1, n, r, z, s, hpm_eq, hn_eq, hpm, hz1_ge, hz1_dvd, hs_bound, hz_pos, hn_gt, h_eq⟩ :=
      partition_equation p G hG_p P hn_p_gt1
    by_cases hz1_eq : z1 = 1
    · exact dickson_branch2_z1_eq_1 p G hG_p P hn_p_gt1 pm z1 n r z s hpm_eq hn_eq hpm hz1_ge hz1_dvd hs_bound hz_pos hn_gt h_eq hz1_eq
    · exact dickson_branch2_z1_ge_2 p G hG_p P hn_p_gt1 pm hpm_eq hpm
```

### child `Dickson.classification_tame_slop`: [`FLT/Slop/PGL2/FiniteSubgroups/TameClassification.lean` lines 1641-1671](https://github.com/ImperialCollegeLondon/FLT/blob/a3210204ad8876e851e32f73dd97d882bf1ccd0a/FLT/Slop/PGL2/FiniteSubgroups/TameClassification.lean#L1641-L1671) ([local copy](code/FLT/Slop/PGL2/FiniteSubgroups/TameClassification.lean))

```lean
theorem classification_tame_slop (G : Subgroup (PGLOf (K p))) [Fintype G]
    (hG_tame : ¬ (p : ℕ) ∣ Nat.card G)
    (hG_nontrivial : Nontrivial G) :
    (IsCyclic G) ∨
    (∃ n : ℕ, n ≥ 2 ∧ Nonempty (G ≃* DihedralGroup n)) ∨
    (Nonempty (G ≃* alternatingGroup (Fin 4))) ∨
    (Nonempty (G ≃* Equiv.Perm (Fin 4))) ∨
    (Nonempty (G ≃* alternatingGroup (Fin 5))) := by

  rcases tame_hasCyclicPartition p G hG_tame hG_nontrivial with
    ⟨N, hN_card, hN_part⟩ | ⟨n, hn_odd, hn_ge, hn_card, hn_part⟩ |
    ⟨n, hn_even, hn_ge, hn_card, hn_part⟩ |
    ⟨h12_card, h12_part⟩ | ⟨h24_card, h24_part⟩ | ⟨h60_card, h60_part⟩

  · exact .inl (isCyclic_of_hasCyclicPartition G N hN_card hN_part)

  · exact .inr (.inl ⟨n, by omega, dihedral_of_hasCyclicPartition_odd G n hn_ge hn_card hn_part⟩)

  · rcases eq_or_ne n 2 with rfl | hn2
    · exact .inr (.inl ⟨2, by omega, dihedral2_of_hasCyclicPartition G hn_card hn_part⟩)

    · exact .inr (.inl ⟨n, by omega,
        dihedral_of_hasCyclicPartition_even G n
          (by obtain ⟨k, rfl⟩ := hn_even; omega)
          hn_card hn_part⟩)

  · exact .inr (.inr (.inl (iso_A4_of_hasCyclicPartition G h12_card h12_part)))

  · exact .inr (.inr (.inr (.inl (iso_S4_of_hasCyclicPartition G h24_card h24_part))))

  · exact .inr (.inr (.inr (.inr (iso_A5_of_hasCyclicPartition G h60_card h60_part))))
```

How the parts fit. The parent opens with two nested `by_cases` that partition
every finite `G` into three cases, and each case is closed by one named lemma
(or a mathlib fact):

```
dickson_classification  (DicksonClassification.lean:54-83)
|-- by_cases hG_nontrivial : Nontrivial G
|   |-- Nontrivial, by_cases h_div : p | Nat.card G
|   |   |-- p | |G|   ->  classification_wild_slop  (WildClassification.lean:694)
|   |   |                  |-- branch1_semidirect        (263) -> complement_isCyclic (230) -> fixes_point_coprime_isCyclic (198)
|   |   |                  |-- partition_equation        (530)
|   |   |                  |-- dickson_branch2_z1_eq_1   (593)
|   |   |                  `-- dickson_branch2_z1_ge_2   (639)
|   |   `-- not p | |G| -> classification_tame_slop  (TameClassification.lean:1641)
|   |                        `-- tame_hasCyclicPartition (1474)
|   |                            `-- isCyclic_of_hasCyclicPartition / dihedral_of_hasCyclicPartition_odd·even
|   |                                / dihedral2_of_hasCyclicPartition / iso_A4·S4·A5_of_hasCyclicPartition  (CyclicPartition.lean)
|   `-- not Nontrivial ->  Subsingleton G, closed by not_nontrivial_iff_subsingleton + Subgroup.mem_zpowers
```

The wild child `classification_wild_slop` proves the four `p ∣ |G|` disjuncts
(semidirect product, `PSL₂(𝔽_{p^m})`, `PGL₂(𝔽_{p^m})`, and the exceptional
`p = 3` giving `A₅`), and the tame child `classification_tame_slop` proves the
five `p ∤ |G|` disjuncts (cyclic, dihedral, `A₄`, `S₄`, `A₅`). The parent turns
each into its own 8-way disjunct with a chain of `Or.inl`/`Or.inr`, and the
subsingleton branch (¬ `Nontrivial G`) is closed directly: a subsingleton group
is cyclic via `Subgroup.mem_zpowers`.

Each child is a good leaf because its statement is self-contained — it carries
its own hypotheses (`hG_p` for the wild side, `hG_tame`/`hG_nontrivial` for the
tame side) and states a disjunction that is a direct slice of the parent's goal
— and its proof closes from named siblings in the same directory. The wild child
is itself a two-level `by_cases` (Sylow count = 1 vs. > 1, then `z1 = 1` vs.
`z1 ≥ 2`) resolved by four branch lemmas; the tame child is an `rcases` on
`tame_hasCyclicPartition` (a 6-way partition of the order) resolved by six
isomorphism lemmas that live in `CyclicPartition.lean` (copied here).

The move is the *case split*: the whole of the parent's proof below the statement
is 16 lines, 10 of which are the positional re-indexing `Or.inl`/`Or.inr` chains,
and 6 of which are the two `by_cases`, the two `rcases`, and the two `have` that
manufacture the `Fintype`/`Subsingleton` instances.

## Why it is good

1. The parent closes from exactly two project lemmas plus a mathlib fact: the
   `p ∣` branch by `classification_wild_slop` (line 70), the `¬ p ∣` branch by
   `classification_tame_slop` (line 76), and the subsingleton branch by
   `not_nontrivial_iff_subsingleton` and `Subgroup.mem_zpowers` (lines 82-83)
   (`check`, [parent lines 54-83](https://github.com/ImperialCollegeLondon/FLT/blob/a3210204ad8876e851e32f73dd97d882bf1ccd0a/FLT/Slop/PGL2/FiniteSubgroups/DicksonClassification.lean#L54-L83)).
2. No branch is closed by a hole: the four copied files contain no `sorry`,
   `admit`, or `axiom` (`check`, grep at the pinned commit over the files named
   in the claim).
3. The module docstring states the plan, and the proof follows it: "This is the
   combination of the tame case (`Dickson.classification_tame_slop`, order
   coprime to `p`) and the wild case (`Dickson.classification_wild_slop`, order
   divisible by `p`)"
   (`author-statement`, [lines 24-26](https://github.com/ImperialCollegeLondon/FLT/blob/a3210204ad8876e851e32f73dd97d882bf1ccd0a/FLT/Slop/PGL2/FiniteSubgroups/DicksonClassification.lean#L24-L26)).
4. The glue is 16 lines (68-83), of which 10 are re-indexing `Or.inl`/`Or.inr`
   and 6 are setup; the children's proofs are 11 lines (wild, 705-715) and 23
   lines (tame, 1649-1671) (`measurement`, line counts of the copied files).
5. The decomposition is 4 project lemmas deep: `dickson_classification` →
   `classification_wild_slop` (WildClassification.lean:694) →
   `branch1_semidirect` (:263) → `complement_isCyclic` (:230) →
   `fixes_point_coprime_isCyclic` (:198), each a proved theorem in the same
   directory (`measurement`, the call chain in the copied file).

In my opinion the reusable detail is the pairing of *named per-branch lemmas*
with *positional re-indexing*: the split is honest (each branch is a real,
separately-proved theorem), but the cost is that the `Or.inr <| Or.inr <| …`
chains are by position, so a change to the disjunction order would silently
re-route a case.

## When to use it, and when not

Use it when the goal is a classification theorem whose cases are indexed by a
small set of decidable predicates on the quantified object (here: nontriviality
and divisibility of the order by a fixed prime), and a named lemma already
exists for each branch, so the glue reduces to `by_cases` plus re-indexing.
Avoid it when the branches overlap or are not a genuine partition; when the
per-branch lemmas do not yet exist (then the split is not the content — the
branch lemmas are); or when the disjunction is deep and shifting enough that
positional `Or.inl`/`Or.inr` chains become error-prone (a dedicated `cases` type
or `match` is clearer).

## Consequences

The two `by_cases` produce three branches whose exhaustiveness is automatic
(each is `Classical.em` on a decidable predicate), so — unlike a residue split —
there is no separate exhaustiveness child. The real cost is re-indexing: each
child proves a disjunction with a different number and order of disjuncts than
the parent (wild is 4-way, tame is 5-way, parent is 8-way), so every branch is
retargeted by a chain of `Or.inl`/`Or.inr`; note the wild child's exceptional
`p = 3` case lands on the same `alternatingGroup (Fin 5)` disjunct as the tame
child's. The failure mode is positional: if the parent's disjunction order
changes, the `Or.inr <| Or.inr <| …` chains silently point at the wrong
disjunct, because the re-indexing is by position, not by name.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/blueprint.yml (workflow 'Build project', job build_project runs leanprover/lean-action@v1 with build:true, triggered on push/PR to main for **/*.lean) builds the file; pinned commit a3210204ad8876e851e32f73dd97d882bf1ccd0a is the tip of default branch main (GitHub compare main...a3210204 returned identical) | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 4 file(s) byte-identical at a3210204ad8876e851e32f73dd97d882bf1ccd0a | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read code/FLT/Slop/PGL2/FiniteSubgroups/DicksonClassification.lean: L68 by_cases Nontrivial G, L69 by_cases p | Nat.card G, L70 rcases classification_wild_slop, L76 rcases classification_tame_slop, L82-83 not_nontrivial_iff_subsingleton + Subgroup.mem_zpowers; only two project lemmas used (classification_wild_slop, classification_tame_slop) | verifier |
| 2 | verified | grep -rn 'sorry|admit|axiom|Admitted' over code/FLT/Slop/PGL2/FiniteSubgroups/{DicksonClassification,WildClassification,TameClassification,CyclicPartition}.lean returned no matches | verifier |
| 3 | verified | Read code DicksonClassification.lean L24-26 module docstring, which says exactly the quoted sentence about combining classification_tame_slop and classification_wild_slop | verifier |
| 4 | verified | Counted in copied files: DicksonClassification.lean L68-83 = 16 lines; Or.inl/Or.inr lines are 71-74,77-81,83 = 10; setup lines 68,69,70,75,76,82 = 6 (two by_cases, two rcases, two have); WildClassification.lean L705-715 = 11 lines; TameClassification.lean L1649-1671 = 23 lines | verifier |
| 5 | verified | Read copied files: classification_wild_slop declared WildClassification.lean:694, called in DicksonClassification.lean:70; branch1_semidirect declared :263 called at :708; complement_isCyclic declared :230 called at :273; fixes_point_coprime_isCyclic declared :198 called at :243. Chain is 4 lemmas deep, all proved theorems in same directory | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent dickson_classification (DicksonClassification.lean:54-83) is an 8-way disjunction closed by two nested by_cases (Nontrivial G, then p|Nat.card G): wild branch uses classification_wild_slop (line 70), tame branch classification_tame_slop (line 76), subsingleton branch not_nontrivial_iff_subsingleton+Subgroup.mem_zpowers (82-83). Children are exactly those two project lemmas. Wild child (WildClassification.lean:694-715) closes via branch1_semidirect(708), partition_equation(712), dickson_branch2_z1_eq_1(714), dickson_branch2_z1_ge_2(715) - matches closed_by. Tame child (TameClassification.lean:1641-1671) closes via tame_hasCyclicPartition(1650) and 6 iso lemmas (isCyclic/dihedral_odd/even/dihedral2/A4/S4/A5 at 1655-1671) - matches closed_by. No sorry/admit/axiom in any of the 4 copied files (grep). Re-indexing Or.inl/Or.inr chains positionally correct against the 8-way disjunction (incl. wild p=3|A5 -> disjunct 5). Shape numbers right: direct_lemmas=2, glue_lines=16 (68-83), child_lines=[11,23] (705-715,1649-1671), depth=4 chain verified dickson_classification->classification_wild_slop(694)->branch1_semidirect(263)->complement_isCyclic(230)->fixes_point_coprime_isCyclic(198). Provenance pass: 4 files byte-identical at a3210204. Minor prose note (not a claim): README says dihedral2_of_hasCyclicPartition is in CyclicPartition.lean but it is TameClassification.lean:1052. | reviewer-correctness |
| generality | accept | Move stated generally: 'finite disjunction over a quantified object, cases indexed by a small set of decidable predicates, one named lemma per branch' (not 'Nontrivial / p-divides' only). avoid_when gives three concrete conditions (overlap/not-a-partition, branch lemmas not yet existing, deep shifting disjunction where positional reindex is error-prone). Consequences honest and specific: automatic exhaustiveness (by_cases = Classical.em, no exhaustiveness child), cost is re-indexing because wild=4-way/tame=5-way/parent=8-way, the wild p=3 case lands on the same A5 disjunct as tame, and the positional (not-by-name) failure mode — all of which match the copied parent proof (Or.inl/Or.inr chain lengths verified at lines 71-83). README explicitly says what makes the children good leaves for a bounded prover: self-contained statement carrying its own hypotheses, a direct slice of the parent's goal, closing from named siblings in the same directory (plus measured 11/23-line proofs). | reviewer-generality |
| provenance-licence | accept | check_provenance passes: 4 code files byte-identical at commit a3210204ad8876e851e32f73dd97d882bf1ccd0a. Commit is recorded identically in entry.json, sources/flt-imperial/source.json and SOURCE.md. Licence is Apache-2.0 everywhere (entry.json, source.json, SOURCE.md) and matches the upstream LICENSE (fetched: Apache License 2.0) and the file header 'Released under Apache 2.0 license as described in the file LICENSE'. Permalinks use the pinned commit and correct paths FLT/Slop/PGL2/FiniteSubgroups/*.lean, and the cited line anchors (parent 54-83, docstring 24-26, wild 694/705-715, tame 1641/1649-1671) all match the byte-identical local copies. Source note links repo, commit and LICENSE correctly. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/ImperialCollegeLondon/FLT at commit `a3210204ad8876e851e32f73dd97d882bf1ccd0a`, under `Apache-2.0`; see the [source note](../../sources/flt-imperial/SOURCE.md) for the licence text and attribution.
