# Extensionality of the obtainable-set count for the Kuratowski 14-set

| | |
|---|---|
| Kind | instance |
| Move | extensionality |
| Language | lean |
| Status | accepted |
| Source | [mathlib4](../../sources/mathlib4/SOURCE.md) at `e1545ebed975` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T09:07:16Z |

## Intent

The parent `ncard_isObtainable_fourteenSet` proves that exactly 14 distinct
subsets of ℝ are obtainable from the 14-set `fourteenSet` by closure and
complement. Its proof is a short rewrite chain that lowers the `Set.ncard` to a
`Multiset.card`, then closes the one remaining set equality pointwise: `congr;
ext` turns it into a membership equivalence and `simp
[mem_theFourteen_iff_isObtainable]` finishes it.

## The decomposition

### parent `ncard_isObtainable_fourteenSet`: [`Archive/Examples/Kuratowski.lean` lines 238-241](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Examples/Kuratowski.lean#L238-L241) ([local copy](code/Archive/Examples/Kuratowski.lean))

```lean
theorem ncard_isObtainable_fourteenSet : {t | IsObtainable fourteenSet t}.ncard = 14 := by
  rw [← card_theFourteen fourteenSet, ← Multiset.toFinset_card_of_nodup
    nodup_theFourteen_fourteenSet, ← Set.ncard_coe_finset]
  congr; ext; simp [mem_theFourteen_iff_isObtainable]
```

### child `card_theFourteen`: [`Archive/Kuratowski.lean` lines 81-81](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Kuratowski.lean#L81-L81) ([local copy](code/Archive/Kuratowski.lean))

```lean
theorem card_theFourteen (s : Set X) : (theFourteen s).card = 14 := rfl
```

### child `nodup_theFourteen_fourteenSet`: [`Archive/Examples/Kuratowski.lean` lines 229-235](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Examples/Kuratowski.lean#L229-L235) ([local copy](code/Archive/Examples/Kuratowski.lean))

```lean
theorem nodup_theFourteen_fourteenSet : (theFourteen fourteenSet).Nodup :=
  nodup_theFourteen_of_nodup_theClosedSix_of_disjoint nodup_theClosedSix_fourteenSet <|
    Multiset.disjoint_iff_ne.mpr <| by
      rintro s hc _ ho rfl
      exact not_eq_univ_of_mem_theClosedSix_fourteenSet hc <| IsClopen.eq_univ
        ⟨isClosed_of_mem_theClosedSix hc, isOpen_of_mem_theOpenSix ho⟩
        (nonempty_of_mem_theClosedSix_fourteenSet hc)
```

### child `mem_theFourteen_iff_isObtainable`: [`Archive/Kuratowski.lean` lines 91-103](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Kuratowski.lean#L91-L103) ([local copy](code/Archive/Kuratowski.lean))

```lean
theorem mem_theFourteen_iff_isObtainable {s t : Set X} :
    t ∈ theFourteen s ↔ IsObtainable s t where
  mp h := by
    repeat
      obtain _ | ⟨_, h⟩ := h
      rotate_left
    all_goals
      repeat
        first
        | apply IsObtainable.complement
        | apply IsObtainable.closure
      exact IsObtainable.base
  mpr := (·.mem_theFourteen)
```

How the parts fit. The lemma graph below the parent is:

```
ncard_isObtainable_fourteenSet   (Examples 238-241)
├── card_theFourteen             (Kuratowski 81)      — theFourteen s has 14 elements
├── nodup_theFourteen_fourteenSet(Examples 229-235)   — the 14 sets are pairwise distinct
│     ├── nodup_theFourteen_of_nodup_theClosedSix_of_disjoint (Examples 114-128)
│     │     ├── theFourteen_eq_pair_add_theClosedSix_add_theOpenSix (Examples 70-73)
│     │     │     └── sum_map_theClosedSix_add_compl (Examples 66-68)
│     │     └── isClosed_of_mem_theClosedSix / isOpen_of_mem_theOpenSix (76-78, 81-83)
│     ├── nodup_theClosedSix_fourteenSet (Examples 194-203)
│     │     └── nodup_theClosedSix_theFourteen_iff (Examples 102-109)
│     │           └── kckckck_eq_kck (Kuratowski 71)
│     └── not_eq_univ_of_mem_theClosedSix_fourteenSet /
│         nonempty_of_mem_theClosedSix_fourteenSet (Examples 214-226, 206-211)
└── mem_theFourteen_iff_isObtainable (Kuratowski 91-103)  — t ∈ theFourteen s ↔ IsObtainable s t
      └── IsObtainable.mem_theFourteen (Kuratowski 85-88)
```

The glue does the bookkeeping in three rewrites and one pointwise step. `←
card_theFourteen fourteenSet` supplies the target `14` from the literal
multiset; `← Multiset.toFinset_card_of_nodup nodup_theFourteen_fourteenSet`
replaces the finset cardinality by the multiset cardinality, justified because
the fourteen operations produce no duplicates; `← Set.ncard_coe_finset` relates
the two cardinalities. What remains is the set equality `{t | IsObtainable
fourteenSet t} = theFourteen fourteenSet`, and that is where the move happens:
`congr; ext` reduces it to the pointwise membership equivalence, and `simp
[mem_theFourteen_iff_isObtainable]` closes it with the already-proved
characterization.

Why each child is a good leaf:

- `card_theFourteen` is self-contained and closes by `rfl`: `theFourteen s` is a
  literal 14-element multiset, so its `.card` normalises with no argument.
- `nodup_theFourteen_fourteenSet` is a self-contained statement — the 14 sets
  are pairwise distinct — whose proof closes on its own by combining two named
  siblings (`nodup_theFourteen_of_nodup_theClosedSix_of_disjoint` and
  `nodup_theClosedSix_fourteenSet`) with a short pointwise argument that no
  closed-six set is empty or the universe.
- `mem_theFourteen_iff_isObtainable` is a self-contained characterization; its
  two directions close by structural case analysis of multiset membership and of
  the inductive `IsObtainable` predicate respectively. It is exactly the fact
  the `ext` step needs.

`card_theFourteen` and `mem_theFourteen_iff_isObtainable` live in the theory
file `Archive/Kuratowski.lean`; the parent and `nodup_theFourteen_fourteenSet`
live in the example file `Archive/Examples/Kuratowski.lean` that realises the
bound, so both files are copied.

## Why it is good

1. The glue is 4 lines over 3 direct lemmas, whose child sites span 1, 7 and 13
   lines; the no-duplicates child closes through a chain of 4 project lemmas
   down to `sum_map_theClosedSix_add_compl` (`measurement`, spans at
   [L238-L241](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Examples/Kuratowski.lean#L238-L241),
   [L81](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Kuratowski.lean#L81),
   [L229-L235](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Examples/Kuratowski.lean#L229-L235),
   [L91-L103](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Kuratowski.lean#L91-L103)).
2. `card_theFourteen` is declared at `Archive/Kuratowski.lean` line 81
   (`check`, [permalink](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Kuratowski.lean#L81)).
3. The parent site cites `mem_theFourteen_iff_isObtainable` (`check`,
   [permalink](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Examples/Kuratowski.lean#L238-L241)).
4. No `sorry`, `admit` or `axiom` closes the parent or its child
   `nodup_theFourteen_fourteenSet` (`check`,
   [permalink](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Examples/Kuratowski.lean#L228-L241)).
5. The same characterization closes the companion "at most 14" theorem
   `ncard_isObtainable_le_fourteen` by `simp [Set.ext_iff,
   mem_theFourteen_iff_isObtainable]` (`known-use`,
   [permalink](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Kuratowski.lean#L107-L109)).

In my opinion the detail worth copying is that the `ext` step is never asked to
prove anything: the pointwise membership equivalence already exists as its own
iff lemma, so `ext` + `simp` is the whole of the final line. The extensionality
move is the last, cheapest step because the two hard facts (the count `14` and
the no-duplicates) were lifted out into their own lemmas first.

## When to use it, and when not

Use it when a cardinality goal `{t | P s t}.ncard = N` has (a) an explicit
finite description — a multiset whose `.card` is `rfl` — and (b) a
characterization lemma `t ∈ M s ↔ P s t`. Then the proof is a rewrite chain
down to a set equality, closed by `ext` and one `simp` with the
characterization.

Avoid it when the pointwise membership equivalence is not yet a lemma: then
`ext` leaves a genuine two-direction proof (an induction over `P`), which is the
real content and belongs in its own lemma before the `ext`. Also avoid it when
the cardinality fact is not `rfl` and needs its own argument, or when the set
equality is not the last step but feeds further structure.

## Consequences

The move concentrates the whole "obtainable = theFourteen" correspondence into
one iff lemma and leaves the value `14` and the no-duplicates obligation to two
named lemmas that are reused from elsewhere in the file. The `ext` step is cheap
only because that iff exists: without `mem_theFourteen_iff_isObtainable` the
pointwise goal would be a real two-direction induction on `IsObtainable`, not a
`simp`. If the characterization lemma drifts out of sync with the inductive
definition (for example, the 14 literal sets change), the `simp` silently stops
firing and the failure appears at the `ext`, far from the lemma that actually
needs fixing.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml (job 'ci') delegates to build_template.yml, whose 'build archive, counterexamples and wanted' step runs lake-build-with-retry.sh Archive Counterexamples Wanted on push to master; commit e1545ebed97594477bbd88b2fe948ffce56e5af2 is an ancestor of master (compare: behind_by 0), so Archive/Examples/Kuratowski.lean and Archive/Kuratowski.lean are built by CI on the default branch | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: card_theFourteen@Archive/Examples/Kuratowski.lean:239, nodup_theFourteen_fourteenSet@Archive/Examples/Kuratowski.lean:240, mem_theFourteen_iff_isObtainable@Archive/Examples/Kuratowski.lean:241; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at e1545ebed97594477bbd88b2fe948ffce56e5af2 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | read code: parent ncard_isObtainable_fourteenSet at Archive/Examples/Kuratowski.lean L238-L241 is exactly 4 lines; children card_theFourteen (Archive/Kuratowski.lean L81, 1 line), nodup_theFourteen_fourteenSet (Examples L229-L235, 7 lines), mem_theFourteen_iff_isObtainable (Archive/Kuratowski.lean L91-L103, 13 lines); depth-4 chain confirmed: nodup_theFourteen_fourteenSet L230 calls nodup_theFourteen_of_nodup_theClosedSix_of_disjoint (def L114), whose body L117 rw's theFourteen_eq_pair_add_theClosedSix_add_theOpenSix (def L71), whose body L73 rw's sum_map_theClosedSix_add_compl (def L66) | verifier |
| 2 | verified | declared(card_theFourteen, Archive/Kuratowski.lean, 81-81) -> declared: card_theFourteen is declared at Archive/Kuratowski.lean:81 | check_claims.py |
| 3 | verified | cites(parent, mem_theFourteen_iff_isObtainable) -> cites: mem_theFourteen_iff_isObtainable occurs at Archive/Examples/Kuratowski.lean:241 | check_claims.py |
| 4 | verified | no_sorry(Archive/Examples/Kuratowski.lean, 228-241) -> no_sorry: none of sorry, admit, axiom in Archive/Examples/Kuratowski.lean:228-241 | check_claims.py |
| 5 | verified | read Archive/Kuratowski.lean L107-L109: theorem ncard_isObtainable_le_fourteen (s : Set X) : {t | IsObtainable s t}.ncard <= 14 := by / convert! Set.ncard_coe_finset _ (theFourteen s).toFinset_card_le / simp [Set.ext_iff, mem_theFourteen_iff_isObtainable]; the characterization closes the companion 'at most 14' theorem by that simp, as claimed | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent ncard_isObtainable_fourteenSet (Examples/Kuratowski.lean 238-241) is a 4-line rw chain + congr; ext; simp that cites exactly card_theFourteen (239), nodup_theFourteen_fourteenSet (240) and mem_theFourteen_iff_isObtainable (241); the other two rw terms are Mathlib lemmas. The three children are exactly the project lemmas the parent uses. Each child's statement and closing method match the code: card_theFourteen := rfl (Kuratowski 81, 1 line); nodup_theFourteen_fourteenSet := nodup_theFourteen_of_nodup_theClosedSix_of_disjoint nodup_theClosedSix_fourteenSet <| Multiset.disjoint_iff_ne.mpr (Examples 229-235, 7 lines); mem_theFourteen_iff_isObtainable by mp/mpr (Kuratowski 91-103, 13 lines). Shape numbers verified: direct_lemmas=3, glue_lines=4 (parent 238-241), child_lines=[1,7,13], depth=4 via the chain parent->nodup_theFourteen_fourteenSet->nodup_theFourteen_of_nodup_theClosedSix_of_disjoint->theFourteen_eq_pair_add_theClosedSix_add_theOpenSix->sum_map_theClosedSix_add_compl (all cites read and confirmed). Provenance pass: 2 files byte-identical. | reviewer-correctness |
| generality | accept | Generality lens: move is stated parametrically (goal shape {t | P s t}.ncard = N, multiset M s, characterization t ∈ M s ↔ P s t), so it applies beyond the Kuratowski example; 'when not to use' lists three concrete, honest conditions (iff not yet a lemma → ext leaves a real two-direction proof; cardinality not rfl; set equality feeds further structure); consequences are specific and honest including the failure mode where simp silently stops firing at the ext if the characterization drifts from the inductive definition. README's 'Why each child is a good leaf' says what makes the lemmas good bounded-prover leaves: each is self-contained and closes on its own (rfl / structural case analysis), with child spans 1, 7, 13 lines. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are consistent with the copied files. check_provenance.py passes (2 files byte-identical at e1545ebed97594477bbd88b2fe948ffce56e5af2); both sha256 hashes in entry.json match the copied files (b715076e… for Archive/Examples/Kuratowski.lean 11283B, 7cb15c93… for Archive/Kuratowski.lean 4617B) and file sizes match; every permalink uses the pinned commit e1545ebed97594477bbd88b2fe948ffce56e5af2, matching source.json, SOURCE.md and entry.json source.commit; licence Apache-2.0 is consistent across entry.json, source.json, SOURCE.md and the copied upstream-LICENSE (Apache License Version 2.0); all cited line ranges (Kuratowski.lean:81, 91-103; Examples/Kuratowski.lean:229-235, 238-241) open to exactly the quoted declarations. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover-community/mathlib4 at commit `e1545ebed97594477bbd88b2fe948ffce56e5af2`, under `Apache-2.0`; see the [source note](../../sources/mathlib4/SOURCE.md) for the licence text and attribution.
