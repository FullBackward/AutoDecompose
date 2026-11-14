# Induction on the construction predicate IsGood for the easy direction of Seymour's theorem

| | |
|---|---|
| Kind | instance |
| Move | induction |
| Language | lean |
| Status | accepted |
| Source | [seymour](../../sources/seymour/SOURCE.md) at `2769b10cb73f` |
| Licence | `Apache-2.0` |

## Intent

A statement about every matroid built from graphic, cographic and R10 matroids
by 1-, 2- and 3-sums is reduced to a single induction on the construction
predicate `Matroid.IsGood`. The induction has one case per constructor, and each
case closes by the regularity lemma written for that constructor, so the whole
easy direction of Seymour's theorem is a 9-line glue over six named lemmas.

## The decomposition

### parent `Matroid.IsGood.isRegular`: [`Seymour/Results/EasyDirection.lean` lines 22-30](https://github.com/Ivan-Sergeyev/seymour/blob/2769b10cb73fda17bafc0f13890dc057a2f4ff2a/Seymour/Results/EasyDirection.lean#L22-L30) ([local copy](code/Seymour/Results/EasyDirection.lean))

```lean
/-- Corollary of the easy direction of the Seymour's theorem. -/
theorem Matroid.IsGood.isRegular {M : Matroid α} (hM : M.IsGood) : M.IsRegular := by
  induction hM with
  | graphic hM => exact hM.isRegular
  | cographic hM hM' => exact hM.isRegular hM'
  | @isomorphicR10 M e hM => simp [←M.isRegular_mapEquiv_iff e, hM]
  | is1sum hMMM hM _ _ ihₗ ihᵣ => exact hMMM.isRegular hM ihₗ ihᵣ
  | is2sum hMMM hM _ _ ihₗ ihᵣ => exact hMMM.isRegular hM ihₗ ihᵣ
  | is3sum hMMM hM _ _ ihₗ ihᵣ => exact hMMM.isRegular hM ihₗ ihᵣ
```

### context `Matroid.IsGood`: [`Seymour/Results/EasyDirection.lean` lines 11-20](https://github.com/Ivan-Sergeyev/seymour/blob/2769b10cb73fda17bafc0f13890dc057a2f4ff2a/Seymour/Results/EasyDirection.lean#L11-L20) ([local copy](code/Seymour/Results/EasyDirection.lean))

```lean
/-- Given matroid can be constructed from graphic matroids & cographics matroids & R10 using 1-sums & 2-sums & 3-sums. -/
inductive Matroid.IsGood : Matroid α → Prop
-- leaf constructors
| graphic {M : Matroid α} (hM : M.IsGraphic) : M.IsGood
| cographic {M : Matroid α} (hM : M.IsCographic) (hM' : M.Finite) : M.IsGood
| isomorphicR10 {M : Matroid α} {e : α ≃ Fin 10} (hM : M.mapEquiv e = matroidR10.toMatroid) : M.IsGood
-- fork constructors
| is1sum {M Mₗ Mᵣ : Matroid α} (hMMM : M.IsSum1of Mₗ Mᵣ) (hM : M.RankFinite) (hMₗ : Mₗ.IsGood) (hMᵣ : Mᵣ.IsGood) : M.IsGood
| is2sum {M Mₗ Mᵣ : Matroid α} (hMMM : M.IsSum2of Mₗ Mᵣ) (hM : M.RankFinite) (hMₗ : Mₗ.IsGood) (hMᵣ : Mᵣ.IsGood) : M.IsGood
| is3sum {M Mₗ Mᵣ : Matroid α} (hMMM : M.IsSum3of Mₗ Mᵣ) (hM : M.RankFinite) (hMₗ : Mₗ.IsGood) (hMᵣ : Mᵣ.IsGood) : M.IsGood
```

### child `Matroid.IsGraphic.isRegular`: [`Seymour/Matroid/Graphicness.lean` lines 174-177](https://github.com/Ivan-Sergeyev/seymour/blob/2769b10cb73fda17bafc0f13890dc057a2f4ff2a/Seymour/Matroid/Graphicness.lean#L174-L177) ([local copy](code/Seymour/Matroid/Graphicness.lean))

```lean
theorem Matroid.IsGraphic.isRegular {M : Matroid α} (hM : M.IsGraphic) :
    M.IsRegular := by
  obtain ⟨X, Y, A, hA, hMA⟩ := hM
  exact ⟨X, Y, A, hA.isTotallyUnimodular, hMA⟩
```

### child `Matroid.IsCographic.isRegular`: [`Seymour/Matroid/Comatroids.lean` lines 390-392](https://github.com/Ivan-Sergeyev/seymour/blob/2769b10cb73fda17bafc0f13890dc057a2f4ff2a/Seymour/Matroid/Comatroids.lean#L390-L392) ([local copy](code/Seymour/Matroid/Comatroids.lean))

```lean
lemma Matroid.IsCographic.isRegular {M : Matroid α} (hM_fin : M.Finite) (hM : M.IsCographic) :
    M.IsRegular :=
  M.dual_dual ▸ (Matroid.IsGraphic.isRegular hM).dual M.dual_finite
```

### child `Matroid.isRegular_mapEquiv_iff`: [`Seymour/Matroid/Regularity.lean` lines 92-100](https://github.com/Ivan-Sergeyev/seymour/blob/2769b10cb73fda17bafc0f13890dc057a2f4ff2a/Seymour/Matroid/Regularity.lean#L92-L100) ([local copy](code/Seymour/Matroid/Regularity.lean))

```lean
lemma Matroid.isRegular_mapEquiv_iff {α β : Type*} (M : Matroid α) (e : α ≃ β) : (M.mapEquiv e).IsRegular ↔ M.IsRegular := by
  constructor
  <;> intro ⟨X, Y, A, hA, hAM⟩
  · use e.symm '' X, e.symm '' Y, A.reindex (e.symm.image X) (e.symm.image Y), hA.reindex _ _
    rw [A.toMatroid_mapEquiv e.symm]
    aesop
  · use e '' X, e '' Y, A.reindex (e.image X) (e.image Y), hA.reindex _ _
    rw [A.toMatroid_mapEquiv e]
    aesop
```

### child `Matroid.IsSum1of.isRegular`: [`Seymour/Matroid/Sum1.lean` lines 235-243](https://github.com/Ivan-Sergeyev/seymour/blob/2769b10cb73fda17bafc0f13890dc057a2f4ff2a/Seymour/Matroid/Sum1.lean#L235-L243) ([local copy](code/Seymour/Matroid/Sum1.lean))

```lean
theorem Matroid.IsSum1of.isRegular {M Mₗ Mᵣ : Matroid α}
    (hMMM : M.IsSum1of Mₗ Mᵣ) (hM : M.RankFinite) (hMₗ : Mₗ.IsRegular) (hMᵣ : Mᵣ.IsRegular) :
    M.IsRegular := by
  obtain ⟨S, Sₗ, Sᵣ, _, _, hSSS, rfl, rfl, rfl⟩ := hMMM
  have hX : Finite S.X := S.finite_X_of_toMatroid_rankFinite hM
  obtain ⟨hXₗ, hXᵣ⟩ : Finite Sₗ.X ∧ Finite Sᵣ.X
  · simpa [standardReprSum1_X_eq hSSS, Set.finite_coe_iff] using hX
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hMₗ hMᵣ ⊢
  exact standardReprSum1_hasTuSigning hMₗ hMᵣ hSSS
```

### child `Matroid.IsSum2of.isRegular`: [`Seymour/Matroid/Sum2.lean` lines 400-408](https://github.com/Ivan-Sergeyev/seymour/blob/2769b10cb73fda17bafc0f13890dc057a2f4ff2a/Seymour/Matroid/Sum2.lean#L400-L408) ([local copy](code/Seymour/Matroid/Sum2.lean))

```lean
theorem Matroid.IsSum2of.isRegular {M Mₗ Mᵣ : Matroid α}
    (hMMM : M.IsSum2of Mₗ Mᵣ) (hM : M.RankFinite) (hMₗ : Mₗ.IsRegular) (hMᵣ : Mᵣ.IsRegular) :
    M.IsRegular := by
  obtain ⟨S, Sₗ, Sᵣ, _, _, _, _, _, _, hSSS, rfl, rfl, rfl⟩ := hMMM
  have hX : Finite S.X := S.finite_X_of_toMatroid_rankFinite hM
  obtain ⟨hXₗ, hXᵣ⟩ : Finite Sₗ.X ∧ Finite Sᵣ.X
  · simpa [standardReprSum2_X_eq hSSS, Set.finite_coe_iff] using hX
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hMₗ hMᵣ ⊢
  exact standardReprSum2_hasTuSigning hMₗ hMᵣ hSSS
```

### child `Matroid.IsSum3of.isRegular`: [`Seymour/Matroid/Sum3.lean` lines 3469-3477](https://github.com/Ivan-Sergeyev/seymour/blob/2769b10cb73fda17bafc0f13890dc057a2f4ff2a/Seymour/Matroid/Sum3.lean#L3469-L3477) ([local copy](code/Seymour/Matroid/Sum3.lean))

```lean
theorem Matroid.IsSum3of.isRegular {M Mₗ Mᵣ : Matroid α}
    (hMMM : M.IsSum3of Mₗ Mᵣ) (hM : M.RankFinite) (hMₗ : Mₗ.IsRegular) (hMᵣ : Mᵣ.IsRegular) :
    M.IsRegular := by
  obtain ⟨S, Sₗ, Sᵣ, _, _, _, _, _, _, _, _, _, _, hSSS, rfl, rfl, rfl⟩ := hMMM
  have hX : Finite S.X := S.finite_X_of_toMatroid_rankFinite hM
  obtain ⟨hXₗ, hXᵣ⟩ : Finite Sₗ.X ∧ Finite Sᵣ.X
  · simpa [standardReprSum3_X_eq hSSS, Set.finite_coe_iff] using hX
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hMₗ hMᵣ ⊢
  exact standardReprSum3_hasTuSigning hMₗ hMᵣ hSSS
```

### context `matroidR10.isRegular`: [`Seymour/Matroid/R10.lean` lines 51-61](https://github.com/Ivan-Sergeyev/seymour/blob/2769b10cb73fda17bafc0f13890dc057a2f4ff2a/Seymour/Matroid/R10.lean#L51-L61) ([local copy](code/Seymour/Matroid/R10.lean))

```lean
@[simp]
theorem matroidR10.isRegular : matroidR10.toMatroid.IsRegular := by
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning]
  use matrixR10Rat
  simp_rw [Matrix.IsTuSigningOf]
  refine ⟨?_, ↓↓?_⟩
  · rw [matrixR10Rat_eq_coe_matrixR10auxRat]
    apply matrixR10auxRat_isTotallyUnimodular.submatrix
  · rw [matrixR10Rat, matroidR10_B_eq]
    simp_rw [Set.coe_setOf, Matrix.map_apply, abs_eq_self]
    apply Nat.cast_nonneg
```

### How the parts fit

The parent inducts on `hM : M.IsGood`. `IsGood` (lines 12-20) is an inductive
predicate with three leaf constructors (`graphic`, `cographic`, `isomorphicR10`)
and three fork constructors (`is1sum`, `is2sum`, `is3sum`). `induction hM with`
produces one goal per constructor, and each branch of the glue is a single
`exact` (or one `simp`) handing the case to a named lemma. The lemma graph:

```
Matroid.IsGood.isRegular                 (induction on hM : M.IsGood)
├─ graphic       → Matroid.IsGraphic.isRegular     (leaf)
├─ cographic     → Matroid.IsCographic.isRegular   (leaf; reuses Matroid.IsGraphic.isRegular by duality)
├─ isomorphicR10 → Matroid.isRegular_mapEquiv_iff  (leaf; simp also uses matroidR10.isRegular)
├─ is1sum        → Matroid.IsSum1of.isRegular      (fork; consumes ihₗ, ihᵣ)
├─ is2sum        → Matroid.IsSum2of.isRegular      (fork; consumes ihₗ, ihᵣ)
└─ is3sum        → Matroid.IsSum3of.isRegular      (fork; consumes ihₗ, ihᵣ)
```

How each case closed:

- **graphic** (`exact hM.isRegular`): `Matroid.IsGraphic.isRegular` unfolds
  `IsGraphic` into a totally-unimodular matrix representation and returns it — a
  4-line leaf that closes on its own (up to `Matrix.IsGraphic.isTotallyUnimodular`,
  a named project lemma in the same file).
- **cographic** (`exact hM.isRegular hM'`): `Matroid.IsCographic.isRegular`
  proves a finite cographic matroid regular because its dual is graphic and
  regularity is preserved by duality — a 3-line leaf that closes from the
  *sibling* `Matroid.IsGraphic.isRegular`.
- **isomorphicR10** (`simp [← M.isRegular_mapEquiv_iff e, hM]`): regularity is
  invariant under `mapEquiv` (`Matroid.isRegular_mapEquiv_iff`), so `M.IsRegular`
  reduces to `matroidR10.toMatroid.IsRegular`, discharged by the `@[simp]` leaf
  `matroidR10.isRegular`.
- **is1sum / is2sum / is3sum** (`exact hMMM.isRegular hM ihₗ ihᵣ`): the two
  inductive hypotheses `ihₗ, ihᵣ` (the summands are regular) and the `RankFinite`
  hypothesis are fed to the matching sum theorem, which reduces regularity to a
  totally-unimodular signing (`standardReprSum1/2/3_hasTuSigning`).

Why each child is a good leaf: each is a *self-contained statement* —
`M.IsGraphic → M.IsRegular`, `M.IsSum2of Mₗ Mᵣ → M.RankFinite → Mₗ.IsRegular →
Mᵣ.IsRegular → M.IsRegular` — that never mentions the `IsGood` predicate, so it
can be stated and proved (or handed to a bounded prover) independently of the
induction. The three leaves close on their own or from named siblings
(`IsCographic` from `IsGraphic`; the R10 case from `isRegular_mapEquiv_iff` plus
the `@[simp]` `matroidR10.isRegular`). The three forks each carry a real proof,
but of a *bounded* shape: unfold the sum, obtain finiteness, rewrite both sides
to `hasTuSigning`, and apply the pre-computed signing lemma.

The longest chain of project lemmas below the main theorem that I checked runs
`Matroid.IsGood.isRegular → Matroid.IsCographic.isRegular →
Matroid.IsGraphic.isRegular → Matrix.IsGraphic.isTotallyUnimodular` (the last is
a ~35-line induction on `k` in `Graphicness.lean`, lines 136-171), so `shape.depth`
is 3 and the chain continues below it.

## Why it is good

1. The main theorem `Matroid.IsGood.isRegular` is declared in
   `Seymour/Results/EasyDirection.lean` at lines 22-30 (check; permalink
   `#L22-L30`).
2. The glue — the parent's induction, from `induction hM with` through the last
   `is3sum` case — is 9 lines, against six children of 4, 3, 9, 9, 9 and 9 lines
   (check; this is the shape measurement, `glue_lines = 9`,
   `child_lines = [4, 3, 9, 9, 9, 9]`).
3. No `sorry`, `admit` or `axiom` occurs in `Seymour/Results/EasyDirection.lean`
   (lines 1-36) (check; permalink to the whole file).
4. The glue cites the remapping lemma `isRegular_mapEquiv_iff` (line 27) to close
   the `isomorphicR10` case (check; permalink `#L27`).
5. The authors annotate the construction predicate "Given matroid can be
   constructed from graphic matroids & cographics matroids & R10 using 1-sums &
   2-sums & 3-sums" (line 11) and title the theorem a "Corollary of the easy
   direction of the Seymour's theorem" (line 22) (author-statement; permalinks
   `#L11` and `#L22`).

In my opinion the detail worth copying is that the *leaf lemmas are stated
without the predicate they are being inducted over*: none of the six children
mentions `IsGood`. Each regularity lemma is phrased in terms of the construction
it closes (`IsGraphic`, `IsCographic`, `IsSum1of`, …), so the induction's only job
is to route each constructor's hypotheses into the lemma that was written for it.
This is what lets the glue stay at 9 lines while the real content sits in six
separately checkable leaves. The cost is the same as the pattern's strength: a
constructor whose regularity lemma is missing stalls the induction, so the
leaf-per-constructor collection has to be complete before the glue is worth
writing.

## When to use it, and when not

Use it when a property `P` is to be shown for everything built by an inductive
construction predicate (`∀ M, M.IsGood → P M`), and `P` is already proved for
each leaf constructor and preserved by each fork constructor. Then `induction`
on the predicate yields exactly one case per constructor, and each case is a
single call to the regularity/preservation lemma written for that constructor.

Avoid it when a constructor's case still needs real new work, or when a leaf's
lemma is missing — the induction then stalls on that case and the glue stops
being a thin router. The fork cases here each demand a `RankFinite` side
condition and two inductive hypotheses, so the sum lemmas must be stated to take
those exactly; a sum lemma whose statement does not line up with the constructor's
hypotheses will not fit the `exact hMMM.isRegular hM ihₗ ihᵣ` call.

## Consequences

The induction creates one goal per constructor of `IsGood` (three leaves, three
forks). Each fork case carries two inductive hypotheses (`ihₗ`, `ihᵣ`) and a
`RankFinite` hypothesis, all fed to the matching sum lemma; each leaf case is
closed by a regularity lemma for that leaf (graphic, cographic,
R10-up-to-`mapEquiv`). The obligations the move creates are exactly those six
lemmas: an induction on an inductive predicate is a complete case analysis, so
there is no exhaustiveness obligation left over, but every constructor must have
a closing lemma. The known failure mode is a missing or mismatched leaf: if a
constructor's regularity lemma does not exist, or its side conditions (here
`RankFinite`) are not among the constructor's own hypotheses, that case stays
open and the glue no longer type-checks.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/blueprint.yml (Compile blueprint): builds the Lean project via leanprover/lean-action on push/PR to main; pinned commit 2769b10cb73fda17bafc0f13890dc057a2f4ff2a is the tip of main (identical to main) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: Matroid.IsGraphic.isRegular@Seymour/Results/EasyDirection.lean:23, Matroid.IsCographic.isRegular@Seymour/Results/EasyDirection.lean:23, Matroid.isRegular_mapEquiv_iff@Seymour/Results/EasyDirection.lean:27, Matroid.IsSum1of.isRegular@Seymour/Results/EasyDirection.lean:23, Matroid.IsSum2of.isRegular@Seymour/Results/EasyDirection.lean:23, Matroid.IsSum3of.isRegular@Seymour/Results/EasyDirection.lean:23; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 8 file(s) byte-identical at 2769b10cb73fda17bafc0f13890dc057a2f4ff2a | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(Matroid.IsGood.isRegular, Seymour/Results/EasyDirection.lean, 22-30) -> declared: Matroid.IsGood.isRegular is declared at Seymour/Results/EasyDirection.lean:23 | check_claims.py |
| 2 | verified | lines(parent, 9) -> lines: site parent has 9 lines | check_claims.py |
| 3 | verified | no_sorry(Seymour/Results/EasyDirection.lean, 1-36) -> no_sorry: none of sorry, admit, axiom in Seymour/Results/EasyDirection.lean:1-36 | check_claims.py |
| 4 | verified | cites(parent, isRegular_mapEquiv_iff) -> cites: isRegular_mapEquiv_iff occurs at Seymour/Results/EasyDirection.lean:27 | check_claims.py |
| 5 | verified | Seymour/Results/EasyDirection.lean line 11 docstring: '/-- Given matroid can be constructed from graphic matroids & cographics matroids & R10 using 1-sums & 2-sums & 3-sums. -/' and line 22 docstring: '/-- Corollary of the easy direction of the Seymour's theorem. -/' (confirmed by grep -n against code/) | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Opened code/Seymour/Results/EasyDirection.lean (parent 22-30, context 11-20), Graphicness.lean 174-177, Comatroids.lean 390-392, Regularity.lean 92-100, Sum1.lean 235-243, Sum2.lean 400-408, Sum3.lean 3469-3477, R10.lean 51-61; all match the README excerpts verbatim. The glue cites exactly six lemmas: graphic->Matroid.IsGraphic.isRegular, cographic->Matroid.IsCographic.isRegular, isomorphicR10->Matroid.isRegular_mapEquiv_iff (simp, also uses matroidR10.isRegular, disclosed as context), is1/2/3sum->Matroid.IsSum1of/2of/3of.isRegular; each branch is a single exact/simp, all 6 constructors covered, so it closes (no_sorry verified). child_lines [4,3,9,9,9,9] match site ranges; glue_lines 9 matches parent site 22-30; direct_lemmas 6 correct; depth 3 matches the documented chain IsGood.isRegular->IsCographic.isRegular->IsGraphic.isRegular->Matrix.IsGraphic.isTotallyUnimodular (Graphicness.lean ~136-171, verified), honestly marked 'continues below it'. | reviewer-correctness |
| generality | accept | Move stated generally: induction on an inductive construction predicate, one case per constructor, each closed by the lemma written for that constructor; use_when/avoid_when are phrased for an arbitrary property P over a construction predicate, not just IsRegular/IsGood. 'When not to use' is honest and specific: missing leaf lemma stalls the induction, and side conditions (RankFinite) must come from the constructor's own hypotheses - confirmed, the IsGood fork constructors carry hM : M.RankFinite and the Sum1/2/3of.isRegular lemmas take exactly (hMMM, hM, hM_l, hM_r). Consequences are honest: one goal per constructor, no leftover exhaustiveness obligation, failure mode = open case. It states what makes these good leaves for a bounded prover: each child is a self-contained statement that never names the IsGood predicate (verified from code - none of the six child declarations mentions IsGood), so it can be stated/proved or handed to a prover independently, and the forks have a bounded shape (unfold sum, obtain finiteness, rewrite both sides to hasTuSigning, apply precomputed signing lemma). | reviewer-generality |
| provenance-licence | accept | check_provenance passes (8 files byte-identical at 2769b10cb73fda17bafc0f13890dc057a2f4ff2a), so every permalink resolves to the pinned commit and matches the copied files. Commit is identical in entry.json source.commit, SOURCE.md, source.json and every permalink. Licence Apache-2.0 in entry.json/SOURCE.md/source.json matches sources/seymour/upstream-LICENSE (Apache License Version 2.0). Source note records commit, licence, licence_files=[LICENSE] and attribution, consistent with the README Source-and-licence section. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/Ivan-Sergeyev/seymour at commit `2769b10cb73fda17bafc0f13890dc057a2f4ff2a`, under `Apache-2.0`; see the [source note](../../sources/seymour/SOURCE.md) for the licence text and attribution.
