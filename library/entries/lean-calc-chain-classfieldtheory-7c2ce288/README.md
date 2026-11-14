# Calc chain assembling two exact short complexes into the natural isomorphism up ≅ down (finite cyclic group)

| | |
|---|---|
| Kind | instance |
| Move | calc-chain |
| Language | lean |
| Status | accepted |
| Source | [classfieldtheory](../../sources/classfieldtheory/SOURCE.md) at `1e7f5dbe3835` |
| Licence | `Apache-2.0` |

## Intent

`upIsoDown` proves that the up and down dimension-shift functors of a finite
cyclic group are naturally isomorphic, `up (R := R) (G := G) ≅ down`, by running
a five-step `calc` chain of natural isomorphisms through the two exact short
complexes `periodSeq₁`/`periodSeq₂`. The two substantive steps are closed by the
exactness lemmas `exact_periodSeq₁` and `exact_periodSeq₂`; the remaining steps
are structural isomorphisms supplied by the library.

## The decomposition

### parent `upIsoDown`: [`ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean` lines 384-392](https://github.com/kbuzzard/ClassFieldTheory/blob/1e7f5dbe38358bd37a0643bb0db2dd3a436e6cb7/ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean#L384-L392) ([local copy](code/ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean))

```lean
def upIsoDown : up (R := R) (G := G) ≅ down := calc
    up (R := R) (G := G)
      ≅ periodSeq₁Functor ⋙ ShortComplex.gFunctor ⋙ coim :=
      ShortComplex.cokerIsoCoim periodSeq₁Functor exact_periodSeq₁
    _ ≅ (periodSeq₁Functor ⋙ ShortComplex.gFunctor) ⋙ coim :=
      (Functor.associator ..).symm
    _ ≅ (periodSeq₂Functor ⋙ ShortComplex.fFunctor) ⋙ im := Functor.isoWhiskerLeft _ coimIsoIm
    _ ≅ periodSeq₂Functor ⋙ ShortComplex.fFunctor ⋙ im := Functor.associator ..
    _ ≅ down := (ShortComplex.kerIsoIm periodSeq₂Functor exact_periodSeq₂).symm
```

### child `exact_periodSeq₁`: [`ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean` lines 356-368](https://github.com/kbuzzard/ClassFieldTheory/blob/1e7f5dbe38358bd37a0643bb0db2dd3a436e6cb7/ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean#L356-L368) ([local copy](code/ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean))

```lean
lemma exact_periodSeq₁ : (periodSeq₁ M).Exact := by
  -- `S` is `ShortComplex (Rep R G)` here, but `Rep R G` is equivalent to `ModuleCat R[G]`.
  -- This step transfers our task to exactness in `ModuleCat R[G]`.
  rw [M.periodSeq₁.rep_exact_iff]
  intro w hw
  have hinj : Function.Injective (ind₁'_iso_coind₁'.inv.app M).hom :=
    (mono_iff_injective _).1 inferInstance
  simp only [periodSeq₁_g, periodSeq₁_f, Representation.IntertwiningMap.mem_ker, hom_comp,
    Representation.IntertwiningMap.comp_apply, Iso.app_inv, map_eq_zero_iff _ hinj,
    Representation.IntertwiningMap.mem_range] at hw ⊢
  rw [coe_map₁_app_hom] at hw
  rw [coe_coind₁'_ι_app_hom]
  exact LinearMap.mem_range.1 (Representation.map₁_ker.le (LinearMap.mem_ker.2 hw))
```

### child `exact_periodSeq₂`: [`ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean` lines 371-381](https://github.com/kbuzzard/ClassFieldTheory/blob/1e7f5dbe38358bd37a0643bb0db2dd3a436e6cb7/ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean#L371-L381) ([local copy](code/ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean))

```lean
lemma exact_periodSeq₂ : (periodSeq₂ M).Exact := by
  rw [M.periodSeq₂.rep_exact_iff]
  intro w hw
  simp only [periodSeq₂_g, periodSeq₂_f, Representation.IntertwiningMap.mem_ker, hom_comp,
    Representation.IntertwiningMap.comp_apply, Iso.app_inv,
    Representation.IntertwiningMap.mem_range] at hw ⊢
  rw [coe_ind₁'_π_app_hom] at hw
  rw [coe_map₁_app_hom, coe_ind₁'_iso_coind₁'_inv_app_hom]
  obtain ⟨y, rfl⟩ :=
    LinearMap.mem_range.1 (Representation.map₂_range.ge (LinearMap.mem_ker.2 hw))
  exact ⟨(y : G → M.V), by simp [Representation.linearEquivFunOnFinite_symm_map₁]⟩
```

### child `periodSeq₁Functor`: [`ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean` lines 345-347](https://github.com/kbuzzard/ClassFieldTheory/blob/1e7f5dbe38358bd37a0643bb0db2dd3a436e6cb7/ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean#L345-L347) ([local copy](code/ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean))

```lean
@[simps] def periodSeq₁Functor : Rep R G ⥤ ShortComplex (Rep R G) where
  obj := periodSeq₁
  map {M N} f := ShortComplex.homMk f (coind₁'.map f) (ind₁'.map f) (by cat_disch) (by cat_disch)
```

### child `periodSeq₂Functor`: [`ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean` lines 351-353](https://github.com/kbuzzard/ClassFieldTheory/blob/1e7f5dbe38358bd37a0643bb0db2dd3a436e6cb7/ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean#L351-L353) ([local copy](code/ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean))

```lean
@[simps] def periodSeq₂Functor : Rep R G ⥤ ShortComplex (Rep R G) where
  obj := periodSeq₂
  map {M N} f := ShortComplex.homMk (coind₁'.map f) (ind₁'.map f) f (by cat_disch) (by cat_disch)
```

### context `module-docstring`: [`ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean` lines 10-31](https://github.com/kbuzzard/ClassFieldTheory/blob/1e7f5dbe38358bd37a0643bb0db2dd3a436e6cb7/ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean#L10-L31) ([local copy](code/ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean))

```lean
/-!
Let `M : Rep R G`, where `G` is a finite cyclic group.
We construct an exact sequence

  `0 ⟶ M ⟶ coind₁'.obj M ⟶ ind₁'.obj M ⟶ M ⟶ 0`.

In fact, we construct this as two exact short complexes

`periodSeq₁Functor : Rep R G ⥤ ShortComplex (Rep R G)`
sending `M` to the exact complex `periodSeq₁ M : M ⟶ coind₁'.obj M ⟶ ind₁'.obj M`
and
`periodSeq₂Functor : Rep R G ⥤ ShortComplex (Rep R G)`
sending `M` to the exact complex `periodSeq₂ M : coind₁'.obj M ⟶ ind₁'.obj M ⟶ M`

Using this sequence, we construct an isomorphism

  `dimensionShift.up.obj M ≅ dimensionShift.down.obj M`.

Using this, construct isomorphisms

  `Hⁿ⁺¹(G,M) ≅ Hⁿ⁺³(G,M)`.

```

How the parts fit. The parent `upIsoDown` is a five-link `calc` chain of
natural isomorphisms from `up (R := R) (G := G)` to `down`. Link 1
(`ShortComplex.cokerIsoCoim periodSeq₁Functor exact_periodSeq₁`) and link 5
(`ShortComplex.kerIsoIm periodSeq₂Functor exact_periodSeq₂`) are the substantive
steps: each is a library isomorphism that consumes an exactness proof. Links 2,
3 and 4 (`Functor.associator`, `Functor.isoWhiskerLeft`, `Functor.associator`)
are structural re-associations closed by the library, and `coimIsoIm` is the
library isomorphism `coim ≅ im`.

The lemma graph (project lemmas only; an arrow means "is cited in the proof of"):

```
upIsoDown
├─ periodSeq₁Functor  (leaf: naturality closed by cat_disch)
├─ exact_periodSeq₁ ──> Representation.map₁_ker ──> Representation.map₁_comp_coind_ι (leaf: ext; simp)
├─ periodSeq₂Functor  (leaf: naturality closed by cat_disch)
└─ exact_periodSeq₂ ──> Representation.map₂_range ──> Representation.ind₁'_π_comp_map₂ ──> Representation.map₂_comp_lsingle (leaf: ext; simp)
```

so the longest chain of project lemmas below `upIsoDown` has depth 4
(`upIsoDown → exact_periodSeq₂ → map₂_range → ind₁'_π_comp_map₂ →
map₂_comp_lsingle`, all in the same copied file).

Each child is a good leaf. `exact_periodSeq₁` and `exact_periodSeq₂` are
self-contained statements (`(periodSeq₁ M).Exact`, `(periodSeq₂ M).Exact`): each
unwraps to `ModuleCat R[G]` and closes by citing a named kernel-range equality —
`Representation.map₁_ker` (line 368) and `Representation.map₂_range` (line 380)
respectively. `periodSeq₁Functor` and `periodSeq₂Functor` are functor
definitions whose only obligations are the two naturality squares, each closed
by `cat_disch`. The deeper lemmas `map₁_ker` (line 82) and `map₂_range` (line
145) carry the actual mathematics (finiteness and cyclicity of `G`), but they
sit in the same file and close on their own, so the glue never has to see them.

## Why it is good

1. The glue is 9 lines, one `calc` step per isomorphism, recorded in `shape` as
   `glue_lines = 9` (claim 1, `check`; parent site lines 384-392).
2. The whole copied file closes with no `sorry`/`admit`/`axiom`, so the parent
   and all four children really close (claim 2, `check`; the whole file).
3. `upIsoDown` occurs 3 times in the file: once as the declaration and twice
   reused as `upIsoDown.symm`, in `periodicCohomologyAux` (line 401) and
   `periodicTateCohomologyAux` (line 447), which is what drives the
   2-periodicity results (claim 3, `check`).
4. The module docstring states the plan the proof follows — "Using this
   sequence, we construct an isomorphism `dimensionShift.up.obj M ≅
   dimensionShift.down.obj M`" — and its consequence "Using this, construct
   isomorphisms `Hⁿ⁺¹(G,M) ≅ Hⁿ⁺³(G,M)`" (claim 4, `author-statement`, lines
   10-31).

In my opinion the detail worth copying is that the two substantive links of the
`calc` chain are made into named exactness lemmas first, so the `calc` itself is
almost purely structural and every non-structural obligation is exactly one
lemma.

## When to use it, and when not

Use this when the target isomorphism factors through a short exact sequence (or
short complex) the file has already built, so `cokerIsoCoim`/`kerIsoIm` plus one
exactness lemma per link supply the content and the remaining links are
structural (associators, whiskering). Avoid it when the chain is a plain
equality rewrite with no per-step content lemma, when the exactness lemmas are
not yet proved (they are the real work), or when the steps need genuinely
different arguments that do not factor through one short complex.

## Consequences

The chain creates one obligation per substantive link — `exact_periodSeq₁` for
the `cokerIsoCoim` step and `exact_periodSeq₂` for the `kerIsoIm` step — plus
the two functors that package the short complexes; the three structural links
(`Functor.associator` twice, `Functor.isoWhiskerLeft` once) are discharged by
the library, not by project lemmas. Each exactness lemma reduces to a
kernel-range equality (`Representation.map₁_ker`, `Representation.map₂_range`)
that carries the real finiteness/cyclicity argument; if one were false, the
corresponding `calc` step would not close.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push.yml; job 'build' runs leanprover/lean-action 'Build and lint the project' on push to main; commit 1e7f5dbe38358bd37a0643bb0db2dd3a436e6cb7 is on main (default branch) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: exact_periodSeq₁@ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean:387, exact_periodSeq₂@ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean:392, periodSeq₁Functor@ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean:386, periodSeq₂Functor@ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean:390; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 1e7f5dbe38358bd37a0643bb0db2dd3a436e6cb7 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(parent, 9) -> lines: site parent has 9 lines | check_claims.py |
| 2 | verified | no_sorry(ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean, 1-534) -> no_sorry: none of sorry, admit, axiom in ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean:1-534 | check_claims.py |
| 3 | verified | count(upIsoDown, 3, ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean) -> count: upIsoDown occurs 3 times in 1 file(s) matching ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean | check_claims.py |
| 4 | verified | module docstring lines 10-31 of code/ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean: 'Using this sequence, we construct an isomorphism' + 'dimensionShift.up.obj M ≅ dimensionShift.down.obj M' (lines 24-26) and 'Using this, construct isomorphisms' + 'Hⁿ⁺¹(G,M) ≅ Hⁿ⁺³(G,M)' (lines 28-30), both quoted verbatim | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent upIsoDown (lines 384-392, 9 lines) is a 5-link calc chain as described; it cites exactly the four children (periodSeq1Functor L386/388, exact_periodSeq1 L387, periodSeq2Functor L390/391, exact_periodSeq2 L392) plus library lemmas (cokerIsoCoim/kerIsoIm/associator/isoWhiskerLeft/coimIsoIm) only, so children are exactly the project lemmas the glue uses. Closing methods match code verbatim: exact_periodSeq1 ends in Representation.map1_ker.le (L368), exact_periodSeq2 in Representation.map2_range.ge (L380), both functor defs close their two naturality goals with cat_disch. No sorry/admit/axiom tokens anywhere in the 533-line file (grep empty), so it closes. Shape numbers correct: direct_lemmas=4 (the 4 children), depth=4 (upIsoDown -> exact_periodSeq2 -> map2_range L145 -> ind1'_pi_comp_map2 L139 -> map2_comp_lsingle L127, verified in code), glue_lines=9 (site 384-392), child_lines=[13,11,3,3] matching sites 356-368, 371-381, 345-347, 351-353. Provenance: file byte-identical at 1e7f5dbe3835. | reviewer-correctness |
| generality | accept | Move generalised correctly: applicability.use_when states the shape ('target isomorphism factors through a short exact sequence/short complex the file has built; coker/ker isos plus one exactness lemma per link supply content; remaining links are structural associators/whiskering'), not the finite-cyclic-group specifics. avoid_when gives three concrete failure modes (plain equality rewrite with no content lemma; exactness lemmas unproved — 'they are the real work'; steps needing genuinely different arguments not through one short complex) — honest and specific. Consequences are specific and non-overclaiming: one obligation per substantive link, three structural links via library, exactness reducing to kernel-range equality (map1_ker line 82 / map2_range line 145) carrying the finiteness/cyclicity; says a false one would not close. 'Each child is a good leaf' paragraph answers the bounded-prover question: self-contained statements unwrapping to ModuleCat and closing by citing one named kernel-range equality, functor defs whose only obligations are naturality squares closed by cat_disch, deeper math hidden below the glue (depth-4 graph shown). I read the cited ranges (82, 145, 395-402, 439-449) and the line numbers/reuse (upIsoDown.symm at 401/447) match the entry. | reviewer-generality |
| provenance-licence | accept | Provenance check passes: 1 file byte-identical at pinned commit 1e7f5dbe38358bd37a0643bb0db2dd3a436e6cb7. source.json/SOURCE.md/entry.json all agree on url https://github.com/kbuzzard/ClassFieldTheory, commit, and licence Apache-2.0; upstream-LICENSE is the Apache 2.0 text. Permalinks use the pinned commit, correct path ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean, and correct line ranges (parent 384-392 = 9 lines; children 356-368, 371-381, 345-347, 351-353; context 10-31 all match the copied file verbatim; known_uses 395-402 and 439-449 both show upIsoDown.symm reuse). | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/kbuzzard/ClassFieldTheory at commit `1e7f5dbe38358bd37a0643bb0db2dd3a436e6cb7`, under `Apache-2.0`; see the [source note](../../sources/classfieldtheory/SOURCE.md) for the licence text and attribution.
