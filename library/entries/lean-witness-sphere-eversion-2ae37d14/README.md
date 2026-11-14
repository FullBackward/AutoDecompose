# Sphere eversion: obtain the witness from the immersion h-principle

| | |
|---|---|
| Kind | instance |
| Move | witness |
| Language | lean |
| Status | accepted |
| Source | [sphere-eversion](../../sources/sphere-eversion/SOURCE.md) at `33ab3d626854` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-12T15:00:42Z |

## Intent

The theorem is an existential goal — find a family `f : ℝ → 𝕊² → E` of immersions
turning the sphere inside-out. The decomposition is: obtain the witness `f` in one
step from the parametric immersion h-principle applied to a formal eversion, then
discharge the four conjuncts (smoothness, value at 0, value at 1, immersion) one per
hole, each against a bundle projection or a named endpoint lemma.

## The decomposition

### parent `sphere_eversion`: [`SphereEversion/Global/Immersion.lean` lines 307-340](https://github.com/leanprover-community/sphere-eversion/blob/33ab3d626854a0f0f04ed5772e3102d652e96475/SphereEversion/Global/Immersion.lean#L307-L340) ([local copy](code/SphereEversion/Global/Immersion.lean))

```lean
theorem sphere_eversion :
    ∃ f : ℝ → 𝕊² → E,
      CMDiff ∞ ↿f ∧ (f 0 = fun x : 𝕊² ↦ (x : E)) ∧ (f 1 = fun x : 𝕊² ↦ -(x : E)) ∧
        ∀ t, Immersion (𝓡 2) 𝓘(ℝ, E) (f t) ∞ := by
  classical
  let ω : Orientation ℝ E (Fin 3) :=
    ((stdOrthonormalBasis _ _).reindex <|
          finCongr (Fact.out : finrank ℝ E = 3)).toBasis.orientation
  have rankE : finrank ℝ E = 3 := Fact.out
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_eq_succ rankE
  have ineq_rank : finrank ℝ (EuclideanSpace ℝ (Fin 2)) < finrank ℝ E := by simp [rankE]
  let ε : 𝕊² → ℝ := fun _ ↦ 1
  have hε_pos : ∀ x, 0 < ε x := fun _ ↦ zero_lt_one
  have hε_cont : Continuous ε := continuous_const
  have : Nontrivial E := nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ E = 3)
  have : Nonempty (sphere 0 1 : Set E) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
  rcases(immersionRel_satisfiesHPrincipleWith (𝓡 2) 𝕊² 𝓘(ℝ, E) E 𝓘(ℝ, ℝ) ℝ ineq_rank
          ((Finite.isClosed (by simp : ({0, 1} : Set ℝ).Finite)).prod isClosed_univ) hε_pos
          hε_cont).bs
      (formalEversion E ω) (formalEversion_hol_near_zero_one E ω) with
    ⟨f, h₁, h₂, -, h₅⟩
  have := h₂.forall_mem principal_le_nhdsSet
  refine ⟨f, h₁, ?_, ?_, ?_/-h₅-/⟩
  · ext x
    rw [this (0, x) (by simp)]
    convert! formalEversion_zero E ω x
  · ext x
    rw [this (1, x) (by simp)]
    convert! formalEversion_one E ω x
  · exact fun t ↦ {
      contMDiff := h₁.uncurry_left 𝓘(ℝ, ℝ) (𝓡 2) 𝓘(ℝ, E) t
      diff_injective := h₅ t
    }
```

### child `immersionRel_satisfiesHPrincipleWith`: [`SphereEversion/Global/Immersion.lean` lines 119-124](https://github.com/leanprover-community/sphere-eversion/blob/33ab3d626854a0f0f04ed5772e3102d652e96475/SphereEversion/Global/Immersion.lean#L119-L124) ([local copy](code/SphereEversion/Global/Immersion.lean))

```lean
/-- parametric h-principle for immersions. -/
theorem immersionRel_satisfiesHPrincipleWith
    [T2Space P] [SigmaCompactSpace P] [T2Space M] [SigmaCompactSpace M] [SigmaCompactSpace M']
    (h : finrank ℝ E < finrank ℝ E') (hC : IsClosed C) (hε_pos : ∀ x, 0 < ε x)
    (hε_cont : Continuous ε) : (immersionRel I M I' M').SatisfiesHPrincipleWith IP C ε :=
  (immersionRel_ample I I' h).satisfiesHPrincipleWith (immersionRel_open I I') hC hε_pos hε_cont
```

### child `formalEversion_hol_near_zero_one`: [`SphereEversion/Global/Immersion.lean` lines 243-256](https://github.com/leanprover-community/sphere-eversion/blob/33ab3d626854a0f0f04ed5772e3102d652e96475/SphereEversion/Global/Immersion.lean#L243-L256) ([local copy](code/SphereEversion/Global/Immersion.lean))

```lean
theorem formalEversion_hol_near_zero_one :
    ∀ᶠ s : ℝ × 𝕊² near {0, 1} ×ˢ univ, (formalEversion E ω s.1).toOneJetSec.IsHolonomicAt s.2 := by
  have : (Iio (1 / 4 : ℝ) ∪ Ioi (3 / 4)) ×ˢ (univ : Set 𝕊²) ∈ 𝓝ˢ (({0, 1} : Set ℝ) ×ˢ univ) := by
    refine ((isOpen_Iio.union isOpen_Ioi).prod isOpen_univ).mem_nhdsSet.mpr ?_
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    refine ⟨?_, mem_univ _⟩
    simp_rw [mem_insert_iff, mem_singleton_iff] at hs
    rcases hs with (rfl | rfl)
    · exact Or.inl (show (0 : ℝ) < 1 / 4 by norm_num)
    · exact Or.inr (show (3 / 4 : ℝ) < 1 by norm_num)
  filter_upwards [this]
  rintro ⟨t, x⟩ ⟨ht | ht, _hx⟩
  · exact formalEversionHolAtZero E ω ht x
  · exact formalEversionHolAtOne E ω ht x
```

### child `formalEversion_zero`: [`SphereEversion/Global/Immersion.lean` lines 209-209](https://github.com/leanprover-community/sphere-eversion/blob/33ab3d626854a0f0f04ed5772e3102d652e96475/SphereEversion/Global/Immersion.lean#L209-L209) ([local copy](code/SphereEversion/Global/Immersion.lean))

```lean
theorem formalEversion_zero (x : 𝕊²) : (formalEversion E ω 0).bs x = x := by simp
```

### child `formalEversion_one`: [`SphereEversion/Global/Immersion.lean` lines 211-211](https://github.com/leanprover-community/sphere-eversion/blob/33ab3d626854a0f0f04ed5772e3102d652e96475/SphereEversion/Global/Immersion.lean#L211-L211) ([local copy](code/SphereEversion/Global/Immersion.lean))

```lean
theorem formalEversion_one (x : 𝕊²) : (formalEversion E ω 1).bs x = -x := by simp
```

How the parts fit. The parent is an `∃` over a family of maps with four conjuncts.
The glue (lines 311-340) first fixes the orientation `ω`, the rank facts (`rankE`,
`ineq_rank`), and an `ε` with `hε_pos`/`hε_cont`, then obtains the witness `f` in one
step:

```
sphere_eversion (307-340)
├─ witness f:  immersionRel_satisfiesHPrincipleWith (119-124) .bs  ← instantiate thm:open_ample at the immersion relation
│      = (immersionRel_ample …).satisfiesHPrincipleWith (immersionRel_open …)   [General section, lines 66/88]
├─ holonomicity hypothesis:  formalEversion_hol_near_zero_one (243-256)
│      ├─ formalEversionHolAtZero (214-223)
│      └─ formalEversionHolAtOne (226-241)
├─ f 0 = inclusion:  formalEversion_zero (209)
└─ f 1 = antipodal:  formalEversion_one (211)
```

`rcases (immersionRel_satisfiesHPrincipleWith …).bs (formalEversion E ω)
(formalEversion_hol_near_zero_one E ω) with ⟨f, h₁, h₂, -, h₅⟩` (lines 324-328) names
the witness `f` and binds the bundle's five fields: `h₁` (smoothness of `↿f`), `h₂`
(agreement with the formal solution near the closed set `{0,1} ×ˢ univ`), a dropped
fourth field, and `h₅` (injectivity of the derivative). `refine ⟨f, h₁, ?_, ?_, ?_⟩`
(line 330) then turns the four conjuncts into: smoothness (closed by `h₁`), value at 0,
value at 1, and immersion.

- *smoothness* is `h₁` directly.
- *`f 0 = inclusion`* (331-333): `h₂.forall_mem principal_le_nhdsSet` gives that the
  formal solution's base map equals `f`'s on `{0,1} ×ˢ univ`; `convert!
  formalEversion_zero` closes it (the `convert!` bridges a definitional gap, as the
  endpoint lemma is stated for the reparametrized `formalEversion`).
- *`f 1 = antipodal`* (334-336): the same, via `formalEversion_one`.
- *every `f t` is an immersion* (337-340): an `Immersion` structure built
  field-by-field from `h₁.uncurry_left` (smoothness) and `h₅` (injectivity).

Each child is a good leaf — a self-contained statement whose proof closes on its own or
from named siblings:

- `immersionRel_satisfiesHPrincipleWith` (119-124) states the parametric h-principle
  specialised to the immersion relation and closes in one line by applying the general
  open+ample h-principle to the same-file `immersionRel_ample` (88) and
  `immersionRel_open` (66), without unfolding the relation.
- `formalEversion_hol_near_zero_one` (243-256) states holonomicity of the formal
  eversion near `{0,1} ×ˢ univ`; it exhibits the neighbourhood `(Iio (1/4) ∪ Ioi
  (3/4)) ×ˢ univ`, then the two cases close by the sibling lemmas
  `formalEversionHolAtZero` (214) and `formalEversionHolAtOne` (226). This is the
  depth-2 chain recorded in `shape.depth`.
- `formalEversion_zero` (209) and `formalEversion_one` (211) are one-line `simp` facts
  (via the `[simp]` lemma `formalEversion_bs`, 204-207) that the formal solution's base
  map at times 0 and 1 is the inclusion and the antipodal map.

The child `immersionRel_satisfiesHPrincipleWith` is the Lean counterpart of the two
blueprint lemmas the node's proof `\uses` (`thm:open_ample`,
`lem:open_ample_immersion`): `immersionRel_open_ample` (98) is exactly
`lem:open_ample_immersion`, and the general `RelMfld.Ample.satisfiesHPrincipleWith`
(Gromov.lean) is `thm:open_ample`.

## Why it is good

1. The parent closes from four named children plus the same-file helper
   `ContMDiff.uncurry_left`, none of which the proof unfolds:
   `immersionRel_satisfiesHPrincipleWith` yields the witness,
   `formalEversion_hol_near_zero_one` supplies its holonomicity hypothesis,
   `formalEversion_zero` and `formalEversion_one` close the two endpoint conjuncts,
   and `ContMDiff.uncurry_left` (line 338) turns the smoothness projection `h₁` into
   the `contMDiff` field of each `f t`
   (*check*, [lines 307-340](https://github.com/leanprover-community/sphere-eversion/blob/33ab3d626854a0f0f04ed5772e3102d652e96475/SphereEversion/Global/Immersion.lean#L307-L340)).
2. The file has no `sorry`, `admit`, `Admitted` or `axiom` token, and the project CI
   builds it (`lake build SphereEversion`) on every push and PR to `master`
   (*check*, [.github/workflows/blueprint.yml lines 34-35](https://github.com/leanprover-community/sphere-eversion/blob/33ab3d626854a0f0f04ed5772e3102d652e96475/.github/workflows/blueprint.yml#L34-L35)).
3. The theorem is the published blueprint node `thm:sphere_eversion` (`Smale 1958`,
   `\lean{sphere_eversion}\leanok`), whose proof `\uses{thm:open_ample,
   lem:open_ample_immersion}` — exactly the open+ample h-principle this glue
   instantiates (*author-statement*, [global_convex_integration.tex lines
   737-746](https://github.com/leanprover-community/sphere-eversion/blob/33ab3d626854a0f0f04ed5772e3102d652e96475/blueprint/src/global_convex_integration.tex#L737-L746)).
4. The glue is 34 lines while the four children span 6, 14, 1 and 1 lines, and two of
   the four close by `simp` alone (*measurement*, `shape` in `entry.json`).

In my opinion the detail worth copying is the single `rcases … .bs … with ⟨f, …⟩`
step: it collapses "apply the h-principle, then name the produced family and its
guarantees" into one move, so the rest of the proof is just filling conjuncts from
projections.

## When to use it, and when not

Use it when an existential goal `∃ f, P f` is to be discharged by a single named
construction (a h-principle, a structure-inhabiting lemma, a universal property) whose
conclusion is a bundle of exactly the properties `P` needs. Then `rcases`/`obtain` the
witness, `refine ⟨f, …⟩` with one hole per conjunct, and close each conjunct against a
projection or a named lemma about the candidate. Avoid it when the witness must satisfy
a property the source lemma does not expose (the bundle would have to be reopened), when
the conjuncts interact (so they cannot be filled independently), or when the witness is
assembled from several independent choices rather than produced by one lemma.

## Consequences

The ∃-goal becomes a `refine ⟨f, …⟩` with one obligation per conjunct, so a missing
conjunct is a missing leaf rather than a partial proof. The witness's usable properties
are only what the source lemma's bundle exposes (`h₁` smoothness, `h₂` agreement near
`C`, `h₅` injectivity); here the immersion conjunct is reconstructed from `h₁.uncurry_left`
and `h₅` rather than taken as a single field. One field of the bundle is dropped with `-`, so if
a later conjunct had needed it the `rcases` would have to be restructured. Definitional
gaps between the witness and the goal's endpoint statement are bridged with `convert!`
(lines 333, 336): the endpoint lemmas are stated for the reparametrized
`formalEversion`, so they must match the `f 0 = …` goal up to definitional equality.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/blueprint.yml triggers push and pull_request on master and runs ~/.elan/bin/lake build SphereEversion (builds SphereEversion incl. Global/Immersion.lean); pinned commit 33ab3d626854a0f0f04ed5772e3102d652e96475 is HEAD of default branch master (compare status identical) | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| glue-cites-children | pass | cited: immersionRel_satisfiesHPrincipleWith@SphereEversion/Global/Immersion.lean:324, formalEversion_hol_near_zero_one@SphereEversion/Global/Immersion.lean:327, formalEversion_zero@SphereEversion/Global/Immersion.lean:333, formalEversion_one@SphereEversion/Global/Immersion.lean:336; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at 33ab3d626854a0f0f04ed5772e3102d652e96475 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | read copied code lines 307-340: line 324 rcases (immersionRel_satisfiesHPrincipleWith ...).bs (formalEversion E omega) (formalEversion_hol_near_zero_one E omega) with <f, h1, h2, -, h5>; line 327 passes formalEversion_hol_near_zero_one; line 333 convert! formalEversion_zero; line 336 convert! formalEversion_one; refine <f, h1, ...> uses h1 smoothness (line 338) and h5 injectivity (line 339); all four lemmas are same-file | verifier |
| 2 | verified | grep of the copied 350-line file found no sorry/admit/Admitted/axiom token; .github/workflows/blueprint.yml triggers push and pull_request on master and runs lake build SphereEversion (command on line 36, "Build project" name on line 35; claim cited lines 34-35) | verifier |
| 3 | verified | global_convex_integration.tex at pinned commit: line 737 \begin{theorem}[Smale 1958], line 738 \label{thm:sphere_eversion}, line 739 \lean{sphere_eversion}\leanok (claim said line 738), line 746 \uses{thm:open_ample, lem:open_ample_immersion}; matches the open+ample h-principle instantiated by immersionRel_satisfiesHPrincipleWith (uses immersionRel_ample + immersionRel_open) | verifier |
| 4 | verified | counted in copied file: glue 307-340 = 34 lines; children immersionRel_satisfiesHPrincipleWith 119-124 = 6, formalEversion_hol_near_zero_one 243-256 = 14, formalEversion_zero 209 = 1, formalEversion_one 211 = 1; lines 209 and 211 close by simp alone | verifier |
| 5 | verified | cites(parent, ContMDiff.uncurry_left) -> cites: ContMDiff.uncurry_left occurs at SphereEversion/Global/Immersion.lean:338 | check_claims.py |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Provenance passes (2 files byte-identical). Parent statement (307-310) and all four child statements match entry.json verbatim; closed_by matches the code (immersionRel_satisfiesHPrincipleWith 119-124 closes via immersionRel_ample/immersionRel_open at line 124; formalEversion_hol_near_zero_one 243-256 via filter_upwards then rcases into formalEversionHolAtZero/HolAtOne at 255-256; formalEversion_zero 209 and formalEversion_one 211 each 'by simp'). Glue (311-340) cites all four children at 324/327/333/336 and closes all three subgoal bullets with no sorry. Shape numbers all correct: glue_lines=34 (307-340), child_lines=[6,14,1,1] (119-124, 243-256, 209, 211), depth=2 (hol_near_zero_one -> holAtZero/holAtOne). The prior objection is fixed: shape.direct_lemmas is now 5, matching the five same-file named theorems the glue invokes (the four children plus ContMDiff.uncurry_left at line 338), and claim 5 correctly says the immersion conjunct's contMDiff field is closed by h1.uncurry_left, not h1 alone; the goal's own smoothness conjunct (CMDiff inf uf) is still correctly described as closed by h1 directly at line 330. children=4 vs direct_lemmas=5 is consistent (four children + one helper). | reviewer-correctness |
| generality | accept | Move stated beyond the example: applicability.goal_shape and use_when abstract to 'an existential goal whose body is a conjunction, witness produced by one named construction', and generalise the source to 'a h-principle, a structure-inhabiting lemma, a universal property' whose bundle of projections matches the conjuncts. avoid_when is specific and honest (property not exposed by the bundle; conjuncts interact so cannot be filled independently; witness assembled from several choices rather than one lemma). Consequences are tied to the actual proof, not generic: the dropped '-' field, the immersion conjunct rebuilt from h1/h5 rather than a single field, and the convert! definitional gap (lines 333/336) are all real. Good-leaf criterion is stated ('self-contained statement whose proof closes on its own or from named siblings') and made concrete per leaf, confirmed against the copied code: formalEversion_zero/one close by simp alone, immersionRel_satisfiesHPrincipleWith closes in one line from same-file immersionRel_ample/immersionRel_open without unfolding, formalEversion_hol_near_zero_one is a 14-line case split on sibling lemmas; shape.child_lines=[6,14,1,1] and children_closed_by_automation=2 give the budget-relevant numbers. | reviewer-generality |
| provenance-licence | accept | check_provenance passes (2 files byte-identical at 33ab3d626854a0f0f04ed5772e3102d652e96475). Commit, URL, licence are consistent across entry.json, sources/sphere-eversion/source.json and SOURCE.md; upstream-LICENSE is Apache-2.0 text matching the recorded 'Apache-2.0'. Both copied files' sha256 in entry.json match the local copies. All file/site permalinks use the same commit, correct paths, and line ranges verified against the local copies (parent 307-340, children 119-124/209/211/243-256). Evidence permalinks resolve: blueprint.yml:34-35 has 'lake build SphereEversion'; global_convex_integration.tex:737-746 has thm:sphere_eversion + leanok + uses. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover-community/sphere-eversion at commit `33ab3d626854a0f0f04ed5772e3102d652e96475`, under `Apache-2.0`; see the [source note](../../sources/sphere-eversion/SOURCE.md) for the licence text and attribution.
