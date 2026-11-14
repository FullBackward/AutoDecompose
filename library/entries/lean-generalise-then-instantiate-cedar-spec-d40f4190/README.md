# Cedar policy slicing: instantiate the general sound-slice theorem at the scope-based bound analysis

| | |
|---|---|
| Kind | instance |
| Move | generalise-then-instantiate |
| Language | lean |
| Status | accepted |
| Source | [cedar-spec](../../sources/cedar-spec/SOURCE.md) at `e619491a5bfb` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T12:10:15Z |

## Intent

The theorem that scope-based slicing preserves `isAuthorized` is reduced to
three chained instantiations of a general sound-slice framework. The glue
`apply`s the general sound-slice theorem `isAuthorized_eq_for_sound_policy_slice`,
then the bridge `sound_bound_analysis_produces_sound_slices` that turns a sound
bound analysis into a sound slice, and closes with the leaf
`scope_analysis_is_sound`.

## The decomposition

### parent `isAuthorized_eq_for_scope_based_policy_slice`: [`cedar-lean/Cedar/Thm/PolicySlice.lean` lines 131-137](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/PolicySlice.lean#L131-L137) ([local copy](code/cedar-lean/Cedar/Thm/PolicySlice.lean))

```lean
theorem isAuthorized_eq_for_scope_based_policy_slice (request : Request) (entities : Entities) (policies : Policies) :
  isAuthorized request entities (BoundAnalysis.slice scopeAnalysis request entities policies) =
  isAuthorized request entities policies
:= by
  apply isAuthorized_eq_for_sound_policy_slice
  apply sound_bound_analysis_produces_sound_slices
  exact scope_analysis_is_sound
```

### child `isAuthorized_eq_for_sound_policy_slice`: [`cedar-lean/Cedar/Thm/PolicySlice.lean` lines 48-56](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/PolicySlice.lean#L48-L56) ([local copy](code/cedar-lean/Cedar/Thm/PolicySlice.lean))

```lean
theorem isAuthorized_eq_for_sound_policy_slice (req : Request) (entities : Entities) (slice policies : Policies) :
  IsSoundPolicySlice req entities slice policies →
  isAuthorized req entities slice = isAuthorized req entities policies
:= by
  intro h₀
  have hf := satisfiedPolicies_eq_for_sound_policy_slice .forbid h₀
  have hp := satisfiedPolicies_eq_for_sound_policy_slice .permit h₀
  have he := errorPolicies_eq_for_sound_policy_slice h₀
  exact isAuthorized_eq_of_satisfied_and_error_policies_eq hf hp he
```

### child `sound_bound_analysis_produces_sound_slices`: [`cedar-lean/Cedar/Thm/PolicySlice.lean` lines 61-86](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/PolicySlice.lean#L61-L86) ([local copy](code/cedar-lean/Cedar/Thm/PolicySlice.lean))

```lean
theorem sound_bound_analysis_produces_sound_slices (ba : BoundAnalysis) (request : Request) (entities : Entities) (policies : Policies) :
  IsSoundBoundAnalysis ba →
  IsSoundPolicySlice request entities (ba.slice request entities policies) policies
:= by
  unfold IsSoundBoundAnalysis
  unfold IsSoundPolicySlice
  intro h₁
  unfold BoundAnalysis.slice
  apply And.intro
  case left =>
    intro p _
    simp_all only [List.mem_filter]
  case right =>
    intro policy
    specialize h₁ policy
    intro h₂ h₃
    rw [List.mem_filter] at h₃
    simp only [h₂, true_and, Bool.not_eq_true] at h₃
    by_contra h₄
    simp only [Bool.not_eq_true, not_and, Bool.not_eq_false] at h₄
    unfold IsSoundPolicyBound at h₁
    specialize h₁ request entities
    have ⟨h₅, h₆⟩ := h₁; clear h₁
    simp only [h₃, Bool.false_eq_true, imp_false, Bool.not_eq_true] at h₅ h₆
    specialize h₄ h₅
    simp only [h₄, Bool.true_eq_false] at h₆
```

### child `scope_analysis_is_sound`: [`cedar-lean/Cedar/Thm/PolicySlice.lean` lines 121-124](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/PolicySlice.lean#L121-L124) ([local copy](code/cedar-lean/Cedar/Thm/PolicySlice.lean))

```lean
theorem scope_analysis_is_sound :
  IsSoundBoundAnalysis scopeAnalysis
:= by
  simp [IsSoundBoundAnalysis, scope_bound_is_sound]
```

### context `scope_bound_is_sound`: [`cedar-lean/Cedar/Thm/PolicySlice.lean` lines 91-116](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/PolicySlice.lean#L91-L116) ([local copy](code/cedar-lean/Cedar/Thm/PolicySlice.lean))

```lean
theorem scope_bound_is_sound (policy : Policy) :
  IsSoundPolicyBound (scopeAnalysis policy) policy
:= by
  unfold IsSoundPolicyBound
  intro request entities
  unfold scopeAnalysis
  unfold satisfiedBound
  unfold inSomeOrNone
  simp only [decide_eq_true_eq]
  apply And.intro <;>
  intro h₁ <;>
  apply And.intro
  case left.left =>
    cases h₂ : policy.principalScope.scope.bound <;> simp
    exact satisfied_implies_principal_scope h₁ h₂
  case left.right =>
    cases h₂ : policy.resourceScope.scope.bound <;> simp
    exact satisfied_implies_resource_scope h₁ h₂
  case right.left =>
    replace ⟨err, h₁⟩ := if_hasError_then_exists_error h₁
    cases h₂ : policy.principalScope.scope.bound <;> simp
    exact error_implies_principal_scope_in h₁ h₂
  case right.right =>
    replace ⟨err, h₁⟩ := if_hasError_then_exists_error h₁
    cases h₂ : policy.resourceScope.scope.bound <;> simp
    exact error_implies_resource_scope_in h₁ h₂
```

**The move.** The parent theorem is a pure instantiation of the general
sound-slice machinery: its proof is three backward steps, each turning one
lemma's premise into the next goal.

```text
isAuthorized_eq_for_scope_based_policy_slice            (parent, 131-137)
  ├─ apply isAuthorized_eq_for_sound_policy_slice       (child, 48-56)
  │    leaves: IsSoundPolicySlice request entities (BoundAnalysis.slice scopeAnalysis …) policies
  ├─ apply sound_bound_analysis_produces_sound_slices   (child, 61-86)
  │    leaves: IsSoundBoundAnalysis scopeAnalysis
  └─ exact scope_analysis_is_sound                      (child, 121-124)
       closed; scope_analysis_is_sound uses scope_bound_is_sound (context, 91-116)
```

**The lemma graph, in text.** The glue cites the three direct lemmas in order.
The only edge below the glue is `scope_analysis_is_sound → scope_bound_is_sound`,
and `scope_bound_is_sound` itself closes on four scope lemmas imported from the
authorization theory (`satisfied_implies_principal_scope`,
`satisfied_implies_resource_scope`, `error_implies_principal_scope_in`,
`error_implies_resource_scope_in`); I did not fetch that theory, so the chain may
go deeper than the depth-2 link I checked.

**Why each lemma is a good leaf.** `isAuthorized_eq_for_sound_policy_slice`
is self-contained — "any sound slice preserves `isAuthorized`" — and its proof
closes on its own by splitting the two outcomes `.forbid`/`.permit` and
recombining with the imported `isAuthorized_eq_of_satisfied_and_error_policies_eq`;
it never mentions the scope analysis, so it is reusable for any slicing.
`sound_bound_analysis_produces_sound_slices` is self-contained — "any sound
bound analysis yields a sound slice" — proved by unfolding
`IsSoundBoundAnalysis`, `IsSoundPolicySlice`, `BoundAnalysis.slice` and
`IsSoundPolicyBound`, the two conjuncts closed by `simp_all` and by
`by_contra`+`simp`, citing no named lemma. `scope_analysis_is_sound` closes from
the named sibling `scope_bound_is_sound` by a single `simp`.

## Why it is good

1. The parent proof cites the general sound-slice theorem:
   `isAuthorized_eq_for_sound_policy_slice` occurs in the parent site at line 135
   (`check`, `cites(parent, isAuthorized_eq_for_sound_policy_slice)`).
2. The file closes every goal without a hole: no `sorry`, `admit` or `axiom`
   token occurs anywhere in `cedar-lean/Cedar/Thm/PolicySlice.lean` (`check`,
   `no_sorry(cedar-lean/Cedar/Thm/PolicySlice.lean, 1-139)`).
3. `scope_analysis_is_sound` is a real declaration in the file, at lines 121-124
   (`check`, `declared(scope_analysis_is_sound, cedar-lean/Cedar/Thm/PolicySlice.lean, 121-124)`).
4. The decomposition is three direct lemmas joined by a four-line glue, and the
   deepest project-lemma chain below the main theorem I traced is
   `scope_analysis_is_sound → scope_bound_is_sound`, i.e. depth 2 (`measurement`;
   glue at lines 134-137, use of `scope_bound_is_sound` at line 124, its
   declaration at lines 91-116).
5. The authors state the design in the module comment: the scope-based theorem is
   "based on a more general lemma (`sound_bound_analysis_produces_sound_slices`)
   that covers all forms of slicing that are based on identifying "bound"
   principal and resource entities", and "the general lemma also covers more
   sophisticated analyses that can extract bounds from policy conditions as well"
   (`author-statement`, lines 29-37).

## When to use it, and when not

Use generalise-then-instantiate when the general statement is already proved
over an abstract predicate (`IsSoundPolicySlice`, `IsSoundBoundAnalysis`), and
the concrete case needs only (a) a bridge lemma mapping the concrete
construction onto that predicate and (b) a leaf proving the concrete analysis
meets the predicate's own hypotheses, so the parent proof is pure
`apply`/`exact` with no new mathematics. Avoid it when the concrete construction
does not literally satisfy the abstract predicate's shape (the bridge then does
real work rather than unfold), when the leaf "the concrete analysis is sound" is
itself substantial rather than a one-line `simp`, or when the general statement
is not yet proved — then proving it is the real content and the instantiation is
the easy part.

## Consequences

Creates three obligations, one per child, and the glue is a pure chain of
`apply`/`exact` with no new goal manipulation. (1) The general sound-slice
theorem `isAuthorized_eq_for_sound_policy_slice`, the expensive part, which
itself imports three per-outcome lemmas. (2) The bridge
`sound_bound_analysis_produces_sound_slices`, which reduces `IsSoundPolicySlice`
for `ba.slice …` to `IsSoundBoundAnalysis ba` and is discharged entirely by
unfolding definitions. (3) The leaf `scope_analysis_is_sound`, a one-line `simp`
over `scope_bound_is_sound`. Failure modes: if the concrete slice is not
literally `BoundAnalysis.slice analysis …` for some `analysis` satisfying
`IsSoundBoundAnalysis`, the bridge does not apply and the general sound-slice
argument must be redone; if the leaf's soundness is not `simp`-trivial (its
per-policy soundness rests on the scope lemmas elsewhere, which are the real
content), the instantiation is not free.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/ci.yml job build_and_test_lean runs 'lake build Cedar SymCC' in ./cedar-lean; Cedar.lean imports Cedar.Thm which imports Cedar.Thm.PolicySlice; commit e619491a5bfb04970ef994dbe286df0bb9d0b73f is HEAD of default branch main | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: isAuthorized_eq_for_sound_policy_slice@cedar-lean/Cedar/Thm/PolicySlice.lean:135, sound_bound_analysis_produces_sound_slices@cedar-lean/Cedar/Thm/PolicySlice.lean:136, scope_analysis_is_sound@cedar-lean/Cedar/Thm/PolicySlice.lean:137; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at e619491a5bfb04970ef994dbe286df0bb9d0b73f | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, isAuthorized_eq_for_sound_policy_slice) -> cites: isAuthorized_eq_for_sound_policy_slice occurs at cedar-lean/Cedar/Thm/PolicySlice.lean:135 | check_claims.py |
| 2 | verified | no_sorry(cedar-lean/Cedar/Thm/PolicySlice.lean, 1-139) -> no_sorry: none of sorry, admit, axiom in cedar-lean/Cedar/Thm/PolicySlice.lean:1-139 | check_claims.py |
| 3 | verified | declared(scope_analysis_is_sound, cedar-lean/Cedar/Thm/PolicySlice.lean, 121-124) -> declared: scope_analysis_is_sound is declared at cedar-lean/Cedar/Thm/PolicySlice.lean:121 | check_claims.py |
| 4 | verified | read code/cedar-lean/Cedar/Thm/PolicySlice.lean lines 91-137: parent proof at 131-137 has a 4-line glue ('by' at 134, 'apply isAuthorized_eq_for_sound_policy_slice' 135, 'apply sound_bound_analysis_produces_sound_slices' 136, 'exact scope_analysis_is_sound' 137); scope_analysis_is_sound at 121-124 uses scope_bound_is_sound at line 124; scope_bound_is_sound declared at lines 91-116 | verifier |
| 5 | verified | read code/cedar-lean/Cedar/Thm/PolicySlice.lean lines 29-37: module comment says proof 'is based on a more general lemma (sound_bound_analysis_produces_sound_slices) that covers all forms of slicing that are based on identifying "bound" principal and resource entities' and 'the general lemma also covers more sophisticated analyses that can extract bounds from policy conditions as well' | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent site (131-137) proof is exactly three backward steps citing the three children in order: apply isAuthorized_eq_for_sound_policy_slice (135), apply sound_bound_analysis_produces_sound_slices (136), exact scope_analysis_is_sound (137); this closes (apply the general sound-slice theorem leaves IsSoundPolicySlice for BoundAnalysis.slice scopeAnalysis, apply the bridge leaves IsSoundBoundAnalysis scopeAnalysis, exact the leaf closes it). Children and closing methods match the copied code verbatim: isAuthorized_eq_for_sound_policy_slice (48-56) closes via satisfiedPolicies_eq_for_sound_policy_slice .forbid/.permit, errorPolicies_eq_for_sound_policy_slice, isAuthorized_eq_of_satisfied_and_error_policies_eq; sound_bound_analysis_produces_sound_slices (61-86) closes by unfolding IsSoundBoundAnalysis/IsSoundPolicySlice/BoundAnalysis.slice/IsSoundPolicyBound then simp_all + by_contra/simp; scope_analysis_is_sound (121-124) closes by simp [IsSoundBoundAnalysis, scope_bound_is_sound], and scope_bound_is_sound (91-116) closes on the four named scope lemmas. Shape numbers are right: direct_lemmas=3 (the three cited children), child_lines=[9,26,4] matching sites 48-56/61-86/121-124, glue_lines=7 matching the 131-137 parent site, depth=2 (scope_analysis_is_sound -> scope_bound_is_sound, deeper chain acknowledged). No sorry/admit/axiom in the file. | reviewer-correctness |
| generality | accept | Move is stated beyond the example: 'when to use'/'goal_shape' are phrased over abstract predicates (IsSoundPolicySlice, IsSoundBoundAnalysis) with the concrete names only as illustration, matching the author's module comment (verified at lines 29-37: the general lemma 'covers all forms of slicing...' and 'also covers more sophisticated analyses...'). avoid_when gives three specific, honest failure conditions (bridge does real work rather than unfold; leaf soundness is substantial not one-line simp; general statement unproved). Consequences are honest and specific, including the failure mode that the leaf's simp-triviality hides the real content in scope_bound_is_sound and its imported scope lemmas. It does say what makes leaves good for a bounded prover: each child is self-contained, never mentions the concrete analysis (reusable), and closes by unfold/simp with no named lemma. | reviewer-generality |
| provenance-licence | accept | check_provenance passes: 1 file byte-identical at e619491a5bfb04970ef994dbe286df0bb9d0b73f. Commit hash is identical across source.json, SOURCE.md, entry.json (source.commit, files[].permalink, sites[].permalink) and the README permalinks (full hash; the table's 12-char abbreviation is display-only). Licence Apache-2.0 is consistent: file header, upstream-LICENSE (Apache License 2.0), upstream-NOTICE (Copyright Cedar Contributors), source.json.licence, SOURCE.md and README all agree. Copied file matches entry.json exactly: 5179 bytes, sha256 9f0cf12d...; single code/ file matches the files[] list. All cited line ranges (131-137, 48-56, 61-86, 121-124, 91-116, and claim 5's 29-37) match the local copy and the quoted excerpts verbatim. SOURCE.md records the pinned commit, licence, attribution and licence files. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/cedar-policy/cedar-spec at commit `e619491a5bfb04970ef994dbe286df0bb9d0b73f`, under `Apache-2.0`; see the [source note](../../sources/cedar-spec/SOURCE.md) for the licence text and attribution.
