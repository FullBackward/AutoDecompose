# Per-component order and duplicate independence for Cedar's isAuthorized

| | |
|---|---|
| Kind | instance |
| Move | per-callee-lemma |
| Language | lean |
| Status | accepted |
| Source | [cedar-spec](../../sources/cedar-spec/SOURCE.md) at `e619491a5bfb` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T12:51:03Z |

## Intent

One lemma per component of `isAuthorized`. The head theorem
`order_and_dup_independent` says Cedar's authorizer returns the same response
for order/dup-equivalent policy lists; the proof obtains that fact separately
for each of the three components `isAuthorized` is built from
(forbid-satisfied, permit-satisfied, erroring), then reassembles the response
in one `simp`.

## The decomposition

### parent `order_and_dup_independent`: [`cedar-lean/Cedar/Thm/Authorization.lean` lines 158-166](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/Authorization.lean#L158-L166) ([local copy](code/cedar-lean/Cedar/Thm/Authorization.lean))

```lean
theorem order_and_dup_independent (request : Request) (entities : Entities) (policies₁ policies₂ : Policies) :
  policies₁ ≡ policies₂ →
  isAuthorized request entities policies₁ = isAuthorized request entities policies₂
:= by
  intro h
  have hf := satisfiedPolicies_order_and_dup_independent .forbid request entities h
  have hp := satisfiedPolicies_order_and_dup_independent .permit request entities h
  have he := errorPolicies_order_and_dup_independent request entities h
  simp [isAuthorized, hf, hp, he]
```

### child `satisfiedPolicies_order_and_dup_independent`: [`cedar-lean/Cedar/Thm/Authorization/Authorizer.lean` lines 62-69](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/Authorization/Authorizer.lean#L62-L69) ([local copy](code/cedar-lean/Cedar/Thm/Authorization/Authorizer.lean))

```lean
theorem satisfiedPolicies_order_and_dup_independent {policies₁ policies₂ : Policies} (effect : Effect) (request : Request) (entities : Entities) :
  policies₁ ≡ policies₂ →
  satisfiedPolicies effect policies₁ request entities = satisfiedPolicies effect policies₂ request entities
:= by
  intro h₁
  unfold satisfiedPolicies
  rw [Set.make_make_eqv]
  exact List.filterMap_equiv (satisfiedWithEffect effect · request entities) policies₁ policies₂ h₁
```

### child `errorPolicies_order_and_dup_independent`: [`cedar-lean/Cedar/Thm/Authorization/Authorizer.lean` lines 71-78](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/Authorization/Authorizer.lean#L71-L78) ([local copy](code/cedar-lean/Cedar/Thm/Authorization/Authorizer.lean))

```lean
theorem errorPolicies_order_and_dup_independent {policies₁ policies₂ : Policies} (request : Request) (entities : Entities) :
  policies₁ ≡ policies₂ →
  errorPolicies policies₁ request entities = errorPolicies policies₂ request entities
:= by
  intro h₁
  unfold errorPolicies
  rw [Set.make_make_eqv]
  exact List.filterMap_equiv (errored · request entities) policies₁ policies₂ h₁
```

### context `isAuthorized`: [`cedar-lean/Cedar/Spec/Authorizer.lean` lines 56-62](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Spec/Authorizer.lean#L56-L62) ([local copy](code/cedar-lean/Cedar/Spec/Authorizer.lean))

```lean
public def isAuthorized (req : Request) (entities : Entities) (policies : Policies) : Response :=
  let forbids := satisfiedPolicies .forbid policies req entities
  let permits := satisfiedPolicies .permit policies req entities
  let erroringPolicies := errorPolicies policies req entities
  if forbids.isEmpty && !permits.isEmpty
  then { decision := .allow, determiningPolicies := permits, erroringPolicies }
  else { decision := .deny,  determiningPolicies := forbids, erroringPolicies }
```

How the parts fit. `isAuthorized` (the context excerpt above) is literally a
`let`-bound combination of three components — `satisfiedPolicies .forbid`,
`satisfiedPolicies .permit` and `errorPolicies` — so the parent's proof is
three `have`s that obtain each component's order/dup independence, then one
`simp [isAuthorized, hf, hp, he]` that reassembles the response:

```
order_and_dup_independent
├── satisfiedPolicies_order_and_dup_independent   (hf for .forbid, and again hp for .permit)
└── errorPolicies_order_and_dup_independent        (he)
```

Each child is a good leaf because its statement is self-contained —
`policies₁ ≡ policies₂ → component policies₁ … = component policies₂ …` — and
its proof closes on its own in three steps, needing no sibling: `unfold` the
component to its `Set.make (policies.filterMap g)` definition, `rw
[Set.make_make_eqv]` to turn the `Set.make` equality into a `List.Equiv` of
the two `filterMap` inputs, then `exact List.filterMap_equiv …` (a Batteries
lemma) to discharge that equivalence from the hypothesis `h₁`. The two
children are the same template with a different predicate (`satisfiedWithEffect
effect` versus `errored`); `satisfiedPolicies_order_and_dup_independent` is
used twice because `.forbid` and `.permit` are the same component at two
different effect values.

## Why it is good

1. The theorem `order_and_dup_independent` is declared in
   `cedar-lean/Cedar/Thm/Authorization.lean` lines 158-166 (`check`,
   [permalink](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/Authorization.lean#L158-L166)).
2. `satisfiedPolicies_order_and_dup_independent` occurs in the parent site
   (`check`,
   [permalink](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/Authorization.lean#L158-L166)).
3. `errorPolicies_order_and_dup_independent` occurs in the parent site
   (`check`,
   [permalink](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/Authorization.lean#L158-L166)).
4. `cedar-lean/Cedar/Thm/Authorization/Authorizer.lean` lines 62-78 contain no
   `sorry`, `admit` or `axiom` (`check`,
   [permalink](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/Authorization/Authorizer.lean#L62-L78)).
5. The glue assembles 2 direct lemmas in a 9-line proof — `satisfiedPolicies_order_and_dup_independent`
   applied twice (for `.forbid` and `.permit`) and `errorPolicies_order_and_dup_independent` once — while
   each child proof is 8 lines and the project-lemma chain below the theorem runs 3 deep (child →
   `Set.make_make_eqv` → `List.canonicalize_equiv`), counted from the site line ranges and by reading the
   two child proofs (`measurement`, see the shape field).
6. The same component-wise move appears a second time in the same file:
   `satisfied_policies_congr_evaluate` (lines 80-89) and `error_policies_congr_evaluate` (lines 91-102)
   prove the same two components congr under evaluation, combined by `is_authorized_congr_evaluate`
   (lines 117-126) with the same `simp only [isAuthorized, …]` glue (`known-use`,
   [permalink](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/Authorization/Authorizer.lean#L80-L126)).

In my opinion the detail worth copying is that the per-component lemmas are a
*template*: the two children differ only in the predicate fed to `filterMap`,
so a proof engine can generate one lemma per component of a structured
definition and the glue is a fixed `simp [f, h₁ … hₙ]`.

## When to use it, and when not

Use it when a composite function `f` is built from a fixed set of named
components (a generated or structured definition — here Cedar's `isAuthorized`),
and the goal is an equality `f x = f y` or a congruence of `f`. The move works
when each component's invariance reduces to a short, uniform rewrite (here
`Set.make_make_eqv` then `List.filterMap_equiv`), and the glue can close with a
single `simp [f, h₁ … hₙ]` that unfolds `f` and drops in the per-component
equalities.

Avoid it when the composite's body reads anything other than its components —
the raw `policies` list directly, or an argument the per-component lemmas do
not hold equal — because the per-component equalities only licence rewriting
the components, and a body that depends on something else cannot be closed by
the `simp`. (Branching on the components themselves is fine: `isAuthorized`
branches on `forbids.isEmpty && !permits.isEmpty`, yet the `simp` still
closes, because any property of a component is preserved by component
equality.) Avoid it too when the components do not share one lemma shape,
since the whole point is one template per component.

## Consequences

One lemma per component of `isAuthorized`, so the obligations are: (1) every
component must be covered — the glue applies `satisfiedPolicies_order_and_dup_independent`
twice, once per effect, and `errorPolicies_order_and_dup_independent` once, and
missing one component leaves the final `simp` unable to close; (2) each
component's definition must be of the shape `Set.make (policies.filterMap g)`,
or the `unfold` / `rw [Set.make_make_eqv]` / `exact List.filterMap_equiv`
template does not apply; (3) the glue's `simp [isAuthorized, hf, hp, he]` only
closes because `isAuthorized` is literally a combination of the three
components, so a change to `isAuthorized`'s body that branches on more than
set-equality breaks the glue. Failure mode: the two per-component lemmas are
near-identical templates, so a change to the shared `Set.make`/`filterMap`
infrastructure breaks the whole family at once.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/ci.yml job build_and_test_lean runs 'lake build Cedar SymCC' in ./cedar-lean, which builds Cedar/Thm/Authorization.lean and Cedar/Thm/Authorization/Authorizer.lean; commit e619491a5bfb04970ef994dbe286df0bb9d0b73f is on default branch main (compare main...e619491 is identical) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: satisfiedPolicies_order_and_dup_independent@cedar-lean/Cedar/Thm/Authorization.lean:163, errorPolicies_order_and_dup_independent@cedar-lean/Cedar/Thm/Authorization.lean:165; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 3 file(s) byte-identical at e619491a5bfb04970ef994dbe286df0bb9d0b73f | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(order_and_dup_independent, cedar-lean/Cedar/Thm/Authorization.lean, 158-166) -> declared: order_and_dup_independent is declared at cedar-lean/Cedar/Thm/Authorization.lean:158 | check_claims.py |
| 2 | verified | cites(parent, satisfiedPolicies_order_and_dup_independent) -> cites: satisfiedPolicies_order_and_dup_independent occurs at cedar-lean/Cedar/Thm/Authorization.lean:163 | check_claims.py |
| 3 | verified | cites(parent, errorPolicies_order_and_dup_independent) -> cites: errorPolicies_order_and_dup_independent occurs at cedar-lean/Cedar/Thm/Authorization.lean:165 | check_claims.py |
| 4 | verified | no_sorry(cedar-lean/Cedar/Thm/Authorization/Authorizer.lean, 62-78) -> no_sorry: none of sorry, admit, axiom in cedar-lean/Cedar/Thm/Authorization/Authorizer.lean:62-78 | check_claims.py |
| 5 | verified | parent cedar-lean/Cedar/Thm/Authorization.lean:158-166 is 9 lines (theorem through 'simp [isAuthorized, hf, hp, he]'); children Authorizer.lean:62-69 and 71-78 are 8 lines each; both child proofs are unfold/rw [Set.make_make_eqv]/exact List.filterMap_equiv; Set.make_make_eqv declared at Thm/Data/Set.lean:303-317 (318 blank) and its proof calls List.canonicalize_equiv (Set.lean:309-310); List.canonicalize_equiv declared at Thm/Data/List/Canonical.lean:468-480 | verifier |
| 6 | verified | cedar-lean/Cedar/Thm/Authorization/Authorizer.lean:80-89 declares satisfied_policies_congr_evaluate, :91-102 declares error_policies_congr_evaluate, :117-126 declares is_authorized_congr_evaluate whose proof is 'simp only [isAuthorized]' then 'rw [satisfied_policies_congr_evaluate .permit heq, satisfied_policies_congr_evaluate .forbid heq, error_policies_congr_evaluate heq]' | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Decomposition matches the code. Parent order_and_dup_independent (Authorization.lean 158-166) is 9 lines whose glue is exactly three have's -- satisfiedPolicies_order_and_dup_independent .forbid/.permit and errorPolicies_order_and_dup_independent -- then simp [isAuthorized, hf, hp, he]; the isAuthorized context (Spec/Authorizer.lean 56-62) is a let-bound combination of those three components, so the glue closes. Children and closed_by match verbatim (Authorizer.lean 62-69 and 71-78; exact List.filterMap_equiv ... at lines 69/78). Children are exactly the lemmas the proof cites (no others; satisfiedPolicies used twice, noted). Shape numbers right: glue_lines 9 (158-166), child_lines [8,8] (62-69, 71-78), direct_lemmas 2, depth 3 (child -> Set.make_make_eqv (Set.lean 303-318, calls List.canonicalize_equiv at 310-311) -> List.canonicalize_equiv (Canonical.lean 468-480)); List.filterMap_equiv is external (Batteries), not a project lemma. | reviewer-correctness |
| generality | accept | Move stated generally (one lemma per component of a structured definition; glue a fixed simp [f, h1..hn]; use_when names goal_shape f x = f y / congruence over let-bound+branching composites). The avoid_when is now correct: it says the body must depend only on the components and fails when it reads anything outside the per-component equalities (raw policies, or an argument not held equal), and explicitly notes branching on the components themselves (isAuthorized branches on forbids.isEmpty && !permits.isEmpty) is fine by congruence -- verified against Spec/Authorizer.lean:56-62. Consequences are specific and honest: cover every component, components must be Set.make (filterMap g), glue closes only because isAuthorized is literally the three components, and the near-identical-template failure mode is named. The good-leaf question is answered: self-contained statement, 3-step proof (unfold / rw Set.make_make_eqv / exact List.filterMap_equiv), no sibling needed, and it names the shared template with different predicates. Minor wording blemish only: consequence (3) says 'branches on more than set-equality' where it means 'reads something beyond the component equalities'; not misleading given the avoid_when parenthetical, so not a standing objection. | reviewer-generality |
| provenance-licence | accept | check_provenance.py passes: 3 copied files byte-identical at commit e619491a5bfb04970ef994dbe286df0bb9d0b73f. Commit is pinned and consistent across entry.json source.commit, README, source note, and source.json. Licence Apache-2.0 recorded identically in entry.json, README and SOURCE.md, and upstream-LICENSE is the Apache 2.0 text with upstream-NOTICE present. All permalinks use the same commit; the cited line ranges (Authorization.lean 158-166, Authorizer.lean 62-78 and 80-126, Spec/Authorizer.lean 56-62) match the local copies and README excerpts verbatim. Source note links the entry to the repo, commit, licence files and attribution. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/cedar-policy/cedar-spec at commit `e619491a5bfb04970ef994dbe286df0bb9d0b73f`, under `Apache-2.0`; see the [source note](../../sources/cedar-spec/SOURCE.md) for the licence text and attribution.
