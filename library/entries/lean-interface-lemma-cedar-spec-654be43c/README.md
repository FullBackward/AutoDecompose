# WellBehavedIsAuthorizedQuery bundles query well-behavedness for generic verifyIsAuthorized soundness

| | |
|---|---|
| Kind | instance |
| Move | interface-lemma |
| Language | lean |
| Status | accepted |
| Source | [cedar-spec](../../sources/cedar-spec/SOURCE.md) at `e619491a5bfb` |
| Licence | `Apache-2.0` |

## Intent

The decomposition states soundness of the symbolic `Cedar.SymCC.verifyIsAuthorized` once, for every query `φ` and response comparison `f` at once, by folding the three properties a query must satisfy into the single predicate `WellBehavedIsAuthorizedQuery` (lines 33-53). A client proves its own analysis sound simply by proving `WellBehavedIsAuthorizedQuery φ f` for its `φ` and `f`, instead of re-proving soundness from the analysis internals.

## The decomposition

### parent `verifyIsAuthorized_is_sound`: [`cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean` lines 99-132](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean#L99-L132) ([local copy](code/cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean))

```lean
theorem verifyIsAuthorized_is_sound {φ : Term → Term → Term} {f : Response → Response → Bool} {ps₁ ps₂ : Policies} {εnv : SymEnv} {asserts : Asserts} :
  WellBehavedIsAuthorizedQuery φ f →
  εnv.StronglyWellFormedForPolicies ps₁ →
  εnv.StronglyWellFormedForPolicies ps₂ →
  verifyIsAuthorized φ ps₁ ps₂ εnv = .ok asserts →
  εnv ⊭ asserts →
  ∀ env,
    env ∈ᵢ εnv →
    env.StronglyWellFormedForPolicies ps₁ →
    env.StronglyWellFormedForPolicies ps₂ →
    f (Spec.isAuthorized env.request env.entities ps₁) (Spec.isAuthorized env.request env.entities ps₂) = true
:= by
  intro ⟨hwφ, hiφ, hφf⟩ hwε₁ hwε₂ hok hsat env ⟨I, hwI, heq⟩ hwe₁ hwe₂
  rw [asserts_unsatisfiable_def] at hsat
  replace ⟨t, hsat⟩ := hsat I hwI
  replace ⟨t₁, t₂, ts, hok₁, hok₂, ha, hok⟩ := verifyIsAuthorized_ok_implies hok
  subst hok
  replace ha := swf_implies_enforce_satisfiedBy heq hwI
    (swf_εnv_for_policies_iff_swf_for_append.mp (And.intro hwε₁ hwε₂))
    (swf_env_for_policies_iff_swf_for_append.mp (And.intro hwe₁ hwe₂)) ha
  replace ha := asserts_last_not_true ha hsat.left hsat.right
  subst ha
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_true, ne_eq, true_and] at hsat
  replace hwε₁ := swf_εnv_for_policies_implies_wf_for_policies hwε₁
  replace hwe₁ := swf_env_for_policies_implies_wf_for_policies hwe₁
  have hrb₁ := isAuthorized_bisimulation hwε₁ hwe₁ hwI heq hok₁
  replace hwε₂ := swf_εnv_for_policies_implies_wf_for_policies hwε₂
  replace hwe₂ := swf_env_for_policies_implies_wf_for_policies hwe₂
  have hrb₂ := isAuthorized_bisimulation hwε₂ hwe₂ hwI heq hok₂
  have hwt₁ := isAuthorized_wf hwε₁ hok₁
  have hwt₂ := isAuthorized_wf hwε₂ hok₂
  rw [interpret_not_wbaq hwI (And.intro hwt₁ hwt₂) hwφ hiφ] at hsat
  have hrb := wbaq_bisimulation (And.intro hwt₁ hwt₂) hφf hwI hrb₁ hrb₂
  exact same_bool_not_not_true_implies_true hrb hsat
```

### child `verifyIsAuthorized_ok_implies`: [`cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean` lines 81-97](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean#L81-L97) ([local copy](code/cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean))

```lean
private theorem verifyIsAuthorized_ok_implies {φ : Term → Term → Term} {ps₁ ps₂ : Policies} {εnv : SymEnv} {asserts : Asserts} :
  verifyIsAuthorized φ ps₁ ps₂ εnv = .ok asserts →
  ∃ t₁ t₂ ts,
    isAuthorized ps₁ εnv = .ok t₁ ∧
    isAuthorized ps₂ εnv = .ok t₂ ∧
    enforce ((ps₁ ++ ps₂).map Policy.toExpr) εnv = Set.mk ts ∧
    asserts = ts ++ [not (φ t₁ t₂)]
:= by
  intro hok
  simp only [verifyIsAuthorized, List.map_append] at hok
  simp_do_let (isAuthorized ps₁ εnv) at hok
  simp_do_let (isAuthorized ps₂ εnv) at hok
  rename_i t₁ hok₁ t₂ hok₂
  simp only [Except.ok.injEq] at hok
  subst hok
  exists t₁, t₂, (enforce (List.map Policy.toExpr ps₁ ++ List.map Policy.toExpr ps₂) εnv).elts
  simp only [List.map_append, and_self]
```

### child `swf_implies_enforce_satisfiedBy`: [`cedar-lean/Cedar/Thm/SymCC/Enforcer.lean` lines 30-37](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/SymCC/Enforcer.lean#L30-L37) ([local copy](code/cedar-lean/Cedar/Thm/SymCC/Enforcer.lean))

```lean
theorem swf_implies_enforce_satisfiedBy {ps : Policies} {env : Env} {εnv : SymEnv} {I : Interpretation} {assumes : Asserts} :
  env ∼ εnv.interpret I →
  I.WellFormed εnv.entities →
  εnv.StronglyWellFormedForPolicies ps →
  env.StronglyWellFormedForPolicies ps →
  enforce (ps.map Policy.toExpr) εnv = Set.mk assumes →
  assumes.satisfiedBy I
:= enforce_satisfiedBy_swf
```

### child `asserts_last_not_true`: [`cedar-lean/Cedar/Thm/SymCC/Enforcer/Asserts.lean` lines 47-58](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/SymCC/Enforcer/Asserts.lean#L47-L58) ([local copy](code/cedar-lean/Cedar/Thm/SymCC/Enforcer/Asserts.lean))

```lean
theorem asserts_last_not_true {I : Interpretation} {ts : Asserts} {t t' : Term} :
  ts.satisfiedBy I →
  t ∈ ts ++ [t'] →
  t.interpret I ≠ Term.prim (TermPrim.bool true) →
  t = t'
:= by
  intro h₁ h₂ h₃
  rw [asserts_satisfiedBy_true] at h₁
  simp only [List.mem_append, List.mem_singleton] at h₂
  rcases h₂ with h₂ | h₂ <;> try exact h₂
  specialize h₁ t h₂
  contradiction
```

### child `isAuthorized_bisimulation`: [`cedar-lean/Cedar/Thm/SymCC/Authorizer.lean` lines 450-461](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/SymCC/Authorizer.lean#L450-L461) ([local copy](code/cedar-lean/Cedar/Thm/SymCC/Authorizer.lean))

```lean
theorem isAuthorized_bisimulation {ps : Policies} {env : Env} {εnv : SymEnv} {t : Term} {I : Interpretation} :
  εnv.WellFormedForPolicies ps →
  env.WellFormedForPolicies ps →
  I.WellFormed εnv.entities →
  env ∼ εnv.interpret I →
  Cedar.SymCC.isAuthorized ps εnv = .ok t →
  Cedar.Spec.isAuthorized env.request env.entities ps ∼ t.interpret I
:= by
  intro hwε hwe hwI heq hok
  replace hok := isAuthorized_interpret hwε hwI hok
  replace hwε := interpret_εnv_wf_for_policies hwε hwI
  exact isAuthorized_same hwε hwe heq hok
```

### child `isAuthorized_wf`: [`cedar-lean/Cedar/Thm/SymCC/Authorizer.lean` lines 375-386](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/SymCC/Authorizer.lean#L375-L386) ([local copy](code/cedar-lean/Cedar/Thm/SymCC/Authorizer.lean))

```lean
theorem isAuthorized_wf {ps : Policies} {εnv : SymEnv} {t : Term} :
  εnv.WellFormedForPolicies ps →
  Cedar.SymCC.isAuthorized ps εnv = .ok t →
  t.WellFormed εnv.entities ∧ t.typeOf = .bool
:= by
  intro hwε hok
  replace ⟨tp, tf, hokp, hokf, hok⟩ := isAuthorized_ok_implies hok
  subst hok
  replace hokp := satisfiedPolicies_wf hwε hokp
  replace hokf := satisfiedPolicies_wf hwε hokf
  replace hokf := wf_not hokf.left hokf.right
  exact wf_and hokp.left hokf.left hokp.right hokf.right
```

### child `wbaq_bisimulation`: [`cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean` lines 55-67](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean#L55-L67) ([local copy](code/cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean))

```lean
private theorem wbaq_bisimulation {φ : Term → Term → Term} {f : Response → Response → Bool} {εs : SymEntities} {t₁ t₂ : Term} {r₁ r₂ : Response} {I : Interpretation} :
  WellBehavedIsAuthorizedQuery.WellFormedInputs t₁ t₂ εs →
  WellBehavedIsAuthorizedQuery.Same φ f →
  I.WellFormed εs →
  r₁ ∼ (t₁.interpret I) → r₂ ∼ (t₂.interpret I) →
  (f r₁ r₂) ∼ (φ (t₁.interpret I) (t₂.interpret I))
:= by
  intro ⟨hwt₁, hwt₂⟩ hφf hwI heq₁ heq₂
  have hwt₁' := interpret_term_wf hwI hwt₁.left
  rw [hwt₁.right] at hwt₁'
  have hwt₂' := interpret_term_wf hwI hwt₂.left
  rw [hwt₂.right] at hwt₂'
  exact hφf _ _ _ _ _ (And.intro hwt₁' hwt₂') heq₁ heq₂
```

### child `interpret_not_wbaq`: [`cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean` lines 69-79](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean#L69-L79) ([local copy](code/cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean))

```lean
private theorem interpret_not_wbaq {φ : Term → Term → Term} {t₁ t₂ : Term} {I : Interpretation} {εs : SymEntities} :
  I.WellFormed εs →
  WellBehavedIsAuthorizedQuery.WellFormedInputs t₁ t₂ εs →
  WellBehavedIsAuthorizedQuery.WellFormedOutput φ →
  WellBehavedIsAuthorizedQuery.Interpretable φ →
  Term.interpret I (not (φ t₁ t₂)) = not (φ (t₁.interpret I) (t₂.interpret I))
:= by
  intro hwI hwt hwφ hiφ
  rw [interpret_not hwI]
  · rw [hiφ t₁ t₂ εs I hwt hwI]
  · exact (hwφ t₁ t₂ εs hwt).left
```

### child `same_bool_not_not_true_implies_true`: [`cedar-lean/Cedar/Thm/SymCC/Verifier/Same.lean` lines 48-58](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/SymCC/Verifier/Same.lean#L48-L58) ([local copy](code/cedar-lean/Cedar/Thm/SymCC/Verifier/Same.lean))

```lean
theorem same_bool_not_not_true_implies_true {b : Bool} {t : Term} :
  b ∼ t →
  ¬ not t = .bool true →
  b = true
:= by
  intro h₁ h₂
  rw [same_bool_def] at h₁
  rw [h₁] at h₂
  cases b
  case false => simp only [pe_not_false, not_true_eq_false] at h₂
  case true  => rfl
```

### context `WellBehavedIsAuthorizedQuery`: [`cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean` lines 33-53](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean#L33-L53) ([local copy](code/cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean))

```lean
def WellBehavedIsAuthorizedQuery (φ : Term → Term → Term) (f : Response → Response → Bool) : Prop :=
  WellFormedOutput ∧ Interpretable ∧ Same
where
  WellFormedInput (t : Term) (εs : SymEntities) :=
    t.WellFormed εs ∧ t.typeOf = .bool
  WellFormedInputs (t₁ t₂ : Term) (εs : SymEntities) :=
    WellFormedInput t₁ εs ∧ WellFormedInput t₂ εs
  WellFormedOutput :=
    ∀ (t₁ t₂ : Term) (εs : SymEntities),
      WellFormedInputs t₁ t₂ εs →
      (φ t₁ t₂).WellFormed εs ∧ (φ t₁ t₂).typeOf = .bool
  Interpretable :=
    ∀ (t₁ t₂ : Term) (εs : SymEntities) (I : Interpretation),
      WellFormedInputs t₁ t₂ εs →
      I.WellFormed εs →
      (φ t₁ t₂).interpret I = φ (t₁.interpret I) (t₂.interpret I)
  Same :=
    ∀ (t₁ t₂ : Term) (εs : SymEntities) (r₁ r₂ : Response),
      WellFormedInputs t₁ t₂ εs →
      r₁ ∼ t₁ → r₂ ∼ t₂ →
      (f r₁ r₂) ∼ (φ t₁ t₂)
```

How the parts fit. The glue — the parent's proof (lines 110-132) — is a linear assembly of the eight named lemmas above. It opens by destructuring the bundle `⟨hwφ, hiφ, hφf⟩` into its three components `WellFormedOutput`, `Interpretable`, `Same`, then discharges one obligation per step:

1. `verifyIsAuthorized_ok_implies` unfolds the `.ok` result of `verifyIsAuthorized` into the two symbolic authorizations `t₁ t₂` and the enforced asserts `ts`, with `asserts = ts ++ [not (φ t₁ t₂)]`.
2. `swf_implies_enforce_satisfiedBy` turns the `enforce` result into `assumes.satisfiedBy I` (the two policy lists are first combined via `swf_εnv_for_policies_iff_swf_for_append` and `swf_env_for_policies_iff_swf_for_append`).
3. `asserts_last_not_true` locates the single unsatisfied assert: it must be the last element, `not (φ t₁ t₂)`.
4. `swf_εnv_for_policies_implies_wf_for_policies` / `swf_env_for_policies_implies_wf_for_policies` weaken strong to plain well-formedness.
5. `isAuthorized_bisimulation` (applied twice) connects the concrete `Spec.isAuthorized` decisions to the symbolic `t₁.interpret I` and `t₂.interpret I`.
6. `isAuthorized_wf` (applied twice) establishes that `t₁ t₂` are well-formed boolean terms — the hypothesis `wbaq_bisimulation` and `interpret_not_wbaq` need.
7. `interpret_not_wbaq` pushes `not` through the interpretation of the query, so the negated query is `not (φ (t₁.interpret I) (t₂.interpret I))`.
8. `wbaq_bisimulation` lifts the `Same` component to the interpreted terms: `f r₁ r₂ ∼ φ (t₁.interpret I) (t₂.interpret I)`.
9. `same_bool_not_not_true_implies_true` closes the goal: `f r₁ r₂` bisimulates a term whose negation is not true, so `f r₁ r₂ = true`.

The glue also cites five further named lemmas that only shuffle the policy-list form and are not shown as children (each has a permalink): `asserts_unsatisfiable_def` ([Asserts.lean L40-L45](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/SymCC/Enforcer/Asserts.lean#L40-L45), copied as `code/cedar-lean/Cedar/Thm/SymCC/Enforcer/Asserts.lean`), `swf_εnv_for_policies_iff_swf_for_append` ([SWF.lean L110-L129](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/SymCC/Env/SWF.lean#L110-L129)), `swf_env_for_policies_iff_swf_for_append` ([SWF.lean L131-L150](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/SymCC/Env/SWF.lean#L131-L150)), `swf_εnv_for_policies_implies_wf_for_policies` ([SWF.lean L152-L161](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/SymCC/Env/SWF.lean#L152-L161)), `swf_env_for_policies_implies_wf_for_policies` ([SWF.lean L163-L172](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/SymCC/Env/SWF.lean#L163-L172)). Together with the eight children that makes 13 direct lemmas.

Lemma graph (which lemma uses which, in text):

- `verifyIsAuthorized_is_sound` (parent) uses all eight children plus the five list-shuffling lemmas above.
- `verifyIsAuthorized_ok_implies` closes on its own by `simp`/`simp_do_let` (no named lemma).
- `swf_implies_enforce_satisfiedBy` → `enforce_satisfiedBy_swf` (the enforcer soundness theorem, in `Enforcer/Enforce.lean`).
- `asserts_last_not_true` → `asserts_satisfiedBy_true`.
- `isAuthorized_bisimulation` → `isAuthorized_interpret` → `isAuthorized_ok_implies` (Authorizer.lean), and `isAuthorized_same`, `interpret_εnv_wf_for_policies`.
- `isAuthorized_wf` → `isAuthorized_ok_implies`, `satisfiedPolicies_wf`, `wf_not`, `wf_and`.
- `wbaq_bisimulation` → `interpret_term_wf`.
- `interpret_not_wbaq` → `interpret_not`.
- `same_bool_not_not_true_implies_true` → `same_bool_def`, `pe_not_false`.

Why each child is a good leaf: each is a self-contained statement whose proof closes either on its own (`verifyIsAuthorized_ok_implies`) or from named siblings one step down (the rest), so none needs the parent's local context — the parent only combines them.

## Why it is good

1. `wbaq_bisimulation` occurs in the parent site (the glue) — the parent's proof actually cites the child rather than only stating it. (`check`, `cites(parent, wbaq_bisimulation)`; [VerifyIsAuthorized.lean L99-L132](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean#L99-L132))
2. No `sorry`, `admit` or `axiom` occurs in the copied file `VerifyIsAuthorized.lean` (lines 1-181). (`check`, `no_sorry`; [VerifyIsAuthorized.lean](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean))
3. The theorem-scale shape is `direct_lemmas=13`, `depth=3`, `glue_lines=34`, `child_lines=[17, 8, 12, 12, 12, 13, 11, 11]`, counted from the copied files. (`measurement`; glue = [L99-L132](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean#L99-L132); depth chain `verifyIsAuthorized_is_sound → isAuthorized_bisimulation → isAuthorized_interpret → isAuthorized_ok_implies` in [Authorizer.lean L450-L461, L406-L421, L361-L373](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/SymCC/Authorizer.lean))
4. The authors state the purpose in the file docstring: "This file proves the soundness and completeness of `Cedar.SymCC.verifyIsAuthorized` for well-behaved verification queries. This enables proving soundness and completenss of analyses built on `verifyIsAuthorized` by proving that their queries are well-behaved." (`author-statement`; [VerifyIsAuthorized.lean L22-L27](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean#L22-L27))
5. The sibling theorem `verifyIsAuthorized_is_complete` in the same file (lines 134-179) reuses the same `WellBehavedIsAuthorizedQuery` bundle and the same children (`verifyIsAuthorized_ok_implies` at line 150, `interpret_not_wbaq` at line 176, `wbaq_bisimulation` at line 177). (`known-use`; [VerifyIsAuthorized.lean L134-L179](https://github.com/cedar-policy/cedar-spec/blob/e619491a5bfb04970ef994dbe286df0bb9d0b73f/cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean#L134-L179))

In my opinion the detail worth copying is the bundle predicate itself: it is the interface. By making the theorem's premise a single `Prop` that packages exactly the properties the glue will need, the soundness proof is written once and every concrete analysis inherits it by filling one hole.

## When to use it, and when not

Use it when the same correctness theorem holds for many concrete queries or analyses that differ only in the parameters (here `φ` and `f`), so the theorem should be proved once against a bundle predicate; the bundle is then what each client proves, by unfolding only its own query. The glue consumes the bundle by pattern-matching it into its components (`⟨hwφ, hiφ, hφf⟩`).

Avoid it when the required properties do not compose into one reusable predicate, or when each client needs a different subset; when one component cannot be stated uniformly (here `Same` requires `f` to be a boolean-term comparison); or when the glue must inspect the bundle's internals in a way the single predicate hides.

## Consequences

The move replaces three separate well-behavedness obligations (`WellFormedOutput`, `Interpretable`, `Same`) with one `WellBehavedIsAuthorizedQuery φ f` obligation per concrete analysis. It couples the three properties: a client that needs `Same` under hypotheses the other components lack still pays for the strongest requirement, and the bundle must be stable under the analysis's own composition (`Interpretable` and `Same` are stated against the query applied to interpreted inputs). Failure mode: the predicate is too strong for some client and too weak for another, and every client is forced to use the same bundle.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/ci.yml job build_and_test_lean runs 'lake build Cedar SymCC' in ./cedar-lean; Cedar is a default-target lean_lib covering Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean; pinned commit e619491a5bfb04970ef994dbe286df0bb9d0b73f on default branch (registered ref HEAD) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: verifyIsAuthorized_ok_implies@cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean:114, swf_implies_enforce_satisfiedBy@cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean:116, asserts_last_not_true@cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean:119, isAuthorized_bisimulation@cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean:124, isAuthorized_wf@cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean:128, wbaq_bisimulation@cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean:131, interpret_not_wbaq@cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean:130, same_bool_not_not_true_implies_true@cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean:132; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 6 file(s) byte-identical at e619491a5bfb04970ef994dbe286df0bb9d0b73f | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, wbaq_bisimulation) -> cites: wbaq_bisimulation occurs at cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean:131 | check_claims.py |
| 2 | verified | no_sorry(cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean, 1-181) -> no_sorry: none of sorry, admit, axiom in cedar-lean/Cedar/Thm/SymCC/Verifier/VerifyIsAuthorized.lean:1-181 | check_claims.py |
| 3 | verified | counted from copied files: glue cites 13 distinct named lemmas (asserts_unsatisfiable_def, verifyIsAuthorized_ok_implies, swf_implies_enforce_satisfiedBy, swf_εnv_for_policies_iff_swf_for_append, swf_env_for_policies_iff_swf_for_append, asserts_last_not_true, swf_εnv_for_policies_implies_wf_for_policies, swf_env_for_policies_implies_wf_for_policies, isAuthorized_bisimulation, isAuthorized_wf, interpret_not_wbaq, wbaq_bisimulation, same_bool_not_not_true_implies_true) at lines 112-132; depth chain verifyIsAuthorized_is_sound -> isAuthorized_bisimulation (Authorizer.lean 459 cites isAuthorized_interpret) -> isAuthorized_interpret (Authorizer.lean 413 cites isAuthorized_ok_implies) -> isAuthorized_ok_implies; glue_lines=34 (99-132); child_lines match the 8 site spans [17,8,12,12,12,13,11,11] | verifier |
| 4 | verified | copied VerifyIsAuthorized.lean lines 22-27 docstring matches the quoted text verbatim, incl. the 'completenss' typo | verifier |
| 5 | verified | verifyIsAuthorized_is_complete at lines 134-179 pattern-matches WellBehavedIsAuthorizedQuery (line 147 intro <hwφ, hiφ, hφf>) and cites verifyIsAuthorized_ok_implies at line 150, interpret_not_wbaq at line 176, wbaq_bisimulation at line 177 | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent site VerifyIsAuthorized.lean 99-132 is a linear glue that cites exactly 13 distinct named lemmas: the 8 children (verifyIsAuthorized_ok_implies L114, swf_implies_enforce_satisfiedBy L116, asserts_last_not_true L119, isAuthorized_bisimulation L124/129, isAuthorized_wf L128/130, interpret_not_wbaq L130, wbaq_bisimulation L131, same_bool_not_not_true_implies_true L132) plus the 5 disclosed list-shuffling lemmas (asserts_unsatisfiable_def L40-45, swf_*_for_policies_* SWF.lean 110-172), so direct_lemmas=13 is right and no child is spurious. Each child's statement and closed_by match the copied code verbatim (e.g. swf_implies_enforce_satisfiedBy := enforce_satisfiedBy_swf; isAuthorized_bisimulation closes via isAuthorized_interpret, interpret_εnv_wf_for_policies, isAuthorized_same). The proof closes: final exact same_bool_not_not_true_implies_true hrb hsat where hrb:(f r1 r2)~(phi (t1.interpret I)(t2.interpret I)) and hsat:not(not(...))=true. Shape numbers all correct: glue_lines=34 = parent site 99-132; child_lines=[17,8,12,12,12,13,11,11] match site spans 81-97,30-37,47-58,450-461,375-386,55-67,69-79,48-58; depth=3 via parent -> isAuthorized_bisimulation(Authorizer 450-461) -> isAuthorized_interpret(406-421) -> isAuthorized_ok_implies(361-373). | reviewer-correctness |
| generality | accept | Move is stated beyond the example: intent and applicability.use_when/avoid_when are generic (bundle the finitely-many properties a correctness theorem depends on into one predicate; client proves only the bundle), and there is a concrete known-use — the sibling verifyIsAuthorized_is_complete (L135, 150, 176, 177) reuses the same WellBehavedIsAuthorizedQuery bundle and children, verified in the copied file. When-not-to-use is honest and specific: non-composable properties, clients needing different subsets, a non-uniform component (Same needs f bisimulating a term), and glue needing hidden internals — all trace to the three actual components. Consequences are honest: replaces three obligations with one, couples them (a client pays the strongest requirement), and states the too-strong/too-weak single-bundle failure mode. Good-leaves question is answered at README L245: each child is self-contained, closes on its own or from one-step-down siblings, needs no parent-local context, backed by shape (child_lines 8-17, depth 3). Minor imprecision only: 'Same requires f to be a boolean-term comparison' is loose (f returns Bool, related to the term via ~), and the known-use is a sibling in the same file, not independent — neither rises to an objection. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are consistent and traceable. check_provenance passes (6 files byte-identical at e619491a5bfb04970ef994dbe286df0bb9d0b73f). All permalinks in entry.json and README use the single pinned commit e619491a5bfb04970ef994dbe286df0bb9d0b73f, matching sources/cedar-spec/SOURCE.md (pinned 2026-11-14). entry.json licence Apache-2.0 matches SOURCE.md detected licence Apache-2.0, and the copied upstream-LICENSE is Apache License 2.0 (NOTICE: Copyright Cedar Contributors). README Source and licence section points to the source note and states Apache-2.0. Everything is traceable to the pinned commit. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/cedar-policy/cedar-spec at commit `e619491a5bfb04970ef994dbe286df0bb9d0b73f`, under `Apache-2.0`; see the [source note](../../sources/cedar-spec/SOURCE.md) for the licence text and attribution.
