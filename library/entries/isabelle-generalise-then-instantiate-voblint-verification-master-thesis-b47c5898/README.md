# One certified solver for all five merge rules via a rule-parameterised interpretation

| | |
|---|---|
| Kind | instance |
| Move | generalise-then-instantiate |
| Language | isabelle |
| Status | accepted |
| Source | [voblint-verification-master-thesis](../../sources/voblint-verification-master-thesis/SOURCE.md) at `07ecd3a886ef` |
| Licence | `BSD-3-Clause` |

## Intent

Certify the pipeline's solver contract `certified_solver` once, for the single
interpretation `TD_side_rule_Interp` parameterised by the `globals_rule` value
`r`, so that all five merge rules (join, per-origin, warrow, warrow-per-origin
and bounded narrowing) inherit the contract from one proof instead of each
discharging it separately.

## The decomposition

### parent `td_certified_solver`: [`src/Abstract_Interpreter/Solver/Globals_Rule.thy` lines 157-165](https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/blob/07ecd3a886efa3a5744caabc19fbb301a40384a5/src/Abstract_Interpreter/Solver/Globals_Rule.thy#L157-L165) ([local copy](code/src/Abstract_Interpreter/Solver/Globals_Rule.thy))

```isabelle
lemma td_certified_solver:
  "certified_solver (TD_side_rule_Interp_solve r)
     (TD_side_rule_Interp.solve_dom TYPE('g) TYPE('d::{bounded_semilattice_sup_bot,warrowing}) r)
     (TD_side_rule_Interp_solve_c r)"
  by unfold_locales
     (erule TD_side_rule_Interp.partial_post_solution[OF _ surjective_pairing],
      erule TD_side_rule_Interp.finite_stabl_solve,
      erule TD_side_rule_Interp.solve_dom_of_solve_c,
      simp add: TD_side_rule_Interp.solve_code_equation)
```

### the contract being discharged: `certified_solver` in [`src/Abstract_Interpreter/Solver/TD_Solver_Bridge.thy` lines 26-38](https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/blob/07ecd3a886efa3a5744caabc19fbb301a40384a5/src/Abstract_Interpreter/Solver/TD_Solver_Bridge.thy#L26-L38) ([local copy](code/src/Abstract_Interpreter/Solver/TD_Solver_Bridge.thy))

```isabelle
locale certified_solver =
  fixes solve :: "('x, 'g, 'd::bounded_semilattice_sup_bot) eqsT
                  \<Rightarrow> 'x \<Rightarrow> 'x set \<times> ('x + 'g \<Rightarrow> 'd)"
    and solve_dom :: "('x, 'g, 'd) eqsT \<Rightarrow> 'x \<Rightarrow> bool"
    and solve_c :: "('x, 'g, 'd) eqsT \<Rightarrow> 'x \<Rightarrow> ('x set \<times> ('x + 'g \<Rightarrow> 'd)) option"
  assumes solve_pp:
      "\<And>eqs x. solve_dom eqs x
         \<Longrightarrow> part_post_solution eqs x (snd (solve eqs x)) (fst (solve eqs x))"
    and solve_fin: "\<And>eqs x. solve_dom eqs x \<Longrightarrow> finite (fst (solve eqs x))"
    and dom_of_solve_c: "\<And>eqs x. solve_c eqs x \<noteq> None \<Longrightarrow> solve_dom eqs x"
    and solve_of_solve_c: "\<And>eqs x sol. solve_c eqs x = Some sol \<Longrightarrow> solve eqs x = sol"
```

### context `update_rule_update_global_of` (the generalise step): [`Globals_Rule.thy` lines 140-146](https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/blob/07ecd3a886efa3a5744caabc19fbb301a40384a5/src/Abstract_Interpreter/Solver/Globals_Rule.thy#L140-L146) ([local copy](code/src/Abstract_Interpreter/Solver/Globals_Rule.thy))

```isabelle
lemma update_rule_update_global_of:
  "update_rule init_ug_state_with_gas (update_global_of r)"
  by (cases r)
     (simp_all add: update_global_of_def update_rule_lift_basic_rule
        always_join.update_rule_axioms per_origin.update_rule_axioms
        warrowing_apinis.update_rule_axioms warrowing_per_origin.update_rule_axioms
        bounded_narrowing.update_rule_axioms)
```

### the interpretation that produces the children: [`Globals_Rule.thy` lines 148-153](https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/blob/07ecd3a886efa3a5744caabc19fbb301a40384a5/src/Abstract_Interpreter/Solver/Globals_Rule.thy#L148-L153) ([local copy](code/src/Abstract_Interpreter/Solver/Globals_Rule.thy))

```isabelle
global_interpretation TD_side_rule_Interp:
  TD_side_upd_rule init_ug_state_with_gas "update_global_of r" T for r T
  defines TD_side_rule_Interp_solve = TD_side_rule_Interp.solve
    and TD_side_rule_Interp_solve_c = TD_side_rule_Interp.solve_c
    and TD_side_rule_Interp_solve_rec_c = TD_side_rule_Interp.solve_rec_c
  by (simp add: TD_side_upd_rule.intro update_rule_update_global_of)
```

The four children are the locale facts of `TD_side_upd_rule` that this one
interpretation instantiates. Each is declared and proved inside the locale, in
the vendored TD solver (`git submodule vendor/td-verification`, session `TD`),
so its statement is outside the two copied files; each child's site above is
the interpretation block that instantiates it.

| child (name as cited by the glue) | statement | closes which `certified_solver` obligation |
|---|---|---|
| `TD_side_rule_Interp.partial_post_solution` | a solve in the solver's domain answers a partial post-solution | `solve_pp` |
| `TD_side_rule_Interp.finite_stabl_solve` | the solved key set is finite | `solve_fin` |
| `TD_side_rule_Interp.solve_dom_of_solve_c` | `solve_c` success implies the query is in the solver's domain | `dom_of_solve_c` |
| `TD_side_rule_Interp.solve_code_equation` | the executable `solve_c` is the solve itself (its code equation) | `solve_of_solve_c` |

### How the parts fit

The glue `by unfold_locales` opens the `certified_solver` locale, turning the
parent into its four assumptions as goals, then closes each with one
elimination of an interpreted fact:

```
td_certified_solver (parent, lines 157-165)
└─ unfold_locales: certified_solver's four assumptions
   ├─ solve_pp          ← erule TD_side_rule_Interp.partial_post_solution[OF _ surjective_pairing]  (line 162)
   ├─ solve_fin         ← erule TD_side_rule_Interp.finite_stabl_solve                               (line 163)
   ├─ dom_of_solve_c    ← erule TD_side_rule_Interp.solve_dom_of_solve_c                             (line 164)
   └─ solve_of_solve_c  ← simp add: TD_side_rule_Interp.solve_code_equation                          (line 165)
```

The four children do not come from four interpretations: they are the facts of
one interpretation, `global_interpretation TD_side_rule_Interp` (lines
148-153), whose single proof is `by (simp add: TD_side_upd_rule.intro
update_rule_update_global_of)`. That proof discharges the `TD_side_upd_rule`
locale for `update_global_of r` in one step, which in turn rests on
`update_rule_update_global_of` (the generalise step, lines 140-146), proved
once by `cases r` over the five `globals_rule` constructors. So the chain
below the parent is: parent → the four children → `update_rule_update_global_of`
→ `update_rule_lift_basic_rule` (lines 65-119), giving `depth` 3.

Each child is a good leaf for exactly that reason: its proof closed inside the
vendored locale, and the glue only eliminates it (`erule`/`simp add`) without
unfolding its internals. Each statement is self-contained — a single property
of the solver (`partial_post_solution`, `finite_stabl_solve`,
`solve_dom_of_solve_c`, `solve_code_equation`) — and the four are named
siblings of one locale, so a reader sees the whole contract as four one-line
obligations rather than one large proof.

## Why it is good

1. The main theorem `td_certified_solver` is declared in
   `src/Abstract_Interpreter/Solver/Globals_Rule.thy` at lines 157-165
   (`check`, `declared(td_certified_solver, src/Abstract_Interpreter/Solver/Globals_Rule.thy, 157-165)`).
2. The parent site is 9 lines long, the `glue_lines` of the theorem-scale shape
   (`check`, `lines(parent, 9)`).
3. The parent site cites `TD_side_rule_Interp.partial_post_solution`
   (`check`, `cites(parent, TD_side_rule_Interp.partial_post_solution)`).
4. The authors state the move in the file's own comment: "a single
   interpretation takes the rule as a parameter, and every solver fact holds
   for all five at once" ([lines 14-16](https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/blob/07ecd3a886efa3a5744caabc19fbb301a40384a5/src/Abstract_Interpreter/Solver/Globals_Rule.thy#L14-L16))
   (`author-statement`).
5. The authors record that this one fact is reused: "`td_certified_solver`
   (`Globals_Rule`) discharges it for every `globals_rule`; the generated
   `<Domain>_Analyses.thy` registrations cite that one fact" ([Solver README lines 38-39](https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/blob/07ecd3a886efa3a5744caabc19fbb301a40384a5/src/Abstract_Interpreter/Solver/README.md#L38-L39))
   (`author-statement`).

The theorem-scale shape — `direct_lemmas = 4`, `depth = 3`,
`glue_lines = 9`, `child_lines = [6, 6, 6, 6]` — is recomputed from the sites
by `validate_entry.py --strict`; `child_lines` is four times 6 because each
child's site is the 6-line interpretation block that instantiates it.

In my opinion the detail worth copying is that the parameter is a *value*
(`update_global_of r`) rather than a choice between five solvers: the file
turns "which merge rule" into a datatype, proves the update rule once over that
datatype, and lets the locale instantiation carry every solver fact across all
five rules at once.

## When to use it, and when not

Use it when a family of instances shares one contract and differs only by a
value (here `globals_rule`): state the value as a datatype, prove the shared
obligation once over its constructors, and discharge the target contract from a
single interpretation parameterised by that value. This collapses N per-instance
proofs into one generalisation plus one instantiation.

Avoid it when the instances need different arguments for some assumption (the
uniform interpretation will not close that case), or when the parameter is not
a value but a first-class choice that each proof must reason about separately —
then a single interpretation cannot carry the difference and per-instance proofs
return.

## Consequences

The move replaces five per-rule interpretations with one. Its obligation is
exhaustiveness over the rule value: `update_rule_update_global_of` proves the
update-rule property by `cases r` (lines 142-146), which must cover every
`globals_rule` constructor. If a new rule is added, `update_global_of` and
`update_rule_update_global_of` must be extended, but the solver-contract proof
`td_certified_solver` does not change. The failure mode is a non-uniform
instance: a rule that needed a different argument for one assumption would
break the single interpretation and force per-rule proofs.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/ci.yml builds every Isabelle session (isabelle-build job: pixi run isabelle-build; isabelle-html job: clean build of every session) on push to main; pinned commit 07ecd3a886efa3a5744caabc19fbb301a40384a5 is identical to main tip (GitHub compare main...07ecd3a: status identical) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: TD_side_rule_Interp.partial_post_solution@src/Abstract_Interpreter/Solver/Globals_Rule.thy:162, TD_side_rule_Interp.finite_stabl_solve@src/Abstract_Interpreter/Solver/Globals_Rule.thy:163, TD_side_rule_Interp.solve_dom_of_solve_c@src/Abstract_Interpreter/Solver/Globals_Rule.thy:164, TD_side_rule_Interp.solve_code_equation@src/Abstract_Interpreter/Solver/Globals_Rule.thy:165; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at 07ecd3a886efa3a5744caabc19fbb301a40384a5 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(td_certified_solver, src/Abstract_Interpreter/Solver/Globals_Rule.thy, 157-165) -> declared: td_certified_solver is declared at src/Abstract_Interpreter/Solver/Globals_Rule.thy:157 | check_claims.py |
| 2 | verified | lines(parent, 9) -> lines: site parent has 9 lines | check_claims.py |
| 3 | verified | cites(parent, TD_side_rule_Interp.partial_post_solution) -> cites: TD_side_rule_Interp.partial_post_solution occurs at src/Abstract_Interpreter/Solver/Globals_Rule.thy:162 | check_claims.py |
| 4 | verified | code/src/Abstract_Interpreter/Solver/Globals_Rule.thy lines 14-15 contain verbatim: 'a single interpretation takes the rule as a parameter, and every solver fact holds for all five at once.' | verifier |
| 5 | verified | Fetched src/Abstract_Interpreter/Solver/README.md at pinned commit; lines 38-39 match the claim's quoted sentences verbatim. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Decomposition matches the copied code: parent td_certified_solver is at Globals_Rule.thy:157-165 and its statement is verbatim; its glue 'by unfold_locales' opens certified_solver and closes its four assumptions solve_pp/solve_fin/dom_of_solve_c/solve_of_solve_c via erule partial_post_solution[OF _ surjective_pairing] (162), erule finite_stabl_solve (163), erule solve_dom_of_solve_c (164), simp add: solve_code_equation (165). The four children named in entry.json are exactly the four facts the glue cites, and the TD_Solver_Bridge.thy text (lines 18-20) confirms those four are proved inside locale TD_side_upd_rule; they are instantiated by global_interpretation TD_side_rule_Interp (148-153). Shape numbers check out: direct_lemmas=4 (four cited facts), glue_lines=9 (parent 157-165), child_lines=[6,6,6,6] (interpretation block 148-153 is 6 lines), depth=3 (children <- update_rule_update_global_of:140-146 <- update_rule_lift_basic_rule:65-119). Five merge rules match the five constructors of globals_rule (18-23). Decomposition closes. | reviewer-correctness |
| generality | accept | Move stated abstractly (state the selector as a datatype, prove the shared obligation once over its constructors, discharge the contract from one parameterised interpretation), and applicability fields give a general goal_shape plus use_when/avoid_when, so it applies beyond this example; known_uses honestly empty. When-not-to-use is specific and tied to the mechanics: avoid when an assumption needs a per-instance argument (a uniform interpretation cannot close it) or when the parameter is a first-class choice each proof must reason about, not a value. Consequences are honest: replaces five per-rule interpretations with one; names the exhaustiveness obligation (cases r over the five constructors, lines 142-146) and that adding a constructor forces extending update_global_of/update_rule_update_global_of but not td_certified_solver; states the non-uniform-instance failure mode. Good-leaf question answered specifically: each child is a self-contained single solver property whose proof closed inside the vendored locale, and the glue only eliminates it (erule/simp add) without unfolding internals, so the contract reads as four one-line obligations. Verified against the cited line ranges (Globals_Rule 14-23, 65-119, 140-165; TD_Solver_Bridge 26-38): parent, context, interpretation and author comment all match the README. | reviewer-generality |
| provenance-licence | accept | Commit 07ecd3a886efa3a5744caabc19fbb301a40384a5 is consistent across entry.json files/sites permalinks, source.json and SOURCE.md; licence BSD-3-Clause matches upstream-LICENSE (BSD 3-Clause) and the source note; check_provenance passes (2 files byte-identical at the pinned commit); cited line ranges (Globals_Rule 14-16 comment, 18-23 datatype, 140-146 context, 148-153 interpretation, 157-165 parent; TD_Solver_Bridge 26-38) all match the local copies. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis at commit `07ecd3a886efa3a5744caabc19fbb301a40384a5`, under `BSD-3-Clause`; see the [source note](../../sources/voblint-verification-master-thesis/SOURCE.md) for the licence text and attribution.
