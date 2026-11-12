# Statement-object: IsCyclotomicExtension.Rat.seven_pid stated in its own file, proved in a solution module

| | |
|---|---|
| Kind | instance |
| Move | statement-object |
| Language | lean |
| Status | draft |
| Source | [flt-anthropic](../../sources/flt-anthropic/SOURCE.md) at `6e837e753555` |
| Licence | `Apache-2.0` |

## Intent

The theorem `IsCyclotomicExtension.Rat.seven_pid` — the ring of integers of a
cyclotomic field with conductor 7 is a principal ideal ring — is stated in its
own six-line file with no proof and closed by delegating to a separate solution
module: the statement file imports `P2M.Sol.S_IsCyclotomicExtension_Rat_seven_pid`
and its single proof line is
`p2m_exact_reverting @_root_.P2MW.S_IsCyclotomicExtension_Rat_seven_pid.solution`,
so statement and proof are two files joined only by an import and a type match.

## The decomposition

### parent `IsCyclotomicExtension.Rat.seven_pid`: [`Theorems/Thm_IsCyclotomicExtension_Rat_seven_pid.lean` lines 1-6](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_IsCyclotomicExtension_Rat_seven_pid.lean#L1-L6) ([local copy](code/Theorems/Thm_IsCyclotomicExtension_Rat_seven_pid.lean))

```lean
import Mathlib
import P2M.Util
import P2M.Sol.S_IsCyclotomicExtension_Rat_seven_pid

open scoped NumberField
theorem IsCyclotomicExtension.Rat.seven_pid (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {7} ℚ K] : IsPrincipalIdealRing (𝓞 K) := by p2m_exact_reverting @_root_.P2MW.S_IsCyclotomicExtension_Rat_seven_pid.solution
```

### child `solution`: [`P2M/Sol/S_IsCyclotomicExtension_Rat_seven_pid.lean` lines 81-84](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsCyclotomicExtension_Rat_seven_pid.lean#L81-L84) ([local copy](code/P2M/Sol/S_IsCyclotomicExtension_Rat_seven_pid.lean))

```lean
open scoped NumberField in
theorem solution (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {7} ℚ K] :
    IsPrincipalIdealRing (𝓞 K) :=
  SevenPidPort.seven_pid K
```

### context `p2m_exact_reverting`: [`P2M/Util.lean` lines 3-16](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Util.lean#L3-L16) ([local copy](code/P2M/Util.lean))

```lean
open Lean Elab Tactic Meta in
elab "p2m_exact_reverting " e:term : tactic => do
  let g ← getMainGoal
  let lctx := (← g.getDecl).lctx
  let fvars := lctx.foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail then acc else acc.push d.fvarId
  let (_, g') ← g.revert fvars (preserveOrder := true) (clearAuxDeclsInsteadOfRevert := true)
  g'.withContext do
    let tgt ← g'.getType
    let v ← Term.withSynthesize <| elabTermEnsuringType e tgt
    let v ← instantiateMVars v
    if v.hasExprMVar then throwError "p2m_exact_reverting: unassigned metavariables remain"
    g'.assign v
  replaceMainGoal []
```

How the parts fit. The statement node (parent) is the whole of
`Theorems/Thm_IsCyclotomicExtension_Rat_seven_pid.lean`: it imports its own
solution at line 3 and closes the theorem with a single tactic call,
`p2m_exact_reverting @_root_.P2MW.S_IsCyclotomicExtension_Rat_seven_pid.solution`
(line 6). `p2m_exact_reverting` (defined in `P2M/Util.lean`) reverts the
context — `K` and the `Field`/`NumberField`/`IsCyclotomicExtension` instances —
from the goal, then elaborates the supplied term against the resulting
general goal and assigns it, failing if metavariables remain. The child
`solution` (`P2M/Sol/S_IsCyclotomicExtension_Rat_seven_pid.lean` lines 81-84)
is a theorem with exactly the statement's type, and it closes by applying
`SevenPidPort.seven_pid K` — the real cyclotomic-PID argument (lines 59-76),
which applies the Minkowski bound to reduce to a handful of small primes and
rules them out case by case. So the statement node carries no proof content of
its own: it is a citation to the solution module, and the type check is what
guarantees the two files have not drifted apart.

## Why it is good

1. The statement file is six lines — three imports, one `open scoped`, and one
   theorem whose entire proof is the single call
   `p2m_exact_reverting @_root_.P2MW.S_IsCyclotomicExtension_Rat_seven_pid.solution`
   — with no other declaration or proof (`check`, statement file lines 1-6).
2. The statement file imports its own solution module
   (`import P2M.Sol.S_IsCyclotomicExtension_Rat_seven_pid`, line 3), and the
   solution module imports five Mathlib files plus `P2M.Util`, never the
   statement file, so the dependency is one-way: statement → solution
   (`check`, statement file lines 1-6 and solution file lines 1-6).
3. `p2m_exact_reverting` reverts the context and type-checks the supplied term
   against the goal before assigning it, failing if metavariables remain, so
   the parent closes only when the solution's type equals the statement's
   (`check`, `P2M/Util.lean` lines 3-16 and the matching solution type at
   lines 81-84).
4. The authors state this split as their project-wide convention: "A theorem
   `X.y` is stated in `Theorems/Thm_X_y.lean` and proved in
   `P2M/Sol/S_X_y.lean`, whose `import Theorems.Thm_…` lines are exactly the
   theorems it cites" (`author-statement`, `PROOF-PATH.md` lines 4-5).

In my opinion the reusable idea is the one-way import: the statement node is
the only thing a parent cites, and the proof lives behind it in a solution
module, so the statement stays stable while the proof inside the solution is
free to change. The matching type, enforced by `p2m_exact_reverting`, is the
whole discipline.

## When to use it, and when not

Use it when you want each theorem to be a stable, citable object whose
statement is independent of the proof that fills it — a proof-path or
blueprint-driven project, or a harness where the statement is the contract
between the decomposer and the prover. The statement file can be imported and
cited before its proof is complete. Avoid it when the statement and proof are
naturally small and local (a one-line lemma with an inline proof), when
splitting every theorem into two files adds import ceremony with no benefit,
or when the proof cannot be expressed as a single term whose type matches the
statement (the `p2m_exact_reverting` / `#p2m_type_eq` type match will reject
any mismatch or any under-general solution).

## Consequences

The statement file has no proof obligations of its own: its single obligation
is discharged by the delegated term, and `p2m_exact_reverting` re-checks that
term's type against the statement. Obligations created: (1) the solution
module must define a term of exactly the statement's type — a mismatch, or a
solution more or less general than the statement, is a hard error (the
`#p2m_type_eq` command in `P2M/Util.lean` reports `P2M_TYPE_MISMATCH` or
`P2M_UNDERGENERAL`); (2) the import must name the right module; (3) statement
and solution are tied by the type match, so neither can change without the
other. Failure modes: a circular import if the solution ever imports the
statement; a statement that silently drifts from the proof it delegates to
(the type check catches a type drift, but not a change in meaning with the
same type).

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | not-run | source has no CI workflow: no .github/workflows directory (root of anthropics/fermats-last-theorem at 6e837e7 lists no .github; verification/ holds local comparator/nanoda tooling, not a hosted build of this file) | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 4 file(s) byte-identical at 6e837e75355538c7f80bab5b956861e86c4eacc2 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read code/Theorems/Thm_IsCyclotomicExtension_Rat_seven_pid.lean: 6 lines = import Mathlib, import P2M.Util, import P2M.Sol.S_IsCyclotomicExtension_Rat_seven_pid, blank, open scoped NumberField, and the single theorem with body (by p2m_exact_reverting @_root_.P2MW.S_IsCyclotomicExtension_Rat_seven_pid.solution); no other declaration | verifier |
| 2 | verified | Thm file line 3 imports P2M.Sol.S_IsCyclotomicExtension_Rat_seven_pid; solution module imports (lines 1-6) are 5 Mathlib files + P2M.Util, none is Theorems.Thm_IsCyclotomicExtension_Rat_seven_pid, so dependency is one-way | verifier |
| 3 | verified | P2M/Util.lean lines 3-16: p2m_exact_reverting folds lctx keeping only non-ImplementationDetail fvars, g.revert, elabTermEnsuringType e tgt, then throwError if hasExprMVar; S file lines 81-84 theorem solution has type (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {7} Q K] : IsPrincipalIdealRing (O K), matching the parent statement | verifier |
| 4 | verified | PROOF-PATH.md lines 4-5 contain the quoted convention verbatim: "A theorem X.y is stated in Theorems/Thm_X_y.lean and proved in P2M/Sol/S_X_y.lean, whose import Theorems.Thm_... lines are exactly the theorems it cites." | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent file is 6 lines (imports Mathlib/P2M.Util/P2M.Sol.S_IsCyclotomicExtension_Rat_seven_pid, open scoped NumberField, one theorem) whose whole proof is p2m_exact_reverting @_root_.P2MW.S_IsCyclotomicExtension_Rat_seven_pid.solution. Child solution (S file L81-84) has type (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {7} Q K] : IsPrincipalIdealRing (O K), textually identical to the parent statement, and closes via SevenPidPort.seven_pid K (a fully proved theorem, L59-76). p2m_exact_reverting (Util.lean L3-16) reverts context then elabTermEnsuringType e tgt and throws on residual metavariables, so the delegation closes exactly on type match. Decomposition, children and closing methods all match the copied code; it closes. | reviewer-correctness |
| generality | object | Move is stated generically (goal_shape, use_when mention proof-path/blueprint/harness projects; author-statement shows it is a project-wide convention), so it does apply beyond the example. But 'when not to use' and consequences overstate the boundary: they say a solution 'more or less general than the statement is a hard error' (applicability.avoid_when, consequences in entry.json, and README consequences). The cited mechanism does not reject a MORE general solution: P2M/Util.lean #p2m_type_eq (L19-40) only reports P2M_TYPE_MISMATCH and P2M_UNDERGENERAL ('the proof is less general than the card'), and p2m_exact_reverting (L3-16) uses elabTermEnsuringType, which specialises a more-general term to the goal. Only a mismatch or an under-general (less general) solution is the hard error. Claiming more-general is rejected wrongly steers users away from a valid, desirable case. Fix: in applicability.avoid_when and both consequences texts, replace 'more or less general' / 'more general or less general' with 'less general (under-general)', and note a more-general proof is accepted (specialised to the statement). | reviewer-generality |
| provenance-licence | accept | Provenance pass: 4 files byte-identical at 6e837e75355538c7f80bab5b956861e86c4eacc2. Commit 6e837e753555... is recorded identically in entry.json, README.md, SOURCE.md and source.json; every permalink (files and sites) pins that commit with correct paths and line anchors (statement L1-L6, solution L81-L84, Util L3-L16, PROOF-PATH L4-L5 all match the copied code). Licence Apache-2.0 is recorded identically in entry.json, README.md and SOURCE.md, and the copied upstream-LICENSE is the Apache-2.0 text (Copyright 2026 Anthropic, PBC); SOURCE.md names LICENSE and NOTICE, both present as upstream-LICENSE and upstream-NOTICE. Everything traceable, nothing inconsistent. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/anthropics/fermats-last-theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, under `Apache-2.0`; see the [source note](../../sources/flt-anthropic/SOURCE.md) for the licence text and attribution.
