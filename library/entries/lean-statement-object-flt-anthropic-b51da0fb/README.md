# Statement-only FLT node fermatLastTheoremFive, closed by delegating to S_fermatLastTheoremFive.solution

| | |
|---|---|
| Kind | instance |
| Move | statement-object |
| Language | lean |
| Status | draft |
| Source | [flt-anthropic](../../sources/flt-anthropic/SOURCE.md) at `6e837e753555` |
| Licence | `Apache-2.0` |

## Intent

The theorem `fermatLastTheoremFive : FermatLastTheoremFor 5` (Fermat's Last Theorem for exponent 5) is stated in its own file with no proof, and its proof lives in a separate solution module. The statement file imports that module and closes with the single line `p2m_exact_reverting @_root_.P2MW.S_fermatLastTheoremFive.solution`, so statement and proof are two immutable files joined only by an import and a type check.

## The decomposition

### parent `fermatLastTheoremFive`: [`Theorems/Thm_fermatLastTheoremFive.lean` lines 1-5](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_fermatLastTheoremFive.lean#L1-L5) ([local copy](code/Theorems/Thm_fermatLastTheoremFive.lean))

```lean
import Mathlib
import P2M.Util
import P2M.Sol.S_fermatLastTheoremFive

theorem fermatLastTheoremFive : FermatLastTheoremFor 5 := by p2m_exact_reverting @_root_.P2MW.S_fermatLastTheoremFive.solution
```

### child `solution`: [`P2M/Sol/S_fermatLastTheoremFive.lean` lines 1987-1989](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_fermatLastTheoremFive.lean#L1987-L1989) ([local copy](code/P2M/Sol/S_fermatLastTheoremFive.lean))

```lean
theorem solution : FermatLastTheoremFor 5 := by
  rw [fermatLastTheoremFor_iff_int]
  exact FLT5.flt_five_int
```

### context `p2m-exact-reverting`: [`P2M/Util.lean` lines 3-16](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Util.lean#L3-L16) ([local copy](code/P2M/Util.lean))

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

### context `proof-path-convention`: [`PROOF-PATH.md` lines 4-5](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md#L4-L5) ([local copy](code/PROOF-PATH.md))

```markdown
run as a proof by contradiction. A theorem `X.y` is stated in `Theorems/Thm_X_y.lean` and proved in
`P2M/Sol/S_X_y.lean`, whose `import Theorems.Thm_…` lines are exactly the theorems it cites. Where this prose and the
```

The parent `fermatLastTheoremFive` is the statement-object: the whole of `Theorems/Thm_fermatLastTheoremFive.lean` is three imports plus one theorem with a one-line proof. It imports `P2M.Util` (for the `p2m_exact_reverting` tactic) and `P2M.Sol.S_fermatLastTheoremFive` (the proof module), then closes by delegating: `by p2m_exact_reverting @_root_.P2MW.S_fermatLastTheoremFive.solution`.

The child `solution` (the last three lines of `P2M/Sol/S_fermatLastTheoremFive.lean`) is the actual proof of `FermatLastTheoremFor 5`: it rewrites to the integer form with `fermatLastTheoremFor_iff_int` and applies `FLT5.flt_five_int`, the roughly 1 900-line descent over Z[(1+√5)/2] developed earlier in the same file.

The join is `p2m_exact_reverting` (`P2M/Util.lean` lines 3-16): it reverts every non-implementation-detail hypothesis, elaborates `@_root_.P2MW.S_fermatLastTheoremFive.solution` against the goal type `FermatLastTheoremFor 5`, and throws if metavariables remain. The parent therefore closes exactly when the solution's type matches the statement — the delegation re-checks sufficiency by type.

The convention (`PROOF-PATH.md` lines 4-5) says every theorem `X.y` is stated in `Theorems/Thm_X_y.lean` and proved in `P2M/Sol/S_X_y.lean`, whose `import Theorems.Thm_…` lines are exactly the theorems it cites. This node is a leaf: `fermatLastTheoremFive` is a self-contained descent, so its solution imports no `Theorems.Thm_…` at all.

## Why it is good

1. The parent file is five lines and one theorem, whose whole proof is the delegation `p2m_exact_reverting @_root_.P2MW.S_fermatLastTheoremFive.solution`; no other declaration or proof appears ([Thm_fermatLastTheoremFive.lean#L1-L5](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_fermatLastTheoremFive.lean#L1-L5)) — `check`.
2. The child `solution` has type `FermatLastTheoremFor 5`, exactly the parent's target, so `p2m_exact_reverting` closes the parent ([S_fermatLastTheoremFive.lean#L1987-L1989](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_fermatLastTheoremFive.lean#L1987-L1989)) — `check`.
3. `p2m_exact_reverting` reverts the context and re-checks the term's type against the goal, so the delegation fails unless the solution matches the statement ([P2M/Util.lean#L3-L16](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Util.lean#L3-L16)) — `check`.
4. The project states the convention itself: "A theorem `X.y` is stated in `Theorems/Thm_X_y.lean` and proved in `P2M/Sol/S_X_y.lean`, whose `import Theorems.Thm_…` lines are exactly the theorems it cites." ([PROOF-PATH.md#L4-L5](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md#L4-L5)) — `author-statement`.
5. The solution module imports seven Mathlib files and `P2M.Util`, never `Theorems.Thm_fermatLastTheoremFive`, so the dependency is one-way: the statement file imports the solution, never the reverse ([S_fermatLastTheoremFive.lean#L1-L8](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_fermatLastTheoremFive.lean#L1-L8)) — `check`.

In my opinion the detail worth copying is not the delegation tactic itself but the one-way split: the statement is a stable, citable object that the proof must match by type, and the proof never imports the statement, so a statement can be cited before it is proved without risking a cycle.

## When to use it, and when not

Use it when you want a statement to be an immutable, citable object separate from its proof — for example when many other nodes must import the statement before it is proved, or when independent proof attempts should converge on one canonical statement (Prove2Me's "milestones"). It needs a check that the proof matches the statement: here `p2m_exact_reverting` (and the `#p2m_type_eq` command in `P2M/Util.lean`) enforce that by type.

Avoid it when the statement and proof are best read together and nothing else needs to cite the statement before it is proved; when the proof is not a single self-contained term that one reference can pull in; or when the proof is more general or less general than the statement, so the type check fails and the statement must be corrected rather than delegated to.

## Consequences

The statement file carries no proof obligations of its own: its single obligation is discharged by the delegated term, and `p2m_exact_reverting` re-checks that term's type. Obligations created: the solution module must define a term of exactly the statement's type (a mismatch, or a solution more or less general than the statement, is a hard error — `#p2m_type_eq` reports `P2M_TYPE_MISMATCH` / `P2M_UNDERGENERAL`); the import must name the right module; and statement and solution are tied by the type match, so neither can change without the other. Failure modes: a circular import if the solution ever imports the statement; a statement that drifts from the proof it delegates to.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | not-run | No CI workflow in the source: no .github/workflows directory exists at commit 6e837e75355538c7f80bab5b956861e86c4eacc2 (pinned commit = HEAD of default branch main, per GitHub API); formalization.yaml is metadata, not CI. No local Lean toolchain installed. | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 4 file(s) byte-identical at 6e837e75355538c7f80bab5b956861e86c4eacc2 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read code/Theorems/Thm_fermatLastTheoremFive.lean (byte-identical to remote at commit): 5 lines = import Mathlib, import P2M.Util, import P2M.Sol.S_fermatLastTheoremFive, blank, and theorem fermatLastTheoremFive : FermatLastTheoremFor 5 := by p2m_exact_reverting @_root_.P2MW.S_fermatLastTheoremFive.solution; no other declaration. | verifier |
| 2 | verified | Read code/P2M/Sol/S_fermatLastTheoremFive.lean lines 1987-1989: theorem solution : FermatLastTheoremFor 5 := by rw [fermatLastTheoremFor_iff_int]; exact FLT5.flt_five_int — type is FermatLastTheoremFor 5, matching the parent target. | verifier |
| 3 | verified | Read code/P2M/Util.lean lines 3-16: p2m_exact_reverting folds lctx collecting non-isImplementationDetail fvarIds (revert), reverts them, elaborates via elabTermEnsuringType e tgt against goal type, throws if v.hasExprMVar (unassigned metavariables remain). | verifier |
| 4 | verified | Read code/PROOF-PATH.md lines 4-5: "A theorem `X.y` is stated in `Theorems/Thm_X_y.lean` and proved in `P2M/Sol/S_X_y.lean`, whose `import Theorems.Thm_…` lines are exactly the theorems it cites." matches the quoted author statement verbatim. | verifier |
| 5 | verified | Read code/P2M/Sol/S_fermatLastTheoremFive.lean lines 1-8: seven Mathlib imports (Algebra.Ring.Associated, Data.Nat.Fib.Basic, Data.ZMod.Basic, NumberTheory.FLT.Basic, RingTheory.Int.Basic, RingTheory.PrincipalIdealDomain, Tactic) plus P2M.Util; no import of Theorems.Thm_fermatLastTheoremFive — one-way dependency. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | object | Child 'solution' closed_by field misattributes the closing method: entry.json records closed_by='p2m_exact_reverting @_root_.P2MW.S_fermatLastTheoremFive.solution', but that is the PARENT's delegation tactic (how fermatLastTheoremFive pulls the child in), not how the child closes. The code (P2M/Sol/S_fermatLastTheoremFive.lean lines 1987-1989) shows the child closes by 'rw [fermatLastTheoremFor_iff_int]; exact FLT5.flt_five_int'. Every sibling entry uses closed_by for how the child itself closes, so this contradicts the code and its own statement field. Fix: set children[0].closed_by to 'rw [fermatLastTheoremFor_iff_int]; exact FLT5.flt_five_int'. All 5 claims verified and the decomposition itself closes correctly; this is the only correctness defect. | reviewer-correctness |
| generality | accept | Move is generalised beyond the FLT5 example: applicability.goal_shape abstracts to 'a theorem statement occupying its own file ... one theorem whose proof body is a single term or tactic that pulls a proof in from a separate module', with the delegation tactic flagged as 'here p2m_exact_reverting <proof-term>'. use_when/avoid_when give concrete, general conditions (immutable citable object cited before proved; vs. statement+proof best read together / proof not a single self-contained term / proof more-or-less general than the statement). The 'when not to use' and consequences are honest and specific: I opened the local copies and confirmed #p2m_type_eq genuinely reports P2M_TYPE_MISMATCH and P2M_UNDERGENERAL (P2M/Util.lean L38, L40), the solution's imports are seven Mathlib files + P2M.Util with no Theorems import (one-way split), and PROOF-PATH.md states the convention. The generalisable principle (one-way split, proof matched by type) is correctly separated from the specific tactic and labelled as opinion. Accept. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are all consistent and traceable. check_provenance.py passes (4 file(s) byte-identical at 6e837e75355538c7f80bab5b956861e86c4eacc2). Local copies' sha256 and byte counts match entry.json's files array exactly (198/1e118431..., 82551/bba6572a..., 5737/66f62069..., 8666/ada9b1b2...). Commit 6e837e75355538c7f80bab5b956861e86c4eacc2 is identical across entry.json source.commit, every file/site permalink, sources/flt-anthropic/SOURCE.md and source.json. Licence Apache-2.0 is identical in entry.json source.licence, README, SOURCE.md and source.json, and upstream-LICENSE is the Apache License 2.0 text; source note lists LICENSE+NOTICE (both present locally as upstream-LICENSE/upstream-NOTICE). Repo URL anthropics/fermats-last-theorem is consistent everywhere. No provenance or licence inconsistency found. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/anthropics/fermats-last-theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, under `Apache-2.0`; see the [source note](../../sources/flt-anthropic/SOURCE.md) for the licence text and attribution.
