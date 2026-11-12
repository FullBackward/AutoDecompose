# Interface lemmas behind CompCert's transf_c_program_correct

| | |
|---|---|
| Kind | instance |
| Move | interface-lemma |
| Language | rocq |
| Status | accepted |
| Source | [compcert](../../sources/compcert/SOURCE.md) at `2685140bf72c` |
| Licence | `LicenseRef-INRIA-Non-Commercial` |

## Intent

CompCert's headline correctness theorem — a C program `p` compiled successfully to
assembly `tp` is related by a backward simulation — is assembled in a single
tactic line from two interface lemmas: `transf_c_program_match` (compilation
yields `match_prog`) and `c_semantic_preservation` (`match_prog` yields the
backward simulation). The client never unfolds the 20-pass compile chain or the
simulation construction.

## The decomposition

### parent `transf_c_program_correct`: [`driver/Compiler.v` lines 446-452](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/driver/Compiler.v#L446-L452) ([local copy](code/driver/Compiler.v))

```coq
Theorem transf_c_program_correct:
  forall p tp,
  transf_c_program p = OK tp ->
  backward_simulation (Csem.semantics p) (Asm.semantics tp).
Proof.
  intros. apply c_semantic_preservation. apply transf_c_program_match; auto.
Qed.
```

### child `transf_c_program_match`: [`driver/Compiler.v` lines 265-318](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/driver/Compiler.v#L265-L318) ([local copy](code/driver/Compiler.v))

```coq
Theorem transf_c_program_match:
  forall p tp,
  transf_c_program p = OK tp ->
  match_prog p tp.
Proof.
  intros p tp T.
  unfold transf_c_program, time in T. simpl in T.
  destruct (SimplExpr.transl_program p) as [p1|e] eqn:P1; simpl in T; try discriminate.
  unfold transf_clight_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (SimplLocals.transf_program p1) as [p2|e] eqn:P2; simpl in T; try discriminate.
  destruct (Cshmgen.transl_program p2) as [p3|e] eqn:P3; simpl in T; try discriminate.
  destruct (Cminorgen.transl_program p3) as [p4|e] eqn:P4; simpl in T; try discriminate.
  unfold transf_cminor_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (Selection.sel_program p4) as [p5|e] eqn:P5; simpl in T; try discriminate.
  destruct (RTLgen.transl_program p5) as [p6|e] eqn:P6; simpl in T; try discriminate.
  unfold transf_rtl_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  set (p7 := total_if optim_tailcalls Tailcall.transf_program p6) in *.
  destruct (Inlining.transf_program p7) as [p8|e] eqn:P8; simpl in T; try discriminate.
  set (p9 := Renumber.transf_program p8) in *.
  set (p10 := total_if optim_constprop Constprop.transf_program p9) in *.
  set (p11 := total_if optim_constprop Renumber.transf_program p10) in *.
  destruct (partial_if optim_CSE CSE.transf_program p11) as [p12|e] eqn:P12; simpl in T; try discriminate.
  destruct (partial_if optim_redundancy Deadcode.transf_program p12) as [p13|e] eqn:P13; simpl in T; try discriminate.
  destruct (Unusedglob.transform_program p13) as [p14|e] eqn:P14; simpl in T; try discriminate.
  destruct (Allocation.transf_program p14) as [p15|e] eqn:P15; simpl in T; try discriminate.
  set (p16 := Tunneling.tunnel_program p15) in *.
  destruct (Linearize.transf_program p16) as [p17|e] eqn:P17; simpl in T; try discriminate.
  set (p18 := CleanupLabels.transf_program p17) in *.
  destruct (partial_if debug Debugvar.transf_program p18) as [p19|e] eqn:P19; simpl in T; try discriminate.
  destruct (Stacking.transf_program p19) as [p20|e] eqn:P20; simpl in T; try discriminate.
  unfold match_prog; simpl.
  exists p1; split. apply SimplExprproof.transf_program_match; auto.
  exists p2; split. apply SimplLocalsproof.match_transf_program; auto.
  exists p3; split. apply Cshmgenproof.transf_program_match; auto.
  exists p4; split. apply Cminorgenproof.transf_program_match; auto.
  exists p5; split. apply Selectionproof.transf_program_match; auto.
  exists p6; split. apply RTLgenproof.transf_program_match; auto.
  exists p7; split. apply total_if_match. apply Tailcallproof.transf_program_match.
  exists p8; split. apply Inliningproof.transf_program_match; auto.
  exists p9; split. apply Renumberproof.transf_program_match; auto.
  exists p10; split. apply total_if_match. apply Constpropproof.transf_program_match.
  exists p11; split. apply total_if_match. apply Renumberproof.transf_program_match.
  exists p12; split. eapply partial_if_match; eauto. apply CSEproof.transf_program_match.
  exists p13; split. eapply partial_if_match; eauto. apply Deadcodeproof.transf_program_match.
  exists p14; split. apply Unusedglobproof.transf_program_match; auto.
  exists p15; split. apply Allocproof.transf_program_match; auto.
  exists p16; split. apply Tunnelingproof.transf_program_match.
  exists p17; split. apply Linearizeproof.transf_program_match; auto.
  exists p18; split. apply CleanupLabelsproof.transf_program_match; auto.
  exists p19; split. eapply partial_if_match; eauto. apply Debugvarproof.transf_program_match.
  exists p20; split. apply Stackingproof.transf_program_match; auto.
  exists tp; split. apply Asmgenproof.transf_program_match; auto.
  reflexivity.
Qed.
```

### child `c_semantic_preservation`: [`driver/Compiler.v` lines 419-432](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/driver/Compiler.v#L419-L432) ([local copy](code/driver/Compiler.v))

```coq
Theorem c_semantic_preservation:
  forall p tp,
  match_prog p tp ->
  backward_simulation (Csem.semantics p) (Asm.semantics tp).
Proof.
  intros.
  apply compose_backward_simulation with (atomic (Cstrategy.semantics p)).
  eapply sd_traces; eapply Asm.semantics_determinate.
  apply factor_backward_simulation.
  apply Cstrategy.strategy_simulation.
  apply Csem.semantics_single_events.
  eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  exact (proj2 (cstrategy_semantic_preservation _ _ H)).
Qed.
```

How the parts fit. The parent `transf_c_program_correct` is a pure composition of
two interface lemmas in one tactic line:

```
intros. apply c_semantic_preservation. apply transf_c_program_match; auto.
```

Working backward from the goal `backward_simulation (Csem.semantics p) (Asm.semantics tp)`:

1. `c_semantic_preservation` has type `match_prog p tp -> backward_simulation ...`
   (lines 419-422), so `apply` replaces the goal with the obligation `match_prog p tp`.
2. `transf_c_program_match` has type `transf_c_program p = OK tp -> match_prog p tp`
   (lines 265-268), so `apply ... ; auto` closes that obligation from the hypothesis
   `transf_c_program p = OK tp` already in context.

The lemma graph is a chain of two edges, each child's conclusion being exactly the
next child's hypothesis:

```
transf_c_program p = OK tp
   --[transf_c_program_match]-->  match_prog p tp
   --[c_semantic_preservation]-->  backward_simulation (Csem.semantics p) (Asm.semantics tp)
```

Neither `apply` leaves a residual goal, which is what makes the one-line glue
type-check. Both children are lemmas stated earlier in the same file and closed
there (`Qed` at lines 318 and 432).

Why each is a good leaf. `transf_c_program_match` is a self-contained statement
whose proof (lines 269-318) unfolds the compile chain exactly once — `transf_c_program`
and each pass are `destruct`ed, then 20 `exists pi; split. apply <pass>proof.transf_program_match`
applications close it from per-pass lemmas in the `*proof` modules (for example
`SimplExprproof.transf_program_match`, line 296). `c_semantic_preservation` is the
same shape one level up: its proof (lines 423-432) closes from the sibling
`cstrategy_semantic_preservation` (line 431), which is itself closed (lines 353-417)
from the per-pass `*_correct` lemmas. So each child is the "nearly trivial given
parents" target of survey F rule 14: the client names the interface and never
re-proves the pass chain.

## Why it is good

1. The parent closes in one line, `apply c_semantic_preservation. apply transf_c_program_match; auto`,
   without unfolding `transf_c_program` or `match_prog` (lines 450-452); the file is
   part of CompCert's main build. *(check)*
2. The authors state the plan in the comment above the theorem: "Combining the
   results above, we obtain semantic preservation for two usage scenarios of
   CompCert: compilation of a single monolithic program, and separate compilation
   of multiple source files followed by linking." (lines 434-444). *(author-statement)*
3. The glue is 1 line applying 2 lemmas, and the two children's proofs are 50 and
   10 lines (shape: `direct_lemmas = 2`, `glue_lines = 1`, `child_lines = [50, 10]`,
   `depth = 2`). *(measurement)*
4. The same two interface lemmas are reused at a second call site:
   `separate_transf_c_program_correct` applies `transf_c_program_match` (line 476)
   and `c_semantic_preservation` (line 480). *(known-use)*
5. `c_semantic_preservation` closes by `exact (proj2 (cstrategy_semantic_preservation _ _ H))`
   (line 431), so the chain of project lemmas below the main theorem reaches
   depth 2: `transf_c_program_correct -> c_semantic_preservation ->
   cstrategy_semantic_preservation`, all in `driver/Compiler.v`. *(check)*

In my opinion the detail worth copying is the discipline of stating
`transf_c_program_match` at the boundary between the executable `transf_c_program`
and its relational spec `match_prog`: it is the one place where the 20-pass chain
is unfolded, and every client below it (`transf_c_program_correct`,
`separate_transf_c_program_correct`) stays one line.

## When to use it, and when not

Use it when a goal is exactly a composition of two named facts stated at an
abstraction boundary, so that unfolding the underlying definition would be long
or would repeat work the lemmas already package. `transf_c_program` here is a
20-pass monadic chain and `match_prog` is a 20-node relational composition;
neither belongs inside the headline theorem. Avoid it when the children's
statements do not line up end to end — the two `apply`s must leave no residual
obligation — or when a child's statement is not self-contained enough to use
without further unfolding, in which case the "interface" leaks and the client is
back to unfolding.

## Consequences

The glue being only `apply` means the decomposition's sole obligation is
statement alignment: `transf_c_program_match` must end in `match_prog` and
`c_semantic_preservation` must take `match_prog`, or the two applies will not
compose. Each child then carries the real work — `transf_c_program_match` proves
the 20-pass chain and `c_semantic_preservation` builds the backward simulation —
so a reader who wants the argument must descend into those bodies and then into
the per-pass proof files. Failure mode: if a pass is added or removed,
`transf_c_program_match`'s body must be updated by hand to stay in sync with
`transf_c_program`, while the parent and `c_semantic_preservation` never change.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml (Build job runs tools/runner.sh build = make all, which compiles every Coq file including driver/Compiler.v; workflow triggers on push to master, the default branch; pinned commit 2685140bf72c959446981fb99b5e44a8975021bc) | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 2685140bf72c959446981fb99b5e44a8975021bc | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | line 451 reads 'intros. apply c_semantic_preservation. apply transf_c_program_match; auto.' — one tactic line applying the two lemmas then auto, no unfold of transf_c_program or match_prog | verifier |
| 2 | verified | lines 436-438 comment reads 'Combining the results above, we obtain semantic preservation for two usage scenarios of CompCert: compilation of a single monolithic program, and separate compilation of multiple source files followed by linking.' | verifier |
| 3 | verified | child proofs Proof. through Qed.: transf_c_program_match lines 269-318 = 50 lines; c_semantic_preservation lines 423-432 = 10 lines; glue = line 451 (1 line) applying 2 lemmas | verifier |
| 4 | verified | line 476 '... apply transf_c_program_match; auto.' and line 480 '... apply c_semantic_preservation; auto.' inside separate_transf_c_program_correct reuse both lemmas | verifier |
| 5 | verified | line 431 'exact (proj2 (cstrategy_semantic_preservation _ _ H)).' closes c_semantic_preservation; cstrategy_semantic_preservation is lines 353-417, all in driver/Compiler.v, giving depth 2 | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Opened code/driver/Compiler.v (provenance pass, byte-identical). Parent (446-452) statement matches entry verbatim; proof is the single line 'intros. apply c_semantic_preservation. apply transf_c_program_match; auto.' (451) with Qed, using exactly the two named children and no other lemma, no unfold of transf_c_program/match_prog. Both children statements (265-268, 419-422) match verbatim and their closed_by matches their bodies (transf_c_program_match: unfold/destruct then exists/split/apply per pass, reflexivity, Qed 318; c_semantic_preservation: compose_backward_simulation ... exact (proj2 (cstrategy_semantic_preservation _ _ H)), Qed 432). Shape numbers correct: direct_lemmas=2, glue_lines=1 (line 451), child_lines=[50,10] (proof 269-318 = 50 lines, 423-432 = 10 lines), depth=2 (main -> c_semantic_preservation -> cstrategy_semantic_preservation, 353-417). All 5 claims verified. Nit, not a blocker: claim 3 says 'counted over ... 265-318 and 419-432' but the 50/10 counts are proof-only 269-318/423-432; the metrics how_counted field states it correctly. | reviewer-correctness |
| generality | accept | Generality holds on all three questions. (1) Move abstracted beyond CompCert: applicability.goal_shape states 'A -> B -> C proved as apply l2; apply l1', and use_when/avoid_when are phrased generically (composition of two named facts at an abstraction boundary), with a second call site (separate_transf_c_program_correct) as known-use. (2) avoid_when and consequences are honest and specific: statement misalignment leaves a residual obligation; a non-self-contained child leaks the interface; the real work sits in the children; and the concrete failure mode (a pass added/removed forces hand-editing transf_c_program_match while parent and c_semantic_preservation never change) is named. (3) The good-leaf rationale is present: each child is self-contained and 'nearly trivial given parents' (survey F rule 14), closing mechanically from per-pass lemmas, which is exactly what a bounded filler needs. Non-blocking flag for the provenance/correctness reviewer: README cites 'survey F rule 14' but entry.json rule.f10_rule records 15 ('shallow and wide'); the two should be reconciled. | reviewer-generality |
| provenance-licence | accept | Provenance pass: file driver/Compiler.v byte-identical at pinned commit 2685140bf72c959446981fb99b5e44a8975021bc (sha256 1782a975... matches, 20511 bytes). Commit is recorded identically across entry.json, README, SOURCE.md and source.json. Licence LicenseRef-INRIA-Non-Commercial is consistent in all four and matches upstream-LICENSE text. Line permalinks verified against the local copy: parent 446-452, author comment 434-444, known-use 466-481 (transf_c_program_match at 476, c_semantic_preservation at 480). Source note records licence text and attribution. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/AbsInt/CompCert at commit `2685140bf72c959446981fb99b5e44a8975021bc`, under `LicenseRef-INRIA-Non-Commercial`; see the [source note](../../sources/compcert/SOURCE.md) for the licence text and attribution.
