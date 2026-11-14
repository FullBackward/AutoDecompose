# The event-loop invariant runsToGood_Invariant preserved by one machine step

| | |
|---|---|
| Kind | instance |
| Move | key-invariant |
| Language | rocq |
| Status | accepted |
| Source | [bedrock2](../../sources/bedrock2/SOURCE.md) at `b4ec84bc6dbb` |
| Licence | `MIT` |

## Intent

The site names the event loop's invariant `runsToGood_Invariant` — "the machine
runs to a good-ready state and is valid" — and proves that this one predicate
is preserved by a single machine step (`runsToGood_is_Invariant`). That single
statement is the idea the whole loop argument rides on: `ToplevelLoop.v`
instantiates it for a concrete loop, so an infinite loop is shown never to
reach a bad state.

## The decomposition

### parent `runsToGood_is_Invariant`: [`compiler/src/compiler/RiscvEventLoop.v` lines 104-152](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/RiscvEventLoop.v#L104-L152) ([local copy](code/compiler/src/compiler/RiscvEventLoop.v))

```coq
  Lemma runsToGood_is_Invariant: forall (st: RiscvMachineL),
      runsToGood_Invariant st -> mcomp_sat (run1 iset) st runsToGood_Invariant.
  Proof.
    unfold runsToGood_Invariant.
    intros m [R V].
    eapply run1_get_sane with (P := (fun m => runsTo (mcomp_sat (run1 iset)) m (goodReadyState false))).
    1, 3: eauto. revert R.
    eapply runsTo_safe1_inv; cycle 1.
    - intros. eapply body_correct; assumption.
    - intros.
      (* this is the loop verification code: *)
      eapply runsToStep. {
        specialize (goodReadyState_implies_jump_back_instr _ H).
        destruct goodReadyState_implies_jump_back_instr. simp.
        specialize (goodReadyState_checks_PC _ _ H). subst pc_end.
        eapply run_Jal0; try eauto.
        unfold program, array.
        rewrite goodReadyState_checks_PC.
        solve [ ecancel ].
      }
      simpl. intros. simp.
      destruct_RiscvMachine state.
      destruct_RiscvMachine mid.
      subst.
      apply runsToDone.
      ssplit; try assumption; cbn;
        ring_simplify (Zmod.add (Zmod.sub pc_start (bits.of_Z width jump)) (bits.of_Z width jump));
        try reflexivity.
      specialize (goodReadyState_checks_PC _ _ H). simpl in *. subst state_pc.
      eapply goodReadyState_preserved_by_jump_back in H.
      + simpl in H.
        match goal with
        | |- ?G => let T := type of H in replace G with T; [exact H|]
        end.
        repeat f_equal.
        all: try solve_word_eq.
        destruct getTrace; simpl.
        { instantiate (1 := [_;_]). reflexivity. }
        reflexivity.
      + simpl.
        match goal with
        | H: valid_machine ?m1 |- valid_machine ?m2 => replace m2 with m1; [exact H|]
        end.
        f_equal. f_equal; try solve_word_eq. destruct getTrace; reflexivity.
    - intros state [C1 C2].
      apply goodReadyState_checks_PC in C1.
      apply goodReadyState_checks_PC in C2.
      congruence.
  Qed.
```

### context `runsToGood_Invariant`: [`compiler/src/compiler/RiscvEventLoop.v` lines 99-100](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/RiscvEventLoop.v#L99-L100) ([local copy](code/compiler/src/compiler/RiscvEventLoop.v))

```coq
  Definition runsToGood_Invariant(m: RiscvMachineL): Prop :=
    runsTo (mcomp_sat (run1 iset)) m (goodReadyState false) /\ valid_machine m.
```

### child `run1_get_sane`: [`compiler/src/compiler/GoFlatToRiscv.v` lines 79-97](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/GoFlatToRiscv.v#L79-L97) ([local copy](code/compiler/src/compiler/GoFlatToRiscv.v))

```coq
  Lemma run1_get_sane: forall iset (P Q: RiscvMachineL -> Prop) mach,
      valid_machine mach ->
      mcomp_sat (run1 iset) mach P ->
      (forall mach': RiscvMachineL,
          (exists diff, mach'.(getLog) = diff ++ mach.(getLog)) ->
          valid_machine mach' ->
          P mach' ->
          Q mach') ->
      mcomp_sat (run1 iset) mach Q.
  Proof.
    intros.
    pose proof run1_sane as A.
    unfold mcomp_sane in A.
    specialize A with (1 := H) (2 := H0).
    apply proj2 in A.
    eapply mcomp_sat_weaken. 2: exact A. cbv beta.
    intros. destruct H2 as ((? & (diff & ?)) & ?).
    eapply H1; eauto.
  Qed.
```

### child `runsTo_safe1_inv`: [`compiler/src/compiler/ForeverSafe.v` lines 108-120](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/ForeverSafe.v#L108-L120) ([local copy](code/compiler/src/compiler/ForeverSafe.v))

```coq
  Lemma runsTo_safe1_inv: forall (st: RiscvMachineL),
      runsTo (mcomp_sat (run1 iset)) st safe1 ->
      mcomp_sat (run1 iset) st (fun st' => runsTo (mcomp_sat (run1 iset)) st' safe1).
  Proof.
    intros st R. destruct R.
    - pose proof (run_1_2 _ H) as P. inversion P.
      + exfalso. eapply exclusive; eauto.
      + eapply mcomp_sat_weaken. 2: eassumption.
        intros. specialize (H1 _ H2).
        eapply run_pong. assumption.
    - eapply mcomp_sat_weaken. 2: eassumption.
      intros. eapply H0. assumption.
  Qed.
```

### child `run_Jal0`: [`compiler/src/compiler/RunInstruction.v` lines 363-374](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/RunInstruction.v#L363-L374) ([local copy](code/compiler/src/compiler/RunInstruction.v))

```coq
  Lemma run_Jal0: run_Jal0_spec.
  Proof.
    repeat intro.
    inline_iff1.
    get_run1_valid_for_free.
    match goal with
    | H: (?P * ?Q * ?R)%sep ?m |- _ =>
      assert ((P * (Q * R))%sep m) as A by ecancel_assumption
    end.
    destruct (invert_ptsto_program1 iset A) as (DE & ?).
    t0.
  Qed.
```

How the parts fit. The parent `runsToGood_is_Invariant` (RiscvEventLoop.v
104-152) unfolds `runsToGood_Invariant`, then threads the one-step argument
through two project lemmas, two constructors of `runsTo`, and the hypotheses of
this section. The dependency graph, in text:

```
runsToGood_is_Invariant
├── run1_get_sane          (RiscvEventLoop.v:109)  — sanity of the step
├── runsTo_safe1_inv       (RiscvEventLoop.v:111)  — one-step preservation
│   └── run_pong           (ForeverSafe.v:117)     — its own sibling helper
├── runsToStep             (RiscvEventLoop.v:115)  — constructor: unfold one step
│   └── run_Jal0           (RiscvEventLoop.v:119)  — execute the jump-back `Jal`
└── runsToDone             (RiscvEventLoop.v:128)  — constructor: close the relation
```

The move is the invariant, so the load-bearing step is `runsTo_safe1_inv`
(line 111). In `ForeverSafe.v` that lemma is stated over section variables
`safe1`/`safe2` with hypotheses `exclusive`, `run_1_2` and `run_2_1`; the glue
instantiates `safe1 := goodReadyState false` (ready at the loop start) and
`safe2 := goodReadyState true` (ready at the jump-back point), then discharges
the three obligations:

- `run_1_2` — the loop body — closes by the hypothesis `body_correct`
  (line 112).
- `run_2_1` — the jump back — is the "loop verification code" (113-147):
  `runsToStep` (115) unfolds one step of `runsTo`, `run_Jal0` (119) executes
  the `Jal Register0 jump` instruction, `runsToDone` (128) closes the relation
  once the state is good, and `goodReadyState_preserved_by_jump_back` (133)
  restores `goodReadyState false`.
- `exclusive` — a state cannot be both at the start and the end — closes by
  `goodReadyState_checks_PC` plus `congruence` (148-151).

Before all of that, `run1_get_sane` (109) is applied so that the `run1` step
carries the `valid_machine` and log-prefix sanity that `run1_sane` (an external
riscv-coq fact) guarantees.

Why each child is a good leaf:

- `run1_get_sane` is a self-contained restatement of `run1_sane`'s conclusion
  that closes by `proj2` of `run1_sane` and `mcomp_sat_weaken`; it needs nothing
  from the parent.
- `runsTo_safe1_inv` case-splits on the `runsTo` hypothesis and closes the two
  cases with its sibling `run_pong` and `mcomp_sat_weaken`; it is the reusable
  "one step preserves the invariant" lemma.
- `run_Jal0` is one of a family of per-instruction execution lemmas in
  `RunInstruction.v`; it closes by the shared tactic `t0` after decoding the
  instruction (`invert_ptsto_program1`), so it needs nothing from the loop.
- `runsToStep` and `runsToDone` are not project lemmas but the two constructors
  of the inductive `runsTo` relation in the external riscv-coq library
  (`riscv.Utility.runsToNonDet` / `riscv.Platform.Run`); the glue cites them
  exactly to step and to close the relation.

## Why it is good

1. The glue cites `runsTo_safe1_inv`, the one-step preservation lemma, so the
   parent's proof genuinely hangs off the invariant child rather than doing the
   step argument itself (check; [`RiscvEventLoop.v` lines 104-152](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/RiscvEventLoop.v#L104-L152)).
2. The parent proof closes with no `sorry`/`admit`/`Admitted` in lines 104-152,
   so the invariant preservation is proved, not axiomatised (check; same range).
3. The glue is 49 lines; the three project children are 19, 13 and 12 lines;
   five named lemmas are used directly, and the longest checked chain is
   `runsToGood_is_Invariant -> runsTo_safe1_inv -> run_pong` (depth 2)
   (measurement; [`RiscvEventLoop.v` 104-152](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/RiscvEventLoop.v#L104-L152),
   [`GoFlatToRiscv.v` 79-97](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/GoFlatToRiscv.v#L79-L97),
   [`ForeverSafe.v` 108-120](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/ForeverSafe.v#L108-L120),
   [`RunInstruction.v` 363-374](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/RunInstruction.v#L363-L374)).
4. The invariant is reused downstream, which is the point of naming it:
   `ToplevelLoop.v` defines `ll_inv := runsToGood_Invariant ll_good iset`
   (line 160) and proves `ll_inv_is_invariant` by instantiating
   `runsToGood_is_Invariant` (lines 418-422) (known-use;
   [`ToplevelLoop.v` 160, 418-422](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/ToplevelLoop.v#L160)).

In my opinion the detail worth copying is the ping-pong shape: the invariant is
`runsTo ... (goodReadyState false)`, and the one-step lemma is stated over two
"sides" (`safe1`/`safe2`) with `run_1_2` and `run_2_1` hypotheses, so that a
single preservation lemma serves both the loop body and the jump back.

## When to use it, and when not

Use it when the property to preserve has a natural one-step formulation over a
"eventually reaches P" relation — here `runsToGood_Invariant` is `runsTo ... 
(goodReadyState false)` plus `valid_machine` — and the per-instruction behaviour
is already proved elsewhere (`run_Jal0` and its siblings in `RunInstruction.v`).
Name the invariant, prove one step preserves it, and let the downstream loop
theorem instantiate it (`ToplevelLoop`). This is the
"strengthen the hypothesis" idea of survey F §10 rule 6, applied to a stepwise
rather than an inductive argument (my reading; the survey has no rule that names
the loop invariant as such, so `entry.json` records `rule: none`).

Avoid it when the invariant itself needs an induction over the loop body (then
that induction, not the one-step statement, is the real content), when the
per-instruction execution lemmas do not exist, or when the machine step cannot
be expressed as a single `run1` transition.

## Consequences

The move isolates the loop argument into three parts: the invariant predicate,
the one-step preservation lemma, and the per-case execution lemmas. Obligations
it creates: the two cases of a step must be distinguished (loop body vs
jump-back, via the `done` flag and `goodReadyState_checks_PC`), and the
preservation proof must discharge `valid_machine` on both the step and the stop
(`run1_get_sane` and `runsToDone`). Known failure modes: an invariant that is
too weak to be preserved (the proof then gets stuck at
`goodReadyState_preserved_by_jump_back`), or a step lemma whose side conditions
(`jimm20 mod 4 = 0`, footprint subset) the glue cannot discharge.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/coq-docker.yml (and debian.yml, alpine.yml) run 'make -k' at the repo root on default branch master; the top-level Makefile 'all' target builds 'compiler_ex' -> 'make -C compiler', which compiles compiler/src/compiler/RiscvEventLoop.v. Pinned commit b4ec84bc is on master (2 commits behind master tip fdf045fd). | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: run1_get_sane@compiler/src/compiler/RiscvEventLoop.v:109, runsTo_safe1_inv@compiler/src/compiler/RiscvEventLoop.v:111, run_Jal0@compiler/src/compiler/RiscvEventLoop.v:119, runsToStep@compiler/src/compiler/RiscvEventLoop.v:115, runsToDone@compiler/src/compiler/RiscvEventLoop.v:128; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 5 file(s) byte-identical at b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, runsTo_safe1_inv) -> cites: runsTo_safe1_inv occurs at compiler/src/compiler/RiscvEventLoop.v:111 | check_claims.py |
| 2 | verified | no_sorry(compiler/src/compiler/RiscvEventLoop.v, 104-152) -> no_sorry: none of admit, Admitted, Axiom, axiom in compiler/src/compiler/RiscvEventLoop.v:104-152 | check_claims.py |
| 3 | verified | Checked copied code: parent glue RiscvEventLoop.v 104-152 = 49 lines (Lemma at 104, Qed at 152); run1_get_sane GoFlatToRiscv.v 79-97 = 19 lines; runsTo_safe1_inv ForeverSafe.v 108-120 = 13 lines; run_Jal0 RunInstruction.v 363-374 = 12 lines. Glue cites five named lemmas: run1_get_sane (L108), runsTo_safe1_inv (L110), runsToStep (L115), run_Jal0 (L119), runsToDone (L128). runsTo_safe1_inv cites run_pong at ForeverSafe.v L117, and run_pong is at 78-87. Depth-2 chain confirmed. | verifier |
| 4 | refuted | ToplevelLoop parts check out in copied code: L160 'Definition ll_inv: MetricRiscvMachine -> Prop := runsToGood_Invariant ll_good iset.' and L418-422 'Lemma ll_inv_is_invariant' with 'eapply runsToGood_is_Invariant'. But the end2end part does not: End2EndPipeline.v (fetched raw at b4ec84bc) line ~315 is 'specialize_first P1 (ll_inv compile_ext_call ml spec).' — ll_inv applied to three args (compile_ext_call ml spec), and CompilerInvariant.v uses 'll_inv compile_ext_call ml spec st'. That 3-argument ll_inv is not ToplevelLoop's 1-argument 'runsToGood_Invariant ll_good iset', so 'end2end threads the same ll_inv' is wrong. | verifier |
| 5 | verified | Checked copied ToplevelLoop.v: line 160 'Definition ll_inv: MetricRiscvMachine -> Prop := runsToGood_Invariant ll_good iset.' and line 418 'Lemma ll_inv_is_invariant: forall (st: MetricRiscvMachine), ll_inv st -> GoFlatToRiscv.mcomp_sat (run1 iset) st ll_inv.' whose proof eapply's runsToGood_is_Invariant at line 422. Both match the claim exactly. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent runsToGood_is_Invariant (RiscvEventLoop.v 104-152) matches its entry statement and closes with Qed (no sorry/admit). Glue cites exactly five named lemmas/constructors: run1_get_sane@109, runsTo_safe1_inv@111, runsToStep@115, run_Jal0@119, runsToDone@128; the other cited names (body_correct, goodReadyState_*_checks_PC/preserved_by_jump_back/implies_jump_back_instr) are Section Hypotheses (RiscvEventLoop.v 60-95), not lemmas, so they are correctly not children. All three project-child statements and closing methods match code: run1_get_sane GoFlatToRiscv.v 79-97 (pose proof run1_sane; proj2; eapply mcomp_sat_weaken), runsTo_safe1_inv ForeverSafe.v 108-120 (destruct R; done case run_1_2+run_pong, step case mcomp_sat_weaken; the earlier 89-105 attempt ends Succeed Qed. Abort. and is outside the cited site), run_Jal0 RunInstruction.v 363-374 (get_run1_valid_for_free; invert_ptsto_program1; t0). Shape numbers correct: glue_lines 49 (104-152), child_lines [19,13,12] (79-97, 108-120, 363-374), direct_lemmas 5, depth 2 via runsTo_safe1_inv->run_pong (ForeverSafe.v 78-87, cited at 117). | reviewer-correctness |
| generality | accept | Move generalises beyond the example: 'When to use it' frames it as a natural one-step formulation over an 'eventually reaches P' relation with per-instruction lemmas already proved elsewhere, and avoid_when gives three concrete negative conditions (invariant needs induction over the loop body; per-instruction lemmas absent; step not expressible as a single run1). Consequences are honest and specific, naming code-tied obligations (discharge valid_machine on step and stop) and failure modes (stuck at goodReadyState_preserved_by_jump_back; jimm20 mod 4 = 0 / footprint subset). 'Why each child is a good leaf' answers the bounded-prover question: each leaf is self-contained, needs nothing from the parent, and closes by a small finite set of facts (proj2+mcomp_sat_weaken; case-split+run_pong+mcomp_sat_weaken; decode+t0). Honesty: records rule: none and labels the survey-F mapping as 'my reading' (opinion), not a claim. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are consistent and traceable. check_provenance.py passes: 5 files byte-identical at b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b. All permalinks pin that commit with correct paths; line anchors verified against the copied files via sed: RiscvEventLoop.v 99-100 (context) and 104-152 (parent), GoFlatToRiscv.v 79-97, ForeverSafe.v 108-120, RunInstruction.v 363-374, ToplevelLoop.v 160 and 418-422. Licence MIT is consistent across entry.json, README, source.json and upstream-LICENSE (MIT text). bedrock2/SOURCE.md matches the entry's commit and licence. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/mit-plv/bedrock2 at commit `b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b`, under `MIT`; see the [source note](../../sources/bedrock2/SOURCE.md) for the licence text and attribution.
