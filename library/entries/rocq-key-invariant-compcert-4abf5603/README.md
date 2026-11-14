# Key invariant sound_state prog for CompCert's constant-propagation forward simulation

| | |
|---|---|
| Kind | instance |
| Move | key-invariant |
| Language | rocq |
| Status | accepted |
| Source | [compcert](../../sources/compcert/SOURCE.md) at `2685140bf72c` |
| Licence | `LicenseRef-INRIA-Non-Commercial` |
| Licence recorded | 2026-11-14T10:05:50Z |

## Intent

The constant-propagation pass is proved correct by one forward simulation. The
glue applies the `Forward_simulation` record constructor and fills its five
fields with six already-proved lemmas, threading the analysis invariant
`sound_state prog` (established by `sound_initial`, preserved by `sound_step`)
alongside the simulation relation `match_states`.

## The decomposition

### parent `transf_program_correct`: [`backend/Constpropproof.v` lines 607-623](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/backend/Constpropproof.v#L607-L623) ([local copy](code/backend/Constpropproof.v))

```coq
Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  apply Forward_simulation with lt (fun n s1 s2 => sound_state prog s1 /\ match_states n s1 s2); constructor.
- apply lt_wf.
- simpl; intros. exploit transf_initial_states; eauto. intros (n & st2 & A & B).
  exists n, st2; intuition. eapply sound_initial; eauto.
- simpl; intros. destruct H. eapply transf_final_states; eauto.
- simpl; intros. destruct H0.
  assert (sound_state prog s1') by (eapply sound_step; eauto).
  fold ge; fold tge.
  exploit transf_step_correct; eauto.
  intros [ [n2 [s2' [A B]]] | [n2 [A [B C]]]].
  exists n2; exists s2'; split; auto. left; apply plus_one; auto.
  exists n2; exists s2; split; auto. right; split; auto. subst t; apply star_refl.
- apply senv_preserved.
Qed.
```

### child `transf_initial_states`: [`backend/Constpropproof.v` lines 581-595](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/backend/Constpropproof.v#L581-L595) ([local copy](code/backend/Constpropproof.v))

```coq
Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists n, exists st2, initial_state tprog st2 /\ match_states n st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated; eauto. intros (cu & FIND & LINK).
  exists O; exists (Callstate nil (transf_fundef (romem_for cu) f) nil m0); split.
  econstructor; eauto.
  apply (Genv.init_mem_match TRANSL); auto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  symmetry; eapply match_program_main; eauto.
  rewrite <- H3. apply sig_function_translated.
  constructor. auto. constructor. constructor. apply Mem.extends_refl.
Qed.
```

### child `transf_final_states`: [`backend/Constpropproof.v` lines 597-602](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/backend/Constpropproof.v#L597-L602) ([local copy](code/backend/Constpropproof.v))

```coq
Lemma transf_final_states:
  forall n st1 st2 r,
  match_states n st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. inv RES. constructor.
Qed.
```

### child `transf_step_correct`: [`backend/Constpropproof.v` lines 350-579](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/backend/Constpropproof.v#L350-L579) ([local copy](code/backend/Constpropproof.v))

```coq
Lemma transf_step_correct:
  forall s1 t s2,
  step ge s1 t s2 ->
  forall n1 s1' (SS: sound_state prog s1) (MS: match_states n1 s1 s1'),
  (exists n2, exists s2', step tge s1' t s2' /\ match_states n2 s2 s2')
  \/ (exists n2, n2 < n1 /\ t = E0 /\ match_states n2 s2 s1')%nat.
Proof.
  induction 1; intros; inv MS; try InvSoundState; try (inv PC; try congruence).

- (* Inop, preserved *)
  rename pc'0 into pc. TransfInstr; intros.
  left; econstructor; econstructor; split.
  eapply exec_Inop; eauto.
  eapply match_states_succ; eauto.

- (* Inop, skipped over *)
  assert (s0 = pc') by congruence. subst s0.
  right; exists n; split. lia. split. auto.
  apply match_states_intro; auto.

- (* Iop *)
  rename pc'0 into pc. TransfInstr.
  set (a := eval_static_operation op (aregs ae args)).
  set (ae' := AE.set res a ae).
  assert (VMATCH: vmatch bc v a) by (eapply eval_static_operation_sound; eauto with va).
  assert (MATCH': ematch bc (rs#res <- v) ae') by (eapply ematch_update; eauto).
  destruct (const_for_result a) as [cop|] eqn:?; intros.
+ (* constant is propagated *)
  exploit const_for_result_correct; eauto. intros (v' & A & B).
  left; econstructor; econstructor; split.
  eapply exec_Iop; eauto.
  apply match_states_intro; auto.
  eapply match_successor; eauto.
  apply set_reg_lessdef; auto.
+ (* operator is strength-reduced *)
  assert(OP:
     let (op', args') := op_strength_reduction op args (aregs ae args) in
     exists v',
        eval_operation ge (Vptr sp0 Ptrofs.zero) op' rs ## args' m = Some v' /\
        Val.lessdef v v').
  { eapply op_strength_reduction_correct with (ae := ae); eauto with va. }
  destruct (op_strength_reduction op args (aregs ae args)) as [op' args'].
  destruct OP as [v' [EV' LD']].
  assert (EV'': exists v'', eval_operation ge (Vptr sp0 Ptrofs.zero) op' rs'##args' m' = Some v'' /\ Val.lessdef v' v'').
  { eapply eval_operation_lessdef; eauto. eapply regs_lessdef_regs; eauto. }
  destruct EV'' as [v'' [EV'' LD'']].
  left; econstructor; econstructor; split.
  eapply exec_Iop; eauto.
  erewrite eval_operation_preserved. eexact EV''. exact symbols_preserved.
  apply match_states_intro; auto.
  eapply match_successor; eauto.
  apply set_reg_lessdef; auto. eapply Val.lessdef_trans; eauto.

- (* Iload *)
  rename pc'0 into pc. TransfInstr.
  set (aa := eval_static_addressing addr (aregs ae args)).
  assert (VM1: vmatch bc a aa) by (eapply eval_static_addressing_sound; eauto with va).
  set (av := loadv chunk (romem_for cu) am aa).
  assert (VM2: vmatch bc v av) by (eapply loadv_sound; eauto).
  destruct (const_for_result av) as [cop|] eqn:?; intros.
+ (* constant-propagated *)
  exploit const_for_result_correct; eauto. intros (v' & A & B).
  left; econstructor; econstructor; split.
  eapply exec_Iop; eauto.
  eapply match_states_succ; eauto.
  apply set_reg_lessdef; auto.
+ (* strength-reduced *)
  assert (ADDR:
     let (addr', args') := addr_strength_reduction addr args (aregs ae args) in
     exists a',
        eval_addressing ge (Vptr sp0 Ptrofs.zero) addr' rs ## args' = Some a' /\
        Val.lessdef a a').
  { eapply addr_strength_reduction_correct with (ae := ae); eauto with va. }
  destruct (addr_strength_reduction addr args (aregs ae args)) as [addr' args'].
  destruct ADDR as (a' & P & Q).
  exploit eval_addressing_lessdef. eapply regs_lessdef_regs; eauto. eexact P.
  intros (a'' & U & V).
  assert (W: eval_addressing tge (Vptr sp0 Ptrofs.zero) addr' rs'##args' = Some a'').
  { rewrite <- U. apply eval_addressing_preserved. exact symbols_preserved. }
  exploit Mem.loadv_extends. eauto. eauto. apply Val.lessdef_trans with a'; eauto.
  intros (v' & X & Y).
  left; econstructor; econstructor; split.
  eapply exec_Iload; eauto.
  eapply match_states_succ; eauto. apply set_reg_lessdef; auto.

- (* Istore *)
  rename pc'0 into pc. TransfInstr.
  assert (ADDR:
     let (addr', args') := addr_strength_reduction addr args (aregs ae args) in
     exists a',
        eval_addressing ge (Vptr sp0 Ptrofs.zero) addr' rs ## args' = Some a' /\
        Val.lessdef a a').
  { eapply addr_strength_reduction_correct with (ae := ae); eauto with va. }
  destruct (addr_strength_reduction addr args (aregs ae args)) as [addr' args'].
  destruct ADDR as (a' & P & Q).
  exploit eval_addressing_lessdef. eapply regs_lessdef_regs; eauto. eexact P.
  intros (a'' & U & V).
  assert (W: eval_addressing tge (Vptr sp0 Ptrofs.zero) addr' rs'##args' = Some a'').
  { rewrite <- U. apply eval_addressing_preserved. exact symbols_preserved. }
  exploit Mem.storev_extends. eauto. eauto. apply Val.lessdef_trans with a'; eauto. apply REGS.
  intros (m2' & X & Y).
  left; econstructor; econstructor; split.
  eapply exec_Istore; eauto.
  eapply match_states_succ; eauto.

- (* Icall *)
  rename pc'0 into pc.
  exploit transf_ros_correct; eauto. intros (cu' & FIND & LINK').
  TransfInstr; intro.
  left; econstructor; econstructor; split.
  eapply exec_Icall; eauto. apply sig_function_translated; auto.
  constructor; auto. constructor; auto.
  econstructor; eauto.
  apply regs_lessdef_regs; auto.

- (* Itailcall *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  exploit transf_ros_correct; eauto. intros (cu' & FIND & LINK').
  TransfInstr; intro.
  left; econstructor; econstructor; split.
  eapply exec_Itailcall; eauto. apply sig_function_translated; auto.
  constructor; auto.
  apply regs_lessdef_regs; auto.

- (* Ibuiltin *)
  rename pc'0 into pc. TransfInstr; intros.
Opaque builtin_strength_reduction.
  set (dfl := Ibuiltin ef (builtin_strength_reduction ae ef args) res pc') in *.
  set (rm := romem_for cu) in *.
  assert (DFL: (fn_code (transf_function rm f))!pc = Some dfl ->
          exists (n2 : nat) (s2' : state),
            step tge
             (State s' (transf_function rm f) (Vptr sp0 Ptrofs.zero) pc rs' m'0) t s2' /\
            match_states n2
             (State s f (Vptr sp0 Ptrofs.zero) pc' (regmap_setres res vres rs) m') s2').
  {
    exploit builtin_strength_reduction_correct; eauto. intros (vargs' & P & Q).
    exploit (@eval_builtin_args_lessdef _ ge (fun r => rs#r) (fun r => rs'#r)).
    apply REGS. eauto. eexact P.
    intros (vargs'' & U & V).
    exploit external_call_mem_extends; eauto.
    intros (v' & m2' & A & B & C & D).
    econstructor; econstructor; split.
    eapply exec_Ibuiltin; eauto.
    eapply eval_builtin_args_preserved. eexact symbols_preserved. eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    eapply match_states_succ; eauto.
    apply set_res_lessdef; auto.
  }
  destruct ef; auto.
  destruct res; auto.
  destruct (lookup_builtin_function name sg) as [bf|] eqn:LK; auto.
  destruct (eval_static_builtin_function ae am rm bf args) as [a|] eqn:ES; auto.
  destruct (const_for_result a) as [cop|] eqn:CR; auto.
  clear DFL. simpl in H1; red in H1; rewrite LK in H1; inv H1.
  exploit const_for_result_correct; eauto. 
  eapply eval_static_builtin_function_sound; eauto.
  intros (v' & A & B).
  left; econstructor; econstructor; split.
  eapply exec_Iop; eauto.
  eapply match_states_succ; eauto.
  apply set_reg_lessdef; auto.
- (* Icond, preserved *)
  rename pc'0 into pc. TransfInstr.
  set (ac := eval_static_condition cond (aregs ae args)).
  assert (C: cmatch (eval_condition cond rs ## args m) ac)
  by (eapply eval_static_condition_sound; eauto with va).
  rewrite H0 in C.
  generalize (cond_strength_reduction_correct bc ae rs m EM cond args (aregs ae args) (eq_refl _)).
  destruct (cond_strength_reduction cond args (aregs ae args)) as [cond' args'].
  intros EV1 TCODE.
  left; exists O; exists (State s' (transf_function (romem_for cu) f) (Vptr sp0 Ptrofs.zero) (if b then ifso else ifnot) rs' m'); split.
  destruct (resolve_branch ac) eqn: RB.
  assert (b0 = b) by (eapply resolve_branch_sound; eauto). subst b0.
  destruct b; eapply exec_Inop; eauto.
  eapply exec_Icond; eauto.
  eapply eval_condition_lessdef with (vl1 := rs##args'); eauto. eapply regs_lessdef_regs; eauto. congruence.
  eapply match_states_succ; eauto.

- (* Icond, skipped over *)
  rewrite H1 in H; inv H.
  right; exists n; split. lia. split. auto.
  econstructor; eauto.

- (* Ijumptable *)
  rename pc'0 into pc.
  assert (A: (fn_code (transf_function (romem_for cu) f))!pc = Some(Ijumptable arg tbl)
             \/ (fn_code (transf_function (romem_for cu) f))!pc = Some(Inop pc')).
  { TransfInstr.
    destruct (areg ae arg) eqn:A; auto.
    generalize (EM arg). fold (areg ae arg); rewrite A.
    intros V; inv V. replace n0 with n by congruence.
    rewrite H1. auto. }
  assert (rs'#arg = Vint n).
  { generalize (REGS arg). rewrite H0. intros LD; inv LD; auto. }
  left; exists O; exists (State s' (transf_function (romem_for cu) f) (Vptr sp0 Ptrofs.zero) pc' rs' m'); split.
  destruct A. eapply exec_Ijumptable; eauto. eapply exec_Inop; eauto.
  eapply match_states_succ; eauto.

- (* Ireturn *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  left; exists O; exists (Returnstate s' (regmap_optget or Vundef rs') m2'); split.
  eapply exec_Ireturn; eauto. TransfInstr; auto.
  constructor; auto.
  destruct or; simpl; auto.

- (* internal function *)
  exploit Mem.alloc_extends. eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros [m2' [A B]].
  simpl. unfold transf_function.
  left; exists O; econstructor; split.
  eapply exec_function_internal; simpl; eauto using Val.has_argtype_list_lessdef.
  simpl. econstructor; eauto.
  constructor.
  apply init_regs_lessdef; auto.

- (* external function *)
  exploit external_call_mem_extends; eauto.
  intros [v' [m2' [A [B [C D]]]]].
  simpl. left; econstructor; econstructor; split.
  eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto.

- (* return *)
  inv H4. inv H1.
  left; exists O; econstructor; split.
  eapply exec_return; eauto.
  econstructor; eauto. constructor. apply set_reg_lessdef; auto.
Qed.
```

### child `sound_initial`: [`backend/ValueAnalysis.v` lines 1896-1914](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/backend/ValueAnalysis.v#L1896-L1914) ([local copy](code/backend/ValueAnalysis.v))

```coq
Theorem sound_initial:
  forall prog st, initial_state prog st -> sound_state prog st.
Proof.
  destruct 1.
  exploit initial_mem_matches; eauto. intros (bc & GE & BELOW & NOSTACK & RM & VALID).
  constructor; intros. apply sound_call_state with bc.
- constructor.
- simpl; tauto.
- apply RM; auto.
- apply mmatch_inj_top with m0.
  replace (inj_of_bc bc) with (Mem.flat_inj (Mem.nextblock m0)).
  eapply Genv.initmem_inject; eauto.
  symmetry; apply extensionality; unfold Mem.flat_inj; intros x.
  destruct (plt x (Mem.nextblock m0)).
  apply inj_of_bc_valid; auto.
  unfold inj_of_bc. erewrite bc_below_invalid; eauto.
- exact GE.
- exact NOSTACK.
Qed.
```

### child `sound_step`: [`backend/ValueAnalysis.v` lines 1530-1534](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/backend/ValueAnalysis.v#L1530-L1534) ([local copy](code/backend/ValueAnalysis.v))

```coq
Theorem sound_step:
  forall st t st', RTL.step ge st t st' -> sound_state st -> sound_state st'.
Proof.
  intros. inv H0. constructor; intros. eapply sound_step_base; eauto.
Qed.
```

### child `senv_preserved`: [`backend/Constpropproof.v` lines 49-51](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/backend/Constpropproof.v#L49-L51) ([local copy](code/backend/Constpropproof.v))

```coq
Lemma senv_preserved:
  Senv.equiv ge tge.
Proof. exact (Genv.senv_match TRANSL). Qed.
```

### context `sound_state`: [`backend/ValueAnalysis.v` lines 1525-1528](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/backend/ValueAnalysis.v#L1525-L1528) ([local copy](code/backend/ValueAnalysis.v))

```coq
Inductive sound_state: state -> Prop :=
  | sound_state_intro: forall st,
      (forall cunit, linkorder cunit prog -> sound_state_base cunit ge st) ->
      sound_state st.
```

How the parts fit. The glue (the parent proof, lines 610-622) builds a
`Forward_simulation` over the invariant `fun n s1 s2 => sound_state prog s1 /\
match_states n s1 s2` and then fills the record's five fields:

- **order well-foundedness** — closed by `apply lt_wf`, a standard-library fact,
  not a child.
- **match initial states** (612-613) — `exploit transf_initial_states` produces
  the matched initial target state, then `eapply sound_initial` adds the
  invariant to it.
- **match final states** (614) — `eapply transf_final_states`.
- **the simulation diagram** (615-621) — first `sound_step` gives
  `sound_state prog s1'` (the invariant is preserved), then
  `transf_step_correct` yields a disjunction of two cases, closed respectively
  with `plus_one` and `star_refl`.
- **symbol/senv preservation** (622) — `apply senv_preserved`.

The lemma graph (which lemma uses which, within the two copied files):

```
transf_program_correct
  -> transf_initial_states  -> function_ptr_translated, symbols_preserved,
                               match_program_main, sig_function_translated
  -> sound_initial          -> initial_mem_matches, sound_call_state
  -> transf_final_states    -> (inversion of match_states / final_state)
  -> sound_step             -> sound_step_base
  -> transf_step_correct    -> match_states_succ, match_states_intro,
                               const_for_result_correct, transf_ros_correct,
                               sig_function_translated, builtin_strength_reduction_correct,
                               match_successor, init_regs_lessdef, senv_preserved, ...
  -> senv_preserved         -> Genv.senv_match
```

Why each child is a good leaf:

- `senv_preserved` (3 lines) is a one-line library fact (`Genv.senv_match`),
  self-contained.
- `transf_final_states` (6 lines) closes by inversion of `match_states` and
  `final_state`; self-contained.
- `transf_initial_states` (15 lines) uses only the per-pass translation lemmas
  proved just above it in the same file; self-contained.
- `transf_step_correct` (230 lines) is the big simulation lemma. It takes
  `sound_state prog s1` as a *hypothesis* (line 353), so it never re-proves the
  invariant; it closes by induction on the source step, one bullet per RTL
  instruction, from lemmas of this file plus imported soundness lemmas.
- `sound_initial` (19 lines) and `sound_step` (5 lines) are the two halves of
  the invariant argument, stated once in `ValueAnalysis.v` and reused by every
  pass. `sound_step` is a one-liner dispatching to `sound_step_base`, the real
  ~260-line case analysis on instructions; `sound_initial` dispatches to
  `sound_call_state`.

## Why it is good

1. `transf_program_correct` is declared at `backend/Constpropproof.v` lines
   607-623 (check, `declared`).
2. `backend/Constpropproof.v` lines 49-623 contain no
   sorry/admit/Admitted/axiom token — the parent and all four of its
   same-file children end in `Qed` (check, `no_sorry`).
3. The theorem-scale shape is 6 direct lemmas, depth 3, glue 17 lines, child
   proof lengths `[15, 6, 230, 19, 5, 3]`; the depth chain
   `transf_program_correct -> transf_step_correct -> transf_ros_correct ->
   functions_translated` is all in `backend/Constpropproof.v` (measurement).
4. The authors describe the argument as a simulation carried by an invariant
   between source and target states: "The proof of semantic preservation is a
   simulation argument based on 'option' diagrams of the following form" and
   "the state [st1] must match its compile-time approximations at the current
   program point" (author-statement, lines 258-282).
5. `sound_initial` and `sound_step`, declared once in `ValueAnalysis.v`, are
   reused by the CSE pass: `CSEproof.v`'s `transf_program_correct` applies
   `sound_initial` (line 1579) and `sound_step` (lines 1586, 1589-1590) over
   the invariant `match_states s1 s2 /\ sound_state prog s1` (known-use,
   lines 1572-1591).

In my opinion the detail worth copying is the *separation of the invariant from
the diagram*: `transf_step_correct` takes `sound_state prog s1` as a hypothesis
instead of proving it, so the 230-line simulation lemma and the invariant's
preservation lemma can be developed and rechecked independently.

## When to use it, and when not

Use it when the goal is a simulation between two programs (or two transition
systems) and one predicate carries the whole argument: it is established on the
initial states and preserved by every step, while the mechanical parts
(initial/final/step matching, symbol preservation) are already named lemmas
whose statements line up with the record fields. The invariant should be
statable once, at the state level, and separable from the step argument.
Avoid it when no single invariant suffices (the step case needs a different
strengthening per instruction), when the step-preservation proof cannot be
split off from the simulation diagram, or when the invariant is not compatible
with the simulation relation so that the single `Forward_simulation`
application does not go through.

## Consequences

The move creates one invariant obligation that the glue must thread through the
whole simulation: `sound_state prog` must hold on the initial state
(`sound_initial`) and be preserved by each step (`sound_step`), carried
alongside `match_states` through the `Forward_simulation` record. The record
forces five field proofs, and the simulation diagram must handle both cases of
`transf_step_correct` — the target advances to a related state, or the source
stutters with a strictly decreasing measure `n2 < n1`. Failure modes: if some
instruction does not preserve the analysis invariant, `sound_step` fails, and
its real content is `sound_step_base` (a ~260-line case analysis in
`ValueAnalysis.v`); if the invariant is not compatible with `match_states`, the
single `Forward_simulation` application does not go through.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml runs tools/runner.sh build (full project, incl. backend/Constpropproof.v) on push to master; pinned commit 2685140bf72c959446981fb99b5e44a8975021bc is on default branch master | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: transf_initial_states@backend/Constpropproof.v:612, transf_final_states@backend/Constpropproof.v:614, transf_step_correct@backend/Constpropproof.v:618, sound_initial@backend/Constpropproof.v:613, sound_step@backend/Constpropproof.v:616, senv_preserved@backend/Constpropproof.v:622; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at 2685140bf72c959446981fb99b5e44a8975021bc | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(transf_program_correct, backend/Constpropproof.v, 607-623) -> declared: transf_program_correct is declared at backend/Constpropproof.v:607 | check_claims.py |
| 2 | verified | no_sorry(backend/Constpropproof.v, 49-623) -> no_sorry: none of admit, Admitted, Axiom, axiom in backend/Constpropproof.v:49-623 | check_claims.py |
| 3 | verified | child spans confirmed in copied code: transf_initial_states 581-595 (15), transf_final_states 597-602 (6), transf_step_correct 350-579 (230), sound_initial (ValueAnalysis.v) 1896-1914 (19), sound_step 1530-1534 (5), senv_preserved 49-51 (3); depth chain confirmed: transf_program_correct cites transf_step_correct at 618, transf_step_correct cites transf_ros_correct at 457/467, transf_ros_correct (declared 89) cites functions_translated (declared 53) at 107 | verifier |
| 4 | verified | copied backend/Constpropproof.v lines 258-282 contain both quotes verbatim: 'The proof of semantic preservation is a simulation argument / based on "option" diagrams of the following form' at 258-259, and 'the state [st1] must match its compile-time approximations at the current program point' at 276-277 (evidence field says line 278, off by one) | verifier |
| 5 | verified | fetched backend/CSEproof.v at pinned commit 2685140b; transf_program_correct (1572) uses invariant 'match_states s1 s2 and sound_state prog s1' (1576) and applies sound_initial at 1579 (auto using sound_initial) and sound_step at 1586 (eauto using sound_step), 1589 (apply sound_step), 1590 (eapply sound_step) | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent transf_program_correct (Constpropproof.v 607-623) is verbatim and its glue cites exactly six project lemmas: transf_initial_states (612), sound_initial (613), transf_final_states (614), sound_step (616), transf_step_correct (618), senv_preserved (622); lt_wf (611) is stdlib, correctly not a child. All six children are listed and each closing method matches the code (e.g. transf_final_states closed by 'inv H0; inv H; inv STACKS; inv RES; constructor'; senv_preserved by 'exact (Genv.senv_match TRANSL)'). Every site ends in Qed and no admit/Admitted/axiom/sorry token appears anywhere in Constpropproof.v, so it closes. Shape numbers are right: glue_lines=17 (parent span 607-623), child_lines=[15,6,230,19,5,3] matching spans 581-595, 597-602, 350-579, 1896-1914, 1530-1534, 49-51; direct_lemmas=6 and depth=3 confirmed by the chain 618 -> 457/467 -> 107 (transf_step_correct uses transf_ros_correct which uses functions_translated). | reviewer-correctness |
| generality | accept | Move is stated beyond the example: use_when and README 'When to use' abstract sound_state prog to 'one predicate established on initial states and preserved by every step', for 'a simulation between two programs (or two transition systems)'; also_known_as gives general terms and claim 5 records reuse in CSEproof. avoid_when is specific and honest (invariant not statable/reusable once, step-preservation inseparable from the diagram, per-instruction invariant), grounded in the code: transf_step_correct takes sound_state prog s1 as a hypothesis (line 353) and never proves it. Consequences are specific (five Forward_simulation fields, plus_one/star_refl diagram cases, failure modes: sound_step_base ~260-line case analysis, invariant/match_states incompatibility blocking the single application). 'Why each child is a good leaf' gives per-leaf size and self-containedness and honestly flags transf_step_correct (230 lines) as the large non-bounded leaf. | reviewer-generality |
| provenance-licence | accept | check_provenance pass: 2 files (backend/Constpropproof.v, backend/ValueAnalysis.v) byte-identical at pinned commit 2685140bf72c959446981fb99b5e44a8975021bc and recorded sha256 match. Commit hash is consistent across source.json, sources/compcert/SOURCE.md, entry.json source.commit, every permalink, and the README. Licence LicenseRef-INRIA-Non-Commercial is consistent across source.json, SOURCE.md, entry.json and README; the copied upstream-LICENSE confirms the INRIA Non-Commercial License Agreement and backend/ is not in the dual-licensed LGPL list, so the non-commercial tag is correct. Source note links to the copied licence text; permalink line ranges spot-checked via sed (607-623, 49-51, 1525-1534, 1896-1914) match the README excerpts verbatim. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/AbsInt/CompCert at commit `2685140bf72c959446981fb99b5e44a8975021bc`, under `LicenseRef-INRIA-Non-Commercial`; see the [source note](../../sources/compcert/SOURCE.md) for the licence text and attribution.
