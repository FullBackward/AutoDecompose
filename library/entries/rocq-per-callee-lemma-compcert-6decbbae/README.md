# Forward simulation of the inlining pass assembled from four per-obligation lemmas

| | |
|---|---|
| Kind | instance |
| Move | per-callee-lemma |
| Language | rocq |
| Status | accepted |
| Source | [compcert](../../sources/compcert/SOURCE.md) at `2685140bf72c` |
| Licence | `LicenseRef-INRIA-Non-Commercial AND (LicenseRef-INRIA-Non-Commercial OR LGPL-2.1-or-later)` |

## Intent

CompCert's inlining pass must show `forward_simulation (semantics prog)
(semantics tprog)`. The proof reduces this to the four fields of the
forward-simulation diagram — symbol environment, initial states, final states,
and the step simulation — and discharges each with its own named lemma, so the
headline theorem is a five-line glue.

## The decomposition

### parent `transf_program_correct`: [`backend/Inliningproof.v` lines 1253-1261](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/backend/Inliningproof.v#L1253-L1261) ([local copy](code/backend/Inliningproof.v))

```coq
Theorem transf_program_correct:
  forward_simulation (semantics prog) (semantics tprog).
Proof.
  eapply forward_simulation_star.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact step_simulation.
Qed.
```

### child `senv_preserved`: [`backend/Inliningproof.v` lines 41-43](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/backend/Inliningproof.v#L41-L43) ([local copy](code/backend/Inliningproof.v))

```coq
Lemma senv_preserved:
  Senv.equiv ge tge.
Proof. exact (Genv.senv_match TRANSF). Qed.
```

### child `transf_initial_states`: [`backend/Inliningproof.v` lines 1226-1242](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/backend/Inliningproof.v#L1226-L1242) ([local copy](code/backend/Inliningproof.v))

```coq
Lemma transf_initial_states:
  forall st1, initial_state prog st1 -> exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros (cu & tf & FIND & TR & LINK).
  exists (Callstate nil tf nil m0); split.
  econstructor; eauto.
    eapply (Genv.init_mem_match TRANSF); eauto.
    rewrite symbols_preserved. replace (prog_main tprog) with (prog_main prog). auto.
    symmetry; eapply match_program_main; eauto.
    rewrite <- H3. eapply sig_function_translated; eauto.
  econstructor; eauto.
  instantiate (1 := Mem.flat_inj (Mem.nextblock m0)).
  erewrite <- Genv.init_mem_genv_next by eauto.
  apply match_stacks_nil. apply Genv.init_inject. apply Ple_refl.
  eapply Genv.initmem_inject; eauto.
Qed.
```

### child `transf_final_states`: [`backend/Inliningproof.v` lines 1244-1251](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/backend/Inliningproof.v#L1244-L1251) ([local copy](code/backend/Inliningproof.v))

```coq
Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H.
  exploit match_stacks_empty; eauto. intros EQ; subst. inv VINJ. constructor.
  exploit match_stacks_inside_empty; eauto. intros [A B]. congruence.
Qed.
```

### child `step_simulation`: [`backend/Inliningproof.v` lines 874-1224](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/backend/Inliningproof.v#L874-L1224) ([local copy](code/backend/Inliningproof.v))

```coq
Theorem step_simulation:
  forall S1 t S2,
  step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  (exists S2', plus step tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros; inv MS.

- (* nop *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  left; econstructor; split.
  eapply plus_one. eapply exec_Inop; eauto.
  econstructor; eauto.

- (* op *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_operation_inject.
    eapply match_stacks_inside_globalenvs; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eexact MINJ. eauto.
  fold (sop ctx op). intros [v' [A B]].
  left; econstructor; split.
  eapply plus_one. eapply exec_Iop; eauto. erewrite eval_operation_preserved; eauto.
  exact symbols_preserved.
  econstructor; eauto.
  apply match_stacks_inside_set_reg; auto.
  apply agree_set_reg; auto.

- (* load *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_addressing_inject.
    eapply match_stacks_inside_globalenvs; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
  fold (saddr ctx addr). intros [a' [P Q]].
  exploit Mem.loadv_inject; eauto. intros [v' [U V]].
  assert (eval_addressing tge (Vptr sp' Ptrofs.zero) (saddr ctx addr) rs' ## (sregs ctx args) = Some a').
  rewrite <- P. apply eval_addressing_preserved. exact symbols_preserved.
  left; econstructor; split.
  eapply plus_one. eapply exec_Iload; eauto.
  econstructor; eauto.
  apply match_stacks_inside_set_reg; auto.
  apply agree_set_reg; auto.

- (* store *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_addressing_inject.
    eapply match_stacks_inside_globalenvs; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
  fold saddr. intros [a' [P Q]].
  exploit Mem.storev_mapped_inject; eauto. eapply agree_val_reg; eauto.
  intros [m1' [U V]].
  assert (eval_addressing tge (Vptr sp' Ptrofs.zero) (saddr ctx addr) rs' ## (sregs ctx args) = Some a').
    rewrite <- P. apply eval_addressing_preserved. exact symbols_preserved.
  left; econstructor; split.
  eapply plus_one. eapply exec_Istore; eauto.
  destruct a; try discriminate. 
  destruct a'; try discriminate.
  econstructor; eauto.
  eapply match_stacks_inside_store; eauto.
  eapply Mem.store_valid_block_1; eauto with mem.
  eapply range_private_invariant; eauto with mem.
  intros. eapply SSZ2. eapply Mem.perm_store_2; eauto with mem.

- (* call *)
  exploit find_function_agree; eauto using match_stacks_inside_globalenvs. intros (cu & fd' & A & B & C).
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
+ (* not inlined *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Icall; eauto.
  eapply sig_function_translated; eauto.
  econstructor; eauto.
  eapply match_stacks_cons; eauto.
  eapply agree_val_regs; eauto.
+ (* inlined *)
  assert (EQ: fd = Internal f0) by (eapply find_inlined_function; eauto).
  subst fd.
  right; split. simpl; lia. split. auto.
  econstructor; eauto.
  eapply match_stacks_inside_inlined; eauto.
  red; intros. apply PRIV. inv H13. destruct H16. extlia.
  apply agree_val_regs_gen; auto.
  red; intros; apply PRIV. destruct H16. lia.

- (* tailcall *)
  exploit find_function_agree; eauto using match_stacks_inside_globalenvs. intros (cu & fd' & A & B & C).
  assert (PRIV': range_private F m' m'0 sp' (dstk ctx) f'.(fn_stacksize)).
  { eapply range_private_free_left; eauto. inv FB. rewrite <- H4. auto. }
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
+ (* within the original function *)
  inv MS0; try congruence.
  assert (X: { m1' | Mem.free m'0 sp' 0 (fn_stacksize f') = Some m1'}).
    apply Mem.range_perm_free. red; intros.
    destruct (zlt ofs f.(fn_stacksize)).
    replace ofs with (ofs + dstk ctx) by lia. eapply Mem.perm_inject; eauto.
    eapply Mem.free_range_perm; eauto. lia.
    inv FB. eapply range_private_perms; eauto. extlia.
  destruct X as [m1' FREE].
  left; econstructor; split.
  eapply plus_one. eapply exec_Itailcall; eauto.
  eapply sig_function_translated; eauto.
  econstructor; eauto.
  eapply match_stacks_bound with (bound := sp').
  eapply match_stacks_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto.
    intros. eapply Mem.perm_free_1; eauto with ordered_type.
    intros. eapply Mem.perm_free_3; eauto.
  erewrite Mem.nextblock_free; eauto. red in VB; extlia.
  eapply agree_val_regs; eauto.
  eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
  (* show that no valid location points into the stack block being freed *)
  intros. rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). lia. intros [P Q].
  eelim Q; eauto. replace (ofs + delta - delta) with ofs by lia.
  apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
+ (* turned into a call *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Icall; eauto.
  eapply sig_function_translated; eauto.
  econstructor; eauto.
  eapply match_stacks_untailcall; eauto.
  eapply match_stacks_inside_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto.
  eapply agree_val_regs; eauto.
  eapply Mem.free_left_inject; eauto.
+ (* inlined *)
  assert (EQ: fd = Internal f0) by (eapply find_inlined_function; eauto).
  subst fd.
  right; split. simpl; lia. split. auto.
  econstructor; eauto.
  eapply match_stacks_inside_inlined_tailcall; eauto.
  eapply match_stacks_inside_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto.
  apply agree_val_regs_gen; auto.
  eapply Mem.free_left_inject; eauto.
  red; intros; apply PRIV'.
    assert (dstk ctx <= dstk ctx'). red in H14; rewrite H14. apply align_le. apply min_safe_alignment_pos.
    lia.

- (* builtin *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit tr_builtin_args; eauto using match_stacks_inside_globalenvs. intros (vargs' & P & Q).
  exploit external_call_mem_inject; eauto using match_stacks_inside_globalenvs.
  intros [F1 [v1 [m1' [A [B [C [D [E [J K]]]]]]]]].
  left; econstructor; split.
  eapply plus_one. eapply exec_Ibuiltin; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor.
    eapply match_stacks_inside_set_res.
    eapply match_stacks_inside_extcall with (F1 := F) (F2 := F1) (m1 := m) (m1' := m'0); eauto.
    intros; eapply external_call_max_perm; eauto.
    intros; eapply external_call_max_perm; eauto.
  auto. eauto. auto.
  destruct res; simpl; [apply agree_set_reg;auto|idtac|idtac]; eapply agree_regs_incr; eauto.
  auto. auto.
  eapply external_call_valid_block; eauto.
  eapply range_private_extcall; eauto.
    intros; eapply external_call_max_perm; eauto.
  auto.
  intros. apply SSZ2. eapply external_call_max_perm; eauto.

- (* cond *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  assert (eval_condition cond rs'##(sregs ctx args) m' = Some b).
    eapply eval_condition_inject; eauto. eapply agree_val_regs; eauto.
  left; econstructor; split.
  eapply plus_one. eapply exec_Icond; eauto.
  destruct b; econstructor; eauto.

- (* jumptable *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  assert (Val.inject F rs#arg rs'#(sreg ctx arg)). eapply agree_val_reg; eauto.
  rewrite H0 in H2; inv H2.
  left; econstructor; split.
  eapply plus_one. eapply exec_Ijumptable; eauto.
  rewrite list_nth_z_map. rewrite H1. simpl; reflexivity.
  econstructor; eauto.

- (* return *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
+ (* not inlined *)
  inv MS0; try congruence.
  assert (X: { m1' | Mem.free m'0 sp' 0 (fn_stacksize f') = Some m1'}).
    apply Mem.range_perm_free. red; intros.
    destruct (zlt ofs f.(fn_stacksize)).
    replace ofs with (ofs + dstk ctx) by lia. eapply Mem.perm_inject; eauto.
    eapply Mem.free_range_perm; eauto. lia.
    inv FB. eapply range_private_perms; eauto.
    generalize (Zmax_spec (fn_stacksize f) 0). destruct (zlt 0 (fn_stacksize f)); lia.
  destruct X as [m1' FREE].
  left; econstructor; split.
  eapply plus_one. eapply exec_Ireturn; eauto.
  econstructor; eauto.
  eapply match_stacks_bound with (bound := sp').
  eapply match_stacks_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto.
    intros. eapply Mem.perm_free_1; eauto with ordered_type.
    intros. eapply Mem.perm_free_3; eauto.
  erewrite Mem.nextblock_free; eauto. red in VB; extlia.
  destruct or; simpl. apply agree_val_reg; auto. auto.
  eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
  (* show that no valid location points into the stack block being freed *)
  intros. inversion FB; subst.
  assert (PRIV': range_private F m' m'0 sp' (dstk ctx) f'.(fn_stacksize)).
    rewrite H8 in PRIV. eapply range_private_free_left; eauto.
  rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). lia. intros [A B].
  eelim B; eauto. replace (ofs + delta - delta) with ofs by lia.
  apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.

+ (* inlined *)
  right. split. simpl. lia. split. auto.
  econstructor; eauto.
  eapply match_stacks_inside_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto.
  destruct or; simpl. apply agree_val_reg; auto. auto.
  eapply Mem.free_left_inject; eauto.
  inv FB. rewrite H4 in PRIV. eapply range_private_free_left; eauto.

- (* internal function, not inlined *)
  assert (A: exists f', tr_function cunit f f' /\ fd' = Internal f').
  { Errors.monadInv FD. exists x. split; auto. eapply transf_function_spec; eauto. }
  destruct A as [f' [TR1 EQ]].
  assert (TR: tr_function prog f f').
  { eapply tr_function_linkorder; eauto. }
  inversion TR; subst.
  exploit Mem.alloc_parallel_inject. eauto. eauto. apply Z.le_refl.
    instantiate (1 := fn_stacksize f'). inv H2. extlia.
  intros [F' [m1' [sp' [A [B [C [D E]]]]]]].
  left; econstructor; split.
  eapply plus_one. eapply exec_function_internal; eauto.
  rewrite H5; eauto using Val.has_argtype_list_inject.
  rewrite H7. econstructor.
  instantiate (1 := F'). apply match_stacks_inside_base.
  assert (SP: sp' = Mem.nextblock m'0) by (eapply Mem.alloc_result; eauto).
  rewrite <- SP in MS0.
  eapply match_stacks_invariant; eauto.
    intros. destruct (eq_block b1 stk).
    subst b1. rewrite D in H9; inv H9. eelim Plt_strict; eauto.
    rewrite E in H9; auto.
    intros. exploit Mem.perm_alloc_inv. eexact H0. eauto.
    destruct (eq_block b1 stk); intros; auto.
    subst b1. rewrite D in H9; inv H9. eelim Plt_strict; eauto.
    intros. eapply Mem.perm_alloc_1; eauto.
    intros. exploit Mem.perm_alloc_inv. eexact A. eauto.
    rewrite dec_eq_false; auto with ordered_type.
  auto. auto. auto. eauto. auto.
  rewrite H6. apply agree_regs_init_regs. eauto. auto. inv H2; auto. congruence. auto.
  eapply Mem.valid_new_block; eauto.
  red; intros. split.
  eapply Mem.perm_alloc_2; eauto. inv H2; extlia.
  intros; red; intros. exploit Mem.perm_alloc_inv. eexact H0. eauto.
  destruct (eq_block b stk); intros.
  subst. rewrite D in H10; inv H10. inv H2; extlia.
  rewrite E in H10; auto. eelim Mem.fresh_block_alloc. eexact A. eapply Mem.mi_mappedblocks; eauto.
  auto.
  intros. exploit Mem.perm_alloc_inv; eauto. rewrite dec_eq_true. lia.

- (* internal function, inlined *)
  inversion FB; subst.
  exploit Mem.alloc_left_mapped_inject.
    eauto.
    eauto.
    (* sp' is valid *)
    instantiate (1 := sp'). auto.
    (* offset is representable *)
    instantiate (1 := dstk ctx). generalize (Z.le_max_r (fn_stacksize f) 0). lia.
    (* negative offsets are not revealed *)
    right; lia.
    (* size of target block is representable *)
    intros. right. exploit SSZ2; eauto with mem. inv FB; lia.
    (* we have full permissions on sp' at and above dstk ctx *)
    intros. apply Mem.perm_cur. apply Mem.perm_implies with Freeable; auto with mem.
    eapply range_private_perms; eauto. extlia.
    (* offset is aligned *)
    replace (fn_stacksize f - 0) with (fn_stacksize f) by lia.
    inv FB. assumption.
    (* nobody maps to (sp, dstk ctx...) *)
    intros. exploit (PRIV (ofs + delta')); eauto. extlia.
    intros [A B]. eelim B; eauto.
    replace (ofs + delta' - delta') with ofs by lia.
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
  intros [F' [A [B [C D]]]].
  exploit tr_moves_init_regs; eauto. intros [rs'' [P [Q R]]].
  left; econstructor; split.
  eapply plus_left. eapply exec_Inop; eauto. eexact P. traceEq.
  econstructor.
  eapply match_stacks_inside_alloc_left; eauto.
  eapply match_stacks_inside_invariant; eauto.
  lia.
  eauto. auto.
  apply agree_regs_incr with F; auto.
  auto. auto. auto.
  rewrite H3. eapply range_private_alloc_left; eauto.
  auto. auto.

- (* external function *)
  exploit external_call_mem_inject; eauto using match_stacks_globalenvs.
  intros [F1 [v1 [m1' [A [B [C [D [E [J K]]]]]]]]].
  simpl in FD. inv FD.
  left; econstructor; split.
  eapply plus_one. eapply exec_function_external; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor.
    eapply match_stacks_bound with (Mem.nextblock m'0).
    eapply match_stacks_extcall with (F1 := F) (F2 := F1) (m1 := m) (m1' := m'0); eauto.
    intros; eapply external_call_max_perm; eauto.
    intros; eapply external_call_max_perm; eauto.
    extlia.
    eapply external_call_nextblock; eauto.
    auto. auto.

- (* return from noninlined function *)
  inv MS0.
+ (* normal case *)
  left; econstructor; split.
  eapply plus_one. eapply exec_return.
  econstructor; eauto.
  apply match_stacks_inside_set_reg; auto.
  apply agree_set_reg; auto.
+ (* untailcall case *)
  inv MS; try congruence.
  rewrite RET in RET0; inv RET0.
  left; econstructor; split.
  eapply plus_one. eapply exec_return.
  eapply match_regular_states.
  eapply match_stacks_inside_set_reg; eauto.
  eauto. auto.
  apply agree_set_reg; auto.
  auto. auto. auto.
  red; intros. destruct (zlt ofs (dstk ctx)). apply PAD; lia. apply PRIV; lia.
  auto. auto.

- (* return from inlined function *)
  inv MS0; try congruence. rewrite RET0 in RET; inv RET.
  unfold inline_return in AT.
  assert (PRIV': range_private F m m' sp' (dstk ctx' + mstk ctx') f'.(fn_stacksize)).
    red; intros. destruct (zlt ofs (dstk ctx)). apply PAD. lia. apply PRIV. lia.
  destruct or.
+ (* with a result *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Iop; eauto. simpl. reflexivity.
  econstructor; eauto. apply match_stacks_inside_set_reg; auto. apply agree_set_reg; auto.
+ (* without a result *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Inop; eauto.
  econstructor; eauto. subst vres. apply agree_set_reg_undef'; auto.
Qed.
```

### context `forward_simulation_star`: [`common/Smallstep.v` lines 617-695](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/common/Smallstep.v#L617-L695) ([local copy](code/common/Smallstep.v))

```coq
Section FORWARD_SIMU_DIAGRAMS.

Variable L1: semantics.
Variable L2: semantics.

Hypothesis public_preserved:
  forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id.

Variable match_states: state L1 -> state L2 -> Prop.

Hypothesis match_initial_states:
  forall s1, initial_state L1 s1 ->
  exists s2, initial_state L2 s2 /\ match_states s1 s2.

Hypothesis match_final_states:
  forall s1 s2 r,
  match_states s1 s2 ->
  final_state L1 s1 r ->
  final_state L2 s2 r.

(** Simulation when one transition in the first program
    corresponds to zero, one or several transitions in the second program.
    However, there is no stuttering: infinitely many transitions
    in the source program must correspond to infinitely many
    transitions in the second program. *)

Section SIMULATION_STAR_WF.

(** [order] is a well-founded ordering associated with states
  of the first semantics.  Stuttering steps must correspond
  to states that decrease w.r.t. [order]. *)

Variable order: state L1 -> state L1 -> Prop.
Hypothesis order_wf: well_founded order.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s2',
  (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order s1' s1))
  /\ match_states s1' s2'.

Lemma forward_simulation_star_wf: forward_simulation L1 L2.
Proof.
  apply Forward_simulation with order (fun idx s1 s2 => idx = s1 /\ match_states s1 s2);
  constructor.
- auto.
- intros. exploit match_initial_states; eauto. intros [s2 [A B]].
    exists s1; exists s2; auto.
- intros. destruct H. eapply match_final_states; eauto.
- intros. destruct H0. subst i. exploit simulation; eauto. intros [s2' [A B]].
  exists s1'; exists s2'; intuition auto.
- auto.
Qed.

End SIMULATION_STAR_WF.

Section SIMULATION_STAR.

(** We now consider the case where we have a nonnegative integer measure
  associated with states of the first semantics.  It must decrease when we take
  a stuttering step. *)

Variable measure: state L1 -> nat.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  (exists s2', Plus L2 s2 t s2' /\ match_states s1' s2')
  \/ (measure s1' < measure s1 /\ t = E0 /\ match_states s1' s2)%nat.

Lemma forward_simulation_star: forward_simulation L1 L2.
Proof.
  apply forward_simulation_star_wf with (ltof _ measure).
  apply well_founded_ltof.
  intros. exploit simulation; eauto. intros [[s2' [A B]] | [A [B C]]].
  exists s2'; auto.
  exists s2; split. right; split. rewrite B. apply star_refl. auto. auto.
Qed.
```

How the parts fit. The parent `transf_program_correct` (lines 1253-1261) is
closed in four steps: `eapply forward_simulation_star` introduces the four
obligations of a forward simulation, and then one lemma closes each —
`senv_preserved` (the `public_preserved` symbol-environment hypothesis),
`transf_initial_states` (the `match_initial_states` hypothesis),
`transf_final_states` (the `match_final_states` hypothesis) and
`step_simulation` (the `simulation` hypothesis). The context site
`forward_simulation_star` (`common/Smallstep.v` 617-695) states those four
hypotheses verbatim, so the mapping from lemma to obligation is read off
mechanically.

Lemma graph (each arrow reads "is closed using"):

```
transf_program_correct
 ├─ senv_preserved          ── Genv.senv_match TRANSF            (library, one exact)
 ├─ transf_initial_states   ── function_ptr_translated, symbols_preserved,
 │                              sig_function_translated, match_stacks_nil,
 │                              Genv.initmem_inject              (siblings, top of file)
 ├─ transf_final_states     ── match_stacks_empty, match_stacks_inside_empty
 │                                                               (siblings, mutual induction)
 └─ step_simulation         ── tr_funbody_inv, match_stacks_*, agree_*, Mem.*
       └─ match_stacks_invariant ── range_private_invariant      (deeper project lemmas)
```

Why each child is a good leaf. `senv_preserved` is a one-liner closed by
`exact (Genv.senv_match TRANSF)`. `transf_initial_states` and
`transf_final_states` close from the small lemmas proved at the top of the same
file (`function_ptr_translated`, `symbols_preserved`, `sig_function_translated`,
`match_stacks_empty`) — their proofs are 17 and 8 lines. `step_simulation` is
the one large child (351 lines): it closes on its own, by induction over the
step relation and case analysis over the RTL instructions, each case discharged
by the `match_stacks_*` and `agree_*` families. The longest chain I checked is
`transf_program_correct → step_simulation → match_stacks_invariant →
range_private_invariant` (depth 3): `step_simulation` cites `match_stacks_invariant`
at line 982, that lemma cites `range_private_invariant` at line 608, and
`range_private_invariant` closes with `exploit H; eauto` and `lia` (lines 274-276).

`common/Smallstep.v` packages this pattern as a reusable family of diagram
lemmas — `forward_simulation_star`, `forward_simulation_plus`,
`forward_simulation_step`, `forward_simulation_opt`, and more — each proving
`forward_simulation L1 L2` from a fixed set of hypotheses, so every CompCert
pass reuses the same four-obligation skeleton.

## Why it is good

1. `transf_program_correct` is declared at `backend/Inliningproof.v` lines
   1253-1261 (check, [permalink](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/backend/Inliningproof.v#L1253-L1261)).
2. No `admit`, `Admitted` or `Axiom` occurs in the `step_simulation` range
   `backend/Inliningproof.v` lines 874-1224 (check, [permalink](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/backend/Inliningproof.v#L874-L1224)).
3. `direct_lemmas = 4` and `glue_lines = 9`: the glue names four lemmas in five
   tactic lines (1256-1260) inside a nine-line parent site (1253-1261), while the
   four children span 3, 17, 8 and 351 lines (measurement; counted in
   `backend/Inliningproof.v` at the pinned commit).
4. The authors frame the star-simulation obligation as a distinct concept the
   lemmas discharge: "Simulation when one transition in the first program
   corresponds to zero, one or several transitions in the second program."
   (author-statement, [`common/Smallstep.v` 637-641](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/common/Smallstep.v#L637-L641)).

In my opinion the detail worth copying is the mechanical mapping from a record's
fields to named lemmas: `eapply forward_simulation_star` turns the four record
fields into four goals, and each goal is already a lemma, so the glue is
literally `apply`/`eexact` of pre-proved children.

## When to use it, and when not

Use it when the goal's head is a record or inductive with a small, fixed set of
fields (a `forward_simulation`, a locale, a structure), and each field can be
stated and proved as its own lemma with the simulation relation and any measure
fixed up front. This is the standard shape of a CompCert-style per-pass proof.

Avoid it when the obligations share substantial auxiliary state that would have
to be re-derived in every lemma (then the "children" are not self-contained and
the split buys nothing), when the simulation relation is still changing while
the diagram is being proved, or when the record has many or open-ended fields.

## Consequences

The move creates one obligation per field of the simulation record, each closed
by a named lemma. Three are small (3, 17, 8 lines); the step-simulation diagram
is the real content (351 lines) and needs a well-founded measure (`measure`,
lines 860-865). The glue's `eapply forward_simulation_star` fixes the diagram
shape (a plus/star simulation with a measure), so the simulation lemma must be
stated in exactly that shape; if the diagram cannot be put in that shape the
glue does not apply. Failure mode: a pass whose step-simulation needs the same
large machinery as its initial/final lemmas ends up with one giant lemma rather
than four.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml at pinned commit 2685140bf72c959446981fb99b5e44a8975021bc runs tools/runner.sh build (whole project, incl. backend/Inliningproof.v) on push to master (default branch) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: senv_preserved@backend/Inliningproof.v:1257, transf_initial_states@backend/Inliningproof.v:1258, transf_final_states@backend/Inliningproof.v:1259, step_simulation@backend/Inliningproof.v:1260; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at 2685140bf72c959446981fb99b5e44a8975021bc | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(transf_program_correct, backend/Inliningproof.v, 1253-1261) -> declared: transf_program_correct is declared at backend/Inliningproof.v:1253 | check_claims.py |
| 2 | verified | no_sorry(backend/Inliningproof.v, 874-1224) -> no_sorry: none of admit, Admitted, Axiom, axiom in backend/Inliningproof.v:874-1224 | check_claims.py |
| 3 | verified | Read backend/Inliningproof.v: parent site 1253-1261 is 9 lines (Theorem..Qed) with proof body 1256-1260 = 5 tactic lines naming senv_preserved, transf_initial_states, transf_final_states, step_simulation (plus eapply forward_simulation_star); child sites 41-43 (3 lines), 1226-1242 (17), 1244-1251 (8), 874-1224 (351) | verifier |
| 4 | verified | Read common/Smallstep.v lines 637-641: comment reads 'Simulation when one transition in the first program corresponds to zero, one or several transitions in the second program.' verbatim | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Verified against the local copy at the pinned commit. Parent transf_program_correct is exactly lines 1253-1261 (Theorem + forward_simulation statement + 5-line glue eapply forward_simulation_star / apply senv_preserved / eexact transf_initial_states / eexact transf_final_states / eexact step_simulation / Qed). The four children are the exact four lemmas the glue cites: senv_preserved (41-43, closed by exact (Genv.senv_match TRANSF)), transf_initial_states (1226-1242, uses function_ptr_translated, Genv.init_mem_match TRANSF, symbols_preserved, sig_function_translated, match_stacks_nil, Genv.initmem_inject), transf_final_states (1244-1251, uses match_stacks_empty + match_stacks_inside_empty), step_simulation (874-1224, induction 1 then per-instruction cases via tr_funbody_inv and the match_stacks_*/agree_*/Mem.* lemmas). Every child and the parent end in Qed; no sorry/admit/Admitted/Axiom in the ranges. Shape numbers check out: direct_lemmas=4, glue_lines=9 (1253-1261), child_lines=[3,17,8,351] (41-43, 1226-1242, 1244-1251, 874-1224), and depth=3 via the chain step_simulation (cites match_stacks_invariant at line 982; declared line 539) -> range_private_invariant (cited at 608, declared 263, closes 274-276). | reviewer-correctness |
| generality | accept | Move is generalised beyond the example: goal_shape names 'a record/inductive with a small fixed set of fields', and the README notes Smallstep.v packages the four-obligation skeleton as a reusable family (forward_simulation_star/plus/step/opt) reused by every CompCert pass. When-not-to-use is concrete (shared auxiliary state that must be re-derived per lemma, relation still unstable, many/open-ended fields) and consequences name a specific failure mode (giant step-simulation vs four lemmas) plus the shape lock imposed by eapply forward_simulation_star. 'Why each child is a good leaf' states per-child closure (one-liner exact, or from named top-of-file lemmas, 17/8-line bodies) and is honest that step_simulation is 351 lines, closing by induction+case analysis over the match_stacks_*/agree_* families. I confirmed in the local copy: measure@860-865, and the depth-3 chain cites step_simulation->match_stacks_invariant (982) and match_stacks_invariant->range_private_invariant (608). | reviewer-generality |
| provenance-licence | accept | Commit 2685140bf72c959446981fb99b5e44a8975021bc is consistent across entry.json (source.commit + all six site/file permalinks), source.json, SOURCE.md and README (12-char prefix). check_provenance passes: 2 files byte-identical at that commit, so repo+commit+paths are correct. All cited line ranges match the local copies verbatim (parent 1253-1261, senv_preserved 41-43, transf_initial_states 1226-1242, transf_final_states 1244-1251, step_simulation 874-1224, context 617-695, author-statement quote 637-641). Licence LicenseRef-INRIA-Non-Commercial is recorded identically in entry.json, SOURCE.md and source.json, and matches upstream-LICENSE (INRIA Non-Commercial; common/ files also dual-licensed LGPL 2.1+, so the NC tag is the conservative correct choice, and the full dual-licence detail is preserved in the copied LICENSE). SOURCE.md lists repo, pinned commit, licence file and attribution. sha256 per file and excerpt_sha256 per site recorded. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/AbsInt/CompCert at commit `2685140bf72c959446981fb99b5e44a8975021bc`, under `LicenseRef-INRIA-Non-Commercial AND (LicenseRef-INRIA-Non-Commercial OR LGPL-2.1-or-later)`; see the [source note](../../sources/compcert/SOURCE.md) for the licence text and attribution. Per file: `backend/Inliningproof.v` is under the INRIA Non-Commercial License Agreement only; `common/Smallstep.v` is dual-licensed under it or the GNU LGPL version 2.1 or later, at the user's choice (its header; CompCert's `LICENSE`). The entry as a whole is therefore non-commercial.
