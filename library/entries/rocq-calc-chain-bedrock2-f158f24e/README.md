# Compiler pipeline correctness as a transitivity chain of six per-pass simulations

| | |
|---|---|
| Kind | instance |
| Move | calc-chain |
| Language | rocq |
| Status | accepted |
| Source | [bedrock2](../../sources/bedrock2/SOURCE.md) at `b4ec84bc6dbb` |
| Licence | `MIT` |

## Intent

Reduce the correctness of the whole bedrock2 compiler pipeline (six passes, from
the source language `SrcLang` down to RISC-V machine code) to the correctness of
each pass alone. Each pass already has a `phase_correct` lemma; the top-level
proof only chains them with the transitivity lemma `compose_phases_correct`, so
the main theorem's proof is a single nested `exact` with no other step.

## The decomposition

### parent `composed_compiler_correct`: [`compiler/src/compiler/Pipeline.v` lines 634-643](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/Pipeline.v#L634-L643) ([local copy](code/compiler/src/compiler/Pipeline.v))

```coq
    Lemma composed_compiler_correct p_funcs stack_pastend ret_addr : phase_correct SrcLang (RiscvLang p_funcs stack_pastend ret_addr) composed_compile.
    Proof.
      unfold composed_compile.
      exact (compose_phases_correct flattening_correct
            (compose_phases_correct useimmediate_correct
            (compose_phases_correct dce_correct
            (compose_phases_correct regalloc_correct
            (compose_phases_correct spilling_correct
                                    (riscv_phase_correct _ _ _)))))).
    Qed.
```

### context `composed_compile`: [`compiler/src/compiler/Pipeline.v` lines 624-632](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/Pipeline.v#L624-L632) ([local copy](code/compiler/src/compiler/Pipeline.v))

```coq
    Definition composed_compile:
      Semantics.env ->
      result (list Instruction * string_keyed_map Z * Z) :=
      (compose_phases flatten_functions
      (compose_phases (useimmediate_functions is5BitImmediate is12BitImmediate)
      (compose_phases dce_functions
      (compose_phases regalloc_functions
      (compose_phases spill_functions
                      (riscvPhase compile_ext_call)))))).
```

### context `phase_correct`: [`compiler/src/compiler/Pipeline.v` lines 79-100](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/Pipeline.v#L79-L100) ([local copy](code/compiler/src/compiler/Pipeline.v))

```coq
  Record phase_correct{L1 L2: Lang}
    {compile: L1.(Program) -> result L2.(Program)}: Prop :=
  {
    phase_preserves_valid: forall p1 p2,
        compile p1 = Success p2 ->
        L1.(Valid) p1 ->
        L2.(Valid) p2;
    phase_preserves_post: forall p1 p2,
        L1.(Valid) p1 ->
        compile p1 = Success p2 ->
        forall fname k1 k2 pick_sp2,
          exists pick_sp1 k2'',
        forall t m argvals mc1 post,
        L1.(Call) p1 pick_sp1 fname k1 t m argvals mc1 post ->
        forall mc2,
          L2.(Call) p2 pick_sp2 fname k2 t m argvals mc2
               (fun k2' t m a mc2' =>
                  exists mc1' k1',
                    post k1' t m a mc1' /\
                      k2' = k2'' k1' /\
                      metricsLeq (mc2' - mc2) (mc1' - mc1));
  }.
```

### context `compose_phases`: [`compiler/src/compiler/Pipeline.v` lines 104-109](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/Pipeline.v#L104-L109) ([local copy](code/compiler/src/compiler/Pipeline.v))

```coq
  Definition compose_phases{A B C: Type}(phase1: A -> result B)(phase2: B -> result C):
    A -> result C :=
    fun a => match phase1 a with
             | Success b => phase2 b
             | Failure e => Failure e
             end.
```

### child `compose_phases_correct`: [`compiler/src/compiler/Pipeline.v` lines 115-135](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/Pipeline.v#L115-L135) ([local copy](code/compiler/src/compiler/Pipeline.v))

```coq
  Lemma compose_phases_correct{L1 L2 L3: Lang}
        {compile12: L1.(Program) -> result L2.(Program)}
        {compile23: L2.(Program) -> result L3.(Program)}:
    phase_correct L1 L2 compile12 ->
    phase_correct L2 L3 compile23 ->
    phase_correct L1 L3 (compose_phases compile12 compile23).
  Proof.
    unfold compose_phases.
    intros [V12 C12] [V23 C23].
    split; intros; fwd; eauto.
    specialize (V12 p1 a E H).
    specialize (C23 a p2 V12 H0 fname nil k2 pick_sp2).
    destruct C23 as [pick_sp_mid [f23 C23] ].
    specialize (C12 p1 a H E fname k1 nil pick_sp_mid).
    destruct C12 as [pick_sp1 [f12 C12] ]. 
    exists pick_sp1. exists (fun k3' => f23 (f12 k3')).
    intros. eapply C12 in H1. eapply C23 in H1.
    eassert ((fun _ _ _ _ _ => exists _, _) = _) as ->. 2: exact H1.
    post_ext. split; intros; fwd; eauto 10 with metric_arith.
    Unshelve. all: exact EmptyMetricLog.
  Qed.
```

### child `flattening_correct`: [`compiler/src/compiler/Pipeline.v` lines 274-324](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/Pipeline.v#L274-L324) ([local copy](code/compiler/src/compiler/Pipeline.v))

```coq
    Lemma flattening_correct: phase_correct SrcLang FlatWithStrVars flatten_functions.
    Proof.
      unfold SrcLang, FlatWithStrVars.
      split; cbn -[flatten_functions].
      { unfold map.forall_values, ParamsNoDup.
        intros. destruct v as ((argnames & retnames) & body).
        eapply flatten_functions_NoDup; try eassumption.
        unfold valid_fun in *.
        intros. specialize H0 with (1 := H2). simpl in H0. eapply H0.
      }
      unfold locals_based_call_spec. intros.
      exists (fun k => pick_sp2 (remove_n_r (length k1) k ++ k2)).
      exists (fun k => remove_n_r (length k1) k ++ k2). intros. fwd.
      pose proof H0 as GF.
      unfold flatten_functions in GF.
      eapply map.try_map_values_fw in GF. 2: eassumption.
      unfold flatten_function in GF. fwd.
      eexists _, _, _, _. split. 1: eassumption. split. 1: eassumption.
      intros.
      eapply FlatImp.exec.weaken.
      - eapply flattenStmt_correct_aux.
        + eassumption.
        + eapply MetricLeakageSemantics.exec.exec_ext. 
          1: eapply MetricLeakageSemantics.exec.exec_to_other_trace.
          1: eapply H1p2.
          intros. simpl. simpl_rev. rewrite List.skipn_app_r.
          2: rewrite rev_length; reflexivity.
          rewrite remove_n_r_spec. rewrite rev_involutive. reflexivity.
        + reflexivity.
        + match goal with
          | |- ?p = _ => rewrite (surjective_pairing p)
          end.
          reflexivity.
        + intros x k A. assumption.
        + unfold map.undef_on, map.agree_on. cbn. intros k A.
          rewrite map.get_empty. destr (map.get l k). 2: reflexivity. exfalso.
          unfold map.of_list_zip in H1p1.
          edestruct (map.putmany_of_list_zip_find_index _ _ _ _ _ _ H1p1 E) as [G | G].
          2: {
            rewrite map.get_empty in G. discriminate.
          }
          destruct G as (i & G1 & G2).
          eapply nth_error_In in G1.
          eapply start_state_spec. 2: exact A.
          eapply ListSet.In_list_union_l. eapply ListSet.In_list_union_l. assumption.
        + eapply @freshNameGenState_disjoint_fbody.
      - simpl. intros. fwd. eexists. split.
        + eauto using map.getmany_of_list_extends.
        + do 2 eexists. split; [eassumption|]. rewrite remove_n_r_spec.
          split; [reflexivity|]. unfold cost_spill_spec in *; solve_MetricLog.
    Qed.
```

### child `useimmediate_correct`: [`compiler/src/compiler/Pipeline.v` lines 342-376](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/Pipeline.v#L342-L376) ([local copy](code/compiler/src/compiler/Pipeline.v))

```coq
    Lemma useimmediate_correct: phase_correct FlatWithStrVars FlatWithStrVars (useimmediate_functions is5BitImmediate is12BitImmediate).
    Proof.
      unfold FlatWithStrVars.
      split; cbn.
      { unfold map.forall_values, ParamsNoDup. intros.
        destruct v as  ((argnames & retnames) & body).
        eapply useimmediate_functions_NoDup; try eassumption.
        intros. specialize H0 with (1 := H2).
        simpl in H0. assumption.
      }

      unfold locals_based_call_spec. intros.
      exists (fun k => pick_sp2 ((rev (skipn (length k1) (rev k)) ++ k2))).
      exists (fun k => remove_n_r (length k1) k ++ k2). intros. fwd.
      pose proof H0 as GI.
      unfold  useimmediate_functions in GI.
      eapply map.try_map_values_fw in GI. 2: eassumption.
      unfold useimmediate_function in GI. fwd.
      eexists _, _, _, _. split. 1: eassumption. split. 1: eassumption.
      intros.
      eapply exec.weaken.
      - eapply useImmediate_correct_aux; eauto.
        eapply FlatImp.exec.exec_ext. 
        1: eapply FlatImp.exec.exec_to_other_trace.
        1: eassumption.
        intros. simpl. simpl_rev. rewrite List.skipn_app_r.
        2: rewrite rev_length; reflexivity.
        simpl_rev. rewrite List.skipn_app_r.
        2: rewrite rev_length; reflexivity.
        rewrite rev_involutive. reflexivity.
      - simpl. intros. fwd. eexists. intuition eauto.
        do 2 eexists. intuition eauto.
        { rewrite remove_n_r_spec. reflexivity. }
        unfold cost_spill_spec in *; solve_MetricLog.
    Qed.
```

### child `dce_correct`: [`compiler/src/compiler/Pipeline.v` lines 391-439](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/Pipeline.v#L391-L439) ([local copy](code/compiler/src/compiler/Pipeline.v))

```coq
    Lemma dce_correct: phase_correct FlatWithStrVars FlatWithStrVars dce_functions.
    Proof.
      unfold FlatWithStrVars.
      split; cbn.
      { unfold map.forall_values, ParamsNoDup. intros.
        destruct v as  ((argnames & retnames) & body).
        eapply dce_functions_NoDup; try eassumption.
        intros. specialize H0 with (1 := H2).
        simpl in H0. assumption.
      }
      unfold locals_based_call_spec. intros.
      assert (E: (exists x, map.get p1 fname = Some x) -> map.get p1 fname = Some (match (map.get p1 fname) with | Some finfo => finfo | None => (nil, nil, SSkip) end)).
      { intros. destruct H1 as [x H1]. destruct (map.get p1 fname); congruence. }
      destruct (match map.get p1 fname with
                    | Some finfo => finfo
                    | None => ([], [], SSkip)
                    end) as [ [argnames0 retnames0] fbody0 ].
      eexists. eexists. intros. fwd.
      assert (H1p0': map.get p1 fname = Some (argnames0, retnames0, fbody0)).
      { eapply E. eexists. apply H1p0. }
      rewrite H1p0 in H1p0'. inversion H1p0'. subst. clear H1p0'.
      pose proof H0 as GI.
      unfold dce_functions in GI.
      eapply map.try_map_values_fw in GI. 2: eassumption.
      unfold dce_function in GI. fwd.
      eexists _, _, _, _. split. 1: eassumption. split. 1: eassumption.
      intros.
      eapply @exec.weaken.
      - eapply exec.exec_ext. 1: eapply dce_correct_aux; eauto.
        { eapply MapEauto.agree_on_refl. }
        2: { intros. simpl. instantiate (1 := fun x => pick_sp2 (rev x)).
             simpl. rewrite rev_involutive. reflexivity. }
        intros. remember (k ++ k1) as kk eqn:Hkk.
        rewrite <- (remove_n_r_spec k k1). forget (k ++ k1) as kk0.
        subst. instantiate (2 := fun _ => _). simpl. reflexivity.
      - unfold compile_post. intros. fwd.
        exists retvals.
        split.
        + erewrite MapEauto.agree_on_getmany; [ eauto | eapply MapEauto.agree_on_comm; [ eassumption ] ].
        + do 3 eexists; ssplit; eauto. 2: unfold cost_spill_spec in *; solve_MetricLog.
          instantiate (1 := fun _ => _). simpl.
          specialize (H1p8 nil (fun _ => nil)). simpl in H1p8.
          do 2 rewrite app_nil_r in H1p8.
          rewrite <- (rev_involutive kL''). rewrite <- H1p8.
          remember (kH'' ++ k1) as kk eqn:Hkk.
          rewrite <- (remove_n_r_spec kH'' k1).
          rewrite <- Hkk. reflexivity.
          Unshelve. all: auto.
    Qed.
```

### child `regalloc_correct`: [`compiler/src/compiler/Pipeline.v` lines 457-503](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/Pipeline.v#L457-L503) ([local copy](code/compiler/src/compiler/Pipeline.v))

```coq
    Lemma regalloc_correct: phase_correct FlatWithStrVars FlatWithZVars regalloc_functions.
    Proof.
      unfold FlatWithStrVars, FlatWithZVars. split; cbn.
      { unfold map.forall_values, ParamsNoDup. intros.
        destruct v as ((argnames & retnames) & body).
        eapply regalloc_functions_NoDup; eassumption.
      }
      unfold locals_based_call_spec.
      intros. exists (fun k => pick_sp2 (remove_n_r (length k1) k ++ k2)).
      exists (fun kH'' => remove_n_r (length k1) kH'' ++ k2). intros. fwd.
      pose proof H0 as GR.
      unfold regalloc_functions in GR.
      fwd. rename E into GR.
      eapply map.try_map_values_fw in GR. 2: eassumption.
      fwd. clear GRp0.
      pose proof E0 as C.
      unfold check_funcs in E0.
      eapply map.get_forall_success in E0. 2: eassumption.
      unfold lookup_and_check_func, check_func in E0. fwd.

      rename l0 into argregs, l1 into retregs.
      apply_in_hyps assert_ins_same_length.
      apply_in_hyps assignments_same_length.
      apply_in_hyps @map.putmany_of_list_zip_sameLength.
      assert (exists l', map.of_list_zip argregs argvals = Some l'). {
        eapply map.sameLength_putmany_of_list. congruence.
      }
      fwd.
      eexists _, _, _, _. split. 1: eassumption. split. 1: eassumption. intros.
      unfold map.of_list_zip in *.
      eapply FlatImp.exec.weaken.
      - eapply checker_correct; eauto.
        + eapply FlatImp.exec.exec_ext. 
          1: eapply FlatImp.exec.exec_to_other_trace.
          1: eassumption.
          intros. simpl. rewrite remove_n_r_spec. simpl_rev. rewrite List.skipn_app_r.
          2: rewrite rev_length; reflexivity.
          rewrite rev_involutive. reflexivity.
        + eapply states_compat_precond.
          edestruct putmany_of_list_zip_states_compat as (lL' & P' & Cp); try eassumption.
          1: eapply states_compat_empty.
          rewrite H1 in P'. inversion P'. exact Cp.
      - simpl. intros. fwd. eexists. split.
        + eauto using states_compat_getmany.
        + do 2 eexists. rewrite remove_n_r_spec. intuition eauto.
          unfold cost_spill_spec in *; solve_MetricLog.
    Qed.
```

### child `spilling_correct`: [`compiler/src/compiler/Pipeline.v` lines 552-584](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/Pipeline.v#L552-L584) ([local copy](code/compiler/src/compiler/Pipeline.v))

```coq
    Lemma spilling_correct: phase_correct FlatWithZVars FlatWithRegs spill_functions.
    Proof.
      unfold FlatWithZVars, FlatWithRegs. split; cbn.
      1: exact spilling_preserves_valid.
      unfold locals_based_call_spec. intros.
      set (finfo := (match (map.get p1 fname) with | Some finfo => finfo | None => (nil, nil, SSkip) end)).
      exists (fun k => snd (fun_leakage p1 pick_sp2 finfo (skipn (length k1) (rev k)) (rev k2))).
      exists (fun k1' => rev (fst (fun_leakage p1 pick_sp2 finfo (rev (remove_n_r (length k1) k1')) (rev k2)))).
      intros. fwd.
      subst finfo. rewrite H1p0 in *.
      pose proof H0 as GL.
      unfold spill_functions in GL.
      eapply map.try_map_values_fw in GL. 2: eassumption.
      destruct GL as (((argnames2 & retnames2) & fbody2) & Sp & G2).
      apply_in_hyps @map.putmany_of_list_zip_sameLength.
      assert (exists l', map.of_list_zip argnames2 argvals = Some l'). {
        eapply map.sameLength_putmany_of_list.
        unfold spill_fun in Sp. fwd.
        rewrite !List.firstn_length.
        change (Datatypes.length (reg_class.all reg_class.arg)) with 8%nat.
        lia.
      }
      fwd.
      exists argnames2, retnames2, fbody2, l'.
      split. 1: exact G2. split. 1: eassumption.
      intros.
      eapply FlatImp.exec.weaken.
      - eapply spill_fun_correct; try eassumption.
        unfold call_spec. intros * E. rewrite E in *. fwd. exact H1p2.
      - cbv beta. intros. fwd. eexists. intuition eauto.
        do 2 eexists. intuition eauto. rewrite remove_n_r_spec.
        rewrite H2p1p2. rewrite rev_involutive. reflexivity.
    Qed.
```

### child `riscv_phase_correct`: [`compiler/src/compiler/Pipeline.v` lines 602-622](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/Pipeline.v#L602-L622) ([local copy](code/compiler/src/compiler/Pipeline.v))

```coq
    Lemma riscv_phase_correct p_funcs stack_pastend ret_addr : phase_correct FlatWithRegs (RiscvLang p_funcs stack_pastend ret_addr) (riscvPhase compile_ext_call).
    Proof.
      unfold FlatWithRegs, RiscvLang.
      split; cbn.
      - intros p1 ((? & finfo) & ?). intros. exact I.
      - intros. set (finfo := match (map.get p1 fname) with | Some finfo => finfo | None => (nil, nil, SSkip) end).
        destruct finfo as [ [argnames0 retnames0] fbody0 ] eqn:E.
        destruct p2 as [ [instrs finfo_] req_stack_size] eqn:E'.
        eexists. eexists. intros.
        cbv [locals_based_call_spec] in H1. fwd. subst finfo. rewrite H1p0 in E.
        inversion E. subst. pose proof flat_to_riscv_correct as H'.
        repeat specialize (H' ltac:(assumption)).
        specialize (H' (instrs, finfo_, req_stack_size)).
        do 2 specialize (H' ltac:(assumption)). cbv beta match in H'. idtac.
        eapply riscv_call_weaken. 1: eapply H'; eauto.
        simpl. intros. fwd. do 2 eexists. split; [eassumption|]. split; [|eassumption].
        rewrite <- (rev_involutive k'). rewrite <- H1p5.       
        remember (kH'' ++ k1) as k''. replace kH'' with (remove_n_r (length k1) k'').
        2: { subst. apply remove_n_r_spec. }
        instantiate (1 := fun _ => _). simpl. reflexivity.
    Qed.
```

How the parts fit. `phase_correct` (lines 79-100) is a two-field simulation
record: a pass is correct if it preserves validity and turns a high-level
`Call` into a low-level `Call` whose postcondition, leakage and metric are no
worse. `compose_phases` (104-109) threads the `result` monad through two
passes. `composed_compile` (624-632) composes the six concrete passes —
`flatten_functions`, `useimmediate_functions`, `dce_functions`,
`regalloc_functions`, `spill_functions`, `riscvPhase compile_ext_call` — in a
right-nested chain. The parent `composed_compiler_correct` (634-643) unfolds
that definition and applies `compose_phases_correct` once per link, in exactly
the same order, so each hole is one whole pass.

The lemma graph is a spine, not a tree: each of the six pass lemmas is a leaf,
and `compose_phases_correct` is the one glue lemma used five times, once per
intermediate language:

```
composed_compiler_correct
  uses compose_phases_correct + flattening_correct + useimmediate_correct
     + dce_correct + regalloc_correct + spilling_correct + riscv_phase_correct
```

Each pass lemma is a good leaf because its statement is self-contained — a
`phase_correct` between two named `Lang` instances — and its proof closes on
its own, by `split` into the two `phase_correct` fields and one imported
per-pass lemma (`flattenStmt_correct_aux`, `useImmediate_correct_aux`,
`dce_correct_aux`, `checker_correct`, `spill_fun_correct`,
`flat_to_riscv_correct`) plus a same-file `_functions_NoDup` lemma for the
validity half. Nothing in the parent proof depends on how any pass is proved;
only on its `phase_correct` type.

## Why it is good

1. The parent's proof is a single nested `exact` over the six children, nothing
   else: `unfold composed_compile` then one application of
   `compose_phases_correct` per link, closing in 9 lines
   ([lines 634-643](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/Pipeline.v#L634-L643)).
2. The file is built by CI: `.github/workflows/debian.yml` runs `make` on
   `master`, and `compiler/Makefile` compiles every `src/compiler/*.v`
   ([debian.yml lines 59-62](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/.github/workflows/debian.yml#L59-L62),
   [compiler/Makefile lines 39-48](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/Makefile#L39-L48)).
3. The decomposition is shallow: 7 direct lemmas in 9 glue lines, the longest
   project-lemma chain below the parent is 2 (`composed_compiler_correct` →
   `flattening_correct` → `flatten_functions_NoDup`), and the six pass lemmas
   have 50, 34, 48, 46, 32, 20 proof lines respectively
   ([flatten_functions_NoDup at lines 249-260, used at line 280](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/Pipeline.v#L249-L260)).
4. The authors kept the compositional core separate from the restatement:
   `compiler_correct` is introduced with the comment "restate
   composed_compiler_correct by unfolding definitions used to compose phases"
   ([line 681](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/Pipeline.v#L681)).
5. The one compositional lemma is reused, not re-proved:
   `compiler_correct` consumes it at
   [line 733](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/Pipeline.v#L733),
   and `compiler_correct_wp` consumes `compiler_correct` at
   [line 806](https://github.com/mit-plv/bedrock2/blob/b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b/compiler/src/compiler/Pipeline.v#L806).

In my opinion the detail worth copying is that the glue applies the children in
exactly the order of `composed_compile`, so the proof *is* the pipeline: a
reader can map each link of the `exact` to one pass without unfolding anything.

## When to use it, and when not

Use it when every pass already has a `phase_correct` (or an equivalent
per-pass simulation) lemma of the same shape, when the passes are composed in
one fixed order captured by a `composed_compile` definition, and when a
transitivity lemma such as `compose_phases_correct` exists. This is the
standard shape for a verified compiler: CompCert and the seL4-style per-pass
proofs work the same way.

Avoid it when a pass has no standalone lemma yet — the chain forces you to
write one lemma per pass before the glue can be written, so the real work is in
the per-pass lemmas, not the top-level theorem. Avoid it when the composition
order has to change, or a pass must be reused or reordered, or when two
consecutive passes share a language but the intermediate language is not
written out explicitly (the transitivity instances will not line up).

## Consequences

The move turns one large end-to-end simulation goal into one transitivity
lemma plus n per-pass `phase_correct` lemmas, so each hole is one whole
compiler pass — the natural unit for a bounded prover. Obligations: each child
must be a full `phase_correct` record (both the validity field and the
relational simulation field); the glue's application order must match
`composed_compile`; and the intermediate languages must be named so consecutive
`compose_phases_correct` instances typecheck. Failure mode: the glue does no
work itself, so a missing or misshaped per-pass lemma surfaces immediately as a
type error at the `exact`; and if two passes share a language the intermediate
must still be written out in the chain.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/debian.yml runs 'make' on push to master (default branch); root Makefile 'all' -> compiler_ex -> compiler_noex -> compiler/Makefile 'noex' compiles every *.v under src/compiler including Pipeline.v; commit b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b is pinned at ref HEAD | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Pipeline.v L634-643: Lemma composed_compiler_correct; proof is 'unfold composed_compile' (636) then a single 'exact' (637-642) applying nested compose_phases_correct over flattening_correct, useimmediate_correct, dce_correct, regalloc_correct, spilling_correct, riscv_phase_correct; Qed 643; no other tactic | verifier |
| 2 | verified | debian.yml L5-8 on push branches [master]; L59-62 run TIMED=1 make -j -k; root Makefile all (L161) includes compiler_ex->compiler_noex (L49-50,131-135) -> compiler/Makefile noex (L45-47) builds VS_NOEX = every *.v under src/compiler (L39,42), which contains Pipeline.v | verifier |
| 3 | verified | Parent 634-643 = 9 lines, applies 6 per-pass lemmas + compose_phases_correct. Pass proof lines (Proof..Qed inclusive): flattening_correct 275-324=50, useimmediate_correct 343-376=34, dce_correct 392-439=48, regalloc_correct 458-503=46, spilling_correct 553-584=32, riscv_phase_correct 603-622=20. Depth 2: flattening_correct uses flatten_functions_NoDup at L280 (defined 249, leaf) | verifier |
| 4 | verified | Pipeline.v L681 comment '(* restate composed_compiler_correct by unfolding definitions used to compose phases *)'; L682 'Lemma compiler_correct: forall' — matches the author-statement claim | verifier |
| 5 | verified | L733 'pose proof (phase_preserves_post (composed_compiler_correct p_funcs stack_hi ret_addr)) as C' inside compiler_correct; L806 'destruct (compiler_correct fs ...) as ...' inside compiler_correct_wp (lemma at L764) | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent composed_compiler_correct (Pipeline.v L634-643) is 'unfold composed_compile' then a single nested 'exact' over compose_phases_correct + the 6 per-pass lemmas flattening_correct/useimmediate_correct/dce_correct/regalloc_correct/spilling_correct/riscv_phase_correct; order matches composed_compile (L624-632) and consecutive instances typecheck (SrcLang->FlatWithStrVars->FlatWithStrVars->FlatWithStrVars->FlatWithZVars->FlatWithRegs->RiscvLang), so it closes. All 7 children are exactly the lemmas the parent uses. Each child closed_by matches its proof: split; validity via *_NoDup/spilling_preserves_valid/exact I; simulation via *_correct_aux/checker_correct/spill_fun_correct/flat_to_riscv_correct. Shape numbers right: direct_lemmas=7, depth=2 (parent->flattening_correct->flatten_functions_NoDup L280), glue_lines=9 (L635-643), child_lines=[15,50,34,48,46,32,20] sum 245=child_proof_lines_total. | reviewer-correctness |
| generality | accept | Move stated beyond the example: applicability.goal_shape abstracts to 'phase_correct L_first L_last composed' with a right-nested compose_phases and a two-field simulation record, and use_when names preconditions (per-pass phase_correct lemmas of one shape, one fixed composed_compile order, an available transitivity lemma) that do not depend on bedrock2; also_known_as maps it to CompCert-style pass composition. 'When not to use' is honest: it concedes the top-level proof is trivial and the real work sits in the per-pass lemmas (20-50 lines each, closed by bespoke *_correct_aux / checker_correct / spill_fun_correct / flat_to_riscv_correct, none by a single automated tactic), and lists concrete avoid conditions (no standalone phase_correct lemma yet, order/reuse changes, intermediate languages not written out). Consequences are specific (both record fields, glue order must match composed_compile, intermediate languages named; failure = type error at the exact). It says what makes the leaves good for a bounded prover: each pass lemma's statement is self-contained (a phase_correct between two named Lang instances), closes on its own via split + one imported per-pass lemma + a _functions_NoDup lemma, and the parent proof depends only on the phase_correct type, not on how any pass is proved. Minor, non-blocking: the prose 'CompCert and seL4-style per-pass proofs work the same way' is uncited (would be a stronger claim with a CompCert Compiler.v permalink), but it sits in README prose, not in entry claims. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are consistent and traceable. check_provenance passes (1 file byte-identical at b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b); the local copy compiler/src/compiler/Pipeline.v is 37416 bytes with sha256 514ccfb9... matching entry.json files[0]. Commit b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b is identical across source.json, SOURCE.md, entry.json and README; all permalinks use that full commit hash on mit-plv/bedrock2. Licence is MIT consistently (source.json licence, SOURCE.md detected MIT with upstream-LICENSE holding the MIT text, entry.json licence, README licence); MIT is permissive so no index withholding mark needed. Source note records pinned commit, browse URL, licence file and attribution. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/mit-plv/bedrock2 at commit `b4ec84bc6dbbd94e6ff778bbba1ab4c4808a3c6b`, under `MIT`; see the [source note](../../sources/bedrock2/SOURCE.md) for the licence text and attribution.
