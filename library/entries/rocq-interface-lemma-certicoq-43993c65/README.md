# Instantiation interface bundling three stage theorems for the Wasm toplevel

| | |
|---|---|
| Kind | instance |
| Move | interface-lemma |
| Language | rocq |
| Status | accepted |
| Source | [certicoq](../../sources/certicoq/SOURCE.md) at `943b52ae6547` |
| Licence | `MIT` |

## Intent

The LambdaANF-to-Wasm backend proves compilation in three stages, each a
separate theorem: the compiled module instantiates, the instantiation
invariants hold, and the post-instantiation instructions reduce to a good final
state. This entry records the interface theorem `instantiation_combined_INV_and_more`,
which bundles the three stages into one conjunction, so a client (the Wasm
top-level correctness proof) applies a single lemma and destructures its
conclusion instead of re-wiring the three stages.

## The decomposition

### parent `instantiation_combined_INV_and_more`: [`theories/CodegenWasm/LambdaANF_to_Wasm_instantiation.v` lines 2026-2116](https://github.com/CertiCoq/certicoq/blob/943b52ae654708130f241ccf8a50ecb95a7956e2/theories/CodegenWasm/LambdaANF_to_Wasm_instantiation.v#L2026-L2116) ([local copy](code/theories/CodegenWasm/LambdaANF_to_Wasm_instantiation.v))

```coq
Theorem instantiation_combined_INV_and_more : forall e fds num_funs module fenv main_lenv hs,
  NoDup (collect_function_vars (Efun fds e)) ->
  expression_restricted cenv (Efun fds e) ->
  correct_cenv_of_exp cenv (Efun fds e) ->
  num_funs = numOf_fundefs fds ->
  (Z.of_nat num_funs <= max_num_functions)%Z ->
  LambdaANF_to_Wasm nenv cenv penv (Efun fds e) = Ret (module, fenv, main_lenv) ->

exists sr fr,
  (* instantiate + post-instantiate *)
  instantiate' module hs sr fr /\
  INV fenv sr fr /\

  (* conclusions of module_instantiate_INV_and_more_hold *)

  inst_funcs (f_inst fr) = [:: 0%N & (funcidcs num_funs (N.of_nat num_custom_funs))] /\
  (* value relation holds for all funcs in fds *)
  (forall a , find_def a fds <> None ->
  	exists fidx : funcidx,
	    repr_funvar fenv a fidx /\
	    repr_val_LambdaANF_Wasm cenv fenv penv (Vfun (M.empty _) fds a) sr (f_inst fr) (Val_funidx fidx)) /\

  exists main_fn e' fns,
    main_fn = {| modfunc_type := 0%N (* [] -> [] *)
               ; modfunc_locals := map (fun _ : var => T_num T_i32) (collect_local_variables e)
               ; modfunc_body := e'
               |} /\
    s_funcs sr =
    [:: FC_func_native (Tf [::] [::]) (f_inst fr) main_fn
    &   map (fun f0 : wasm_function =>
             FC_func_native (Tf (repeat (T_num T_i32) (N.to_nat (type f0))) [::]) (f_inst fr)
             {| modfunc_type := type f0; modfunc_locals := locals f0; modfunc_body := body f0 |})
            fns
     ] /\
  (* links e and e' in main_fn above *)
  translate_body nenv cenv (create_local_variable_mapping (collect_local_variables e)) fenv penv e 0 = Ret e' /\
  (* translation of functions *)
  translate_functions nenv cenv fenv penv fds = Ret fns.
Proof.
  intros ??????? Hnodup HeRestr HcenvCorrect Hnumfuns HfnsLength LANF2Wasm.
  (* module instantiates *)
  have HINST := @module_instantiate _ nenv _  _ _ _ _ _ _ _ hs HcenvCorrect Hnodup LANF2Wasm.
  destruct HINST as [sr [fr [es_post Hinst]]].

  assert (HcenvCorrect' : (forall (f : var) (t : fun_tag) (ys : seq var) (e : exp),
             find_def f fds = Some (t, ys, e) ->
             correct_cenv_of_exp cenv e)). {
    intros.
    eapply Forall_constructors_subterm. eassumption.
    apply find_def_dsubterm_fds_e in H.
    apply t_step. apply dsubterm_fds. eassumption. }

  (* INV_instantiate hold after instantiation *)
  have HINST_INV := module_instantiate_INV_and_more_hold _ _ _ _ module fenv main_lenv sr fr es_post Hnodup HeRestr HcenvCorrect' Hnumfuns HfnsLength LANF2Wasm Hinst.
  destruct HINST_INV as [Hinv_inst [HinstFuncs [HvalRel [main_fn [e' [fns' [H_main [Hfuncs [HesPost [He Hfns]]]]]]]]]].

  assert (HfenvBound: (forall (f0 : var) (f' : u32),
             M.get f0 fenv = Some f' ->
             N.to_nat f' < num_funs + num_custom_funs)). {
    intros.
    unfold LambdaANF_to_Wasm in LANF2Wasm.
    remember (list_function_types (Z.to_nat max_function_args)) as ftypes.
    destruct (check_restrictions cenv (Efun fds e))=>//.
    destruct (translate_functions _ _ _ _ _) eqn:Hfuns=>//.
    rename l into fns. cbn in LANF2Wasm.
    destruct (translate_body nenv cenv _ _ _) eqn:Hexpr=>//.
    inv LANF2Wasm. rename l into wasm_main_instr.
    unfold create_fname_mapping in H.
    eapply var_mapping_list_lt_length' in H.
    now rewrite collect_function_vars_length in H. }

  (* post-instantiation *)
  have HinstPost := post_instantiation_reduce hs _ _ _ _ HfenvBound Hinv_inst Logic.eq_refl.
  destruct HinstPost as [sr' [HredPost [Hinv HfuncsEq]]].

  exists sr', fr.
  split.
  { unfold instantiate'.
    exists sr, fr, es_post. split. assumption.
    subst.
    apply translate_functions_length in Hfns.
    now rewrite -Hfns. }
  split. assumption.
  split. assumption.
  split.
  { intros ? HfdNone. apply HvalRel in HfdNone.
    destruct HfdNone as [fidx [Hvar Hval]].
    exists fidx. split=>//.
    by apply val_relation_func_depends_on_funcs with (s:=sr). }
  now exists main_fn, e', fns'.
Qed.
```

### child `module_instantiate`: [`theories/CodegenWasm/LambdaANF_to_Wasm_instantiation.v` lines 792-1081](https://github.com/CertiCoq/certicoq/blob/943b52ae654708130f241ccf8a50ecb95a7956e2/theories/CodegenWasm/LambdaANF_to_Wasm_instantiation.v#L792-L1081) ([local copy](code/theories/CodegenWasm/LambdaANF_to_Wasm_instantiation.v))

```coq
Theorem module_instantiate : forall e module fenv venv (hs : host_state),
  correct_cenv_of_exp cenv e ->
  NoDup (collect_function_vars e) ->
  LambdaANF_to_Wasm nenv cenv penv e = Ret (module, fenv, venv) ->
  exists sr fr es_post,
  instantiate initial_store module [] (sr, fr, es_post).
Proof.
  intros ????? Hcenv Hnodup H. unfold LambdaANF_to_Wasm in H.
  destruct (check_restrictions cenv e) eqn:Hrestr. inv H. destruct u.
  eapply check_restrictions_expression_restricted in Hrestr; last by apply rt_refl.
  destruct e =>//.
  destruct (translate_functions _ _ _ _ f) eqn:Hfuns. inv H.
  rename l into fns, f into fds. cbn in H.
  destruct (translate_body nenv cenv _ _) eqn:Hexpr. inv H.
  rename l into wasm_main_instr.

  remember (list_function_types (Z.to_nat max_function_args)) as ts. rewrite -Heqts in H.
  inversion H. clear H. cbn. rename venv into lenv.

  destruct (interp_alloc_module initial_store module []
             ((repeat (VAL_num (nat_to_value 0)) 4) ++ (repeat (VAL_num (nat_to_value64 0)) 4))
                                (elem_vals (Datatypes.length fns + num_custom_funs) 0))
        as [s' inst] eqn:HallocM.

  subst module.
  rewrite Heqts in HallocM.

  (* final store *)
  exists s'.
  (* module instance *)
  exists (Build_frame [] inst).
  (* es_post: instructions post-instantiation *)
  exists (concat (mapi_aux (0, [::]) (fun n : nat => get_init_expr_elem n)
                                     (table_element_mapping (length fns + num_custom_funs) 0))).
  (* import types *)
  exists []. exists [].

  (* export types *)
  exists ([:: ET_func (Tf [::] [::])] ++  (* main *)
         map (fun f => ET_func (Tf (repeat (T_num T_i32) (N.to_nat f.(type))) [::])) fns ++ (* all fns exported *)
         [:: ET_global {| tg_mut := MUT_var; tg_t := T_num T_i32 |}
           ; ET_global {| tg_mut := MUT_var; tg_t := T_num T_i32 |}
           ; ET_global {| tg_mut := MUT_var; tg_t := T_num T_i32 |}           (* global vars *)
           ; ET_mem {| lim_min := 1%N; lim_max := Some max_mem_pages|}]).     (* global mem *)
  exists hs.
  exists inst.
  (* initial values of globals: 0 *)
  exists ((repeat (VAL_num (nat_to_value 0)) 4) ++ (repeat (VAL_num (nat_to_value64 0)) 4)).
  (* element values (table entries) *)
  exists (elem_vals (length fns + num_custom_funs) 0).

  repeat split.
  (* module typing *) {
  - unfold module_typing. simpl.
    (* function types *)
    exists ([:: Tf [::] [::]] ++ (* main, fns *)
             map (fun f => Tf (repeat (T_num T_i32) (N.to_nat (type f)))[::]) fns).
    (* table types *)
    exists ([{| tt_limits := {| lim_min := N.of_nat (length fns + num_custom_funs);
                                lim_max := None |}
              ; tt_elem_type := T_funcref |}]).
    (* mem types *)
    exists [{| lim_min := 1%N; lim_max := Some max_mem_pages |}].
    (* global types *)
    exists ((repeat ({| tg_mut := MUT_var; tg_t := T_num T_i32 |}) 4) ++ (repeat ({| tg_mut := MUT_var; tg_t := T_num T_i64 |}) 4)).
    (* elem types *)
    exists (repeat T_funcref (length fns + num_custom_funs)).
    (* data types *)
    exists [].

    repeat split=>//.
    + (* func_types valid *)
      subst ts. by apply list_function_types_valid.
    + (* module_func_typing *)
      apply Forall2_cons.
      { (* main func *)
        subst ts. cbn. repeat split =>//.
        apply translate_body_correct in Hexpr.
        2:{ eapply Forall_constructors_subterm. eassumption.
            apply t_step. by apply dsubterm_fds2. }
        eapply repr_expr_LambdaANF_Wasm_typing =>//; last by eassumption.
        2: { (* expr restr *) by inv Hrestr. }
        repeat split =>//.
        * (* locals in bound *)
          intros ?? Hvar. cbn.
          unfold lookup_N. rewrite nth_error_map.
          destruct (nth_error _ (N.to_nat x')) eqn:Hcontra =>//.
          inv Hvar. apply var_mapping_list_lt_length in H.
          by apply nth_error_Some in H.
        * (* i32 globals *)
          intros var Hin. cbn.
          by repeat destruct Hin as [|Hin]; subst =>//.
        * (* i64 globals *)
          intros var Hin. cbn.
          by repeat destruct Hin as [|Hin]; subst =>//.
        * (* table *)
          eexists. cbn. split; reflexivity.
        * (* types *)
          intros ? Hmax. cbn. unfold max_function_args in Hmax. unfold lookup_N.
          erewrite nth_error_nth'; first rewrite nth_list_function_types =>//.
          by rewrite Nat2N.id. lia. rewrite length_list_function_types. lia.
          apply notNone_Some. rewrite <- map_repeat_eq.
          eexists. apply default_vals_i32_Some.
      }
      { (* funcs *)
        apply Forall2_spec.
        { rewrite length_map length_is_size length_is_size
            size_map -length_is_size.
          now erewrite <- mapi_length.
        }
        intros ?? [t1s t2s] Hnth1 Hnth2. cbn. unfold module_func_typing.
        repeat split =>//.
        rewrite nth_error_map in Hnth1. simpl in Hfuns.
        unfold unique_export_names in Hnth1.
        destruct (nth_error fns n) eqn:Hin. 2:{ by rewrite mapi_nth_error_None in Hnth1. }
        erewrite mapi_nth_error in Hnth1; eauto. cbn in Hnth1.
        destruct m. injection Hnth1 as <-<-<-.
        rewrite nth_error_map in Hnth2. rewrite Hin in Hnth2.
        injection Hnth2 as Hnth2. subst t1s t2s.
        assert (n = N.to_nat (fidx w) - num_custom_funs).
        { eapply translate_functions_nth_error_idx; eauto. } subst n.

        have H' := translate_functions_exists_original_fun fds fds fns
          _ _ _ _ Hnodup Hfuns Logic.eq_refl (nth_error_In _ _ Hin).
        destruct H' as [f [t [ys [e1 [Hfd [Htype Hvarr]]]]]].

        assert (HcenvFds : (forall (f : var) (t : fun_tag) (ys : seq var) (e : exp),
            find_def f fds = Some (t, ys, e) -> correct_cenv_of_exp cenv e)). {
          intros ???? Hfd'.
          eapply Forall_constructors_subterm. eassumption.
          apply t_step. apply dsubterm_fds. now eapply find_def_dsubterm_fds_e.
        }
        have H' := translate_functions_find_def fds _ _ _ _ e1 _ _ Hnodup Hfuns Hfd HcenvFds.

        destruct H' as [f' [e' [locs [func [Hvar [-> [Hin' [<- [Hty [Hlocs [<- Hexpr']]]]]]]]]]].
        assert (func = w). {
          assert (Heq: fidx func = fidx w). {
            inv Hvar. inv Hvarr. congruence.
          }
          apply In_nth_error in Hin'. destruct Hin' as [j Hj].
          assert (j = N.to_nat (fidx func) - num_custom_funs).
            eapply translate_functions_nth_error_idx; try apply Hfuns; eauto.
          congruence.
        } subst w. clear Hvarr Hin'.

        split. { inv Hrestr.
          apply H5 in Hfd. destruct Hfd as [Hfd _].
          unfold lookup_N. erewrite nth_error_nth'.
          rewrite nth_list_function_types; auto. lia.
          rewrite length_list_function_types. lia. }
        split.
        eapply repr_expr_LambdaANF_Wasm_typing =>//; last by apply Hexpr'.
        { (* context restrictions *)
          repeat split =>//.
          * (* locs i32 *)
            intros ?? Hvar'.
            rewrite Hlocs Htype Nat2N.id. unfold lookup_N. cbn.
            rewrite <-repeat_app, <-length_app.
            apply nth_error_repeat. inv Hvar'. now eapply var_mapping_list_lt_length.
          * (* i32 globals *)
            intros ? Hin'. cbn. by repeat destruct Hin' as [|Hin']; subst =>//.
          * (* i64 globals *)
            intros ? Hin'. cbn. by repeat destruct Hin' as [|Hin']; subst =>//.
          * (* table *)
            eexists. cbn. unfold lookup_N. split; reflexivity.
          * (* length *)
            cbn. subst ts. rewrite length_list_function_types. lia.
          * (* types *)
            intros ? Hmax. unfold lookup_N. cbn. subst ts.
            erewrite nth_error_nth'. rewrite nth_list_function_types.
            now rewrite Nat2N.id. lia.
            rewrite length_list_function_types. lia.
        }
        { inv Hfd. inv Hrestr. now eapply H4. }
        { rewrite Hlocs. apply notNone_Some. eexists. apply default_vals_i32_Some. }
      }
    + (* module_table_typing *)
      apply Forall2_cons. unfold module_table_typing, tabletype_valid, limit_valid_range. cbn.
      assert (HfnsBound: (N.of_nat (Datatypes.length fns + num_custom_funs) <= 4294967295)%N).
      { apply translate_functions_length in Hfuns. rewrite -Hfuns.
        inv Hrestr. unfold num_custom_funs.
        unfold max_num_functions in H6. lia. }
      apply N.leb_le in HfnsBound. rewrite HfnsBound. by apply /eqtable_typeP.
      apply Forall2_nil.
    + (* module_mem_typing *)
      apply Forall2_cons=>//.
    + (* module_glob_typing *)
      repeat (apply Forall2_cons; repeat split; try by apply bet_const_num =>//).
      by apply Forall2_nil.
    + (* module_elem_typing *)
      simpl. eapply module_typing_module_elem_typing=>//. clear HallocM.
      simpl. { intros n Hn. unfold lookup_N in Hn. apply nth_error_Some in Hn. cbn in Hn.
        rewrite length_is_size size_map -length_is_size in Hn.
        apply nodup_In. simpl. apply in_or_app. left.
        apply nodup_In. apply funcidx_in_table_element_mapping with (idx:=0).
        unfold num_custom_funs. lia. }
    + (* module_export_typing *)
      apply Forall2_cons.
      { (* main func *)
        now cbn. }
      apply Forall2_app.
      { (* fns *)
        intros. cbn.
        apply Forall2_spec. { repeat rewrite length_map. now erewrite <-mapi_length. }
        intros ??? Hnth1 Hnth2. rewrite nth_error_map in Hnth2.
        destruct (nth_error fns n) eqn:Hnth =>//.
        rewrite nth_error_map in Hnth1.
        unfold unique_export_names in Hnth1.
        erewrite mapi_nth_error in Hnth1; eauto. cbn in Hnth1.
        destruct m. injection Hnth1 as <-<-.
        injection Hnth2 as <-.
        assert (n = N.to_nat (fidx w) - num_custom_funs). {
          now eapply translate_functions_nth_error_idx; eauto. } subst n. cbn.
        assert (Hbounds: (N.of_nat num_custom_funs <= fidx w < N.of_nat (length fns + num_custom_funs))%N). {
          eapply translate_functions_idx_bounds; eauto.
          2:{ apply In_map. now eapply nth_error_In. }
          intros. split; first by apply local_variable_mapping_gt_idx in H; lia.
          apply var_mapping_list_lt_length' in H.
          rewrite collect_function_vars_length in H.
          erewrite (translate_functions_length _ fns) in H; eauto. lia.
        }
        unfold num_custom_funs in *. unfold lookup_N.
        destruct (N.to_nat (fidx w)) eqn:Hidx; first by lia. cbn in Hnth.
        rewrite Nat.sub_0_r in Hnth. cbn.
        rewrite nth_error_map. rewrite Hnth. by apply /eqfunction_typeP.
      }
      (* global vars, memory *)
      repeat apply Forall2_cons =>//.
      (* export names unique *)
      apply /eqseqP.
      apply nodup_fixed_point. cbn.
      erewrite map_app, map_map. cbn.
      have H' := unique_export_name_NoDup fns _ Logic.eq_refl.
destruct H' as [HnoDup H_].
      eapply Permutation_NoDup.
      have Hperm := Permutation_app_rot _
                      [ String.print main_function_name ]
                      (List.map (fun x : wasm_function => String.print (export_name x))
                      (unique_export_names fns)).
      apply Hperm.
      repeat (constructor; first
                (intro Hc; repeat (destruct Hc as [Hc|Hc]=>//); by apply H_ in Hc)).
      assumption.
    }
  - (* imports typing *)
    by apply Forall2_nil.
  - (* imports subtyping *)
    by apply Forall2_nil.
  - (* alloc_module is true *) { cbn.
    unfold interp_alloc_module, initial_store in HallocM.
    destruct (alloc_funcs _ _ _) eqn:Hfuncs.
    have Hfuncs' := Hfuncs.
    apply alloc_func_iota_N in Hfuncs.
    rewrite <- Heqts in *. (* prevent unfolding of types *)
    cbn in HallocM.

    destruct Hfuncs as [Hfuncs1 [Hfuncs2 [Hfuncs3 [Hfuncs4 [Hfuncs5 [Hfuncs6 Hfuncs7]]]]]].
    cbn in Hfuncs1, Hfuncs2, Hfuncs3, Hfuncs4, Hfuncs5, Hfuncs6, Hfuncs7.

    destruct (alloc_elems _ _ _) eqn:Helems.
    injection HallocM as <-<-.
    have Helems' := Helems.
    apply alloc_elem_iota_N in Helems. cbn in Helems.
    rewrite Hfuncs2 -Hfuncs3 -Hfuncs4 -Hfuncs5 -Hfuncs6 -Hfuncs7 in Helems.
    (*  clear Hfuncs2 Hfuncs3 Hfuncs4 Hfuncs5 Hfuncs6 Hfuncs7. *)
    destruct Helems as [Helems1 [Helems2 [Helems3 [Helems4 [Helems5 [Helems6 Helems7]]]]]].
    cbn in Helems1, Helems2, Helems3, Helems4, Helems5, Helems6, Helems7.

    rewrite Hfuncs'. rewrite Helems'. cbn. clear Hfuncs' Helems'.
    (* rewrite Helems1. -Helems2. Helems3. -Helems4 -Helems5. *)

    rewrite Hfuncs1 -Hfuncs3 -Hfuncs4 -Hfuncs5.
    repeat split=>//.
    by rewrite table_element_mapping_length elem_vals_length. }
  - (* instantiate globals *)
    unfold instantiate_globals. cbn.
    repeat (apply Forall2_cons; first by apply rt_refl).
    by apply Forall2_nil.
  - (* instantiate elem *)
    unfold instantiate_elems. cbn. unfold interp_alloc_module in HallocM.
    destruct (alloc_funcs _ _ _) eqn:Hfuncs.
    apply alloc_func_iota_N in Hfuncs. cbn in Hfuncs. cbn in HallocM.
    destruct (alloc_elems _ _) eqn:Helems.
    injection HallocM as <-.
    apply elems_instantiate. subst inst. cbn.
    rewrite Nat.add_comm. rewrite length_map.
    unfold unique_export_names. now erewrite <-mapi_length.
  - by rewrite cats0.
Unshelve. all: apply (Tf [] []).
Qed.
```

### child `module_instantiate_INV_and_more_hold`: [`theories/CodegenWasm/LambdaANF_to_Wasm_instantiation.v` lines 1183-1458](https://github.com/CertiCoq/certicoq/blob/943b52ae654708130f241ccf8a50ecb95a7956e2/theories/CodegenWasm/LambdaANF_to_Wasm_instantiation.v#L1183-L1458) ([local copy](code/theories/CodegenWasm/LambdaANF_to_Wasm_instantiation.v))

```coq
Theorem module_instantiate_INV_and_more_hold : forall eAny e fds num_funs module fenv main_lenv sr f es_post,
  NoDup (collect_function_vars (Efun fds eAny)) ->
  expression_restricted cenv (Efun fds e) ->
  (forall (f : var) (t : fun_tag) (ys : seq var) (e : exp),
      find_def f fds = Some (t, ys, e) -> correct_cenv_of_exp cenv e) ->
  num_funs = numOf_fundefs fds ->
  (Z.of_nat num_funs <= max_num_functions)%Z ->
  LambdaANF_to_Wasm nenv cenv penv (Efun fds e) = Ret (module, fenv, main_lenv) ->
  (* instantiate with the two imported functions *)
  instantiate initial_store module [] (sr, f, es_post) ->

  (* invariants hold initially *)
  INV_instantiation sr f (num_funs + num_custom_funs) /\
  inst_funcs (f_inst f) = [:: 0%N & (funcidcs num_funs (N.of_nat num_custom_funs))] /\
  (* value relation holds for all funcs in fds *)
  (forall a, find_def a fds <> None ->
	   exists fidx : funcidx,
	     repr_funvar fenv a fidx /\
	     repr_val_LambdaANF_Wasm cenv fenv penv (Vfun (M.empty _) fds a)
                                            sr (f_inst f) (Val_funidx fidx)) /\

  exists main_fn e' fns,
    main_fn = {| modfunc_type := 0%N (* [] -> [] *)
               ; modfunc_locals := map (fun _ : var => T_num T_i32) (collect_local_variables e)
               ; modfunc_body := e'
               |} /\
    s_funcs sr =
    [:: FC_func_native (Tf [::] [::]) (f_inst f) main_fn
    &   map (fun f0 : wasm_function =>
             FC_func_native (Tf (repeat (T_num T_i32) (N.to_nat (type f0))) [::]) (f_inst f)
             {| modfunc_type := type f0; modfunc_locals := locals f0; modfunc_body := body f0 |})
            fns
     ] /\
  es_post = concat (mapi_aux (0, [::]) (fun n : nat => get_init_expr_elem n)
                             (table_element_mapping (Datatypes.length fns + num_custom_funs) 0)) /\
  (* links e and e' in main_fn above *)
  translate_body nenv cenv
          (create_local_variable_mapping
             (collect_local_variables e)) fenv penv e 0 = Ret e' /\
  (* translation of functions *)
  translate_functions nenv cenv fenv penv fds = Ret fns.
Proof.
  intros eAny e fds num_funs module fenv lenv s f es_post Hnodup HeRestr HcenvCorrect ->
    HfnsLength Hcompile Hinst.
  unfold instantiate in Hinst.
  unfold LambdaANF_to_Wasm in Hcompile.
  remember (list_function_types (Z.to_nat max_function_args)) as types.
  destruct (check_restrictions cenv (Efun fds e)) eqn:HRestr. inv Hcompile.
  destruct (translate_functions nenv cenv _ penv fds) eqn:HtransFns. inv Hcompile. simpl in Hcompile.
  destruct (translate_body nenv cenv _ _ _) eqn:Hexpr. inv Hcompile. rename l0 into e'.
  inv Hcompile.
  unfold INV_instantiation. unfold is_true in *.
  destruct Hinst as [t_imps_mod [t_imps [t_exps [state [mi [ g_inits [r_inits
    [Hmodule [Himports [HimportsSt [HallocModule [HinstGlobals [HinstElem [Hframe HinitExprs]]]]]]]]]]]]]].
  rename l into fns. cbn in HinitExprs.

  (* globals red. to const *)
  unfold instantiate_globals in HinstGlobals. cbn in HinstGlobals.
  inv HinstGlobals. inv H3. inv H5. inv H6. inv H7. inv H8. inv H9. inv H10. cbn in H1.
  apply reduce_trans_value with (v1:=VAL_num (nat_to_value 0)) in H1, H2, H3, H4.
  apply reduce_trans_value with (v1:=VAL_num (nat_to_value64 0)) in H5, H6, H7, H8.
  subst y y0 y1 y2 y3 y4 y5 y6.
  unfold alloc_module, alloc_funcs, alloc_globs, add_mem, alloc_Xs in HallocModule.
  cbn in HallocModule. repeat rewrite map_app in HallocModule. cbn in HallocModule.
  destruct (fold_left _ (map _ (unique_export_names fns)) _) eqn:HaddF.
  destruct (alloc_elems _ _ _) eqn:HallocElems.
  apply alloc_elem_iota_N in HallocElems. 2:{ by apply Forall2_length in HinstElem. }
  cbn in HallocElems.
  destruct HallocElems as [-> [E0 [E1 [E2 [E3 [E4 E5]]]]]].

  destruct HallocModule as [<- [F0 [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]]]].
  cbn in HaddF.
  rewrite table_element_mapping_length in F5.

  (* main fn *)
  destruct (add_func initial_store _) eqn:HaddF'.
  unfold add_func, gen_func_instance in HaddF'. rewrite F0 in HaddF'.
  replace (Pos.to_nat 100) with 100 in HaddF' by reflexivity. cbn in HaddF'.
  replace (Pos.to_nat 1) with 1 in HaddF' by reflexivity. cbn in HaddF'.
  injection HaddF' as <- <- <- <- <- <-.

  apply add_funcs_effect in HaddF. cbn in HaddF.
  destruct HaddF as [Hs01 [Hs02 [Hs03 [Hs04 [Hs05 [Hs06 ->]]]]]].

  rewrite <- Hs01 in *. rewrite <- Hs02 in *. rewrite <- Hs03 in *.
  rewrite <- Hs04 in *. rewrite <- Hs05 in *. rewrite -> Hs06 in *. cbn in F0.
  (* clear Hs01 Hs02 Hs03 Hs04. *)
  cbn in E0, E1, E2, E3, E4, E5.
  cbn in F0, F1, F2, F3, F4.
  rewrite length_map in F1. rewrite rev_app_distr in F1.
  rewrite rev_involutive in F1. cbn in F1.

  split.
  (* INV *)
  unfold INV_glob_result_writable, INV_glob_out_of_mem_writable,
    INV_glob_mem_ptr_writable, INV_glob_cap_writable, INV_i64_glob_tmps_writable.
  unfold global_var_w, supdate_glob, supdate_glob_s.
  cbn. rewrite F4.
  split. (* res_var_w *)   eexists. rewrite -E3. reflexivity.
  split. (* res_var_M_w *) eexists. rewrite -E3. reflexivity.
  split. (* res_var_M_0 *) unfold INV_glob_out_of_mem_is_zero. unfold sglob_val, sglob.
  cbn. rewrite F4. rewrite -E3. reflexivity.
  split. (* gmp_w *) eexists. rewrite -E3. reflexivity.
  split. (* cap_w *) eexists. rewrite -E3. reflexivity.
  (* globals mut i32 *)
  split.
  unfold INV_globals_all_mut, globals_all_mut, globals_all_mut32, globals_all_mut64.
  split; intros. unfold lookup_N in H1.
  {
    unfold glob_result, glob_out_of_mem, glob_mem_ptr, glob_cap in *.
    cbn in H0; try subst gidx; try rewrite F4 in H0; unfold lookup_N in H0.
    rewrite -E3 in H1. cbn in H1.
    destruct (N.to_nat gidx) eqn:Hgidx. cbn in H0.
    replace g with 0%N in * by congruence. inv H1. now eexists.
    destruct n. cbn in H0.
    replace g with 1%N in * by congruence. inv H1. now eexists.
    destruct n. cbn in H0.
    replace g with 2%N in * by congruence. inv H1. now eexists.
    destruct n. cbn in H0.
    replace g with 3%N in * by congruence. inv H1. now eexists.
    repeat (try destruct H;[now subst gidx|]).
    now inv H.
  }
  {
    unfold glob_tmp1, glob_tmp2, glob_tmp3, glob_tmp4 in *.
    cbn in H0; try subst gidx; try rewrite F4 in H0; unfold lookup_N in H0.
    rewrite -E3 in H1.
    destruct (List.in_inv H).
    { subst gidx. replace (N.to_nat 4) with 4 in * by now cbn. inv H0. inv H1. now eexists. }
    destruct (List.in_inv H2).
    { subst gidx. replace (N.to_nat 5) with 5 in * by now cbn. inv H0. inv H1. now eexists. }
    destruct (List.in_inv H3).
    { subst gidx. replace (N.to_nat 6) with 6 in * by now cbn. inv H0. inv H1. now eexists. }
    destruct (List.in_inv H4).
    { subst gidx. replace (N.to_nat 7) with 7 in * by now cbn. inv H0. inv H1. now eexists. }
    now inv H5.
  }
  split. (* linmem *)
  { unfold INV_linear_memory. unfold smem. cbn. rewrite F3.
    split; auto. unfold smem. eexists; auto.
    split. rewrite -E2. reflexivity.
    eexists. split. reflexivity.
    split. reflexivity.
    unfold max_mem_pages, gen_mem_instance, mem_size, mem_length. cbn.
    rewrite memory.mem_make_length. cbn. lia. }
   split. (* gmp in linmem *)
   { unfold INV_glob_mem_ptr_in_linear_memory.
     unfold sglob_val, sglob. cbn. intros ?? Hm Hm0 Hbound. unfold smem in Hm.
     rewrite F3 in Hm0, Hm. rewrite -E2 in Hm. rewrite -E3 F4 in Hm0.
     inv Hm. inv Hm0.
     cbn.
     unfold gen_mem_instance, mem_length. rewrite memory.mem_make_length. cbn.
     rewrite Wasm_int.Int32.Z_mod_modulus_id in H0; lia. }
   split. (* all locals i32 *)
   { unfold INV_locals_all_i32. intros. rewrite nth_error_nil in H. inv H. }
   split. (* num functions upper bound *)
   { unfold INV_num_functions_bounds, max_num_functions.
     split.
     - cbn. rewrite -E0. cbn.
       do 2! rewrite length_map.
       inv HtransFns.
       unfold unique_export_names. erewrite <-mapi_length; eauto.
       erewrite <- translate_functions_length; eauto.
       unfold max_num_functions in HfnsLength. simpl_modulus. cbn. lia.
     - cbn. rewrite F5. rewrite iota_N_length. unfold num_custom_funs.
       erewrite <- translate_functions_length; eauto.
       unfold max_num_functions in HfnsLength. lia. }
   split. (* inst_globals (f_inst f) no dups *)
   unfold INV_inst_globals_nodup. rewrite F4.
   repeat constructor; cbn; lia.
  split. (* types *)
  { unfold INV_types. intros. unfold stypes. cbn. unfold max_function_args in H.
    rewrite F0. unfold lookup_N. erewrite nth_error_nth'.
    rewrite nth_list_function_types =>//. lia.
    rewrite length_list_function_types. lia. }
  split. (* gmp multiple of two *)
  { unfold INV_glob_mem_ptr_multiple_of_two.
    intros ?? Hm Hgmp Hbound. exists 0%N.
    unfold glob_mem_ptr, sglob_val, sglob in Hgmp.
    rewrite -E3 in Hgmp. cbn in Hgmp. rewrite F4 in Hgmp. inv Hgmp.
    rewrite Wasm_int.Int32.Z_mod_modulus_id in H0; lia. }
  split. (* inst_funcs_id *)
  { unfold INV_inst_funcs_id. intros ? Hbound. cbn. rewrite F1. unfold lookup_N.
    remember (N.to_nat i) as i'.
    destruct (Nat.leb_spec i' 0).
    { (* n <= 0 *)
      do 1 (destruct i'; cbn; f_equal; try lia). }
    { (* 0 < n *)
      separate_instr. (* rewrite catA. *)
      erewrite nth_error_app2=>//. cbn.
      erewrite nth_error_funcidcs; eauto.
      f_equal. lia. unfold num_custom_funs in *.
      rewrite -E0 in Hbound. cbn in Hbound.
      do 2! rewrite length_map in Hbound. lia. }
  }
  split. (* i64 globs writable *)
  { intros gidx [Htmp1 | [Htmp2 | [Htmp3 | [Htmp4 | Hfls]]]]; intro v.
    all: eexists; unfold glob_tmp1, glob_tmp2, glob_tmp3, glob_tmp4 in *; auto; subst gidx.
    all: rewrite -E3; cbn; unfold Pos.to_nat in *; rewrite F4; reflexivity.
  }
  split. (* instantiation_elems *)
  { unfold INV_instantiation_elems.
    apply translate_functions_length in HtransFns. split.
    - intros. erewrite init_elems_effect; eauto.
      f_equal; lia. rewrite F1.
      unfold unique_export_names. erewrite <- mapi_length; eauto.
      by rewrite Nat.add_comm. congruence.
    - rewrite F5. cbn. congruence.
  }
  (* instantiate table *)
  { unfold INV_instantiation_table_empty. cbn. split.
    - rewrite F2. reflexivity.
    - rewrite -E1. cbn.
      apply translate_functions_length in HtransFns. repeat f_equal; try lia.
  }
  split. (* inst_funcs (f_inst f) *)
  { rewrite F1. repeat f_equal.
    inv HtransFns; auto.
    unfold unique_export_names. erewrite <-mapi_length;eauto.
    symmetry. eapply translate_functions_length. eassumption. }
  split. (* val relation holds for functions *)
  { intros. apply notNone_Some in H. destruct H as [[[v' ys'] e''] Hfd].

    have H' := translate_functions_find_def _ _ _ _ _ _ _ _ e'' _ _ Hnodup HtransFns Hfd HcenvCorrect.
    destruct H' as [fidx [e''' [? [func [? [? [? [? [? [? [? ?]]]]]]]]]]].
    subst. eauto.
    exists (fidx func).
    split. { inv H. now econstructor. }
    econstructor; eauto. rewrite -E0. cbn.
    unfold lookup_N.
    assert ((N.to_nat (fidx func)) >= num_custom_funs). {
      inv H. apply local_variable_mapping_gt_idx in H0. lia. }

    assert (nth_error fns ((N.to_nat (fidx func)) - num_custom_funs) = Some func). {
      apply In_nth_error in H1. destruct H1 as [j Hj].
      erewrite <- translate_functions_nth_error_idx; eauto. }
    unfold num_custom_funs in *.

    assert (HnodupFns: NoDup fns). {
      assert (Hinj: map_injective (create_fname_mapping (Efun fds e))). {
        by apply create_local_variable_mapping_injective. }
      have H' := translate_functions_NoDup _ _ _ _ _ _ _ _ Logic.eq_refl Hinj Hnodup HtransFns.
      now eapply NoDup_map_inv.
    }

    destruct (N.to_nat (fidx func)). lia. cbn.
    replace (_ - _) with n in H2 by lia.

    do 2! rewrite nth_error_map.
    unfold unique_export_names.
    erewrite mapi_nth_error; eauto.
    cbn. f_equal. unfold gen_func_instance.
    rewrite F0. cbn. f_equal. rewrite H4.
    assert (HtypeBound : (type func <= 100)%N). {
      inv HeRestr.
      eapply translate_functions_type_bound; eauto.
    }
    unfold lookup_N. erewrite nth_error_nth'. 2:{ rewrite length_list_function_types. lia. }
    rewrite nth_list_function_types; try lia.
    rewrite H3. by rewrite Nat2N.id.
  }
  (* from exists statement on *)
  eexists. exists e', fns. split=>//. rewrite -E0.
  split. do 4 f_equal. cbn.
  rewrite <- map_map_seq.
  { clear Hmodule E1.
    rewrite unique_export_names_preserves_functions=>//.
    rewrite gen_fun_instance_simplify_eq; eauto.
    - apply translate_functions_length in HtransFns.
      rewrite -HtransFns. lia.
    - intros. inv HeRestr.
      eapply translate_functions_type_bound; eauto. }
	split; first by rewrite cats0.
  split=>//.
Unshelve. all: by repeat constructor.
```

### child `post_instantiation_reduce`: [`theories/CodegenWasm/LambdaANF_to_Wasm_instantiation.v` lines 1888-2016](https://github.com/CertiCoq/certicoq/blob/943b52ae654708130f241ccf8a50ecb95a7956e2/theories/CodegenWasm/LambdaANF_to_Wasm_instantiation.v#L1888-L2016) ([local copy](code/theories/CodegenWasm/LambdaANF_to_Wasm_instantiation.v))

```coq
Theorem post_instantiation_reduce {fenv} : forall hs sr fr fr' num_funs,
  (forall f f', M.get f fenv = Some f' -> N.to_nat f' < num_funs) ->
  INV_instantiation sr fr num_funs ->
  f_inst fr = f_inst fr' ->
  exists sr',
    reduce_trans (hs, sr, fr', [seq AI_basic i | i <- concat
                                 (mapi
                                   (fun n : nat => get_init_expr_elem n)
                                   (table_element_mapping num_funs 0))])
                 (hs, sr', fr', [::]) /\
  INV fenv sr' fr /\
  s_funcs sr = s_funcs sr'.
Proof.
  intros ????? Hfenv Hinv Hfinst.
  unfold INV_instantiation in *.
  destruct Hinv as [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]]]]].
  destruct H15 as [HiT HsT].
  destruct H14 as [HsE HiE].

  assert (HiE1': (forall i : nat,
      i < num_funs + 0 -> nth_error (inst_elems (f_inst fr')) i = Some (N.of_nat i))). {
    intros ? Hn. rewrite Nat.add_0_r in Hn. rewrite -Hfinst.
    rewrite HiE. rewrite iota_N_lookup. f_equal. apply /ssrnat.leP. lia. }
  assert (HsE': (forall i : N,
    0 <= N.to_nat i < num_funs + 0 ->
    selem sr (f_inst fr') i = Some {| eleminst_type := T_funcref; eleminst_elem := [:: VAL_ref_func i] |})). {
    intros. rewrite -Hfinst. apply HsE. lia. }

  assert (Hempty1: (forall i : N,
      N.to_nat i < 0 ->
      selem sr (f_inst fr') i = Some {| eleminst_type := T_funcref; eleminst_elem := [::] |})). {
    intros. lia. }
  assert (Hempty2: (forall i : N,
      N.to_nat i < 0 ->
      stab_elem sr (f_inst fr') 0%N i = Some (VAL_ref_func i))). {
    intros. lia. }

  assert (HiE2': Datatypes.length (inst_elems (f_inst fr')) = num_funs + 0). {
    rewrite -Hfinst HiE. rewrite iota_N_length. lia.
  }

  remember ({| tableinst_type := {| tt_limits := {| lim_min := N.of_nat num_funs; lim_max := None |}
                                  ; tt_elem_type := T_funcref
                                  |}
             ; tableinst_elem := repeat (VAL_ref_null T_funcref) num_funs
             |}) as t.
  assert (HsT' : stab sr (f_inst fr') 0%N = Some t). {
    unfold stab. by rewrite HsT -Hfinst HiT. }
  assert (Htabsize: tab_size t = num_funs). { subst t. cbn. by rewrite repeat_length. }
  assert (HTtype : tt_elem_type (tableinst_type t) = T_funcref). { subst t. reflexivity. }

  assert (Hnumfuns: num_funs <= Z.to_nat max_num_functions + num_custom_funs). {
    destruct H8 as [Hbound1 Hbound2].
    rewrite Nat.add_0_r in HiE2'.
    rewrite -HiE2' -Hfinst. lia. }

  rewrite Hfinst in HiT.
  have H' := post_instantiation_reduce_aux num_funs 0 hs sr fr' t HiE1' HiE2' HsT' HTtype Htabsize Hnumfuns HsE'  Hempty1 Hempty2.
  destruct H' as [sr' [Hred [Htab [_ [Hfuncs [Hmems Hglobals]]]]]].
  exists sr'.
  split. apply Hred.
  split=>//.
  (* INV holds now *)
  unfold INV.
  split. (* glob_result writable *)
    intro. intros. destruct (H val) as [s Hs].
    unfold global_var_w, supdate_glob, supdate_glob_s, sglob, sglob_ind in *.
    repeat rewrite Hglobals in Hs.
    destruct (lookup_N (inst_globals (f_inst fr)) glob_result)=>//. cbn. cbn in Hs.
    rewrite <- Hglobals in *.
    destruct (lookup_N (s_globals sr) g)=>//. eexists. reflexivity.
  split. (* glob_out_of_mem writable *)
    intro. intros. destruct (H0 val) as [s Hs].
    unfold global_var_w, supdate_glob, supdate_glob_s, sglob, sglob_ind in *.
    repeat rewrite Hglobals in Hs.
    destruct (lookup_N (inst_globals (f_inst fr)) glob_out_of_mem)=>//. cbn. cbn in Hs.
    rewrite <- Hglobals in *.
    destruct (lookup_N (s_globals sr) g)=>//. eexists. reflexivity.
  split. (* glob_result is 0 *)
  unfold INV_glob_out_of_mem_is_zero, sglob_val, sglob, sglob_ind in *.
    by repeat rewrite <- Hglobals in *.
  split. (* glob_mem_ptr writable *)
    intro. intros. destruct (H2 val) as [s Hs].
    unfold global_var_w, supdate_glob, supdate_glob_s, sglob, sglob_ind in *.
    repeat rewrite Hglobals in Hs.
    destruct (lookup_N (inst_globals (f_inst fr)) glob_mem_ptr)=>//. cbn. cbn in Hs.
    rewrite <- Hglobals in *.
    destruct (lookup_N (s_globals sr) g)=>//. eexists. reflexivity.
  split. (* glob_cap writable *)
    intro. intros. destruct (H3 val) as [s Hs].
    unfold global_var_w, supdate_glob, supdate_glob_s, sglob, sglob_ind in *.
    repeat rewrite Hglobals in Hs.
    destruct (lookup_N (inst_globals (f_inst fr)) glob_cap)=>//. cbn. cbn in Hs.
    rewrite <- Hglobals in *.
    destruct (lookup_N (s_globals sr) g)=>//. eexists. reflexivity.
  split. (* globals all mut i32s *)
    unfold INV_globals_all_mut, globals_all_mut, globals_all_mut32, globals_all_mut64.
    rewrite -Hglobals. assumption.
  split. (* linear memory *)
    unfold INV_linear_memory, smem. by rewrite -Hmems.
  split. (* glob_mem_ptr in linear mem *)
    unfold INV_glob_mem_ptr_in_linear_memory. unfold smem, sglob_val, sglob, sglob_ind.
    rewrite - Hglobals. by rewrite -Hmems.
  split. (* locals all i32s *)
    assumption.
  split. (* num funcs bound *)
    unfold INV_num_functions_bounds. by rewrite -Hfuncs.
  split. (* globals nodup *)
    assumption.
  split. (* table id mapping *)
    unfold INV_table_id. intros ?? Htrans. rewrite Hfinst.
    apply Htab. inv Htrans. apply Hfenv in H14. lia.
  split. (* types *)
    assumption.
  split. (* glob_mem_ptr multiple of 2 *)
    unfold INV_glob_mem_ptr_multiple_of_two, sglob_val, sglob, sglob_ind, smem.
    rewrite -Hglobals. rewrite -Hmems. assumption.
  (* inst funcs id mapping *)
  split.
    unfold INV_inst_funcs_id. rewrite -Hfuncs. assumption.
    unfold INV_i64_glob_tmps_writable.
    intros. intro.
    destruct (H13 gidx H14 val) as [s Hs].
    unfold global_var_w, supdate_glob, supdate_glob_s, sglob, sglob_ind in *.
    repeat rewrite Hglobals in Hs.
    destruct (lookup_N (inst_globals (f_inst fr)) gidx)=>//. cbn. cbn in Hs.
    rewrite <- Hglobals in *.
    destruct (lookup_N (s_globals sr) g)=>//. eexists. reflexivity.
Qed.
```

How the parts fit. The parent's proof is 91 lines of glue that applies the
three stages in order and assembles their conclusions:

1. `module_instantiate` (stage 1) yields `sr, fr, es_post` with
   `instantiate initial_store module [] (sr, fr, es_post)` (line 2067).
2. A small `assert` re-derives `correct_cenv_of_exp` for each function body in
   `fds` (lines 2070-2076), discharging the stronger per-function hypothesis
   stage 2 needs.
3. `module_instantiate_INV_and_more_hold` (stage 2) yields `INV_instantiation`,
   `inst_funcs`, the value relation, and the reconstructed `main_fn`, `e'`,
   `fns` (line 2079).
4. Another `assert` derives the `fenv` bound `N.to_nat f' < num_funs +
   num_custom_funs` (lines 2082-2095).
5. `post_instantiation_reduce` (stage 3) yields the post-instantiation reduction
   and the final `INV` and `s_funcs` preservation (line 2098).
6. The parent then `exists sr', fr` and closes each conjunct of its statement
   by destructuring what the stages returned (lines 2101-2115), using
   `val_relation_func_depends_on_funcs` to lift the value relation to `sr'`.

Lemma graph (an arrow means "applied by"):

```text
instantiation_combined_INV_and_more
├── module_instantiate                     (stage 1, line 2067)
├── module_instantiate_INV_and_more_hold   (stage 2, line 2079)
└── post_instantiation_reduce              (stage 3, line 2098)
        └── post_instantiation_reduce_aux  (helper, line 1679 of the same file)
```

Why each child is a good leaf:

- `module_instantiate` is a self-contained statement — "the compiled module
  instantiates to some store, frame and post-instantiation instructions" — whose
  proof constructs the witnesses and closes by `repeat split` over the
  `instantiate` relation, then `Unshelve. all: apply (Tf [] []).`. It closes on
  its own from the compile hypothesis.
- `module_instantiate_INV_and_more_hold` states exactly the invariant-and-relation
  bundle the client needs. Its proof unfolds the `instantiate` and compile
  relations and re-proves each conjunct, closing on its own with
  `Unshelve. all: by repeat constructor.` (the proof is terminated by `Qed.` at
  line 1458).
- `post_instantiation_reduce` reduces the post-instantiation instruction list and
  preserves the invariant. It calls the same-file helper
  `post_instantiation_reduce_aux` for the reduction and preservation facts, then
  re-proves `INV` by `split` into its conjuncts, each closed by rewriting with
  the preservation facts.

The second copied file, `toplevel_theorem.v`, is where the interface is consumed:
the top-level correctness theorem `LambdaANF_Wasm_related` applies
`instantiation_combined_INV_and_more` once (line 95) and destructures the result,
rather than re-applying the three stages. This is what makes the interface a
real abstraction boundary rather than a convenience: the client never touches
`module_instantiate`, `module_instantiate_INV_and_more_hold` or
`post_instantiation_reduce`.

## Why it is good

1. The parent's proof cites `module_instantiate` (check; line 2067).
2. The parent's proof cites `module_instantiate_INV_and_more_hold` (check; line 2079).
3. The parent's proof cites `post_instantiation_reduce` (check; line 2098).
4. The interface's glue proof is 91 lines (2026-2116), assembled from three
   separately-proved stage theorems of 290, 276 and 129 lines (measurement;
   direct_lemmas 3, checked depth 2 via `post_instantiation_reduce` →
   `post_instantiation_reduce_aux`).
5. The Wasm top-level correctness theorem `LambdaANF_Wasm_related` obtains
   `instantiate'`, `INV`, the function-index map and the value relation by one
   application of `instantiation_combined_INV_and_more` (known-use;
   `toplevel_theorem.v:95-97`), without re-applying the three stages.

In my opinion the detail worth copying is the *direction* of the split: the
three stages are proved bottom-up as independent theorems, and the interface is
a thin forward theorem whose proof is only the wiring (two `assert`s and three
`have`s), so the top-level simulation proof stays short and never re-derives the
instantiation argument.

## When to use it, and when not

Use it when several stage theorems are already proved separately and one or
more clients would otherwise re-apply them in a fixed order with shared
assumptions (`correct_cenv_of_exp`, `NoDup`, the function-count bound here). The
interface theorem bundles the stages and discharges those shared assumptions
once; the client destructures the conjunction. It fits the abstraction-boundary
pattern of `interface-lemma`: the client stops unfolding the pipeline and names
one fact.

Avoid it when the stages are not yet proved separately — the interface then
carries the whole proof burden in one place, which is harder to split across
bounded provers. Avoid it too when different clients need different subsets of
the stages: a single conjunction hides the parts, so a client that only needs
`module_instantiate` would have to unfold the interface or reach for the stage
theorem directly.

## Consequences

The interface theorem is a conjunction, so each conjunct becomes an obligation
the client discharges by destructuring rather than by proving; the client writes
no new proof for the pipeline, but its destructuring must stay in sync with the
interface if a stage's conclusion changes. The glue assumes the three stages are
already proved, and it is the single place to update if a stage's assumptions
change (here the glue re-derives two hypotheses — the per-function
`correct_cenv_of_exp` and the `fenv` bound — that the stages could not take
directly). Because the interface hides the three stages, a client that needs
only one stage must either unfold the interface or use the stage theorem
directly, which couples it to the pipeline's internals.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/nix-action-default.yml (push to main builds CertiRocq job via coq-nix-toolbox; theories/_CoqProject lists CodegenWasm/LambdaANF_to_Wasm_instantiation.v, built by 'make all'); commit 943b52ae654708130f241ccf8a50ecb95a7956e2 on default branch main | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: module_instantiate@theories/CodegenWasm/LambdaANF_to_Wasm_instantiation.v:2067, module_instantiate_INV_and_more_hold@theories/CodegenWasm/LambdaANF_to_Wasm_instantiation.v:2039, post_instantiation_reduce@theories/CodegenWasm/LambdaANF_to_Wasm_instantiation.v:2098; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at 943b52ae654708130f241ccf8a50ecb95a7956e2 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, module_instantiate) -> cites: module_instantiate occurs at theories/CodegenWasm/LambdaANF_to_Wasm_instantiation.v:2067 | check_claims.py |
| 2 | verified | cites(parent, module_instantiate_INV_and_more_hold) -> cites: module_instantiate_INV_and_more_hold occurs at theories/CodegenWasm/LambdaANF_to_Wasm_instantiation.v:2039 | check_claims.py |
| 3 | verified | cites(parent, post_instantiation_reduce) -> cites: post_instantiation_reduce occurs at theories/CodegenWasm/LambdaANF_to_Wasm_instantiation.v:2098 | check_claims.py |
| 4 | verified | checked copied LambdaANF_to_Wasm_instantiation.v: parent Theorem at 2026, Qed at 2116 (91 lines); module_instantiate 792-1081 (290); module_instantiate_INV_and_more_hold 1183-1458 (276); post_instantiation_reduce 1888-2016 (129); 3 children; post_instantiation_reduce_aux declared at 1679 and called at 1945 inside post_instantiation_reduce (depth 2) | verifier |
| 5 | verified | toplevel_theorem.v:95-97 has LambdaANF_Wasm_related applying @instantiation_combined_INV_and_more once and destructuring [sr [fr [Hinst [Hinv [HinstFuncs [HfVal ...]]]]]]; grep shows no application of module_instantiate / module_instantiate_INV_and_more_hold / post_instantiation_reduce (only a comment at 111) | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent instantiation_combined_INV_and_more (lines 2026-2116, 91 lines) closes with Qed and applies the three children exactly as claimed: @module_instantiate at 2067, module_instantiate_INV_and_more_hold at 2079, post_instantiation_reduce at 2098. Each child statement matches entry.json verbatim and each closing method matches the code (module_instantiate: 'Unshelve. all: apply (Tf [] []).'; module_instantiate_INV_and_more_hold: 'Unshelve. all: by repeat constructor.' then Qed at 1458; post_instantiation_reduce: Qed, and it calls post_instantiation_reduce_aux (declared 1679) at 1945). Shape numbers are right: direct_lemmas=3, depth=2 (reduce -> reduce_aux), glue_lines=91 (2116-2026+1), child_lines 290/276/129 all correct. Known-use claim 5 confirmed at toplevel_theorem.v:95-97 (single application + destructuring yielding Hinst/Hinv/HinstFuncs/HfVal). | reviewer-correctness |
| generality | accept | Generality: the move is stated beyond the example — 'when to use' and applicability give general conditions (stages proved separately; clients that would re-apply them in fixed order with shared assumptions like correct_cenv_of_exp/NoDup/the bound, so the client names one fact instead of unfolding the pipeline). 'When not to use' is honest and specific (stages not yet proved -> interface carries the whole burden; different clients need different subsets -> conjunction hides the parts). Consequences are honest and specific (destructuring must stay in sync; glue is the single update point; single-stage clients couple to internals). The entry says what makes the lemmas good bounded-prover leaves: 'Why each child is a good leaf' states each stage theorem is self-contained and closes on its own, and I confirmed Qed termination at 1081, 1458, 2016; the known-use client applies the interface once and destructures (toplevel_theorem.v:95-96). | reviewer-generality |
| provenance-licence | accept | Commit 943b52ae654708130f241ccf8a50ecb95a7956e2 is recorded consistently in entry.json, source.json and SOURCE.md. check_provenance.py passes: both copied files (theories/CodegenWasm/LambdaANF_to_Wasm_instantiation.v, toplevel_theorem.v) are byte-identical at that commit, so every file/site permalink resolves to the recorded commit. Licence MIT is recorded in entry.json, source.json and SOURCE.md, and the copied upstream-LICENSE.md is the genuine MIT text matching the label. SOURCE.md carries attribution and a link to LICENSE.md at the pinned commit. Everything is traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/CertiCoq/certicoq at commit `943b52ae654708130f241ccf8a50ecb95a7956e2`, under `MIT`; see the [source note](../../sources/certicoq/SOURCE.md) for the licence text and attribution.
