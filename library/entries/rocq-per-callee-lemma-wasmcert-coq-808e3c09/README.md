# Executable instantiation soundness assembled from per-component lemmas

| | |
|---|---|
| Kind | instance |
| Move | per-callee-lemma |
| Language | rocq |
| Status | accepted |
| Source | [wasmcert-coq](../../sources/wasmcert-coq/SOURCE.md) at `58a3d3f8b7af` |
| Licence | `MIT` |

## Intent

The executable instantiation `interp_instantiate hs s m v_imps` returns, on
success, a store, a frame and an init-expression list; the relational
specification `instantiate` (`instantiation_spec.v` 629-643) is an existential
over witnesses plus a conjunction of component obligations. This proof
discharges each conjunct with one soundness lemma per component (module type
checker, external type checker, allocator, global and element initialisers,
plus the bit-level type-checker reflection), so the headline theorem is a glue
that `destruct`s the executable run, supplies the witnesses with `exists`, and
closes each goal with `repeat split`.

## The decomposition

### parent `interp_instantiate_imp_instantiate`: [`theories/interp_instantiate_sound.v` lines 246-402](https://github.com/WasmCert/WasmCert-Coq/blob/58a3d3f8b7af4dc8aa9351f254a9e672643b21f8/theories/interp_instantiate_sound.v#L246-L402) ([local copy](code/theories/interp_instantiate_sound.v))

```coq
Lemma interp_instantiate_imp_instantiate : forall hs hs' s m v_imps s_end f bes str,
  interp_instantiate hs s m v_imps = (Some (hs', s_end, f, bes), str) ->
  instantiate s m v_imps (s_end, f, bes).
Proof.
  move => hs hs' s m v_imps s_end f bes str.
  unfold interp_instantiate, instantiate.
  move => Hinterp.
  destruct (module_type_checker m) as [[[t_imps_mod t_exps]|] str'] eqn:Hmodcheck => //.
  destruct (those _) as [t_imps | ] eqn:Hextcheck => //.
  destruct (all2 import_subtyping _ _) eqn:Hextsubtyping => //.
  destruct (get_global_inits _ _ (mod_globals m)) as [g_inits |] eqn:Hglobinit => //.
  destruct (get_elem_inits _ _ (mod_elems m)) as [r_inits |] eqn:Heleminit => //.
  destruct (interp_alloc_module s m v_imps g_inits r_inits) as [s' inst'] eqn:Halloc => //.
  injection Hinterp as <- <- Heq.

  exists t_imps_mod, t_imps, t_exps, hs, inst', g_inits, r_inits.

  (* Proving these first so they can be used in the reasoning for initialisers later *)
  assert (module_typing m t_imps_mod t_exps) as Hmodtype; first by eapply module_type_checker_sound; eauto.
  
  assert (alloc_module s m v_imps g_inits r_inits (s', inst')) as Hallocmodule.
  { apply interp_alloc_sound => //.
    - by apply those_length in Hglobinit; rewrite length_is_size size_map -length_is_size in Hglobinit.
    - by apply those_length in Heleminit; rewrite length_is_size size_map -length_is_size in Heleminit.
  }
  
  assert (List.Forall2 (external_typing s) v_imps t_imps) as Hexttype.
  { apply Forall2_spec.
    - apply those_length in Hextcheck.
      by rewrite List.length_map in Hextcheck.
    - move => n vext text Hnthv Hntht.
      apply external_type_checker_sound.
      eapply those_map_lookup in Hextcheck as [text' [Hmap Hnth]]; eauto.
      by simplify_multieq.
  }
  
  assert (Hgvs_len : length g_inits = length m.(mod_globals)).
  {
    apply those_length in Hglobinit.
    rewrite length_is_size size_map in Hglobinit.
    by rewrite length_is_size.
  }
  
  assert (Hrvs_len : length r_inits = length m.(mod_elems)).
  {
    apply those_length in Heleminit.
    rewrite length_is_size size_map in Heleminit.
    by rewrite length_is_size.
  }

  (* store *)
  unfold interp_alloc_module in Halloc.
  destruct (alloc_funcs _ _ _) as [s1 ifs] eqn:Hallocfuncs.
  destruct (alloc_tabs _ _) as [s2 its] eqn:Halloctabs.
  destruct (alloc_mems _ _) as [s3 ims] eqn:Hallocmems.
  destruct (alloc_globs _ _) as [s4 igs] eqn:Hallocglobs.
  destruct (alloc_elems _ _) as [s5 ies] eqn:Hallocelems.
  destruct (alloc_datas _ _) as [s6 ids] eqn:Hallocdatas.

  injection Halloc as <- Heqinst.
  specialize (alloc_func_iota_N Hallocfuncs) as Hfuncaddrs.
  specialize (alloc_table_iota_N Halloctabs) as Htableaddrs.
  specialize (alloc_mem_iota_N Hallocmems) as Hmemaddrs.
  specialize (alloc_global_iota_N Hallocglobs Hgvs_len) as Hglobaladdrs.
  specialize (alloc_elem_iota_N Hallocelems Hrvs_len) as Helemaddrs.
  specialize (alloc_data_iota_N Hallocdatas) as Hdataaddrs.

  extract_premise.

  destruct s, s1, s2, s3, s4, s5, s6; simpl in *.
  repeat split => //.
  - (* subtyping *)
    by eapply Forall2_all2_impl; eauto.
  - (* global initialisers -- hardest case, since it's the main difference in the 
       executable version *)
    unfold instantiate_globals.
    apply Forall2_spec => //.
    move => n mglob gv Hnth1 Hnth2.
    eapply those_map_lookup in Hglobinit as [gi [Hmap Hnth]]; last by eauto.
    apply module_typecheck_glob_aux in Hmodcheck as [C Hmodcheck].
    unfold module_global_type_checker in Hmodcheck.
    eapply all_projection in Hmodcheck; eauto.
    destruct mglob.
    move/andP in Hmodcheck.
    destruct Hmodcheck as [Hconstexpr Hbetype].
    move/b_e_type_checker_reflects_typing in Hbetype.
    eapply const_exprs_impl in Hconstexpr; last by eauto.
    destruct Hconstexpr as [e [-> Hconst]].
    unfold const_expr in Hconst.
    destruct e => //; subst; simpl in Hmap.
    1,2,3: (* const_num/const_vec/ref_null *)
      injection Hmap as <-;
      simpl in *;
      simplify_multieq;
      by constructor.
    { (* ref_func *)
      remove_bools_options; simplify_multieq.
      by constructor; apply r_ref_func => /=.
    }
    { (* global_get *)
      remove_bools_options; simplify_multieq.
      constructor; apply r_global_get => /=.
      unfold sglob_val, sglob, sglob_ind in *; simpl in *.
      remove_bools_options.
      unfold lookup_N in *.
      by erewrite nth_error_app_Some; eauto.
    }
  - subst.
    unfold instantiate_elems.
    apply Forall2_spec => //.
    move => n melem vs Hnth1 Hnth2.
    eapply those_map_lookup in Heleminit as [ei [Hmap Hnth]]; last by eauto.
    apply module_typecheck_elem_aux in Hmodcheck as [C Hmodcheck].
    unfold module_elem_type_checker in Hmodcheck.
    eapply all_projection in Hmodcheck; eauto.
    destruct melem.
    move/andP in Hmodcheck; destruct Hmodcheck as [Hmodcheck Hmode].
    move/andP in Hmodcheck; destruct Hmodcheck as [Hconstexpr Hbetype].
    simplify_multieq.
    apply Forall2_spec => //=.
    + apply those_length in Hmap.
      by rewrite List.length_map in Hmap; simpl in Hmap.
    + move => i bes vref Hnthinit Hnthei.
      eapply all_projection in Hbetype; eauto.
      eapply all_projection in Hconstexpr; eauto.
      eapply those_map_lookup in Hmap as [vref' [Hmap Hnth']]; eauto.
      move/b_e_type_checker_reflects_typing in Hbetype.
      eapply const_exprs_impl in Hconstexpr; last by eauto.
      destruct Hconstexpr as [e [-> Hconst]].
      unfold const_expr in Hconst.
      destruct e => //; subst; simpl in Hmap.
      { (* ref_null *)
        injection Hmap as <-.
        simpl in *.
        simplify_multieq.
        by constructor.
      }
      { (* ref_func *)
        remove_bools_options; simplify_multieq.
        constructor => /=.
        unfold interp_get_vref in Hmap.
        simpl in Hmap; remove_bools_options.
        by apply r_ref_func.
      }
      { (* global_get *)
        unfold interp_get_vref in Hmap; simpl in Hmap.
        remove_bools_options; simplify_multieq; destruct v => //.
        injection Hmap as ->.
        constructor.
        replace (vref_to_e vref') with (v_to_e (VAL_ref vref')) => //.
        eapply r_global_get => /=.
        unfold sglob_val, sglob, sglob_ind in *; simpl in *.
        remove_bools_options.
        unfold lookup_N in *.
        by erewrite nth_error_app_Some; eauto.
      }
Qed.
```

### child `module_type_checker_sound`: [`theories/interp_instantiate_sound.v` lines 16-174](https://github.com/WasmCert/WasmCert-Coq/blob/58a3d3f8b7af4dc8aa9351f254a9e672643b21f8/theories/interp_instantiate_sound.v#L16-L174) ([local copy](code/theories/interp_instantiate_sound.v))

```coq
Lemma module_type_checker_sound: forall m t_imps t_exps str,
  module_type_checker m = (Some (t_imps, t_exps), str) ->
  module_typing m t_imps t_exps.
Proof.
  move => m t_imps t_exps str Hmodcheck.
  unfold module_type_checker in Hmodcheck.
  destruct m.
  destruct (gather_m_f_types mod_types mod_funcs) as [fts | ] eqn:Hmftypes => //;
                                                                               destruct (module_imports_typer mod_types mod_imports) as [impts | ] eqn:Hmitypes => //.
  destruct (gather_m_e_types (ext_t_tables impts ++ map modtab_type mod_tables) mod_elems) as [ets | ] eqn:Hmetypes => //.
  destruct (gather_m_d_types (ext_t_mems impts ++ map modmem_type mod_mems) mod_datas) as [dts | ] eqn:Hmdtypes => //.
  destruct (all _ _ && _ && _ && _ && _ && _ && _ && _ && _) eqn:Hallcond => //.
  destruct (module_exports_typer _ mod_exports) eqn:Hmexptypes => //.
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hnameunique].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hstartcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hdatacheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Helemcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hglobalcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hmemcountcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hmemcheck].
  move/andP in Hallcond; destruct Hallcond as [Hfunccheck Htablecheck].
  unfold module_typing.
  injection Hmodcheck as ->->.
  
  exists fts, (map modtab_type mod_tables), (map modmem_type mod_mems), (gather_m_g_types mod_globals), ets, dts.
  repeat split => //.

  (* types *)
  { by apply Forall_spec => //. }
  
  (* funcs *)
  { clear - Hfunccheck Hmftypes hfc.
    unfold gather_m_f_types in Hmftypes.
    apply Forall2_spec => //; first by apply those_length in Hmftypes; rewrite List.length_map in Hmftypes.
    move => n mfunc [tx ty] Hfuncnth Hftsnth.
    eapply all_projection in Hfunccheck; eauto.
    eapply those_map_lookup in Hmftypes as [ft [Hmap Hnth]]; eauto.
    destruct mfunc, ft.
    unfold gather_m_f_type in Hmap.
    Opaque type_checker.b_e_type_checker.
    simpl in *.
    simplify_multieq.
    split => //.
    rewrite Hmap in Hfunccheck.
    remove_bools_options.
    split => //; last by apply/eqP.
    by apply/b_e_type_checker_reflects_typing.
  }
  (* tables *)
  { apply Forall2_spec => //; first by rewrite List.length_map.
    move => n mtable [tx ty] Htablenth Hftsnth.
    eapply all_projection in Htablecheck; eauto.
    simpl in *.
    unfold module_table_typing, module_table_type_checker in *; rewrite Htablecheck => /=.
    apply nth_error_map in Hftsnth as [mtab [??]].
    simplify_multieq.
    by apply/eqP.
  }
  (* memories *)
  { apply Forall2_spec => //; first by rewrite List.length_map.
    move => n mmem [tx ty] Hmemnth Hftsnth.
    eapply all_projection in Hmemcheck; eauto.
    simpl in *.
    unfold module_mem_typing, module_mem_type_checker in *; rewrite Hmemcheck => /=.
    apply nth_error_map in Hftsnth as [mtab [??]].
    simplify_multieq.
    by apply/eqP.
  }
  (* globals *)
  { clear -Hglobalcheck hfc.
    unfold gather_m_g_types.
    apply Forall2_spec; first by rewrite List.length_map.
    move => n mglob gt Hgnth Hmgnth.
    erewrite List.map_nth_error in Hmgnth; last by eauto.
    injection Hmgnth as <-.
    unfold module_global_typing.
    destruct mglob => /=.
    eapply all_projection in Hglobalcheck; eauto.
    unfold module_global_type_checker in Hglobalcheck.
    move/andP in Hglobalcheck; destruct Hglobalcheck as [? Hbet].
    repeat split => //.
    by move/b_e_type_checker_reflects_typing in Hbet.
  }
  (* elem *)
  { clear -Helemcheck Hmetypes hfc.
    unfold gather_m_e_types in Hmetypes.
    apply Forall2_spec => //; first by apply those_length in Hmetypes; rewrite List.length_map in Hmetypes.
    move => n x tref Hnthelem Hntht.
    eapply those_map_lookup in Hmetypes as [t [Hmap Hnth]]; eauto; simpl in *.
    simplify_multieq.
    eapply all_projection in Helemcheck; eauto.
    unfold module_elem_typing.
    unfold module_elem_type_checker in Helemcheck.
    destruct x; simpl in *.
    move/andP in Helemcheck; destruct Helemcheck as [Helemcheck Hmode].
    move/andP in Helemcheck; destruct Helemcheck as [Hconst Hbet].
    assert (t = modelem_type) as Hteq.
    { unfold gather_m_e_type in Hmap.
      destruct modelem_mode; simpl in *; try by inversion Hmap.
      by remove_bools_options.
    }
    subst t.
    repeat split => //.
    { apply Forall_spec.
      move => m be Hnth.
      split.
      - by eapply all_projection in Hconst; eauto.
      - eapply all_projection in Hbet; eauto.
        by move/b_e_type_checker_reflects_typing in Hbet.
    }
    { unfold module_elem_mode_checker in Hmode; destruct modelem_mode; simpl in * => //.
      remove_bools_options.
      eexists; split; first by eauto.
      destruct t0; repeat split => //.
      by move/b_e_type_checker_reflects_typing in H1.
    }
  }
  (* data *)
  { clear -Hdatacheck Hmdtypes hfc.
    unfold gather_m_d_types in Hmdtypes.
    apply Forall2_spec => //; first by apply those_length in Hmdtypes; rewrite List.length_map in Hmdtypes.
    move => n x tref Hnthdata Hntht.
    eapply those_map_lookup in Hmdtypes as [t [Hmap Hnth]]; eauto; simpl in *.
    simplify_multieq.
    eapply all_projection in Hdatacheck; eauto.
    unfold module_data_typing.
    unfold module_data_type_checker in Hdatacheck.
    destruct x; simpl in *.
    unfold module_data_mode_checker in Hdatacheck; destruct moddata_mode; simpl in * => //; try repeat split => //; remove_bools_options => //.
    eexists; split; first by eauto.
    repeat split => //.
    by move/b_e_type_checker_reflects_typing in H.
  }
  (* imports *)
  { clear - Hmitypes.
    unfold module_imports_typer in Hmitypes.
    apply Forall2_spec; first by apply those_length in Hmitypes; rewrite List.length_map in Hmitypes.
    move => n mi extt Hminth Htinth.
    eapply those_map_lookup in Hmitypes as [Htext [Hmap Hnth]]; eauto.
    simplify_multieq.
    destruct mi; simpl in *.
    unfold module_import_desc_typer in Hmap.
    unfold module_import_typing.
    destruct imp_desc; apply/eqP => /=; remove_bools_options => //; by rewrite eq_refl.
  }
  (* exports *)
  { clear - Hmexptypes.
    unfold module_exports_typer in Hmexptypes.
    apply Forall2_spec; first by apply those_length in Hmexptypes; rewrite List.length_map in Hmexptypes.
    move => n me extt Hmexpth Htexpth.
    eapply those_map_lookup in Hmexptypes as [Htext [Hmap Hnth]]; eauto.
    simplify_multieq.
    destruct me; simpl in *.
    unfold module_export_typer in Hmap.
    unfold module_export_typing.
    simpl in *.
    destruct modexp_desc => //=; remove_bools_options; unfold module_export_desc_typing => /=; rewrite Hoption; by apply/eqP.
  }
Qed.
```

### child `external_type_checker_sound`: [`theories/interp_instantiate_sound.v` lines 176-183](https://github.com/WasmCert/WasmCert-Coq/blob/58a3d3f8b7af4dc8aa9351f254a9e672643b21f8/theories/interp_instantiate_sound.v#L176-L183) ([local copy](code/theories/interp_instantiate_sound.v))

```coq
Lemma external_type_checker_sound: forall s ext t,
  external_type_checker s ext = Some t ->
  external_typing s ext t.
Proof.
  move => s ext t Hextcheck.
  unfold external_type_checker in Hextcheck; move/eqP in Hextcheck.
  by destruct ext; destruct t => //; remove_bools_options; subst.
Qed.
```

### child `interp_alloc_sound`: [`theories/interp_instantiate_sound.v` lines 185-216](https://github.com/WasmCert/WasmCert-Coq/blob/58a3d3f8b7af4dc8aa9351f254a9e672643b21f8/theories/interp_instantiate_sound.v#L185-L216) ([local copy](code/theories/interp_instantiate_sound.v))

```coq
Lemma interp_alloc_sound: forall s m v_imps g_inits r_inits s' inst,
  length g_inits = length m.(mod_globals) ->
  length r_inits = length m.(mod_elems) ->
  interp_alloc_module s m v_imps g_inits r_inits = (s', inst) ->
  alloc_module s m v_imps g_inits r_inits (s', inst).
Proof.
  move => s m v_imps g_inits r_inits s' inst Hgvs_len Hrvs_len Halloc.
  unfold interp_alloc_module in Halloc.
  unfold alloc_module; simpl in *.
  destruct (alloc_funcs _ _ _) as [s1 ifs] eqn:Hallocfuncs.
  destruct (alloc_tabs _ _) as [s2 its] eqn:Halloctabs.
  destruct (alloc_mems _ _) as [s3 ims] eqn:Hallocmems.
  destruct (alloc_globs _ _) as [s4 igs] eqn:Hallocglobs.
  destruct (alloc_elems _ _) as [s5 ies] eqn:Hallocelems.
  destruct (alloc_datas _ _) as [s6 ids] eqn:Hallocdatas.

  injection Halloc as <-<-.
  rewrite Hallocfuncs Halloctabs Hallocmems Hallocglobs Hallocelems Hallocdatas => /=.
  apply alloc_func_iota_N in Hallocfuncs.
  apply alloc_table_iota_N in Halloctabs.
  apply alloc_mem_iota_N in Hallocmems.
  apply alloc_global_iota_N in Hallocglobs; last assumption.
  apply alloc_elem_iota_N in Hallocelems; last assumption.
  apply alloc_data_iota_N in Hallocdatas.

  extract_premise.

  destruct s, s1, s2, s3, s4, s5, s6; simpl in *.
  subst.
  repeat rewrite List.length_map.
  by repeat rewrite eq_refl => /=.
Qed.
```

### child `module_typecheck_glob_aux`: [`theories/interp_instantiate_sound.v` lines 220-231](https://github.com/WasmCert/WasmCert-Coq/blob/58a3d3f8b7af4dc8aa9351f254a9e672643b21f8/theories/interp_instantiate_sound.v#L220-L231) ([local copy](code/theories/interp_instantiate_sound.v))

```coq
Lemma module_typecheck_glob_aux: forall m t_imps t_exps str,
    module_type_checker m = (Some (t_imps, t_exps), str) ->
    exists c, all (module_global_type_checker c) m.(mod_globals).
Proof.
  move => m t_imps t_exps str.
  unfold module_type_checker.
  move => Hmodcheck.
  destruct m.
  remove_bools_options.
  simpl in *.
  by eexists; eauto.
Qed.
```

### child `module_typecheck_elem_aux`: [`theories/interp_instantiate_sound.v` lines 233-244](https://github.com/WasmCert/WasmCert-Coq/blob/58a3d3f8b7af4dc8aa9351f254a9e672643b21f8/theories/interp_instantiate_sound.v#L233-L244) ([local copy](code/theories/interp_instantiate_sound.v))

```coq
Lemma module_typecheck_elem_aux: forall m t_imps t_exps str,
    module_type_checker m = (Some (t_imps, t_exps), str) ->
    exists c, all (module_elem_type_checker c) m.(mod_elems).
Proof.
  move => m t_imps t_exps str.
  unfold module_type_checker.
  move => Hmodcheck.
  destruct m.
  remove_bools_options.
  simpl in *.
  by eexists; eauto.
Qed.
```

### child `b_e_type_checker_reflects_typing`: [`theories/type_checker_reflects_typing.v` lines 1527-1610](https://github.com/WasmCert/WasmCert-Coq/blob/58a3d3f8b7af4dc8aa9351f254a9e672643b21f8/theories/type_checker_reflects_typing.v#L1527-L1610) ([local copy](code/theories/type_checker_reflects_typing.v))

```coq
Lemma b_e_type_checker_reflects_typing:
  forall C bes tf,
    reflect (be_typing C bes tf) (b_e_type_checker C bes tf).
Proof.
  move => C bes tf.
  destruct tf as [tn tm].
  destruct (b_e_type_checker C bes (Tf tn tm)) eqn: Htc_bool.
  - apply ReflectT.
    unfold b_e_type_checker, b_e_type_checker_aux in Htc_bool.
    fold (check (context_reverse C) bes (Some <<(rev tn), false>>)) in Htc_bool.
    remove_bools_options.
    eapply tc_to_bet_list in Htc_bool; eauto.
    destruct Htc_bool as [ts [Hagree Hbet]].
    unfold c_types_agree in Hagree; simpl in *.
    apply values_subtyping_rev in Hagree.
    rewrite -> revK in *.
    eapply bet_subtyping; eauto.
    eapply instr_subtyping_weaken1; first reflexivity; by resolve_subtyping.
  - apply ReflectF.
    move => Hbet.
    assert (b_e_type_checker C bes (Tf tn tm)) as H; (try by rewrite H in Htc_bool); clear Htc_bool.
    induction Hbet; subst => //=; (try rewrite H); unfold type_update, type_update_top, produce; simplify_tc_goal; (try by unfold c_types_agree in *; simplify_tc_goal).
    (* Ref_func *)
    + move/inP in H0.
      by rewrite H0.
    + rewrite value_type_select_refl => //.
      unfold c_types_agree.
      by simplify_tc_goal.
    (* Br_table *)
    + apply common_lab_cond in H as [ty [Hcommon Hsub]]; last by destruct ins.
      apply common_lab_rev in Hcommon.
      rewrite Hcommon.
      apply values_subtyping_rev in Hsub.
      specialize consume_subtyping with (ct1 := << rev ty ++ rev t1s, false >>) (ct1' := << rev ts ++ rev t1s, false >>) (ct2 := << rev t1s, false >>) (ts := rev ty) as Hconsume.
      destruct Hconsume as [ct2' [Hconsume' Hctsub]].
      { by apply consume_prefix. }
      { apply ct_subtyping_prefix => //.
        by apply ct_subtyping_refl.
      }
      { rewrite Hconsume'.
        by unfold c_types_agree; simplify_tc_goal.
      }
    (* Call *)
    + destruct tf as [t1 t2] => /=.
      by unfold c_types_agree, type_update; simplify_tc_goal.
    (* Composition *)
    + rewrite List.fold_left_app => //=.
      rewrite Hoption0.
      destruct (List.fold_left _ es _) as [ct_res | ] eqn:Htc => //=.
      injection Hoption0 as <-.
      assert (ct_res <ct: (<<rev t2s, false>>)) as Hctsub.
      { unfold ct_subtyping; rewrite IHHbet1 => /=; by rewrite eq_refl; lias. }
      eapply check_single_subtyping in Hoption as [ct2' [Hcheck Hagree]]; eauto.
      rewrite Hcheck.
      by eapply c_types_agree_subtyping; eauto; resolve_subtyping.
    (* Subtyping *)
    + simplify_subtyping.
      apply values_subtyping_rev in Hconjl2.
      apply values_subtyping_rev in Hconjr0.
      apply values_subtyping_rev in Hconjl1.
      simplify_tc_goal.
      destruct c as [cts [|]].
      { eapply check_extend_top with (ts2 := rev extr0) in Hoption; eauto.
        eapply check_subtyping with (ct1' := <<rev extr1 ++ rev extr, false>>) in Hoption as [ct' [Hcheck Hagree]]; eauto; last by unfold ct_subtyping, c_types_agree => /=; resolve_subtyping => //.
        fold (check (context_reverse C) es (Some <<rev extr1 ++ rev extr, false>>)).
        rewrite Hcheck.
        apply c_types_agree_extend_top with (ts := rev extr0) in IHHbet.
        eapply c_types_agree_subtyping; eauto.
        by resolve_subtyping.
      }
      { eapply check_extend with (ts2 := rev extr0) in Hoption; eauto.
        eapply check_subtyping with (ct1' := <<rev extr1 ++ rev extr, false>>) in Hoption as [ct' [Hcheck Hagree]]; eauto; last by unfold ct_subtyping, c_types_agree => /=; resolve_subtyping => //.
        fold (check (context_reverse C) es (Some <<rev extr1 ++ rev extr, false>>)).
        rewrite Hcheck.
        unfold ct_subtyping, c_types_agree in *; destruct ct' as [cts' [|]]; simplify_tc_goal => //.
        - eapply values_subtyping_trans; eauto.
          apply values_subtyping_take.
          rewrite values_subtyping_cat; last by apply values_subtyping_size in IHHbet; apply values_subtyping_size in Hconjr0; lias.
          by resolve_subtyping.
        - eapply values_subtyping_trans; eauto.
          rewrite values_subtyping_cat; last by apply values_subtyping_size in IHHbet; apply values_subtyping_size in Hconjr0; lias.
          by resolve_subtyping.
      }
Qed.
```

### child `alloc_func_iota_N`: [`theories/instantiation_properties.v` lines 211-236](https://github.com/WasmCert/WasmCert-Coq/blob/58a3d3f8b7af4dc8aa9351f254a9e672643b21f8/theories/instantiation_properties.v#L211-L236) ([local copy](code/theories/instantiation_properties.v))

```coq
Lemma alloc_func_iota_N modfuncs ws inst ws' l:
  alloc_funcs ws modfuncs inst = (ws', l) ->
  l = iota_N (length (s_funcs ws)) (length modfuncs) /\
  ws'.(s_funcs) = ws.(s_funcs) ++ map (fun mf => gen_func_instance mf inst) modfuncs /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_mems) = ws'.(s_mems) /\
  ws.(s_globals) = ws'.(s_globals) /\
  ws.(s_elems) = ws'.(s_elems) /\
  ws.(s_datas) = ws'.(s_datas).
Proof.
  unfold alloc_funcs.
  move => Halloc.
  eapply alloc_Xs_IP with
    (R := (fun s_i s_e xs ys => ys = iota_N _ (length xs) /\ _))
    in Halloc; eauto => //=.
  - unfold iota_N => /=.
    repeat split.
    by rewrite cats0.
  - move => s s0 x xs' ys' s' y Hallocx [Hys [Hcomp [? [? [?[??]]]]]].
    repeat rewrite -> iota_N_iota_N in *.
    unfold alloc_func, add_func in Hallocx; injection Hallocx as ->; subst => /=.
    rewrite List.length_app map_cat iota_N_extend Hcomp => /=.
    repeat split => //=.
    + by rewrite List.length_app List.length_map.
    + by rewrite catA => /=.
Qed.
```

### child `alloc_global_iota_N`: [`theories/instantiation_properties.v` lines 315-352](https://github.com/WasmCert/WasmCert-Coq/blob/58a3d3f8b7af4dc8aa9351f254a9e672643b21f8/theories/instantiation_properties.v#L315-L352) ([local copy](code/theories/instantiation_properties.v))

```coq
Lemma alloc_global_iota_N modglobals g_inits ws ws' l:
  alloc_globs ws modglobals g_inits = (ws', l) ->
  length g_inits = length modglobals ->
  l = iota_N (length (s_globals ws)) (length modglobals) /\
  ws.(s_funcs) = ws'.(s_funcs) /\
  ws.(s_tables) = ws'.(s_tables) /\
  ws.(s_mems) = ws'.(s_mems) /\
  ws'.(s_globals) = ws.(s_globals) ++ map (fun '({| modglob_type := gt; modglob_init := ge |}, v) => {| g_type := gt; g_val := v |} ) (List.combine modglobals g_inits) /\
  ws.(s_elems) = ws'.(s_elems) /\
  ws.(s_datas) = ws'.(s_datas).
Proof.
  unfold alloc_globs.
  move => Halloc.
  remember (List.combine modglobals g_inits) as comb.
  move : modglobals g_inits Heqcomb.
  eapply alloc_Xs_IP with
    (R := (fun s_i s_e xs ys => forall globs g_inits, xs = List.combine globs g_inits -> length g_inits = length globs -> ys = iota_N _ _ /\ _))
    in Halloc; eauto => //=.
  - unfold iota_N => /=.
    repeat split; last by rewrite cats0.
    by destruct globs, g_inits => //.
  - repeat setoid_rewrite iota_N_iota_N.
    move => s s0 x xs' ys' s' y Hallocx Hind modglobs g_inits Hcomb Hgloblen.
    apply combine_snoc in Hcomb; last by lias.
    destruct Hcomb as [modglobs' [g_inits' [g [v [-> [-> [-> ->]]]]]]].
    destruct (Hind modglobs' g_inits') as [Hys [? [? [? [Hcomp [??]]]]]] => //; clear Hind.
    { repeat rewrite List.length_app in Hgloblen; simpl in Hgloblen. by lias. }
    unfold alloc_glob, add_glob in Hallocx. injection Hallocx as ->; subst => /=.
    rewrite map_cat List.length_app iota_N_extend Hcomp => /=.
    rewrite List.length_app.
    repeat split => //=.
    + do 3 f_equal.
      repeat rewrite List.length_app in Hgloblen; simpl in Hgloblen.
      rewrite List.length_map List.length_combine.
      by lias.
    + rewrite -catA.
      by destruct g.
Qed.
```

How the parts fit. The parent unfolds both `interp_instantiate` and
`instantiate`, then `destruct`s each step of the executable pipeline in turn —
the module type check, the external-import check, the import-subtyping check,
the global/element init extraction, and the allocation — each with `eqn:` and
`=> //` so a failing step closes the goal trivially. It then supplies the
witnesses of the relational `instantiate` with
`exists t_imps_mod, t_imps, t_exps, hs, inst', g_inits, r_inits` (line 261) and
`repeat split` (line 316) leaves one goal per conjunct. The comment above the
three asserts documents the order — prove the component lemmas first, then
reuse them in the initialiser reasoning. The conjuncts close as follows:

- `module_typing m t_imps_mod t_exps` — `module_type_checker_sound` (assert at
  line 264).
- `alloc_module s m v_imps g_inits r_inits (s', inst')` — `interp_alloc_sound`
  (lines 266-270), which itself is closed by the six `alloc_*_iota_N` lemmas.
- `Forall2 (external_typing s) v_imps t_imps` — `external_type_checker_sound`
  (lines 272-280).
- `Forall2 import_subtyping t_imps t_imps_mod` — `Forall2_all2_impl`
  (line 318), a generic library lemma, not counted among the per-component
  children.
- The store equalities `f = ...` / `bes = ...` — the six `alloc_*_iota_N`
  lemmas, specialised in the `store` block (lines 306-311) after the allocator
  is re-`destruct`ed.
- `instantiate_globals ...` — `module_typecheck_glob_aux` (line 325) plus
  `b_e_type_checker_reflects_typing` (line 331) plus `const_exprs_impl`
  (line 332), which extracts the single const-expression of each global init.
- `instantiate_elems ...` — `module_typecheck_elem_aux` (line 358) plus
  `b_e_type_checker_reflects_typing` (line 372) plus `const_exprs_impl`
  (line 373).

Lemma graph (each arrow reads "is closed using"):

```
interp_instantiate_imp_instantiate
 ├─ module_type_checker_sound      ── its own destruct/unfold/repeat-split proof;
 │                                    each component block closes via b_e_type_checker_reflects_typing
 ├─ external_type_checker_sound    ── destruct ext; destruct t => //; remove_bools_options; subst
 ├─ interp_alloc_sound             ── the six alloc_*_iota_N siblings
 │    ├─ alloc_func_iota_N         ── eapply alloc_Xs_IP (instantiation_properties.v 182-209)
 │    ├─ alloc_global_iota_N       ── eapply alloc_Xs_IP; combine_snoc (296-313)
 │    └─ alloc_table/mem/elem/data_iota_N ── same family, listed below
 ├─ module_typecheck_glob_aux      ── unfold; destruct m; remove_bools_options; eexists; eauto
 ├─ module_typecheck_elem_aux      ── unfold; destruct m; remove_bools_options; eexists; eauto
 └─ b_e_type_checker_reflects_typing ── destruct (b_e_type_checker ...); ReflectT / ReflectF
```

The other four direct lemmas, which the glue cites at lines 307, 308, 310 and
311 but which are near-duplicates of the two shown (`alloc_func_iota_N`,
`alloc_global_iota_N`), are listed rather than shown as sites:

- `alloc_table_iota_N`, [`instantiation_properties.v` 238-265](https://github.com/WasmCert/WasmCert-Coq/blob/58a3d3f8b7af4dc8aa9351f254a9e672643b21f8/theories/instantiation_properties.v#L238-L265)
- `alloc_mem_iota_N`, [`instantiation_properties.v` 267-294](https://github.com/WasmCert/WasmCert-Coq/blob/58a3d3f8b7af4dc8aa9351f254a9e672643b21f8/theories/instantiation_properties.v#L267-L294)
- `alloc_elem_iota_N`, [`instantiation_properties.v` 354-391](https://github.com/WasmCert/WasmCert-Coq/blob/58a3d3f8b7af4dc8aa9351f254a9e672643b21f8/theories/instantiation_properties.v#L354-L391)
- `alloc_data_iota_N`, [`instantiation_properties.v` 393-420](https://github.com/WasmCert/WasmCert-Coq/blob/58a3d3f8b7af4dc8aa9351f254a9e672643b21f8/theories/instantiation_properties.v#L393-L420)

Why each child is a good leaf. `external_type_checker_sound` and the two
`module_typecheck_*_aux` lemmas are self-contained: 8 and 12 lines, closed by
`destruct ... ; remove_bools_options ; subst` or `eexists; eauto` with no
further project lemma. `alloc_func_iota_N` closes by one `eapply alloc_Xs_IP`,
a shared fold-induction lemma for the whole `alloc_*` family;
`alloc_global_iota_N` needs the same plus `combine_snoc` for its `List.combine`
side condition. `interp_alloc_sound` is the allocator's own soundness lemma and
closes by applying all six `alloc_*_iota_N` siblings. `module_type_checker_sound`
is the large child (159 lines): it closes on its own by `destruct`ing every
sub-checker and then one `{ ... }` block per module component, each funnelling
through `b_e_type_checker_reflects_typing` to turn the executable boolean check
into a typing judgement. `b_e_type_checker_reflects_typing` (84 lines) closes by
`destruct`ing the boolean checker and proving both `ReflectT` and `ReflectF`.

The longest chain I checked is
`interp_instantiate_imp_instantiate → interp_alloc_sound → alloc_global_iota_N →
combine_snoc` (depth 3): the parent cites `interp_alloc_sound` at line 267, that
lemma cites `alloc_global_iota_N` at line 206, and `alloc_global_iota_N` cites
`combine_snoc` at line 338, whose proof closes by induction alone.

The relational target `instantiate` (`instantiation_spec.v` 629-643) is a
`Definition`, not an inductive: an existential over the witnesses plus a
conjunction. That is why the glue is `exists ... ; repeat split` rather than a
`constructor`/`eapply`, and why each conjunct maps to exactly one component
lemma.

## Why it is good

1. `interp_instantiate_imp_instantiate` is declared at
   `theories/interp_instantiate_sound.v` lines 246-402 (check,
   [permalink](https://github.com/WasmCert/WasmCert-Coq/blob/58a3d3f8b7af4dc8aa9351f254a9e672643b21f8/theories/interp_instantiate_sound.v#L246-L402)).
2. No `admit`, `Admitted` or `Axiom` occurs in
   `theories/interp_instantiate_sound.v` lines 246-402 (check,
   [permalink](https://github.com/WasmCert/WasmCert-Coq/blob/58a3d3f8b7af4dc8aa9351f254a9e672643b21f8/theories/interp_instantiate_sound.v#L246-L402)).
3. The parent site cites `module_type_checker_sound` (check,
   [permalink](https://github.com/WasmCert/WasmCert-Coq/blob/58a3d3f8b7af4dc8aa9351f254a9e672643b21f8/theories/interp_instantiate_sound.v#L246-L402)).
4. `direct_lemmas = 12` and `glue_lines = 157`: the parent site is 157 lines
   and names twelve lemmas directly, while the eight shown children span 159,
   8, 32, 12, 12, 84, 26 and 38 lines (measurement; counted in the copied
   files at commit `58a3d3f8b7af`).
5. The authors document the assembly order in a comment inside the glue:
   "Proving these first so they can be used in the reasoning for initialisers
   later", above the three asserts that discharge `module_typing`,
   `alloc_module` and `external_typing` (author-statement,
   [`interp_instantiate_sound.v` line 263](https://github.com/WasmCert/WasmCert-Coq/blob/58a3d3f8b7af4dc8aa9351f254a9e672643b21f8/theories/interp_instantiate_sound.v#L263)).

In my opinion the detail worth copying is the one-to-one mapping from the
conjuncts of a relational specification to a soundness lemma per executable
component, with the existential assembly as the only glue; the six
`alloc_*_iota_N` lemmas show the cost — a near-duplicate per store component.

## When to use it, and when not

Use it when a soundness theorem relates an executable, option-returning
pipeline to a relational specification that is an existential plus a fixed
conjunction of component obligations, and each executable step already has a
corresponding relational component whose soundness can be stated and proved
independently. This is the standard shape of a per-pass or per-stage soundness
proof.

Avoid it when one component's soundness needs the intermediate state of another
component (then the lemmas are not self-contained and the split buys nothing),
when the executable and relational versions diverge so the witnesses cannot be
read off by `destruct`, or when the obligation list is open-ended rather than a
fixed finite conjunction.

## Consequences

The move creates one obligation per conjunct of the `instantiate` relation,
each closed by a named lemma. Five of the eight shown children are small or
moderate (8, 12, 12, 26, 38 lines); `module_type_checker_sound` (159 lines) and
`b_e_type_checker_reflects_typing` (84 lines) carry the real content, and the
initialiser conjuncts are the hard part because the executable version computes
initialiser values under a smaller context than the relational one (the file
header calls it "breaking circularities in the evaluation of various
initialisers"). The glue's `exists ... ; repeat split` fixes the witness order
to match the `instantiate` definition, so a child must discharge exactly its
conjunct. Failure mode: the six `alloc_*_iota_N` lemmas are near-duplicates
generated per store component, so the split buys width, not depth, and a new
store component requires another near-identical lemma.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/main.yml 'Test compilation' build job runs coq-community/docker-coq-action with opam_file coq-wasm.opam, coq_version 9.0, which runs 'opam install .' -> dune build -p coq-wasm @install (coq-wasm.opam build stanza); theories/dune declares (coq.theory (name Wasm) (package coq-wasm)) so all theories/*.v incl. interp_instantiate_sound.v compile; workflow triggers on push and pull_request; commit 58a3d3f8b7af4dc8aa9351f254a9e672643b21f8 is pinned at ref HEAD (default branch) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: module_type_checker_sound@theories/interp_instantiate_sound.v:264, external_type_checker_sound@theories/interp_instantiate_sound.v:277, interp_alloc_sound@theories/interp_instantiate_sound.v:267, module_typecheck_glob_aux@theories/interp_instantiate_sound.v:325, module_typecheck_elem_aux@theories/interp_instantiate_sound.v:358, b_e_type_checker_reflects_typing@theories/interp_instantiate_sound.v:331, alloc_func_iota_N@theories/interp_instantiate_sound.v:306, alloc_global_iota_N@theories/interp_instantiate_sound.v:309; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 4 file(s) byte-identical at 58a3d3f8b7af4dc8aa9351f254a9e672643b21f8 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(interp_instantiate_imp_instantiate, theories/interp_instantiate_sound.v, 246-402) -> declared: interp_instantiate_imp_instantiate is declared at theories/interp_instantiate_sound.v:246 | check_claims.py |
| 2 | verified | no_sorry(theories/interp_instantiate_sound.v, 246-402) -> no_sorry: none of admit, Admitted, Axiom, axiom in theories/interp_instantiate_sound.v:246-402 | check_claims.py |
| 3 | verified | cites(parent, module_type_checker_sound) -> cites: module_type_checker_sound occurs at theories/interp_instantiate_sound.v:264 | check_claims.py |
| 4 | verified | parent site interp_instantiate_sound.v 246-402 is 157 lines (246 'Lemma interp_instantiate_imp_instantiate', 402 'Qed.'); it names twelve lemmas directly: module_type_checker_sound (264), interp_alloc_sound (267), external_type_checker_sound (277), alloc_func_iota_N (306), alloc_table_iota_N (307), alloc_mem_iota_N (308), alloc_global_iota_N (309), alloc_elem_iota_N (310), alloc_data_iota_N (311), module_typecheck_glob_aux (325), module_typecheck_elem_aux (358), b_e_type_checker_reflects_typing (331,372). Child line counts: 16-174=159, 176-183=8, 185-216=32, 220-231=12, 233-244=12 (all Qed.-terminated, starts at 'Lemma' lines checked); type_checker_reflects_typing.v 1527-1610=84; instantiation_properties.v 211-236=26, 315-352=38 | verifier |
| 5 | verified | comment at interp_instantiate_sound.v:263 reads exactly '(* Proving these first so they can be used in the reasoning for initialisers later *)', directly above the three asserts: module_typing (assert ... Hmodtype, line 264), alloc_module (assert ... Hallocmodule, 266), List.Forall2 (external_typing s) v_imps t_imps (assert ... Hexttype, 272) | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent interp_instantiate_imp_instantiate is at interp_instantiate_sound.v 246-402 and ends Qed at 402 with no admit/Admitted/Axiom; it destructs the executable pipeline then exists+repeat split, discharging each conjunct with a per-component lemma exactly as the README describes. All 8 child sites' statements match their declarations verbatim (module_type_checker_sound 16-174, external_type_checker_sound 176-183, interp_alloc_sound 185-216, module_typecheck_glob_aux 220-231, module_typecheck_elem_aux 233-244, b_e_type_checker_reflects_typing 1527-1610, alloc_func_iota_N 211-236, alloc_global_iota_N 315-352) and each closes with Qed; closed_by descriptions match the code. The parent cites all 8 children plus 4 further per-component lemmas (alloc_table/mem/elem/data_iota_N at 307/308/310/311), so direct_lemmas=12 is correct and documented; glue_lines=157 (402-246+1) and child_lines=[159,8,32,12,12,84,26,38] equal the site line counts; depth=3 (parent->interp_alloc_sound line 267 -> alloc_global_iota_N line 206 -> combine_snoc line 338, which closes by induction) is verified. | reviewer-correctness |
| generality | accept | Move stated generally: 'when to use' names the reusable shape (executable option-returning pipeline vs relational existential+fixed-conjunction spec, one soundness lemma per component, witnesses read off by destruct), and related links to CompCert. Avoid-when is specific and honest (component needs a sibling's intermediate state; exe/relational diverge so no destruct witnesses; open-ended obligation list). Consequences are honest (two large children carry content; alloc_*_iota_N near-duplicates buy width not depth). 'Why each child is a good leaf' answers the bounded-prover question: small (8-38 lines), self-contained, closed by one tactic/lemma. Verified cited ranges: instantiation_spec.v 629-643 is an existential+conjunction; interp_instantiate_sound.v header has 'breaking circularities' comment. | reviewer-generality |
| provenance-licence | accept | Provenance and licence are now consistent and traceable. check_provenance passes (4 files byte-identical at 58a3d3f8b7af4dc8aa9351f254a9e672643b21f8); the same commit appears in entry.json, README, source.json and SOURCE.md. The prior licence inconsistency is resolved: SOURCE.md's licence line and source.json's licence field no longer read LGPL-2.1 but now record 'MIT AND LGPL-2.1-or-later' (with an explanatory note that only src/Parray/ is LGPL), which is correct for the whole repository. entry.json source.licence and the README record MIT, correct for the four copied files (interp_instantiate_sound.v, type_checker_reflects_typing.v, instantiation_properties.v, instantiation_spec.v), all under theories/; upstream-LICENSE.txt confirms MIT except src/Parray/ (LGPL-2.1+), so the copied files are MIT. The README's 'Source and licence' section states this split explicitly. Cited line ranges resolve to the copied code (parent site 246 begins 'Lemma interp_instantiate_imp_instantiate'; instantiation_spec.v 629-643 is the existential+conjunction Definition instantiate). | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/WasmCert/WasmCert-Coq at commit `58a3d3f8b7af4dc8aa9351f254a9e672643b21f8`, under `MIT`. The upstream [LICENSE.txt](../../sources/wasmcert-coq/upstream-LICENSE.txt) states the project is MIT except `src/Parray/`, which is LGPL-2.1+; all four copied files are under `theories/` (`interp_instantiate_sound.v`, `type_checker_reflects_typing.v`, `instantiation_properties.v`, `instantiation_spec.v`), so they are MIT, not LGPL. See the [source note](../../sources/wasmcert-coq/SOURCE.md) for the licence text and attribution.
