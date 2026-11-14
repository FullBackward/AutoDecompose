# Per-pass correctness lemmas for erasure, dearging and match-on-box removal, composed in extract_correct

| | |
|---|---|
| Kind | instance |
| Move | per-callee-lemma |
| Language | rocq |
| Status | accepted |
| Source | [metarocq](../../sources/metarocq/SOURCE.md) at `51b14e4bb5f4` |
| Licence | `MIT` |

## Intent

Reduce the end-to-end correctness of the verified extraction pipeline — that
a well-typed, axiom-free PCUIC constant evaluating to a constructor extracts
to an erased, dearged, match-on-box-removed λ□ term evaluating to the same
constructor — to one correctness lemma per pass (`erases_correct`,
`dearg_transform_correct`, `optimize_correct`) plus the typing,
well-formedness and dependency-closure lemmas their premises need, so
`extract_correct` is a 51-line composition that never re-proves a pass.

## The decomposition

### parent `extract_correct`: [`erasure/theories/Typed/ExtractionCorrectness.v` lines 530-580](https://github.com/MetaRocq/metarocq/blob/51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56/erasure/theories/Typed/ExtractionCorrectness.v#L530-L580) ([local copy](code/erasure/theories/Typed/ExtractionCorrectness.v))

```coq
Theorem extract_correct
        (H := EWellformed.all_env_flags)
        (wfl := opt_wcbv_flags)
        (Σ : P.global_env_ext) (wfΣ : ∥wf_ext Σ∥)
        kn ui ind c ui' ignored exΣ :
  axiom_free Σ ->
  welltyped Σ [] (P.tConst kn ui) ->
  Σ p⊢ P.tConst kn ui ⇓ P.tConstruct ind c ui' ->
  (isErasable Σ [] (P.tConstruct ind c ui') -> False) ->
  (forall k, ignored k = false) ->
  extract_pcuic_env
    (pcuic_args extract_within_coq)
    Σ (wf_squash wfΣ) (KernameSet.singleton kn) ignored = Ok exΣ ->
  ∥trans_env exΣ e⊢ E.tConst kn ⇓ E.tConstruct ind c []∥.
Proof.
  intros ax [T wt] ev not_erasable no_ignores ex.
  cbn -[dearg_transform] in *.
  destruct dearg_transform eqn:dt; cbn -[dearg_transform] in *; [|congruence].
  injection ex as ->.
  destruct wfΣ.
  eapply erases_correct with
    (Σ' := trans_env (Erasure.erase_global_decls_deps_recursive (PCUICAst.PCUICEnvironment.declarations Σ)
               (PCUICAst.PCUICEnvironment.universes Σ) _ _
               (KernameSet.singleton kn) ignored)) in ev as (erv&erase_to&[erev]);eauto.
  + depelim erase_to;[|easy].
    constructor.
    eapply dearg_transform_correct; eauto.
    clear dt.
    eapply (@optimize_correct _ _ _ (tConst kn) (tConstruct ind c []));eauto.
    * remember (Erasure.erase_global_decls_deps_recursive _ _ _ _ _ _) as eΣ.
      assert (EWellformed.wf_glob (trans_env eΣ)).
      { subst eΣ. now eapply wf_erase_global_decls_recursive. }
      now apply EWellformed.wellformed_closed_env.
    * eapply wf_erase_global_decls_recursive; auto.
  + now eexists.
  + eapply inversion_Const in wt as (?&?&?&?&?); auto.
    clear dt.
    eapply global_erased_with_deps_erases_deps_tConst; eauto.
    destruct Σ as [Σ0 univ_decls].
    destruct Σ0 as [univs Σ1].
    apply wf_ext_wf in w as w1. cbn.
    eapply erase_global_decls_deps_recursive_correct;eauto.
    * unfold PCUICAst.declared_constant in *.
      cbn.
      intros ? ->%KernameSet.singleton_spec;cbn in *.
      intros eq. set (env := {| PEnv.declarations := Σ1 |}) in *.
      eapply (lookup_global_In_wf _ env) in d; eauto.
    * now apply KernameSet.singleton_spec.
    Unshelve. eapply fresh_globals_erase_global_decl_rec.
      now eapply PCUICWfEnvImpl.wf_fresh_globals.
Qed.
```

### child `erases_correct`: [`erasure/theories/ErasureCorrectness.v` lines 51-1232](https://github.com/MetaRocq/metarocq/blob/51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56/erasure/theories/ErasureCorrectness.v#L51-L1232) ([local copy](code/erasure/theories/ErasureCorrectness.v))

```coq
Lemma erases_correct (wfl := default_wcbv_flags) Σ t t' v Σ' :
  wf_ext Σ ->
  welltyped Σ [] t ->
  Σ;;; [] |- t ⇝ℇ t' ->
  erases_deps Σ Σ' t' ->
  Σ |-p t ⇓ v ->
  exists v', Σ;;; [] |- v ⇝ℇ v' /\ ∥ Σ' ⊢ t' ⇓ v' ∥.
Proof.
  intros wfΣ [T Hty] He Hed H.
  revert T Hty t' He Hed.
  induction H; intros T Hty t' He Hed.
  - assert (Hty' := Hty).
    assert (eval Σ (PCUICAst.tApp f a) res) by eauto.
    eapply inversion_App in Hty as (? & ? & ? & ? & ? & ?).
    invs He.

    + depelim Hed.
      eapply IHeval1 in H4 as (vf' & Hvf' & [He_vf']); eauto.
      eapply IHeval2 in H6 as (vu' & Hvu' & [He_vu']); eauto.
      pose proof (subject_reduction_eval t0 H).
      eapply inversion_Lambda in X0 as (? & h1 & ? & e0).
      apply isTypeRel_isType in h1.
      assert (Σ ;;; [] |- a' : t). {
          eapply subject_reduction_eval; eauto.
          eapply PCUICConversion.ws_cumul_pb_Prod_Prod_inv in e0 as [? e1 e2].
          eapply type_Cumul_alt; tea.
          symmetry in e1.
          eapply ws_cumul_pb_forget in e1.
          now eapply conv_cumul. }
      assert (eqs := type_closed_subst b wfΣ X0).
      invs Hvf'.
      * assert (Σ;;; [] |- PCUICAst.subst1 a' 0 b ⇝ℇ ELiftSubst.subst1 vu' 0 t').
        eapply (erases_subst Σ [] [vass na t] [] b [a'] t'); eauto.
        econstructor. econstructor. rewrite PCUICLiftSubst.subst_empty. eassumption.
        rewrite eqs in H2.
        eapply IHeval3 in H2 as (v' & Hv' & [He_v']).
        -- exists v'. split; eauto.
           constructor.
           econstructor; eauto.
           rewrite ECSubst.closed_subst; auto.
           eapply erases_closed in Hvu'; auto; fvs.
        -- rewrite <-eqs. eapply substitution0; eauto.
        -- eapply erases_deps_subst1; [now eauto|].
           eapply erases_deps_eval in He_vf'; [|now eauto].
           depelim He_vf'.
           assumption.
      * exists EAst.tBox. split.
        eapply Is_type_lambda in X1; eauto. destruct X1. econstructor.
        eapply (is_type_subst Σ [] [vass na _] [] _ [a']) in X1 ; auto.
        cbn in X1.
        eapply Is_type_eval; try assumption.
        eauto. eapply H1. rewrite <-eqs. eassumption.
        all: eauto. econstructor. econstructor. rewrite PCUICLiftSubst.subst_empty.
        eauto. constructor. econstructor. eauto. eauto.
      * auto.
    + exists EAst.tBox. split. 2:constructor; econstructor; eauto.
      econstructor.
      eapply Is_type_eval; eauto.
    + auto.
  - assert (Hty' := Hty).
    assert (Σ |-p tLetIn na b0 t b1 ⇓ res) by eauto.
    eapply inversion_LetIn in Hty' as (? & h1 & ? & ?); auto.
    assert (wf_rel : lift_typing0 (typing Σ []) (j_vdef na b0' t)).
    { apply lift_sorting_it_impl_gen with h1 => // HT. eapply subject_reduction_eval; eauto. }
    apply unlift_TermTyp in h1 as h1'.
    invs He.
    + depelim Hed.
      eapply IHeval1 in H6 as (vt1' & Hvt2' & [He_vt1']); eauto.
      assert (Hc : conv_context cumulAlgo_gen Σ ([],, vdef na b0 t) [vdef na b0' t]). {
        econstructor. econstructor. econstructor. reflexivity.
        eapply PCUICCumulativity.red_conv.
        eapply wcbveval_red; eauto.
        reflexivity.
      }
      assert (Σ;;; [vdef na b0' t] |- b1 : x). {
        cbn in *. eapply context_conversion. 3:eauto. all:cbn; eauto.
        econstructor. constructor. assumption.
      }
      assert (Σ;;; [] |- subst1 b0' 0 b1 ⇝ℇ ELiftSubst.subst1 vt1' 0 t2'). {
        eapply (erases_subst Σ [] [vdef na b0' t] [] b1 [b0'] t2'); eauto.
        enough (subslet Σ [] [subst [] 0 b0'] [vdef na b0' t]).
        now rewrite PCUICLiftSubst.subst_empty in X1.
        econstructor. econstructor.
        rewrite !PCUICLiftSubst.subst_empty.
        eapply subject_reduction_eval; eauto.
        eapply erases_context_conversion. 3:eassumption.
        all: cbn; eauto.
        econstructor. constructor. assumption.
      }
      pose proof (subject_reduction_eval h1' H).
      assert (eqs := type_closed_subst b1 _ X1).
      rewrite eqs in H1.
      eapply IHeval2 in H1 as (vres & Hvres & [Hty_vres]); [| |now eauto].
      2:{ rewrite <-eqs. eapply substitution_let; eauto. }
      exists vres. split. eauto. constructor; econstructor; eauto.
      enough (ECSubst.csubst vt1' 0 t2' = ELiftSubst.subst10 vt1' t2') as ->; auto.
      eapply ECSubst.closed_subst. eapply erases_closed in Hvt2'; auto.
      eapply eval_closed. eauto. 2:eauto. now eapply subject_closed in h1'.
    + exists EAst.tBox. split. 2:constructor; econstructor; eauto.
      econstructor. eapply Is_type_eval; eauto.

  - assert (Σ |-p tConst c u ⇓ res) by eauto.
    eapply inversion_Const in Hty as (? & ? & ? & ? & ?); [|easy].
    invs He.
    + depelim Hed.
      assert (isdecl' := isdecl). destruct wfΣ as [wfΣ ?].
      unshelve eapply declared_constant_to_gen in H0, d; eauto.
      eapply declared_constant_inj in H0; [|now eauto]; subst.
      unfold erases_constant_body in *. rewrite -> e in *.
      destruct ?; try tauto. cbn in *.
      eapply declared_constant_inj in d; [|now eauto]; subst.
      edestruct IHeval as (? & ? & [?]).
      * cbn in *.
        assert (isdecl'' := isdecl').
        apply declared_constant_from_gen in isdecl', isdecl''.
        eapply declared_constant_inv in isdecl'; [| |now eauto|now apply wfΣ].
        2:exact weaken_env_prop_typing.
        unfold on_constant_decl in isdecl'. rewrite e in isdecl'. eapply unlift_TermTyp in isdecl'.
        unfold declared_constant in isdecl''.
        now eapply @typing_subst_instance_decl with (Σ := Σ) (Γ := []); eauto.
      * assert (isdecl'' := isdecl').
        apply declared_constant_from_gen in isdecl', isdecl''.
        eapply declared_constant_inv in isdecl'; [| |now eauto|now apply wfΣ].
        unfold on_constant_decl in isdecl'. rewrite e in isdecl'. eapply unlift_TermTyp in isdecl'.
        2:exact weaken_env_prop_typing.
        now eapply erases_subst_instance_decl with (Σ := Σ) (Γ := []); eauto.
      * now eauto.
      * exists x0. split; eauto. constructor; econstructor; eauto.
    + exists EAst.tBox. split. econstructor.
      eapply Is_type_eval. 3: eassumption. eauto. eauto. eauto. constructor. econstructor. eauto.

  - assert (Hty' := Hty).
  assert (Σ |-p tCase ci p discr brs ⇓ res) by eauto.
  (* assert (Σ |-p tCase ci p discr brs ⇓ res) by eauto.
 *)
  eapply inversion_Case in Hty' as (mdecl' & idecl' & di & indices & [] & c0); auto.

  rename ci into ind.
  pose proof d as d'. pose proof (wfΣ' := wfΣ.1).
  eapply declared_constructor_inductive in d'.
  unshelve eapply declared_inductive_to_gen in di; eauto.
  edestruct (declared_inductive_inj d' di); subst. clear d'.
  assert (Σ ;;; [] |- mkApps (tConstruct ind c u) args :   mkApps (tInd ind (puinst p)) (pparams p ++ indices)).
  eapply subject_reduction_eval; eauto.
  assert (Hcstr := X0).
  eapply Construct_Ind_ind_eq in X0; tea. 2:{ eapply declared_constructor_from_gen; tea. }
  destruct X0 as (((([_ Ru] & cu) & cpu) & ?) & (parsubst & argsubst & parsubst' & argsubst' & [])).
  invs He.
  + depelim Hed. rename H5 into Hlen.
    rename H1 into decli. rename H2 into decli'.
    rename H3 into em. rename Hed into er.
    rename H6 into H5. rename H7 into H6. rename H8 into H7.
    edestruct (IHeval1 _ scrut_ty) as (v' & Hv' & [He_v']); eauto.
    pose proof e0 as Hnth.
    assert (lenppars : ind_npars mdecl = #|pparams p|).
    { now rewrite (wf_predicate_length_pars wf_pred). }
    unshelve eapply declared_inductive_to_gen in decli; eauto.
    destruct (declared_inductive_inj d.p1 decli); subst mdecl0 idecl0.
    eapply erases_mkApps_inv in Hv' as [(? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)]; eauto.
    * subst.
      eapply Is_type_app in X1; auto. destruct X1.
      2:{ rewrite -mkApps_app; tea. }
      rewrite -mkApps_app in X1.

      eapply tConstruct_no_Type in X1; auto.

      eapply H6 in X1 as []; eauto.
      2: eapply declared_inductive_from_gen; eauto.
      2: split; auto; exists []; now destruct Σ.
      destruct (ind_ctors idecl) eqn:hctors.
      { cbn in *. depelim brs_ty. depelim X0. rewrite nth_error_nil // in Hnth. }
      depelim brs_ty. cbn in H1.
      destruct l; cbn in *; try lia.
      depelim brs_ty. depelim X0. depelim X0.
      destruct p1.
      destruct c; cbn in *. noconf Hnth. 2:{ rewrite nth_error_nil // in Hnth. }
      destruct p0 as (? & ? & ? & ?).
      assert (c1 = cdecl).
      { destruct d.
        rewrite hctors /= in H10. now noconf H10. }
      depelim H5.
      subst c1.
      destruct y0 as [n br']; cbn in *.
      rename y into br.
      edestruct IHeval2 as (? & ? & [?]).
      eapply subject_reduction. eauto. exact Hty.
      etransitivity.
      eapply PCUICReduction.red_case_c. eapply wcbveval_red; eauto.
      econstructor. econstructor.
      eauto.
      all:unfold iota_red in *. all:cbn in *.
      { rewrite e2 e1. now f_equal. }
      {
        assert (expand_lets (inst_case_branch_context p br) (br.(PCUICAst.bbody)) = br.(PCUICAst.bbody)) as ->. {
          unshelve edestruct @on_declared_constructor as (? & ? & ? & []).
          8: eapply declared_constructor_from_gen; exact d. all: eauto.
          pattern br.
          eapply All_nth_error.
          pose proof (d_ := declared_constructor_from_gen d).
          eapply (expand_lets_erasure (p:=p) d_ wf_brs); eauto.
          rewrite hctors; constructor.
          solve_all. constructor.
          instantiate (1 := 0); cbn; eassumption.
        }
        invs H9.
        eapply erases_subst0; eauto.
        rewrite [case_branch_context_gen _ _ _ _ _ _]PCUICCasesContexts.inst_case_branch_context_eq; eauto.
        1:{ unfold app_context. cbn. rewrite app_nil_r.
            eapply (subslet_cstr_branch_context (u:=u)); tea.
            - eapply declared_constructor_from_gen. eauto.
            - rewrite lenppars firstn_app_left // in s0. exact s0.
            - eapply declared_constructor_from_gen in d.
              eapply (declared_constructor_assumption_context d).
            - destruct s3 as [Hs [_ []]].
              rewrite {2}lenppars [firstn _ (pparams p ++ _)]firstn_app_left // in a1.
            - red in wf_brs. rewrite hctors in wf_brs. now depelim wf_brs.
            - rewrite -eq_npars. exact s1. }
        eapply All2_rev.
        rewrite -eq_npars.
        eapply All_All2_flex; tea.
        2:{ instantiate (1 := repeat EAst.tBox #|skipn (ind_npars mdecl) (x ++ x0)|).
            now rewrite repeat_length. }
        intros ? ? ? % repeat_spec. subst.
        constructor.
        now eapply isErasable_Proof. }
      2:{
      exists x2. split; eauto. constructor. eapply eval_iota_sing => //.
      pose proof (EWcbvEval.eval_to_value _ _ He_v').
      let X0 := match goal with H : EWcbvEval.value _ (EAst.mkApps _ _) |- _ => H end in
      eapply value_app_inv in X0. subst. eassumption.
      depelim H2.
      eapply isErasable_Propositional in X0; eauto.
      rewrite -eq_npars.
      erewrite isPropositional_propositional; eauto. now rewrite X0.
      apply declared_inductive_from_gen; eauto.
      invs e. cbn in *.
      rewrite length_map.
      rewrite length_skipn H13 e3 in H11.
      rewrite (@assumption_context_assumptions (bcontext br)) // ?rev_repeat in H11 => //.
      { eapply assumption_context_compare_decls. symmetry in a. exact a.
        rewrite /cstr_branch_context. eapply assumption_context_expand_lets_ctx.
        eapply assumption_context_subst_context.
        eapply declared_constructor_from_gen in d.
        apply (declared_constructor_assumption_context d). }
      rewrite ECSubst.substl_subst //.
      { eapply forallb_repeat. econstructor. }
      replace (ind_npars mdecl + #|bcontext br| - ind_npars mdecl)
      with #|bcontext br| in H11 by lia. eauto.
      }
      depelim H4.
      cbn in H1.
      eapply erases_deps_subst. 2: eauto.
      eapply All_rev. eapply Forall_All.
      eapply All_Forall, All_repeat. econstructor.
    * subst. unfold iota_red in *.
      destruct (All2_nth_error_Some _ _ X0 Hnth) as (? & ? & ? & ?).
      destruct (All2i_nth_error_r _ _ _ _ _ _ brs_ty Hnth) as (? & ? & ? & ? & ? & ?).
      cbn in *. subst.
      assert (declared_constructor Σ (ind, c) mdecl idecl x2).
      { apply declared_constructor_from_gen; split; tea. }
      unshelve eapply declared_constructor_to_gen in H1; eauto.
      destruct (declared_constructor_inj d H1) as [_ [_ <-]]. clear H1.
      edestruct IHeval2 as (? & ? & [?]).
      eapply subject_reduction. eauto. exact Hty.
      etransitivity.
      eapply PCUICReduction.red_case_c. eapply wcbveval_red. eauto.
      eauto. eauto.

      etransitivity. constructor. constructor.
      eauto.
      { rewrite e1 /cstr_arity e3. congruence. }
      unfold iota_red. reflexivity.

      {
        assert (expand_lets (inst_case_branch_context p br) (br.(PCUICAst.bbody)) = br.(PCUICAst.bbody)) as ->. {
        unshelve edestruct @on_declared_constructor as (? & ? & ? & []).
          8: eapply declared_constructor_from_gen; exact d. all: eauto.
          pattern br.
          eapply All_nth_error. 2: eauto.
          pose proof (d_ := declared_constructor_from_gen d).
          eapply (expand_lets_erasure d_ wf_brs). solve_all.
        }
        eapply erases_subst0; eauto.
        all: try rewrite case_branch_type_fst PCUICCasesContexts.inst_case_branch_context_eq; eauto.
        rewrite app_context_nil_l.
        erewrite <-PCUICCasesContexts.inst_case_branch_context_eq; eauto.
        1:{ eapply (subslet_cstr_branch_context (u:=u)); tea.
            - eapply declared_constructor_from_gen; eauto.
            - rewrite lenppars firstn_app_left // in s0. exact s0.
            - apply declared_constructor_from_gen in d.
              eapply (declared_constructor_assumption_context d).
            - destruct s3 as [Hs [_ []]].
              rewrite {2}lenppars [firstn _ (pparams p ++ _)]firstn_app_left // in a1.
            - red in wf_brs. eapply Forall2_All2 in wf_brs.
              eapply All2_nth_error in wf_brs; tea.
            - rewrite -eq_npars. exact s1. }
      eapply All2_rev. eapply All2_skipn.
      eapply Forall2_All2 in H3. eapply All2_impl. exact H3. intros. eauto.
       }

      eapply nth_error_forall in H5; [|now eauto].
      eapply erases_deps_subst; eauto.
      eapply All_rev.
      eapply erases_deps_eval in He_v'; [|now eauto].
      eapply erases_deps_mkApps_inv in He_v' as (? & ?).
      now eapply All_skipn, Forall_All.

      invs H2.
      -- exists x2. split; eauto.
         constructor. econstructor. eauto. eauto. 2:eauto.
         4:{ unfold EGlobalEnv.iota_red.
          rewrite ECSubst.substl_subst //.
          rewrite forallb_rev forallb_skipn //.
          assert (forallb (closedn 0) args).
          { move/eval_closed: H; tea.
            move/(_ (subject_closed scrut_ty)).
            now rewrite closedn_mkApps /=. }
          solve_all. eapply (erases_closed _ []); tea. }
         rewrite -eq_npars.
         erewrite isPropositional_propositional_cstr; eauto.
         move/negbTE: H13 => ->. reflexivity.
         eapply declared_constructor_from_gen; eauto.
         rewrite  -(Forall2_length H3) /= e2 //.
         rewrite length_skipn -(Forall2_length H3) -e6 /= length_map.
         rewrite (All2_length a).
         replace #|cstr_branch_context ind mdecl cdecl|
          with (context_assumptions (cstr_branch_context ind mdecl cdecl)).
         2:{ eapply assumption_context_assumptions.
             apply declared_constructor_from_gen in d.
             eapply (assumption_context_cstr_branch_context d). }
         rewrite e2 /cstr_arity e1 cstr_branch_context_assumptions; lia.
      -- eapply Is_type_app in X1 as []; auto.
         2:{ eapply subject_reduction_eval. 2:eassumption. eauto. }
         assert (ispind : inductive_isprop_and_pars Σ' ind = Some (true, ind_npars mdecl)).
         { erewrite isPropositional_propositional; eauto. f_equal. f_equal.
           eapply isErasable_Propositional; eauto.
          apply declared_inductive_from_gen; eauto. }

         eapply tConstruct_no_Type in X1; auto.
         eapply H6 in X1 as []; eauto.
         2: apply declared_inductive_from_gen; eauto.
         2:reflexivity.

         destruct (ind_ctors idecl) eqn:hctors. cbn in *. destruct c; invs e7.
         destruct l; cbn in *; try lia. destruct c as [ | []]; cbn in *; invs e7.

         (* destruct btys as [ | ? []]; cbn in *; try discriminate. *)
         destruct brs'; invs e4.
         destruct brs; invs Hnth.
         destruct H9.
         depelim brs_ty. depelim brs_ty.
         depelim X0. depelim X0.
         destruct p0 as (? & ? & ? & ?).
         edestruct IHeval2 as (? & ? & [?]).
         eapply subject_reduction. eauto. exact Hty.
         etransitivity.
         eapply PCUICReduction.red_case_c. eapply wcbveval_red. eauto.
         eauto. eauto.
         etransitivity. constructor. constructor. cbn. reflexivity.
         { rewrite e1 /cstr_arity e2 e3 //. }
         eauto.

         {
          assert (expand_lets (inst_case_branch_context p br) (br.(PCUICAst.bbody)) = br.(PCUICAst.bbody)) as ->. {
            unshelve edestruct @on_declared_constructor as (? & ? & ? & []).
            8: apply declared_constructor_from_gen; exact d. all: eauto.
            pattern br.
            eapply All_nth_error.
            eapply expand_lets_erasure; eauto.
            eapply declared_constructor_from_gen; eauto.
            2: instantiate (1 := 0); cbn; eassumption.
            rewrite hctors. constructor; auto. constructor. }
          destruct p1.
          eapply erases_subst0; eauto.
          - rewrite case_branch_type_fst PCUICCasesContexts.inst_case_branch_context_eq; eauto.
          - rewrite app_context_nil_l.
            eapply subslet_cstr_branch_context. tea.
            eapply declared_constructor_from_gen; eauto.
            exact cu. all:eauto.
            now rewrite lenppars firstn_app_left // in s0.
            eapply declared_constructor_from_gen in d.
            eapply (declared_constructor_assumption_context d).
            destruct s3 as [? [? [eqp _]]].
            rewrite lenppars (firstn_app_left) // in eqp.
            match goal with
            | [ H : ?f (firstn ?n ?ls) ?p |- ?f (firstn ?n' ?ls) ?p ]
              => replace n' with n; first [ exact H | congruence ]
            end.
            move: wf_brs. now rewrite /wf_branches hctors => h; depelim h.
            rewrite -eq_npars. exact s1.
          - eapply All2_rev. cbn.
            rewrite -eq_npars.
            eapply All_All2_flex.
            exact X1.
            intros ? ? -> % repeat_spec.
            intros. econstructor. eapply isErasable_Proof. eauto.
            rewrite repeat_length. reflexivity.
        }

         depelim H5.
         eapply erases_deps_subst; eauto.
         eapply All_rev, All_repeat.
         econstructor.

         exists x. split; eauto.
         constructor.
         destruct x1 as [n br'].
         eapply eval_iota_sing => //.
         pose proof (EWcbvEval.eval_to_value _ _ He_v') as X0.
         apply value_app_inv in X0; subst x0.
         apply He_v'.
         now rewrite -eq_npars.

         cbn in *.

         rewrite ECSubst.substl_subst.
         { eapply forallb_repeat. econstructor. }

         rewrite rev_repeat in H10.

         enough (#|skipn (ind_npars mdecl) args| = #|n|) as <- by eauto.
         edestruct invert_Case_Construct as (? & ? & ? & ?).
         { econstructor. eauto. }
         { eapply subject_reduction. eauto. exact Hty.
           eapply PCUICReduction.red_case_c. eapply wcbveval_red; eauto. }

        rewrite eq_npars. rewrite List.length_skipn e1 /cstr_arity -e2 e3.
        replace (ci_npar ind + context_assumptions (bcontext br) - ci_npar ind)
    with (context_assumptions (bcontext br)) by lia.
        subst n. rewrite length_map.
        rewrite assumption_context_assumptions //.
        eapply assumption_context_compare_decls. symmetry; tea.
        eapply declared_constructor_from_gen in d.
        eapply (assumption_context_cstr_branch_context d).
    + exists EAst.tBox. split. econstructor.
      eapply Is_type_eval; eauto. constructor. econstructor; eauto.


  - pose (Hty' := Hty).
    pose proof (proj2 (proj2 d)) as eqpars.
    rename e1 into hnth. rename e0 into eargs.
    eapply inversion_Proj in Hty' as (? & ? & ? & [] & ? & ? & ? & ? & ? & ?); [|easy].
    pose proof (wfΣ' := wfΣ.1).
    unshelve eapply declared_projection_to_gen in d0; eauto.
    assert (Hpars : p.(proj_npars) = ind_npars x0).
    { destruct (declared_constructor_inj d0.p1 d.p1). now subst. }
    invs He.

    + depelim Hed.
      rename H1 into decli. rename H2 into decli'. rename H4 into er. rename H3 into em. rename H5 into H3.
      eapply IHeval1 in H6 as (vc' & Hvc' & [Hty_vc']); eauto.
      eapply erases_mkApps_inv in Hvc'; eauto.
      destruct Hvc' as [ (? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)]; subst.
      * exists EAst.tBox.
        unshelve eapply declared_projection_to_gen in decli; eauto.
        destruct (declared_inductive_inj decli.p1 d.p1) as [<- <-].
        assert (isprop : inductive_isprop_and_pars Σ' p.(proj_ind) = Some (true, ind_npars mdecl)).
        { erewrite isPropositional_propositional; eauto. f_equal. f_equal.
          eapply isErasable_Propositional; eauto.
          eapply declared_inductive_from_gen; exact d. all:eauto. apply decli'. }
        split.
        eapply Is_type_app in X as []; eauto. 2:{ rewrite -mkApps_app. eapply subject_reduction_eval; eauto. }
        rewrite -mkApps_app in X.

        eapply tConstruct_no_Type in X; eauto. eapply H3 in X as [? []]; eauto.
        2:{ eapply declared_inductive_from_gen; exact d. }
        2: split; auto; now exists []; destruct Σ.
        destruct d0 as (? & ? & ?).

        econstructor.
        eapply Is_type_eval; eauto.
        eapply nth_error_all.
        erewrite nth_error_skipn. eassumption.
        eapply All_impl.
        subst. rewrite -eqpars.
        eassumption.
        eapply isErasable_Proof. constructor. eauto.

        eapply eval_proj_prop => //.
        pose proof (EWcbvEval.eval_to_value _ _ Hty_vc') as X0.
        eapply value_app_inv in X0. subst. eassumption.
        now rewrite -eqpars.
      * rename H3 into Hinf.
        assert (lenx5 := Forall2_length H4).
        eapply Forall2_nth_error_Some in H4 as (? & ? & ?); eauto.
        assert (Σ ;;; [] |- mkApps (tConstruct p.(proj_ind) 0 u) args : mkApps (tInd p.(proj_ind) x) x3).
        eapply subject_reduction_eval; eauto.
        eapply inversion_mkApps in X as (? & ? & ?); eauto.
        eapply Prelim.typing_spine_inv in t1 as []; eauto.
        eapply IHeval2 in H3 as (? & ? & [?]); eauto.
        unshelve eapply declared_projection_to_gen in decli; eauto.
        destruct (declared_projection_inj decli d0) as [? [? []]].
        subst x0 x1 cdecl0 x2.
        destruct (declared_projection_inj d d0) as [? [? []]]; subst mdecl0 idecl0 pdecl0 cdecl.
        invs H2.
        -- exists x9. split; eauto. constructor.
            eapply EWcbvEval.eval_proj; eauto. rewrite -eqpars.
            erewrite isPropositional_propositional_cstr; eauto.
            move/negbTE: H9 => ->. reflexivity.
            eapply declared_constructor_from_gen. apply d0. cbn. eapply decli'. cbn. rewrite -lenx5 //.
            move: eargs. unfold PCUICWcbvEval.cstr_arity; cbn.
            now rewrite -eqpars.
        -- exists EAst.tBox.
          assert (isprop : inductive_isprop_and_pars Σ' p.(proj_ind) = Some (true, ind_npars mdecl)).
          { erewrite isPropositional_propositional; eauto. do 2 f_equal.
            eapply (isErasable_Propositional (args:=[])); eauto.
            eapply declared_inductive_from_gen. apply d. apply decli'. }
          split.
          eapply Is_type_app in X as []; eauto. 2:{ eapply subject_reduction_eval; [|eauto]; eauto. }

          eapply tConstruct_no_Type in X. eapply Hinf in X as [? []]; eauto.
          2: apply declared_inductive_from_gen; now eapply d. 2:reflexivity. 2:eauto.
          econstructor.
          eapply Is_type_eval; eauto.
          eapply nth_error_all.
          erewrite nth_error_skipn. eassumption. rewrite -eqpars.
          eapply All_impl.
          eassumption.
          eapply isErasable_Proof.
          constructor. eapply eval_proj_prop => //.
          pose proof (EWcbvEval.eval_to_value _ _ Hty_vc') as X0.
          eapply value_app_inv in X0. subst. eassumption.
          now rewrite -eqpars.
        -- eapply erases_deps_eval in Hty_vc'; [|now eauto].
            eapply erases_deps_mkApps_inv in Hty_vc' as (? & ?).
            now eapply nth_error_forall in H1; eauto.
    + exists EAst.tBox. split. econstructor.
      eapply Is_type_eval. 3: eassumption. all:eauto. constructor. econstructor. eauto.
  - assert (Hty' := Hty).
    assert (Hunf := H).
    assert (Hcon := H0).
    eapply inversion_App in Hty' as (? & ? & ? & ? & ? & e0); eauto.
    assert (Ht := t).
    eapply subject_reduction in t. 2:auto. 2:eapply wcbveval_red; eauto.
    assert (HT := t).
    apply PCUICValidity.inversion_mkApps in HT as (? & ? & ?); auto.
    assert (Ht1 := t1).
    apply inversion_Fix in t1 as Hfix; auto.
    rename e0 into hcum.
    rename e1 into e.
    destruct Hfix as (? & ? & ? & ? & ? & ? & e1).
    unfold cunfold_fix in e. rewrite e0 in e. invs e.
    depelim He; first last.

    + exists EAst.tBox. split; [|now constructor; constructor].
      econstructor.
      eapply Is_type_eval. 3:eapply X. eauto.
      eapply eval_fix; eauto.
      rewrite /cunfold_fix e0 //. now rewrite H3.
    + depelim Hed.
      eapply IHeval1 in He1 as (er_stuck_v & er_stuck & [ev_stuck]); eauto.
      eapply IHeval2 in He2 as (er_argv & er_arg & [ev_arg]); eauto.
      eapply erases_mkApps_inv in er_stuck; eauto.
      destruct er_stuck as [(? & ? & ? & -> & ? & ? & ? & ->)|
                            (? & ? & -> & ? & ?)].
      { exists E.tBox.
        eapply eval_to_mkApps_tBox_inv in ev_stuck as ?; subst.
        cbn in *.
        split; [|constructor; eauto].
        2:{ eapply (eval_box_apps _ _ [_]); eauto. }
        destruct H2.
        eapply (Is_type_app _ _ _ (x5 ++ [av])) in X as []; eauto; first last.
        - rewrite -mkApps_app app_assoc mkApps_snoc.
          eapply PCUICValidity.type_App'; eauto.
          eapply subject_reduction; eauto.
          eapply wcbveval_red; eauto.
        - eapply erases_box.
          eapply Is_type_eval; auto. 2:eauto.
          rewrite mkApps_app /=.
          eapply eval_fix.
          rewrite -mkApps_app. eapply value_final.
          eapply eval_to_value; eauto.
          eapply value_final, eval_to_value; eauto.
          rewrite /cunfold_fix e0 //. auto.
          now rewrite H3. auto. }

      invs H2.
      * assert (Hmfix' := X).
        eapply All2_nth_error_Some in X as (? & ? & ?); eauto.
        pose proof (closed_fix_substl_subst_eq (subject_closed t1) e0) as cls.
        destruct x3. cbn in *. subst.

        enough (Σ;;; [] ,,, subst_context (fix_subst mfix) 0 []
                |- subst (fix_subst mfix) 0 dbody
                ⇝ℇ ELiftSubst.subst (EGlobalEnv.fix_subst mfix') 0 (Extract.E.dbody x4)).
        destruct a2.

        rename e3 into eargsv.
        -- rename x5 into L.
           eapply (erases_mkApps _ _ _ _ (argsv ++ [av])) in H2; first last.
           { eapply Forall2_app.
             - exact H4.
             - eauto. }
           rewrite mkApps_app in H2.
           rewrite EAstUtils.mkApps_app in H2.
           cbn in *. simpl in H2.
          rewrite cls in H2.
          eapply IHeval3 in H2 as (? & ? & [?]); cbn; eauto; cycle 1.
           { eapply subject_reduction. eauto. exact Hty.
             etransitivity.
             eapply PCUICReduction.red_app. eapply wcbveval_red; eauto.
             eapply wcbveval_red; eauto.
             rewrite <- !mkApps_snoc.
             eapply PCUICReduction.red1_red.
             eapply PCUICReduction.red_fix.
             rewrite closed_unfold_fix_cunfold_eq.
             now eapply subject_closed in t1.
             rewrite /cunfold_fix e0 /= //.
             pose proof (eval_to_value _ _ _ H) as vfix.
             eapply PCUICWcbvEval.stuck_fix_value_args in vfix; eauto.
             2:{ rewrite /cunfold_fix e0 //. }
             simpl in vfix.
             subst. unfold is_constructor.
             rewrite nth_error_snoc. lia.
             assert(Σ ;;; [] |- mkApps (tFix mfix idx) (argsv ++ [av]) : subst [av] 0 x1).
             { rewrite mkApps_app. eapply PCUICValidity.type_App'; eauto.
               eapply subject_reduction_eval; eauto. }
             epose proof (fix_app_is_constructor (args:=argsv ++ [av]) X).
             rewrite /unfold_fix e0 in X0.
             specialize (X0 eq_refl). simpl in X0.
             rewrite nth_error_snoc in X0. auto. apply X0.
             eapply value_axiom_free, eval_to_value; eauto.
             eapply value_whnf; eauto.
             eapply eval_closed; eauto. now eapply subject_closed in t0.
             eapply eval_to_value; eauto. }

           { constructor.
             - eapply erases_deps_eval in ev_stuck; [|now eauto].
               eapply erases_deps_mkApps_inv in ev_stuck as (? & ?).
               apply erases_deps_mkApps; [|now eauto].
               depelim H3.
               eapply nth_error_forall in H3 as H'; eauto.
               apply erases_deps_subst; [|now eauto].
               now apply Forall_All, Forall_erases_deps_fix_subst; eauto.
             - now eapply erases_deps_eval in ev_arg; eauto. }

           exists x3. split. eauto.
           constructor. eapply EWcbvEval.eval_fix.
           ++ eauto.
           ++ eauto.
           ++ eauto.
           ++ rewrite <- EWcbvEval.closed_unfold_fix_cunfold_eq.
              { unfold EGlobalEnv.unfold_fix. rewrite e.
                eapply All2_nth_error in Hmfix' as []; tea. cbn in *.
                rewrite -eargsv -(Forall2_length H4); trea. }
              eapply eval_closed in H; eauto.
              clear -H Hmfix'. rename H into e3.
              pose proof (All2_length Hmfix').
              rewrite closedn_mkApps in e3.
              apply andb_true_iff in e3 as (e3 & _).
              change (?a = true) with (is_true a) in e3.
              simpl in e3 |- *. solve_all.
              rewrite app_context_nil_l in b.
              destruct b as [eqb eqrar isl isl' e].
              eapply erases_closed in e. simpl in e.
              rewrite <- H.
              unfold EAst.test_def.
              simpl in e.
              rewrite fix_context_length in e.
              now rewrite Nat.add_0_r.
              unfold test_def in a. apply andb_and in a as [_ Hbod].
              rewrite fix_context_length.
              now rewrite Nat.add_0_r in Hbod.
              eauto with pcuic.
              now eapply subject_closed in Ht.
          ++ auto.

        -- cbn. destruct a2 as [eqb eqrar isl isl' e5].
           eapply (erases_subst Σ [] (fix_context mfix) [] dbody (fix_subst mfix)) in e5; cbn; eauto.
           ++ eapply subslet_fix_subst. now eapply wf_ext_wf. all: eassumption.
           ++ eapply nth_error_all in a1; eauto. cbn in a1.
              eapply a1.
           ++ eapply All2_from_nth_error.
              erewrite fix_subst_length, EGlobalEnv.fix_subst_length, All2_length; eauto.
              intros.
              rewrite fix_subst_nth in H3. now rewrite fix_subst_length in H2.
              rewrite efix_subst_nth in H5. rewrite fix_subst_length in H2.
              erewrite <- All2_length; eauto.
              invs H5; invs H3.
              erewrite All2_length; eauto.
      * eapply (Is_type_app _ _ _ (argsv ++ [av])) in X as []; tas.
        -- exists EAst.tBox.
           split.
           ++ econstructor.
              eapply Is_type_eval. 3:eauto. all:eauto.
              rewrite mkApps_app.
              eapply eval_fix; eauto.
              1-2:eapply value_final, eval_to_value; eauto.
              rewrite /cunfold_fix e0 //. congruence.
           ++ constructor. eapply EWcbvEval.eval_box; [|now eauto].
              apply eval_to_mkApps_tBox_inv in ev_stuck as ?; subst.
              eauto.
        -- eauto.
        -- rewrite mkApps_snoc.
           eapply PCUICValidity.type_App'; eauto.
           eapply subject_reduction; eauto.
           eapply wcbveval_red; eauto.

  - apply inversion_App in Hty as Hty'; [|eauto].
    destruct Hty' as (? & ? & ? & ? & ? & ?).

    eapply subject_reduction in t as typ_stuck_fix; [|eauto|]; first last.
    { eapply wcbveval_red; eauto. }

    eapply erases_App in He as [(-> & [])|(? & ? & -> & ? & ?)].
    + exists E.tBox.
      split; [|now constructor; eauto using @EWcbvEval.eval].
      constructor.
      eapply Is_type_red.
      * eauto.
      * eapply PCUICReduction.red_app.
        -- eapply wcbveval_red; revgoals; eauto.
        -- eapply wcbveval_red; revgoals; eauto.
      * eauto.
    + depelim Hed.
      eapply subject_reduction in t0 as typ_arg; [|eauto|]; first last.
      { eapply wcbveval_red; revgoals; eauto. }

      eapply IHeval1 in H1 as (? & ? & [?]); [|now eauto|now eauto].
      eapply IHeval2 in H2 as (? & ? & [?]); [|now eauto|now eauto].
      eapply erases_mkApps_inv in H1.
      destruct H1 as [(? & ? & ? & -> & [] & ? & ? & ->)|(? & ? & -> & ? & ?)].
      * apply eval_to_mkApps_tBox_inv in H3 as ?; subst.
        depelim H5.
        rewrite -> !app_nil_r in *.
        cbn in *.
        exists E.tBox.
        split; [|now constructor; eauto using @EWcbvEval.eval].
        eapply (Is_type_app _ _ _ [av]) in X as [].
        -- constructor.
           apply X.
        -- eauto.
        -- eauto.
        -- cbn.
           eapply PCUICValidity.type_App'; eauto.
      * depelim H1.
        -- exists (E.tApp (E.mkApps (E.tFix mfix' idx) x7) x5).
           split; [eauto using erases_tApp, erases_mkApps|].
           unfold cunfold_fix in *.
           destruct (nth_error _ _) eqn:nth; [|congruence].
           eapply All2_nth_error_Some in X as (?&?&[? ? ? ? ?]); [|eauto].
           constructor. eapply EWcbvEval.eval_fix_value.
           ++ eauto.
           ++ eauto.
           ++ eauto.
           ++ unfold EGlobalEnv.cunfold_fix. now rewrite e.
           ++ eapply Forall2_length in H5. noconf e1. lia.

        -- exists E.tBox.
           apply eval_to_mkApps_tBox_inv in H3 as ?; subst.
           split; [|now constructor; eauto using @EWcbvEval.eval].
           eapply Is_type_app in X as [].
           ++ constructor.
              rewrite <- mkApps_snoc.
              exact X.
           ++ eauto.
           ++ eauto.
           ++ rewrite mkApps_snoc.
              eapply PCUICValidity.type_App'; eauto.

  - assert (Hty' := Hty).
    eapply inversion_Case in Hty' as [mdecl [idecl [decli [args' [[] ht0]]]]]; auto.
    assert (t0' := scrut_ty).
    pose proof H as Heval.
    eapply subject_reduction_eval in t0' as t1. 2: eauto.
    eapply PCUICValidity.inversion_mkApps in t1 as (? & ? & ?); eauto.
    pose proof (subject_closed t) as clfix.
    assert (htcof : Σ ;;; [] |- tCase ip p (mkApps (tCoFix mfix idx) args) brs : T).
    { eapply subject_reduction; eauto. eapply PCUICReduction.red_case_c.
      eapply wcbveval_red in H; eauto. }
    assert (hredcasecof :
      PCUICReduction.red Σ [] (tCase ip p (mkApps (tCoFix mfix idx) args) brs)
        (tCase ip p (mkApps fn args) brs)).
    { constructor; eapply PCUICReduction.red_cofix_case.
        move: e. rewrite closed_unfold_cofix_cunfold_eq; eauto. }
    assert (htcasefn : Σ ;;; [] |- tCase ip p (mkApps fn args) brs : T).
    { eapply subject_reduction; eauto. }
    assert (hredcasediscrcof :
      PCUICReduction.red Σ [] (tCase ip p discr brs) res).
    { etransitivity. eapply PCUICReduction.red_case_c; tea.
      eapply wcbveval_red in H. tea. eauto.
      etransitivity; tea. eapply wcbveval_red; tea. }
    assert (htunfcof : Σ ;;; [] |- tCase ip p (mkApps fn args) brs : T).
    { eapply subject_reduction; eauto. }
    specialize (IHeval1 _ t0').
    specialize (IHeval2 _ htunfcof).
    eapply inversion_CoFix in t; destruct_sigma t; auto.
    pose proof (wfΣ' := wfΣ.1).
    eapply PCUICSpine.typing_spine_strengthen in t0; eauto.
    2:{ now eapply nth_error_all, isTypeRel_isType in a; tea. }
    invs He.
    * edestruct IHeval1 as (? & ? & ?); eauto. now depelim Hed.
      depelim Hed. rename H5 into Hlen.
      rename H6 into H5. rename H7 into H6. rename H8 into H7.
      rename H9 into H8. rename H10 into H9.
      unshelve eapply declared_inductive_to_gen in H1, decli; eauto.
      destruct (declared_inductive_inj H1 decli). subst mdecl0 idecl0.
      rename H0 into decli'. rename H1 into decli''. rename H2 into er. rename H3 into H0.
      eapply erases_mkApps_inv in H8; eauto.
      destruct H8 as [He|He]; destruct_sigma He.
      -- destruct He as (? & ? & ? & ? & ? & ? & ? & ?). subst.
        destruct H9.
        edestruct IHeval2 as (? & ? & [?]).
        { destruct H2 as [i1]. constructor; eauto.
          rewrite mkApps_app.
          eapply erases_mkApps. instantiate(1:=EAst.tBox).
          constructor.
          eapply isErasable_Proof.
          eapply tCoFix_no_Type in i1; auto.
          pose proof i1 as X0'. destruct X0' as [tyapp [u [Htyapp Hu]]].
          eapply Is_proof_ty; eauto.
          eapply unfold_cofix_type; eauto.
          move: e. rewrite -closed_unfold_cofix_cunfold_eq // /unfold_cofix e0.
          intros e; eapply e. eauto. }
        { destruct (declared_inductive_inj decli'' decli); subst.
          econstructor; eauto.
          eapply declared_inductive_from_gen; eauto.  }
        destruct H2.
        eapply tCoFix_no_Type in X0; auto.
        move: (eval_to_mkApps_tBox_inv _ _ H1). intros ->. depelim H8.
        rewrite -> app_nil_r in *.
        exists x0; split; [|constructor]; auto.
        eapply eval_case_eval_inv_discr; tea.
      -- destruct H9.
        destruct He as [f' [L' [-> [hcof hl']]]].
        have clfix' : ELiftSubst.closed f'.
        { now eapply erases_closed in hcof; tea. }
        depelim hcof.
        { eapply All2_nth_error_Some in X0 as X'; tea.
          destruct X' as [t' [nth' [bn [rar eb]]]].
          specialize (IHeval2 (E.tCase (ip, ci_npar ip)
            (E.mkApps (ELiftSubst.subst0 (EGlobalEnv.cofix_subst mfix') (E.dbody t')) L') brs')).
          forward IHeval2.
          econstructor; eauto.
          eapply erases_mkApps.
          move: e0 e. rewrite -closed_unfold_cofix_cunfold_eq //.
          unfold unfold_cofix. intros hnth; rewrite hnth. intros [=].
          subst fn narg.
          eapply All_nth_error in a0 as a'; tea. apply unlift_TermTyp in a'.
          eapply erases_subst0. eauto. 2:eauto. pcuic. all:tea.
          { rewrite app_context_nil_l. eapply subslet_cofix_subst; eauto.
            econstructor; eauto. }
          {eapply All2_from_nth_error.
            erewrite cofix_subst_length, EGlobalEnv.cofix_subst_length, All2_length; eauto.
            intros.
            rewrite cofix_subst_nth in H3. now rewrite cofix_subst_length in H2.
            rewrite ecofix_subst_nth in H8. rewrite cofix_subst_length in H2.
            erewrite <- All2_length; eauto.
            invs H3; invs H8.
            erewrite All2_length; eauto. }
          destruct IHeval2 as [v' [Hv' [ev]]].
          { econstructor; eauto.
            apply declared_inductive_from_gen; eauto.
            eapply erases_deps_eval in Hed. 2:tea.
            apply erases_deps_mkApps_inv in Hed as (edcofix & edargs).
            depelim edcofix.
            apply erases_deps_mkApps; [|now eauto].
            apply erases_deps_subst.
            - now apply Forall_All, Forall_erases_deps_cofix_subst; eauto.
            - now eapply nth_error_forall in H2; eauto. }
          exists v'. split => //. split.
          eapply EWcbvEval.eval_cofix_case; tea.
          rewrite /EGlobalEnv.cunfold_cofix nth' //. f_equal.
          f_equal.
          rewrite -(EWcbvEval.closed_cofix_substl_subst_eq (idx:=idx)) //. }
        { eapply eval_to_mkApps_tBox_inv in H1 as H'; subst L'; cbn in *. depelim hl'.
          edestruct IHeval1 as (? & ? & [?]); tea.
          pose proof (EWcbvEval.eval_deterministic H1 H3). subst x0.
          eapply erases_deps_eval in Hed; tea.
          specialize (IHeval2 (E.tCase (ip, ci_npar ip) E.tBox brs')).
          forward IHeval2.
          econstructor; eauto. cbn.
          move: e0 e. rewrite -closed_unfold_cofix_cunfold_eq //.
          unfold unfold_cofix. intros hnth; rewrite hnth. intros [=].
          subst fn narg.
          constructor.
          eapply isErasable_unfold_cofix; tea.
          destruct IHeval2 as [v' [Hv' [ev]]].
          { econstructor; eauto.
            apply declared_inductive_from_gen; eauto. }
          exists v'. split => //. split.
          eapply eval_case_eval_inv_discr; tea. }

    * depelim Hed.
      exists E.tBox. split; repeat constructor; auto.
      assert (PCUICReduction.red Σ [] (tCase ip p discr brs) res).
      eapply wcbveval_red in Heval; tea.
      now eapply isErasable_red.

  - assert (Hty' := Hty).
    eapply inversion_Proj in Hty' as (? & ? & ? & ? & [] & ? & ? & ? & e0 & e1); auto.
    pose proof (t0' := t).
    pose proof (subject_closed t) as cldiscr.
    assert(clcof : PCUICAst.closedn 0 (mkApps (tCoFix mfix idx) args)).
    { eapply eval_closed; tea; eauto. }
    move: clcof; rewrite closedn_mkApps => /andP[] clcofix clargs.
    eapply subject_reduction_eval in t as t0''; tea.
    eapply inversion_mkApps in t0'' as (? & ? & ?).
    eapply type_tCoFix_inv in t0 as t1'; eauto.
    destruct_sigma t1'; auto.
    eapply inversion_CoFix in t0; destruct_sigma t0.
    destruct p0 as [[hnth wfcof] hdef].
    eapply PCUICSpine.typing_spine_strengthen in t1; eauto.
    2:{ now eapply validity. }
    assert(Hty' := Hty).
    eapply subject_reduction in Hty'. 2:auto.
    2:{ etransitivity. eapply PCUICReduction.red_proj_c.
        eapply wcbveval_red; tea.
        constructor. eapply PCUICReduction.red_cofix_proj. eauto.
        rewrite closed_unfold_cofix_cunfold_eq; eauto. }
    specialize (IHeval2 _ Hty').
    specialize (IHeval1 _ t).
    pose proof (wfΣ' := wfΣ.1).
    invs He.
    * depelim Hed.
      unshelve eapply declared_projection_to_gen in d, H1; eauto.
      destruct (declared_projection_inj d H1) as [? [? []]]. subst x0 x1 x2 pdecl.
      rename H1 into decli. rename H2 into decli'.
      rename H3 into erm. rename H4 into erb.
      destruct (IHeval1 _ H6 Hed) as [dv' [? []]].
      eapply erases_mkApps_inv in H1 as []; eauto.
      { destruct H1 as (? & ? & ? & ? & ? & ? & ? & ?). subst.
        destruct H3.
        eapply eval_to_mkApps_tBox_inv in H2 as H'. subst. depelim H7.
        edestruct IHeval2 as (? & ? & [?]).
        { constructor; eauto.
          instantiate(1:=EAst.tBox).
          constructor.
          eapply isErasable_Proof.
          eapply tCoFix_no_Type in X; auto.
          pose proof X as X0'. destruct X0' as [tyapp [u [Htyapp Hu]]].
          eapply Is_proof_ty; eauto.
          move: e. rewrite -closed_unfold_cofix_cunfold_eq // /unfold_cofix e2.
          intros [= <- <-].
          eapply unfold_cofix_type; eauto.
          2:{ unfold unfold_cofix; erewrite e2. reflexivity. }
          now rewrite app_nil_r. }
        { eapply erases_deps_eval in Hed. 2:tea.
          apply erases_deps_mkApps_inv in Hed as (_ & edargs).
          econstructor; eauto.
          apply declared_projection_from_gen; eauto.
          constructor. }
        exists x1; split; [|constructor]; auto.
        eapply eval_proj_eval_inv_discr; tea. }
      { destruct H1 as [f' [L' [-> [hcof hl']]]].
        have clfix' : ELiftSubst.closed f'.
        { now eapply erases_closed in hcof; tea. }
        depelim hcof.
        { eapply All2_nth_error_Some in X as X'; tea.
          destruct X' as [t' [nth' [bn [rar eb]]]].
          specialize (IHeval2 (E.tProj p
            (E.mkApps (ELiftSubst.subst0 (EGlobalEnv.cofix_subst mfix') (E.dbody t')) L'))).
          forward IHeval2.
          econstructor; eauto.
          eapply erases_mkApps.
          move: hnth e. rewrite -closed_unfold_cofix_cunfold_eq //.
          unfold unfold_cofix. intros hnth'; rewrite hnth'. intros [=].
          subst fn narg. rewrite hnth' in e2. noconf e2.
          eapply All_nth_error in a0 as a'; tea. eapply unlift_TermTyp in a'.
          eapply erases_subst0. eauto. 2:eauto. pcuic. all:tea.
          { rewrite app_context_nil_l. eapply subslet_cofix_subst; eauto.
            econstructor; eauto. }
          {eapply All2_from_nth_error.
            erewrite cofix_subst_length, EGlobalEnv.cofix_subst_length, All2_length; eauto.
            intros.
            rewrite cofix_subst_nth in H3. now rewrite cofix_subst_length in H1.
            rewrite ecofix_subst_nth in H4. rewrite cofix_subst_length in H1.
            erewrite <- All2_length; eauto.
            invs H3; invs H4.
            erewrite All2_length; eauto. }
          destruct IHeval2 as [v' [Hv' [ev]]].
          { econstructor; eauto.
            eapply declared_projection_from_gen; eauto.
            eapply erases_deps_eval in Hed. 2:tea.
            apply erases_deps_mkApps_inv in Hed as (edcofix & edargs).
            depelim edcofix.
            apply erases_deps_mkApps; [|now eauto].
            apply erases_deps_subst.
            - now apply Forall_All, Forall_erases_deps_cofix_subst; eauto.
            - now eapply nth_error_forall in H1; eauto. }
          exists v'. split => //. split.
          eapply EWcbvEval.eval_cofix_proj; tea.
          rewrite /EGlobalEnv.cunfold_cofix nth' //. f_equal.
          f_equal.
          rewrite -(EWcbvEval.closed_cofix_substl_subst_eq (idx:=idx)) //. }
        { eapply eval_to_mkApps_tBox_inv in H2 as H'; subst L'; cbn in *. depelim hl'.
          edestruct IHeval1 as (? & ? & [?]); tea.
          pose proof (EWcbvEval.eval_deterministic H3 H2). subst x0.
          eapply erases_deps_eval in Hed; tea.
          specialize (IHeval2 (E.tProj p E.tBox)).
          forward IHeval2.
          econstructor; eauto. cbn.
          move: hnth e. rewrite -closed_unfold_cofix_cunfold_eq //.
          unfold unfold_cofix. intros hnth; rewrite hnth. intros [=].
          subst fn narg.
          constructor.
          eapply isErasable_unfold_cofix; tea.
          destruct IHeval2 as [v' [Hv' [ev]]].
          { econstructor; eauto.
            eapply declared_projection_from_gen; eauto. }
          exists v'. split => //. split.
          eapply eval_proj_eval_inv_discr; tea. }
      }

    * depelim Hed.
      exists E.tBox. split; repeat constructor; auto.
      assert (PCUICReduction.red Σ [] (tProj p discr) res).
      eapply wcbveval_red in H0; tea.
      etransitivity; tea.
      etransitivity. eapply PCUICReduction.red_proj_c.
      eapply wcbveval_red; tea.
      constructor. eapply PCUICReduction.red_cofix_proj.
      move: e. rewrite closed_unfold_cofix_cunfold_eq //. intros e; exact e.
      now eapply isErasable_red.

    * eauto.

  - pose (Hty' := Hty).
    eapply inversion_App in Hty' as (? & ? & ? & ? & ? & ?); eauto.
    invs He.
    + depelim Hed.
      assert (t' := t). eapply IHeval1 in t as (? & ? & [?]); eauto.
      eapply IHeval2 in t0 as (? & ? & [?]); eauto.
      destruct (EAstUtils.isBox x2) eqn:E.
      * destruct x2; invs E. exists EAst.tBox. split. 2: now constructor; econstructor; eauto.
        pose proof (Is_type_app Σ [] (mkApps (tConstruct ind c u) args) [a']).
        inversion H1.
        edestruct H7; eauto. cbn. eapply subject_reduction. eauto.
        exact Hty. eapply PCUICReduction.red_app.
        eapply wcbveval_red; eauto.
        eapply inversion_App in Hty as [na [A [B [Hf [Ha _]]]]]; eauto.
        eapply wcbveval_red; eauto. constructor. rewrite mkApps_app //.
      * exists (E.tApp x2 x3).
        rewrite mkApps_app.
        split; [econstructor; eauto|].
        eapply erases_mkApps_inv in H1; eauto.
        destruct H1 as [].
        { destruct H1 as (? & ? & ? & ? & ? & ? & ? & ?). subst.
          eapply eval_to_mkApps_tBox_inv in H2 as H'. subst. depelim H9.
          now cbn in E. }
        destruct H1 as [f'' [L' [eq []]]].
        subst x2.
        depelim H1.
        2:{ eapply eval_to_mkApps_tBox_inv in H2 as H'. subst. now cbn in E. }
        eapply erases_deps_eval in Hed1; tea.
        eapply erases_deps_mkApps_inv in Hed1 as [].
        depelim H8.
        constructor. eapply EWcbvEval.eval_construct; tea. eauto.
        eapply (EGlobalEnv.declared_constructor_lookup H9).
        rewrite -(Forall2_length H7).
        rewrite /EAst.cstr_arity.
        pose proof (wfΣ' := wfΣ.1).
        unshelve eapply declared_constructor_to_gen in H8; eauto.
        destruct (declared_constructor_inj H8 d) as [? []]. subst mdecl0 idecl0 cdecl0.
        destruct H8, H9, H11 as [Hc _].
        eapply Forall2_nth_error_Some in Hc as [? []]; tea.
        rewrite H14 in H11. noconf H11.
        destruct cdecl' as [cname cargs]; cbn. cbn in *.
        destruct H15 as [<- _].
        destruct H10 as [_ <-].
        move: l. rewrite /cstr_arity.
        clear -d wfΣ.
        eapply declared_constructor_from_gen in d.
        destruct (on_declared_constructor d) as [_ [? []]].
        eapply cstr_args_length in o. lia.
    + exists E.tBox. split => //. 2:repeat constructor.
      econstructor.
      eapply inversion_App in Hty as [na [A [B [Hf [Ha _]]]]]; auto.
      eapply Is_type_red. 3:eauto. eauto.
      rewrite mkApps_app.
      eapply PCUICReduction.red_app.
      eapply subject_closed in Hf; auto.
      eapply wcbveval_red; eauto.
      eapply subject_closed in Ha; auto.
      eapply wcbveval_red; eauto.

  - pose (Hty' := Hty).
    eapply inversion_App in Hty' as (? & ? & ? & ? & ? & ?); eauto.
    invs He.
    + depelim Hed.
      assert (t' := t). eapply IHeval1 in t as (? & ? & [?]); eauto.
      eapply IHeval2 in t0 as (? & ? & [?]); eauto.
      destruct (EAstUtils.isBox x2) eqn:E.
      * destruct x2; invs E. exists EAst.tBox. split. 2: now constructor; econstructor; eauto.
        pose proof (Is_type_app Σ [] f' [a']).
        inversion H1.
        edestruct H7; eauto. cbn. eapply subject_reduction. eauto.
        exact Hty. eapply PCUICReduction.red_app.
        eapply wcbveval_red; eauto.
        eapply inversion_App in Hty as [na [A [B [Hf [Ha _]]]]]; eauto.
        eapply wcbveval_red; eauto.
      * exists (E.tApp x2 x3).
        split; [econstructor; eauto|].
        constructor; eapply EWcbvEval.eval_app_cong; eauto.
        eapply ssrbool.negbT.
        repeat eapply orb_false_intro.
        -- destruct x2; try reflexivity.
          invs H1. invs i.
        -- destruct x2 eqn:Ex; try reflexivity.
          ++ cbn. invs H1. cbn in *.
            eapply ssrbool.negbTE, is_FixApp_erases.
            econstructor; eauto.
            rewrite orb_false_r !negb_or in i.
            now move/andP: i => [] /andP [].
          ++ cbn in *.
            invs H1. invs i.
        -- eauto.
        -- rewrite !negb_or in i.
           rtoProp; intuition auto.
           eapply is_ConstructApp_erases in H9; tea.
           now move/negbTE: H9.
        -- rewrite !negb_or in i. rtoProp; intuition auto.
           eapply is_PrimApp_erases in H8; tea.
           now move/negbTE: H8.
        -- rewrite !negb_or in i.
           rtoProp; intuition auto.
           apply/negbTE. apply PCUICNormal.negb_is_true => isl.
           eapply erases_lazy in H1; tea.
    + exists EAst.tBox. split. 2: now constructor; econstructor.
      econstructor.
      eapply inversion_App in Hty as [na [A [B [Hf [Ha _]]]]]; auto.
      eapply Is_type_red. 3:eauto. eauto.
      eapply PCUICReduction.red_app.
      eapply subject_closed in Hf; auto.
      eapply wcbveval_red; eauto.
      eapply subject_closed in Ha; auto.
      eapply wcbveval_red; eauto.

  - depelim X; (depelim He; try depelim H; [|now eapply nisErasable_tPrim in X]).
    + exists (EAst.tPrim (EPrimitive.prim_int i)); split => //; repeat constructor.
      depelim X. constructor.
    + exists (EAst.tPrim (EPrimitive.prim_float f)); split => //; repeat constructor.
      depelim X. constructor.
    + exists (EAst.tPrim (EPrimitive.prim_string s)); split => //; repeat constructor.
      depelim X. constructor.
    + depelim X. subst a0 a'; cbn in *.
      depelim Hed; cbn in *.
      eapply inversion_Prim in Hty as [prim_ty [cdecl []]]; cbn in *; eauto.
      depelim p0; cbn in *. eapply e in hdef as [d' [er [e'v]]]; tea.
      eapply All2_undep in a.
      eapply (All2_apply ty) in a.
      assert (exists ev, ∥ All3 (fun x y z => erases Σ [] x z /\ ∥ Σ' ⊢ y ⇓ z ∥) v' ev0 ev ∥).
      { clear -a a2 H hvalue.
        solve_all.
        induction a in ev0, a2 |- *; depelim a2.
        + exists []; repeat constructor.
        + destruct (IHa _ a2) as [x0 [hx0]]. destruct p as [[] ?].
          specialize (r t _ e e0) as [v' []].
          exists (v' :: x0). sq. repeat constructor; intuition eauto. }
      destruct H0 as [evr [Hevr]].
      exists (EAst.tPrim (EPrimitive.prim_array {| EPrimitive.array_default := d'; EPrimitive.array_value := evr |})); split => //; eauto.
      repeat constructor; eauto.
      * clear -Hevr; induction Hevr; constructor; intuition eauto.
      * clear -Hevr e'v; induction Hevr. repeat constructor; eauto.
        destruct r; sq. constructor; intuition eauto. constructor; eauto. depelim IHHevr. depelim e. constructor; eauto. now cbn in i.

  - destruct t; try easy.
    + invs He. eexists. split; eauto. now constructor; econstructor.
    + invs He. eexists. split; eauto. now constructor; econstructor.
    + invs He.
      * eexists. split; eauto. now constructor; econstructor.
      * eexists. split. 2: now constructor; econstructor.
        econstructor; eauto.
    + invs He.
      * eexists. split. 2: now constructor; econstructor.
        econstructor; eauto.
    + invs He.
      * eexists. split. 2:{ constructor. eapply EWcbvEval.eval_atom. cbn [EWcbvEval.atom].
        depelim Hed. eapply EGlobalEnv.declared_constructor_lookup in H0. now rewrite H0. }
        econstructor; eauto.
      * eexists. split. 2: now constructor; econstructor.
        eauto.
    + invs He.
      * eexists. split; eauto. now constructor; econstructor.
      * eexists. split. 2: now constructor; econstructor.
        econstructor; eauto.
    + invs He.
      * eexists. split; eauto. now constructor; econstructor.
      * eexists. split. 2: now constructor; econstructor.
        econstructor; eauto.
        Unshelve. all: repeat econstructor.
Qed.
```

### child `dearg_transform_correct`: [`erasure/theories/Typed/OptimizeCorrectness.v` lines 5179-5200](https://github.com/MetaRocq/metarocq/blob/51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56/erasure/theories/Typed/OptimizeCorrectness.v#L5179-L5200) ([local copy](code/erasure/theories/Typed/OptimizeCorrectness.v))

```coq
Lemma dearg_transform_correct {wfl : WcbvFlags} overridden_masks do_trim_const_masks do_trim_ctor_masks :
  ExtractTransformCorrect (dearg_transform overridden_masks do_trim_const_masks do_trim_ctor_masks true true true).
Proof.
  red.
  intros Σ Σopt kn ind c block opt ev.
  cbn in opt.
  destruct env_closed eqn:clos; cbn in *; [|congruence].
  destruct analyze_env; cbn in *.
  destruct is_expanded_env eqn:exp; cbn in *; [|congruence].
  destruct valid_masks_env eqn:valid; cbn in *; [|congruence].
  injection opt as <-.
  set (im := (if do_trim_ctor_masks then trim_ind_masks else id) ind_masks) in *; clearbody im.
  set (cm := (if do_trim_const_masks then trim_const_masks else id) const_masks) in *; clearbody cm.
  apply eval_debox_env_types;eauto.
  eapply eval_const_construct_expanded in ev as expanded_const; eauto.
  eapply eval_is_expanded_aux in ev as empty_ctor_mask; eauto.
  cbn in *.
  replace (tConst kn) with (dearg im cm (tConst kn)).
  replace (tConstruct ind c []) with (dearg im cm (tConstruct ind c [])).
  2-3: now cbn; destruct get_const_mask, get_ctor_mask.
  apply dearg_correct; eauto.
Qed.
```

### child `optimize_correct`: [`erasure/theories/Typed/ExtractionCorrectness.v` lines 506-527](https://github.com/MetaRocq/metarocq/blob/51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56/erasure/theories/Typed/ExtractionCorrectness.v#L506-L527) ([local copy](code/erasure/theories/Typed/ExtractionCorrectness.v))

```coq
Lemma optimize_correct `{EWellformed.EEnvFlags} Σ fgΣ t v :
  ELiftSubst.closed t = true ->
  EGlobalEnv.closed_env (trans_env Σ) = true ->
  EWellformed.wf_glob (trans_env Σ) ->
  @EWcbvEval.eval default_wcbv_flags (trans_env Σ) t v ->
  @EWcbvEval.eval
      (EWcbvEval.disable_prop_cases opt_wcbv_flags)
      (trans_env (map (on_snd (remove_match_on_box_decl (EEnvMap.GlobalContextMap.make (trans_env Σ) (OptimizePropDiscr.trans_env_fresh_globals _ fgΣ)))) Σ))
      (EOptimizePropDiscr.remove_match_on_box (EEnvMap.GlobalContextMap.make (trans_env Σ) (OptimizePropDiscr.trans_env_fresh_globals _ fgΣ)) t)
      (EOptimizePropDiscr.remove_match_on_box (EEnvMap.GlobalContextMap.make (trans_env Σ) (OptimizePropDiscr.trans_env_fresh_globals _ fgΣ)) v).
Proof.
  intros cl_t cl_env wfg ev.
  remember (EEnvMap.GlobalContextMap.make _ _) as Σ0.
  assert (trans_env (map (on_snd (remove_match_on_box_decl Σ0)) Σ) =
    EOptimizePropDiscr.remove_match_on_box_env Σ0) as ->.
  { cbn. rewrite /trans_env HeqΣ0 map_map_compose. cbn. rewrite /trans_env.
    rewrite map_map_compose /on_snd. cbn. eapply map_ext.
    intros [[] []]; cbn. destruct c as [[] []] => //. reflexivity.
    do 2 f_equal. rewrite /EOptimizePropDiscr.remove_match_on_box_constant_decl /=.
    now destruct o; cbn. }
  unshelve eapply (EOptimizePropDiscr.remove_match_on_box_correct (fl := default_wcbv_flags) (Σ := Σ0));subst;cbn;eauto.
Qed.
```

### child `wf_erase_global_decls_recursive`: [`erasure/theories/Typed/ExtractionCorrectness.v` lines 440-476](https://github.com/MetaRocq/metarocq/blob/51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56/erasure/theories/Typed/ExtractionCorrectness.v#L440-L476) ([local copy](code/erasure/theories/Typed/ExtractionCorrectness.v))

```coq
Lemma wf_erase_global_decls_recursive (H := EWellformed.all_env_flags) :
  forall X_type X decls univs retros w seeds (ignored : kername -> bool),
    (forall k, ignored k = false) ->
    let Σex := @Erasure.erase_global_decls_deps_recursive X_type X decls univs retros w seeds ignored in
    EWellformed.wf_glob (trans_env Σex).
Proof.
  intros X_type X decls univs retros w seeds ignored hign ?.
  subst Σex.
  revert seeds.
  induction decls in X_type, X, w |- *;intros seeds;auto;try constructor.
  simpl.
  destruct a;simpl.
  destruct (KernameSet.mem _ _);cbn.
  - unfold MRProd.test_snd;cbn.
    constructor.
    * unfold trans_env in *;cbn in *.
      apply IHdecls.
    * cbn.
      remember (KernameSet.union _ _) as kns.
      rewrite hign in Heqkns. cbn in Heqkns.
      remember (Erasure.erase_global_decls_deps_recursive decls univs _ _ _ _) as Σex.
      assert (EWellformed.wf_glob (trans_env Σex)) by now subst Σex.
      rewrite -/(trans_env _).
      eapply wf_erase_global_decl; eauto. rewrite HeqΣex. f_equal. exact Heqkns.
    * sq.
      apply OptimizePropDiscr.trans_env_fresh_global.
      apply fresh_globals_erase_global_decl_rec.
      change decls with (PEnv.declarations
        {| PEnv.universes := univs; PEnv.declarations := decls; PEnv.retroknowledge := retros |}).
      eapply Erasure.abstract_eq_wf in w as [? []].
      apply PCUICWfEnvImpl.wf_fresh_globals; eauto.
      eapply Erasure.wf_pop_decl in X0; trea. eapply X0.
      apply fresh_global_erase_global_decl_rec.
      eapply Erasure.abstract_eq_wf in w as [? []].
      eapply PCUICWfEnvImpl.wf_fresh_globals in X0. now depelim X0.
  - apply IHdecls.
Qed.
```

### child `global_erased_with_deps_erases_deps_tConst`: [`erasure/theories/Typed/ExtractionCorrectness.v` lines 66-77](https://github.com/MetaRocq/metarocq/blob/51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56/erasure/theories/Typed/ExtractionCorrectness.v#L66-L77) ([local copy](code/erasure/theories/Typed/ExtractionCorrectness.v))

```coq
Lemma global_erased_with_deps_erases_deps_tConst Σ Σer kn cst :
  wf Σ ->
  P.declared_constant Σ kn cst ->
  global_erased_with_deps Σ Σer kn ->
  erases_deps Σ Σer (E.tConst kn).
Proof.
  intros wf decl glob.
  destruct glob as [(?&?&?&?&?&?)|(?&?&?&?&?)].
  - econstructor; eauto.
  - unfold P.declared_constant, PCUICAst.declared_minductive in *.
    eapply lookup_env_In in decl; tea. now cbn in decl. auto.
Qed.
```

### child `erase_global_decls_deps_recursive_correct`: [`erasure/theories/Typed/ErasureCorrectness.v` lines 296-303](https://github.com/MetaRocq/metarocq/blob/51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56/erasure/theories/Typed/ErasureCorrectness.v#L296-L303) ([local copy](code/erasure/theories/Typed/ErasureCorrectness.v))

```coq
Lemma erase_global_decls_deps_recursive_correct decls univs retro wfΣ include ignore_deps :
  let Σ := mk_global_env univs decls retro in
  (forall k, ignore_deps k = false) ->
  (forall k, KernameSet.In k include -> P.lookup_env Σ k <> None) ->
  includes_deps Σ (trans_env (erase_global_decls_deps_recursive (X_type := X_type) (X := X) decls univs retro wfΣ include ignore_deps)) include.
Proof.
  intros; eapply erase_global_decls_deps_recursive_correct_gen; eauto. reflexivity.
Qed.
```

### child `inversion_Const`: [`pcuic/theories/PCUICInversion.v` lines 211-221](https://github.com/MetaRocq/metarocq/blob/51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56/pcuic/theories/PCUICInversion.v#L211-L221) ([local copy](code/pcuic/theories/PCUICInversion.v))

```coq
  Lemma inversion_Const :
    forall {Γ c u T},
      Σ ;;; Γ |- tConst c u : T ->
      ∑ decl,
        wf_local Σ Γ ×
        declared_constant Σ c decl ×
        (consistent_instance_ext Σ decl.(cst_universes) u) ×
        Σ ;;; Γ ⊢ subst_instance u (cst_type decl) ≤ T.
  Proof using wfΣ.
    intros Γ c u T h. invtac h.
  Qed.
```

### context `ExtractTransformCorrect`: [`erasure/theories/Typed/Transform.v` lines 15-20](https://github.com/MetaRocq/metarocq/blob/51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56/erasure/theories/Typed/Transform.v#L15-L20) ([local copy](code/erasure/theories/Typed/Transform.v))

```coq
Definition ExtractTransformCorrect `{wcbvf : EWcbvEval.WcbvFlags} (transform : ExtractTransform) : Type :=
  forall Σ Σopt kn ind c,
    EWcbvEval.with_constructor_as_block = false ->
    transform Σ = Ok Σopt ->
    trans_env Σ e⊢ tConst kn ⇓ tConstruct ind c [] ->
    trans_env Σopt e⊢ tConst kn ⇓ tConstruct ind c [].
```

How the parts fit. The glue (lines 545-579) threads eight named lemmas, one
per pass plus the side conditions they need. The graph:

```
extract_correct (parent, the glue)
├── eapply erases_correct                        erasure pass correctness
│     ├── depelim erase_to; constructor          (the erased value is a constructor)
│     ├── eapply dearg_transform_correct         dearging pass correctness
│     │     └─ reduces to dearg_correct
│     └── eapply optimize_correct                match-on-box removal correctness
│           ├─ wf_glob discharged by wf_erase_global_decls_recursive
│           └─ reduces to remove_match_on_box_correct
│     └── erases_deps hypothesis:
│           ├─ inversion_Const                                  declared_constant
│           ├─ global_erased_with_deps_erases_deps_tConst         declared -> erases_deps
│           └─ erase_global_decls_deps_recursive_correct          erased env includes deps
└── Unshelve: fresh_globals_erase_global_decl_rec
```

The glue first runs `dearg_transform` (line 547), then `eapply erases_correct`
(550) to obtain the erased evaluation `trans_env eΣ e⊢ E.tConst kn ⇓
E.tConstruct ind c []`. That call opens three obligations. (a) The erased value
is a constructor: `depelim erase_to; constructor` (554-555). (b) Compose the
remaining two passes on that constructor: `eapply dearg_transform_correct`
(556) then `eapply (@optimize_correct …)` (558); optimize_correct's `wf_glob
(trans_env eΣ)` hypothesis is discharged by `wf_erase_global_decls_recursive`
(561, 563) plus `wellformed_closed_env`. (c) The `erases_deps` hypothesis:
`inversion_Const` (565) recovers the declared constant,
`global_erased_with_deps_erases_deps_tConst` (567) turns declared +
globally-erased-with-deps into `erases_deps`, and
`erase_global_decls_deps_recursive_correct` (571) proves the erased
environment includes the dependencies (`lookup_global_In_wf` and
`KernameSet.singleton_spec` close the last facts). A final `Unshelve`
discharges a shelved freshness goal with `fresh_globals_erase_global_decl_rec`
(578).

Each child is a self-contained statement whose proof closes on its own (all
eight are `Qed.`), so the glue never opens a pass's internals:

- `erases_correct` — the erasure pass: a well-typed `t` erasing to `t'` and
  evaluating to `v` yields a `v'` with `v` erasing to `v'` and `t'` evaluating
  to `v'`. Proved once by induction on the PCUIC evaluation relation, using
  inversion lemmas (`inversion_App`, `inversion_LetIn`) and `erases_subst`; it
  knows nothing about dearging or optimization, so it closes before those
  passes are even named.
- `dearg_transform_correct` — the dearging pass, stated as
  `ExtractTransformCorrect (dearg_transform …)`. Its proof reduces to
  `dearg_correct` (line 5199). A good leaf because dearging is proven against
  its own analysis (`analyze_env`, `is_expanded_env`, `valid_masks_env`), not
  against the shape of the erased term.
- `optimize_correct` — the match-on-box removal pass, stated locally in the
  parent's file. Reduces to `EOptimizePropDiscr.remove_match_on_box_correct`
  (line 526). A good leaf: it needs only closedness and well-formedness, which
  the glue supplies from `wf_erase_global_decls_recursive`.
- `wf_erase_global_decls_recursive` — "the recursively erased environment is
  well-formed", by induction over declarations plus `wf_erase_global_decl`.
  Discharges optimize_correct's well-formedness side condition.
- `global_erased_with_deps_erases_deps_tConst` — "declared +
  globally-erased-with-deps gives erases_deps of tConst", a 12-line case split.
- `erase_global_decls_deps_recursive_correct` — "the erased environment
  includes its dependencies", an 8-line wrapper over its `_gen` variant.
- `inversion_Const` — typing inversion for `tConst` (`invtac h`), giving the
  `declared_constant` that the erases_deps hypothesis needs.
- `fresh_globals_erase_global_decl_rec` — "the recursively erased environment
  is fresh", by induction over declarations plus
  `fresh_global_erase_global_decl_rec`. Discharges the shelved freshness
  obligation of the parent's final `Unshelve`.

The context excerpt `ExtractTransformCorrect` is the shared signature every
pass lemma discharges: a transform is correct when, if the source evaluates
`tConst kn` to `tConstruct ind c []`, the transformed environment does too.
Making each pass prove this one predicate is what lets the glue compose them
blindly.

## Why it is good

1. `extract_correct` is declared in
   `erasure/theories/Typed/ExtractionCorrectness.v`, lines 530-580 (`check`,
   `declared`).
2. No `admit`, `Admitted` or `Axiom` closes any goal in `extract_correct`'s
   proof, lines 530-580 (`check`, `no_sorry`).
3. `erases_correct` is cited by the parent site (`check`, `cites`); the other
   seven children are likewise each cited once by the glue (lines 550-578).
5. The same per-pass composition is codified as a reusable combinator:
   `compose_transforms_correct` proves that a list of `ExtractTransformCorrect`
   transforms composes to an `ExtractTransformCorrect` transform, generalising
   the one-lemma-per-pass pattern `extract_correct` uses by hand
   (`known-use`, `Transform.v` lines 35-44).
6. The main theorem composes 8 direct project lemmas in a 51-line parent site;
   the eight children (declaration and proof) span 1182, 22, 22, 37, 12, 8, 11
   and 19 lines (1313 in total); the deepest chain below the theorem is
   `extract_correct → erases_correct → inversion_App` and
   `extract_correct → dearg_transform_correct → dearg_correct`, depth 2
   (`measurement`).

## When to use it, and when not

Use it when the goal is the correctness of a whole pipeline that is a fixed
sequence of independently specifiable passes, each a function on a global
environment with a single shared correctness predicate (`ExtractTransformCorrect`
here), and each pass's statement closes on its own from the definitions plus
one per-pass lemma (`dearg_correct`, `remove_match_on_box_correct`). The parent
must be able to discharge each pass's side conditions (`wf_glob`,
`erases_deps`) with named supporting lemmas rather than re-proving them.

Avoid it when a pass's correctness depends on the output of the next pass (the
passes are not independent, so no self-contained per-pass statement exists), or
when the side conditions cannot be stated as their own lemmas and would have to
be re-proved inline at every call site. Note the passes may be very unequal: one
pass (erasure) carries the bulk of the work here, and the per-callee pattern
does not make that one pass any smaller.

## Consequences

The move produces one obligation per pass plus its side conditions. The three
pass lemmas differ hugely in size: `erases_correct` is 1182 lines (erasure
correctness is the hard part), while `dearg_transform_correct` and
`optimize_correct` are 22 lines each because they reduce to a single existing
lemma. The glue must discharge each pass's hypotheses in the exact shape the
pass lemma expects (`wf_glob` via `wf_erase_global_decls_recursive`,
`erases_deps` via `inversion_Const` + `global_erased_with_deps_erases_deps_tConst`
+ `erase_global_decls_deps_recursive_correct`); a wrong shape fails the
`eapply`. A failure mode: if the passes share state, their lemmas are not
self-contained and the composition needs an invariant threaded through all of
them instead of one independent lemma per pass.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml (MetaRocq CI) runs on push to the default branch 9.1; 'make ci-local'/'ci-opam' builds 'make all' which includes the 'erasure' target (erasure/theories/Typed/ExtractionCorrectness.v); pinned commit 51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56 is the head of default branch 9.1 | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: erases_correct@erasure/theories/Typed/ExtractionCorrectness.v:550, dearg_transform_correct@erasure/theories/Typed/ExtractionCorrectness.v:556, optimize_correct@erasure/theories/Typed/ExtractionCorrectness.v:558, wf_erase_global_decls_recursive@erasure/theories/Typed/ExtractionCorrectness.v:561, global_erased_with_deps_erases_deps_tConst@erasure/theories/Typed/ExtractionCorrectness.v:567, erase_global_decls_deps_recursive_correct@erasure/theories/Typed/ExtractionCorrectness.v:571, inversion_Const@erasure/theories/Typed/ExtractionCorrectness.v:565, fresh_globals_erase_global_decl_rec@erasure/theories/Typed/ExtractionCorrectness.v:578; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 9 file(s) byte-identical at 51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): erasure/theories/Typed/Extraction.v:170 (Axiom) | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(extract_correct, erasure/theories/Typed/ExtractionCorrectness.v, 530-580) -> declared: extract_correct is declared at erasure/theories/Typed/ExtractionCorrectness.v:530 | check_claims.py |
| 2 | verified | no_sorry(erasure/theories/Typed/ExtractionCorrectness.v, 530-580) -> no_sorry: none of admit, Admitted, Axiom, axiom in erasure/theories/Typed/ExtractionCorrectness.v:530-580 | check_claims.py |
| 3 | verified | cites(parent, erases_correct) -> cites: erases_correct occurs at erasure/theories/Typed/ExtractionCorrectness.v:550 | check_claims.py |
| 4 | verified | parent site ExtractionCorrectness.v 530-580 (51 lines) composes 7 lemmas in the glue (erases_correct@549, dearg_transform_correct@559, optimize_correct@561, wf_erase_global_decls_recursive@567/570, inversion_Const@573, global_erased_with_deps_erases_deps_tConst@575, erase_global_decls_deps_recursive_correct@578); child spans 1182/22/22/37/12/8/11 = 1294 (51-1232, 5179-5200, 506-527, 440-476, 66-77, 296-303, 211-221); depth chain: erases_correct applies inversion_App at ErasureCorrectness.v:64 and dearg_transform_correct applies dearg_correct at OptimizeCorrectness.v:5199 | verifier |
| 5 | verified | Transform.v:35-44 declares compose_transforms_correct: 'All ExtractTransformCorrect transforms -> ExtractTransformCorrect (compose_transforms transforms)', the reusable list-composition combinator generalising extract_correct's per-pass pattern | verifier |
| 6 | verified | Parent site ExtractionCorrectness.v 530-580 = 51 lines (grep: 'Theorem extract_correct' at 530, Qed at 580). 8 children cited in the glue (glue-cites-children pass: erases_correct@550, dearg_transform_correct@556, optimize_correct@558, wf_erase_global_decls_recursive@561, inversion_Const@565, global_erased_with_deps_erases_deps_tConst@567, erase_global_decls_deps_recursive_correct@571, fresh_globals_erase_global_decl_rec@578). Child spans read from code: erases_correct 51-1232 (1182), dearg_transform_correct 5179-5200 (22), optimize_correct 506-527 (22), wf_erase_global_decls_recursive 440-476 (37), global_erased_with_deps_erases_deps_tConst 66-77 (12), erase_global_decls_deps_recursive_correct 296-303 (8), inversion_Const 211-221 (11), fresh_globals_erase_global_decl_rec 66-84 (19); sum 1313. Depth chains: erases_correct applies inversion_App at ErasureCorrectness.v:64 ('eapply inversion_App in Hty'); dearg_transform_correct applies dearg_correct at OptimizeCorrectness.v:5199 ('apply dearg_correct; eauto'); depth 2. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Decomposition is faithful and closes, and the prior objection is fully met. Parent extract_correct (ExtractionCorrectness.v 530-580) ends in Qed at 580 and the glue eapplies all 8 children verbatim: erases_correct@550, dearg_transform_correct@556, optimize_correct@558, wf_erase_global_decls_recursive@561/563, inversion_Const@565, global_erased_with_deps_erases_deps_tConst@567, erase_global_decls_deps_recursive_correct@571, fresh_globals_erase_global_decl_rec@578 (Unshelve). The 8th child is now present: site erasure/theories/Typed/Extraction.v 66-84 (Lemma at 66, Qed at 84, 19 lines), its statement copied verbatim from the declaration, closed_by 'induction Σ0; ... fresh_global_erase_global_decl_rec (Qed.)' matching the code. Every child statement and closed_by matches the local code and ends in Qed (checked line ranges: erases_correct 51-1232, dearg_transform_correct 5179-5200, optimize_correct 506-527, wf_erase_global_decls_recursive 440-476, global_erased_with_deps_erases_deps_tConst 66-77, erase_global_decls_deps_recursive_correct 296-303, inversion_Const 211-221). Shape numbers are right: direct_lemmas=8 (8 children), glue_lines=51 (530-580), child_lines=[1182,22,22,37,12,8,11,19]=1313, depth=2 (erases_correct applies inversion_App at ErasureCorrectness.v:64; dearg_transform_correct applies dearg_correct at OptimizeCorrectness.v:5199). Claim 6, metrics (1313), README point 6 and the glue-cites-children check (now lists fresh_globals_erase_global_decl_rec@578) are all consistent at 8. Generic metatheory lemmas also applied in the glue (wellformed_closed_env, wf_ext_wf, lookup_global_In_wf, KernameSet.singleton_spec, wf_fresh_globals) are library plumbing, not per-pass or side-condition lemmas of this decomposition, so they are correctly not counted as children. | reviewer-correctness |
| generality | accept | Move is stated beyond the example: applicability.goal_shape/use_when abstract to 'a pipeline = fixed sequence of independently specifiable passes, each a function on a global environment with one shared correctness predicate (ExtractTransformCorrect)'; the known-use compose_transforms_correct (Transform.v:35-44, verified) codifies the pattern as a reusable combinator. avoid_when is specific (pass depends on next pass's output -> no self-contained per-pass statement; side conditions not statable as own lemmas) and consequences are honest (erases_correct 1182 lines vs 22-line dearg/optimize; exact-shape eapply; shared-state failure mode needing a threaded invariant). Good-leaf properties are stated: children are self-contained and each Qed.-closed so the glue never opens a pass's internals; dearg is a good leaf because proven against its own analysis not the erased term's shape; optimize because it needs only closedness/well-formedness; the shared ExtractTransformCorrect signature lets the glue compose them blindly. | reviewer-generality |
| provenance-licence | accept | Commit, licence and links are consistent and traceable. Pinned commit 51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56 is identical across source.json, SOURCE.md, entry.json and every permalink in README/entry.json (the README source row uses the unambiguous 12-char prefix 51b14e4bb5f4). Licence is MIT everywhere (entry.json source.licence, README licence row, source.json, SOURCE.md) and matches sources/metarocq/upstream-LICENSE, which is the MIT text copied from the pinned LICENSE per SOURCE.md. check_provenance.py returns pass: 9 files byte-identical at the pinned commit, matching the 9 files/sites listed and the code/ tree. Source note records repository, pinned commit, browse URL, detected licence, licence file, and attribution. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/MetaRocq/metarocq at commit `51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56`, under `MIT`; see the [source note](../../sources/metarocq/SOURCE.md) for the licence text and attribution.
