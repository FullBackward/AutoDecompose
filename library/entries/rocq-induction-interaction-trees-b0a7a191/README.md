# Induction on the Imp statement for compile_correct (Imp-to-Asm compiler)

| | |
|---|---|
| Kind | instance |
| Move | induction |
| Language | rocq |
| Status | accepted |
| Source | [interaction-trees](../../sources/interaction-trees/SOURCE.md) at `284d42248a3c` |
| Licence | `MIT` |
| Licence recorded | 2026-11-12T15:54:43Z |

## Intent

Prove the Imp-to-Asm compiler correct by induction on the Imp statement,
reducing the theorem to one case per constructor (Assign, Seq, If, While,
Skip), each case rewriting the target denotation with the matching linking or
correctness lemma proved earlier in the same file and closing on the induction
hypothesis.

## The decomposition

### parent `compile_correct`: [`tutorial/Imp2AsmCorrectness.v` lines 822-976](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/tutorial/Imp2AsmCorrectness.v#L822-L976) ([local copy](code/tutorial/Imp2AsmCorrectness.v))

```coq
  Theorem compile_correct {E} {HasExit : Exit -< E} (s : stmt) :
    equivalent (E := E) s (compile s).
  Proof.
    unfold equivalent.
    induction s.

    - (* Assign *)
      simpl.
      (* We push [denote_asm] inside of the combinators *)
      rewrite raw_asm_block_correct.
      rewrite denote_after.

      (* The head trees match by correctness of assign *)
      rewrite <- (bind_ret_r (ITree.bind (denote_expr e) _)).
      eapply bisimilar_bind'.
      { eapply compile_assign_correct; auto. }

      (* And remains to trivially relate the results *)

      intros []; simpl.
      repeat intro.
      force_left; force_right.
      Transparent eutt. red.
      rewrite <- eqit_Ret; auto.
      unfold state_invariant; auto.

    - (* Seq *)
      (* We commute [denote_asm] with [seq_asm] *)
      rewrite fold_to_itree'; simpl.
      rewrite seq_asm_correct. unfold to_itree'.

      (* And the result is immediate by indcution hypothesis *)
      eapply bisimilar_bind'.
      { eassumption. }
      intros [] ? _. rewrite (unique_f0 a').
      eassumption.

    - (* If *)
      (* We commute [denote_asm] with [if_asm] *)
      rewrite fold_to_itree'. simpl.
      rewrite if_asm_correct.
      unfold to_itree'.

      (* We now need to line up the evaluation of the test,
         and eliminate them by correctness of [compile_expr] *)
      repeat intro.
      rewrite interp_asm_bind.
      rewrite interp_imp_bind.
      eapply eutt_clo_bind.
      { apply compile_expr_correct; auto. }

      (* We get in return [sim_rel] related environments *)
      intros [g_imp' v] [g_asm' [l' x]] HSIM.

      (* We know that interpreting [GetVar tmp_if] is eutt to [Ret (g_asm,v)] *)
      generalize HSIM; intros EQ.  eapply sim_rel_get_tmp0 in EQ.
      unfold tmp_if.
      rewrite interp_asm_bind.
      rewrite EQ; clear EQ.
      rewrite bind_ret_; simpl.

      (* We can weaken [sim_rel] down to [Renv] *)
      apply sim_rel_Renv in HSIM.
      (* And finally conclude in both cases *)
      destruct v; simpl; auto.

    - (* While *)
      (* We commute [denote_asm] with [while_asm], and restructure the
         _Imp_ [loop] with [while_is_loop] *)
      simpl; rewrite fold_to_itree'.
      rewrite while_is_loop.
      rewrite while_asm_correct.
      Local Opaque denote_asm.

      unfold to_itree'.
      unfold loop. unfold iter at 2.
      unfold Iter_sub, Inr_sub, Inr_Kleisli, inr_, lift_ktree, cat, Cat_sub, cat, Cat_Kleisli.
      unfold from_bif, FromBifunctor_ktree_fin.
      cbn. rewrite 2 bind_ret_l. cbn.
      eapply (bisimilar_iter (fun x x' => (x = inl tt /\ x' = f0) \/ (x = inr tt /\ x' = fS f0))).
      2: {
        right. split. auto. apply unique_fin; reflexivity.
        }
      (* The two cases correspond to entering the loop, or exiting it*)
      intros ? ? [[] | []]; subst; cbn.

      (* The exiting case is trivial *)
      2:{ repeat intro.
          unfold to_bif, ToBifunctor_ktree_fin. rewrite !bind_ret_l. cbn.
          force_left. force_right.
          red; rewrite <- eqit_Ret; auto.
          unfold state_invariant. simpl.
          split; auto.
          setoid_rewrite split_fin_sum_L_L_f1.
          constructor. left. auto.
      }

      (* We now need to line up the evaluation of the test,
         and eliminate them by correctness of [compile_expr] *)
      repeat intro.
      rewrite !interp_imp_bind.
      rewrite !interp_asm_bind.
      rewrite !bind_bind.

      eapply eutt_clo_bind.
      { apply compile_expr_correct; auto. }

      intros [g_imp' v] [g_asm' [l' x]] HSIM.
      rewrite !interp_asm_bind.
      rewrite !bind_bind.

      (* We know that interpreting [GetVar tmp_if] is eutt to [Ret (g_asm,v)] *)
      generalize HSIM; intros EQ. eapply sim_rel_get_tmp0 in EQ.
      unfold tmp_if.

      rewrite EQ; clear EQ.
      rewrite bind_ret_; simpl.

      (* We can weaken [sim_rel] down to [Renv] *)
      apply sim_rel_Renv in HSIM.
      (* And now consider both cases *)
      destruct v; simpl; auto.
      + (* The false case is trivial *)
        force_left; force_right.
        red.
        rewrite <- eqit_Ret.
        unfold state_invariant. simpl.
        split; auto; constructor; auto.

      + (* In the true case, we line up the body of the loop to use the induction hypothesis *)
        rewrite !interp_asm_bind.
        rewrite !interp_imp_bind.
        rewrite !bind_bind.
        eapply eutt_clo_bind.
        { eapply IHs; auto. }
        intros [g_imp'' v''] [g_asm'' [l'' x']] [HSIM' ?].
        force_right; force_left.
        apply eqit_Ret.
        setoid_rewrite split_fin_sum_L_L_f1.
        constructor; auto.
        simpl. constructor; left; auto.

    - (* Skip *)

      simpl.
      unfold id_asm.
      pose proof (@pure_asm_correct).
      do 5 red in H. rewrite H.
      red. intros.
      setoid_rewrite interp_asm_ret.
      unfold interp_imp.
      rewrite interp_ret. unfold interp_map. rewrite interp_state_ret.
      apply eqit_Ret.
      unfold state_invariant. auto.
Qed.
```

### child `bisimilar_bind'`: [`tutorial/Imp2AsmCorrectness.v` lines 353-371](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/tutorial/Imp2AsmCorrectness.v#L353-L371) ([local copy](code/tutorial/Imp2AsmCorrectness.v))

```coq
  Lemma bisimilar_bind' {A A' B C E} (RAA' : A -> A' -> Prop) (RBC: B -> C -> Prop):
    forall (t1 : itree (ImpState +' E) A) (t2 : itree (Reg +' Memory +' E) A') ,
      bisimilar RAA' t1 t2 ->
      forall (k1 : A -> itree (ImpState +' E) B) (k2 : A' -> itree (Reg +' Memory +' E) C)
        (H: forall (a:A) (a':A'), RAA' a a' -> bisimilar RBC (k1 a) (k2 a')),
        bisimilar RBC (t1 >>= k1) (t2 >>= k2).
  Proof.
    repeat intro.
    rewrite interp_asm_bind.
    rewrite interp_imp_bind.
    eapply eutt_clo_bind.
    { eapply H; auto. }
    intros.
    destruct u1 as [? ?].
    destruct u2 as [? [? ?]].
    unfold state_invariant in H2.
    simpl in H2. destruct H2. subst.
    eapply H0; eauto.
  Qed.
```

### child `bisimilar_iter`: [`tutorial/Imp2AsmCorrectness.v` lines 373-402](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/tutorial/Imp2AsmCorrectness.v#L373-L402) ([local copy](code/tutorial/Imp2AsmCorrectness.v))

```coq
  Lemma bisimilar_iter {E A A' B B'}
        (R : A -> A' -> Prop)
        (S : B -> B' -> Prop)
        (t1 : A -> itree (_ +' E) (A + B))
        (t2 : A' -> itree (_ +' _ +' E) (A' + B')) :
    (forall l l', R l l' -> bisimilar (sum_rel R S) (t1 l) (t2 l')) ->
    forall x x', R x x' ->
    bisimilar S (iter (C := ktree _) t1 x) (iter (C := ktree _) t2 x').
  Proof.

    unfold bisimilar, interp_asm, interp_imp, interp_map.
    intros. rewrite 2 interp_iter.
    unfold iter, Iter_Kleisli.
    pose proof @interp_state_iter'.
    red in H2. unfold Basics.iter, MonadIter_itree.

    rewrite 2 H2.
    unfold Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_itree; cbn.
    rewrite H2.
    apply (eutt_iter' (state_invariant R)).
    intros.
    destruct H3; cbn.
    rewrite interp_state_bind, bind_bind.
    setoid_rewrite interp_state_ret.
    setoid_rewrite bind_ret_l. cbn.
    apply (@eutt_clo_bind _ _ _ _ _ _ (state_invariant (sum_rel R S))).
    - auto.
    - intros ? ? [? []]; cbn; apply eqit_Ret; constructor; split; auto.
    - constructor; auto.
  Qed.
```

### child `seq_asm_correct`: [`tutorial/Imp2AsmCorrectness.v` lines 454-462](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/tutorial/Imp2AsmCorrectness.v#L454-L462) ([local copy](code/tutorial/Imp2AsmCorrectness.v))

```coq
  Lemma seq_asm_correct {A B C} (ab : asm A B) (bc : asm B C) :
      denote_asm (seq_asm ab bc)
    ⩯ denote_asm ab >>> denote_asm bc.
  Proof.
    unfold seq_asm.
    rewrite loop_asm_correct, relabel_asm_correct, app_asm_correct.
    rewrite fmap_id0, cat_id_r, fmap_swap.
    apply cat_from_loop.
  Qed.
```

### child `if_asm_correct`: [`tutorial/Imp2AsmCorrectness.v` lines 466-520](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/tutorial/Imp2AsmCorrectness.v#L466-L520) ([local copy](code/tutorial/Imp2AsmCorrectness.v))

```coq
  Lemma if_asm_correct {A} (e : list instr) (tp fp : asm 1 A) :
      denote_asm (if_asm e tp fp)
    ⩯ ((fun _ =>
         denote_list e ;;
         v <- trigger (GetReg tmp_if) ;;
         if v : value then denote_asm fp f0 else denote_asm tp f0)).
  Proof.
    unfold if_asm.
    rewrite seq_asm_correct.
    unfold cond_asm.
    rewrite raw_asm_block_correct_lifted.
    rewrite relabel_asm_correct.

    intros ?.
    Local Opaque Asm.denote_asm.

    unfold CategoryOps.cat, Cat_sub, CategoryOps.cat, Cat_Kleisli; simpl.
    rewrite denote_after.
    cbn.
    repeat setoid_rewrite bind_bind.
    apply eqit_bind; try reflexivity. intros _.
    apply eqit_bind; try reflexivity. intros [].

    - rewrite !bind_ret_l.
      setoid_rewrite (app_asm_correct tp fp _).
      setoid_rewrite bind_bind.
      match goal with
      | [ |- _ (?t >>= _) _ ] => let y := eval compute in t in change t with y
      end.
      rewrite bind_ret_l. cbn.
      setoid_rewrite bind_ret_l.
      rewrite bind_bind.
      setoid_rewrite bind_ret_l.
      unfold from_bif, FromBifunctor_ktree_fin; cbn.
      rewrite bind_ret_r'.
      { rewrite (unique_f0 (fi' 0)). reflexivity. }
      { intros.
        Local Opaque split_fin_sum R. cbv. Local Transparent split_fin_sum R.
        rewrite split_fin_sum_R. reflexivity. }

    - rewrite !bind_ret_l.
      setoid_rewrite (app_asm_correct tp fp _).
      repeat setoid_rewrite bind_bind.
      match goal with
      | [ |- _ (?t >>= _) _ ] => let y := eval compute in t in change t with y
      end.
      rewrite bind_ret_l. cbn. rewrite bind_bind.
      setoid_rewrite bind_ret_l.
      unfold from_bif, FromBifunctor_ktree_fin.
      setoid_rewrite bind_ret_l.
      rewrite bind_ret_r'.
      { rewrite (unique_f0 (fi' 0)). reflexivity. }
      { intros. Local Opaque split_fin_sum L. cbv. Local Transparent split_fin_sum R.
        rewrite split_fin_sum_L. reflexivity. }
  Qed.
```

### child `while_asm_correct`: [`tutorial/Imp2AsmCorrectness.v` lines 526-579](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/tutorial/Imp2AsmCorrectness.v#L526-L579) ([local copy](code/tutorial/Imp2AsmCorrectness.v))

```coq
  Lemma while_asm_correct (e : list instr) (p : asm 1 1) :
      denote_asm (while_asm e p)
    ⩯ (loop (C := sub (ktree _) fin) (fun l : fin (1 + 1) =>
         match label_case l with
         | inl _ =>
           denote_list e ;;
           v <- trigger (GetReg tmp_if) ;;
           if (v:value) then Ret (fS f0) else (denote_asm p f0;; Ret f0)
         | inr _ => Ret f0
         end)).
  Proof.
    unfold while_asm.
    rewrite loop_asm_correct.
    apply Proper_loop.
    rewrite relabel_asm_correct.
    rewrite fmap_id0, cat_id_l.
    rewrite app_asm_correct.
    rewrite if_asm_correct.
    intros x.
    cbn.
    unfold to_bif, ToBifunctor_ktree_fin.
    rewrite bind_ret_l.
    destruct (label_case x); cbn.
    - rewrite !bind_bind. setoid_rewrite bind_ret_l.
      eapply eutt_clo_bind; try reflexivity. intros; subst.
      rewrite bind_bind.
      eapply eutt_clo_bind; try reflexivity. intros; subst.
      unfold from_bif, FromBifunctor_ktree_fin; cbn.
      setoid_rewrite bind_ret_l.
      destruct u0.
      + rewrite (pure_asm_correct _ _); cbn.
        rewrite !bind_ret_l.
        apply eqit_Ret.
        apply unique_fin; reflexivity.

      + rewrite (relabel_asm_correct _ _ _ _). cbn.
        rewrite bind_ret_l.
        setoid_rewrite bind_bind.
        eapply eutt_clo_bind; try reflexivity.
        intros ? ? [].
        repeat rewrite bind_ret_l.
        apply eqit_Ret.
        rewrite (unique_f0 u1).
        apply unique_fin; reflexivity.

    - cbn.
      rewrite (pure_asm_correct _ _).
      rewrite bind_bind. cbn.
      unfold from_bif, FromBifunctor_ktree_fin.
      rewrite !bind_ret_l.
      apply eqit_Ret.
      rewrite (unique_f0 f).
      apply unique_fin; reflexivity.
Qed.
```

### child `compile_expr_correct`: [`tutorial/Imp2AsmCorrectness.v` lines 597-713](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/tutorial/Imp2AsmCorrectness.v#L597-L713) ([local copy](code/tutorial/Imp2AsmCorrectness.v))

```coq
  Lemma compile_expr_correct : forall {E} e g_imp g_asm l n,
      Renv g_imp g_asm ->
      @eutt E _ _ (sim_rel l n)
            (interp_imp (denote_expr e) g_imp)
            (interp_asm (denote_list (compile_expr n e)) g_asm l).
  Proof.
    induction e; simpl; intros.
    - (* Var case *)
      (* We first compute and eliminate taus on both sides. *)
      force_left.
      rewrite tau_eutt.

      tau_steps.

      (* We are left with [Ret] constructs on both sides, that remains to be related *)
      red; rewrite <-eqit_Ret.
      unfold lookup_default, lookup, Map_alist.

      (* On the _Asm_ side, we bind to [gen_tmp n] a lookup to [varOf v] *)
      (* On the _Imp_ side, we return the value of a lookup to [varOf v] *)
      erewrite Renv_find; [| eassumption].
      apply sim_rel_add; assumption.

    - (* Literal case *)
      (* We reduce both sides to Ret constructs *)
      tau_steps.

      red; rewrite <-eqit_Ret.
      (* _Asm_ bind the litteral to [gen_tmp n] while _Imp_ returns it *)
      apply sim_rel_add; assumption.

    (* The three binary operator cases are identical *)
    - (* Plus case *)
      (* We push [interp_locals] into the denotations *)

      do 2 setoid_rewrite denote_list_app.
      rewrite interp_asm_bind.
      rewrite interp_imp_bind.

      (* The Induction hypothesis on [e1] relates the first itrees *)
      eapply eutt_clo_bind.
      { eapply IHe1; assumption. }
      (* We obtain new related environments *)
      intros [g_imp' v] [g_asm' [l' []]] HSIM.
      (* The Induction hypothesis on [e2] relates the second itrees *)
      rewrite interp_asm_bind.
      rewrite interp_imp_bind.
      eapply eutt_clo_bind.
      { eapply IHe2.
        eapply sim_rel_Renv; eassumption. }
      (* And we once again get new related environments *)
      intros [g_imp'' v'] [g_asm'' [l'' []]] HSIM'.
      (* We can now reduce down to Ret constructs that remains to be related *)
      tau_steps.
      red. rewrite <- eqit_Ret.

      clear -HSIM HSIM'. unfold lookup_default, lookup, Map_alist.
      erewrite sim_rel_find_tmp_n_trans; eauto.
      erewrite sim_rel_find_tmp_n; eauto.
      eapply sim_rel_binary_op; eauto.

    - (* Sub case *)
      (* We push [interp_locals] into the denotations *)
      do 2 setoid_rewrite denote_list_app.
      rewrite interp_asm_bind.
      rewrite interp_imp_bind.

      (* The Induction hypothesis on [e1] relates the first itrees *)
      eapply eutt_clo_bind.
      { eapply IHe1; assumption. }
      (* We obtain new related environments *)
      intros [g_imp' v] [g_asm' [l' []]] HSIM.
      (* The Induction hypothesis on [e2] relates the second itrees *)
      rewrite interp_asm_bind.
      rewrite interp_imp_bind.
      eapply eutt_clo_bind.
      { eapply IHe2.
        eapply sim_rel_Renv; eassumption. }
      (* And we once again get new related environments *)
      intros [g_imp'' v'] [g_asm'' [l'' []]]  HSIM'.
      (* We can now reduce down to Ret constructs that remains to be related *)
      tau_steps.
      red. rewrite <- eqit_Ret.

      clear -HSIM HSIM'. unfold lookup_default, lookup, Map_alist.
      erewrite sim_rel_find_tmp_n_trans; eauto.
      erewrite sim_rel_find_tmp_n; eauto.
      eapply sim_rel_binary_op; eauto.

    - (* Mul case *)
      (* We push [interp_locals] into the denotations *)
      do 2 setoid_rewrite denote_list_app.
      rewrite interp_asm_bind.
      rewrite interp_imp_bind.

      (* The Induction hypothesis on [e1] relates the first itrees *)
      eapply eutt_clo_bind.
      { eapply IHe1; assumption. }
      (* We obtain new related environments *)
      intros [g_imp' v] [g_asm' [l' []]] HSIM.
      (* The Induction hypothesis on [e2] relates the second itrees *)
      rewrite interp_asm_bind.
      rewrite interp_imp_bind.
      eapply eutt_clo_bind.
      { eapply IHe2.
        eapply sim_rel_Renv; eassumption. }
      (* And we once again get new related environments *)
      intros [g_imp'' v'] [g_asm'' [l'' []]] HSIM'.
      (* We can now reduce down to Ret constructs that remain to be related *)
      tau_steps.
      red. rewrite <- eqit_Ret.

      clear -HSIM HSIM'. unfold lookup_default, lookup, Map_alist.
      erewrite sim_rel_find_tmp_n_trans; eauto.
      erewrite sim_rel_find_tmp_n; eauto.
      eapply sim_rel_binary_op; eauto.
  Qed.
```

### child `compile_assign_correct`: [`tutorial/Imp2AsmCorrectness.v` lines 719-753](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/tutorial/Imp2AsmCorrectness.v#L719-L753) ([local copy](code/tutorial/Imp2AsmCorrectness.v))

```coq
  Lemma compile_assign_correct : forall {E} e x,
      bisimilar eq
        ((v <- denote_expr e ;; trigger (Imp.SetVar x v)) : itree (ImpState +' E) unit)
        ((denote_list (compile_assign x e)) : itree (Reg +' Memory +' E) unit).
  Proof.
    red; intros.
    unfold compile_assign.
    (* We push interpreters inside of the denotations *)
    rewrite denote_list_app.
    rewrite interp_asm_bind.
    rewrite interp_imp_bind.

    (* By correctness of the compilation of expressions,
       we can match the head trees.
     *)
    eapply eutt_clo_bind.
    { eapply compile_expr_correct; eauto. }

    (* Once again, we get related environments *)
    intros [g_imp' v]  [g_asm' [l' y]] HSIM.
    simpl in HSIM.

    (* We can now reduce to Ret constructs *)
    tau_steps.
    red. rewrite <- eqit_Ret.

    (* And remains to relate the results *)
    unfold state_invariant.
    unfold lookup_default, lookup, Map_alist.
    rewrite sim_rel_find_tmp_n; eauto; simpl.
    apply sim_rel_Renv in HSIM.
    split; auto.
    eapply Renv_write_local; eauto.
    eauto.
  Qed.
```

### child `while_is_loop`: [`tutorial/Imp2AsmCorrectness.v` lines 772-797](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/tutorial/Imp2AsmCorrectness.v#L772-L797) ([local copy](code/tutorial/Imp2AsmCorrectness.v))

```coq
  Lemma while_is_loop {E} (body : itree E (unit+unit)) :
    while body
          ≈ iter (C := ktree _) (fun l : unit + unit =>
                    match l with
                    | inl _ => x <- body;; match x with inl _ => Ret (inl (inl tt)) | inr _ => Ret (inr tt) end
                    | inr _ => Ret (inl (inl tt))   (* Enter loop *)
                    end) (inr tt).
  Proof.
    unfold while.
    rewrite! unfold_iter_ktree.
    rewrite bind_ret_l, tau_eutt.
    rewrite unfold_iter_ktree.
    rewrite !bind_bind.
    eapply eutt_clo_bind. reflexivity.
    intros. subst.
    destruct u2 as [[]|[]].
    2 : { force_right. reflexivity. }
    rewrite bind_ret_l, !tau_eutt.
    unfold iter, Iter_Kleisli.
    apply eutt_iter' with (RI := fun _ r => inl tt = r).
    - intros _ _ [].
      rewrite <- bind_ret_r at 1.
      eapply eutt_clo_bind; try reflexivity.
      intros [|[]] _ []; apply eqit_Ret; auto; constructor; auto.
    - constructor.
  Qed.
```

### child `raw_asm_block_correct`: [`tutorial/AsmCombinators.v` lines 296-300](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/tutorial/AsmCombinators.v#L296-L300) ([local copy](code/tutorial/AsmCombinators.v))

```coq
  Lemma raw_asm_block_correct {A} (b : block (fin A)) :
    denote_asm (raw_asm_block b) f0 ≈ denote_bk b.
  Proof.
    apply raw_asm_block_correct_lifted.
  Qed.
```

How the parts fit. The parent `compile_correct` is a single `induction s`, one
goal per constructor of `stmt`. The five cases use the eleven direct lemmas:

- **Assign** rewrites the block denotation with `raw_asm_block_correct` +
  `denote_after`, then `bisimilar_bind'` + `compile_assign_correct` match the
  head, and the tail closes trivially.
- **Seq** rewrites with `fold_to_itree'` + `seq_asm_correct`, then
  `bisimilar_bind'` carries the induction hypothesis `IHs`.
- **If** rewrites with `fold_to_itree'` + `if_asm_correct`, then
  `compile_expr_correct` lines up the test and the two branches close by
  `destruct v`.
- **While** rewrites the source loop with `while_is_loop` and the target with
  `while_asm_correct`, then `bisimilar_iter` discharges the coinductive loop;
  inside, `compile_expr_correct` lines up the test and `IHs` closes the body.
- **Skip** is closed by `pure_asm_correct` (the pure combinator is denoted as
  the pure function), a one-line reflexivity.

The lemma graph (A → B means "A's proof uses B", all in
`tutorial/Imp2AsmCorrectness.v` unless noted):

```
compile_correct
├── bisimilar_bind'      (Assign, Seq glue)
├── bisimilar_iter       (While glue)
├── raw_asm_block_correct (AsmCombinators.v) ── raw_asm_block_correct_lifted ── raw_asm_correct
├── compile_assign_correct ── compile_expr_correct ── sim_rel_binary_op ── sim_rel_Renv
├── compile_expr_correct
├── seq_asm_correct      ── loop_asm_correct, relabel_asm_correct, app_asm_correct
├── if_asm_correct       ── seq_asm_correct, raw_asm_block_correct_lifted, app_asm_correct
├── while_asm_correct    ── loop_asm_correct, if_asm_correct, pure_asm_correct
├── while_is_loop        ── unfold_iter_ktree, eutt_iter'
├── fold_to_itree'       (reflexivity)
└── pure_asm_correct     (AsmCombinators.v) ── raw_asm_correct
```

Each child is a good leaf because its statement is self-contained (it mentions
only its own denotation and the combinators it is about) and its proof closes
on its own or on named siblings: the linking lemmas `raw_asm_block_correct`,
`seq_asm_correct`, `if_asm_correct`, `while_asm_correct` are short equational
rewrites ending in a library lemma (`raw_asm_block_correct_lifted`,
`cat_from_loop`, `unique_f0`, `unique_fin`);
`compile_expr_correct` and `compile_assign_correct` close by their own
induction / `eutt_clo_bind` over the `sim_rel_*` facts;
`bisimilar_bind'`/`bisimilar_iter` close over the `itree` library's
`eutt_clo_bind`/`eutt_iter'`; and `fold_to_itree'`/`pure_asm_correct` are
`reflexivity`.

The two remaining direct lemmas are shown here rather than as excerpts:
[`fold_to_itree'` (tutorial/Imp2AsmCorrectness.v lines 800-801)](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/tutorial/Imp2AsmCorrectness.v#L800-L801),
a one-line `reflexivity`, and
[`pure_asm_correct` (tutorial/AsmCombinators.v lines 308-314)](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/tutorial/AsmCombinators.v#L308-L314),
`unfold pure_asm; rewrite raw_asm_correct; reflexivity`, which closes the Skip
case. Both files are copied under [`code/`](code/).

## Why it is good

2. The file header announces the decomposition and the proof follows it: "The
   proof is essentially structured as followed: … Linking is proved in
   isolation … Finally, all the pieces are tied together to prove the
   correctness." (`author-statement`, [lines 17-33](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/tutorial/Imp2AsmCorrectness.v#L17-L33)
   and [lines 818-820](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/tutorial/Imp2AsmCorrectness.v#L818-L820)).
4. The authors state the result is axiom-free — "For example, the compiler
   proof in `tutorial` doesn't need it [UIP] and is axiom-free."
   (`author-statement`, [README.md lines 58-60](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/README.md#L58-L60),
   with `Print Assumptions` in `tutorial/PrintAssumptions.v`).
5. The same move is used again in the repository's labelled variant,
   `compile_stmt_correct` proved by `induction s`
   (`known-use`, [secure_example/LabelledImp2AsmCorrectness.v lines 1105-1108](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/secure_example/LabelledImp2AsmCorrectness.v#L1105-L1108)).
6. The parent proof cites `raw_asm_block_correct` — it is applied directly as
   the Assign-case linking rewrite at line 831 (`check`,
   [line 831](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/tutorial/Imp2AsmCorrectness.v#L831)).
7. The shape is measurable: 11 direct lemmas, a 153-line glue body, child
   bodies of 13/22/6/49/44/112/31/19/3 lines, and a longest checked dependency
   chain of depth 4 — `compile_assign_correct → compile_expr_correct →
   sim_rel_binary_op → sim_rel_Renv` (`measurement`, permalinks in claim 7 of
   `entry.json`).

In my opinion the detail worth copying is the separation the header names:
control-flow correctness is pushed out of the induction into the linking
lemmas (`seq_asm_correct`, `if_asm_correct`, `while_asm_correct`), so the
induction itself only glues a matching lemma per constructor and never
re-reasons about control flow. The `While` case is the one that shows the
shape most clearly — it is two rewrites plus one coinductive step.

## When to use it, and when not

Use it when the language is defined by an inductive type and correctness is
naturally per-constructor; when each constructor's target denotation already
has a linking lemma that commutes the denotation with the combinator, and each
leaf has its own correctness lemma; and when a library-level bind/iter
bisimulation lemma can compose the cases. Avoid it when the per-constructor
linking lemmas are not yet proved (the induction then cannot close and the
linking is itself the real work, a separate subtree); when the target
semantics is not stated uniformly across constructors, so a shared induction
step does not fit; or when the language has a diverging constructor (a loop)
not covered by a coinductive `iter`/`eutt_iter'` lemma.

## Consequences

The induction produces one obligation per constructor (Assign, Seq, If,
While, Skip). Each obligation must first rewrite the target denotation with
its matching linking lemma (`raw_asm_block_correct`, `seq_asm_correct`,
`if_asm_correct`, `while_asm_correct`, `pure_asm_correct`) before the
induction hypothesis or a bisimulation step can be applied. The While case is
the hard obligation: it needs both a restructuring of the source loop
(`while_is_loop`) and a coinductive bisimulation step (`bisimilar_iter`); if
the loop body's denotation does not match the `iter` shape exactly, the
`bisimilar_iter` application fails. The three control-flow cases (Seq, If,
While) each depend on the trivial ktree unfolding `fold_to_itree'` (a
`reflexivity`) being applied at the right point before the linking rewrite.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | Pinned commit 284d42248a3c5517cff9f582e335fcee2f6bdc1f on default branch master; .github/workflows/docker-action.yml (on push to master) builds via coq-itree.opam (dune build -p coq-itree @install @runtest @doc), which includes tutorial/dune (coq.theory (name ITreeTutorial) (theories ITree)) covering tutorial/Imp2AsmCorrectness.v; .github/workflows/build-with-make.yml (on push to master) runs make all. | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| glue-cites-children | pass | cited: bisimilar_bind'@tutorial/Imp2AsmCorrectness.v:836, bisimilar_iter@tutorial/Imp2AsmCorrectness.v:901, seq_asm_correct@tutorial/Imp2AsmCorrectness.v:851, if_asm_correct@tutorial/Imp2AsmCorrectness.v:862, while_asm_correct@tutorial/Imp2AsmCorrectness.v:893, compile_expr_correct@tutorial/Imp2AsmCorrectness.v:871, compile_assign_correct@tutorial/Imp2AsmCorrectness.v:837, while_is_loop@tutorial/Imp2AsmCorrectness.v:890, raw_asm_block_correct@tutorial/Imp2AsmCorrectness.v:831, fold_to_itree'@tutorial/Imp2AsmCorrectness.v:850, pure_asm_correct@tutorial/Imp2AsmCorrectness.v:968; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at 284d42248a3c5517cff9f582e335fcee2f6bdc1f | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read the entry's byte-identical code copy of tutorial/Imp2AsmCorrectness.v. Parent body L824-L976 applies: bisimilar_bind' L836,L854; bisimilar_iter L901; seq_asm_correct L851; if_asm_correct L862; while_asm_correct L893; compile_expr_correct L871,L927; compile_assign_correct L837; while_is_loop L892; fold_to_itree' L850,L861,L891; pure_asm_correct L968 (pose proof @pure_asm_correct). Each of the ten is a closed Lemma/Theorem ending in Qed. (bisimilar_bind' L371; bisimilar_iter L402; seq_asm_correct L462; if_asm_correct L520; while_asm_correct L579; compile_expr_correct L713; compile_assign_correct L753; while_is_loop L797; fold_to_itree' L801; pure_asm_correct AsmCombinators.v L314); none is an axiom or admit. | verifier |
| 2 | verified | Header comment L17-L33 reads 'The proof is essentially structured as followed: ... Linking is proved in isolation ... Finally, all the pieces are tied together to prove the correctness.'; comment L818-L820 reads 'We are only left with reasoning about the functional correctness of the compiler, all control-flow related reasoning having been handled in isolation.' Both match the claim's quotations. | verifier |
| 3 | verified | Parent body L824-L976 is 153 lines. Child proof bodies (Proof..Qed): bisimilar_bind' L359-L371=13; bisimilar_iter L381-L402=22; seq_asm_correct L457-L462=6; if_asm_correct L472-L520=49; while_asm_correct L536-L579=44; compile_expr_correct L602-L713=112; compile_assign_correct L723-L753=31; while_is_loop L779-L797=19. Dependency chain edges all present: L735 compile_assign_correct applies compile_expr_correct; L656 compile_expr_correct applies sim_rel_binary_op; L281 sim_rel_binary_op applies sim_rel_Renv; L207-L210 sim_rel_Renv closes on its own (apply H). | verifier |
| 4 | verified | README.md L58-L60: 'For example, the compiler proof in tutorial doesn't need it and is axiom-free.' tutorial/PrintAssumptions.v L3: 'Print Assumptions Imp2AsmCorrectness.compile_correct.' Both fetched at the pinned commit and match the claim. | verifier |
| 5 | verified | secure_example/LabelledImp2AsmCorrectness.v (fetched at pinned commit): L1105 'Lemma compile_stmt_correct (s : stmt sensitivity_lat) :' and L1108 'induction s.' Match the claim's known-use. | verifier |
| 6 | verified | cites(parent, raw_asm_block_correct) -> cites: raw_asm_block_correct occurs at tutorial/Imp2AsmCorrectness.v:831 | check_claims.py |
| 7 | verified | Read the entry's byte-identical code. Parent glue body Imp2AsmCorrectness.v L824-L976 = 153 lines (Proof. at 824, Qed. at 976). It cites 11 distinct project lemmas: raw_asm_block_correct L831, bisimilar_bind' L836/L854, compile_assign_correct L837, fold_to_itree' L850/L861/L891, seq_asm_correct L851, if_asm_correct L862, compile_expr_correct L871/L927, while_is_loop L892, while_asm_correct L893, bisimilar_iter L901, pure_asm_correct L968. Child proof bodies (Proof..Qed) match: bisimilar_bind' L359-L371=13, bisimilar_iter L381-L402=22, seq_asm_correct L457-L462=6, if_asm_correct L472-L520=49, while_asm_correct L536-L579=44, compile_expr_correct L602-L713=112, compile_assign_correct L723-L753=31, while_is_loop L779-L797=19, raw_asm_block_correct AsmCombinators.v L298-L300=3. Dependency chain depth 4: compile_assign_correct applies compile_expr_correct at L735; compile_expr_correct applies sim_rel_binary_op at L656; sim_rel_binary_op applies sim_rel_Renv at L281; sim_rel_Renv closes on its own (L207-L210, Proof at 209, apply H). | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Prior objection fixed: raw_asm_block_correct is now the 11th child (site AsmCombinators.v#L296-L300), direct_lemmas=11 in shape and metrics, claim 6 records cites(parent, raw_asm_block_correct) at Imp2AsmCorrectness.v#L831. Re-verified whole lens against copied code: parent compile_correct is induction s (L826) with one case per constructor, closes at Qed L976, no admit/axiom in either copied file. The 11 direct lemmas applied in the glue are exactly the 11 children (raw_asm_block_correct L831, bisimilar_bind' L836/L854, compile_assign_correct L837, fold_to_itree' L850/L861/L891, seq_asm_correct L851, if_asm_correct L862, compile_expr_correct L871/L927, while_is_loop L892, while_asm_correct L893, bisimilar_iter L901, pure_asm_correct L968); no extra child, none missing, and all 11 child statements and closed_by fields match the code verbatim. Shape numbers right: glue_lines=155 = parent site 822-976 (declaration-included), child_lines=[19,30,9,55,54,117,35,26,5] = the 9 child sites (bisimilar_bind' 353-371=19, bisimilar_iter 373-402=30, seq_asm_correct 454-462=9, if_asm_correct 466-520=55, while_asm_correct 526-579=54, compile_expr_correct 597-713=117, compile_assign_correct 719-753=35, while_is_loop 772-797=26, raw_asm_block_correct 296-300=5); metrics proof-body counts 153 and [13,22,6,49,44,112,31,19,3] all match; depth-4 chain verified (compile_assign_correct L735 -> compile_expr_correct L656 -> sim_rel_binary_op L281 -> sim_rel_Renv L207-211). | reviewer-correctness |
| generality | accept | Move stated transferably: goal_shape is 'forall s : stmt, equivalent s (compile s)' over an inductive syntax type proved by induction s, and use_when/avoid_when name the enabling conditions (per-constructor linking lemmas raw_asm_block_correct/seq_asm_correct/if_asm_correct/while_asm_correct/pure_asm_correct, leaf correctness lemmas, a library bind/iter bisimulation lemma bisimilar_bind'/bisimilar_iter). When-not-to-use is honest and specific (unproved linking lemmas; non-uniform target semantics; diverging constructor without coinductive iter/eutt_iter'). Good-leaves question answered at README L612-622 (self-contained statements; linking lemmas close on library lemmas; compile_* close by own induction/eutt_clo_bind; bisimilar_* close on eutt_clo_bind/eutt_iter'; fold_to_itree'/pure_asm_correct are reflexivity). Prior objection's fix is correctly applied: both README Consequences (L684-686) and entry.json consequences (L280) now say 'the three control-flow cases (Seq, If, While) each depend on fold_to_itree''; verified against local copy that fold_to_itree' appears only at L850/861/891 (Assign uses raw_asm_block_correct L831, Skip uses pure_asm_correct L968). | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note all consistent and traceable. Commit 284d42248a3c5517cff9f582e335fcee2f6bdc1f matches across entry.json, sources/interaction-trees/source.json and SOURCE.md; check_provenance reports both copied files (Imp2AsmCorrectness.v, AsmCombinators.v) byte-identical at that commit. Licence MIT is recorded in entry.json, source.json, SOURCE.md and README.md and the copied upstream-LICENSE is the MIT License (Copyright 2018 DeepSpec). All site/full permalinks resolve to the correct paths and the line ranges in the permalinks match the named lemma/Theorem in the local copies (bisimilar_bind' 353, bisimilar_iter 373, seq_asm_correct 454, if_asm_correct 466, while_asm_correct 526, compile_expr_correct 597, compile_assign_correct 719, while_is_loop 772, fold_to_itree' 800, compile_correct 822, pure_asm_correct 308 in AsmCombinators.v). | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/DeepSpec/InteractionTrees at commit `284d42248a3c5517cff9f582e335fcee2f6bdc1f`, under `MIT`; see the [source note](../../sources/interaction-trees/SOURCE.md) for the licence text and attribution.
