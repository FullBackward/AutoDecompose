# Type soundness for labelled Imp by strengthening to statement-and-throw security

| | |
|---|---|
| Kind | instance |
| Move | suffices-or-strengthen |
| Language | rocq |
| Status | accepted |
| Source | [interaction-trees](../../sources/interaction-trees/SOURCE.md) at `284d42248a3c` |
| Licence | `MIT` |
| Licence recorded | 2026-11-14T10:26:58Z |

## Intent

Prove type soundness of the labelled Imp system (`well_typed_stmt s pc ->
secure_stmt s pc`) by strengthening the goal with `enough` to the conjunction
`secure_stmt s pc /\ secure_throw_stmt s pc`, then inducting on the typing
derivation. The strengthening is what makes the induction go through: each of
the eight constructors of `well_typed_stmt` is then closed by a per-constructor
lemma (for the normal `secure_stmt` conjunct) together with its primed twin (for
the throw `secure_throw_stmt` conjunct), both proved earlier in the same file.

## The decomposition

### parent `well_typed_stmt_sound`: [`secure_example/LabelledImpTypes.v` lines 1089-1113](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/secure_example/LabelledImpTypes.v#L1089-L1113) ([local copy](code/secure_example/LabelledImpTypes.v))

```coq
Lemma well_typed_stmt_sound s pc : well_typed_stmt s pc -> secure_stmt s pc.
Proof.
  intros Htype. enough (secure_stmt s pc /\ secure_throw_stmt s pc); try tauto.
  induction Htype; eauto.
  - (* Skip *) split; try apply well_typed_skip; try apply well_typed_skip'.
  - (* Seq *)
    split; try apply seq_well_typed_correct; try apply seq_well_typed_correct'; tauto.
  - (* Assign *)
    split; try eapply assign_well_typed_correct; try eapply assign_well_typed_correct';
      try apply well_typed_expr_correct; eauto.
  - (* Output *)
    split; try eapply output_well_typed_correct; try eapply output_well_typed_correct';
      try apply well_typed_expr_correct; eauto.
  - (* If *)
    apply well_typed_expr_correct in H.
    split; try eapply if_well_typed_correct; try eapply if_well_typed_correct'; eauto; try tauto.
  - (* While *)
    destruct IHHtype. apply well_typed_expr_correct in H.
    split; try eapply while_well_typed_correct; try eapply while_well_typed_correct'; eauto.
  - (* Raise *)
    split; try eapply well_typed_raise; try eapply well_typed_raise'; eauto.
  - (* TryCatch *)
    destruct IHHtype1. destruct IHHtype2.
    split; try eapply try_catch_throw_secure_stmt; try eapply try_catch_throw_secure_stmt'; eauto.
Qed.
```

### child `well_typed_skip`: [`secure_example/LabelledImpTypes.v` lines 901-910](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/secure_example/LabelledImpTypes.v#L901-L910) ([local copy](code/secure_example/LabelledImpTypes.v))

```coq
Lemma well_typed_skip pc : secure_stmt pc Skip.
Proof.
  intro observer. case_leq pc observer.
  - left; auto. unfold sem_stmt, interp_imp. do 2 red. intros.
    cbn. setoid_rewrite interp_state_ret. apply secure_eqit_ret; auto.
    split; auto.
  - right; auto. unfold sem_stmt, interp_imp. do 2 red. intros.
    cbn. setoid_rewrite interp_state_ret. apply secure_eqit_ret; auto.
    split; auto. cbv. auto.
Qed.
```

### child `seq_well_typed_correct`: [`secure_example/LabelledImpTypes.v` lines 569-596](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/secure_example/LabelledImpTypes.v#L569-L596) ([local copy](code/secure_example/LabelledImpTypes.v))

```coq
Lemma seq_well_typed_correct pc s1 s2 :
  secure_stmt pc s1 -> secure_stmt pc s2 ->
  secure_stmt pc (Seq s1 s2).
Proof.
  intros Hc1 Hc2. red. intros.
  specialize (Hc1 observer) as Hc1obs. specialize (Hc2 observer) as Hc2obs.
  inv Hc1obs.
  - do 2 red in H0. left; auto. unfold sem_stmt.
    cbn. unfold interp_imp. do 2 red. intros. setoid_rewrite interp_state_bind.
    eapply secure_eqit_bind; eauto. intros [? [] ] [? [] ] [? ?].
    clear H3. cbn in H2. cbn.
    inv Hc2obs; try apply H4; auto.
    do 2 red in H4.
    eapply eqit_secure_RR_imp with (RR1 := product_rel (labelled_equiv Γ observer) top2 ).
    { intros [ ? [] ] [? [] ] [? ?] . split; auto. }
    eapply state_secure_eutt_ret_aux; try apply H4; eauto.
    (* I think this ends up being fine*)
  - right; auto. unfold sem_stmt, interp_imp. cbn. do 2 red. intros.
    setoid_rewrite interp_state_bind.
    inv Hc2obs.
    { exfalso. apply H. auto. }
    match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
                      assert (t ≈ (ITree.bind (Ret (σ2, tt)) (fun st => Ret (fst st, tt) ))) end.
    rewrite bind_ret_l. reflexivity.
    eapply proper_eutt_secure_eutt; try apply H4; try reflexivity.
    eapply secure_eqit_bind; try eapply H0; auto.
    intros [? ?] [? ?] [? ?]. apply H3; auto.
Qed.
```

### child `assign_well_typed_correct`: [`secure_example/LabelledImpTypes.v` lines 297-341](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/secure_example/LabelledImpTypes.v#L297-L341) ([local copy](code/secure_example/LabelledImpTypes.v))

```coq
Lemma assign_well_typed_correct x e pc l : secure_expr l e -> leq (join l pc) (Γ x) -> secure_stmt pc (Assign x e).
Proof.
  intros Hle Hx.
  assert (Hpc : leq pc (Γ x) ).
  { eapply leq_trans_lat; eauto. apply leq_join_r; auto. }
  assert (Hl : leq l (Γ x) ).
  { eapply leq_trans_lat; try apply Hx; auto. apply leq_join_l; eauto. }
  assert (He : secure_expr (Γ x) e ).
  { eapply secure_expr_upward_close with (l2:= Γ x); eauto. }
  intros observer.
  specialize ( He observer). inv He.
  - left. eapply leq_trans_lat; eauto.
    do 2 red in H0. do 2 red. intros. unfold sem_stmt.
    cbn. unfold interp_imp. setoid_rewrite interp_state_bind.
    eapply secure_eqit_bind; eauto. intros [? ?] [? ?] [? ?].
    cbn in H2, H3. subst. eapply proper_eutt_secure_eutt; try apply interp_state_trigger.
    cbn. apply secure_eqit_ret; split; auto. cbn. cbn in *; subst; apply update_labelled_equiv_visible; auto.
  - case_leq pc observer.
    + left; auto.
      destruct H0 as [n Hn]. unfold sem_stmt.
      cbn. unfold interp_imp. do 2 red. intros. setoid_rewrite interp_state_bind.
      do 2 red in Hn.
      eapply secure_eqit_bind with (RR := product_rel (labelled_equiv Γ observer) top2 ); eauto.
      2 : { eapply state_secure_eutt_ret_aux; try apply Hn; auto. }
      intros [? ?] [? ?] [? ?]. cbn in H1. cbn.
      eapply proper_eutt_secure_eutt; try apply interp_state_trigger.
      cbn. apply secure_eqit_ret. split. 2 : cbv; auto. cbn.
      apply update_labelled_equiv_invisible; auto. symmetry.
      apply update_labelled_equiv_invisible;  auto.
      symmetry; auto.
    + right; auto.
      destruct H0 as [n Hn]. unfold sem_stmt. cbn.
      do 2 red in Hn. do 2 red. intros. unfold sem_stmt. cbn.
      setoid_rewrite interp_state_bind.
      match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
                      assert (t ≈ (ITree.bind (Ret (σ2, n)) (fun st => Ret (fst st, tt) ))) end.
      rewrite bind_ret_l. reflexivity.
      eapply proper_eutt_secure_eutt; try apply H1; try reflexivity.
      eapply secure_eqit_bind; try apply Hn; eauto.
      intros [? ?] [? ?] [? ?]. cbn in H3.
      eapply proper_eutt_secure_eutt; try apply interp_state_trigger; try reflexivity.
      cbn.
      apply secure_eqit_ret; split; auto.
      cbn. apply update_labelled_equiv_invisible; auto.
Qed.
```

### child `output_well_typed_correct`: [`secure_example/LabelledImpTypes.v` lines 457-503](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/secure_example/LabelledImpTypes.v#L457-L503) ([local copy](code/secure_example/LabelledImpTypes.v))

```coq
Lemma output_well_typed_correct l1 le pc e :
  secure_expr le e -> leq (join le pc) l1 ->
  secure_stmt pc (Output l1 e).
Proof.
  intros He0 Hle1.
  assert (Hle : leq le l1).
  { eapply leq_trans_lat; eauto. apply leq_join_l; auto. }
  assert (Hpc : leq pc l1).
  { eapply leq_trans_lat; try apply Hle1; auto. apply leq_join_r; eauto.  }
  assert (He : secure_expr l1 e ).
  { eapply secure_expr_upward_close with (l1 := le); eauto. }
  intros observer. specialize (He observer).
  inv He.
  - assert (Hobs : leq pc observer). eapply leq_trans_lat; eauto.
    left; auto.
    do 2 red in H0. do 2 red. intros. unfold sem_stmt. cbn.
    unfold interp_imp. setoid_rewrite interp_state_bind.
    eapply secure_eqit_bind; eauto. intros [? ?] [? ?] [? ?].
    cbn in H2, H3. subst. cbn. eapply proper_eutt_secure_eutt; try apply interp_state_trigger.
    cbn. setoid_rewrite bind_trigger. cbn.
    apply eqit_secure_public_Vis; try apply H.
    intros []. apply secure_eqit_ret; auto. split; auto.
  - case_leq pc observer.
    + left; auto. destruct H0 as [n Hn]. do 2 red in Hn. cbn in Hn.
      unfold sem_stmt. cbn. unfold interp_imp. do 2 red.
      intros. setoid_rewrite interp_state_bind.
      eapply secure_eqit_bind with (RR := product_rel (labelled_equiv Γ observer) top2 ); eauto.
      2 : { eapply state_secure_eutt_ret_aux; try apply Hn; auto. }
      intros [? ?] [? ?] [? ?]. cbn in H1. cbn.
      eapply proper_eutt_secure_eutt; try apply interp_state_trigger.
      cbn. setoid_rewrite bind_trigger. apply eqit_secure_private_VisLR; auto.
      constructor; apply tt. constructor; apply tt. intros [] [].
      apply secure_eqit_ret. split; auto.
    + right; auto. destruct H0 as [n Hn]. do 2 red in Hn.
      do 2 red. intros. unfold sem_stmt. cbn.
      unfold interp_imp. setoid_rewrite interp_state_bind.
      match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
                      assert (t ≈ (ITree.bind (Ret (σ2, n)) (fun st => Ret (fst st, tt) ))) end.
      rewrite bind_ret_l. reflexivity.
      eapply proper_eutt_secure_eutt; try apply H1; try reflexivity.
      eapply secure_eqit_bind; try apply Hn; eauto.
      intros [? ?] [? ?] [? ?]. cbn.
      eapply proper_eutt_secure_eutt; try apply interp_state_trigger; try reflexivity.
      cbn. setoid_rewrite bind_trigger. cbn.
      apply eqit_secure_private_VisL; auto. constructor; apply tt.
      intros []. apply secure_eqit_ret; auto. split; auto.
Qed.
```

### child `if_well_typed_correct`: [`secure_example/LabelledImpTypes.v` lines 623-665](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/secure_example/LabelledImpTypes.v#L623-L665) ([local copy](code/secure_example/LabelledImpTypes.v))

```coq
Lemma if_well_typed_correct pc le e s1 s2 :
  secure_expr le e -> secure_stmt (join pc le) s1 -> secure_stmt (join pc le) s2 ->
  secure_stmt pc (If e s1 s2).
Proof.
  intros He Hc1 Hc2. red. intros.
  specialize (Hc1 observer) as Hc1obs. specialize (Hc2 observer) as Hc2obs.
  specialize (He observer).
  inv Hc1obs; inv Hc2obs; try contradiction.
  - left. eapply leq_trans_lat; eauto. apply leq_join_l; auto.
    inv He. 2 : { exfalso. apply H3. eapply leq_trans_lat; eauto. apply leq_join_r; auto. }
    unfold sem_stmt, interp_imp.
    cbn. do 2 red. intros. setoid_rewrite interp_state_bind. eapply secure_eqit_bind; try apply H4; auto.
    intros [? ?] [? ?] [? ?]. cbn in H6, H7. subst. cbn. destruct v0; eauto.
  - case_leq pc observer.
    + left; auto. unfold sem_stmt, interp_imp. cbn. do 2 red. intros.
      setoid_rewrite interp_state_bind.
      inv He; try contradiction.
      * eapply secure_eqit_bind; try apply H5; eauto.
        intros [? ?] [? ?] [? ?]. cbn in H7, H6. cbn. subst. do 2 red in H0, H2.
        eapply eqit_secure_RR_imp with (RR1 := product_rel (labelled_equiv Γ observer) top2 ).
        { intros [? [] ] [? [] ] [? ?]. split; auto. }
        destruct v0; try eapply  state_secure_eutt_ret_aux; cbn in *; eauto.
      * destruct H5 as [n Hn]. do 2 red in Hn.
        eapply secure_eqit_bind; try eapply  state_secure_eutt_ret_aux; cbn in Hn; eauto.
        intros [? ?] [? ?] [? ?]. cbn. cbn in H6.
        eapply eqit_secure_RR_imp with (RR1 := product_rel (labelled_equiv Γ observer) top2 ).
        { intros [? [] ] [? [] ] [? ?]. split; auto. }
        destruct v; destruct v0;
        try eapply state_secure_eutt_ret_aux; try apply H0; try apply H2; eauto.
     + right; auto. do 2 red. intros. unfold sem_stmt, interp_imp. cbn.
       setoid_rewrite interp_state_bind.
       match goal with |- eqit_secure _ _ _ _ _ _ _ ?t =>
                      assert (t ≈ (ITree.bind (Ret (σ2, 0)) (fun st => Ret (fst st, tt) ))) end.
       rewrite bind_ret_l. reflexivity.
       eapply proper_eutt_secure_eutt; try apply H4; try reflexivity.
       inv He.
       * eapply secure_eqit_bind with (RR := product_rel (labelled_equiv Γ observer) top2) .
         2 : { apply expr_only_ret_aux1; auto. }
         intros [? ?] [? ?] [? ?]. cbn. destruct v; cbn in *; eauto.
       * destruct H6. eapply secure_eqit_bind; try apply expr_only_ret_aux1; auto.

         intros [? ?] [? ?] [? ?]. cbn. destruct v; cbn in *; eauto.
Qed.
```

### child `while_well_typed_correct`: [`secure_example/LabelledImpTypes.v` lines 724-750](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/secure_example/LabelledImpTypes.v#L724-L750) ([local copy](code/secure_example/LabelledImpTypes.v))

```coq
Lemma while_well_typed_correct e s :
  secure_expr bot e -> secure_stmt bot s ->
  secure_stmt bot (While e s).
Proof.
  intros He Hc. red. intros.
  assert (leq bot observer).
  { cbn. destruct LabelLattice.
    setoid_rewrite <- join_comm. rewrite <- join_unit. reflexivity. }
  specialize (He observer).
  specialize (Hc observer).
  inv He; inv Hc; try contradiction.
  left; auto. unfold sem_stmt, interp_imp. cbn. unfold while.
  specialize @interp_state_iter' as Hisi. red in Hisi. do 2 red. intros.
  setoid_rewrite Hisi. eapply secure_eqit_iter with (RA := product_rel (labelled_equiv Γ observer) eq).
  { split; auto. }
  intros [? [] ] [? [] ] [? ?]. cbn.
  setoid_rewrite interp_state_bind. setoid_rewrite bind_bind.
  eapply secure_eqit_bind; try apply H1; auto.
  intros [? ?] [? ?] [? ?]. cbn. cbn in H7, H8; subst. destruct v0.
  - setoid_rewrite interp_state_ret. setoid_rewrite bind_ret_l. cbn.
    apply secure_eqit_ret. constructor. split; auto.
  - setoid_rewrite interp_state_bind. setoid_rewrite bind_bind.
    eapply secure_eqit_bind; try apply H3; auto.
    intros [? [] ] [? [] ] [? ?]. cbn. cbn in H8.
    setoid_rewrite interp_state_ret. setoid_rewrite bind_ret_l. cbn.
    apply secure_eqit_ret. constructor. split; auto.
Qed.
```

### child `well_typed_raise`: [`secure_example/LabelledImpTypes.v` lines 796-808](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/secure_example/LabelledImpTypes.v#L796-L808) ([local copy](code/secure_example/LabelledImpTypes.v))

```coq
Lemma well_typed_raise : secure_stmt bot (Raise bot).
Proof.
  red. intros. left.
  destruct LabelLattice. cbn.
  setoid_rewrite <- join_comm. rewrite <- join_unit. reflexivity.
  red. red. intros. unfold sem_stmt, interp_imp.
  cbn. setoid_rewrite interp_state_bind. eapply secure_eqit_bind with (RR := eq).
  intros [ _ [] ].
  eapply proper_eutt_secure_eutt; try apply interp_state_trigger; try reflexivity.
  cbn. setoid_rewrite bind_trigger. apply eqit_secure_public_Vis.
  cbn. destruct LabelLattice.
  setoid_rewrite <- join_comm. rewrite <- join_unit. reflexivity. intros [].
Qed.
```

### child `try_catch_throw_secure_stmt`: [`secure_example/LabelledImpTypes.v` lines 845-861](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/secure_example/LabelledImpTypes.v#L845-L861) ([local copy](code/secure_example/LabelledImpTypes.v))

```coq
Lemma try_catch_throw_secure_stmt pc s catch :
  secure_stmt pc s -> secure_throw_stmt pc s -> secure_stmt pc catch ->
  secure_stmt pc (TryCatch s catch).
Proof.
  intros Hs Hthrows Hcatch. intros observer.
  specialize (Hs observer). specialize (Hthrows observer). specialize (Hcatch observer).
  inv Hs; inv Hthrows; inv Hcatch; try contradiction.
  - left; auto. unfold sem_stmt. cbn. eapply try_catch_public_exc; eauto.
  - right; auto. unfold sem_stmt. cbn. cbn in H2. unfold sem_throw_stmt in H2.
    do 2 red. intros. apply H0 in H5 as H6. cbn in H6. unfold interp_imp.
    eapply proper_eutt_secure_eutt; try setoid_rewrite try_catch_to_throw_prefix; try reflexivity.
    setoid_rewrite <- bind_ret_r at 6.
    setoid_rewrite interp_state_bind.
    eapply secure_eqit_bind; eauto.
    intros [σ3 [ [] | l] ] [σ4 []] [Hσ Hsum]; inv Hsum. cbn.
    setoid_rewrite interp_state_ret. apply secure_eqit_ret; split; cbv; auto.
Qed.
```

### The ninth direct lemma: `well_typed_expr_correct` (listed, not a site)

The finder named nine direct lemmas, one more than the eight child sites
allowed. The ninth, `well_typed_expr_correct`, is the shared expression lemma
the Assign, Output, If and While branches call before applying their
per-constructor lemma:

- [`secure_example/LabelledImpTypes.v` lines 1016-1087](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/secure_example/LabelledImpTypes.v#L1016-L1087) — `Lemma well_typed_expr_correct l e : well_typed_expr l e -> secure_expr l e.`, a 72-line induction over expressions that lifts the typing judgement to the security judgement.

It is the glue's only way to turn a `well_typed_expr` hypothesis into the
`secure_expr` hypothesis the assign/output/if/while lemmas take; the glue calls
it in four places (lines 1098, 1101, 1103, 1106).

### How the parts fit

The glue is 25 lines. Line 1091 does the strengthening:
`enough (secure_stmt s pc /\ secure_throw_stmt s pc); try tauto`, which replaces
the original goal with the conjunction and lets `tauto` close the leftover
"conjunction implies first projection" obligation. Line 1092 then
`induction Htype; eauto.`, producing one goal per constructor of
`well_typed_stmt`. Each remaining bullet is a `split` into the two conjuncts and
a pair of `try eapply`s, one per conjunct:

```text
well_typed_stmt_sound
└─ enough (secure_stmt s pc /\ secure_throw_stmt s pc)   [line 1091]
   └─ induction on the typing derivation Htype          [line 1092]
      ├─ Skip     → well_typed_skip            (+ well_typed_skip')
      ├─ Seq      → seq_well_typed_correct     (+ seq_well_typed_correct')
      ├─ Assign   → well_typed_expr_correct, then assign_well_typed_correct (+ assign_well_typed_correct')
      ├─ Output   → well_typed_expr_correct, then output_well_typed_correct (+ output_well_typed_correct')
      ├─ If       → well_typed_expr_correct, then if_well_typed_correct     (+ if_well_typed_correct')
      ├─ While    → well_typed_expr_correct, then while_well_typed_correct  (+ while_well_typed_correct')
      ├─ Raise    → well_typed_raise           (+ well_typed_raise')
      └─ TryCatch → try_catch_throw_secure_stmt (+ try_catch_throw_secure_stmt')
                     └─ try_catch_public_exc   (helper, lines 825-843)
```

The primed names (`well_typed_skip'`, `seq_well_typed_correct'`, …) are the
throw twins: they prove the same constructor for `secure_throw_stmt`, so each
`split` discharges its two conjuncts with the unprimed/primed pair. They are
cited by the glue but are not separate children here — the finder counted each
constructor as one lemma with its twin.

Why each shown child is a good leaf (a self-contained statement whose proof
closes on its own, or from a named sibling):

- `well_typed_skip` — no hypotheses; a two-way `case_leq pc observer`, each side
  a single `secure_eqit_ret`.
- `seq_well_typed_correct` — composed from its two hypotheses alone; the left
  branch is `secure_eqit_bind`, the right reuses the sibling
  `state_secure_eutt_ret_aux` (lines 253-264).
- `assign_well_typed_correct` — turns its two hypotheses into three internal
  facts (`Hpc`, `Hl`, `He`), then a case split, each branch a
  `secure_eqit_bind`/`secure_eqit_ret` pair.
- `output_well_typed_correct` — mirrors `assign_well_typed_correct` with a print
  event (`eqit_secure_public_Vis`/private variants) instead of a store update.
- `if_well_typed_correct` — a case split over the two branch hypotheses and the
  expression, each branch a `secure_eqit_bind` over the boolean.
- `while_well_typed_correct` — the one coinductive step: it reduces the `while`
  to `secure_eqit_iter` over the body's own security (via `interp_state_iter'`).
- `well_typed_raise` — no hypotheses; the raise is public at `bot` and closes by
  the public-Vis rule.
- `try_catch_throw_secure_stmt` — the left branch is a single `eapply` of the
  helper `try_catch_public_exc` (lines 825-843), which itself closes on its own.

The longest chain of project lemmas below the main theorem (`shape.depth`) is
four: `well_typed_stmt_sound → assign_well_typed_correct →
secure_expr_upward_close → expr_only_ret → expr_only_ret_aux1` (lines 297 →
162 → 157 → 125). The assign child calls `secure_expr_upward_close` (line 305),
which calls `expr_only_ret` (line 169), which calls `expr_only_ret_aux1` (line
159), a leaf proved by induction on the expression alone.

## Why it is good

1. The parent site `well_typed_stmt_sound` is 25 lines long — the whole
   soundness proof fits in one screen (`check`, [lines 1089-1113](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/secure_example/LabelledImpTypes.v#L1089-L1113)).
2. `well_typed_stmt_sound` is declared at `secure_example/LabelledImpTypes.v`
   1089-1113 (`check`, same permalink).
3. None of `admit`, `Admitted`, `Axiom` or `axiom` occurs in the parent site:
   every constructor branch closes (`check`, same permalink).
4. `try_catch_throw_secure_stmt` occurs in the parent site, so the glue cites
   its children rather than inlining them (`check`, same permalink).
5. The parent proof cites 9 named lemmas directly (the eight per-constructor
   lemmas plus `well_typed_expr_correct`), counted by reading lines 1091-1112
   (`measurement`).

In my opinion the detail worth copying is that the strengthening is chosen to
*match the inductive hypothesis*: `well_typed_stmt`'s While and TryCatch
constructors recurse through the throw form, so proving only `secure_stmt` by
induction would be stuck, while proving the conjunction is no harder per case
because a throw twin already exists for every constructor.

## When to use it, and when not

Use it when a soundness goal `well_typed P -> secure P` needs two paired
security forms proved in lockstep (normal and exceptional termination here),
and each constructor of the typing relation already has a per-constructor lemma
for each form. Strengthening to the conjunction lets one induction cover both
forms at once, and the extra conjunct costs nothing per case. Avoid it when one
of the forms is not actually needed by the inductive step (then the
strengthening over-proves), when the per-constructor lemmas have side conditions
the induction cannot supply, or when the strengthened goal cannot be discharged
back to the original with a cheap step like `try tauto`.

## Consequences

The move turns one soundness goal into eight constructor goals, each a pair
(normal and throw). Its obligations: every constructor needs both a
`secure_stmt` and a `secure_throw_stmt` lemma — the two never collapse — and the
strengthened conjunct must be recoverable from the original goal (`try tauto`).
The While and TryCatch cases `destruct` their induction hypotheses to reach the
throw form, which is exactly why the strengthening is needed. Failure mode:
strengthening to a conjunction that is not strong enough for the recursive
constructors leaves the induction stuck; strengthening too much (a form no
constructor needs) over-proves.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build-with-make.yml runs 'make all' on push to master (default branch); 'make all' -> 'make -C secure_example' -> builds every .v listed in secure_example/_CoqProject, including LabelledImpTypes.v | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: well_typed_skip@secure_example/LabelledImpTypes.v:1093, seq_well_typed_correct@secure_example/LabelledImpTypes.v:1095, assign_well_typed_correct@secure_example/LabelledImpTypes.v:1097, output_well_typed_correct@secure_example/LabelledImpTypes.v:1100, if_well_typed_correct@secure_example/LabelledImpTypes.v:1104, while_well_typed_correct@secure_example/LabelledImpTypes.v:1107, well_typed_raise@secure_example/LabelledImpTypes.v:1109, try_catch_throw_secure_stmt@secure_example/LabelledImpTypes.v:1112; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 284d42248a3c5517cff9f582e335fcee2f6bdc1f | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(well_typed_stmt_sound, 25) -> lines: site well_typed_stmt_sound has 25 lines | check_claims.py |
| 2 | verified | declared(well_typed_stmt_sound, secure_example/LabelledImpTypes.v, 1089-1113) -> declared: well_typed_stmt_sound is declared at secure_example/LabelledImpTypes.v:1089 | check_claims.py |
| 3 | verified | no_sorry(secure_example/LabelledImpTypes.v, 1089-1113) -> no_sorry: none of admit, Admitted, Axiom, axiom in secure_example/LabelledImpTypes.v:1089-1113 | check_claims.py |
| 4 | verified | cites(parent, try_catch_throw_secure_stmt) -> cites: try_catch_throw_secure_stmt occurs at secure_example/LabelledImpTypes.v:1112 | check_claims.py |
| 5 | verified | read code/secure_example/LabelledImpTypes.v lines 1091-1112: all 9 names occur (well_typed_skip L1093, seq_well_typed_correct L1095, assign_well_typed_correct L1097, output_well_typed_correct L1100, if_well_typed_correct L1104, while_well_typed_correct L1107, well_typed_raise L1109, try_catch_throw_secure_stmt L1112, well_typed_expr_correct L1098/1101/1103/1106); 8 constructor lemmas each cite a primed throw twin in the same lines | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent site (1089-1113, 25 lines) strengthens via 'enough (secure_stmt s pc and secure_throw_stmt s pc); try tauto' then 'induction Htype; eauto', closing each of the 8 constructors by a split + unprimed/primed eapply pair; Qed. at 1113. All 8 child statements and closed_by match the code verbatim (well_typed_skip 901, seq 569, assign 297, output 457, if 623, while 724, raise 796, try_catch 845); each closes by Qed. The 8 throw twins exist at cited lines 912,598,388,513,667,752,810,863. well_typed_expr_correct (1016) is the documented 9th direct lemma, not a child. Shape numbers correct: direct_lemmas=9, glue_lines=25, child_lines=[10,28,45,47,43,27,13,17] match site spans; depth=4 chain assign->secure_expr_upward_close (305/162) -> expr_only_ret (169/157) -> expr_only_ret_aux1 (159/125) verified. All 5 claims accurate; provenance pass. | reviewer-correctness |
| generality | accept | Move generalizes beyond the example: applicability.goal_shape and README 'When to use it' abstract to 'a soundness statement well_typed P -> secure P over an inductively defined typing relation whose target property has two paired forms proved in lockstep', with 'normal and exceptional termination here' marking the example as one instance. 'When not to use' is specific and honest (three conditions: unneeded form -> over-proving; side conditions induction cannot supply; strengthened goal not cheaply recoverable). Consequences name real obligations (both lemmas per constructor, recoverability via try tauto) and failure modes (too weak -> stuck, too strong -> over-prove), all consistent with the copied code where While/TryCatch destruct their IHs into the throw form. Good-leaf question answered explicitly: 'self-contained statement whose proof closes on its own, or from a named sibling', plus per-child good-leaf notes and shape numbers (child_lines, depth) for the bounded-prover framing. | reviewer-generality |
| provenance-licence | accept | Provenance pass: check_provenance.py reports 1 file byte-identical at 284d42248a3c5517cff9f582e335fcee2f6bdc1f. Commit recorded in entry.json source.commit and in every permalink (README + entry.json) matches the source note's pinned commit 284d42248a3c5517cff9f582e335fcee2f6bdc1f. Licence MIT is consistent across entry.json, README header, and SOURCE.md, and matches the copied upstream-LICENSE (MIT License, Copyright 2018 DeepSpec). Spot-checked cited line ranges against the local copy: parent 1089-1113 begins 'Lemma well_typed_stmt_sound', well_typed_skip at 901, seq_well_typed_correct at 569, well_typed_expr_correct at 1016, try_catch_public_exc at 825; all match their declarations. Source note, permalinks, commit and licence are consistent and fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/DeepSpec/InteractionTrees at commit `284d42248a3c5517cff9f582e335fcee2f6bdc1f`, under `MIT`; see the [source note](../../sources/interaction-trees/SOURCE.md) for the licence text and attribution.
