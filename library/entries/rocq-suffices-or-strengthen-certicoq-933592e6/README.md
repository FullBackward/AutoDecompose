# Strengthened well-formedness invariant glues the MetaRocq pipeline to LambdaANF

| | |
|---|---|
| Kind | instance |
| Move | suffices-or-strengthen |
| Language | rocq |
| Status | accepted |
| Source | [certicoq](../../sources/certicoq/SOURCE.md) at `943b52ae6547` |
| Licence | `MIT` |
| Licence recorded | 2026-11-14T10:24:47Z |

## Intent

CertiRocq's compiler theorem `metarocq_to_anf_correct` connects the MetaRocq
erasure pipeline to the LambdaANF backend. Its move is to *strengthen* the
statement with the well-formedness invariant `EProgram.wf_eprogram
(certirocq_flags env_flags) p` — no axioms, no primitive arrays — which is
exactly what the general pass theorem `convert_top_anf_correct` needs as its
Section context. The body then applies that one pass theorem and discharges
each of its hypotheses as a separate bullet, one named lemma per hypothesis.

## The decomposition

### parent `metarocq_to_anf_correct`: [`theories/Compiler/correctness.v` lines 140-188](https://github.com/CertiCoq/certicoq/blob/943b52ae654708130f241ccf8a50ecb95a7956e2/theories/Compiler/correctness.v#L140-L188) ([local copy](code/theories/Compiler/correctness.v))

```coq
  Theorem metarocq_to_anf_correct (econf : erasure_configuration) (p : EProgram.eprogram) : 
    (* The postcondition on MetaRocq's pipeline *)
    Transform.Transform.post (certirocq_post_metarocq_pipeline [] econf) p ->
    (* Stronger invariant: no axioms, no primitives *)
    EProgram.wf_eprogram (certirocq_flags env_flags) p ->
    let ie := inductive_env_east (fst p) in
    let tgm := (convert_env default_tag default_itag ie).2 in
    forall e_tgt comp_d', 
      anf_convert ie tgm (List.rev (fst p)) (snd p) = (compM.Ret e_tgt, comp_d') ->
      exists M, refines_toplevel (fst p) ie tgm M (snd p) e_tgt.
  Proof.
    intros hp wf' ie tgm e_tgt comp_d' cvt.
    cbn in hp. unfold certirocq_flags in wf'. cbn in wf'.
    unfold all_env_flags in hp. cbn in hp.
    match goal with
    | [ _ : EProgram.wf_eprogram ?fl p /\ _ |- _ ] => set (efl := fl) in *
    end.
    destruct hp as [wfp [vg]].
    have wf : wf_env_east ie.
    { apply wf_env_inductive, wfp. }
    eapply (convert_top_anf_correct func_tag kon_tag default_tag default_itag tgm (fst p) 
      (efl:=certirocq_flags env_flags)); trea.
    - (* The tag map is injective *) 
      now apply convert_env_inj.
    - (* All the original constructors are registered in the tag map *) 
      apply convert_env_reg.
    - (* The environment entries evaluate to values *)
      intros kn decl hl hb hbody.
      eapply lambda_glob_eval_env_fuel in hb; tea.
      destruct hb as [srcv [f [t [ev eq]]]]. now exists srcv, f, t. apply wfp.
    - (* The environment entries should evaluate to values with 0 fuel (they're lambdas) *)
      intros kn decl b srcv f t hd hbody hev.
      eapply lambda_glob_eval_env_fuel in hd; tea. 2:apply wfp.
      destruct hd as [srcv' [f' [t' [ev eqf]]]].
      eapply eval_val_exact_det in hev; tea. destruct hev as [eq [eq' eq'']].
      now subst f' srcv' t' f.
    - (* Wellformed declarations in the global environment *) 
      clear wfp wf. destruct wf' as [wfΣ wf].       
      intros kn decl body hdecl hb.
      eapply (lookup_env_wellformed (efl := certirocq_flags (switch_off_box env_flags))) in hdecl; tea.
      destruct decl; trivial. cbn in hdecl. cbn in hb.
      now subst cst_body.
    - apply wf'.
    - (* No prims *)
      intros s. cbn. reflexivity.
    - eapply (cenv_tgm_coh default_tag default_itag) in wf. unfold top_cenv.
      destruct convert_env as [[[[] ?] ?] ?]. apply wf.
    - apply wf'.
  Qed.
```

### child `convert_top_anf_correct`: [`theories/LambdaBox_to_LambdaANF/anf_toplevel.v` lines 581-609](https://github.com/CertiCoq/certicoq/blob/943b52ae654708130f241ccf8a50ecb95a7956e2/theories/LambdaBox_to_LambdaANF/anf_toplevel.v#L581-L609) ([local copy](code/theories/LambdaBox_to_LambdaANF/anf_toplevel.v))

```coq
  Theorem convert_top_anf_correct next_id e e_tgt comp_d' :
    wellformed Σ 0 e = true ->
    convert_top_anf func_tag default_tag prim_map default_itag next_id tgm prims
      (fun _ => None)
      ie (List.rev Σ) e = (compM.Ret e_tgt, comp_d') ->
    exists M, refines_top ie M e e_tgt.
  Proof.
    intros Hwf Hrun.
    edestruct (@convert_top_anf_corresp
                 func_tag default_tag default_itag
                 tgm Σ efl HnoAxioms
                 prim_map prims Hwf_glob
                 HnoVar HnoEvar HnoCoFix HnoLazy Hblocks HnoArray
                 no_prims Htgm
                 next_id ie e e_tgt comp_d' Hwf Hrun)
      as [cm [Sg' [S' [C_env [C [r [Hglob_cvt [Hmain_cvt ->]]]]]]]].
    eapply (@anf_correct_top_explicit
              func_tag kon_tag default_tag default_itag
              tgm cm (top_cenv ie) Σ efl
              HnoAxioms
              dcon_to_tag_inj Htgm             
              cenv_tgm_coh
              Hglob_term Hglob_fuel_zero Hglob_wf
              prim_map prims Hwf_glob
              HnoVar HnoEvar HnoCoFix HnoLazy Hblocks HnoArray
              no_prims
              e (fun x => (next_id <= x)%positive) Sg' S'
              C_env C r); eauto.
  Qed.
```

### child `convert_env_inj`: [`theories/LambdaBox_to_LambdaANF/anf_convert_env.v` lines 352-363](https://github.com/CertiCoq/certicoq/blob/943b52ae654708130f241ccf8a50ecb95a7956e2/theories/LambdaBox_to_LambdaANF/anf_convert_env.v#L352-L363) ([local copy](code/theories/LambdaBox_to_LambdaANF/anf_convert_env.v))

```coq
Lemma convert_env_inj default_tag default_itag ie : 
  wf_env_east ie ->
  let tgm := (convert_env default_tag default_itag ie).2 in
  inj_conIdMap tgm.
Proof.
  unfold convert_env. cbn.
  intros wf.
  have he := convert_env'_tgm ie _ _ eq_refl.
  apply he; cbn; auto. red. cbn => //.
  cbn. red. constructor. cbn.
  red. now cbn.
Qed.
```

### child `convert_env_reg`: [`theories/LambdaBox_to_LambdaANF/anf_convert_env.v` lines 515-536](https://github.com/CertiCoq/certicoq/blob/943b52ae654708130f241ccf8a50ecb95a7956e2/theories/LambdaBox_to_LambdaANF/anf_convert_env.v#L515-L536) ([local copy](code/theories/LambdaBox_to_LambdaANF/anf_convert_env.v))

```coq
Lemma convert_env_reg default_tag default_itag Σ : 
  let ie := inductive_env_east Σ in
  let tgm := (convert_env default_tag default_itag ie).2 in
  registered_constructors tgm Σ.
Proof.
  intros ie ice.
  eapply registered_constructors_inductive_env. subst ie.
  subst ice. generalize (inductive_env_east Σ).
  clear.
  intros i mind ind cstrs hl. apply dcon_to_tag_ok.
  unfold declared_constructor_ienv in hl.
  destruct lookup_env_east eqn:hl' => //.
  unfold declared_constructor_ityp in hl.
  destruct nth_error eqn:hn => //.
  destruct i1 as [na cnstrs]. apply Nat.ltb_lt in hl.
  eapply (in_convert_env _ _ _ mind i0); tea.
  clear -hl'; move: hl'.
  induction i in mind, i0 |- * => //.
  cbn. case: eqb_spec.
  + intros -> [= <-]. now left.
  + now move=> diff /IHi.
Qed.
```

### child `cenv_tgm_coh`: [`theories/LambdaBox_to_LambdaANF/anf_convert_env.v` lines 552-573](https://github.com/CertiCoq/certicoq/blob/943b52ae654708130f241ccf8a50ecb95a7956e2/theories/LambdaBox_to_LambdaANF/anf_convert_env.v#L552-L573) ([local copy](code/theories/LambdaBox_to_LambdaANF/anf_convert_env.v))

```coq
Lemma cenv_tgm_coh default_tag default_itag ie : 
  wf_env_east ie ->
  let tgm := convert_env default_tag default_itag ie in
  cenv_tgm_coherence tgm.1.1.1.2 tgm.2.
Proof.
  intros wf.
  have h := convert_env_coh default_tag default_itag ie wf.
  cbn. set (ce := convert_env _ _ _) in *.
  cbn in *.
  destruct ce as ((((? & ?) & ?) & ?) & tgm); cbn in *.
  destruct h as [hin htwo].
  intros ind n n' c_tag c_tag' ha hb.
  unfold dcon_to_tag in *.
  apply dcon_to_info_spec in ha, hb.
  destruct ha as [itag hin'].
  destruct hb as [itag' hin''].
  specialize (htwo _ _ _ _ _ _ _ hin' hin''). subst itag'.
  apply hin in hin' as [cinfo []].
  apply hin in hin'' as [cinfo' []].
  exists cinfo, cinfo'; split => //; split => //.
  congruence.
Qed.
```

### child `wf_env_inductive`: [`theories/LambdaBox_to_LambdaANF/anf_convert_env.v` lines 304-320](https://github.com/CertiCoq/certicoq/blob/943b52ae654708130f241ccf8a50ecb95a7956e2/theories/LambdaBox_to_LambdaANF/anf_convert_env.v#L304-L320) ([local copy](code/theories/LambdaBox_to_LambdaANF/anf_convert_env.v))

```coq
Lemma wf_env_inductive {efl : EEnvFlags} Σ :
  wf_glob Σ ->
  wf_env_east (inductive_env_east Σ).
Proof.
  induction 1.
  - econstructor; tea.
  - destruct d; cbn; tea.
    constructor; tea.
    clear -H1 IHwf_glob.
    induction H1.
    * constructor.
    * destruct x as [kn' []]; tea. 
      + cbn in *. now apply IHForall.
      + cbn in *. constructor; tea.
        apply IHForall.
        now depelim IHwf_glob.
Qed.
```

### child `lambda_glob_eval_env_fuel`: [`theories/Compiler/correctness.v` lines 100-114](https://github.com/CertiCoq/certicoq/blob/943b52ae654708130f241ccf8a50ecb95a7956e2/theories/Compiler/correctness.v#L100-L114) ([local copy](code/theories/Compiler/correctness.v))

```coq
Lemma lambda_glob_eval_env_fuel (p : EProgram.eprogram) (efl := env_flags) :
  wf_glob p.1 ->
  EWcbvEval.lambda_glob p.1 ->
  forall (k : kername) (decl : constant_body) (body : term),
  EGlobalEnv.declared_constant p.1 k decl ->
  cst_body decl = Some body -> exists (src_v : fuel_sem.value) (f t : nat), 
  eval_env_fuel (Hf:=LambdaBox_resource_fuel) p.1 [] body (Val src_v) f t /\ f = <0>.
Proof.
  destruct p as [Σ p]; cbn; clear p.
  intros hwf hv kn decl body hd hb.
  have hwfd := wf.wf_glob_globals_wf _ hwf _ _ _ hd hb.
  eapply (lambda_glob_declared _ hwf hv) in hd; tea.
  destruct decl as [[|]]=> //. noconf hb. cbn in hd.
  destruct hd as [na [b ->]]. do 3 eexists. split. constructor. constructor. now cbn.
Qed.
```

### child `eval_val_exact_det`: [`theories/LambdaBox_to_LambdaANF/fuel_sem.v` lines 448-645](https://github.com/CertiCoq/certicoq/blob/943b52ae654708130f241ccf8a50ecb95a7956e2/theories/LambdaBox_to_LambdaANF/fuel_sem.v#L448-L645) ([local copy](code/theories/LambdaBox_to_LambdaANF/fuel_sem.v))

```coq
  Lemma eval_val_exact_det rho e v1 v2 f1 t1 f2 t2 :
    eval_env_fuel rho e (Val v1) f1 t1 ->
    eval_env_fuel rho e (Val v2) f2 t2 ->
    v1 = v2 /\ f1 = f2 /\ t1 = t2.
  Proof.
    intros Heval1. revert v2 f2 t2.
    set (Pstep := fun (rho : env) (e : EAst.term) (r : result) (f : nat) (t : trace) =>
      match r with
      | Val v1 => forall v2 f2 t2,
          eval_env_step rho e (Val v2) f2 t2 ->
          v1 = v2 /\ f = f2 /\ t = t2
      | OOT => True
      end).
    set (Pmany := fun (rho : env) (es : list EAst.term) (vs : list value)
                      (fs : nat) (ts : trace) =>
      forall vs2 fs2 ts2,
        eval_fuel_many rho es vs2 fs2 ts2 ->
        vs = vs2 /\ fs = fs2 /\ ts = ts2).
    set (Pfuel := fun (rho : env) (e : EAst.term) (r : result) (f : nat) (t : trace) =>
      match r with
      | Val v1 => forall v2 f2 t2,
          eval_env_fuel rho e (Val v2) f2 t2 ->
          v1 = v2 /\ f = f2 /\ t = t2
      | OOT => True
      end).
    enough (Haux : Pfuel rho e (Val v1) f1 t1) by exact Haux.
    apply (eval_env_fuel_ind' Pstep Pmany Pfuel); try exact Heval1;
      unfold Pstep, Pmany, Pfuel; try solve [intros; exact I].
    - intros n rho0 v Hnth v2 f2 t2 Heval2.
      remember (EAst.tRel n) as ea in Heval2.
      remember (Val v2) as rv in Heval2.
      destruct Heval2; try discriminate;
        try match goal with
            | [ Hrv : Val _ = Val _ |- _ ] => injection Hrv as <-; subst
            end.
      injection Heqea as <-. subst.
      split; [congruence | split; reflexivity].
    - intros body rho0 na v2 f2 t2 Heval2.
      remember (EAst.tLambda na body) as ea in Heval2.
      remember (Val v2) as rv in Heval2.
      destruct Heval2; try discriminate;
        try match goal with
            | [ Hrv : Val _ = Val _ |- _ ] => injection Hrv as <-; subst
            end.
      injection Heqea as <- <-. subst.
      split; [reflexivity | split; reflexivity].
    - intros mfix idx rho0 v2 f2 t2 Heval2.
      remember (EAst.tFix mfix idx) as ea in Heval2.
      remember (Val v2) as rv in Heval2.
      destruct Heval2; try discriminate;
        try match goal with
            | [ Hrv : Val _ = Val _ |- _ ] => injection Hrv as <-; subst
            end.
      injection Heqea as <- <-. subst.
      split; [reflexivity | split; reflexivity].    
    - intros e1 e2 body v2' r na rho0 rho' f0 f2 t0 t2 f3 t3
             _ IH1 _ IH2 _ IH3.
      destruct r as [v_r |]; [| exact I].
      intros v_target f_t t_t Heval2.
      remember (EAst.tApp e1 e2) as ea in Heval2.
      remember (Val v_target) as rv in Heval2.
      destruct Heval2; try discriminate;
        try match goal with
            | [ Hrv : Val _ = Val _ |- _ ] => injection Hrv as <-; subst
            end.
      + injection Heqea as <- <-. subst.
        specialize (IH1 _ _ _ H). destruct IH1 as [Heq1 [-> ->]].
        injection Heq1 as <- <- <-.
        specialize (IH2 _ _ _ H0). destruct IH2 as [Heq2 [-> ->]].
        subst. specialize (IH3 _ _ _ H1). destruct IH3 as [-> [-> ->]].
        split; [reflexivity | split; reflexivity].
      + injection Heqea as <- <-. subst.
        specialize (IH1 _ _ _ H). destruct IH1 as [Heq1 _].
        discriminate.
    - intros e1 e2 body rho0 rho' rho'' idx na mfix v2' r
             f0 f2 t0 t2 f3 t3 _ IH1 Hfb Hmre _ IH2 _ IH3.
      destruct r as [v_r |]; [| exact I].
      intros v_target f_t t_t Heval2.
      remember (EAst.tApp e1 e2) as ea in Heval2.
      remember (Val v_target) as rv in Heval2.
      destruct Heval2; try discriminate;
        try match goal with
            | [ Hrv : Val _ = Val _ |- _ ] => injection Hrv as <-; subst
            end.
      + injection Heqea as <- <-. subst.
        specialize (IH1 _ _ _ H). destruct IH1 as [Heq1 _].
        discriminate.
      + injection Heqea as <- <-. subst.
        lazymatch goal with
        | [ He1_2 : eval_env_fuel _ _ (Val (ClosFix_v ?rho2 ?mfix2 ?idx2)) _ _,
            Hfb2 : fix_body ?mfix3 ?idx3 = Some (EAst.tLambda ?na2 ?body2),
            He2_2 : eval_env_fuel _ _ (Val ?v2_2) _ _,
            Hbody2 : eval_env_fuel _ ?body2 (Val ?v_target2) _ _ |- _ ] =>
          specialize (IH1 _ _ _ He1_2); destruct IH1 as [Heq1 [-> ->]];
          injection Heq1 as <- <- <-;
          rewrite Hfb in Hfb2; injection Hfb2 as <- <-;
          specialize (IH2 _ _ _ He2_2); destruct IH2 as [-> [-> ->]];
          specialize (IH3 _ _ _ Hbody2); destruct IH3 as [-> [-> ->]];
          split; [reflexivity | split; reflexivity]
        end.
    - intros na b t0 v1' r rho0 f0 t2 f2 t3 _ IH1 _ IH2.
      destruct r as [v_r |]; [| exact I].
      intros v_target f_t t_t Heval2.
      remember (EAst.tLetIn na b t0) as ea in Heval2.
      remember (Val v_target) as rv in Heval2.
      destruct Heval2; try discriminate;
        try match goal with
            | [ Hrv : Val _ = Val _ |- _ ] => injection Hrv as <-; subst
            end.
      injection Heqea as <- <- <-. subst.
      specialize (IH1 _ _ _ H). destruct IH1 as [Heq1 [-> ->]].
      subst. specialize (IH2 _ _ _ H0). destruct IH2 as [-> [-> ->]].
      split; [reflexivity | split; reflexivity].
    - intros ind c args vs rho0 dc fs ts Hdc _ IHmany.
      intros v_target f_t t_t Heval2.
      remember (EAst.tConstruct ind c args) as ea in Heval2.
      remember (Val v_target) as rv in Heval2.
      destruct Heval2; try discriminate. subst.
      injection Heqea as <- <- <-. injection Heqrv as <-.
      specialize (IHmany _ _ _ H0). destruct IHmany as [-> [-> ->]].
      split; [congruence | split; reflexivity].
    - intros ind npars mch brs rho0 dc vs body c r f0 f2 t0 t2
             _ IH1 Hdc Hfind _ IH2.
      destruct r as [v_r |]; [| exact I].
      intros v_target f_t t_t Heval2.
      remember (EAst.tCase (ind, npars) mch brs) as ea in Heval2.
      remember (Val v_target) as rv in Heval2.
      destruct Heval2; try discriminate;
        try match goal with
            | [ Hrv : Val _ = Val _ |- _ ] => injection Hrv as <-; subst
            end.
      assert (ind0 = ind) by congruence.
      assert (mch0 = mch) by congruence.
      assert (brs0 = brs) by congruence.
      subst. clear Heqea.
      specialize (IH1 _ _ _ H). destruct IH1 as [Heq1 [-> ->]].
      assert (vs0 = vs) by congruence. subst vs0.
      assert (c0 = c).
      { assert (Hde : dcon_of_con ind c = dcon_of_con ind c0) by congruence.
        unfold dcon_of_con in Hde. injection Hde as HN.
        now apply Nnat.Nat2N.inj. }
      subst c0. rewrite Hfind in H1. injection H1 as <-.
      specialize (IH2 _ _ _ H2). destruct IH2 as [-> [-> ->]].
      split; [reflexivity | split; reflexivity].
    - intros p c rho0 vs v f0 t0 _ IH Hnth.
      intros v_target f_t t_t Heval2.
      remember (EAst.tProj p c) as ea in Heval2.
      remember (Val v_target) as rv in Heval2.
      destruct Heval2; try discriminate;
        try match goal with
            | [ Hrv : Val _ = Val _ |- _ ] => injection Hrv as <-; subst
            end.
      injection Heqea as <- <-. subst.
      specialize (IH _ _ _ H). destruct IH as [Heq1 [-> ->]].
      injection Heq1 as <-.
      rewrite Hnth in H0. injection H0 as <-.
      split; [reflexivity | split; reflexivity].
    - intros k body v decl rho0 f0 t0 Hdecl Hbody _ IH.
      intros v_target f_t t_t Heval2.
      remember (EAst.tConst k) as ea in Heval2.
      remember (Val v_target) as rv in Heval2.
      destruct Heval2; try discriminate;
        try match goal with
            | [ Hrv : Val _ = Val _ |- _ ] => injection Hrv as <-; subst
            end.
      injection Heqea as <-. subst.
      assert (decl = decl0) by (unfold declared_constant in *; congruence).
      subst decl0. rewrite Hbody in H0. injection H0 as <-.
      specialize (IH _ _ _ H1). destruct IH as [-> [-> ->]].
      split; [reflexivity | split; reflexivity].
    - intros rho0 p v Htrans v_target f_t t_t Heval2.
      remember (EAst.tPrim p) as ea in Heval2.
      remember (Val v_target) as rv in Heval2.
      destruct Heval2; try discriminate;
        try match goal with
            | [ Hrv : Val _ = Val _ |- _ ] => injection Hrv as <-; subst
            end.
      injection Heqea as <-. subst. split; [congruence | split; reflexivity].
    - intros rho0 vs2 fs2 ts2 Hmany2.
      remember (@nil EAst.term) as es in Hmany2.
      destruct Hmany2; [split; [reflexivity | split; reflexivity] | discriminate].
    - intros rho0 e0 es v vs f0 fs t0 ts _ IH_e _ IH_es.
      intros vs2 fs2 ts2 Hmany2.
      remember (e0 :: es) as ees in Hmany2.
      destruct Hmany2; [discriminate |].
      injection Heqees as <- <-.
      specialize (IH_e _ _ _ H). destruct IH_e as [-> [-> ->]].
      specialize (IH_es _ _ _ Hmany2). destruct IH_es as [-> [-> ->]].
      split; [reflexivity | split; reflexivity].
    - intros rho0 e0 r f0 t0 _ IH.
      destruct r as [v_r |]; [| exact I].
      intros v2 f2 t2 Heval2.
      remember e0 as ea in Heval2.
      remember (Val v2) as rv in Heval2.
      destruct Heval2; try discriminate. subst.
      specialize (IH _ _ _ H). destruct IH as [-> [-> ->]].
      split; [reflexivity | split; reflexivity].
  Qed.
```

How the parts fit. The glue does two things, then discharges the pass
theorem's hypotheses one bullet each.

1. It turns the MetaRocq postcondition into the facts the pass theorem needs.
   `destruct hp as [wfp [vg]]` (line 157) keeps the `wf_glob` half `wfp` and the
   value guard `vg`; `have wf : wf_env_east ie` is closed by `wf_env_inductive`
   (line 159), lifting `wf_glob` to the ANF-side environment.
2. It applies the single general pass theorem `convert_top_anf_correct`
   (line 160), whose Section contexts are exactly the parts of the strengthened
   invariant, and then discharges them, one `-` bullet each:

| bullet (correctness.v) | goal of `convert_top_anf_correct` | closed by |
|---|---|---|
| 162-163 | tag map injective (`dcon_to_tag_inj`) | `convert_env_inj` |
| 164-165 | constructors registered (`Htgm`) | `convert_env_reg` |
| 166-169 | globals evaluate to values (`Hglob_term`) | `lambda_glob_eval_env_fuel` |
| 170-175 | globals evaluate in 0 fuel (`Hglob_fuel_zero`) | `lambda_glob_eval_env_fuel`, `eval_val_exact_det` |
| 176-181 | globals well-formed (`Hglob_wf`) | `lookup_env_wellformed` (MetaRocq) |
| 182 | a flag of the strengthened invariant | `apply wf'` |
| 183-184 | no primitives (`no_prims`) | `reflexivity` |
| 185-186 | cenv/tgm coherence (`cenv_tgm_coh`) | `cenv_tgm_coh` |
| 187 | a flag of the strengthened invariant | `apply wf'` |

Each named lemma is a good leaf: a self-contained statement whose proof closes
on its own or from a named sibling.

- `wf_env_inductive` closes by induction on `wf_glob` alone.
- `convert_env_inj` delegates to `convert_env'_tgm`, the same helper that also
  closes the sibling `convert_env_coh`.
- `convert_env_reg` closes through `registered_constructors_inductive_env` and
  `in_convert_env`.
- `cenv_tgm_coh` reuses the sibling `convert_env_coh` and `dcon_to_info_spec`.
- `lambda_glob_eval_env_fuel` closes through `lambda_glob_declared`
  (correctness.v 86), which itself closes through `lambda_glob_lookup`
  (correctness.v 72) — the longest checked chain of project lemmas below the
  parent (depth 3).
- `eval_val_exact_det` is a determinism lemma closed by a mutual-style induction
  over `eval_env_fuel` (`eval_env_fuel_ind'`), one case per term constructor,
  all ending in `reflexivity`.
- `lookup_env_wellformed` is the one leaf declared outside the copied files, in
  the MetaRocq dependency (`From MetaRocq.Erasure Require Import EWellformed`,
  correctness.v line 20).

The sibling `metarocq_to_anf_total` (correctness.v 190-215) reuses the same
strengthened hypothesis: it applies `convert_top_anf_total` to obtain the
target, then calls `metarocq_to_anf_correct` for the refinement.

## Why it is good

1. The parent site is 49 lines long, declaration through `Qed` (correctness.v
   140-188). *(check; `lines(metarocq_to_anf_correct, 49)`)*
2. The general pass theorem `convert_top_anf_correct` is declared at
   `theories/LambdaBox_to_LambdaANF/anf_toplevel.v` 581-609. *(check;
   `declared(...)`)*
3. None of `admit`, `Admitted`, `Axiom` or `axiom` occurs in the parent site
   correctness.v 140-188. *(check; `no_sorry(...)`)*
4. The authors state the strengthening in a comment: "To prove the correctness
   of connecting the MetaRocq pipeline and CertiRocq's ANF, we need a stronger
   well-formedness property" (correctness.v 123-128). *(author-statement)*
5. The parent's body cites 8 named lemmas directly (`wf_env_inductive`,
   `convert_top_anf_correct`, `convert_env_inj`, `convert_env_reg`,
   `lambda_glob_eval_env_fuel`, `eval_val_exact_det`, `lookup_env_wellformed`,
   `cenv_tgm_coh`), counted by reading correctness.v 150-188. *(measurement)*

In my opinion the detail worth copying is that the strengthened invariant
(`certirocq_flags`) is *stated once* as a hypothesis of the parent and then
consumed uniformly: every part of it is one Section context of the general pass
theorem, so the glue is a single `eapply` followed by one bullet per context,
each bullet a named lemma rather than an ad-hoc sub-proof.

## When to use it, and when not

Use it when a general pass theorem already exists (`convert_top_anf_correct`)
but needs stronger hypotheses than the pipeline's own postcondition provides.
Strengthen the parent's statement with exactly the invariant that makes those
hypotheses dischargeable (here `certirocq_flags`: no axioms, no primitive
arrays, constructors as blocks), then discharge each with a named lemma.

Avoid it when the strengthened invariant does not decompose into the pass
theorem's individual hypotheses — then the one-lemma-per-bullet structure
breaks and the glue grows ad-hoc sub-proofs; when the pass theorem's hypotheses
need genuinely new proofs rather than existing `convert_env_*`/determinism
lemmas; or when the strengthening is not reused elsewhere, so a dedicated flags
record is not worth carrying.

## Consequences

The move creates one obligation per hypothesis of the general pass theorem:
here 9 goals, one per bullet, each closed by a named lemma or a trivial step
(`apply wf'`, `reflexivity`). The strengthened statement
`EProgram.wf_eprogram (certirocq_flags env_flags) p` is itself a precondition
the caller must establish; the sibling `metarocq_to_anf_total` (correctness.v
190-215) keeps the same strengthened hypothesis and shows the total/existential
form by first applying `convert_top_anf_total` and then
`metarocq_to_anf_correct`. Failure mode: if the strengthened invariant does not
decompose into the pass theorem's individual hypotheses, the bullets stop being
one-lemma-each and the glue grows.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/nix-action-default.yml runs on push to main (default branch); its CertiRocq job runs 'nix-build --argstr bundle default --argstr job CertiRocq', which compiles the whole CertiRocq project including theories/Compiler/correctness.v (mapped to CertiRocq.Compiler by _CoqProject line 3). Pinned commit 943b52ae654708130f241ccf8a50ecb95a7956e2 is HEAD of main (GitHub compare main...943b52a: status identical, ahead_by 0, behind_by 0). | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: convert_top_anf_correct@theories/Compiler/correctness.v:160, convert_env_inj@theories/Compiler/correctness.v:163, convert_env_reg@theories/Compiler/correctness.v:165, cenv_tgm_coh@theories/Compiler/correctness.v:185, wf_env_inductive@theories/Compiler/correctness.v:159, lambda_glob_eval_env_fuel@theories/Compiler/correctness.v:168, eval_val_exact_det@theories/Compiler/correctness.v:174, lookup_env_wellformed@theories/Compiler/correctness.v:179; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 7 file(s) byte-identical at 943b52ae654708130f241ccf8a50ecb95a7956e2 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(metarocq_to_anf_correct, 49) -> lines: site metarocq_to_anf_correct has 49 lines | check_claims.py |
| 2 | verified | declared(convert_top_anf_correct, theories/LambdaBox_to_LambdaANF/anf_toplevel.v, 581-609) -> declared: convert_top_anf_correct is declared at theories/LambdaBox_to_LambdaANF/anf_toplevel.v:581 | check_claims.py |
| 3 | verified | no_sorry(theories/Compiler/correctness.v, 140-188) -> no_sorry: none of admit, Admitted, Axiom, axiom in theories/Compiler/correctness.v:140-188 | check_claims.py |
| 4 | verified | Read code/theories/Compiler/correctness.v: the comment at lines 122-127 reads 'To prove the correctness of connecting the MetaRocq pipeline and CertiRocq's ANF, we need a stronger well-formedness property. This formalizes the remaining mismatch between metarocq's pipeline and certirocq's LambdaANF: - primitives are not supported in fuel_sem ... - the environment must be axiom free, as usual'. The quoted sentence appears verbatim. Note: the comment actually spans 122-127 (claim says 123-128, off by one) but the quote is exact. | verifier |
| 5 | verified | Read code/theories/Compiler/correctness.v lines 150-188 (parent body). All 8 named lemmas are cited directly: wf_env_inductive (159), convert_top_anf_correct (160), convert_env_inj (163), convert_env_reg (165), lambda_glob_eval_env_fuel (168 and 172), eval_val_exact_det (174), lookup_env_wellformed (179), cenv_tgm_coh (185). No other named lemma is applied in the body, so the count of 8 is exact. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent site correctness.v 140-188 is 49 lines and matches parent.statement verbatim; all 8 children (convert_top_anf_correct, convert_env_inj, convert_env_reg, cenv_tgm_coh, wf_env_inductive, lambda_glob_eval_env_fuel, eval_val_exact_det, lookup_env_wellformed) are exactly the named lemmas the proof body cites (lines 159,160,163,165,168/172,174,179,185), each statement verbatim and each closed_by matching the copied code; glue is one eapply of convert_top_anf_correct plus 9 bullets, one per hypothesis, matching the README table. Shape numbers correct: direct_lemmas=8, glue_lines=49 (188-140+1), child_lines=[29,12,22,22,17,15,198] matching the 7 child sites, depth=3 via lambda_glob_eval_env_fuel->lambda_glob_declared(86)->lambda_glob_lookup(72). Provenance pass (7 files byte-identical). | reviewer-correctness |
| generality | accept | Move is abstracted beyond the example: applicability.goal_shape/use_when/avoid_when restate it as a general schema (general pass theorem needs stronger hypotheses than the pipeline postcondition; strengthen the parent with exactly the invariant that makes them dischargeable). The strengthening is the authors' own framing, confirmed at correctness.v 123-128. 'When not to use' is specific and honest: the three avoid_when conditions (invariant fails to decompose into the pass theorem's hypotheses; hypotheses need genuinely new proofs; strengthening not reused) each name the actual breakage point. Consequences are honest and code-confirmed: 9 bullets = one obligation per Section context of convert_top_anf_correct (Hwf_glob/HnoVar/HnoEvar/HnoCoFix/HnoLazy/Hblocks/HnoArray/no_prims/cenv_tgm_coh, anf_toplevel.v 560-580), the strengthened hypothesis is a caller precondition, and the sibling metarocq_to_anf_total (correctness.v 190-215) really reuses it via convert_top_anf_total then metarocq_to_anf_correct. Good leaves for a bounded prover are stated: self-contained statement closing on its own or via a named sibling, enumerated per leaf with its closure path and depth. Minor caveat, not material: the leaf criterion says 'self-contained/closes independently' rather than size, and eval_val_exact_det is a 198-line mutual induction; but the entry is transparent (shape.child_lines=198) and describes it as mechanical (one reflexivity case per term constructor). | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are consistent and traceable. check_provenance.py reports 7 files byte-identical at commit 943b52ae654708130f241ccf8a50ecb95a7956e2, so every file permalink, sha256 and byte count in entry.json matches the copied code. entry.json source.commit and source.licence (MIT) match sources/certicoq/source.json (commit 943b52..., licence MIT, licence_files [LICENSE.md]) and SOURCE.md. The copied upstream-LICENSE.md is the standard MIT text, and the README 'Source and licence' section names the same commit, MIT licence and source note. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/CertiCoq/certicoq at commit `943b52ae654708130f241ccf8a50ecb95a7956e2`, under `MIT`; see the [source note](../../sources/certicoq/SOURCE.md) for the licence text and attribution.
