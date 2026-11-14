# Law-by-law assembly of disp_Monad_laws_from_hss, the monad laws of the monad induced by a heterogeneous substitution system

| | |
|---|---|
| Kind | instance |
| Move | other |
| Language | rocq |
| Status | accepted |
| Source | [unimath](../../sources/unimath/SOURCE.md) at `7a4b03cce494` |
| Licence | `LicenseRef-UniMath` |
| Licence recorded | 2026-11-14T22:40:52Z |

## Intent

Reduce the monad laws of the monad induced by a heterogeneous substitution
system (hss) to four same-file lemmas: the two unit laws are closed by named
lemmas, and the associativity law is closed not by a single named lemma but by
a transitivity bridge (`intermediate_path`) between two named equations for the
bracket `μ_3`.

## The decomposition

### parent `disp_Monad_laws_from_hss`: [`UniMath/SubstitutionSystems/MonadsFromSubstitutionSystems.v` lines 547-562](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/SubstitutionSystems/MonadsFromSubstitutionSystems.v#L547-L562) ([local copy](code/UniMath/SubstitutionSystems/MonadsFromSubstitutionSystems.v))

```coq
Lemma disp_Monad_laws_from_hss : disp_Monad_laws disp_Monad_data_from_hss.
Proof.
  split.
  - unfold disp_Monad_data_from_hss; simpl; split.
    + apply Monad_law_1_from_hss.
    + apply Monad_law_2_from_hss.
  - unfold disp_Monad_data_from_hss; simpl.
    intro c.
    intermediate_path (pr1 μ_3 c).
    + set (H1 := μ_3_T_μ_2_μ_2).
      set (H2 := nat_trans_eq_weq (homset_property C) _ _ H1).
      apply pathsinv0, H2.
    + set (H1 :=  μ_3_μ_2_T_μ_2).
      set (H2 := nat_trans_eq_weq (homset_property C) _ _ H1).
      apply pathsinv0, H2.
Qed.
```

### child `Monad_law_1_from_hss`: [`UniMath/SubstitutionSystems/MonadsFromSubstitutionSystems.v` lines 163-172](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/SubstitutionSystems/MonadsFromSubstitutionSystems.v#L163-L172) ([local copy](code/UniMath/SubstitutionSystems/MonadsFromSubstitutionSystems.v))

```coq
Lemma Monad_law_1_from_hss :
  ∏ c : C, μ_0 (pr1 (`T) c) · μ_2 c = identity ((pr1 (`T)) c).
Proof.
  intro c.
  unfold μ_0.
  set (H' := prejoin_from_hetsubst_η T).
  set (H2:= nat_trans_eq_weq (homset_property C) _ _ H').
  apply pathsinv0.
  apply H2.
Qed.
```

### child `Monad_law_2_from_hss`: [`UniMath/SubstitutionSystems/MonadsFromSubstitutionSystems.v` lines 177-244](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/SubstitutionSystems/MonadsFromSubstitutionSystems.v#L177-L244) ([local copy](code/UniMath/SubstitutionSystems/MonadsFromSubstitutionSystems.v))

```coq
Lemma Monad_law_2_from_hss:
  ∏ c : C, # (pr1 (`T)) (μ_0 c)· μ_2 c = identity ((pr1 (`T)) c).
Proof.
  intro c.
  intermediate_path (μ_1 c).
  - unfold μ_1.
    assert (H' := @fbracket_unique_target_pointwise _ _ _ T).
    assert (H1 := H'  _ μ_0_ptd).
    set (x := post_whisker μ_0 (`T)
             : EndC ⟦ `T • functor_identity _  , `T • `T ⟧).
    set (x' := x · μ_2).
    assert (H2 := H1 x').
    apply H2; clear H2.
    unfold x'. clear x'.
    unfold x; clear x.
    clear H1. clear H'. clear c.
    split.
    + apply nat_trans_eq_alt.
      intro c.
      assert (H' := nat_trans_ax (η T)).
      simpl in H'.
      rewrite assoc.
      cbn.
      rewrite <- H'; clear H'.
      assert (H' := prejoin_from_hetsubst_η T).
      assert (H2 := nat_trans_eq_weq (homset_property C) _ _ H').
      simpl in H2.
      rewrite <- assoc.
      rewrite <- H2.
      apply pathsinv0. apply id_right.
    + rewrite functor_comp.
      apply nat_trans_eq_alt.
      intro c.
      rewrite <- horcomp_id_postwhisker.
      do 2 rewrite assoc.
      simpl in *. unfold horcomp_data; simpl.
      intermediate_path ( # (pr1 (H ( (` T)))) (μ_0 c) · pr1 (θ ((`T) ⊗ (p T))) c ·
                  pr1 (# H μ_2) c · pr1 (τ T) c).
      * unfold tau_from_alg; cbn.
        do 2 rewrite assoc.
        do 3 apply cancel_postcomposition.
        assert (H' := θ_nat_2 _ _ _ H θ).
        assert (H2 := H' (`T) _ _ μ_0_ptd); clear H'.
        assert (H3 := nat_trans_eq_weq (homset_property C) _ _ H2 c); clear H2.
        simpl in H3. unfold horcomp_data in H3; simpl in H3.
        rewrite id_left in H3.
        apply (!H3).
      * assert (H' := prejoin_from_hetsubst_τ T).
        assert (H2 := nat_trans_eq_weq (homset_property C) _ _ H' c); clear H'.
        simpl in *.
        do 2 rewrite <- assoc.
        {
          intermediate_path (  # (pr1 (H (` T))) (μ_0 c) ·
                       (pr1 (τ T) (pr1 (`T) c) · pr1 μ_2 c)).
          - apply maponpaths.
            rewrite assoc.
            apply H2. (* rewrite done *)
          - clear H2.
            do 2 rewrite assoc.
            apply cancel_postcomposition.
            etrans.
            { apply (nat_trans_ax (τ T) ). }
            apply cancel_postcomposition.
            apply pathsinv0.
            apply id_right.
        }
  - apply μ_1_identity'.
Qed.
```

### child `μ_3_T_μ_2_μ_2`: [`UniMath/SubstitutionSystems/MonadsFromSubstitutionSystems.v` lines 286-336](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/SubstitutionSystems/MonadsFromSubstitutionSystems.v#L286-L336) ([local copy](code/UniMath/SubstitutionSystems/MonadsFromSubstitutionSystems.v))

```coq
Lemma μ_3_T_μ_2_μ_2 : μ_3 =
                      (`T ∘ μ_2 : EndC ⟦ `T • _  , `T • `T ⟧ ) · μ_2.
Proof.
  apply pathsinv0.
  apply (fbracket_unique T μ_2_ptd).
  split.
  - apply nat_trans_eq_alt.
    intro c.
    assert (H2 := nat_trans_ax (η T)); simpl in H2.
    rewrite assoc.
    simpl; rewrite <- H2 ; clear H2.
    intermediate_path (μ_2 c · identity _ ).
    + apply pathsinv0, id_right.
    + etrans; [| apply assoc ].
      apply maponpaths. apply pathsinv0. apply Monad_law_1_from_hss.
  - rewrite functor_comp.
    assert (H1 := θ_nat_2 _ _ _ H θ (`T) _ _ μ_2_ptd).
    simpl in H1.
    repeat rewrite assoc.
    match goal with |[H1 : ?g = _ |- _ · _ · ?f · ?h = _ ] =>
         intermediate_path (g · f · h) end.
    + do 2 apply cancel_postcomposition.
      apply pathsinv0.
      etrans; [apply H1 |].
      clear H1.
      do 2 apply maponpaths.
      assert (H3 := horcomp_id_postwhisker).
      assert (H4 := H3 _ _ _ _ _ μ_2 (`T)); clear H3.
      apply H4.
    + clear H1.
      apply nat_trans_eq_alt.
      intro c; simpl. unfold horcomp_data; simpl.
      rewrite id_left.
      assert (H2 := prejoin_from_hetsubst_τ T).
      assert (H3 := nat_trans_eq_pointwise H2 c); clear H2.
      simpl in *.
      match goal with |[H3 : _ = ?f |- ?e · _ · _ · _  = _ ] =>
         intermediate_path (e · f) end.
      * etrans; [ apply assoc' |].
        etrans; [ apply assoc' |].
        apply maponpaths.
        etrans; [| apply H3 ].
        apply assoc.
      * clear H3.
        repeat rewrite assoc.
        apply cancel_postcomposition.
        assert (H1 := nat_trans_ax (τ T )).
        unfold tau_from_alg in H1.
        etrans; [ | apply H1]; clear H1.
        apply assoc'.
Qed.
```

### child `μ_3_μ_2_T_μ_2`: [`UniMath/SubstitutionSystems/MonadsFromSubstitutionSystems.v` lines 347-447](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/SubstitutionSystems/MonadsFromSubstitutionSystems.v#L347-L447) ([local copy](code/UniMath/SubstitutionSystems/MonadsFromSubstitutionSystems.v))

```coq
Lemma μ_3_μ_2_T_μ_2 :  (
    @compose (functor_category C C)
                 (* TtimesTthenT *) T²∙T _ _
                 (* (@functor_composite C C C ((functor_ptd_forget C hs) T)
                    ((functor_ptd_forget C hs) T))
                 ((functor_ptd_forget C hs) T) *)
          ((μ_2 •• `T) (* :  TtimesTthenT' --> _ *)
                  (*:@functor_compose C C C hs hs
                    (@functor_composite C C C ((functor_ptd_forget C hs) T)
                                              ((functor_ptd_forget C hs) T))
                    ((functor_ptd_forget C hs) T) --> _*) ) μ_2 :
            (*TtimesTthenT'*) T•T² --> `T) = μ_3.
Proof.
  apply (fbracket_unique (*_pointwise*) T μ_2_ptd).
  split.
  - apply nat_trans_eq_alt; intro c.
    simpl.
    intermediate_path (identity _ · μ_2 c).
    + apply pathsinv0, id_left.
    + etrans; [ | apply assoc' ].
      apply cancel_postcomposition.
      assert (H1 := Monad_law_1_from_hss (pr1 (`T) c)).
      apply (!H1).
  - set (B := τ T).
    match goal with | [|- _ · # ?H (?f · _ ) · _ = _ ] => set (F := f : (*TtimesTthenT'*) T•T² --> _ ) end.
    assert (H3 := functor_comp H F μ_2).
    unfold functor_compose in H3.
    etrans.
    { apply cancel_postcomposition. apply maponpaths. apply H3. }
    clear H3.
    apply nat_trans_eq_alt.
    intro c.
    simpl.
    match goal with | [ |- ?a · _ · _ = _ ] => set (Ac := a) end.
    simpl in Ac.
    simpl in *.
    unfold functor_compose in *.
    assert (HX := θ_nat_1 _ _ _ H θ _ _ μ_2).  (* it may be tested with the primed version *)
    assert (HX1 := HX (ptd_from_alg T)); clear HX.
    simpl in HX1.
    assert (HXX := nat_trans_eq_pointwise HX1 c); clear HX1.
    simpl in HXX. unfold horcomp_data in HXX.
    rewrite (functor_id ( H (`T))) in HXX.
    rewrite id_right in HXX. (* last two lines needed because of def. of theta on product category *)
    match goal with |[HXX : ?f · ?h = _ · _ |- _ · (_ · ?x ) · ?y = _ ] =>
      intermediate_path (pr1 (θ ((`T) ⊗ (ptd_from_alg T))) (pr1 (pr1 (pr1 T)) c)·
                       f · h · x · y) end.
    * repeat rewrite assoc.
      do 3 apply cancel_postcomposition.
      unfold Ac. clear Ac.
      etrans; [| apply assoc ].
      etrans.
      2: { apply maponpaths. apply (!HXX). }
      clear HXX.
      assert (Strength_2 :
                ∏ α : functor_compose (functor_composite (`T) (`T))(`T) --> functor_composite (` T) (`T),
                     pr1 (θ (`T ⊗ T_squared)) c · pr1 (# H α) c =
                     pr1 (θ ((`T) ⊗ (ptd_from_alg T))) ((pr1 (pr1 (pr1 T))) c)·
                     pr1 (θ (( ((`T) • (`T) : [_, _])) ⊗ (ptd_from_alg T))) c·
                     pr1 (# H (α : functor_compose (`T) (functor_composite (`T) (` T))--> _)) c ).
      { intro α;
          assert (HA := θ_Strength2_int_implies_θ_Strength2 _ θ_strength2_int);
          assert (HA' := HA (`T) (ptd_from_alg T) (ptd_from_alg T) _ α); clear HA;
          assert (HA2 := nat_trans_eq_pointwise HA' c ); clear HA';
          simpl in HA2; apply HA2.
      }
      etrans; [ apply (Strength_2 F) |].
      clear Strength_2.
      etrans; [ apply assoc' |].
      do 2 apply maponpaths.
      match goal with |[ |- _ = ?pr1 (# ?G ?g) _ ] =>
              assert (X : F = g) end.
      { apply nat_trans_eq; try apply homset_property.
        intros. unfold F.
        simpl. unfold horcomp_data; simpl.
        rewrite functor_id.
        apply pathsinv0, id_right.
      }
      apply (maponpaths (λ T,  pr1 (# H T) c)).
      apply X.
    * clear HXX. clear Ac. clear F. clear B.
      assert (H4 := prejoin_from_hetsubst_τ T).
      assert (H5 := nat_trans_eq_pointwise H4 c); clear H4.
      simpl in H5.
      {
        match goal with |[ H5 : _ = ?e |- ?a · ?b · _ · _ · _ = _ ] =>
                         intermediate_path (a · b · e) end.
        - repeat rewrite <- assoc.
          do 2 apply maponpaths.
          repeat rewrite <- assoc in H5. apply H5.
        - clear H5.
          repeat rewrite assoc.
          apply cancel_postcomposition.
          assert (HT := prejoin_from_hetsubst_τ T).
          assert (H6 := nat_trans_eq_pointwise HT); clear HT.
          unfold coproduct_nat_trans_in2_data.
          unfold tau_from_alg, tau2_from_alg in H6.
          rewrite assoc in H6.
          apply H6.
      }
Qed.
```

How the parts fit. `disp_Monad_laws_from_hss` is the proof that the data
`disp_Monad_data_from_hss := μ_2 ,, μ_0` (line 158) satisfies the monad laws.
The glue `split`s the `disp_Monad_laws` structure into its two components, then
`split`s again on the unit-law component, so each law is a separate obligation
closed by one named lemma:

```
disp_Monad_laws_from_hss (parent, 547-562)
├─ split → unit laws
│   ├─ Monad_law_1_from_hss (163-172)    η · μ = id
│   └─ Monad_law_2_from_hss (177-244)    Tη · μ = id
│         └─ μ_1_identity' (124-129)     closes its right branch
│               └─ μ_1_identity (101-121)
└─ associativity: intermediate_path (pr1 μ_3 c)
    ├─ μ_3_T_μ_2_μ_2 (286-336)    μ_3 = (T ∘ μ_2) · μ_2   (uses Monad_law_1_from_hss, line 300)
    └─ μ_3_μ_2_T_μ_2 (347-447)    (μ_2 •• T) · μ_2 = μ_3  (uses Monad_law_1_from_hss, line 368)
```

The distinctive part is the associativity branch. Instead of a single
`Monad_law_3_from_hss`, the authors state *two* equations — each side of the
associativity pentagon, separately equal to the bracket `μ_3` — and join them in
the glue with `intermediate_path (pr1 μ_3 c)`, flipping each with `pathsinv0`.
So associativity is a transitivity (calc) chain whose two links are the named
lemmas.

Why each lemma is a good leaf:

- `Monad_law_1_from_hss` is self-contained: it unfolds `μ_0` and applies the
  η-law of the prejoin (`prejoin_from_hetsubst_η T`), closing in six lines from
  one imported fact.
- `Monad_law_2_from_hss` closes from named facts: the uniqueness of the bracket
  (`fbracket_unique_target_pointwise`) on the left and the same-file sibling
  `μ_1_identity'` on the right (`apply μ_1_identity'`, line 243), which itself
  rests on `μ_1_identity`.
- `μ_3_T_μ_2_μ_2` and `μ_3_μ_2_T_μ_2` are each an instance of the same leaf
  principle: `μ_3` is the *unique* bracket arrow, so each side's equality to `μ_3`
  is closed by `apply (fbracket_unique T μ_2_ptd)` plus the two naturality
  conditions, reusing `Monad_law_1_from_hss` as a leaf (lines 300 and 368).

The move at the top is a backward split on the structure (survey-F rule 8); in
my opinion the copy-worthy detail is the transitivity bridge (rule 9), because
it turns a law with no single named proof into two provable equations plus a
one-line glue step.

## Why it is good

1. The parent site `disp_Monad_laws_from_hss` is 16 lines long (check; lines
   547-562), so the assembly of four named lemmas costs little glue.
2. The glue closes the associativity law with a transitivity step: the tactic
   `intermediate_path` occurs in the parent site (check; line 555).
3. No `sorry`/`admit`/`Admitted`/`axiom` token occurs in lines 163-562 of the
   copied file, the span covering all five sites (check).
4. The theorem-scale shape: 4 direct lemmas assembled by a 16-line glue, with
   child proof sites of 10, 68, 51 and 101 lines (230 in all) — a measurement
   of the shape recorded in `entry.json`.
5. The authors state the plan in comments: the third law is "Proof of the third
   monad law via transitivity" and "We show that both sides are equal to
   [μ_3 = fbracket μ_2]" (lines 282-283), and the parent is "Finally putting
   together all the preparatory results to obtain a monad" (line 545)
   (author-statement).

The same two `μ_3` lemmas are reused, with an explicit associator inserted, by
`third_monad_law_from_hss` in the same file (lines 453-458).

## When to use it, and when not

Use it when the goal is a structure/record of laws whose fields are equations,
and each field already has a separately proved lemma in the same development;
the glue is then a backward `split` on the structure with one `apply` per law.
Use the transitivity bridge specifically when an equality field is best proved
by showing both sides equal to a shared intermediate object (here the bracket
`μ_3`), i.e. when the two directions are themselves non-trivial and worth
stating as named lemmas.

Avoid it when a single named lemma for the whole law would be shorter and
clearer; when the two sides of the equality are equal to different
representatives, so the `intermediate_path` bridge does not typecheck; or when
the record's fields are trivial enough for one automation pass.

## Consequences

The glue `split`s `disp_Monad_laws` into its two components, and the
associativity component is closed by a transitivity bridge rather than one
lemma. Both `μ_3` equations must land on the same intermediate value (`μ_3`) for
`intermediate_path` to typecheck, and each is flipped by `pathsinv0` because the
named equations are oriented `μ_3 = …` while the goal wants the reverse
orientation. If the two sides of the associative law are equal to different
representatives of `μ_3`, the bridge does not apply and the law needs a single
named lemma, or an explicit associator as in `third_monad_law_from_hss` (which
inserts `rassociator_CAT`).

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | CI workflow .github/workflows/build-unimath.yml runs on push/PR to master (default branch); commit 7a4b03cce49449f45ce0d4285615165172f50546 is on master (branches-where-head=master). Main build runs 'dune build' over the default UniMath target, which compiles UniMath/SubstitutionSystems/MonadsFromSubstitutionSystems.v. | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: Monad_law_1_from_hss@UniMath/SubstitutionSystems/MonadsFromSubstitutionSystems.v:551, Monad_law_2_from_hss@UniMath/SubstitutionSystems/MonadsFromSubstitutionSystems.v:552, μ_3_T_μ_2_μ_2@UniMath/SubstitutionSystems/MonadsFromSubstitutionSystems.v:556, μ_3_μ_2_T_μ_2@UniMath/SubstitutionSystems/MonadsFromSubstitutionSystems.v:559; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 7a4b03cce49449f45ce0d4285615165172f50546 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(disp_Monad_laws_from_hss, 16) -> lines: site disp_Monad_laws_from_hss has 16 lines | check_claims.py |
| 2 | verified | cites(disp_Monad_laws_from_hss, intermediate_path) -> cites: intermediate_path occurs at UniMath/SubstitutionSystems/MonadsFromSubstitutionSystems.v:555 | check_claims.py |
| 3 | verified | no_sorry(UniMath/SubstitutionSystems/MonadsFromSubstitutionSystems.v, 163-562) -> no_sorry: none of admit, Admitted, Axiom, axiom in UniMath/SubstitutionSystems/MonadsFromSubstitutionSystems.v:163-562 | check_claims.py |
| 4 | verified | Line counts checked against the copied file: Monad_law_1_from_hss 163-172 = 10 lines (Lemma at 163, Qed at 172); Monad_law_2_from_hss 177-244 = 68 lines; mu_3_T_mu_2_mu_2 286-336 = 51 lines; mu_3_mu_2_T_mu_2 347-447 = 101 lines; children sum 230; parent 547-562 = 16 lines; 4 direct lemmas. | verifier |
| 5 | verified | Read lines 282-283 of the copied file: comment 'Proof of the third monad law via transitivity' and 'We show that both sides are equal to [mu_3 = fbracket mu_2]'; line 545: 'Finally putting together all the preparatory results to obtain a monad'. Matches the claim verbatim. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Provenance pass (1 file byte-identical at 7a4b03cce494). Parent site 547-562 (16 lines) matches code: split -> unfold/split -> apply Monad_law_1_from_hss (551) and Monad_law_2_from_hss (552); associativity branch intro c, intermediate_path (pr1 mu_3 c) then mu_3_T_mu_2_mu_2 (556) and mu_3_mu_2_T_mu_2 (559) via pathsinv0. All 4 children are exactly the lemmas the glue cites, and each ends in Qed (closes). Child statements and closed_by match code: Monad_law_1 (apply pathsinv0/apply H2 with prejoin_from_hetsubst_eta T), Monad_law_2 (apply mu_1_identity' at 243), mu_3 lemmas (apply fbracket_unique T mu_2_ptd). Shape numbers correct: glue 16 lines, child sites 10/68/51/101 = 230 (163-172, 177-244, 286-336, 347-447), depth 3 via Monad_law_2 -> mu_1_identity' (124-129) -> mu_1_identity (101-121). Author comments at 282-283 and 545 read as quoted; known_uses third_monad_law_from_hss 453-458 reuses both mu_3 lemmas. | reviewer-correctness |
| generality | accept | Move is stated beyond the example: applicability.goal_shape/use_when/also_known_as generalize to any structure/record of law fields closed by a backward split with one named lemma per field, plus a transitivity bridge for an equality field. 'When not to use' is honest and specific: (1) a single lemma would be shorter/clearer, (2) sides equal to different representatives so intermediate_path won't typecheck, (3) fields trivial enough for one automation pass. Consequences are specific and verified in code: both μ_3 equations must land on the same intermediate μ_3 (sed 547-562 confirmed intermediate_path (pr1 μ_3 c) plus pathsinv0 on each side), and the failure mode names third_monad_law_from_hss inserting rassociator_CAT (sed 453-458 confirmed). Good-leaf rationale for a bounded prover is explicit: 'Why each lemma is a good leaf' shows Monad_law_1 closes from one imported fact (prejoin_from_hetsubst_η), Monad_law_2 from named facts (fbracket_unique_target_pointwise + sibling μ_1_identity'), and both μ_3 lemmas are instances of the single fbracket_unique principle; metrics note no child closes by a single automation tactic — each applies a named project lemma. No standing objection for generality. | reviewer-generality |
| provenance-licence | accept | Provenance pass: check_provenance reports the 1 copied file byte-identical at pinned commit 7a4b03cce49449f45ce0d4285615165172f50546. Copied file sha256 4b9391c5...b400b6 and 21145 bytes match entry.json files[0]. Commit identical across entry.json, sources/unimath/source.json and SOURCE.md. Licence MIT consistent across entry.json, source.json, SOURCE.md and upstream-LICENSE.md (MIT text). All permalinks use the pinned commit; cited line ranges verified against the local copy: parent 547-562, children 163-172/177-244/286-336/347-447, author-statement lines 282-283 and 545, and known_uses 453-458 all match the README excerpts and claims. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/UniMath/UniMath at commit `7a4b03cce49449f45ce0d4285615165172f50546`, under `LicenseRef-UniMath`; see the [source note](../../sources/unimath/SOURCE.md) for the licence text and attribution.
