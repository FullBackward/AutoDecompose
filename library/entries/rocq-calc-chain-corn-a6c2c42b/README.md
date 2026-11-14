# Calculation chain of equalities then inequalities for CoRN's first refinement lemma

| | |
|---|---|
| Kind | instance |
| Move | calc-chain |
| Language | rocq |
| Status | accepted |
| Source | [corn](../../sources/corn/SOURCE.md) at `f67899611292` |
| Licence | `GPL-2.0-or-later` |

## Intent

Bound the difference between the Riemann sum of a partition `P` and that of its
refinement `Q` by `e * (b - a)`, where `e` is the modulus-of-continuity
parameter. The proof chains four equality rewrites (`ref_calc2`..`ref_calc5`)
that normalise the difference into one double sum of
`(fP_i - fQ_j) * (Q_j - Q_{j-1})`, then three inequalities
(`ref_calc6`..`ref_calc8`) up to `e` times that telescoping sum, and finally
`ref_calc1` collapses the inner sum to `P_i - P_{i-1}`.

## The decomposition

### parent `first_refinement_lemma`: [`ftc/RefLemma.v` lines 553-594](https://github.com/rocq-community/corn/blob/f678996112929e1674e20b75fb9bd728ded35e55/ftc/RefLemma.v#L553-L594) ([local copy](code/ftc/RefLemma.v))

```coq
Lemma first_refinement_lemma : AbsIR (Partition_Sum HfP incF[-]Partition_Sum HfQ incF) [<=] e[*] (b[-]a).
Proof.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply ref_calc2.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply ref_calc3.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply ref_calc4.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply ref_calc5.
 eapply leEq_transitive.
  apply ref_calc6.
 eapply leEq_transitive.
  apply ref_calc7.
 eapply leEq_transitive.
  apply ref_calc8.
 apply leEq_wdl with (e[*] Sumx (fun (i : nat) (Hi : i < n) => Sum2
   (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
     Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj'))))).
  apply mult_resp_leEq_lft.
   2: apply less_leEq; assumption.
  apply leEq_wdl with (Sumx (fun (i : nat) (Hi : i < n) => P _ Hi[-]P _ (Nat.lt_le_incl _ _ Hi))).
   2: apply Sumx_wd; intros.
   2: apply eq_symmetric_unfolded; apply ref_calc1.
  eapply leEq_wdl.
   2: apply eq_symmetric_unfolded; apply Mengolli_Sum with (f := fun (i : nat) (Hi : i <= n) => P i Hi).
    eapply leEq_transitive.
     apply leEq_AbsIR.
    eapply leEq_wdr.
     2: apply AbsIR_eq_x.
     2: apply shift_leEq_minus; astepl a; assumption.
    apply compact_elements with Hab; apply Partition_in_compact.
   red in |- *; intros; apply prf1; auto.
  intros; apply cg_minus_wd; apply prf1; auto.
 apply eq_symmetric_unfolded; eapply eq_transitive_unfolded.
  2: apply Sumx_comm_scal'.
 apply Sumx_wd; intros.
 eapply eq_transitive_unfolded.
  2: apply Sum2_comm_scal'.
  algebra.
 apply RL_sub_SS.
Qed.
```

### child `ref_calc1`: [`ftc/RefLemma.v` lines 238-284](https://github.com/rocq-community/corn/blob/f678996112929e1674e20b75fb9bd728ded35e55/ftc/RefLemma.v#L238-L284) ([local copy](code/ftc/RefLemma.v))

```coq
Lemma ref_calc1 :
  forall (i : nat) (Hi : i < n),
  Sum2
    (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
     Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj'))) [=]
  P _ Hi[-]P _ (Nat.lt_le_incl _ _ Hi).
Proof.
 intros.
 unfold Sum2 in |- *.
 elim (RL_sub_hyp (S i) Hi); intros P1 HP1.
 elim (RL_sub_hyp i (Nat.lt_le_incl _ _ Hi)); intros P2 HP2.
 apply eq_transitive_unfolded with (Q _ P1[-]Q _ P2).
  2: apply eq_symmetric_unfolded; apply cg_minus_wd; [ apply HP1 | apply HP2 ].
 cut (sub (S i) = S (pred (sub (S i)))).
  2: symmetry; apply Nat.lt_succ_pred with 0; apply RL_sub_S.
 intro.
 generalize P1 HP1; clear HP1 P1. pattern (sub (S i)) at 1 2 11 in |- *.
 rewrite H1; intros.
 eapply eq_transitive_unfolded.
  apply str_Mengolli_Sum_gen with (f := h).
   apply RL_sub_SS.
  intros j Hj Hj'.
  elim (le_lt_dec j (pred (sub (S i)))); intro; simpl in |- *.
   elim (le_lt_dec (sub i) j); intro; simpl in |- *.
    unfold h in |- *.
    apply cg_minus_wd.
     elim (le_lt_dec (S j) m); intro; simpl in |- *.
      apply prf1; auto.
     cut (S j <= m); [ intro | apply H' with i; assumption ].
     exfalso; apply (proj1 (Nat.le_ngt _ _) H2 b0).
    elim (le_lt_dec j m); intro; simpl in |- *.
     apply prf1; auto.
    cut (j < m); [ intro | apply H with i; assumption ].
    exfalso; apply Nat.le_ngt with m j; auto with arith.
   exfalso; apply Nat.le_ngt with (sub i) j; auto with arith.
  exfalso; apply (proj1 (Nat.le_ngt _ _) Hj' b0).
 unfold h in |- *.
 apply cg_minus_wd.
  elim (le_lt_dec (S (pred (sub (S i)))) m); intro; simpl in |- *.
   apply prf1; auto.
  exfalso.
  apply (proj1 (Nat.le_ngt _ _) P1 b0).
 elim (le_lt_dec (sub i) m); intro; simpl in |- *.
  apply prf1; auto.
 exfalso.
 apply (proj1 (Nat.le_ngt _ _) P2 b0).
Qed.
```

### child `ref_calc2`: [`ftc/RefLemma.v` lines 289-350](https://github.com/rocq-community/corn/blob/f678996112929e1674e20b75fb9bd728ded35e55/ftc/RefLemma.v#L289-L350) ([local copy](code/ftc/RefLemma.v))

```coq
Lemma ref_calc2 :
  AbsIR (Partition_Sum HfP incF[-]Partition_Sum HfQ incF) [=]
  AbsIR
    (Sumx
       (fun (i : nat) (Hi : i < n) =>
        Part F (fP i Hi) just1[*]
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))) [-]
     Sumx
       (fun (i : nat) (Hi : i < n) =>
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           Part F (fQ j (H _ _ Hi Hj')) just2[*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))).
Proof.
 apply AbsIR_wd; unfold Partition_Sum in |- *.
 apply cg_minus_wd.
  apply Sumx_wd; intros.
  apply mult_wdr.
  apply eq_symmetric_unfolded; apply ref_calc1.
 apply eq_symmetric_unfolded; unfold Sum2 in |- *.
 apply eq_transitive_unfolded with (Sumx (fun (j : nat) (Hj : j < m) => part_tot_nat_fun _ _
   (fun (i : nat) (H : i < m) => Part F (fQ i H) just2[*] (Q _ H[-]Q _ (Nat.lt_le_incl _ _ H))) j)).
  apply str_Sumx_Sum_Sum with (g := fun (i : nat) (Hi : i < n) (i0 : nat) =>
    sumbool_rect (fun _ : {sub i <= i0} + {i0 < sub i} => IR) (fun _ : sub i <= i0 => sumbool_rect
      (fun _ : {i0 <= pred (sub (S i))} + {pred (sub (S i)) < i0} => IR)
        (fun a1 : i0 <= pred (sub (S i)) => Part F (fQ i0 (H i i0 Hi a1)) just2[*]
          (Q (S i0) (H' i i0 Hi a1) [-] Q i0 (Nat.lt_le_incl i0 m (H i i0 Hi a1))))
            (fun _ : pred (sub (S i)) < i0 => [0]) (le_lt_dec i0 (pred (sub (S i)))))
              (fun _ : i0 < sub i => [0]) (le_lt_dec (sub i) i0)) (h := part_tot_nat_fun _ _
                (fun (i : nat) (H : i < m) =>
                  Part F (fQ i H) just2[*] (Q _ H[-]Q _ (Nat.lt_le_incl _ _ H)))).
     exact RL_sub_0.
    exact RL_sub_mon.
   intros.
   elim (le_lt_dec (sub i) j); intro; simpl in |- *.
    elim (le_lt_dec j (pred (sub (S i)))); intro; simpl in |- *.
     unfold part_tot_nat_fun in |- *.
     elim (le_lt_dec m j); intro; simpl in |- *.
      exfalso.
      cut (0 < sub (S i)); [ intro | apply RL_sub_S ].
      cut (sub (S i) <= m); intros.
       apply (proj1 (Nat.le_ngt _ _) H4); apply Nat.le_lt_trans with j; auto.
      rewrite <- RL_sub_n.
      apply RL_sub_mon'; apply Hi.
     apply mult_wd.
      apply pfwdef.
      apply HfQ'; auto.
     apply cg_minus_wd; apply prf1; auto.
    exfalso; apply (proj1 (Nat.le_ngt _ _) b0).
    rewrite (Nat.lt_succ_pred _ _ (RL_sub_S i)); auto.
   exfalso; apply (proj1 (Nat.le_ngt _ _) H1 b0).
  symmetry  in |- *; apply RL_sub_n.
 apply Sumx_wd; intros.
 unfold part_tot_nat_fun in |- *.
 elim (le_lt_dec m i); intro; simpl in |- *.
  exfalso; apply Nat.le_ngt with m i; auto.
 apply mult_wd.
  apply pfwdef; apply HfQ'; auto.
 apply cg_minus_wd; apply prf1; auto.
Qed.
```

### child `ref_calc3`: [`ftc/RefLemma.v` lines 352-387](https://github.com/rocq-community/corn/blob/f678996112929e1674e20b75fb9bd728ded35e55/ftc/RefLemma.v#L352-L387) ([local copy](code/ftc/RefLemma.v))

```coq
Lemma ref_calc3 :
  AbsIR
    (Sumx
       (fun (i : nat) (Hi : i < n) =>
        Part F (fP i Hi) just1[*]
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))) [-]
     Sumx
       (fun (i : nat) (Hi : i < n) =>
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           Part F (fQ j (H _ _ Hi Hj')) just2[*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))) [=]
  AbsIR
    (Sumx
       (fun (i : nat) (Hi : i < n) =>
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           Part F (fP i Hi) just1[*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj'))))) [-]
     Sumx
       (fun (i : nat) (Hi : i < n) =>
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           Part F (fQ j (H _ _ Hi Hj')) just2[*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))).
Proof.
 apply AbsIR_wd.
 apply cg_minus_wd; apply Sumx_wd; intros.
  apply eq_symmetric_unfolded; apply Sum2_comm_scal' with
    (f := fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
      Q (S j) (H' _ _ H1 Hj') [-]Q j (Nat.lt_le_incl _ _ (H _ _ H1 Hj'))).
  apply RL_sub_SS.
 algebra.
Qed.
```

### child `ref_calc4`: [`ftc/RefLemma.v` lines 389-421](https://github.com/rocq-community/corn/blob/f678996112929e1674e20b75fb9bd728ded35e55/ftc/RefLemma.v#L389-L421) ([local copy](code/ftc/RefLemma.v))

```coq
Lemma ref_calc4 :
  AbsIR
    (Sumx
       (fun (i : nat) (Hi : i < n) =>
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           Part F (fP i Hi) just1[*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj'))))) [-]
     Sumx
       (fun (i : nat) (Hi : i < n) =>
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           Part F (fQ j (H _ _ Hi Hj')) just2[*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))) [=]
  AbsIR
    (Sumx
       (fun (i : nat) (Hi : i < n) =>
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           Part F (fP i Hi) just1[*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj'))) [-]
           Part F (fQ j (H _ _ Hi Hj')) just2[*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))).
Proof.
 apply AbsIR_wd.
 eapply eq_transitive_unfolded.
  apply Sumx_minus_Sumx.
 apply Sumx_wd; intros.
 eapply eq_transitive_unfolded.
  apply Sum2_minus_Sum2.
  apply RL_sub_SS.
 algebra.
Qed.
```

### child `ref_calc5`: [`ftc/RefLemma.v` lines 423-445](https://github.com/rocq-community/corn/blob/f678996112929e1674e20b75fb9bd728ded35e55/ftc/RefLemma.v#L423-L445) ([local copy](code/ftc/RefLemma.v))

```coq
Lemma ref_calc5 :
  AbsIR
    (Sumx
       (fun (i : nat) (Hi : i < n) =>
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           Part F (fP i Hi) just1[*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj'))) [-]
           Part F (fQ j (H _ _ Hi Hj')) just2[*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))) [=]
  AbsIR
    (Sumx
       (fun (i : nat) (Hi : i < n) =>
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           (Part F (fP i Hi) just1[-]Part F (fQ j (H _ _ Hi Hj')) just2) [*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))).
Proof.
 apply AbsIR_wd; apply Sumx_wd; intros.
 apply Sum2_wd; intros.
  apply RL_sub_SS.
 algebra.
Qed.
```

### child `ref_calc6`: [`ftc/RefLemma.v` lines 447-472](https://github.com/rocq-community/corn/blob/f678996112929e1674e20b75fb9bd728ded35e55/ftc/RefLemma.v#L447-L472) ([local copy](code/ftc/RefLemma.v))

```coq
Lemma ref_calc6 :
  AbsIR
    (Sumx
       (fun (i : nat) (Hi : i < n) =>
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           (Part F (fP i Hi) just1[-]Part F (fQ j (H _ _ Hi Hj')) just2) [*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))) [<=]
  Sumx
    (fun (i : nat) (Hi : i < n) =>
     AbsIR
       (Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           (Part F (fP i Hi) just1[-]Part F (fQ j (H _ _ Hi Hj')) just2) [*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))).
Proof.
 eapply leEq_wdr.
  apply triangle_SumxIR.
 apply Sumx_wd.
 intros.
 apply AbsIR_wd.
 apply Sum2_wd.
  apply RL_sub_SS.
 intros j Hj Hj'.
 algebra.
Qed.
```

### child `ref_calc7`: [`ftc/RefLemma.v` lines 474-495](https://github.com/rocq-community/corn/blob/f678996112929e1674e20b75fb9bd728ded35e55/ftc/RefLemma.v#L474-L495) ([local copy](code/ftc/RefLemma.v))

```coq
Lemma ref_calc7 :
  Sumx
    (fun (i : nat) (Hi : i < n) =>
     AbsIR
       (Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           (Part F (fP i Hi) just1[-]Part F (fQ j (H _ _ Hi Hj')) just2) [*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))) [<=]
  Sumx
    (fun (i : nat) (Hi : i < n) =>
     Sum2
       (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
        AbsIR
          ((Part F (fP i Hi) just1[-]Part F (fQ j (H _ _ Hi Hj')) just2) [*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))).
Proof.
 apply Sumx_resp_leEq; intros.
 eapply leEq_wdr.
  apply triangle_Sum2IR.
  apply RL_sub_SS.
 algebra.
Qed.
```

### child `ref_calc8`: [`ftc/RefLemma.v` lines 497-550](https://github.com/rocq-community/corn/blob/f678996112929e1674e20b75fb9bd728ded35e55/ftc/RefLemma.v#L497-L550) ([local copy](code/ftc/RefLemma.v))

```coq
Lemma ref_calc8 :
  Sumx
    (fun (i : nat) (Hi : i < n) =>
     Sum2
       (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
        AbsIR
          ((Part F (fP i Hi) just1[-]Part F (fQ j (H _ _ Hi Hj')) just2) [*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))) [<=]
  Sumx
    (fun (i : nat) (Hi : i < n) =>
     Sum2
       (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
        e[*] (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj'))))).
Proof.
 apply Sumx_resp_leEq; intros.
 apply Sum2_resp_leEq.
  apply RL_sub_SS.
 intros j Hj Hj'.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
 apply mult_resp_leEq_both.
    apply AbsIR_nonneg.
   apply AbsIR_nonneg.
  generalize (proj2b_sig2T _ _ _ (contF' e He)); fold d in |- *; intros.
  apply H2.
    unfold I in |- *; apply Pts_part_lemma with n P; assumption.
   unfold I in |- *; apply Pts_part_lemma with m Q; assumption.
  apply leEq_transitive with (Mesh P).
   2: assumption.
  apply leEq_transitive with (AbsIR (P (S i) H1[-]P i (Nat.lt_le_incl _ _ H1))).
   2: eapply leEq_wdl.
    3: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
    2: apply Mesh_lemma.
   2: apply shift_leEq_minus; astepl (P i (Nat.lt_le_incl _ _ H1)); apply prf2.
  apply compact_elements with (prf2 _ _ _ _ P i (Nat.lt_le_incl _ _ H1) H1).
   apply HfP.
  elim (HfQ j (H _ _ H1 Hj')); intros.
  split.
   elim (RL_sub_hyp i (Nat.lt_le_incl _ _ H1)); intros.
   eapply leEq_wdl.
    2: apply eq_symmetric_unfolded; apply p.
   apply leEq_transitive with (Q j (Nat.lt_le_incl _ _ (H i j H1 Hj'))).
    apply Partition_mon; assumption.
   assumption.
  elim (RL_sub_hyp (S i) H1); intros.
  eapply leEq_wdr.
   2: apply eq_symmetric_unfolded; apply p.
  apply leEq_transitive with (Q _ (H i j H1 Hj')).
   assumption.
  apply Partition_mon.
  rewrite <- (Nat.lt_succ_pred _ _ (RL_sub_S i)); auto with arith.
 apply eq_imp_leEq; apply AbsIR_eq_x.
 apply shift_leEq_minus; astepl (Q j (Nat.lt_le_incl _ _ (H _ _ H1 Hj'))); apply prf2.
Qed.
```

How the parts fit. The parent `first_refinement_lemma` rewrites the goal with
four equalities, then walks three inequalities, then finishes with a
telescoping sum:

```text
first_refinement_lemma (553-594)
├── ref_calc2 ──► ref_calc1   (equality: unfold Partition_Sum into two double sums)
├── ref_calc3                 (equality: commute the scalar fQ_j into the inner sum)
├── ref_calc4                 (equality: merge the two Sumx, subtract inside the sum)
├── ref_calc5                 (equality: factor the common Q-difference)
├── ref_calc6                 (inequality: AbsIR through Sumx, triangle_SumxIR)
├── ref_calc7                 (inequality: AbsIR through Sum2, triangle_Sum2IR)
├── ref_calc8                 (inequality: |fP_i - fQ_j| <= e via the modulus of continuity)
└── ref_calc1                 (telescope: the inner Sum2 equals P (S i) - P i)
```

The first four links are equalities applied with `leEq_wdl` (rewrite the left
side of the inequality down); the next three are inequalities applied with
`leEq_transitive`. After `ref_calc8` the goal is `e * Sumx (Sum2 (Q_j -
Q_{j-1}))`; the parent's tail factors out `e`, applies `ref_calc1` to replace
the inner `Sum2` by `P (S i) - P i`, and uses the library lemma `Mengolli_Sum`
to telescope the outer `Sumx` to `b - a`.

Each child is a self-contained statement that closes on its own, except
`ref_calc2`, whose proof uses `ref_calc1` for the `P` side (line 309) and
`str_Sumx_Sum_Sum` for the `Q` side. So the longest chain of the
decomposition's own lemmas below the theorem is `first_refinement_lemma →
ref_calc2 → ref_calc1` (depth 2); the other six children close from library
rewrite/triangle lemmas plus the support facts about the refinement map `sub`
(`RL_sub_0`, `RL_sub_n`, `RL_sub_mon`, `RL_sub_mon'`, `RL_sub_hyp`,
`RL_sub_S`, `RL_sub_SS` and the `Let` maps `H`, `H'`, `H0`, in lines 151-217).
The modulus of continuity enters only at `ref_calc8`, so the first seven links
are purely algebraic and reusable for other integrands.

## Why it is good

1. The parent's proof cites the child `ref_calc1` (it applies
   `ref_calc1` at line 576). (`check`, `cites(parent, ref_calc1)`; [parent site
   lines 553-594](https://github.com/rocq-community/corn/blob/f678996112929e1674e20b75fb9bd728ded35e55/ftc/RefLemma.v#L553-L594))
2. `ref_calc2`'s proof cites `ref_calc1` (line 309), the only dependency from
   one child to another, which is why the chain below the theorem has depth 2.
   (`check`, `cites(ftc/RefLemma.v:289-350, ref_calc1)`; [ref_calc2 site
   lines 289-350](https://github.com/rocq-community/corn/blob/f678996112929e1674e20b75fb9bd728ded35e55/ftc/RefLemma.v#L289-L350))
3. No closing-by-sorry token (`admit`, `Admitted`, `Axiom`, `axiom`) occurs in
   the parent and all eight children (lines 238-594): every link ends in `Qed`.
   (`check`, `no_sorry(ftc/RefLemma.v, 238-594)`; [lines
   238-594](https://github.com/rocq-community/corn/blob/f678996112929e1674e20b75fb9bd728ded35e55/ftc/RefLemma.v#L238-L594))
4. The glue is 42 lines and the eight children are 303 lines in total, so the
   parent proof is the thin skeleton over eight named links. (`measurement`,
   counted from the site line ranges: parent 553-594; children 238-284,
   289-350, 352-387, 389-421, 423-445, 447-472, 474-495, 497-550)
5. The authors state the plan in the file's header: "we prove our main lemma
   in several steps (and versions)" ([lines
   85-86](https://github.com/rocq-community/corn/blob/f678996112929e1674e20b75fb9bd728ded35e55/ftc/RefLemma.v#L85-L86)).
   (`author-statement`)

In my opinion the detail worth copying is the split into a flat equality phase
then an inequality phase: the first seven links are algebra, and only
`ref_calc8` touches the analytic hypothesis (`contF' e He`). That ordering
means each phase can be searched or checked independently of the continuity
argument.

## When to use it, and when not

Use a calculational chain when the goal is a bound (here `AbsIR(._-_.) [<=]
e[*](b[-]a)`) whose two sides differ by a sequence of algebraic normalisations
— pull sums apart, commute scalars, factor a common difference — followed by
triangle inequalities and one analytic bound. Each step is worth naming as its
own lemma, so the main proof cites a flat list of statements and each link can
be proved or checked in isolation.

Avoid it when the intermediate terms are not worth naming (inline the rewrites
instead of giving each one a lemma), when the steps need different hypotheses
at different points in a way that is not monotone (a single `leEq_transitive`
chain composes only same-direction inequalities), or when a single
`eapply leEq_wdl`-style rewrite would be fragile to term-index mismatches. Here
the chain composes cleanly because all three inequality links are `[<=]` in the
same direction, and the equalities are applied to the left side only.

## Consequences

Each link is either an equality applied with `leEq_wdl` (rewriting the left side
of the inequality down, `ref_calc2`..`ref_calc5`) or an inequality applied with
`leEq_transitive` (`ref_calc6`..`ref_calc8`), so the chain is only as strong as
its weakest link, and a single mismatched rewrite breaks every link after it.
The head of the chain must end in a form the tail can discharge: here
`ref_calc8` leaves `e` times an inner sum, the tail factors out `e`,
`ref_calc1` telescopes the inner sum to `P_i - P_{i-1}`, and the library lemma
`Mengolli_Sum` telescopes the outer sum to `b - a`. The modulus of continuity
enters only at `ref_calc8`, so the first seven links are purely algebraic.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/docker-action.yml (default branch master, commit f6789961 on HEAD): docker-coq-action builds coq-corn.opam -> ./configure.sh && make, compiling all -R . CoRN files including ftc/RefLemma.v | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: ref_calc1@ftc/RefLemma.v:576, ref_calc2@ftc/RefLemma.v:556, ref_calc3@ftc/RefLemma.v:558, ref_calc4@ftc/RefLemma.v:560, ref_calc5@ftc/RefLemma.v:562, ref_calc6@ftc/RefLemma.v:564, ref_calc7@ftc/RefLemma.v:566, ref_calc8@ftc/RefLemma.v:568; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at f678996112929e1674e20b75fb9bd728ded35e55 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, ref_calc1) -> cites: ref_calc1 occurs at ftc/RefLemma.v:576 | check_claims.py |
| 2 | verified | cites(ftc/RefLemma.v:289-350, ref_calc1) -> cites: ref_calc1 occurs at ftc/RefLemma.v:309 | check_claims.py |
| 3 | verified | no_sorry(ftc/RefLemma.v, 238-594) -> no_sorry: none of admit, Admitted, Axiom, axiom in ftc/RefLemma.v:238-594 | check_claims.py |
| 4 | verified | counted code/ftc/RefLemma.v site ranges: parent 553-594 = 42 lines; children 238-284=47, 289-350=62, 352-387=36, 389-421=33, 423-445=23, 447-472=26, 474-495=22, 497-550=54 (total 303) | verifier |
| 5 | verified | code/ftc/RefLemma.v lines 85-86 read 'Using the results from these files, we prove our main lemma in several steps (and versions).' | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Children and statements match the code verbatim (declarations at 238,289,352,389,423,447,474,497); the parent proof cites exactly ref_calc2..8 at 556,558,560,562,564,566,568 and ref_calc1 at 576, so the 8 children are exactly the lemmas the glue uses; ref_calc2 cites ref_calc1 at 309 (only child-to-child dependency, depth 2 correct); every site ends in Qed (no sorry/admit in 238-594); shape numbers check out: parent 594-553+1=42, children 47+62+36+33+23+26+22+54=303, direct_lemmas=8, depth=2; closing methods match (str_Mengolli_Sum_gen/str_Sumx_Sum_Sum/Sum2_comm_scal'/Sumx_minus_Sumx/Sum2_wd/triangle_SumxIR/triangle_Sum2IR/mult_resp_leEq_both with contF' e He). Minor non-blocking note: intent/consequences prose says ref_calc1 telescopes to 'P_i - P_{i-1}' while the code is P (S i) - P i; the diagram and child note already state 'P (S i) - P i', and the 1-based reading describes the same differences, so I do not object. | reviewer-correctness |
| generality | accept | Move is stated beyond the example (a bound whose two sides differ by algebraic normalisations, then triangle inequalities, then one analytic bound); 'when not to use' is specific and honest (inline when steps aren't worth naming; non-monotone hypotheses break a single leEq_transitive chain; one long rewrite is fragile to term-index mismatches); consequences name real failure modes (weakest-link; head must match the tail). Good-leaf characterisation present: flat 8 direct lemmas, depth 2, 22-62 lines each, self-contained (six close from library/triangle lemmas, only ref_calc2 uses ref_calc1), with the modulus-of-continuity isolated to ref_calc8 so the first seven links are pure algebra and checkable in isolation. Verified header comment 'several steps' (lines 85-86) and second_refinement_lemma reuse (lines 656,659) in local copy. | reviewer-generality |
| provenance-licence | accept | Commit f678996112929e1674e20b75fb9bd728ded35e55 is consistent across source.json, sources/corn/SOURCE.md, entry.json source.commit and every permalink; all permalinks use the same full commit hash and the correct repo/path (rocq-community/corn, ftc/RefLemma.v). Licence GPL-2.0 is recorded identically in entry.json, README and SOURCE.md, and the upstream LICENSE at the pinned commit is GNU GPL v2 (verified: fetched LICENSE is byte-identical sha256 ab15fd52... to sources/corn/upstream-LICENSE, whose header is 'GNU GENERAL PUBLIC LICENSE, Version 2, June 1991'). Copied code file is byte-identical at the commit (check_provenance pass; local sha256 293b56ac... matches entry.json files[0].sha256 and 37384 bytes). Everything traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/rocq-community/corn at commit `f678996112929e1674e20b75fb9bd728ded35e55`, under `GPL-2.0-or-later`; see the [source note](../../sources/corn/SOURCE.md) for the licence text and attribution.
