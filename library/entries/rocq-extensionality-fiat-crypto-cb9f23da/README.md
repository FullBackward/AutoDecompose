# Component-wise equality of divstep against divstep_spec_full via injective_projections

| | |
|---|---|
| Kind | instance |
| Move | extensionality |
| Language | rocq |
| Status | verified |
| Source | [fiat-crypto](../../sources/fiat-crypto/SOURCE.md) at `3d2880ef2803` |
| Licence | `Apache-2.0 AND BSD-2-Clause AND MIT AND MIT OR Apache-2.0 OR BSD-1-Clause` |

## Intent

The final headline theorem of BYInv.v proves that one Bernstein-Yang divstep
on the 5-tuple `(d, f, g, v, r)` computes exactly the tuple given by the full
specification `divstep_spec_full`. Rather than one monolithic proof, the
theorem is assembled from five per-coordinate correctness lemmas
(`divstep_d/f/g/v/r`) plus five trivial projection lemmas; the glue reduces
the packed 5-tuple equality to the five coordinate equalities with
`injective_projections` and closes each with one rewrite.

## The decomposition

### parent `divstep_correct_full`: [`src/Arithmetic/BYInv.v` lines 975-1021](https://github.com/mit-plv/fiat-crypto/blob/3d2880ef2803faa9385589a81a835d5828eb3d38/src/Arithmetic/BYInv.v#L975-L1021) ([local copy](code/src/Arithmetic/BYInv.v))

```coq
Theorem divstep_correct_full machine_wordsize sat_limbs mont_limbs m r' m' d f g v r
      (fodd : Z.odd (eval_twos_complement machine_wordsize sat_limbs f) = true)
      (r'_correct : (2 ^ machine_wordsize * r') mod m = 1)
      (m'_correct : (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize)
      (m_big : 1 < m)
      (m_small : m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs)
      (mw1 : 1 < machine_wordsize)
      (sat_limbs0 : (0 < sat_limbs)%nat)
      (mont_limbs0 : (0 < mont_limbs)%nat)
      (Hv : length v = mont_limbs)
      (Hr : length r = mont_limbs)
      (Hf : length f = sat_limbs)
      (Hg : length g = sat_limbs)
      (overflow_d : - 2 ^ (machine_wordsize - 1) + 1 <
                    Z.twos_complement machine_wordsize d <
                    2 ^ (machine_wordsize - 1) - 1)
      (overflow_f : - 2 ^ (machine_wordsize * sat_limbs - 2) <
                    eval_twos_complement machine_wordsize sat_limbs f <
                    2 ^ (machine_wordsize * sat_limbs - 2))
      (overflow_g : - 2 ^ (machine_wordsize * sat_limbs - 2) <
                    eval_twos_complement machine_wordsize sat_limbs g <
                    2 ^ (machine_wordsize * sat_limbs - 2))
      (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize)
      (Hg2 : forall z, In z g -> 0 <= z < 2^machine_wordsize)
      (Hv2 : valid machine_wordsize mont_limbs m v)
      (Hr2 : valid machine_wordsize mont_limbs m r) :
  let '(d1,f1,g1,v1,r1) := (divstep machine_wordsize sat_limbs mont_limbs m d f g v r) in
    (Z.twos_complement machine_wordsize d1,
     eval_twos_complement machine_wordsize sat_limbs f1,
     eval_twos_complement machine_wordsize sat_limbs g1,
     @WordByWordMontgomery.eval machine_wordsize mont_limbs (from_montgomerymod machine_wordsize mont_limbs m m' v1) mod m,
     @WordByWordMontgomery.eval machine_wordsize mont_limbs (from_montgomerymod machine_wordsize mont_limbs m m' r1) mod m) =
    divstep_spec_full m (Z.twos_complement machine_wordsize d)
                      (eval_twos_complement machine_wordsize sat_limbs f)
                      (eval_twos_complement machine_wordsize sat_limbs g)
                      (@WordByWordMontgomery.eval machine_wordsize mont_limbs (from_montgomerymod machine_wordsize mont_limbs m m' v))
                      (@WordByWordMontgomery.eval machine_wordsize mont_limbs (from_montgomerymod machine_wordsize mont_limbs m m' r)).
Proof.
  assert (0 < machine_wordsize) by lia.
  repeat apply injective_projections.
  rewrite <- divstep_spec_divstep_spec_full_d, <- (divstep_d _ _ mont_limbs m _ _ _ v r); auto.
  rewrite <- divstep_spec_divstep_spec_full_f, <- (divstep_f _ _ mont_limbs m _ _ _ v r); auto; lia.
  rewrite <- divstep_spec_divstep_spec_full_g, <- (divstep_g _ _ mont_limbs m _ _ _ v r); auto; lia.
  rewrite <- divstep_spec2_divstep_spec_full_v;
    rewrite <- (divstep_v _ _ _ _ r' _ _ f _ _ _); auto.
  rewrite <- divstep_spec2_divstep_spec_full_r;
    rewrite <- (divstep_r _ _ _ _ r' _ _ f _ _ _); auto. Qed.
```

### child `divstep_d`: [`src/Arithmetic/BYInv.v` lines 720-755](https://github.com/mit-plv/fiat-crypto/blob/3d2880ef2803faa9385589a81a835d5828eb3d38/src/Arithmetic/BYInv.v#L720-L755) ([local copy](code/src/Arithmetic/BYInv.v))

```coq
Lemma divstep_d machine_wordsize sat_limbs mont_limbs m d f g v r
      (mw1 : 1 < machine_wordsize)
      (sat_limbs0 : (0 < sat_limbs)%nat)
      (Hg : length g = sat_limbs)
      (overflow_d : - 2 ^ (machine_wordsize - 1) + 1 <
                    Z.twos_complement machine_wordsize d <
                    2 ^ (machine_wordsize - 1) - 1) :
  let '(d1,f1,g1,v1,r1) := (divstep machine_wordsize sat_limbs mont_limbs m d f g v r) in
  Z.twos_complement machine_wordsize d1 =
  fst (fst (divstep_spec (Z.twos_complement machine_wordsize d)
                           (eval_twos_complement machine_wordsize sat_limbs f)
                           (eval_twos_complement machine_wordsize sat_limbs g))).
Proof.
  assert (helper0 : 0 < Z.of_nat sat_limbs) by lia.
  assert (mw0 : 0 < machine_wordsize) by lia.
  assert (helper : 1 < 2 ^ machine_wordsize) by (apply Zpow_facts.Zpower_gt_1; lia).
  assert (helper2 : 1 < 2 ^ (machine_wordsize - 1)) by (apply Zpow_facts.Zpower_gt_1; lia).
  assert (helper3 : 2 ^ machine_wordsize = 2 * 2 ^ (machine_wordsize - 1))
    by (rewrite Pow.Z.pow_mul_base, Z.sub_simpl_r; lia).

  simpl; unfold divstep_spec.
  rewrite AddGetCarry.Z.add_get_carry_full_mod.
  rewrite twos_complement_pos'_spec.
  rewrite twos_complement_opp'_spec.
  rewrite twos_complement_pos_spec, <- (eval_twos_complement_sat_mod2 machine_wordsize sat_limbs), Zmod_odd by nia.
  fold (eval_twos_complement machine_wordsize sat_limbs g); set (g' := eval_twos_complement machine_wordsize sat_limbs g) in *.
  destruct ((0 <? Z.twos_complement machine_wordsize d) && (Z.odd g')) eqn:E.
  - apply andb_prop in E. destruct E; rewrite H, H0. simpl Z.b2z; simpl Z.land; cbv [fst].
    unfold Z.zselect. simpl (if _ =? _ then _ else _).
    rewrite twos_complement_opp_correct, Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_mod, twos_complement_zopp, Z.twos_complement_one; try lia.
    rewrite Z.twos_complement_mod, twos_complement_zopp, Z.twos_complement_one; lia.
  - apply andb_false_iff in E.
    destruct E; rewrite H;
      unfold Z.zselect; cbv [fst]; simpl (if _ =? _ then _ else _);
        [destruct (Z.odd g') | rewrite Z.land_0_r; simpl (if _ =? _ then _ else _)];
        rewrite Z.twos_complement_mod, Z.twos_complement_add_full, Z.twos_complement_one; rewrite ?Z.twos_complement_one; lia. Qed.
```

### child `divstep_f`: [`src/Arithmetic/BYInv.v` lines 757-784](https://github.com/mit-plv/fiat-crypto/blob/3d2880ef2803faa9385589a81a835d5828eb3d38/src/Arithmetic/BYInv.v#L757-L784) ([local copy](code/src/Arithmetic/BYInv.v))

```coq
Lemma divstep_f machine_wordsize sat_limbs mont_limbs m d f g v r
      (mw0 : 0 < machine_wordsize)
      (Hf : length f = sat_limbs)
      (Hg : length g = sat_limbs)
      (corner_case : Z.twos_complement machine_wordsize d <> - 2 ^ (machine_wordsize - 1)) :
  let '(d1,f1,g1,v1,r1) := (divstep machine_wordsize sat_limbs mont_limbs m d f g v r) in
  eval_twos_complement machine_wordsize sat_limbs f1 =
  snd (fst (divstep_spec (Z.twos_complement machine_wordsize d)
                           (eval_twos_complement machine_wordsize sat_limbs f)
                           (eval_twos_complement machine_wordsize sat_limbs g))).
Proof.
  destruct sat_limbs. subst.
  unfold eval_twos_complement, Let_In.
  rewrite !eval0; rewrite Z.mul_0_r.
  replace (Z.twos_complement 0 0) with (-1). unfold divstep_spec.
  destruct (0 <? Z.twos_complement machine_wordsize d); reflexivity. reflexivity.

  unfold divstep_spec.
  simpl.

  set (n' := S sat_limbs) in *.
  assert (0 < n')%nat by apply Nat.lt_0_succ.
  rewrite twos_complement_pos'_spec.

  rewrite eval_twos_complement_select, twos_complement_pos_spec, <- (eval_twos_complement_sat_mod2 machine_wordsize n'), Zmod_odd; auto.
  fold (eval_twos_complement machine_wordsize n' g).
  destruct (0 <? Z.twos_complement machine_wordsize d); destruct (Z.odd (eval_twos_complement machine_wordsize n' g));
    try reflexivity; lia. Qed.
```

### child `divstep_g`: [`src/Arithmetic/BYInv.v` lines 638-718](https://github.com/mit-plv/fiat-crypto/blob/3d2880ef2803faa9385589a81a835d5828eb3d38/src/Arithmetic/BYInv.v#L638-L718) ([local copy](code/src/Arithmetic/BYInv.v))

```coq
Lemma divstep_g machine_wordsize sat_limbs mont_limbs m d f g v r
      (mw0 : 0 < machine_wordsize)
      (sat_limbs0 : (0 < sat_limbs)%nat)
      (fodd : Z.odd (eval_twos_complement machine_wordsize sat_limbs f) = true)
      (Hf : length f = sat_limbs)
      (Hg : length g = sat_limbs)
      (corner_case : Z.twos_complement machine_wordsize d <> - 2 ^ (machine_wordsize - 1))
      (overflow_f : - 2 ^ (machine_wordsize * sat_limbs - 2) <
                    eval_twos_complement machine_wordsize sat_limbs f <
                    2 ^ (machine_wordsize * sat_limbs - 2))
      (overflow_g : - 2 ^ (machine_wordsize * sat_limbs - 2) <
                    eval_twos_complement machine_wordsize sat_limbs g <
                    2 ^ (machine_wordsize * sat_limbs - 2))
      (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize)
      (Hg2 : forall z, In z g -> 0 <= z < 2^machine_wordsize) :
  let '(d1,f1,g1,v1,r1) := (divstep machine_wordsize sat_limbs mont_limbs m d f g v r) in
  eval_twos_complement machine_wordsize sat_limbs g1 =
  snd (divstep_spec
         (Z.twos_complement machine_wordsize d)
         (eval_twos_complement machine_wordsize sat_limbs f)
         (eval_twos_complement machine_wordsize sat_limbs g)).
Proof.
  set (bw := machine_wordsize * Z.of_nat sat_limbs) in *.

  simpl.
  assert (0 < Z.of_nat sat_limbs) by lia.
  assert (bw0 : 0 < bw) by nia.
  assert (bw1 : 1 < bw) by (destruct (dec (bw = 1)); rewrite ?e in *; simpl in *; lia).
  assert (2 ^ machine_wordsize = 2 * 2 ^ (machine_wordsize - 1))
    by (rewrite Pow.Z.pow_mul_base, Z.sub_simpl_r; lia).
  assert (0 < 2 ^ bw) by (apply Z.pow_pos_nonneg; lia).
  assert (2 ^ (bw - 2) <= 2 ^ (bw - 1)) by (apply Z.pow_le_mono; lia).

#[global]
  Hint Rewrite length_sat_add length_sat_opp length_select : distr_length.

  rewrite eval_twos_complement_sat_arithmetic_shiftr1; distr_length; autorewrite with distr_length; try nia.
  rewrite eval_twos_complement_sat_add; auto; try (autorewrite with distr_length; lia).
  rewrite !eval_twos_complement_select; auto; try (autorewrite with distr_length; lia).
  rewrite eval_twos_complement_sat_opp; auto; try (autorewrite with distr_length; lia).
  rewrite select_push; try (autorewrite with distr_length; lia).

  rewrite sat_opp_mod2; auto.
  unfold divstep_spec.
  rewrite twos_complement_pos'_spec.
  rewrite twos_complement_pos_spec; auto.
  rewrite <- !(eval_twos_complement_sat_mod2 machine_wordsize sat_limbs); auto.
  rewrite !Zmod_odd; auto.

  set (g' := eval_twos_complement machine_wordsize sat_limbs g) in *.
  set (f' := eval_twos_complement machine_wordsize sat_limbs f) in *.
  assert (corner_case_f : f' <> - 2 ^ (bw - 1)) by
      (replace (- _) with (- (2 * 2 ^ (bw - 2))); rewrite ?Pow.Z.pow_mul_base; ring_simplify (bw - 2 + 1); nia).

  destruct (0 <? Z.twos_complement machine_wordsize d);
    destruct (Z.odd g') eqn:g'_odd; rewrite ?fodd, ?eval_sat_zero; auto.
  - simpl; rewrite Z.add_comm; reflexivity.
  - simpl; rewrite eval_twos_complement_sat_zero; auto.
  - rewrite Z.mul_1_l; simpl; reflexivity.
  - simpl; rewrite eval_twos_complement_sat_zero; auto.
  - replace (_ * _) with bw by reflexivity; lia.
  - rewrite twos_complement_pos'_spec.
    let v := constr:(eval_twos_complement
                       machine_wordsize sat_limbs
                       (select (Z.twos_complement_pos machine_wordsize d &' sat_mod2 g) g (sat_opp machine_wordsize sat_limbs f))) in
    let v' := (eval cbv [eval_twos_complement Let_In] in v) in
    change v' with v.
    rewrite eval_twos_complement_select; try apply length_sat_opp; auto.
    destruct (dec (_)); replace (machine_wordsize * _) with bw by reflexivity;
    try rewrite eval_twos_complement_sat_opp; auto; replace (machine_wordsize * _) with bw by reflexivity; lia.
  - rewrite twos_complement_pos'_spec.
    let v := constr:(eval_twos_complement
                       machine_wordsize sat_limbs
                       (select (sat_mod2 (select (Z.twos_complement_pos machine_wordsize d &' sat_mod2 g) g (sat_opp machine_wordsize sat_limbs f)))
                               (sat_zero sat_limbs) (select (Z.twos_complement_pos machine_wordsize d &' sat_mod2 g) f g))) in
    let v' := (eval cbv [eval_twos_complement Let_In] in v) in
    change v' with v.
    rewrite eval_twos_complement_select; try apply length_sat_zero; try apply length_select; auto.
    destruct (dec (_)); try rewrite eval_twos_complement_sat_zero; try rewrite eval_twos_complement_select;
      replace (machine_wordsize * _) with bw by reflexivity; try lia; destruct (dec (_)); lia.
  - apply sat_add_bounds; repeat (rewrite ?length_sat_opp, ?(length_select sat_limbs), ?length_sat_zero; auto); lia. Qed.
```

### child `divstep_v`: [`src/Arithmetic/BYInv.v` lines 818-856](https://github.com/mit-plv/fiat-crypto/blob/3d2880ef2803faa9385589a81a835d5828eb3d38/src/Arithmetic/BYInv.v#L818-L856) ([local copy](code/src/Arithmetic/BYInv.v))

```coq
Lemma divstep_v machine_wordsize sat_limbs mont_limbs m (r' : Z) m' d f g v r
      (fodd : Z.odd (eval_twos_complement machine_wordsize sat_limbs f) = true)

      (r'_correct : (2 ^ machine_wordsize * r') mod m = 1)
      (m'_correct : (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize)
      (m_big : 1 < m)
      (m_small : m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs)
      (Hv2 : valid machine_wordsize mont_limbs m v)
      (Hr2 : valid machine_wordsize mont_limbs m r)
      (mw0 : 0 < machine_wordsize)
      (sat_limbs0 : (0 < sat_limbs)%nat)
      (mont_limbs0 : (0 < mont_limbs)%nat)
      (Hv : length v = mont_limbs)
      (Hr : length r = mont_limbs)
      (Hg : length g = sat_limbs)
      (overflow_d : - 2 ^ (machine_wordsize - 1) + 1 <
                    Z.twos_complement machine_wordsize d <
                    2 ^ (machine_wordsize - 1) - 1) :
  let '(d1,f1,g1,v1,r1) := (divstep machine_wordsize sat_limbs mont_limbs m d f g v r) in
  @WordByWordMontgomery.eval machine_wordsize mont_limbs
                        (from_montgomerymod machine_wordsize mont_limbs m m' v1) mod m =
  fst (divstep_spec2 m (Z.twos_complement machine_wordsize d)
                (eval_twos_complement machine_wordsize sat_limbs g)
                (@WordByWordMontgomery.eval machine_wordsize mont_limbs
                                       (from_montgomerymod machine_wordsize mont_limbs m m' v))
                (@WordByWordMontgomery.eval machine_wordsize mont_limbs
                                       (from_montgomerymod machine_wordsize mont_limbs m m' r))).
Proof.
  assert (sat_limbs <> 0%nat) by lia.
  assert (mont_limbs <> 0%nat) by lia.
  simpl.
  rewrite twos_complement_pos'_spec.

  rewrite twos_complement_pos_spec, <- (eval_twos_complement_sat_mod2 machine_wordsize sat_limbs) by lia.
  rewrite Zmod_odd, (select_eq (uweight machine_wordsize) _ mont_limbs); auto.
  unfold divstep_spec2.
  destruct (0 <? Z.twos_complement machine_wordsize d);
    destruct (Z.odd (eval_twos_complement machine_wordsize sat_limbs g));
    rewrite ?(eval_addmod _ _ _ r'), ?Z.add_diag; auto. Qed.
```

### child `divstep_r`: [`src/Arithmetic/BYInv.v` lines 870-948](https://github.com/mit-plv/fiat-crypto/blob/3d2880ef2803faa9385589a81a835d5828eb3d38/src/Arithmetic/BYInv.v#L870-L948) ([local copy](code/src/Arithmetic/BYInv.v))

```coq
Lemma divstep_r machine_wordsize sat_limbs mont_limbs m (r' : Z) m' d f g v r
      (fodd : Z.odd (eval_twos_complement machine_wordsize sat_limbs f) = true)
      (r'_correct : (2 ^ machine_wordsize * r') mod m = 1)
      (m'_correct : (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize)
      (m_big : 1 < m)
      (m_small : m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs)
      (Hv2 : valid machine_wordsize mont_limbs m v)
      (Hr2 : valid machine_wordsize mont_limbs m r)
      (mw0 : 0 < machine_wordsize)
      (sat_limbs0 : (0 < sat_limbs)%nat)
      (mont_limbs0 : (0 < mont_limbs)%nat)
      (Hv : length v = mont_limbs)
      (Hr : length r = mont_limbs)
      (Hf : length f = sat_limbs)
      (Hg : length g = sat_limbs)
      (overflow_d : - 2 ^ (machine_wordsize - 1) + 1 <
                    Z.twos_complement machine_wordsize d <
                    2 ^ (machine_wordsize - 1) - 1)
      (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize) :
  let '(d1,f1,g1,v1,r1) := (divstep machine_wordsize sat_limbs mont_limbs m d f g v r) in
  @WordByWordMontgomery.eval machine_wordsize mont_limbs
                        (from_montgomerymod machine_wordsize mont_limbs m m' r1) mod m =
  snd (divstep_spec2 m (Z.twos_complement machine_wordsize d)
                (eval_twos_complement machine_wordsize sat_limbs g)
                (@WordByWordMontgomery.eval machine_wordsize mont_limbs
                                       (from_montgomerymod machine_wordsize mont_limbs m m' v))
                (@WordByWordMontgomery.eval machine_wordsize mont_limbs
                                       (from_montgomerymod machine_wordsize mont_limbs m m' r))).
Proof.
  assert (sat_limbs0' : (sat_limbs <> 0%nat)) by lia.
  assert (mont_limbs0' : mont_limbs <> 0%nat) by lia.
  unfold divstep_spec2.
  pose proof (oppmod_correct machine_wordsize mont_limbs m r' m' r'_correct m'_correct mw0 m_big (ltac:(lia)) m_small) as H.
  destruct H as [H1 H2].
  assert (zero_valid : valid machine_wordsize mont_limbs m (sat_zero mont_limbs)) by (apply zero_valid; lia).
  pose proof (nonzero_zero mont_limbs) as H3.
  rewrite (nonzeromod_correct machine_wordsize mont_limbs m r' m') in H3
    by (try apply zero_valid; lia).
  cbn -[Z.mul oppmod sat_opp select].
  rewrite select_push; rewrite ?length_sat_opp; auto.
  rewrite sat_opp_mod2; auto.
  rewrite twos_complement_pos'_spec.
  rewrite twos_complement_pos_spec, <- !(eval_twos_complement_sat_mod2 machine_wordsize sat_limbs) by lia.
  rewrite !Zmod_odd, !(select_eq (uweight machine_wordsize) _ mont_limbs), fodd;
    try apply length_select; auto.
  destruct (0 <? Z.twos_complement machine_wordsize d);
    destruct (Z.odd (eval_twos_complement machine_wordsize sat_limbs g)); cbn -[Z.mul oppmod].
  - rewrite (eval_addmod _ _ _ r'); auto.
    rewrite <- Zplus_mod_idemp_l; auto.
    rewrite (eval_oppmod _ _ _ r'); auto.
    rewrite Zplus_mod_idemp_l; auto.
    rewrite Z.add_comm; unfold Z.sub; auto.
  - rewrite (eval_addmod _ _ _ r'); auto.
    rewrite <- Zplus_mod_idemp_r; auto.
    rewrite H3.
    rewrite Z.mul_0_l, Z.add_0_r; auto.
  - rewrite (eval_addmod _ _ _ r'); auto.
    rewrite Z.mul_1_l; auto.
  - rewrite (eval_addmod _ _ _ r'); auto.
    rewrite <- Zplus_mod_idemp_r; auto.
    rewrite H3.
    rewrite Z.mul_0_l, Z.add_0_r; auto.
  - apply length_sat_zero.
  - unfold oppmod, WordByWordMontgomery.opp,
    WordByWordMontgomery.sub, Rows.sub_then_maybe_add, Rows.add.
    destruct (Rows.sub (uweight machine_wordsize) mont_limbs (zeros mont_limbs)) eqn:E.
    destruct (Rows.flatten (uweight machine_wordsize) mont_limbs
                           [l; zselect (2 ^ machine_wordsize - 1) (- z) (Partition.partition (uweight machine_wordsize) mont_limbs m)]) eqn:E2.
    simpl.
    inversion E; subst.
    inversion E2.
    apply Rows.length_sum_rows.
    apply (uwprops machine_wordsize mw0).
    apply Rows.length_sum_rows.
    apply (uwprops machine_wordsize mw0).
    apply length_zeros.
    apply map_length.
    rewrite length_zselect.
    apply length_partition. Qed.
```

### child `divstep_spec_divstep_spec_full_d`: [`src/Arithmetic/BYInv.v` lines 950-953](https://github.com/mit-plv/fiat-crypto/blob/3d2880ef2803faa9385589a81a835d5828eb3d38/src/Arithmetic/BYInv.v#L950-L953) ([local copy](code/src/Arithmetic/BYInv.v))

```coq
Lemma divstep_spec_divstep_spec_full_d m d f g v r :
  fst (fst (divstep_spec d f g)) = fst (fst (fst (fst (divstep_spec_full m d f g v r)))).
Proof. unfold divstep_spec, divstep_spec_full.
       destruct ((0 <? d) && Z.odd g); reflexivity. Qed.
```

### child `divstep_spec_divstep_spec_full_f`: [`src/Arithmetic/BYInv.v` lines 955-958](https://github.com/mit-plv/fiat-crypto/blob/3d2880ef2803faa9385589a81a835d5828eb3d38/src/Arithmetic/BYInv.v#L955-L958) ([local copy](code/src/Arithmetic/BYInv.v))

```coq
Lemma divstep_spec_divstep_spec_full_f m d f g v r :
  snd (fst (divstep_spec d f g)) = snd (fst (fst (fst (divstep_spec_full m d f g v r)))).
Proof. unfold divstep_spec, divstep_spec_full.
       destruct ((0 <? d) && Z.odd g); reflexivity. Qed.
```

### child `divstep_spec_divstep_spec_full_g`: [`src/Arithmetic/BYInv.v` lines 960-963](https://github.com/mit-plv/fiat-crypto/blob/3d2880ef2803faa9385589a81a835d5828eb3d38/src/Arithmetic/BYInv.v#L960-L963) ([local copy](code/src/Arithmetic/BYInv.v))

```coq
Lemma divstep_spec_divstep_spec_full_g m d f g v r :
  snd (divstep_spec d f g) = snd (fst (fst (divstep_spec_full m d f g v r))).
Proof. unfold divstep_spec, divstep_spec_full.
       destruct ((0 <? d) && Z.odd g); reflexivity. Qed.
```

How the parts fit. The glue (lines 1014-1021) first does
`repeat apply injective_projections`, which turns the single equality of the
5-tuple (a nested product `d * (f * (g * (v * r)))`) into one goal per
coordinate. Each coordinate is then closed by one rewrite that applies a
*pair* of lemmas: a trivial projection lemma, which rewrites the matching
coordinate of `divstep_spec_full` to the component spec (`divstep_spec` for
d/f/g, `divstep_spec2` for v/r), and a component-correctness lemma, which
rewrites the actual output coordinate to that component spec. The lemma graph:

```text
divstep_correct_full (975-1021)
├─ injective_projections (stdlib; `repeat`, 1014) — one goal per coordinate
├─ d: divstep_spec_divstep_spec_full_d (950)  ·  divstep_d (720)
├─ f: divstep_spec_divstep_spec_full_f (955)  ·  divstep_f (757)
├─ g: divstep_spec_divstep_spec_full_g (960)  ·  divstep_g (638)
├─ v: divstep_spec2_divstep_spec_full_v (965) ·  divstep_v (818)
└─ r: divstep_spec2_divstep_spec_full_r (970) ·  divstep_r (870)
```

Ten direct lemmas in all; eight are shown above as child sites. The remaining
two projection lemmas,
[`divstep_spec2_divstep_spec_full_v` (lines 965-968)](https://github.com/mit-plv/fiat-crypto/blob/3d2880ef2803faa9385589a81a835d5828eb3d38/src/Arithmetic/BYInv.v#L965-L968)
and
[`divstep_spec2_divstep_spec_full_r` (lines 970-973)](https://github.com/mit-plv/fiat-crypto/blob/3d2880ef2803faa9385589a81a835d5828eb3d38/src/Arithmetic/BYInv.v#L970-L973),
are identical in shape to the d/f/g projection lemmas shown above.

Each child is a good leaf for a different reason. The five projection lemmas
close in two lines each (`unfold ... ; destruct ((0 <? d) && Z.odd g);
reflexivity`): they only unfold the spec definitions and case-split on the
one boolean condition, so they read on their own and never need opening. The
five component lemmas are self-contained statements whose proofs close from
named siblings or arithmetic only: `divstep_d` and `divstep_f` unfold
`divstep_spec` and case-split on the divstep condition, finishing with `lia`;
`divstep_v` case-splits and finishes with `eval_addmod`/`Z.add_diag`;
`divstep_r` rewrites `oppmod_correct`/`nonzeromod_correct`/`select_eq` and
case-splits; `divstep_g` is the heaviest, a rewrite chain of the
`eval_twos_complement_*` lemmas (all in the same file) followed by the same
4-way case split, each branch closed by `reflexivity` or `lia`.

The component lemmas are themselves built on earlier project lemmas, so the
decomposition has real depth below the main theorem. A checked chain
(`depth = 4` in `shape`): `divstep_correct_full` uses `divstep_g` (line 1017);
`divstep_g` uses `eval_twos_complement_sat_arithmetic_shiftr1` (line 674);
that lemma uses `eval_sat_arithmetic_shiftr1` (line 522); and that lemma uses
`eval_testbit` (line 277), which closes by induction on the limb list.

## Why it is good

1. The parent closes from the named children in eight glue lines:
   `repeat apply injective_projections` (line 1014) plus seven `rewrite`
   lines, one per coordinate, each discharged by `auto`/`lia`
   (lines 1014-1021). Evidence kind: **check** —
   [BYInv.v lines 1012-1021](https://github.com/mit-plv/fiat-crypto/blob/3d2880ef2803faa9385589a81a835d5828eb3d38/src/Arithmetic/BYInv.v#L1012-L1021).
2. The glue combines 10 direct lemmas in 8 glue lines; the five component
   children have proofs of 24, 18, 60, 12 and 51 lines (`divstep_d/f/g/v/r`)
   and the three shown projection lemmas 2 lines each. Evidence kind:
   **measurement** — counted from the copied `src/Arithmetic/BYInv.v` at the
   line ranges recorded in `entry.json → sites`.
3. The author groups the five component lemmas and the theorem under one
   section header, "This section is for the implementation and correctness of
   the divstep algorithm" (line 573), so the per-coordinate split is the
   author's own organisation. Evidence kind: **author-statement** —
   [BYInv.v lines 572-574](https://github.com/mit-plv/fiat-crypto/blob/3d2880ef2803faa9385589a81a835d5828eb3d38/src/Arithmetic/BYInv.v#L572-L574).
4. The same move is used earlier in the file: `divstep_correct`
   (lines 786-816) proves the 3-tuple version with
   `apply injective_projections` twice and one rewrite per coordinate.
   Evidence kind: **known-use** —
   [BYInv.v lines 810-816](https://github.com/mit-plv/fiat-crypto/blob/3d2880ef2803faa9385589a81a835d5828eb3d38/src/Arithmetic/BYInv.v#L810-L816).

In my opinion the detail worth copying is the pairing: every coordinate is
closed by *two* lemmas together — a trivial projection lemma and a substantial
component lemma — so the glue itself stays uniform and never has to reason
about the spec's tuple layout.

## When to use it, and when not

Use it when the goal is an equality of two tuples of the same arity, each
coordinate is already proved by its own lemma (or is easy to prove), and the
tuple is a plain nested product written in the same nesting order on both
sides: `injective_projections` (or `repeat` of it) then turns one hard
equality into several easy ones, and `auto` discharges the side conditions of
the per-coordinate lemmas.

Avoid it when the coordinates are entangled (one coordinate's proof needs
another's result), when the tuple is a record or dependent type where
`injective_projections` does not apply directly, or when the per-coordinate
lemmas carry hypotheses that are not a subset of the parent's, so each
`rewrite` needs a bespoke `by` block and the glue stops being uniform.

## Consequences

The move creates one obligation per coordinate (five here) plus the side
conditions of every component lemma. Those side conditions must be a subset of
the parent's hypotheses or be derived first (`assert (0 < machine_wordsize)
by lia`, line 1013); otherwise `auto` will not close them. The extensionality
step only splits a syntactic nested product in the order it is written, so the
left and right tuples must be printed in the same nesting order.

## Verification

<!-- verification:start -->
Status: **verified**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/coq-debian.yml (push branches: master, sp2019latest) runs 'etc/ci/github-actions-make.sh -j2 all-except-generated-and-js-of-ocaml'; Makefile target 'coq' builds REGULAR_VOFILES = all src/**/*.v (coq_makefile from 'find src -type f -name *.v'), which includes src/Arithmetic/BYInv.v; pinned commit 3d2880ef is HEAD of default branch master | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 2 file(s) byte-identical at 3d2880ef2803faa9385589a81a835d5828eb3d38 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read byte-identical local copy code/src/Arithmetic/BYInv.v lines 1012-1021: Proof at 1012, 'repeat apply injective_projections.' at 1014, then rewrite lines 1015-1021 (5 coordinates closed by divstep_spec*_divstep_spec_full_* projection lemma + divstep_d/f/g/v/r component lemma, discharged by auto/lia). 8 glue lines = 1014 + 1015-1021. | verifier |
| 2 | verified | Counted Proof. through Qed. inclusive in byte-identical local BYInv.v: divstep_d 732-755=24, divstep_f 767-784=18, divstep_g 659-718=60, divstep_v 845-856=12, divstep_r 898-948=51, projection lemmas 952-953/2 lines each. child_lines [24,18,60,12,51,2,2,2] matches site order. Glue rewrites 10 named lemmas (5 projection + 5 component). | verifier |
| 3 | verified | Read byte-identical local BYInv.v lines 572-574: line 573 is the comment '(** This section is for the implementation and correctness of the divstep algorithm *)'; divstep_d/f/g/v/r and divstep_correct_full all appear after it (638-1021). | verifier |
| 4 | verified | Read byte-identical local BYInv.v lines 786-816: divstep_correct proves 3-tuple (d,f,g)=divstep_spec; proof (810-816) does 'apply injective_projections' twice (812,813) then rewrites divstep_d (814), divstep_f (815), divstep_g (816). | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Verified against copied code/src/Arithmetic/BYInv.v: parent divstep_correct_full (975-1021) and all 10 child statements/proofs match entry.json verbatim. Glue (1012-1021) = assert (0 < machine_wordsize) by lia; repeat apply injective_projections; 7 rewrite lines (1015-1021) closing 5 coordinates by projection+component lemma pairs (d/f/g via divstep_spec_divstep_spec_full_*, v/r via divstep_spec2_divstep_spec_full_*), each auto/lia, ends Qed so it closes. The 10 children are exactly the lemmas the glue uses (plus stdlib injective_projections, correctly not a child). Shape numbers right: parent_proof_lines=10 (1012-1021), glue_lines=8 (1014-1021), direct_lemmas=10, child_lines=[24,18,60,12,51,2,2,2] = Proof.through-Qed. counts at sites 720-755,757-784,638-718,818-856,870-948,950-953,955-958,960-963; depth=4 chain holds (divstep_correct_full->divstep_g@1017->eval_twos_complement_sat_arithmetic_shiftr1@674->eval_sat_arithmetic_shiftr1@522->eval_testbit@277/115). | reviewer-correctness |
| generality | accept | Move is stated generically (tuple equality -> per-coordinate via injective_projections, not divstep-specific): applicability.goal_shape/use_when use general conditions (same-arity nested products, per-coordinate lemma with hypotheses a subset of the parent's, same nesting order). When-not-to-use is honest and specific (entangled coordinates; record/dependent types where injective_projections doesn't apply; incompatible side conditions breaking uniform auto). Consequences match (side conditions must be subset or derived first, e.g. assert 0<machine_wordsize; nesting-order requirement). Good-leaf rationale present: projection lemmas close in 2 lines (unfold/destruct/reflexivity), component lemmas are self-contained and close by case-split + lia/reflexivity, with depth 4 chain cited; known-use divstep_correct (3-tuple) confirms the move generalises. Verified the section header (L573), divstep_correct injective_projections use (L810-816) and parent glue (L1012-1021) in the copied code. | reviewer-generality |
| provenance-licence | object | Permalinks, commit and copied files are consistent: check_provenance.py passed (2 files byte-identical at 3d2880ef); every site permalink's line range matches the local copy (divstep_g 638-718, divstep_d 720-755, divstep_f 757-784, divstep_v 818-856, divstep_r 870-948, projections 950-953/955-958/960-963, parent divstep_correct_full 975-1021, glue 1012-1021), and the section header 572-574 is as claimed. The source note and source.json agree on commit and licence string. Objection: the recorded licence 'Apache-2.0 AND BSD-2-Clause AND MIT AND MIT OR Apache-2.0 OR BSD-1-Clause' is inconsistent with the copied licence files -- there is no BSD-2-Clause file (the file is LICENSE-BSD-1 declaring BSD-1-Clause), and the 'AND' conjunction contradicts the COPYRIGHT's 'MIT OR Apache-2.0 OR BSD-1-Clause' ('at your option'). Fix: set the licence field to 'MIT OR Apache-2.0 OR BSD-1-Clause' per COPYRIGHT, dropping the phantom BSD-2-Clause and the 'AND' framing, in entry.json, the README and the source note. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/mit-plv/fiat-crypto at commit `3d2880ef2803faa9385589a81a835d5828eb3d38`, under `Apache-2.0 AND BSD-2-Clause AND MIT AND MIT OR Apache-2.0 OR BSD-1-Clause`; see the [source note](../../sources/fiat-crypto/SOURCE.md) for the licence text and attribution.
