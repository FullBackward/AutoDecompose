# Key invariant: the guided well-ordered subsets form a chain (Zermelo's well-ordering theorem)

| | |
|---|---|
| Kind | instance |
| Move | key-invariant |
| Language | rocq |
| Status | accepted |
| Source | [unimath](../../sources/unimath/SOURCE.md) at `7a4b03cce494` |
| Licence | `LicenseRef-UniMath` |
| Licence recorded | 2026-11-14T22:40:52Z |

## Intent

Zermelo's well-ordering theorem — from the axiom of choice, every set carries a
well-ordering — is proved by introducing one auxiliary notion, the *guided*
well-ordered subsets (those whose every element is the choice function's pick
for the initial segment below it), and one invariant about them: that the
guided subsets form a chain under inclusion. The main theorem then becomes a
95-line skeleton that applies this invariant plus a small set of
point-extension lemmas; the difficulty is concentrated in the invariant lemma
`guided_WOSubset_total`.

## The decomposition

### parent `ZermeloWellOrdering`: [`UniMath/OrderTheory/OrderedSets/WellOrderedSets.v` lines 1169-1263](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/OrderTheory/OrderedSets/WellOrderedSets.v#L1169-L1263) ([local copy](code/UniMath/OrderTheory/OrderedSets/WellOrderedSets.v))

```coq
Theorem ZermeloWellOrdering {X:hSet} : AxiomOfChoice ⇒ ∃ R : hrel X, isWellOrder R.
(* see http://www.math.illinois.edu/~dan/ShortProofs/WellOrdering.pdf *)
Proof.
  intros ac. assert (lem := AC_to_LEM ac).
  (* a choice function g allows us to single out the "guided" well ordered subsets of X *)
  apply (squash_to_hProp (AC_to_choice_fun X ac)); intro g.
  set (S := guidedFamily g).
  set (Schain := guided_WOSubset_total g lem).
  (* we form the union, W, of all the guided (well ordered) subsets of X *)
  set (W := ⋃ Schain).
  (* we show W itself is guided, so W is the biggest guided subset of X *)
  assert (Wguided : is_guided_WOSubset g W).
  { intros [w Ww]. apply (squash_to_hProp Ww); intros [C Cw].
    change (hProptoType (C w)) in Cw. simpl.
    assert (Q := pr2 C (w,,Cw)); simpl in Q.
    simple refine (Q @ _); clear Q.
    assert (CW := chain_union_le S Schain C : C ≼ W).
    use upto'_eqn.
    - exact CW.
    - reflexivity. }
  (* now we prove W is all of X *)
  assert (all : ∀ x, W x).
  { (* ... for if not, we can add a guided element and get a bigger guided subset *)
    apply (proof_by_contradiction lem); intro n.
    (* it's not constructive to get an element not in W: *)
    assert (Q := negforall_to_existsneg _ lem n); clear n.
    change hfalse.
    (* zn is the guided element not in W: *)
    set (znW := g (pr1 W,,Q) : ∑ z : X, ¬ pr1 W z).
    set (z := pr1 znW).
    set (nWz := pr2 znW : ¬ pr1 W z).
    (* make a larger well ordered subset of X by appending z to the top of W *)
    set (W' := WOSubset_plus_point W z nWz lem).
    assert (W'z := subtype_plus_has_point W z : W' z).
    set (j := TOSubset_plus_point_incl W z nWz : W ⊆ W').
    set (jmap := subtype_inc j).
    assert (W'guided : is_guided_WOSubset g W').
    { unfold is_guided_WOSubset.
      intros [x W'x].
      change (x = pr1 (g (@upto' X W' (x,, W'x))))%logic.
      apply (squash_to_hProp W'x); intros [Wx|ezx].
      - assert (x_guided := Wguided (x,,Wx)).
        change (x = pr1 (g (@upto' X W (x,, Wx))))%type in x_guided.
        simple refine (x_guided @ _); clear x_guided.
        use upto'_eqn.
        + (* show W ≼ W'; abstract later *)
          assert (WW' := TOSubset_plus_point_le W z nWz).
          induction WW' as [WW' comp].
          exists WW'.
          split.
          * exact comp.
          * intros w w' Ww W'w' le.
            simple refine (TOSubset_plus_point_initial W z nWz w w' Ww W'w' _).
            now apply (h1'' le).
        + reflexivity.
      - induction ezx.
        change (pr1 (g (pr1 W,, Q)) = pr1 (g (@upto' X W' (z,, W'x)))).
        assert (e : (pr1 W,, Q) = @upto' X W' (z,, W'x)).
        { apply subtypePath_prop. apply (invmap (hsubtype_univalence _ _)).
          intros y.
          change (W y ⇔ @upto X W' (z,, W'x) y).
          split.
          - intros Wy.
            (* show that the element y in W is less than z *)
            exists (j y Wy). unfold lt. intros le.
            induction (ishinh_irrel (ii2 (idpath z)) W'x).
            change empty in le.
            exact le.
          - intros [W'y yz].
            (* show that if y in W' is less than z, then it's in W *)
            apply (squash_to_hProp W'y); intros [Wy|ezy].
            + exact Wy.         (* it was in W, anyway *)
            + induction ezy.    (* y = x, and we know z<z *)
              apply fromempty. unfold lt,hneg in yz. apply yz.
              induction (proofirrelevance_hProp _ W'y W'x).
              exact (TOrefl W' (z,, W'y)). }
        now induction e. }
    assert (W'W := chain_union_le S Schain (W',,W'guided) : W' ≼ W).
    assert (K := pr2 (subtype_inc (pr1 W'W) (z,,W'z)) : W z).
    exact (nWz K).
    }
  clear Wguided.
  apply hinhpr.
  induction W as [W R'].
  change (∏ x : X, W x)%type in all.
  change (WellOrdering X).
  assert (e : X = carrier_subset W).
  { apply (invmap (hSet_univalence _ _)). apply invweq. apply weqpr1.
    intros x.
    simpl in all.
    apply iscontraprop1.
    - apply propproperty.
    - apply all. }
  induction e. exact R'.
Defined.
```

### child `AC_to_choice_fun`: [`UniMath/OrderTheory/OrderedSets/WellOrderedSets.v` lines 938-944](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/OrderTheory/OrderedSets/WellOrderedSets.v#L938-L944) ([local copy](code/UniMath/OrderTheory/OrderedSets/WellOrderedSets.v))

```coq
Lemma AC_to_choice_fun (X:hSet) : AxiomOfChoice ⇒ ∥ choice_fun X ∥.
Proof.
  intros ac.
  exact (squash_to_hProp (ac (proper_subtypes_set X)
                             (λ S, ∑ x, hProp_to_hSet (¬ (pr1 S x))) pr2)
                         hinhpr).
Defined.
```

### child `guided_WOSubset_total`: [`UniMath/OrderTheory/OrderedSets/WellOrderedSets.v` lines 976-1165](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/OrderTheory/OrderedSets/WellOrderedSets.v#L976-L1165) ([local copy](code/UniMath/OrderTheory/OrderedSets/WellOrderedSets.v))

```coq
Lemma guided_WOSubset_total {X:hSet} (g : choice_fun X) :
  LEM -> is_wosubset_chain (guidedFamily g).
Proof.
  intros lem [C gC] [D gD].
  set (W := max_common_initial C D).
  assert (Q := max_common_initial_is_common_initial C D).
  induction Q as [WC [WD [WCi [WDi WCD]]]]; fold W in WC, WD, WCi, WDi.
  assert (E : W ≡ C ∨ W ≡ D).
  { apply (proof_by_contradiction lem); intro h.
    assert (k := fromnegcoprod_prop h); clear h; induction k as [nc nd].
    assert (nCW : C ⊈ W).
    { use subtype_notEqual_containedIn.
      - exact WC.
      - now apply subtype_notEqual_from_negEqual. }
    assert (nDW : D ⊈ W).
    { use subtype_notEqual_containedIn.
      - exact WD.
      - now apply subtype_notEqual_from_negEqual. }
    assert (p : ∃ t : C, W ≡ upto t). { now use isInterval. }
    assert (q : ∃ t : D, W ≡ upto t). { now use isInterval. }
    change hfalse.
    apply (squash_to_hProp p); clear p; intros [c cE].
    apply (squash_to_hProp q); clear q; intros [d dE].
    assert (ce : W = upto c).
    { now apply (invmap (hsubtype_univalence _ _)). }
    assert (de : W = upto d).
    { now apply (invmap (hsubtype_univalence _ _)). }
    assert (cd := !ce @ de : upto c = upto d).
    assert (cd' : upto' c = upto' d).
    { now apply subtypePath_prop. }
    assert (p := gC c); simpl in p.
    assert (q := gD d); simpl in q.
    unfold choice_fun in g.
    assert (cd1 : pr1 c = pr1 d).
    { simple refine (p @ _ @ !q). now induction cd'. }
    clear cd'.
    set (W' := subtype_plus W (pr1 c)).
    assert (j := subtype_plus_incl W (pr1 c) : W ⊆ W').
    assert (W'c := subtype_plus_has_point W (pr1 c) : W' (pr1 c)).
    assert (W'd := transportf W' cd1 W'c : W' (pr1 d)).
    assert (ci : common_initial W' C D).
    { assert (W'C := subtype_plus_in WC (pr2 c));
        assert (W'D := subtype_plus_in WD (transportb (λ x : X, D x) cd1 (pr2 d)));
        fold W' in W'C, W'D.
      exists W'C, W'D.
      assert (cmax : ∏ (v : carrier W') (W'c : W' (pr1 c)),
                     subtype_inc W'C v ≤ subtype_inc W'C (pr1 c,,W'c)).
      { intros v W'c'. assert (e : c = subtype_inc W'C (pr1 c,, W'c')).
        { now apply subtypePath_prop. }
        induction e. clear W'c'. induction v as [v W'v]. apply (squash_to_hProp W'v); intros [Wv|k].
        - assert (L := pr1 (cE v) Wv). unfold upto,lt in L.
          assert (Q := @tot_nge_to_le (carrier_subset C) (TOSrel C) (TOtot C) _ _ (pr2 L)).
          now apply(h1'' Q).
        - use (TOeq_to_refl C). apply subtypePath_prop. simpl. exact (!k). }
      assert (cmax' : ∏ (w : carrier W) (W'c : W' (pr1 c)),
                     subtype_inc W'C (subtype_inc j w) < subtype_inc W'C (pr1 c,,W'c)).
      { intros w W'c'. assert (e : c = subtype_inc W'C (pr1 c,, W'c')).
        { now apply subtypePath_prop. }
        induction e. clear W'c'. induction w as [v Wv].
        assert (L := pr1 (cE v) Wv). unfold upto,lt in L.
        assert (Q := @tot_nge_to_le (carrier_subset C) (TOSrel C) (TOtot C) _ _ (pr2 L)).
        apply (@tot_nle_iff_gt (carrier_subset C) (TOSrel C) (pr122 C)).
        split.
        - now apply (h1'' Q).
        - intros e. assert (e' := maponpaths pr1 e); clear e. change (v = pr1 c)%type in e'.
          assert ( L' := pr2 L ). simpl in L'. apply L'; clear L'.
          exact (TOeq_to_refl_1 C c (v,, pr1 L) (!e')). }
      assert (dmax : ∏ (v : carrier W') (W'd : W' (pr1 d)),
                     subtype_inc W'D v ≤ subtype_inc W'D (pr1 d,,W'd)).
      { intros v W'd'. assert (e : d = subtype_inc W'D (pr1 d,, W'd')).
        { now apply subtypePath_prop. }
        induction e. clear W'd'. induction v as [v W'v]. apply (squash_to_hProp W'v); intros [Wv|k].
        - assert (L := pr1 (dE v) Wv). unfold upto,lt in L.
          assert (Q := @tot_nge_to_le (carrier_subset D) (TOSrel D) (TOtot D) _ _ (pr2 L)).
          now apply(h1'' Q).
        - use (TOeq_to_refl D). apply subtypePath_prop. simpl. exact (!k @ cd1). }
      assert (dmax' : ∏ (w : carrier W) (W'd : W' (pr1 d)),
                     subtype_inc W'D (subtype_inc j w) < subtype_inc W'D (pr1 d,,W'd)).
      { intros w W'd'. assert (e : d = subtype_inc W'D (pr1 d,, W'd')).
        { now apply subtypePath_prop. }
        induction e. clear W'd'. induction w as [v Wv].
        assert (L := pr1 (dE v) Wv). unfold upto,lt in L.
        assert (Q := @tot_nge_to_le (carrier_subset D) (TOSrel D) (TOtot D) _ _ (pr2 L)).
        apply (@tot_nle_iff_gt (carrier_subset D) (TOSrel D) (pr122 D)).
        split.
        - now apply (h1'' Q).
        - intros e. assert (e' := maponpaths pr1 e); clear e. change (v = pr1 d)%type in e'.
          assert ( L' := pr2 L ). simpl in L'. apply L'; clear L'.
          exact (TOeq_to_refl_1 D d (v,, pr1 L) (!e')). }
      split.
      { intros w' c' W'w' Cc' le.
        apply (squash_to_hProp W'w'); intros B. induction B as [Ww'|e].
        - apply hinhpr, ii1. apply (WCi w' c' Ww' Cc'). now apply (h1'' le).
        - induction e.
          induction (lem (pr1 c = c')) as [e|ne].
          + induction e. exact W'c.
          + use j. rewrite ce. exists Cc'. unfold lt. intro le'. apply ne.
            assert (e : c = (c',,Cc')).
            { apply (TOanti C).
              - exact le'.
              - now apply (h1'' le). }
            exact (maponpaths pr1 e). }
      split.
      { intros w' d' W'w' Dd' le.
        apply (squash_to_hProp W'w'); intros B. induction B as [Ww'|e].
        - apply hinhpr, ii1. apply (WDi w' d' Ww' Dd'). now apply (h1'' le).
        - induction e.
          induction (lem (pr1 d = d')) as [e|ne].
          + induction e. exact W'd.
          + use j. rewrite de. exists Dd'. unfold lt. intro le'. apply ne.
            assert (e : d = (d',,Dd')).
            { apply (TOanti D).
              - exact le'.
              - now apply (h1'' le). }
            exact (maponpaths pr1 e). }
      {
        intros [v W'v] [w W'w]. change (hProptoType (W' v)) in W'v; change (hProptoType (W' w)) in W'w.
        apply (squash_to_hProp W'v); intros [Wv|Ev].
        - apply (squash_to_hProp W'w); intros [Ww|Ew].
          + assert (Q := WCD (v,,Wv) (w,,Ww)).
            change (hProptoType (
                        (subtype_inc WC (v,, Wv) ≤ subtype_inc WC (w,, Ww))
                          ⇔
                          (subtype_inc WD (v,, Wv) ≤ subtype_inc WD (w,, Ww))
                      )%tosubset) in Q.
            assert (e : subtype_inc W'C (v,, W'v) = subtype_inc WC (v,, Wv)).
            { now apply subtypePath_prop. }
            induction e.
            assert (e : subtype_inc W'C (w,, W'w) = subtype_inc WC (w,, Ww)).
            { now apply subtypePath_prop. }
            induction e.
            assert (e : subtype_inc W'D (v,, W'v) = subtype_inc WD (v,, Wv)).
            { now apply subtypePath_prop. }
            induction e.
            assert (e : subtype_inc W'D (w,, W'w) = subtype_inc WD (w,, Ww)).
            { now apply subtypePath_prop. }
            induction e.
            exact Q.
          + induction Ew. apply logeq_if_both_true.
            * apply cmax.
            * induction (!cd1). apply dmax.
        - induction Ev. apply (squash_to_hProp W'w); intros [Ww|Ew].
          + apply logeq_if_both_false.
            * assert (Q := cmax' (w,,Ww) W'v). unfold lt in Q.
              assert (e : (w,, W'w) = (subtype_inc j (w,, Ww))).
              { now apply subtypePath_prop. }
              induction e.
              exact Q.
            * assert (Q := dmax' (w,,Ww) W'd). unfold lt in Q.
              assert (e : (w,, W'w) = (subtype_inc j (w,, Ww))).
              { now apply subtypePath_prop. }
              induction e.
              assert (e : subtype_inc W'D (pr1 c,, W'v) = subtype_inc W'D (pr1 d,, W'd)).
              { now apply subtypePath_prop. }
              induction e.
              exact Q.
          + induction Ew. apply logeq_if_both_true ; now use TOeq_to_refl_1. } }
    assert (K := max_common_initial_is_max C D W' ci); fold W in K.
    assert (Wc : W (pr1 c)).
    { exact (K (pr1 c) W'c). }
    assert (L := pr1 (cE (pr1 c)) Wc). induction L as [Cc Q]. change (neg (c ≤ pr1 c,, Cc)) in Q.
    apply Q; clear Q.
    simple refine (transportf (λ c', c ≤ c') _ (TOrefl C c)).
    now apply subtypePath_prop. }
  change (wosub_comparable C D). unfold wosub_comparable.
  apply (squash_to_hProp E); clear E; intros E. apply hinhpr.
  Set Printing Coercions.
  induction E as [eWC|eWD].
  - apply ii1.
    assert (e : W = C).
    { now apply hsubtype_univalence. }
    unfold W in *. clear W.
    induction (!e); clear e.
    use tpair.
    { exact WD. }
    split.
    { intros x y le. apply (pr1 (WCD x y)). now apply (h1'' le). }
    exact WDi.
  - apply ii2.
    assert (e : W = D).
    { now apply hsubtype_univalence. }
    unfold W in *. clear W.
    induction (!e); clear e.
    use tpair.
    { exact WC. }
    split.
    { intros x y le. apply (pr2 (WCD x y)). now apply (h1'' le). }
    exact WCi.
  Unset Printing Coercions.
Defined.
```

### child `chain_union_le`: [`UniMath/OrderTheory/OrderedSets/WellOrderedSets.v` lines 913-920](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/OrderTheory/OrderedSets/WellOrderedSets.v#L913-L920) ([local copy](code/UniMath/OrderTheory/OrderedSets/WellOrderedSets.v))

```coq
Lemma chain_union_le {X:hSet} {I:UU} (S : I -> WOSubset X) (Schain : is_wosubset_chain S) :
  ∀ i, S i ≼ ⋃ Schain.
Proof.
  intros i. exists (subtype_union_containedIn S i). split.
  * exact (pr2 (chain_union_tosub_le _ i)).
  * intros s t Ss Tt.
    exact (chain_union_rel_initial Schain i (s,,Ss) (t,,Tt)).
Defined.
```

### child `upto'_eqn`: [`UniMath/OrderTheory/OrderedSets/WellOrderedSets.v` lines 953-965](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/OrderTheory/OrderedSets/WellOrderedSets.v#L953-L965) ([local copy](code/UniMath/OrderTheory/OrderedSets/WellOrderedSets.v))

```coq
Lemma upto'_eqn {X:hSet} (g : choice_fun X) (C D : WOSubset X) (j : C ≼ D)
      (c : C) (d : D) :
  pr1 (subtype_inc (pr1 j) c) = pr1 d ->
  pr1 (g (upto' c)) = pr1 (g (upto' d)).
Proof.
  intros p. assert (e' : upto' c = upto' d).
  { apply subtypePath_prop. change (upto c = upto d).
    assert (q : subtype_inc (pr1 j) c = d).
    { now apply subtypePath_prop. }
    clear p. induction q.
    now apply upto_eqn. }
  now induction e'.
Defined.
```

### child `WOSubset_plus_point`: [`UniMath/OrderTheory/OrderedSets/WellOrderedSets.v` lines 461-466](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/OrderTheory/OrderedSets/WellOrderedSets.v#L461-L466) ([local copy](code/UniMath/OrderTheory/OrderedSets/WellOrderedSets.v))

```coq
Definition WOSubset_plus_point {X:hSet}
           (S:WOSubset X) (z:X) (nSz : ¬ S z) : LEM -> WOSubset X
  := λ lem, subtype_plus S z,,
            TOSrel (TOSubset_plus_point S z nSz),,
            TOtotal (TOSubset_plus_point S z nSz),,
            hasSmallest_WOSubset_plus_point S z nSz lem.
```

### child `TOSubset_plus_point_incl`: [`UniMath/OrderTheory/OrderedSets/WellOrderedSets.v` lines 307-311](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/OrderTheory/OrderedSets/WellOrderedSets.v#L307-L311) ([local copy](code/UniMath/OrderTheory/OrderedSets/WellOrderedSets.v))

```coq
Lemma TOSubset_plus_point_incl {X:hSet} (S:TOSubset X) (z:X) (nSz : ¬ S z) :
  S ⊆ TOSubset_plus_point S z nSz.
Proof.
  apply subtype_plus_incl.
Defined.
```

### child `TOSubset_plus_point_le`: [`UniMath/OrderTheory/OrderedSets/WellOrderedSets.v` lines 313-319](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/OrderTheory/OrderedSets/WellOrderedSets.v#L313-L319) ([local copy](code/UniMath/OrderTheory/OrderedSets/WellOrderedSets.v))

```coq
Lemma TOSubset_plus_point_le {X:hSet} (S:TOSubset X) (z:X) (nSz : ¬ S z) :
  S ≼ TOSubset_plus_point S z nSz.
Proof.
  use tpair.
  - apply TOSubset_plus_point_incl.
  - intros s t le. exact le.
Defined.
```

### child `TOSubset_plus_point_initial`: [`UniMath/OrderTheory/OrderedSets/WellOrderedSets.v` lines 321-329](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/OrderTheory/OrderedSets/WellOrderedSets.v#L321-L329) ([local copy](code/UniMath/OrderTheory/OrderedSets/WellOrderedSets.v))

```coq
Lemma TOSubset_plus_point_initial {X:hSet} (S:TOSubset X) (z:X) (nSz : ¬ S z) :
  sub_initial (TOSubset_plus_point_incl S z nSz).
Proof.
  intros s t Ss Tt le.
  apply (squash_to_hProp Tt); intros [St|ezt].
  - exact St.
  - induction ezt, (ishinh_irrel (ii2 (idpath z)) Tt); change empty in le.
    exact (fromempty le).
Defined.
```

How the parts fit. The glue is a skeleton laid over the key invariant
`guided_WOSubset_total`. Reading the parent's proof top to bottom:

```
AC_to_choice_fun          turn the axiom of choice into a choice function g
                          on proper subsets (line 1174)
        ↓
guided_WOSubset_total     THE INVARIANT: the guided well-ordered subsets
                          form a chain under ≼ (line 1176)
        ↓
set W := ⋃ Schain         the union of all guided subsets, well-ordered via
                          chain_union_WOSubset through the ⋃ notation (line 1178)
        ↓
assert Wguided             W is itself guided: chain_union_le gives each
                          C ≼ W, then upto'_eqn transfers guided-ness (1180-1188)
        ↓
assert all : ∀ x, W x      by contradiction: if not, the guided element z is
                          appended to W via WOSubset_plus_point, using
                          TOSubset_plus_point_incl/_le/_initial, and chain_union_le
                          again contradicts maximality (1190-1249)
        ↓
induction e. exact R'.     transport the well-ordering of W back to X through
                          hSet univalence + weqpr1 (1250-1262)
```

- `AC_to_choice_fun` (938) turns the axiom of choice into a `choice_fun`: for
  every proper subset it chooses an element outside it. Its proof is one
  `exact` instantiating the axiom at the hSet of proper subsets. It is the
  input to the guided construction, not part of the invariant argument itself.
- `guided_WOSubset_total` (976) is the key invariant: under LEM, the guided
  well-ordered subsets form a chain. Its proof is the central 190-line
  argument — two guided subsets C, D are compared through their maximal common
  initial segment W; `W ≡ C ∨ W ≡ D` is forced by contradiction (via
  `isInterval` and the guided-ness equations), and each disjunct assembles the
  comparison from the common-initial data.
- `chain_union_le` (913) says each member of a chain sits below the union. The
  glue applies it twice (lines 1185 and 1246): once to show W is guided, once
  to contradict maximality with `W' ≼ W`.
- `upto'_eqn` (953) says guided-ness transfers along `C ≼ D`: if the map
  carries c to d, then the choice of `upto' c` and `upto' d` agree. The glue
  applies it twice (lines 1186 and 1213) to keep the union W and the extended
  W' guided. It closes via the named sibling `upto_eqn` (line 602), so the
  chain `ZermeloWellOrdering → upto'_eqn → upto_eqn` has depth 2.
- `WOSubset_plus_point` (461) appends a point z to a well-ordered subset,
  needing LEM for the smallest-element condition. The glue uses it (line 1201)
  to build the larger W' from W.
- `TOSubset_plus_point_incl`, `TOSubset_plus_point_le`,
  `TOSubset_plus_point_initial` (307, 313, 321) are the three facts about the
  totally-ordered-subset-plus-point construction the glue needs to show W' is
  guided and extends W: inclusion, order-preservation, and being an initial
  segment.

Why each child is a good leaf. Each is a self-contained statement whose proof
closes on its own or from a named sibling in the same file, without unfolding
the parent's strategy: `AC_to_choice_fun` from the axiom of choice itself;
`TOSubset_plus_point_incl` from `subtype_plus_incl`; `TOSubset_plus_point_le`
from the sibling `TOSubset_plus_point_incl`; `WOSubset_plus_point` assembled
from `hasSmallest_WOSubset_plus_point`; `chain_union_le` from the two siblings
`chain_union_tosub_le` and `chain_union_rel_initial`; `upto'_eqn` from
`upto_eqn`; `guided_WOSubset_total` from `isInterval` and
`max_common_initial_is_common_initial`.

Other direct dependencies, not counted among the eight children: the glue also
applies the `guidedFamily` coercion (line 1175), the union-of-a-chain
construction `chain_union_WOSubset` reached through the `⋃` notation
(line 1178, declared at
[lines 899-909](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/OrderTheory/OrderedSets/WellOrderedSets.v#L899-L909)),
and imported lemmas `AC_to_LEM` (from MoreFoundations.AxiomOfChoice),
`negforall_to_existsneg`, `proof_by_contradiction`, `subtype_plus_has_point`,
`hSet_univalence` and `weqpr1`.

## Why it is good

1. The 95-line parent proof contains no `admit`, `Admitted`, `Axiom` or `axiom`
   closing token — the glue is a complete proof, not a skeleton with holes
   (check; lines 1169-1263).
2. `guided_WOSubset_total` occurs in the parent site — the invariant is what
   the glue actually cites (check; line 1176).
3. `guided_WOSubset_total` is declared at line 976 of the copied file
   (check; lines 976-977).
4. The shape is theorem-scale and carries the move: 8 direct lemmas, a 95-line
   glue, child sites of 7, 190, 8, 13, 6, 5, 7 and 9 lines, and a depth-2
   chain `ZermeloWellOrdering → upto'_eqn → upto_eqn` (measurement; see
   `shape` in entry.json).
5. The authors themselves name the auxiliary notion and its role: "Given a
   choice function g, we single out well ordered subsets C of X that follow the
   choice functions advice when constructed by adding one element at a time to
   the top. We may say that C is 'guided' by g." (author-statement; lines
   946-951).

In my opinion the detail worth copying is the *choice of the invariant itself*:
the well-ordering theorem cannot be proved by building the relation directly,
so the authors identify exactly the strengthened class (guided subsets) for
which comparability is provable, and then argue maximality. The move is not
among survey F §10's rules (closest is §8's "generalise / strengthen" row), so
`rule` is recorded as `none`.

## When to use it, and when not

Use this move when the goal is a maximality or universality statement — build a
maximal or universal object (`AxiomOfChoice ⇒ ∃ R, isWellOrder R`) — and the
object cannot be built all at once, but there is a notion of *good* or *guided*
approximation that is closed under unions of chains and extendable by one
element when not yet universal. State the invariant ("the approximations form a
chain") as its own lemma and let the main theorem be a skeleton over it plus
the extension lemmas.

Avoid it when the approximations do not form a chain, when the invariant lemma
itself is the hard part and does not decompose further (here
`guided_WOSubset_total` is 190 lines — the move concentrates, not removes, the
difficulty), or when a direct transfinite recursion would be more natural than
a maximality argument.

## Consequences

The move concentrates the difficulty into the invariant lemma
`guided_WOSubset_total` (190 lines) and reduces the main theorem to a 95-line
skeleton. It creates the obligation to show the union of a chain of guided
subsets is itself guided (and well ordered, via `chain_union_WOSubset`), and to
transport the induced well-ordering from the maximal guided subset W back to
the whole set X through an `hSet` univalence equivalence. Failure mode: if the
invariant is left as one opaque block, the decomposition buys nothing — the
children (`upto'_eqn`, the `TOSubset_plus_point` lemmas, `chain_union_le`)
must be standalone lemmas for the invariant to be re-assembled and re-used.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build-unimath.yml: job build-Unimath-ubuntu runs 'opam exec -- dune build -j 2 --display=short --cache=enabled' (default target) over the full UniMath tree, which includes UniMath/OrderTheory/OrderedSets/WellOrderedSets.v; the workflow runs on default branch master | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: AC_to_choice_fun@UniMath/OrderTheory/OrderedSets/WellOrderedSets.v:1174, guided_WOSubset_total@UniMath/OrderTheory/OrderedSets/WellOrderedSets.v:1176, chain_union_le@UniMath/OrderTheory/OrderedSets/WellOrderedSets.v:1185, upto'_eqn@UniMath/OrderTheory/OrderedSets/WellOrderedSets.v:1186, WOSubset_plus_point@UniMath/OrderTheory/OrderedSets/WellOrderedSets.v:1201, TOSubset_plus_point_incl@UniMath/OrderTheory/OrderedSets/WellOrderedSets.v:1203, TOSubset_plus_point_le@UniMath/OrderTheory/OrderedSets/WellOrderedSets.v:1215, TOSubset_plus_point_initial@UniMath/OrderTheory/OrderedSets/WellOrderedSets.v:1221; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 7a4b03cce49449f45ce0d4285615165172f50546 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | no_sorry(UniMath/OrderTheory/OrderedSets/WellOrderedSets.v, 1169-1263) -> no_sorry: none of admit, Admitted, Axiom, axiom in UniMath/OrderTheory/OrderedSets/WellOrderedSets.v:1169-1263 | check_claims.py |
| 2 | verified | cites(parent, guided_WOSubset_total) -> cites: guided_WOSubset_total occurs at UniMath/OrderTheory/OrderedSets/WellOrderedSets.v:1176 | check_claims.py |
| 3 | verified | declared(guided_WOSubset_total, UniMath/OrderTheory/OrderedSets/WellOrderedSets.v, 976-977) -> declared: guided_WOSubset_total is declared at UniMath/OrderTheory/OrderedSets/WellOrderedSets.v:976 | check_claims.py |
| 4 | verified | Shape numbers cross-checked against code/UniMath/OrderTheory/OrderedSets/WellOrderedSets.v: 8 children in entry.json; parent 1169-1263 = 95 lines; child line counts 938-944=7, 976-1165=190, 913-920=8, 953-965=13, 461-466=6, 307-311=5, 313-319=7, 321-329=9; depth-2 chain: glue applies upto'_eqn at line 1186 and 1213, and upto'_eqn applies upto_eqn at line 963 | verifier |
| 5 | verified | Comment at lines 946-948 of code/UniMath/OrderTheory/OrderedSets/WellOrderedSets.v reads verbatim: 'Given a choice function g, we single out well ordered subsets C of X that follow the choice functions advice when constructed by adding one element at a time to the top. We may say that C is "guided" by g.' | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Provenance passes (1 file byte-identical at 7a4b03c). Read parent site 1169-1263 and all eight child sites in the local copy: parent statement and all eight child statements match entry.json verbatim, and each child's closed_by matches the code (AC_to_choice_fun's exact ... hinhpr at 941-943; TOSubset_plus_point_incl's apply subtype_plus_incl at 310; TOSubset_plus_point_le's use tpair at 316-318; TOSubset_plus_point_initial's squash/fromempty at 325-328; chain_union_le's exists+split at 916-919; upto'_eqn's assert e'/upto_eqn at 958-963; WOSubset_plus_point's assembly at 463-466). The parent proof closes with Defined at 1263, contains no admit/Admitted/Axiom/axiom, and cites all eight children by name (1174, 1176, 1185/1246, 1186/1213, 1201, 1203, 1215, 1221). Shape numbers recomputed from the sites are right: glue_lines=1263-1169+1=95, child_lines=[7,190,8,13,6,5,7,9] equal the eight child ranges, direct_lemmas=8, and depth=2 is real (parent applies upto'_eqn at 1186/1213; upto'_eqn applies upto_eqn at 963, upto_eqn declared at 602). The only other in-file lemma the parent reaches, chain_union_WOSubset (via the union notation at 1178), is disclosed as a non-child dependency, so the 8-child decomposition is honest. | reviewer-correctness |
| generality | accept | Move is generalized beyond Zermelo: 'When to use it' abstracts to maximality/universality goals with a good/guided approximation closed under chain unions and extendable by one element, and applicability.goal_shape names a Zorn-style maximality argument; also_known_as ties it to 'strengthen the hypothesis' and 'invariant/potential'. When-not-to-use is honest and specific: three conditions including the candid admission that the invariant lemma is 190 lines and 'concentrates, not removes, the difficulty'. Consequences are specific (union-of-chain closure, transport through hSet univalence; failure mode that an opaque invariant buys nothing). Good-leaf criterion is stated: each child is self-contained, closes on its own or from a named same-file sibling, without unfolding the parent's strategy. Verifier note: author-statement quote matches lines 946-951 and known_uses (transfiniteRecursion, lines 1487-1501) shows the same guided-maximality move reused, supporting generality. The one soft spot is listing the 190-line invariant as a 'leaf' closing from isInterval/max_common_initial, which undersells its size, but the when-not-to-use and consequences sections already disclose it, so no standing objection. | reviewer-generality |
| provenance-licence | accept | Provenance pass: 1 file byte-identical at pinned commit 7a4b03cce49449f45ce0d4285615165172f50546. Commit is consistent across entry.json source.commit, source.json, SOURCE.md and all 10 permalinks (file + 9 sites), which share the same blob hash and line anchors (spot-checked declarations at 1169, 976, 938, 913, 953, 461, 307, 313, 321, and author comment 946-951). Licence recorded as MIT in entry.json, README table, source.json and SOURCE.md, with the licence text captured verbatim in sources/unimath/upstream-LICENSE.md (a permissive MIT-style licence). Source note carries repo URL, pinned commit, licence and attribution. Everything traceable and consistent. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/UniMath/UniMath at commit `7a4b03cce49449f45ce0d4285615165172f50546`, under `LicenseRef-UniMath`; see the [source note](../../sources/unimath/SOURCE.md) for the licence text and attribution.
