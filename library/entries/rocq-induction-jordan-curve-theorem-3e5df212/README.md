# Induction on the ring list for the discrete Jordan curve theorem

| | |
|---|---|
| Kind | instance |
| Move | induction |
| Language | rocq |
| Status | draft |
| Source | [jordan-curve-theorem](../../sources/jordan-curve-theorem/SOURCE.md) at `906762607c3e` |
| Licence | `LicenseRef-unknown` |
| Licence recorded | 2026-11-14T12:38:48Z |

## Intent

The project's headline result — breaking a planar hypermap along a face ring
raises its number of connected components by exactly one — is proved by
induction on the ring list. The induction's step case is not proved inline:
it is assembled from six named lemmas about the one-link break `Br1`, each
stated and proved earlier in the same file.

## The decomposition

### parent `Jordan`: [`Jordan10.v` lines 8763-8819](https://github.com/coq-contribs/jordan-curve-theorem/blob/906762607c3e05bedd3f9aab002172e34dd1b595/Jordan10.v#L8763-L8819) ([local copy](code/Jordan10.v))

```coq
Theorem Jordan: forall(l:list)(m:fmap),
 inv_hmap m -> planar m -> ring m l ->
   nc (Br m l) = nc m + 1.
Proof.
induction l.
 unfold ring in |- *.
   simpl in |- *.
    tauto.
rename d into x.
  rename d0 into x'.
  simpl in |- *.
  intros.
  induction l.
 simpl in |- *.
   generalize (Jordan1 m x x').
   simpl in |- *.
    tauto.
rename d into xs.
  rename d0 into xs'.
  set (y := cA m zero x) in |- *.
  set (y' := cA m zero x') in |- *.
  assert (~ expf m y y').
 unfold y in |- *.
   unfold y' in |- *.
   unfold ring in H1.
   apply (ring1_ring3_connect m x x' xs xs' l).
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
rewrite IHl in |- *.
 rewrite nc_Br1 in |- *.
  fold y in |- *.
    fold y' in |- *.
    elim (expf_dec m y y').
    tauto.
  intro.
     omega.
  tauto.
  tauto.
 unfold ring in H1.
   simpl in H1.
    tauto.
apply inv_hmap_Br1.
   tauto.
apply planar_Br1.
  tauto.
 tauto.
unfold ring in H1.
  simpl in H1.
  unfold double_link in H1.
   tauto.
generalize (ring_Br1 m (cons x x' (cons xs xs' l)) H H0 H1).
  simpl in |- *.
   tauto.
Qed.
```

### child `Jordan1`: [`Jordan10.v` lines 5994-6030](https://github.com/coq-contribs/jordan-curve-theorem/blob/906762607c3e05bedd3f9aab002172e34dd1b595/Jordan10.v#L5994-L6030) ([local copy](code/Jordan10.v))

```coq
Lemma Jordan1:forall(m:fmap)(x x':dart),
  inv_hmap m -> planar m -> 
   let l:= cons x x' lam in 
    ring m l -> nc (Br m l) = nc m + 1.
Proof.
unfold ring in |- *.
unfold pre_ring0 in |- *.
unfold pre_ring1 in |- *.
unfold pre_ring2 in |- *.
unfold pre_ring3 in |- *.
unfold double_link_list in |- *.
unfold double_link in |- *.
unfold distinct_face_list in |- *.
unfold distinct_edge_list in |- *.
unfold face_adjacent in |- *.
simpl in |- *.
intros.
decompose [and] H1.
clear H1 H2 H6 H5 H9 H3 H10 H12.
set (y := cA m zero x) in |- *.
set (y' := cA m zero x') in |- *.
fold y in H8.
fold y' in H8.
rewrite nc_Br1 in |- *.
 fold y in |- *.
   fold y' in |- *.
   elim (expf_dec m y y').
   tauto.
 intro.
   elim b.
   apply expf_symm.
    tauto.
 tauto.
 tauto.
unfold double_link in |- *.
   tauto.
Qed.
```

### child `nc_Br1`: [`Jordan10.v` lines 5379-5601](https://github.com/coq-contribs/jordan-curve-theorem/blob/906762607c3e05bedd3f9aab002172e34dd1b595/Jordan10.v#L5379-L5601) ([local copy](code/Jordan10.v))

```coq
Theorem nc_Br1: forall (m:fmap)(x x':dart),
  inv_hmap m -> planar m -> double_link m x x' ->
    let y  := cA m zero x in
    let y' := cA m zero x' in
  nc (Br1 m x x') = nc m + 
     if expf_dec m y y' then 1 else 0.
Proof.
intros.
unfold Br1 in |- *.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  intros.
    set (m0 := L (B m zero x) zero (top m zero x) 
  (bottom m zero x)) in |- *.
    assert (inv_hmap m0).
   unfold m0 in |- *.
     apply inv_hmap_L_B_top_bot.
     tauto.
    tauto.
  assert (succ m0 zero x').
   unfold succ in |- *.
     unfold m0 in |- *.
     rewrite A_L_B_top_bot in |- *.
    elim (eq_dart_dec x x').
     elim (eq_dart_dec (top m zero x) x').
      intros.
        rewrite <- a1 in a.
         absurd (succ m zero (top m zero x)).
       apply not_succ_top.
          tauto.
       tauto.
     unfold double_link in H1.
        tauto.
    elim (eq_dart_dec (top m zero x) x').
     intros.
       rewrite <- a1 in a.
        absurd (succ m zero (top m zero x)).
      apply not_succ_top.
         tauto.
      tauto.
    unfold succ in a.
       tauto.
    tauto.
    tauto.
  assert (y = bottom m0 zero x').
   unfold m0 in |- *.
     unfold double_link in H1.
     assert (x <> x').
     tauto.
   assert (exd m x').
    apply MA0.expo_exd with x.
      tauto.
    unfold expe in H1.
       tauto.
   rewrite (bottom_L_B_top_bot m x x' H a0 H5 H4) in |- *.
     elim (MA0.expo_dec m x x').
    unfold y in |- *.
      rewrite cA_eq in |- *.
     elim (succ_dec m zero x).
       tauto.
      tauto.
     tauto.
    tauto.
  assert (y' = A m0 zero x').
   unfold m0 in |- *.
     rewrite A_L_B_top_bot in |- *.
    elim (eq_dart_dec x x').
     unfold double_link in H1.
        tauto.
    elim (eq_dart_dec (top m zero x) x').
     intro.
       rewrite <- a1 in a.
        absurd (succ m zero (top m zero x)).
      apply not_succ_top.
         tauto.
      tauto.
    intros.
      unfold y' in |- *.
      rewrite cA_eq in |- *.
     elim (succ_dec m zero x').
       tauto.
      tauto.
     tauto.
    tauto.
    tauto.
  generalize (expf_L_B_top_bot m zero x y y' H a0).
    fold m0 in |- *.
    intro.
    assert (nc m0 = nc m).
   unfold m0 in |- *.
     rewrite nc_L_B_top_bot in |- *.
     tauto.
    tauto.
    tauto.
  rewrite nc_B in |- *.
   assert (planar m0).
    unfold m0 in |- *.
      apply planar_L_B_top_bot_0.
      tauto.
     tauto.
     tauto.
   generalize (disconnect_planar_criterion_B0 m0 x' H2 H8 H3).
     intro.
     rewrite <- H5 in H9.
     rewrite <- H4 in H9.
     assert (expf m0 y' y <-> ~ eqc (B m0 zero x') x' y').
    apply H9.
   rewrite <- H5 in |- *.
     clear H9.
     rewrite <- H7 in |- *.
     elim (eqc_dec (B m0 zero x') x' y').
    elim (expf_dec m y y').
     intro.
       assert (expf m0 y' y).
      apply expf_symm.
         tauto.
      tauto.
     tauto.
   elim (expf_dec m y y').
    intro.
      assert (expf m0 y' y).
     apply expf_symm.
        tauto.
     tauto.
   intros.
     assert (expf m0 y y').
    apply expf_symm.
       tauto.
    tauto.
   tauto.
   tauto.
 intros.
   rewrite nc_B in |- *.
  unfold y' in |- *.
    assert (y = A m zero x).
   unfold y in |- *.
     rewrite cA_eq in |- *.
    elim (succ_dec m zero x).
      tauto.
     tauto.
    tauto.
  rewrite <- H2 in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x').
     tauto.
   intro.
     generalize (disconnect_planar_criterion_B0 m x H H0 a).
     simpl in |- *.
     rewrite <- H2 in |- *.
     intros.
     elim (eqc_dec (B m zero x) x y).
    elim (expf_dec m y (bottom m zero x')).
     intros.
       assert (bottom m zero x = bottom m zero x').
      apply expe_bottom.
        tauto.
      unfold double_link in H1.
        unfold expe in H1.
         tauto.
     rewrite <- H4 in a0.
        tauto.
     tauto.
   elim (expf_dec m y (bottom m zero x')).
     tauto.
   intros.
     assert (bottom m zero x = bottom m zero x').
    apply expe_bottom.
      tauto.
    unfold double_link in H1.
      unfold expe in H1.
       tauto.
   rewrite <- H4 in b1.
      tauto.
   tauto.
  tauto.
  tauto.
intro.
  assert (succ m zero x').
 generalize (double_link_succ m x x').
    tauto.
rewrite nc_B in |- *.
 assert (y' = A m zero x').
  unfold y' in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x').
     tauto.
    tauto.
   tauto.
 rewrite <- H3 in |- *.
   assert (y = bottom m zero x').
  unfold y in |- *.
    rewrite cA_eq in |- *.
   elim (succ_dec m zero x).
     tauto.
   intro.
     apply expe_bottom.
     tauto.
   unfold double_link in H1.
     unfold expe in H1.
      tauto.
   tauto.
 rewrite H4 in |- *.
   generalize (disconnect_planar_criterion_B0 m x' H H0 H2).
   simpl in |- *.
   rewrite <- H3 in |- *.
   intros.
   elim (eqc_dec (B m zero x') x' y').
  elim (expf_dec m (bottom m zero x') y').
   intros.
     assert (expf m y' (bottom m zero x')).
    apply expf_symm.
       tauto.
    tauto.
   tauto.
 elim (expf_dec m (bottom m zero x') y').
   tauto.
 intros.
   elim b0.
   apply expf_symm.
    tauto.
 tauto.
 tauto.
Qed.
```

### child `ring1_ring3_connect`: [`Jordan10.v` lines 6296-6329](https://github.com/coq-contribs/jordan-curve-theorem/blob/906762607c3e05bedd3f9aab002172e34dd1b595/Jordan10.v#L6296-L6329) ([local copy](code/Jordan10.v))

```coq
Lemma ring1_ring3_connect: 
  forall(m:fmap)(x x' xs xs':dart)(l:list),
   let l1:= cons x x' (cons xs xs' l) in
   let y  := cA m zero x in
   let y' := cA m zero x' in 
   inv_hmap m -> planar m -> 
     double_link_list m l1 ->
       pre_ring1 m l1 -> pre_ring3 m l1 ->
         ~ expf m y y'.
Proof.
simpl in |- *.
unfold double_link in |- *.
unfold distinct_faces in |- *.
unfold face_adjacent in |- *.
intros.
generalize H1 H2 H3.
clear H1 H2 H3.
set (y := cA m zero x) in |- *.
set (ys := cA m zero xs) in |- *.
set (y' := cA m zero x') in |- *.
set (xb0 := bottom m zero x) in |- *.
intros.
decompose [and] H1.
clear H1.
decompose [and] H2.
clear H2.
decompose [and] H3.
clear H3.
intro.
apply H13.
apply expf_trans with y'.
  tauto.
 tauto.
Qed.
```

### child `inv_hmap_Br1`: [`Jordan10.v` lines 4229-4255](https://github.com/coq-contribs/jordan-curve-theorem/blob/906762607c3e05bedd3f9aab002172e34dd1b595/Jordan10.v#L4229-L4255) ([local copy](code/Jordan10.v))

```coq
Lemma inv_hmap_Br1:forall(m:fmap)(x x':dart),
   inv_hmap m -> inv_hmap (Br1 m x x').
Proof.
unfold Br1 in |- *.
intros.
elim (succ_dec m zero x).
 intro.
 elim (succ_dec m zero x').
  intros.
  apply inv_hmap_B.
    apply inv_hmap_L_B_top_bot.
    tauto.
   tauto.
 intro.
   apply inv_hmap_B.
    tauto.
intro.
  elim (succ_dec m zero x').
 intro.
   apply inv_hmap_B.
    tauto.
intro.
  rewrite not_succ_B in |- *.
  tauto.
 tauto.
 tauto.
Qed.
```

### child `planar_Br1`: [`Jordan10.v` lines 4257-4307](https://github.com/coq-contribs/jordan-curve-theorem/blob/906762607c3e05bedd3f9aab002172e34dd1b595/Jordan10.v#L4257-L4307) ([local copy](code/Jordan10.v))

```coq
Lemma planar_Br1:forall(m:fmap)(x x':dart),
  inv_hmap m -> planar m -> x <> x' -> 
     planar (Br1 m x x').
Proof.
intros.
unfold Br1 in |- *.
elim (succ_dec m zero x).
 elim (succ_dec m zero x').
  intros.
    apply planar_B0.
   apply inv_hmap_L_B_top_bot.
     tauto.
    tauto.
  unfold succ in |- *.
    simpl in |- *.
    elim (eq_dart_dec (top m zero x) x').
   intro.
     rewrite <- a1 in a.
      absurd (succ m zero (top m zero x)).
    apply not_succ_top.
       tauto.
    tauto.
  intro.
    rewrite A_B_bis in |- *.
   unfold succ in a.
      tauto.
  intro.
    symmetry  in H2.
     tauto.
  apply planar_L_B_top_bot_0.
    tauto.
   tauto.
   tauto.
 intros.
   apply planar_B0.
   tauto.
  tauto.
  tauto.
intro.
  elim (succ_dec m zero x').
 intro.
   apply planar_B0.
   tauto.
  tauto.
  tauto.
intro.
  rewrite not_succ_B in |- *.
  tauto.
 tauto.
 tauto.
Qed.
```

### child `ring_Br1`: [`Jordan10.v` lines 8714-8759](https://github.com/coq-contribs/jordan-curve-theorem/blob/906762607c3e05bedd3f9aab002172e34dd1b595/Jordan10.v#L8714-L8759) ([local copy](code/Jordan10.v))

```coq
Lemma ring_Br1: forall(m:fmap)(l:list),
 inv_hmap m -> planar m -> 
   let x:= fst (first l) in let x' := snd (first l) in
   let m1 := Br1 m x x' in
 ring m l -> (emptyl (tail l) \/ ring m1 (tail l)).
Proof.
intros.
unfold m1 in |- *.
unfold ring in H1.
induction l.
 unfold ring in H1.
   simpl in H1.
    tauto.
simpl in |- *.
  simpl in x.
  simpl in x'.
  fold x in H1.
  fold x' in H1.
  induction l.
 simpl in |- *.
    tauto.
rename d1 into xs.
  rename d2 into xs'.
  set (y := cA m zero x) in |- *.
  set (y' := cA m zero x') in |- *.
  assert (~ expf m y y').
 unfold y in |- *.
   unfold y' in |- *.
   apply (ring1_ring3_connect m x x' xs xs' l).
   tauto.
  tauto.
  tauto.
  tauto.
  tauto.
generalize (ring_Br1_aux m (cons x x' (cons xs xs' l))).
  simpl in |- *.
  fold y in |- *.
  fold y' in |- *.
  intros.
  apply H3.
  tauto.
 tauto.
 tauto.
unfold ring in |- *.
   tauto.
Qed.
```

How the parts fit. The glue is a double induction on the ring list `l`. The
outer `induction l` closes the empty-list case by `unfold ring; simpl; tauto`
(a ring is `~emptyl l ∧ …`, Jordan10.v:5981, so the empty list is no ring). In
the cons case the head elements are renamed `x`, `x'` and the hypotheses
`inv_hmap m`, `planar m`, `ring m l` are introduced; a second `induction l`
then splits the rest into the length-one case, closed by `Jordan1`, and the
general step. The six children fit together as follows (the glue cites each
exactly once):

```
Jordan
 ├─ Jordan1               — length-one base case (line 8777)
 ├─ nc_Br1                — the arithmetic of one break (line 8795)
 ├─ ring1_ring3_connect   — the key `~ expf` assertion (line 8788)
 ├─ inv_hmap_Br1          — preserves `inv_hmap` (line 8807)
 ├─ planar_Br1            — preserves `planar` (line 8809)
 └─ ring_Br1              — rebuilds `ring` for the tail (line 8816)
```

The step case runs in four moves. First the glue asserts
`~ expf m y y'` with `ring1_ring3_connect` (8784–8788), where `y` and `y'` are
the faces `cA m zero x` and `cA m zero x'` at the broken link. Then it rewrites
with the induction hypothesis `IHl` on the tail and with `nc_Br1`, turning the
goal into `nc m + (if expf_dec m y y' then 1 else 0) = nc m + 1`; because
`~ expf` was asserted, `elim (expf_dec m y y')` lands on the `0` branch and
`omega` closes the arithmetic (8794–8801). The three hypotheses that `IHl` and
`nc_Br1` need — `inv_hmap`, `planar` and `ring` on the tail — are discharged by
`inv_hmap_Br1`, `planar_Br1` and `ring_Br1` respectively (8807–8818).

Why each child is a good leaf, i.e. a self-contained statement that closes on
its own or from named siblings:

- `Jordan1` is the whole theorem for a ring of length one (`cons x x' lam`).
  It is not a degenerate case of the step, so it earns its own lemma; its
  proof reduces to `rewrite nc_Br1` and closes with `expf_symm` and `tauto`.
- `nc_Br1` is the component-count engine: for a single link it states
  `nc (Br1 m x x') = nc m + if expf_dec m y y' then 1 else 0` — the count rises
  by exactly 1 when the two faces at the link are distinct. It closes on its
  own, by case analysis on `succ_dec m zero x` and rewrites through `nc_B`,
  `nc_L_B_top_bot` and `disconnect_planar_criterion_B0`.
- `ring1_ring3_connect` is the mathematical heart: it turns the ring
  predicates `double_link_list`, `pre_ring1`, `pre_ring3` into the
  non-adjacency fact `~ expf m y y'`. It closes with
  `apply expf_trans with y'; tauto`.
- `inv_hmap_Br1` and `planar_Br1` are stability lemmas — breaking one link of a
  hypermap keeps it a hypermap and keeps it planar — each closing by case
  analysis on `succ_dec m zero x` and `tauto`.
- `ring_Br1` is the invariant-rebuilder: `ring m l` yields
  `emptyl (tail l) ∨ ring (Br1 m x x') (tail l)`, so the induction hypothesis
  applies to the tail. Its proof is itself an induction on `l` that reuses
  `ring1_ring3_connect` for the same `~ expf` fact and hands the five ring
  predicates to `ring_Br1_aux` (which uses `pre_ring0_Br1` … `pre_ring3_Br1`).
  The longest chain below the theorem I checked is
  `Jordan → ring_Br1 → ring_Br1_aux → pre_ring3_Br1 → pre_ring3_Br1_aux_bis`
  (depth 4), recorded in `shape.depth`.

## Why it is good

1. The parent site is 57 lines long, from the `Theorem Jordan` declaration
   through `Qed` — a thin glue (check: `lines(parent, 57)`).
2. The glue cites `nc_Br1`, the one-link component-count lemma, at
   Jordan10.v:8795 (check: `cites(parent, nc_Br1)`).
3. No `admit`, `Admitted`, `Axiom` or `axiom` token appears in Jordan10.v
   lines 4229–8819, the parent and all six children (check:
   `no_sorry(Jordan10.v, 4229-8819)`).
4. The six direct child lemmas span 418 proof lines in total against 57 glue
   lines, so the decomposition moves nearly all of the argument into reusable
   one-step lemmas (measurement; see `metrics`).
5. The authors state the result as a discrete Jordan curve theorem: "When the
   hypermap is planar and is broken at these edges, the number of its connected
   components increases by one, which is a discrete version of the famous
   Jordan curve theorem." (author-statement, project README line 7).

In my opinion the detail worth copying is the division of labour in the step
case: `ring1_ring3_connect` isolates the one genuinely mathematical fact
(`~ expf`) that makes the `+1` real, while `inv_hmap_Br1`, `planar_Br1` and
`ring_Br1` are pure "the hypothesis is preserved" bookkeeping. That split — one
hard leaf, three stability leaves — is what makes the induction hypothesis
reusable at each step and keeps the glue to `tauto`/`omega`.

## When to use it, and when not

Use induction-on-a-list-with-named-step-lemmas when the target is a quantity
(`nc` here) that changes by a fixed increment per `cons`-step of a list, and
the step's side conditions — the hypothesis is preserved and the increment is
real — are already proved as named one-step lemmas about the single operation
(`Br1`). The base case need not be a degenerate form of the step; here it is
its own lemma, `Jordan1`.

Avoid it when the step does not preserve the hypothesis you need to reapply the
induction hypothesis (here `ring` is re-established by `ring_Br1`), when the
increment depends on a case the invariant does not exclude (here `expf` vs
`~ expf`, excluded by `ring1_ring3_connect`), or when the quantity is not
additive across the step.

## Consequences

The induction creates three obligations that the six lemmas are arranged to
meet: (i) the empty and length-one base cases, closed by `tauto` and then by
`Jordan1`; (ii) a `~ expf` assertion that makes `nc_Br1`'s `if expf_dec` branch
land on `0` so `omega` closes `nc m + 0 = nc m + 1`, discharged by
`ring1_ring3_connect`; (iii) the side conditions to reapply the induction
hypothesis on the tail — `inv_hmap_Br1` and `planar_Br1` preserve the map's
hypotheses, and `ring_Br1` rebuilds the ring invariant for the tail.

Failure mode: if the invariant does not compose under the break (the tail of a
ring were not a ring), the induction hypothesis is unusable; and the whole `+1`
rests on `planar`, since without it the two faces at the broken link could be
equal (`expf`) and `nc` would not increase.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: Jordan1@Jordan10.v:8777, nc_Br1@Jordan10.v:8795, ring1_ring3_connect@Jordan10.v:8788, inv_hmap_Br1@Jordan10.v:8807, planar_Br1@Jordan10.v:8809, ring_Br1@Jordan10.v:8816; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(parent, 57) -> lines: site parent has 57 lines | check_claims.py |
| 2 | verified | cites(parent, nc_Br1) -> cites: nc_Br1 occurs at Jordan10.v:8795 | check_claims.py |
| 3 | verified | no_sorry(Jordan10.v, 4229-8819) -> no_sorry: none of admit, Admitted, Axiom, axiom in Jordan10.v:4229-8819 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/coq-contribs/jordan-curve-theorem at commit `906762607c3e05bedd3f9aab002172e34dd1b595`, under `LicenseRef-unknown`; see the [source note](../../sources/jordan-curve-theorem/SOURCE.md) for the licence text and attribution.
