# The Yoneda lemma: witness isweq of yoneda_map_1 by the inverse natural transformation

| | |
|---|---|
| Kind | instance |
| Move | witness |
| Language | rocq |
| Status | accepted |
| Source | [unimath](../../sources/unimath/SOURCE.md) at `7a4b03cce494` |
| Licence | `MIT` |

## Intent

Prove the Yoneda lemma — that a natural transformation from the representable
`yoneda C c` to a functor `F` is a weak equivalence onto `F c` — by supplying,
via `isweq_iso`, an explicit inverse natural transformation (`yoneda_map_2`, the
witness) and discharging the two inverse laws as separate, self-contained
same-file lemmas.

## The decomposition

### parent `isweq_yoneda_map_1`: [`UniMath/CategoryTheory/yoneda.v` lines 305-317](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/CategoryTheory/yoneda.v#L305-L317) ([local copy](code/UniMath/CategoryTheory/yoneda.v))

```coq
Lemma isweq_yoneda_map_1 (C : category) (c : C)
   (F : functor C^op HSET) :
  isweq
     (*a := make_hSet (hom _ ((yoneda C) hs c) F) (isaset_nat_trans_yoneda C hs c F)*)
     (*b := F c*)
     (yoneda_map_1 C c F).
Proof.
  set (T:=yoneda_map_2 C c F). simpl in T.
  use isweq_iso.
  - apply T.
  - apply yoneda_map_1_2.
  - apply yoneda_map_2_1.
Defined.
```

### child `yoneda_map_1_2`: [`UniMath/CategoryTheory/yoneda.v` lines 178-194](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/CategoryTheory/yoneda.v#L178-L194) ([local copy](code/UniMath/CategoryTheory/yoneda.v))

```coq
Lemma yoneda_map_1_2 (C : category) (c : C)
  (F : functor C^op HSET)
  (alpha : hom _ (yoneda C c) F) :
      yoneda_map_2 _ _ _ (yoneda_map_1 _ _ _ alpha) = alpha.
Proof.
  simpl in *.
  set (T:=nat_trans_eq (C:=C^op) (has_homsets_HSET)).
  apply T.
  intro a'; simpl.
  apply funextsec; intro f.
  unfold yoneda_map_1.
  intermediate_path ((alpha c · #F f) (identity c)).
    apply idpath.
  rewrite <- nat_trans_ax.
  unf; apply maponpaths.
  apply (id_right f ).
Qed.
```

### child `yoneda_map_2_1`: [`UniMath/CategoryTheory/yoneda.v` lines 197-204](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/CategoryTheory/yoneda.v#L197-L204) ([local copy](code/UniMath/CategoryTheory/yoneda.v))

```coq
Lemma yoneda_map_2_1 (C : category) (c : C)
   (F : functor C^op HSET) (x : pr1 (F c)) :
   yoneda_map_1 _ _ _ (yoneda_map_2 _  _ _ x) = x.
Proof.
  simpl.
  rewrite (functor_id F).
  apply idpath.
Qed.
```

### context `yoneda_map_1`: [`UniMath/CategoryTheory/yoneda.v` lines 147-150](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/CategoryTheory/yoneda.v#L147-L150) ([local copy](code/UniMath/CategoryTheory/yoneda.v))

```coq
Definition yoneda_map_1 (C : category) (c : C)
   (F : functor C^op HSET) :
       hom _ (yoneda C c) F -> pr1 (F c) :=
   λ h,  pr1 h c (identity c).
```

### context `yoneda_map_2_ax`: [`UniMath/CategoryTheory/yoneda.v` lines 154-167](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/CategoryTheory/yoneda.v#L154-L167) ([local copy](code/UniMath/CategoryTheory/yoneda.v))

```coq
Lemma yoneda_map_2_ax (C : category) (c : C)
       (F : functor C^op HSET) (x : pr1 (F c)) :
  is_nat_trans (pr1 (yoneda C c)) F
         (fun (d : C) (f : hom (C ^op) c d) => #F f x).
Proof.
  intros a b f; simpl in *.
  apply funextsec.
  unfold yoneda_objects_ob; intro g.
  set (H:= @functor_comp _ _ F  _ _  b g).
  unfold functor_comp in H;
  unfold opp_precat_data in H;
  simpl in *.
  apply (toforallpaths _ _ _ (H f) x).
Qed.
```

### context `yoneda_map_2`: [`UniMath/CategoryTheory/yoneda.v` lines 169-176](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/CategoryTheory/yoneda.v#L169-L176) ([local copy](code/UniMath/CategoryTheory/yoneda.v))

```coq
Definition yoneda_map_2 (C : category) (c : C)
   (F : functor C^op HSET) :
       pr1 (F c) -> hom _ (yoneda C c) F.
Proof.
  intro x.
  exists (λ d : ob C, λ f, #F f x).
  apply yoneda_map_2_ax.
Defined.
```

How the parts fit. The parent's proof is five lines of glue. `set
(T:=yoneda_map_2 C c F)` introduces the named witness: the inverse natural
transformation. `use isweq_iso` applies the library theorem `isweq_iso {X Y : UU}
(f : X -> Y) (g : Y -> X) (egf : ∏ x, g (f x) = x) (efg : ∏ y, f (g y) = y) :
isweq f` (defined at [`UniMath/Foundations/PartA.v` lines 1751-1766](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/Foundations/PartA.v#L1751-L1766)), which turns
`isweq (yoneda_map_1 C c F)` into three obligations: an inverse `g`, and the two
homotopies `g ∘ f = id` and `f ∘ g = id`. The three bullets close each: `apply
T` supplies the inverse, `apply yoneda_map_1_2` supplies the section law
`yoneda_map_2 ∘ yoneda_map_1 = id`, and `apply yoneda_map_2_1` supplies the
retraction law `yoneda_map_1 ∘ yoneda_map_2 = id`.

The lemma graph is

```
isweq_yoneda_map_1  (glue: set T := yoneda_map_2; use isweq_iso)
├── yoneda_map_2    (context, the witness / inverse; a Definition) ── yoneda_map_2_ax (context, its naturality)
├── yoneda_map_1_2  (child, section law g ∘ f = id)
└── yoneda_map_2_1  (child, retraction law f ∘ g = id)
```

Both children are good leaves: `yoneda_map_1_2` is a self-contained statement
about an arbitrary `alpha` that closes by reducing the equality of natural
transformations pointwise with `nat_trans_eq` and then rewriting by the
naturality axiom `nat_trans_ax`; `yoneda_map_2_1` closes almost trivially with
`functor_id`. The witness `yoneda_map_2` is not a lemma but a `Definition` whose
only proof obligation — that its component map is natural — is discharged by
`yoneda_map_2_ax`, giving the depth-2 chain `isweq_yoneda_map_1 → yoneda_map_2 →
yoneda_map_2_ax`.

## Why it is good

1. *(check)* The parent closes from the named witness and the two lemmas in a
   five-line proof: `set (T:=yoneda_map_2 C c F)`, `use isweq_iso`, then `apply
   T`, `apply yoneda_map_1_2`, `apply yoneda_map_2_1`
   ([lines 312-316](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/CategoryTheory/yoneda.v#L305-L317)).
2. *(check)* Each child closes on its own without another same-file lemma:
   `yoneda_map_1_2` uses `nat_trans_eq ... has_homsets_HSET` then
   `nat_trans_ax` and `id_right` ([lines 184-193](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/CategoryTheory/yoneda.v#L178-L194));
   `yoneda_map_2_1` uses `functor_id` and `idpath`
   ([lines 201-203](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/CategoryTheory/yoneda.v#L197-L204)).
3. *(author-statement)* The authors label this the Yoneda lemma: "Yoneda lemma:
   natural transformations from [yoneda C c] to [F] are isomorphic to [F c]"
   ([lines 143-144](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/CategoryTheory/yoneda.v#L143-L144)).
4. *(measurement)* The glue is 13 lines (305-317) with a 5-line proof body
   (312-316); the two children are 17 and 8 lines (178-194, 197-204); the
   longest chain of project items below the main theorem is 2
   (`isweq_yoneda_map_1 → yoneda_map_2 → yoneda_map_2_ax`).
5. *(known-use)* The same witness move (`isweq_iso` with an inverse and two
   homotopies) is reused in the same file to prove the Yoneda embedding is
   fully faithful, `yoneda_fully_faithful`
   ([lines 327-346](https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/CategoryTheory/yoneda.v#L327-L346)).

In my opinion the detail worth copying is that the two inverse laws are stated
for an arbitrary `alpha` (resp. `x`) and named as lemmas, so the glue stays a
one-`apply`-per-obligation skeleton and no unfixed witness appears inside any
child.

## When to use it, and when not

Use it when the goal is `isweq f` and the inverse (witness) has an explicit,
constructible definition whose two inverse laws can be stated as separate
self-contained lemmas; an extensionality principle (here `nat_trans_eq` /
`funextsec`) then reduces each law to pointwise equalities. This is the standard
way to build a weak equivalence from a section-retraction pair.

Avoid it when the inverse is not constructible without a choice or classical
axiom (then prove `isweq` by unfolding it and showing contractibility of
fibres); when the two inverse laws share a long common proof that would be
duplicated across two lemmas; or when the map is already a known equivalence,
where `make_weq` with an existing `isweq` (or `isweqinvmap`) is shorter.

## Consequences

`use isweq_iso` creates exactly three obligations: an inverse `g`, and the two
homotopies `g ∘ f = id` and `f ∘ g = id`; each is discharged by a single `apply`
to a named lemma. The witness `yoneda_map_2` is a `Definition` that must first
prove its own naturality (done by the sub-lemma `yoneda_map_2_ax`); if that
definition changes, both the sub-lemma and the two inverse laws must be
revisited. The inverse laws are stated for an arbitrary `alpha` (resp. `x`), so
no unfixed witness appears inside any child (survey F rule 8). A failure mode is
that the glue assumes `isweq_iso`'s argument order matches the order of the
three bullets; swapping the two inverse laws would still type-check only if the
statements are symmetric, which they are not here.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build-unimath.yml; runs 'dune build' of the whole UniMath project on push to master; pinned commit 7a4b03cce49449f45ce0d4285615165172f50546 is on the default branch master | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 7a4b03cce49449f45ce0d4285615165172f50546 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Copied file yoneda.v lines 305-317: proof body is lines 312-316 = set (T:=yoneda_map_2 C c F). simpl in T. / use isweq_iso. / - apply T. / - apply yoneda_map_1_2. / - apply yoneda_map_2_1. (5 lines), matching the claim exactly | verifier |
| 2 | verified | Copied file: yoneda_map_1_2 (178-194) sets T:=nat_trans_eq (C:=C^op) (has_homsets_HSET) (184), rewrite <- nat_trans_ax (191), apply (id_right f) (193); yoneda_map_2_1 (197-204) rewrite (functor_id F) (202), apply idpath (203). Neither uses a same-file lemma | verifier |
| 3 | verified | Copied file lines 143-144 read: (** ** Yoneda lemma: natural transformations from [yoneda C c] to [F] / are isomorphic to [F c] *), matching the quoted author comment | verifier |
| 4 | verified | Copied file line counts: 317-305+1=13, 312-316=5, 194-178+1=17, 204-197+1=8. Depth: isweq_yoneda_map_1 uses yoneda_map_2 (169-176, Definition) which applies yoneda_map_2_ax (154-167); inverse-law lemmas are direct children | verifier |
| 5 | verified | Copied file lines 327-346: yoneda_fully_faithful applies isweq_iso (330) with inverse yoneda_map_1, closes two homotopy goals inline (332-333 by id_left; 334-345). Same witness move reused in-file | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent isweq_yoneda_map_1 (L305-317) closes with set T:=yoneda_map_2, use isweq_iso, then apply T / yoneda_map_1_2 / yoneda_map_2_1; no admit/Admitted. Children yoneda_map_1_2 (L178-194) and yoneda_map_2_1 (L197-204) match entry statements verbatim and are exactly the two lemmas the glue applies; yoneda_map_2 is a Definition, correctly listed as context not a child. closing methods match: yoneda_map_1_2 uses nat_trans_eq/has_homsets_HSET then rewrite <- nat_trans_ax and id_right; yoneda_map_2_1 uses rewrite (functor_id F) and idpath. Shape: direct_lemmas=2, glue_lines=13 (305-317), child_lines=[17,8] (178-194, 197-204) all correct; depth=2 counts isweq_yoneda_map_1 -> yoneda_map_2 (Definition) -> yoneda_map_2_ax, disclosed in claim 4. Provenance pass (1 file byte-identical). | reviewer-correctness |
| generality | accept | Move is stated beyond the example: goal_shape/use_when abstract from the Yoneda instance to any 'isweq f' with a constructible inverse and two factorable homotopies plus an extensionality principle, and known-use claim 5 shows the same isweq_iso witness reused at yoneda_fully_faithful (code lines 330-345 confirm). avoid_when is honest and specific: non-constructible inverse -> prove isweq via contractible fibres; long shared proof duplicated across two laws; already-known equivalence -> make_weq (confirmed at yoneda_weq, code lines 319-322). Consequences are specific: three isweq_iso obligations each closed by one apply; witness yoneda_map_2 is a Definition carrying its own naturality obligation yoneda_map_2_ax; argument-order failure mode is real (section vs retraction laws are not symmetric here). Good leaves are explained: both children are self-contained for an arbitrary alpha/x with no unfixed witness inside any child, yoneda_map_1_2 closing via nat_trans_eq/nat_trans_ax and yoneda_map_2_1 near-trivially via functor_id (claim 2 + 'Both children are good leaves'). | reviewer-generality |
| provenance-licence | accept | Permalinks all use pinned commit 7a4b03cce49449f45ce0d4285615165172f50546 and their line ranges match the copied file (yoneda_map_1 147-150, yoneda_map_2_ax 154-167, yoneda_map_2 169-176, yoneda_map_1_2 178-194, yoneda_map_2_1 197-204, isweq_yoneda_map_1 305-317, yoneda_fully_faithful 327-346). Commit is identical across entry.json, source.json, SOURCE.md and README, and check_provenance.py confirms the file byte-identical at that commit. Licence MIT recorded consistently in all four places, and upstream-LICENSE.md holds the MIT permission grant (no copyleft/non-commercial). SOURCE.md source note (repo, commit, browse URL, licence, LICENSE.md -> upstream-LICENSE.md) matches the copied file and entry. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/UniMath/UniMath at commit `7a4b03cce49449f45ce0d4285615165172f50546`, under `MIT`; see the [source note](../../sources/unimath/SOURCE.md) for the licence text and attribution.
