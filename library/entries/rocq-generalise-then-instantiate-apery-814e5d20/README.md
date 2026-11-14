# General order-1 recurrence uniqueness instantiated at the Apéry casoratian

| | |
|---|---|
| Kind | instance |
| Move | generalise-then-instantiate |
| Language | rocq |
| Status | accepted |
| Source | [apery](../../sources/apery/SOURCE.md) at `97f0c01bec42` |
| Licence | `CECILL-C` |
| Licence recorded | 2026-11-14T12:44:48Z |

## Intent

Prove the casoratian identity `ba_casoratian n = 6%:Q / (n%:Q + 1) ^ 3` not by a
direct computation of `ba_casoratian` but by generalising the question. The glue
states, once, that a sequence satisfying a given order-1 recurrence and agreeing
with another sequence at `n = 2` is equal to it everywhere, then instantiates
that uniqueness at `ba_casoratian` and the closed form `v n = 6%:Q / (n%:Q + 1) ^ 3`.

## The decomposition

### parent `ba_casoratianE`: [`theories/b_over_a_props.v` lines 24-58](https://github.com/rocq-community/apery/blob/97f0c01bec4282c4504c0225a71ff0e75aeab115/theories/b_over_a_props.v#L24-L58) ([local copy](code/theories/b_over_a_props.v))

```coq
Lemma ba_casoratianE (n : int) :
  2%:~R <= n -> ba_casoratian n = 6%:Q / (n%:Q + 1) ^ 3.
Proof.
move=> le2n; have le0n : 0 <= n by exact: le_trans le2n.
pose v (k : int) : rat := 6%:Q / (k%:Q + 1) ^ 3.
pose c1 := annotated_recs_c.P_cf2.
pose c0 := annotated_recs_c.P_cf0.
pose Urec (v : int -> rat) := forall (k : int), 2%:~R <= k ->
                      c1 k * v (int.shift 1 k) - c0 k * v k = 0.
have uUrec : Urec ba_casoratian.
  move=> k le2k; have le0k : 0 <= k by exact: le_trans le2k.
  have brec := b_Sn2 le0k; have arec := a_Sn2 le2k.
  have -> : 0 = a (int.shift 1 k) * annotated_recs_c.P_horner b k
                - b (int.shift 1 k) * annotated_recs_c.P_horner a k.
    by rewrite brec arec !mulr0 subrr.
  rewrite /annotated_recs_c.P_horner /annotated_recs_c.P_seq /c1 /c0.
  by rewrite /punk.horner_seqop /= /ba_casoratian; ring.
have vUrec : Urec v.
  move=> k le2k.
  rewrite /c0 /c1 /annotated_recs_c.P_cf2 /annotated_recs_c.P_cf0 /v.
  by rewrite int.shift2R; field; ring_lia.
(* this step below is only the fact that U is a rec of order 1 : should be *)
(* obtained from something more general... *)
suff {uUrec vUrec v} Urec1P (w1 w2 : int -> rat) : w1 2 = w2 2 ->
  Urec w1 -> Urec w2 -> forall (k : int), 2%:~R <= k -> w1 k = w2 k.
  apply: (Urec1P _ v) => //; rewrite /ba_casoratian /v b2_eq b3_eq.
  rewrite int.shift2Z a2_eq a3_eq.
  by field; ring_lia.
have hUrec w k : Urec w -> 2%:~R <= k -> w (int.shift 1 k) = (c0 k / c1 k) * w k.
  move=> wUrec le2k; rewrite mulrAC; apply: canRL (mulfK _) _.
    by rewrite /c1 /annotated_recs_c.P_cf2 expf_eq0; ring_lia.
  by apply/eqP; rewrite [_ * c1 k]mulrC -subr_eq0 wUrec.
move=> ic Uw1 Uw2 [] //; elim => // [[]] // [] // k ihk _.
by rewrite -[_.+3]addn1 PoszD -int.zshiftP !hUrec // ihk.
Qed.
```

### child `b_Sn2`: [`theories/reduce_order.v` lines 250-260](https://github.com/rocq-community/apery/blob/97f0c01bec4282c4504c0225a71ff0e75aeab115/theories/reduce_order.v#L250-L260) ([local copy](code/theories/reduce_order.v))

```coq
Lemma b_Sn2 (n : int) : n >= 0 -> annotated_recs_c.P_horner b n = 0.
Proof.
move=> hn.
case: (altP (n =P 0)) => [-> | h0]; first exact: b_Sn2_at_0.
case: (altP (n =P 1)) => [-> | h1]; first exact: b_Sn2_at_1.
pose p : int := n - (2 : int); simpl in p.
have hnp : n = p + (2 : int) by rewrite /p addrNK.
have {hn h0 h1} le0p : 0 <= p by lia.
have {le0p hnp p} h : (2 : int) <= n by rewrite hnp lerDr.
exact: b_Sn2_almost.
Qed.
```

### child `a_Sn2`: [`theories/algo_closures.v` lines 43-44](https://github.com/rocq-community/apery/blob/97f0c01bec4282c4504c0225a71ff0e75aeab115/theories/algo_closures.v#L43-L44) ([local copy](code/theories/algo_closures.v))

```coq
Lemma a_Sn2 (n : int) : 2 <= n :> int -> annotated_recs_c.P_horner a n = 0.
Proof. by move=> h; exact: (ops_for_a.recAperyA c_ann h). Qed.
```

### child `b2_eq`: [`theories/initial_conds.v` lines 56-57](https://github.com/rocq-community/apery/blob/97f0c01bec4282c4504c0225a71ff0e75aeab115/theories/initial_conds.v#L56-L57) ([local copy](code/theories/initial_conds.v))

```coq
Lemma b2_eq : b 2 = rat_of_Z 351 / rat_of_Z 4.
Proof. solve_b_evaluation. Qed.
```

### child `b3_eq`: [`theories/initial_conds.v` lines 59-60](https://github.com/rocq-community/apery/blob/97f0c01bec4282c4504c0225a71ff0e75aeab115/theories/initial_conds.v#L59-L60) ([local copy](code/theories/initial_conds.v))

```coq
Lemma b3_eq : b 3 = rat_of_Z 62531 / rat_of_Z 36.
Proof. solve_b_evaluation. Qed.
```

### child `a2_eq`: [`theories/initial_conds.v` lines 72-73](https://github.com/rocq-community/apery/blob/97f0c01bec4282c4504c0225a71ff0e75aeab115/theories/initial_conds.v#L72-L73) ([local copy](code/theories/initial_conds.v))

```coq
Lemma a2_eq : a 2 = rat_of_Z 73.
Proof. solve_a_evaluation. Qed.
```

### child `a3_eq`: [`theories/initial_conds.v` lines 75-76](https://github.com/rocq-community/apery/blob/97f0c01bec4282c4504c0225a71ff0e75aeab115/theories/initial_conds.v#L75-L76) ([local copy](code/theories/initial_conds.v))

```coq
Lemma a3_eq : a 3 = rat_of_Z 1445.
Proof. solve_a_evaluation. Qed.
```

The glue (the proof of `ba_casoratianE`) first `pose`s the closed form
`v k = 6%:Q / (k%:Q + 1) ^ 3`, the recurrence coefficients `c1 := P_cf2` and
`c0 := P_cf0` (where `P_cf2 n = (n+2)^3`, `P_cf0 n = (n+1)^3`), and the order-1
recurrence predicate

```
Urec w := forall k, 2 <= k -> c1 k * w (k+1) - c0 k * w k = 0
```

i.e. `(k+2)^3 · w(k+1) = (k+1)^3 · w k`. It then proves `uUrec : Urec
ba_casoratian` (the casoratian satisfies the recurrence) and `vUrec : Urec v`
(the closed form does), states the general uniqueness statement `Urec1P`, proves
it with the helper `hUrec`, and closes by `apply: (Urec1P _ v)`.

The lemma graph:

```
ba_casoratianE
 ├─ uUrec : Urec ba_casoratian   uses b_Sn2, a_Sn2          (then ring)
 ├─ vUrec : Urec v                closed by field; ring_lia  (no project lemma)
 ├─ w1 2 = w2 2                   uses b2_eq, b3_eq, a2_eq, a3_eq  (then field; ring_lia)
 └─ Urec1P                        general uniqueness, proved inline via hUrec + induction
```

Why each child is a good leaf:

- `b_Sn2` and `a_Sn2` are the order-2 recurrences of `b` and `a`
  (`annotated_recs_c.P_horner b n = 0`, `annotated_recs_c.P_horner a n = 0`);
  rewriting the casoratian with them turns `uUrec` into an identity closed by
  `ring`. Each is a self-contained recurrence statement: `a_Sn2` closes in one
  line from the closures development (`exact: (ops_for_a.recAperyA c_ann h)`),
  and `b_Sn2` splits on `n = 0` / `n = 1` and otherwise hands off to the named
  sibling `b_Sn2_almost`.
- `b2_eq`, `b3_eq`, `a2_eq`, `a3_eq` are the evaluations of `b` and `a` at 2 and
  3; together they rewrite `ba_casoratian 2` to `v 2`, discharging the initial
  condition `w1 2 = w2 2`. Each is a one-line `field` computation
  (`solve_b_evaluation` / `solve_a_evaluation`).

The generalisation is the point: `Urec1P` ranges over arbitrary `w1 w2 :
int -> rat`, so it is stated and proved independently of the casoratian, and the
casoratian identity becomes the instantiation plus three leaf obligations
(`uUrec`, `vUrec`, the initial condition). The author marks this in a comment on
lines 45-46.

The `shape.depth` of 7 is the chain of project lemmas below the main theorem
through `b_Sn2`, all in `reduce_order.v`:
`ba_casoratianE → b_Sn2 → b_Sn2_almost → b'_eq_b → b'_eq_b_reduction → b'_Sn4 →
b'_Sn2_rew → b'_rec_eq`.

## Why it is good

1. The parent site (the glue) is 35 lines long, and those 35 lines assemble six
   project lemmas plus one general uniqueness lemma (check; the site spans
   lines 24-58).
2. The parent cites `b_Sn2` — the recurrence of `b` that feeds `uUrec` (check;
   line 35).
3. The parent cites `a_Sn2` — the recurrence of `a` that feeds `uUrec` (check;
   line 35).
4. The parent site contains no `admit`/`Admitted`/`Axiom`/`axiom`: the glue
   closes from the lemmas with `ring`, `field` and `ring_lia`, not a hole
   (check; lines 24-58).
5. The author flags the generalisation as deliberate: "this step below is only
   the fact that U is a rec of order 1 : should be obtained from something more
   general" (author-statement; lines 45-46).

In my opinion the detail worth copying is the *three-way split* of the
instantiation: the glue keeps "which sequence" out of the uniqueness lemma by
making the recurrence (`uUrec`, `vUrec`) and the initial value (`w1 2 = w2 2`)
separate leaves, so the closed form's recurrence is proved by `field` alone
while the casoratian's recurrence is proved from the two named order-2
recurrences.

## When to use it, and when not

Use it when two quantities each satisfy the same recurrence and agree at one
initial value: a single general uniqueness lemma ("same recurrence and same start
imply equal") settles the identity, and each side's recurrence becomes a separate
leaf. Avoid it when the two sides do not share a recurrence, when the recurrence
is of higher order than 1 (the uniqueness induction, and its
coefficient-nonvanishing side conditions, grow), or when the initial values
differ.

## Consequences

The generalisation creates three obligations at the point of instantiation:
`Urec` for each sequence (`uUrec`, `vUrec`) and the initial-value match
`w1 2 = w2 2`. The uniqueness lemma itself relies on the recurrence being
genuinely order 1 with a non-zero leading coefficient (`c1 k = (k+2)^3 != 0`,
discharged by `expf_eq0`), so that each term determines the next via
`w (k+1) = (c0 k / c1 k) * w k`. If the leading coefficient could vanish at some
`k`, the step fails and the lemma must be restricted to a range where it does
not.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/docker-action.yml (Docker CI) triggers on push to master (default branch) and builds the opam package coq-mathcomp-apery.opam via coq-community/docker-coq-action; the opam build is 'make', which compiles every file in _CoqProject, including theories/b_over_a_props.v (listed at line 19). Pinned commit 97f0c01 is HEAD (default branch) of rocq-community/apery. | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: b_Sn2@theories/b_over_a_props.v:35, a_Sn2@theories/b_over_a_props.v:35, b2_eq@theories/b_over_a_props.v:49, b3_eq@theories/b_over_a_props.v:49, a2_eq@theories/b_over_a_props.v:50, a3_eq@theories/b_over_a_props.v:50; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 8 file(s) byte-identical at 97f0c01bec4282c4504c0225a71ff0e75aeab115 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(ba_casoratianE, 35) -> lines: site ba_casoratianE has 35 lines | check_claims.py |
| 2 | verified | cites(parent, b_Sn2) -> cites: b_Sn2 occurs at theories/b_over_a_props.v:35 | check_claims.py |
| 3 | verified | cites(parent, a_Sn2) -> cites: a_Sn2 occurs at theories/b_over_a_props.v:35 | check_claims.py |
| 4 | verified | no_sorry(theories/b_over_a_props.v, 24-58) -> no_sorry: none of admit, Admitted, Axiom, axiom in theories/b_over_a_props.v:24-58 | check_claims.py |
| 5 | verified | Read code/theories/b_over_a_props.v lines 45-46 (provenance byte-identical): line 45 '(* this step below is only the fact that U is a rec of order 1 : should be *)', line 46 '(* obtained from something more general... *)'. The quoted author comment matches, and it sits immediately before the 'suff {uUrec vUrec v} Urec1P ...' that states the general order-1 uniqueness lemma, so the authors do flag the uniqueness step as a general fact that belongs apart. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent ba_casoratianE (b_over_a_props.v:24-58) is exactly a generalise-then-instantiate: it poses v/c1/c0/Urec, proves uUrec and vUrec, suffices the general uniqueness Urec1P over arbitrary w1 w2, instantiates via apply:(Urec1P _ v), and closes by field/ring_lia; ends Qed with no admit/Admitted. The 6 children (b_Sn2, a_Sn2, b2_eq, b3_eq, a2_eq, a3_eq) are exactly the 6 project lemmas the glue cites (lines 35, 49, 50), their statements are verbatim, and closing methods match (a_Sn2 exact recAperyA; the four *_eq by solve_a/b_evaluation; b_Sn2 by case altP n=0/n=1 then exact b_Sn2_almost). Shape numbers are right: glue_lines 35 (24-58), child_lines [11,2,2,2,2,2] (250-260, 43-44, 56-57, 59-60, 72-73, 75-76), direct_lemmas 6, and depth 7 verified as the chain ba_casoratianE -> b_Sn2 -> b_Sn2_almost -> b'_eq_b -> b'_eq_b_reduction -> b'_Sn4 -> b'_Sn2_rew -> b'_rec_eq (reduce_order.v:259,227,207,195-198,93,57). | reviewer-correctness |
| generality | accept | Move is stated transferably: applicability.goal_shape and the README's use/avoid text generalize from the casoratian to 'same order-1 recurrence + same initial value => equal', which is reusable for any such pair. Avoid-when is honest and specific: no shared recurrence, higher order (uniqueness induction and coefficient-nonvanishing side conditions grow), differing initial values. Consequences are specific and match the code: three instantiation obligations (uUrec, vUrec, w1 2 = w2 2) and the order-1 / non-zero leading coefficient condition c1 k = (k+2)^3 != 0 discharged by expf_eq0 at line 55. Leaf goodness is stated: b_Sn2/a_Sn2 are self-contained recurrence statements closing in one line (a_Sn2 via recAperyA, b_Sn2 by a 0/1 case split then b_Sn2_almost), and b2_eq/b3_eq/a2_eq/a3_eq are one-line field computations via solve_a/b_evaluation. Minor, non-blocking: README omits the third avoid_when condition present in entry.json ('one side's recurrence cannot be stated without the other's'). | reviewer-generality |
| provenance-licence | accept | Provenance passes: check_provenance.py reports 8 files byte-identical at 97f0c01bec4282c4504c0225a71ff0e75aeab115. Commit, repo path and licence (CECILL-C) are consistent across entry.json, README.md, sources/apery/SOURCE.md and source.json; upstream-LICENSE is CeCILL-C text, matching the recorded licence. All 8 file permalinks and 7 site permalinks point at the pinned commit with paths matching the copied code/ files (8 files, include/ann_c.v + 7 theories). Cited line ranges (parent 24-58; children reduce_order.v 250-260, algo_closures.v 43-44, initial_conds.v 56-57/59-60/72-73/75-76) reproduce exactly in the copied files. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/rocq-community/apery at commit `97f0c01bec4282c4504c0225a71ff0e75aeab115`, under `CECILL-C`; see the [source note](../../sources/apery/SOURCE.md) for the licence text and attribution.
