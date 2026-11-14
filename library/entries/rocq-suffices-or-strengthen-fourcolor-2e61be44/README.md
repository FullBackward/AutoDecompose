# Strengthen the goal to arity x in iota 5 7 in the four-colour unavoidability theorem

| | |
|---|---|
| Kind | instance |
| Move | suffices-or-strengthen |
| Language | rocq |
| Status | accepted |
| Source | [fourcolor](../../sources/fourcolor/SOURCE.md) at `c1d6b1cd5288` |
| Licence | `CECILL-B` |
| Licence recorded | 2026-11-14T09:57:23Z |

## Intent

The main unavoidability theorem — reducibility implies no minimal
counterexample — is reduced by `suffices` to showing that the high-score vertex
given by `posz_dscore` has arity in `iota 5 7` (the seven arities 5..11). The
per-arity exclusion lemmas then close the original goal from that range, while
seven score/fit lemmas close the range itself.

## The decomposition

### parent `unavoidability`: [`theories/proof/unavoidability.v` lines 20-34](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/unavoidability.v#L20-L34) ([local copy](code/theories/proof/unavoidability.v))

```coq
Lemma unavoidability : reducibility -> forall G, ~ minimal_counter_example G.
Proof.
move=> red_check G cexG; have [x pos_x] := posz_dscore cexG.
suffices: arity x \in iota 5 7.
  rewrite !inE exclude5 ?exclude6 ?exclude7 ?exclude8 //=.
  by rewrite exclude9 ?exclude10 ?exclude11.
rewrite mem_iota (cexG : pentagonal G) (@dscore_cap1 G 5) {x pos_x}// => y.
have{y} [x ->]: {x | y = face (face x)} by exists (inv_face2 y); rewrite !nodeK.
pose n := arity x; pose rf := DruleFork (DruleForkValues n).
rewrite (dbound1_eq rf) // lez_nat.
have [Dn | /source_drules_range-> //] := boolP (Pr58 n).
have fit_x: exact_fitp x (pcons_ n) by apply: exact_fitp_pcons_ cexG _.
apply: (check_dbound1P (no_fit_the_redpart red_check cexG)) fit_x _ => //.
by case/or4P: Dn @rf => /eqP->.
Qed.
```

### child `posz_dscore`: [`theories/proof/discharge.v` lines 212-217](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/discharge.v#L212-L217) ([local copy](code/theories/proof/discharge.v))

```coq
Lemma posz_dscore : exists x : G, dscore x > 0.
Proof.
apply/existsP; have: ~~ (0 <= - (120 : int)) by []; apply: contraR.
rewrite negb_exists -dscore_roots -sumrN => /forallP-score_le0.
by apply: sumr_ge0 => x _; rewrite oppr_ge0 leNgt.
Qed.
```

### child `dscore_cap1`: [`theories/proof/discharge.v` lines 378-390](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/discharge.v#L378-L390) ([local copy](code/theories/proof/discharge.v))

```coq
Lemma dscore_cap1 (m : nat) :
   (forall y : G, dscore1 y <= m) ->
  forall x : G, 0 < dscore x -> forall d, (59 < (10 - m) * d -> arity x < d)%N.
Proof.
move=> ub_m x pos_x d max_m; apply: contraLR pos_x; rewrite -leqNgt => ledx.
have ltm10: (m < 10)%N by rewrite -subn_gt0; case: (10 - m)%N max_m.
have{max_m}: 60%:Z <= ((10 - m) * arity x)%:Z.
  by rewrite lez_nat (leq_trans max_m) ?leq_mul.
rewrite -leNgt -lerBrDr lerBlDl add0r => /le_trans-> //.
rewrite !PoszM -!mulrzz -![_ *~ _]sumr_const -sumrB ler_sum // => y _.
rewrite -(lerD2r m%:Z) -PoszD subnK 1?ltnW // addrAC.
by rewrite lerBrDr lerD2l lerBlDr ler_wpDr.
Qed.
```

### child `dbound1_eq`: [`theories/proof/discharge.v` lines 336-341](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/discharge.v#L336-L341) ([local copy](code/theories/proof/discharge.v))

```coq
Lemma dbound1_eq : dscore1 (face (face x)) = dbound1 rs x.
Proof.
congr _%:Z; rewrite /rs /source_drules; case: rf => _ _ [].
elim: the_drules => //= r dr ->.
by rewrite /exact_fitp /inv_face2 !faceK nFx eq_sym; case: ifP.
Qed.
```

### child `source_drules_range`: [`theories/proof/discharge.v` lines 392-399](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/discharge.v#L392-L399) ([local copy](code/theories/proof/discharge.v))

```coq
Lemma source_drules_range : ~~ Pr58 nhub -> rs = [::].
Proof.
rewrite /rs /source_drules; case: rf => _ _ [] not_u58.
have Eu: (fun p => size_part p == nhub)
            =1 (fun n => ~~ Pr58 n && (n == nhub)) \o size_part.
- by move=> p; rewrite /= andbC; case: eqP => // ->.
by rewrite /pick_source_drules (eq_filter Eu).
Qed.
```

### child `exact_fitp_pcons_`: [`theories/proof/part.v` lines 1253-1254](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/part.v#L1253-L1254) ([local copy](code/theories/proof/part.v))

```coq
Lemma exact_fitp_pcons_ (x : G) : exact_fitp x (pcons_ (arity x)).
Proof. by rewrite /exact_fitp fitp_pcons_; elim (arity x). Qed.
```

### child `check_dbound1P`: [`theories/proof/hubcap.v` lines 142-158](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/hubcap.v#L142-L158) ([local copy](code/theories/proof/hubcap.v))

```coq
Lemma check_dbound1P (x : G) p ns :
  arity x = nhub -> exact_fitp x p -> check_dbound1 p ns -> dbound1 rs0 x <= ns.
Proof.
move=> nFx; rewrite /check_dbound1 /rs0 /source_drules.
case: rf => rs _ _; move: (size rs + 1) => m.
elim: m ns rs p => // m IHm ns [|r rs] //= p fit_xp.
case: ifP => [/(leq_trans _)-> //| _ /andP[]].
  by rewrite -add1n leq_add ?leq_b1 ?count_size.
case fit_xr: (fitp x r); last by clear 1; apply: IHm => //=; rewrite fit_xr.
set p1 := meet_part p r.
have Efit_p1: exact_fitp x p1 by apply: exact_fitp_meet.
have [_ /sort_drulesP[dns rs1]] := andP Efit_p1.
case Dns1: (ns - dns) => [|ns1]; first by move/redpP/negP/(_ Efit_p1).
have dns_lt_ns: dns < ns by rewrite -subn_gt0 Dns1.
move=> bound_p1 _; rewrite -(subnKC (ltnW dns_lt_ns)) Dns1 /=.
by rewrite addnCA leq_add2l ltnS; apply: IHm bound_p1.
Qed.
```

### child `no_fit_the_redpart`: [`theories/proof/present.v` lines 168-184](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/present.v#L168-L184) ([local copy](code/theories/proof/present.v))

```coq
Lemma no_fit_the_redpart G :
    minimal_counter_example G ->
  forall (x : G) p', the_redpart p' -> ~~ exact_fitp x p'.
Proof.
move=> cexG x p1 redp1; apply: (no_fit_redpart cexG) p1 redp1 x => x.
move Dq: the_quiz_tree => q.
have{q Dq} <-: cfquiz_tree the_configs = q by exact <: Dq.
have:= red_check; rewrite /reducibility; move Dcfs: the_configs => cfs red_cfs.
apply/negP; case/(qzt_fit_cfquiz cexG)=> [cf ltcf [qz fit_qz [cf_ok [u qz_u]]]].
wlog{x fit_qz} [x fit_qz]: G cexG / exists x : G, fitqz x qz.
  move=> IH; case: fit_qz; apply: IH; first exact: cexG.
  exact: minimal_counter_example_mirror.
have red_cf: cfreducible (nth cf000 cfs cf).
  by have:= red_check (leq0n cf); rewrite Dcfs => /(_ ltcf).
have embedG := quiz_preembedding cexG cf_ok qz_u fit_qz.
exact: not_embed_reducible cexG cf_ok embedG red_cf.
Qed.
```

How the parts fit. The lemma graph below the parent is:

```
unavoidability                                     (unavoidability.v 20-34)
├── posz_dscore                                    (discharge.v 212-217)  — a vertex x with 0 < dscore x
├── suffices: arity x \in iota 5 7                 (unavoidability.v 23)   — the strengthen step
│     ├── discharge: exclude5..exclude11           (present5..present11.v) — closes the original goal
│     └── the strengthened range, closed by:
│           ├── pentagonal G  (from cexG)          — arity x >= 5 (lower bound)
│           ├── dscore_cap1                        (discharge.v 378-390)  — arity x < 12 (upper bound)
│           └── dbound1_eq                         (discharge.v 336-341)  — dscore1 = dbound1 rs x
│                 ├── source_drules_range          (discharge.v 392-399)  — rs = [::] off Pr58
│                 ├── exact_fitp_pcons_            (part.v 1253-1254)     — the fitting hypothesis
│                 ├── no_fit_the_redpart           (present.v 168-184)    — the redpart hypothesis
│                 └── check_dbound1P               (hubcap.v 142-158)     — dbound1 rs0 x <= 5
│                       └── sort_drulesP (discharge.v 356) ── sort_dbound1_eq (discharge.v 343)
```

The glue first obtains the witness: `have [x pos_x] := posz_dscore cexG` gives
a vertex `x` with `0 < dscore x`, which together with `cexG` makes `(cexG,
pos_x)` a `valid_hub` (present.v line 75). It then states the strengthened
goal with `suffices: arity x \in iota 5 7` — `iota 5 7` is the seven-element
list `[5;6;7;8;9;10;11]`, so this is `5 <= arity x < 12`.

The suffices produces two goals. The first, the original `~ minimal_counter_example
G` under the new hypothesis, is closed at lines 24-25 by the per-arity exclusion
lemmas `exclude5`..`exclude11` (from `present5.v`..`present11.v`): each says
`excluded_arity k`, i.e. a valid hub cannot have arity `k`, so `arity x \in iota
5 7` contradicts minimality. These seven lemmas are the results collated from
the `presentNN.v` files — the author's header comment says exactly that the
theorem is "collating the result of all the presentNN.v files". They are the
discharge side of the suffices, not the argument for the strengthened goal, so
they are listed here rather than as children.

The second goal, `arity x \in iota 5 7`, is closed at lines 26-33. Its lower
bound `5 <= arity x` comes from `(cexG : pentagonal G)` (a minimal
counterexample is pentagonal, i.e. every vertex has arity >= 5). Its upper bound
`arity x < 12` comes from `dscore_cap1` instantiated at `m = 5`: the cap says
that if every vertex has `dscore1 <= 5` and `0 < dscore x`, then `arity x < d`
whenever `59 < (10 - 5) * d`, and `d = 12` satisfies `59 < 60`. What remains is
the premise `forall y, dscore1 y <= 5`, and this is where the four fork lemmas
combine: `dbound1_eq` rewrites `dscore1 (face (face x))` into `dbound1 rs x` (the
count of source discharge rules fitting `x`); `source_drules_range` handles the
case where the arity is outside `Pr58` by making `rs` empty; `exact_fitp_pcons_`
supplies the fit `exact_fitp x (pcons_ n)`; `no_fit_the_redpart` supplies the
redpart hypothesis (no reducible part fits a minimal counterexample); and
`check_dbound1P` turns all of that into the bound `dbound1 rs0 x <= 5`. The
remaining finite case (`n \in {5,6,7,8}`) is discharged by `case/or4P: Dn @rf =>
/eqP->` at line 34.

Why each child is a good leaf — a self-contained statement whose proof closes on
its own or from named siblings:

- `posz_dscore` closes by contraposition from its sibling `dscore_roots` (the
  total score over the face roots is 120, discharge.v line 201) and `sumr_ge0`:
  if no vertex had positive score the sum would be non-positive.
- `dscore_cap1` is a self-contained arithmetic cap and closes on its own by
  `apply: contraLR pos_x` plus ring/order rewriting — no project lemma.
- `dbound1_eq` closes on its own by `elim: the_drules`, induction over the
  finite list of discharge rules.
- `source_drules_range` closes on its own by a filter-extensionality rewrite
  `eq_filter`, given that `Pr58` picks out the arities `5,6,7,8`.
- `exact_fitp_pcons_` closes by its sibling `fitp_pcons_` (the line above it)
  and `elim (arity x)`.
- `check_dbound1P` closes by induction on the bound counter, using the named
  siblings `sort_drulesP` and `exact_fitp_meet`; `sort_drulesP` itself closes by
  `sort_dbound1_eq` — the depth-3 chain recorded in the shape.
- `no_fit_the_redpart` closes by `no_fit_redpart` and the reducibility/quiz-tree
  machinery (`qzt_fit_cfquiz`, `not_embed_reducible`), a deeper but fully named
  sibling chain.

Four of the seven children live in `discharge.v` (the score/discharge
development); one each live in `part.v` (`exact_fitp_pcons_`), `hubcap.v`
(`check_dbound1P`) and `present.v` (`no_fit_the_redpart`), so all five files are
copied.

## Why it is good

1. The glue `unavoidability` is 15 lines over 7 direct lemmas, whose child sites
   span 6, 13, 6, 8, 2, 17 and 17 lines; the bound-check child `check_dbound1P`
   closes through a chain of 3 project lemmas down to `sort_dbound1_eq`
   (`measurement`, spans at
   [L20-L34](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/unavoidability.v#L20-L34),
   [discharge L212-L217](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/discharge.v#L212-L217),
   [L378-L390](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/discharge.v#L378-L390),
   [L336-L341](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/discharge.v#L336-L341),
   [L392-L399](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/discharge.v#L392-L399),
   [part L1253-L1254](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/part.v#L1253-L1254),
   [hubcap L142-L158](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/hubcap.v#L142-L158),
   [present L168-L184](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/present.v#L168-L184)).
2. The parent `unavoidability` site is 15 lines long (`check`,
   [permalink](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/unavoidability.v#L20-L34)).
3. The parent site cites `suffices` (`check`,
   [permalink](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/unavoidability.v#L20-L34)).
4. No `admit`, `Admitted` or `Axiom` closes the parent's proof (`check`,
   [permalink](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/unavoidability.v#L20-L34)).
5. The authors describe the theorem as "The main unavoidability theorem:
   reducibility implies no minimal counter example, collating the result of all
   the presentNN.v files" (`author-statement`,
   [header comment](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/unavoidability.v#L11-L14)).

In my opinion the detail worth copying is that the strengthen step is chosen so
that its two sides are both already proved elsewhere: the strengthened range
`arity x \in iota 5 7` is *implied* by the score/fit lemmas and *excludes* the
goal via the `presentNN` lemmas. The `suffices` is cheap only because the range
was picked to sit exactly on top of both bodies of machinery — a different
window (say arity 5..12) would break the discharge, and a wider cap would break
the bound.

## When to use it, and when not

Use it when a goal is a contradiction (`reducibility -> forall G, ~
minimal_counter_example G`) and there is a finite range for some invariant of a
witness that is (a) provable from a cap/bound argument and (b) excluded
value-by-value by lemmas already collated from elsewhere. The strengthened
statement `arity x \in iota 5 7` is smaller and more mechanical than the
original, and its two sides are both ready-made.

Avoid it when the strengthened statement does not actually imply the original —
the exclusions must cover the whole range, or the discharge fails. Also avoid it
when the cap argument is itself the hard part: here the real content `forall y,
dscore1 y <= 5` is pushed into `dscore_cap1` plus the fork machinery
(`dbound1_eq`, `check_dbound1P`, …), and the move works only because that
machinery already exists.

## Consequences

The `suffices` creates two goals: the original under the suffices hypothesis
(closed by `exclude5..exclude11`) and the strengthened statement itself. The
strengthened range must line up exactly with what the exclusions rule out — a
gap (an arity >= 12) would leave the discharge open, and a different cap `m` in
`dscore_cap1` changes the window. The move fixes the instantiation `m = 5`,
which only closes because `59 < 5 * 12`; the substantive bound (`dscore1 <= 5`
for every vertex) is not removed but routed through the fork machinery, so the
proof is only as strong as `check_dbound1P` and `no_fit_the_redpart`.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/docker-action.yml triggers on push to master (default branch) and runs 'opam install coq-fourcolor', building the whole library; _CoqProject line 126 lists theories/proof/unavoidability.v; pinned commit c1d6b1cd5288bea4b067aac13cdde3c18dffe018 is HEAD of default branch master | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: posz_dscore@theories/proof/unavoidability.v:22, dscore_cap1@theories/proof/unavoidability.v:26, dbound1_eq@theories/proof/unavoidability.v:29, source_drules_range@theories/proof/unavoidability.v:30, exact_fitp_pcons_@theories/proof/unavoidability.v:31, check_dbound1P@theories/proof/unavoidability.v:32, no_fit_the_redpart@theories/proof/unavoidability.v:32; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 5 file(s) byte-identical at c1d6b1cd5288bea4b067aac13cdde3c18dffe018 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | parent unavoidability.v:20-34 = 15 lines (also claim 2); 7 direct children cited (glue-cites-children); child site line counts confirmed in copied code: discharge.v:212-217=6 (posz_dscore), 378-390=13 (dscore_cap1), 336-341=6 (dbound1_eq), 392-399=8 (source_drules_range), part.v:1253-1254=2 (exact_fitp_pcons_), hubcap.v:142-158=17 (check_dbound1P), present.v:168-184=17 (no_fit_the_redpart); chain check_dbound1P -> sort_drulesP -> sort_dbound1_eq confirmed: hubcap.v:153 'have [_ /sort_drulesP[dns rs1]] := andP Efit_p1', discharge.v:356-357 sort_drulesP whose proof rewrites sort_dbound1_eq, discharge.v:343 Lemma sort_dbound1_eq | verifier |
| 2 | verified | lines(parent, 15) -> lines: site parent has 15 lines | check_claims.py |
| 3 | verified | cites(parent, suffices) -> cites: suffices occurs at theories/proof/unavoidability.v:23 | check_claims.py |
| 4 | verified | no_sorry(theories/proof/unavoidability.v, 20-34) -> no_sorry: none of admit, Admitted, Axiom, axiom in theories/proof/unavoidability.v:20-34 | check_claims.py |
| 5 | verified | unavoidability.v:11-14 header comment reads '(* The main unavoidability theorem: reducibility implies no minimal counter *) (* example, collating the result of all the presentNN.v files. *)', matching the quoted author statement | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent unavoidability (unavoidability.v 20-34, 15 lines) reduces via 'suffices: arity x \in iota 5 7' at line 23; verified all 7 child statements verbatim against code (posz_dscore discharge.v 212-217, dscore_cap1 378-390, dbound1_eq 336-341, source_drules_range 392-399, exact_fitp_pcons_ part.v 1253-1254, check_dbound1P hubcap.v 142-158, no_fit_the_redpart present.v 168-184) and each closed_by matches its proof. Parent cites all 7 children directly at lines 22,26,29,30,31,32(2x) and closes with Qed; no sorry/admit/axiom. Shape numbers right: direct_lemmas=7, glue_lines=15, child_lines=[6,13,6,8,2,17,17], depth=3 via check_dbound1P->sort_drulesP(discharge.v 356)->sort_dbound1_eq(343). Minor prose nit only: README says case/or4P is 'at line 34' but it is line 33 (34 is Qed) - immaterial to correctness. | reviewer-correctness |
| generality | accept | Move is stated abstractly (goal_shape: contradiction -> suffices to finite membership f x in iota a b on a witness, bounded below by structural hypothesis and above by a cap lemma; use_when/avoid_when give general conditions), so it applies beyond the four-colour example. When-not-to-use and consequences are honest and specific: they acknowledge the move only works because the range iota 5 7 lines up exactly with the excluded arities 5..11 and that the real content (dscore1 <= 5) is pushed into dscore_cap1 plus the fork machinery rather than removed; arithmetic checked (m=5, d=12 gives 59<60). Good-leaf question is answered: 'Why each child is a good leaf' states each child closes on its own or from named siblings (verified against code: posz_dscore cites dscore_roots/sumr_ge0; dscore_cap1 self-contained; dbound1_eq elim the_drules; source_drules_range eq_filter; exact_fitp_pcons_ uses fitp_pcons_ at part.v:1252; check_dbound1P uses sort_drulesP/sort_dbound1_eq at discharge.v:356/343), and honestly flags check_dbound1P and no_fit_the_redpart as deeper chains. | reviewer-generality |
| provenance-licence | accept | provenance pass: check_provenance.py reports 5 file(s) byte-identical at c1d6b1cd5288bea4b067aac13cdde3c18dffe018. Commit c1d6b1cd5288bea4b067aac13cdde3c18dffe018 is identical across entry.json, README, sources/fourcolor/SOURCE.md and source.json. Licence CECILL-B recorded identically in all four and upstream-LICENSE is the CeCILL-B text. Every site permalink uses the same pinned commit and its line range matches the local copy (parent 20-34, header 11-14, discharge 212-217/336-341/378-390/392-399, part 1253-1254, hubcap 142-158, present 168-184). Traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/math-comp/fourcolor at commit `c1d6b1cd5288bea4b067aac13cdde3c18dffe018`, under `CECILL-B`; see the [source note](../../sources/fourcolor/SOURCE.md) for the licence text and attribution.
