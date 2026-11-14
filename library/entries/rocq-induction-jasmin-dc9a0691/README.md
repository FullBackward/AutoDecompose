# cmd_rect induction over commands proves the array-init pass preserves function equivalence

| | |
|---|---|
| Kind | instance |
| Move | induction |
| Language | rocq |
| Status | accepted |
| Source | [jasmin](../../sources/jasmin/SOURCE.md) at `211aa617685e` |
| Licence | `MIT` |

## Intent

The array-init pass (`add_init_prog`) inserts an array initialisation before
the first use of an array variable. `it_add_init_callP` proves that this pass
preserves whole-function equivalence `wiequiv_f`, by structural induction over
the command language with `cmd_rect`. Each command form is closed by one of
three auxiliary lemmas, and the finished result is threaded into the
compiler's per-pass simulation chain.

## The decomposition

### parent `it_add_init_callP`: [`proofs/compiler/array_init_proof.v` lines 200-254](https://github.com/jasmin-lang/jasmin/blob/211aa617685e0a0b074646fc27c85d017aced9cb/proofs/compiler/array_init_proof.v#L200-L254) ([local copy](code/proofs/compiler/array_init_proof.v))

```coq
Lemma it_add_init_callP fn : wiequiv_f p p' ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof.
 apply wequiv_fun_ind => {}fn _ fs _ [<- <-] fd hget.
 exists (add_init_fd fd).
 + by rewrite get_map_prog hget.
 move=> {hget}.
 rewrite /add_init_fd /=.
 set I := (I in add_init_c _ I _).
 set cm := add_init_c _ _ _.
 set fd' := with_body _ _.
 move=> s1 hinit.
 exists s1=> //; exists (cmpl_inv I), (cmpl_inv cm.2); split => //.
 + move: hinit; rewrite /initialize_funcall.
   t_xrbindP => vs hargs s0 hini hw.
   split => //; split => //.
   move=> x hx.
   move: hw; rewrite (write_vars_lvals _ gd) => /disjoint_eq_ons -/(_ (Sv.singleton x)) <-.
   + by move: hini => [<-] /=; rewrite Vm.initP.
   + by rewrite -/I /disjoint /is_true Sv.is_empty_spec; SvD.fsetdec.
   by SvD.fsetdec.
 2:{
   move=> s2 t2 fs2 h.
   rewrite /finalize_funcall; t_xrbindP => vs hget vs' hmap <-.
   eexists; last by eauto.
   case: h => [<- <- [_ h]].
   have -> /= : get_var_is (~~ direct_call) (evm t2) (f_res fd') = ok vs.
   + by rewrite -hget; apply mapM_ext => // y; rewrite /get_var -h.
   by rewrite hmap.
 }

 apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => // {fd fn fs hinit cm I fd' s1}.
 + by move=> I /=; apply wequiv_nil.
 + move=> i c hi hc I /=.
   case heqi: add_init_i => [i' I'].
   case heqc: add_init_c => [c' I''] /=.
   rewrite -cat1s.
   apply wequiv_cat with (cmpl_inv I').
   + by have /= := hi I; rewrite heqi.
   by have /= := hc I'; rewrite heqc.
 1-4, 6-8: by move=> * ii I; apply/it_aux.
 move=> e c1 c2 hc1 hc2 ii I /=.
 case heq1 : add_init_c => [c1' I1].
 case heq2 : add_init_c => [c2' I2] /=.
 apply add_init_auxP.
 + by apply/Sv.is_empty_spec; SvD.fsetdec.
 apply wequiv_if_eq.
 + apply wrequiv_weaken with (st_eq tt) eq => //.
   + by move=> ?? [?? []].
   by apply st_eq_sem_pexpr.
 move=> [].
 + have := hc1 I; rewrite heq1; apply: wequiv_weaken => //=.
   by move=> ??; apply cmpl_inv_incl; SvD.fsetdec.
 have := hc2 I; rewrite heq2; apply: wequiv_weaken => //=.
 by move=> ??; apply cmpl_inv_incl; SvD.fsetdec.
Qed.
```

### child `it_aux`: [`proofs/compiler/array_init_proof.v` lines 183-198](https://github.com/jasmin-lang/jasmin/blob/211aa617685e0a0b074646fc27c85d017aced9cb/proofs/compiler/array_init_proof.v#L183-L198) ([local copy](code/proofs/compiler/array_init_proof.v))

```coq
Lemma it_aux I ii1 ii i :
  wequiv_rec p p' ev ev eq_spec (cmpl_inv I)
     [:: MkI ii i]
     (add_init ii1 I (Sv.union (write_i i) (read_i i)) (MkI ii i)) (cmpl_inv (Sv.union I (write_i i))).
Proof.
  apply add_init_auxP; first by apply/Sv.is_empty_spec; SvD.fsetdec.
  apply wkequivP' => s t.
  have h := [elaborate wequiv_rec_st_eq (p:=p) (p':=p') ev ev erefl [:: MkI ii i]].
  have /(_ s) {h} := wequiv_write1 h.
  apply wkequiv_weaken => //.
  + by move=> s1 s2 [ [-> ->] [?? []]].
  move=> ???? [[-> ->] [_ _ [hundef _]]] [h1] [?? heq2]; split => //; split => //.
  move=> z hz; rewrite -h1.
  + by apply hundef; SvD.fsetdec.
  rewrite write_c_cons write_c_nil write_Ii; SvD.fsetdec.
Qed.
```

### child `add_init_auxP`: [`proofs/compiler/array_init_proof.v` lines 156-181](https://github.com/jasmin-lang/jasmin/blob/211aa617685e0a0b074646fc27c85d017aced9cb/proofs/compiler/array_init_proof.v#L156-L181) ([local copy](code/proofs/compiler/array_init_proof.v))

```coq
Lemma add_init_auxP ii c c' I I' X :
 disjoint I X ->
 wequiv_rec p p' ev ev eq_spec (cmpl_inv I) c c' (cmpl_inv I') ->
 wequiv_rec p p' ev ev eq_spec (cmpl_inv I) c (Sv.fold (add_init_aux ii) X c') (cmpl_inv I').
Proof.
  move=> hdisj hs; rewrite Sv.fold_spec.
  have h : forall x, x \in Sv.elements X -> ~Sv.In x I.
  + by move: hdisj; rewrite /disjoint => /Sv.is_empty_spec hdisj x /Sv_elemsP; SvD.fsetdec.
  elim: Sv.elements c c' h hs => [ | x xs ih] c c' {}hdisj hcc' //=.
  apply ih.
  + by move=> z hz; apply hdisj; rewrite in_cons hz orbT.
  rewrite /add_init_aux.
  case heq: vtype => [||len|] //; case:ifP => _ //.
  rewrite -(cat0s c) -cat1s.
  apply wequiv_cat with (cmpl_inv I) => //.
  apply wequiv_assign_right => s t h.
  rewrite /= /truncate_val /= to_arrK /=.
  eexists.
  + by apply write_varP; split => //; rewrite heq /= eqxx.
  case h => h1 h2 [h3 h4]; split => //; split => //.
  move: h4; rewrite !vm_eq_vm_rel => hu1; apply vm_rel_set_r.
  + move=> _ /=; rewrite h3.
    + by rewrite heq /= eqxx.
    by apply/hdisj/mem_head.
  by apply: vm_relI hu1.
Qed.
```

### child `cmpl_inv_incl`: [`proofs/compiler/array_init_proof.v` lines 138-142](https://github.com/jasmin-lang/jasmin/blob/211aa617685e0a0b074646fc27c85d017aced9cb/proofs/compiler/array_init_proof.v#L138-L142) ([local copy](code/proofs/compiler/array_init_proof.v))

```coq
Lemma cmpl_inv_incl I1 I2 s1 s2 : Sv.Subset I1 I2 -> cmpl_inv I1 s1 s2 → cmpl_inv I2 s1 s2.
Proof.
  move=> hincl [h1 h2 [h3 h4]]; split => //; split => //.
  move=> z hz; apply h3; clear -hincl hz; SvD.fsetdec.
Qed.
```

How the parts fit. The parent is the pass's per-function correctness theorem;
its proof is the glue. It first establishes the function's argument/result
relation with `wequiv_fun_ind`, picks the transformed body `add_init_fd fd`,
and proves the `initialize_funcall` / `finalize_funcall` wrappers directly.
The remaining obligation — the body — is discharged by `cmd_rect` (the command
induction), one goal per constructor. The glue's lemma graph is:

```
it_add_init_callP (parent: cmd_rect induction over the command)
├─ it_aux           — closes the 7 non-branching instruction cases at once,
│                     via the dispatch `1-4, 6-8: apply/it_aux` (line 239)
│     └─ add_init_auxP — it_aux's own proof delegates to add_init_auxP (line 188)
├─ add_init_auxP    — closes the if-case (line 243), folding add_init_aux over
│                     the extra read/written variables of the condition and branches
└─ cmpl_inv_incl    — weakens the invariant in the two if-branch subgoals (lines 251, 253)
```

Each child is a good leaf because its statement is self-contained and its proof
closes on its own or from a sibling:

- `it_aux` (lines 183-198) states that adding the initialisation of a single
  instruction `MkI ii i` is equivalent; it closes by delegating to
  `add_init_auxP` (line 188) for the folding, then `apply wkequivP'` and the
  write-equivalence machinery for the assignment itself.
- `add_init_auxP` (lines 156-181) states that folding `add_init_aux` over a
  disjoint variable set `X` preserves equivalence; it closes by induction over
  `Sv.elements` (line 164) and, in the step, one `wequiv_cat` (line 170) and
  one `wequiv_assign_right` (line 171) that inserts the initialising
  assignment.
- `cmpl_inv_incl` (lines 138-142) states that the invariant `cmpl_inv I` is
  monotone in the variable set; it closes by `SvD.fsetdec` alone (line 141).

The definitions the lemmas refer to (`add_init_i`, `add_init_c`,
`add_init_aux`, `remove_init`) live in
[`array_init.v`](code/proofs/compiler/array_init.v), copied alongside.

## Why it is good

1. The three child lemmas and the parent close with no `admit`, `Admitted` or
   `Axiom` token (`check`, [array_init_proof.v lines 138-254](https://github.com/jasmin-lang/jasmin/blob/211aa617685e0a0b074646fc27c85d017aced9cb/proofs/compiler/array_init_proof.v#L138-L254)).
2. `it_aux` itself is a child that cites its sibling `add_init_auxP` (`check`,
   [array_init_proof.v lines 183-198](https://github.com/jasmin-lang/jasmin/blob/211aa617685e0a0b074646fc27c85d017aced9cb/proofs/compiler/array_init_proof.v#L183-L198)).
3. `add_init_auxP` is used twice below the parent — once by `it_aux` (line
   188) and once directly by the parent (line 243) — so the graph has depth 2
   with a shared leaf (`measurement`,
   [line 188](https://github.com/jasmin-lang/jasmin/blob/211aa617685e0a0b074646fc27c85d017aced9cb/proofs/compiler/array_init_proof.v#L188),
   [line 243](https://github.com/jasmin-lang/jasmin/blob/211aa617685e0a0b074646fc27c85d017aced9cb/proofs/compiler/array_init_proof.v#L243)).
4. The lemma is consumed as one pass of the whole-compiler chain
   (`known-use`, [it_compiler_proof.v line 615](https://github.com/jasmin-lang/jasmin/blob/211aa617685e0a0b074646fc27c85d017aced9cb/proofs/compiler/it_compiler_proof.v#L615)).

In my opinion the detail worth copying is the dispatch `1-4, 6-8: apply/it_aux`
(line 239): seven of the eight instruction constructors are proved by one
shared lemma, and only the branching `Cif` constructor gets a separate
argument, so the induction body is two cases rather than nine.

## When to use it, and when not

Use it when a pass is syntax-directed — its effect on each command constructor
is local, so an induction (`cmd_rect` here) follows the pass's own recursive
definition, and the invariant can be a relation indexed by a set of live
variables (`cmpl_inv I`). It fits the per-pass pattern: one induction theorem
per compiler pass, each a small step in a larger simulation chain.

Avoid it when the pass's effect is non-local (whole-program or global
analysis), when the invariant is not indexable by syntax, or when the
constructors need substantially different reasoning, so a shared dispatch such
as `1-4, 6-8: apply/it_aux` would not fit.

## Consequences

The induction creates one goal per command constructor (here ten: `nil`,
`cons`, and the eight instruction forms). The branching `Cif` case
additionally splits into two branch subgoals, each of which must weaken the
invariant from that branch's variable set to the whole set — exactly the job of
`cmpl_inv_incl`. The `1-4, 6-8` dispatch assumes the seven non-branching
constructors share one shape; a constructor whose init effect differs (say one
that reads and writes overlapping variables) would need its own lemma and
would break the shared step.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .gitlab-ci.yml coq-proof job runs 'make -C proofs', which builds proofs/_CoqProject including compiler/array_init_proof.v (and it_compiler_proof.v); pinned commit 211aa617685e0a0b074646fc27c85d017aced9cb is the tip of main (default branch, compare main...commit = identical) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: it_aux@proofs/compiler/array_init_proof.v:239, add_init_auxP@proofs/compiler/array_init_proof.v:243, cmpl_inv_incl@proofs/compiler/array_init_proof.v:251; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 3 file(s) byte-identical at 211aa617685e0a0b074646fc27c85d017aced9cb | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | no_sorry(proofs/compiler/array_init_proof.v, 138-254) -> no_sorry: none of admit, Admitted, Axiom, axiom in proofs/compiler/array_init_proof.v:138-254 | check_claims.py |
| 2 | verified | cites(it_aux, add_init_auxP) -> cites: add_init_auxP occurs at proofs/compiler/array_init_proof.v:188 | check_claims.py |
| 3 | verified | grep add_init_auxP in code/proofs/compiler/array_init_proof.v: 3 matches at lines 156 (Lemma declaration), 188 (inside it_aux), 243 (inside parent it_add_init_callP) — matches 'used twice below the parent' | verifier |
| 4 | verified | code/proofs/compiler/it_compiler_proof.v line 615 reads 'apply: wiequiv_f_trans_EE_EU; first exact: it_add_init_callP.' — matches the quoted chain step exactly | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Provenance pass (3 files byte-identical at 211aa617685e). Read the cited ranges in the local copies: parent it_add_init_callP (200-254) applies cmd_rect and cites all three children (it_aux@239, add_init_auxP@243, cmpl_inv_incl@251,253); closing methods match the code (it_aux -> apply add_init_auxP@188 then wkequivP'@189; add_init_auxP -> elim Sv.elements@164, wequiv_cat@170/wequiv_assign_right@171; cmpl_inv_incl -> SvD.fsetdec@141). No admit/Admitted/Axiom in 138-254; parent ends Qed@254. Shape numbers verified: direct_lemmas=3, depth=2 (parent->it_aux->add_init_auxP), glue_lines=55 (200-254), child_lines=[16,26,5] (=183-198,156-181,138-142). known-use line 615 in it_compiler_proof.v confirmed (apply: ...; first exact: it_add_init_callP). | reviewer-correctness |
| generality | accept | Generality is stated beyond the example: applicability/use_when give 'syntax-directed pass -> induction follows the definition', 'invariant = relation indexed by a live-variable set', and the per-pass pattern (one induction theorem per pass in a simulation chain). avoid_when is specific and honest (non-local effect, invariant not indexable by syntax, constructors needing divergent reasoning). Consequences are accurate against the code: cmd_rect yields 10 goals (nil+cons+8 instrs, verified in lines 230-253), the 1-4,6-8 dispatch closes 7 (line 239), Cif splits into two branch subgoals weakened by cmpl_inv_incl (lines 249-253). Good leaves for a bounded prover are stated: self-contained statements that close on their own or from a sibling, with short proofs (cmpl_inv_incl by fsetdec alone, add_init_auxP by a short elim + two wequiv lemmas) and child_lines 5/26/16. Minor imprecision, not an objection: the 'reads and writes overlapping variables' example of a differing effect is off, since it_aux already unions write_i/read_i so overlap is handled; a differing effect is really exemplified by Cif (recursion). | reviewer-generality |
| provenance-licence | accept | Commit 211aa617685e0a0b074646fc27c85d017aced9cb is consistent across entry.json, source.json, SOURCE.md and every permalink. Licence MIT is recorded in entry.json, source.json and SOURCE.md and the upstream-LICENSE copy is a genuine MIT licence. All three copied files' sha256 match entry.json exactly; every cited line range (138-142 cmpl_inv_incl, 156 add_init_auxP, 183 it_aux, 200-254 it_add_init_callP, it_compiler_proof.v:615) points to the declared statement. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/jasmin-lang/jasmin at commit `211aa617685e0a0b074646fc27c85d017aced9cb`, under `MIT`; see the [source note](../../sources/jasmin/SOURCE.md) for the licence text and attribution.
