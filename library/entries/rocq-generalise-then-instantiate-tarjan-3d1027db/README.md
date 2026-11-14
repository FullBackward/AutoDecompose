# Kosaraju SCC output decides acyclicity: a general SCC-sequence lemma specialised to Kosaraju

| | |
|---|---|
| Kind | instance |
| Move | generalise-then-instantiate |
| Language | rocq |
| Status | accepted |
| Source | [tarjan](../../sources/tarjan/SOURCE.md) at `34fe042cc482` |
| Licence | `CECILL-B` |

## Intent

Establish that the Kosaraju SCC sequence characterises acyclicity (`kosaraju_acyclic =1 @acyclic`) by proving the equivalence once for an arbitrary SCC sequence satisfying three abstract hypotheses, then specialising to Kosaraju and discharging the hypotheses with `kosaraju_correct`.

## The decomposition

### parent `kosaraju_acyclicE`: [`theories/acyclic_tsorted.v` lines 61-62](https://github.com/rocq-community/tarjan/blob/34fe042cc482e65d27bc68b455d922d47da81c9d/theories/acyclic_tsorted.v#L61-L62) ([local copy](code/theories/acyclic_tsorted.v))

```coq
Lemma kosaraju_acyclicE : kosaraju_acyclic =1 @acyclic V.
Proof. by move=> g; rewrite [LHS]sccs_acyclicE; case: (kosaraju_correct g). Qed.
```

### context `kosaraju_acyclic`: [`theories/acyclic_tsorted.v` lines 59-59](https://github.com/rocq-community/tarjan/blob/34fe042cc482e65d27bc68b455d922d47da81c9d/theories/acyclic_tsorted.v#L59-L59) ([local copy](code/theories/acyclic_tsorted.v))

```coq
Definition kosaraju_acyclic := sccs_acyclic (@kosaraju V).
```

### child `sccs_acyclicE`: [`theories/acyclic.v` lines 363-371](https://github.com/rocq-community/tarjan/blob/34fe042cc482e65d27bc68b455d922d47da81c9d/theories/acyclic.v#L363-L371) ([local copy](code/theories/acyclic.v))

```coq
Lemma sccs_acyclicE : sccs_acyclic = acyclic g.
Proof.
apply: (sameP allP); apply: (equivP acyclicP); rewrite -(rwP preacyclic_sccsP).
split=> /= [[/= Ng scc_le1 c cscc]|acyP].
  by apply/class_acyclicP => //; rewrite scc_le1 ?sccsP//; split.
split=> [x|C /sccs_ex[c -> /acyP/class_acyclicP[]]//].
have /flattenP[c /[swap] xc cscc] := all_in_flatten x.
by have /class_acyclicP[//|_->//] := acyP _ cscc; rewrite inE.
Qed.
```

### context `AcyclicSCCS`: [`theories/acyclic.v` lines 320-326](https://github.com/rocq-community/tarjan/blob/34fe042cc482e65d27bc68b455d922d47da81c9d/theories/acyclic.v#L320-L326) ([local copy](code/theories/acyclic.v))

```coq
Section AcyclicSCCS.

Variables (V : finType) (scc_seq : rel V -> seq (seq V)) (g : rel V).
Hypothesis uniq_flatten : uniq (flatten (scc_seq g)).
Hypothesis all_in_flatten : forall v : V, v \in flatten (scc_seq g).
Hypothesis class_symconnect : forall c, c \in scc_seq g ->
  exists x, forall y, (y \in c) = symconnect g x y.
```

### context `sccs_acyclic`: [`theories/acyclic.v` lines 361-361](https://github.com/rocq-community/tarjan/blob/34fe042cc482e65d27bc68b455d922d47da81c9d/theories/acyclic.v#L361-L361) ([local copy](code/theories/acyclic.v))

```coq
Definition sccs_acyclic := all [pred c | class_acyclic c] (scc_seq g).
```

### child `kosaraju_correct`: [`theories/kosaraju.v` lines 716-783](https://github.com/rocq-community/tarjan/blob/34fe042cc482e65d27bc68b455d922d47da81c9d/theories/kosaraju.v#L716-L783) ([local copy](code/theories/kosaraju.v))

```coq
Lemma kosaraju_correct :
  let l := flatten kosaraju in
  [/\ uniq l, forall i, i \in l &
     forall c : seq T, c \in kosaraju ->
      exists x, forall y, (y \in c) = symconnect r x y].
Proof.
rewrite /kosaraju.
set f := pdfs (rgraph [rel x y | r y x]).
set g := fun p x => if _ then _ else _.
set p := (_, _).
have: uniq (flatten p.2) by [].
have: forall c, c \in (flatten p.2) ++ (tseq (rgraph r)).
  by move=>c; case: (tseq_correct (rgraph r)) => _ /(_ c).
have: forall c, c \in p.2 ->
                exists x, c =i (symconnect (relto predT r) x) by [].
have: ~: p.1 =i flatten p.2.
 by move=> i; rewrite !inE in_nil.
have reltoE:  relto predT r =2 relto predT (grel (rgraph r)).
  by move=> x1 y1; rewrite rgraphK.
have: tsorted r (predT : pred T) [seq i <- tseq (rgraph r) | i \in p.1].
  have->: [seq i <- tseq (rgraph r) | i \in p.1] = tseq (rgraph r).
    by apply/all_filterP/allP=> y; rewrite inE.
  case: (tseq_correct (rgraph r)).
  move=> [tsub tconn tbef] _; split => // x y xtseq.
    by move => xyconn; apply (tconn _ _ xtseq); rewrite -(eq_connect reltoE).
  rewrite (eq_connect reltoE) => conn0; move: (tbef _ _ xtseq conn0).
  by rewrite /before /= /can_to (eq_find (eq_symconnect reltoE _)).
elim: tseq p => [[s l]/= HR HI HE HFI HUF|].
  split=> // i.
  by have := HFI i; rewrite cats0.
move=> x l IH [s1 l1] HR HI HE HFI HUF.
rewrite /g /f /=.
have [xIs1|xNIs1] := boolP (x \in s1); last first.
  apply: IH => //= [|i]; first by move: HR; rewrite /= (negPf xNIs1).
  have:= HFI i; rewrite !mem_cat inE /=.
  by case: eqP => //->; rewrite -HI !inE xNIs1.
have := (@pdfs_connect (rgraph [rel x y | r y x]) s1 x xIs1).
case: pdfs => s2 l2 /= [Ul2 s2E Dl2 xCy].
move: HR; rewrite /= xIs1; set L := [seq _ <- _ | _] => HR.
have l2R : l2 =i (symconnect r x).
  move=> y; rewrite xCy; set re := [rel x0 y0 | _].
  rewrite (_ : connect _ _ _ = connect (relto [pred u in s1] re) x y); last first.
    by apply: eq_connect => x0 y0; by rewrite /rgraph /= mem_enum.
  rewrite -(@connect_to_rev r L setT) // => [|i|].
  - rewrite -tsorted_symconnect.
      by apply: eq_symconnect => i j; rewrite /= !inE.
    by apply: eq_tsorted HR => i; rewrite  !inE //= topredE inE.
  - rewrite /= !inE mem_filter.
    have := HFI i; rewrite /= mem_cat -HI /= !inE.
    case: (_ =P _) => [->|] /=; first by rewrite xIs1.
    by case: (_ \in _).
 by apply: eq_tsorted HR => i; rewrite // inE topredE inE.
apply: IH => [|i|i|i|] /=.
- suff->: [seq i <- l | i \in s2] =
          [seq i <- x :: L | ~~ symconnect r x i].
    by apply: tsorted_inv.
  rewrite /= symconnect0 /= -filter_predI.
  by apply: eq_filter => y /=; rewrite s2E !inE l2R.
- by rewrite s2E !mem_cat !inE -HI negb_and negbK inE.
- by rewrite inE => /orP[/eqP->|//]; [exists x | apply: HE].
- have:= HFI i.
  rewrite /= !mem_cat !inE => /or3P[->|/eqP->|->]; rewrite ?orbT //.
  by rewrite xCy connect0.
rewrite cat_uniq Ul2 HUF /= andbT.
apply/hasPn => i /=.
have/subsetP/(_ i)/= := Dl2.
by rewrite -HI /= !inE; do 2 case: (_ \in _).
Qed.
```

### context `kosaraju`: [`theories/kosaraju.v` lines 710-714](https://github.com/rocq-community/tarjan/blob/34fe042cc482e65d27bc68b455d922d47da81c9d/theories/kosaraju.v#L710-L714) ([local copy](code/theories/kosaraju.v))

```coq
Definition kosaraju :=
  let f := pdfs (rgraph [rel x y | r y x]) in
  (foldl  (fun (p : {set T} * seq (seq T)) x => if x \notin p.1 then p else
                      let p1 := f (p.1, [::]) x in  (p1.1, p1.2 :: p.2))
          (setT, [::]) (tseq (rgraph r))).2.
```

### How the parts fit

The parent `kosaraju_acyclicE` is the instantiation step of the move. Its proof is one line of glue: it `rewrite`s `kosaraju_acyclic` with the general lemma `sccs_acyclicE`, then `case`s on `kosaraju_correct` to discharge the three section hypotheses. The two children play distinct roles:

- `sccs_acyclicE` is the **general** lemma, proved in section `AcyclicSCCS` for an arbitrary `scc_seq : rel V -> seq (seq V)` under the hypotheses `uniq_flatten`, `all_in_flatten` and `class_symconnect` (shown in the `AcyclicSCCS` context above). It is a good leaf because it is self-contained: it closes from the acyclicity predicates of the same file (`acyclicP`, `preacyclic_sccsP`, `class_acyclicP`), with no reference to any concrete algorithm.
- `kosaraju_correct` is the **instantiation** lemma. Its three conjuncts are exactly `uniq_flatten`, `all_in_flatten` and `class_symconnect` for `scc_seq := @kosaraju V`, so it is the only place the concrete algorithm enters. It is a good leaf because it closes by induction over `tseq` from `pdfs_connect` and `tseq_correct`, with no reference to acyclicity.

Lemma graph, in text: `kosaraju_acyclicE` uses `sccs_acyclicE` (the `rewrite`) and `kosaraju_correct` (the `case`). `sccs_acyclicE` uses `acyclicP`, `preacyclic_sccsP` and `class_acyclicP`; `preacyclic_sccsP` uses `preacyclicP`, which closes on the mathcomp view `'forall_'forall_implyP`. `kosaraju_correct` uses `pdfs_connect`, `tseq_correct`, `tsorted_inv`, `foldr_pdfs_subset` and `pdfs_uniq`. The definition `kosaraju_acyclic := sccs_acyclic (@kosaraju V)` (line 59) is the generalised predicate specialised at the concrete sequence; the three hypotheses are `let l := flatten kosaraju in uniq l`, `forall i, i \in l`, and `forall c, c \in kosaraju -> exists x, c =i symconnect r x`.

## Why it is good

1. The glue cites `sccs_acyclicE` (check, `cites(parent, sccs_acyclicE)`): the parent site `acyclic_tsorted.v:61-62` contains `sccs_acyclicE` in its proof line.
2. The glue cites `kosaraju_correct` (check, `cites(parent, kosaraju_correct)`): the parent site contains `kosaraju_correct` in its proof line.
3. `kosaraju_correct` closes without holes (check, `no_sorry(theories/kosaraju.v, 716-783)`): no `sorry`/`admit`/`Admitted` in its 68-line proof.
4. The decomposition is theorem scale with 2 direct lemmas, `glue_lines` 2 and `child_lines` [9, 68] (measurement): parent site `acyclic_tsorted.v:61-62`, children `acyclic.v:363-371` and `kosaraju.v:716-783`; the checked dependency chain `sccs_acyclicE -> preacyclic_sccsP -> preacyclicP` is depth 3.
5. The same move is used earlier in the file (known-use): `acyclic_connect_before` is generalised over an abstract `vs` (hypotheses `vs_all`, `vs_tsorted`) and instantiated at `tseq g` by `tseq_connect_before`, which supplies those hypotheses from `tseq_correct` (`acyclic_tsorted.v:18-51`).

*Opinion:* the elegance of this entry is that the two children are cleanly separated by concern — one knows acyclicity but nothing about Kosaraju, the other knows Kosaraju but nothing about acyclicity — so the parent is pure glue and neither child's statement mentions the other's domain.

## When to use it, and when not

Use this move when several algorithms or instances share a proof that depends only on an abstract interface — here an SCC sequence with the three facts `uniq_flatten`, `all_in_flatten` and `class_symconnect` — so the shared lemma can be proved once over section variables and each concrete case closed by discharging the hypotheses. It suits a graph or structure whose property (acyclicity) is defined uniformly for any of its decompositions (SCC sequence).

Do not use it when the concrete instances need different arguments, or when a concrete algorithm's correctness lemma does not already expose the interface facts in the exact shape the general lemma assumes: then instantiation needs an adapter lemma and the "pure glue" parent stops being one line. It also buys nothing when there is only one instance — the generality is then just indirection.

## Consequences

The move splits the work into (a) proving the general lemma once over the abstract `scc_seq` and its three hypotheses, and (b) discharging the three hypotheses at each concrete algorithm (here Kosaraju). The obligation it creates is that every instantiation must re-supply `uniq_flatten`, `all_in_flatten` and `class_symconnect`; a new SCC algorithm whose correctness lemma does not expose exactly these three facts cannot use `sccs_acyclicE` without an adapter. The Kosaraju instantiation is pure glue (`rewrite` + `case`), so any failure of acyclicity must lie in one of the two lemmas, not in the parent. Failure mode to watch: if the generalised statement is weakened to fit every instance, the instantiation no longer yields the original strength of the concrete theorem.

Survey F §10 has no rule for generalise-then-instantiate; the nearest are rule 4 (extract a `have` into a standalone lemma) and rule 11 (hypothesis consequences), neither of which captures section-variable generalisation, so this entry maps to no rule (`f10_rule: null`).

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/docker-action.yml runs on push to master (default branch) and builds via coq-community/docker-coq-action from the opam file, compiling every file in _CoqProject including theories/acyclic_tsorted.v; commit 34fe042cc482e65d27bc68b455d922d47da81c9d is on master (branches-where-head = master) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: sccs_acyclicE@theories/acyclic_tsorted.v:62, kosaraju_correct@theories/acyclic_tsorted.v:62; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 4 file(s) byte-identical at 34fe042cc482e65d27bc68b455d922d47da81c9d | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, sccs_acyclicE) -> cites: sccs_acyclicE occurs at theories/acyclic_tsorted.v:62 | check_claims.py |
| 2 | verified | cites(parent, kosaraju_correct) -> cites: kosaraju_correct occurs at theories/acyclic_tsorted.v:62 | check_claims.py |
| 3 | verified | no_sorry(theories/kosaraju.v, 716-783) -> no_sorry: none of admit, Admitted, Axiom, axiom in theories/kosaraju.v:716-783 | check_claims.py |
| 4 | verified | parent site acyclic_tsorted.v:61-62 is 2 lines (Lemma + one-line Proof/Qed); children acyclic.v:363-371 is 9 lines (sccs_acyclicE) and kosaraju.v:716-783 is 68 lines (kosaraju_correct); 2 direct lemmas; depth-3 chain confirmed: sccs_acyclicE proof applies preacyclic_sccsP (acyclic.v:223), whose proof applies preacyclicP (acyclic.v:213) | verifier |
| 5 | verified | acyclic_tsorted.v:9-33 Section AcyclicTSorted has Variables (V:finType)(g:rel V) and vs:seq V with Hypotheses vs_all, vs_tsorted; acyclic_connect_before (line 30) proved over abstract vs; tseq_connect_before (line 39) does move=> acycg; have [sorted all] := tseq_correct g; by apply: acyclic_connect_before, instantiating at tseq g and supplying vs_all/vs_tsorted from tseq_correct | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent acyclic_tsorted.v:61-62 is one glue line 'move=> g; rewrite [LHS]sccs_acyclicE; case: (kosaraju_correct g)' citing exactly the two children, and the three hypotheses uniq_flatten/all_in_flatten/class_symconnect (acyclic.v:323-326) match kosaraju_correct's three conjuncts (kosaraju.v:716-720), so the case discharges the rewrite's side conditions and it closes. Child closed_by strings match code verbatim: sccs_acyclicE at acyclic.v:365, kosaraju_correct's 'elim: tseq p' at kosaraju.v:743. Statements match the declarations. Shape numbers correct: glue_lines 2 (61-62), child_lines [9,68] (363-371 and 716-783), direct_lemmas 2, depth 3 (sccs_acyclicE rewrites preacyclic_sccsP acyclic.v:365 -> preacyclic_sccsP applies preacyclicP acyclic.v:226). Children are exactly the lemmas the parent uses (no others). | reviewer-correctness |
| generality | accept | Move is stated abstractly (prove over section variables under an interface of three hypotheses, then specialise); also_known_as gives cross-language names; a real second instance of the move is cited and present at acyclic_tsorted.v:18-51 (acyclic_connect_before over abstract vs, instantiated at tseq g via tseq_correct), so it is not a one-off. 'When not to use' names concrete failure modes (instances needing different arguments; correctness lemma not exposing the interface facts in the exact shape -> adapter lemma; single instance -> indirection). Consequences are specific and honest (obligation to re-supply the three facts; weakened general statement loses the concrete theorem's strength; pure-glue parent means failure lies in a child). It states why each child is a good bounded leaf: sccs_acyclicE is self-contained over same-file acyclicity predicates with no reference to a concrete algorithm, kosaraju_correct closes by induction over tseq from pdfs_connect/tseq_correct with no reference to acyclicity. | reviewer-generality |
| provenance-licence | accept | Provenance and licence consistent and traceable. check_provenance passes: 4 files (acyclic_tsorted.v, acyclic.v, kosaraju.v, extra.v) byte-identical at commit 34fe042cc482e65d27bc68b455d922d47da81c9d; source.json, SOURCE.md and entry.json all pin the same full commit hash; every permalink uses that commit with the correct path and line range (parent acyclic_tsorted.v:61-62, context 59-59, child sccs_acyclicE acyclic.v:363-371, contexts 320-326 and 361-361, child kosaraju_correct kosaraju.v:716-783, context 710-714) and each cited range matches the local copy. Licence CECILL-B is recorded identically in source.json, SOURCE.md, entry.json and README, and upstream-LICENSE (copied from LICENSE) is the CeCILL-B text. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/rocq-community/tarjan at commit `34fe042cc482e65d27bc68b455d922d47da81c9d`, under `CECILL-B`; see the [source note](../../sources/tarjan/SOURCE.md) for the licence text and attribution.
