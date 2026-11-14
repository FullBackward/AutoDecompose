# Quotient-and-lift: Puig_factorization G = O_p^'(G) * N_G(Z(L(S))) via the Frattini argument

| | |
|---|---|
| Kind | instance |
| Move | other |
| Language | rocq |
| Status | accepted |
| Source | [odd-order](../../sources/odd-order/SOURCE.md) at `ba734c020d9f` |
| Licence | `CECILL-B` |

## Intent

Prove B & G Theorem B.4(a), the factorization `'O_p^'(G) * 'N_G('Z('L(S))) = G` for an odd solvable group `G`, by the *quotient-and-lift* move: quotient out the normal subgroup `D := 'O_p^'(G)` to reach a situation where the already-proved Theorem B.4(b) applies (it assumes the p-core is trivial), prove the needed normality in that quotient, then lift it back to `G` through the Frattini argument.

## The decomposition

### parent `Puig_factorization`: [`theories/BGappendixAB.v` lines 483-506](https://github.com/math-comp/odd-order/blob/ba734c020d9f7dce5758fa822904dea29e2624ba/theories/BGappendixAB.v#L483-L506) ([local copy](code/theories/BGappendixAB.v))

```coq
Theorem Puig_factorization : 'O_p^'(G) * 'N_G('Z('L(S))) = G.
Proof.
set D := 'O_p^'(G); set Z := 'Z(_); have [sSG pS _] := and3P sylS.
have sSN: S \subset 'N(D) by rewrite (subset_trans sSG) ?gFnorm.
have p'D: p^'.-group D := pcore_pgroup _ _.
have tiSD: S :&: D = 1 := coprime_TIg (pnat_coprime pS p'D).
have def_Zq: Z / D = 'Z('L(S / D)).
  rewrite !quotientE -(setIid S) -(morphim_restrm sSN); set f := restrm _ _.
  have injf: 'injm f by rewrite ker_restrm ker_coset tiSD.
  rewrite -!(injmF _ injf) ?Puig_sub //= morphim_restrm.
  by rewrite (setIidPr _) // subIset ?Puig_sub.
have{def_Zq} nZq: Z / D <| G / D.
  have sylSq: p.-Sylow(G / D) (S / D) by apply: morphim_pHall.
  rewrite def_Zq (Puig_center_normal _ _ sylSq) ?quotient_odd ?quotient_sol //.
  exact: trivg_pcore_quotient.
have sZS: Z \subset S by rewrite subIset ?Puig_sub.
have sZN: Z \subset 'N_G(Z) by rewrite subsetI normG (subset_trans sZS).
have nDZ: Z \subset 'N(D) by rewrite (subset_trans sZS).
rewrite -(mulSGid sZN) mulgA -(norm_joinEr nDZ) (@Frattini_arg p) //= -/D -/Z.
  rewrite -cosetpre_normal quotientK ?quotientGK ?pcore_normal // in nZq.
  by rewrite norm_joinEr.
rewrite /pHall -divgS joing_subr ?(pgroupS sZS) /= ?norm_joinEr //= -/Z.
by rewrite TI_cardMg ?mulnK //; apply/trivgP; rewrite /= setIC -tiSD setSI.
Qed.
```

### child `Puig_sub`: [`theories/BGsection1.v` lines 1296-1297](https://github.com/math-comp/odd-order/blob/ba734c020d9f7dce5758fa822904dea29e2624ba/theories/BGsection1.v#L1296-L1297) ([local copy](code/theories/BGsection1.v))

```coq
Lemma Puig_sub G : 'L(G) \subset G.
Proof. exact: Puig_at_sub. Qed.
```

### child `Puig_center_normal`: [`theories/BGappendixAB.v` lines 428-473](https://github.com/math-comp/odd-order/blob/ba734c020d9f7dce5758fa822904dea29e2624ba/theories/BGappendixAB.v#L428-L473) ([local copy](code/theories/BGappendixAB.v))

```coq
Theorem Puig_center_normal : 'Z(L) <| G.
Proof.
have [sLiST sLTS] := pcore_Sylow_Puig_sub.
have sLiLT: 'L_*(T) \subset 'L(T) by apply: Puig_sub_even_odd.
have sZY: 'Z(L) \subset Y.
  rewrite subsetI andbC subIset ?centS ?orbT //=.
  suffices: 'C_S('L_*(S)) \subset 'L(T).
    by apply: subset_trans; rewrite setISS ?Puig_sub ?centS ?Puig_sub_even_odd.
  apply: subset_trans (subset_trans sLiST sLiLT).
  by apply: sub_cent_Puig_at pS; rewrite double_gt0.
have chY: Y \char G by rewrite !gFchar_trans.
have nsCY_G: 'C_G(Y) <| G by rewrite char_normal 1?subcent_char ?char_refl.
have [C defC sCY_C nsCG] := inv_quotientN nsCY_G (pcore_normal p _).
have sLG: L \subset G by rewrite gFsub_trans ?(pHall_sub sylS).
have nsL_nCS: L <| 'N_G(C :&: S).
  have sYLiS: Y \subset 'L_*(S).
    rewrite abelian_norm_Puig ?double_gt0 ?center_abelian //.
    apply: normalS (pHall_sub sylS) (char_normal chY).
    by rewrite subIset // (subset_trans sLTS) ?Puig_sub.
  have gYL: Y --> L := norm_abgenS sYLiS (Puig_gen _ _).
  have sLCS: L \subset C :&: S.
    rewrite subsetI Puig_sub andbT.
    rewrite -(quotientSGK _ sCY_C) ?(subset_trans sLG) ?normal_norm // -defC.
    rewrite odd_abelian_gen_stable ?char_normal ?norm_abgen_pgroup //.
      by rewrite (pgroupS _ pT) ?subIset // Puig_sub.
    by rewrite (pgroupS _ pS) ?Puig_sub.
  rewrite -[L](sub_Puig_eq _ sLCS) ?subsetIr // gFnormal_trans ?normalSG //.
  by rewrite subIset // sSG orbT.
have sylCS: p.-Sylow(C) (C :&: S) := Sylow_setI_normal nsCG sylS.
have{} defC: 'C_G(Y) * (C :&: S) = C.
  apply/eqP; rewrite eqEsubset mulG_subG sCY_C subsetIl /=.
  have nCY_C: C \subset 'N('C_G(Y)).
    exact: subset_trans (normal_sub nsCG) (normal_norm nsCY_G).
  rewrite -quotientSK // -defC /= -pseries1.
  rewrite -(pseries_catr_id [:: p : nat_pred]) (pseries_rcons_id [::]) /=.
  rewrite pseries1 /= pseries1 defC pcore_sub_Hall // morphim_pHall //.
  by rewrite subIset ?nCY_C.
have defG: 'C_G(Y) * 'N_G(C :&: S) = G.
  have sCS_N: C :&: S \subset 'N_G(C :&: S).
    by rewrite subsetI normG subIset // sSG orbT.
  by rewrite -(mulSGid sCS_N) mulgA defC (Frattini_arg _ sylCS).
have nsZ_N: 'Z(L) <| 'N_G(C :&: S) := gFnormal_trans _ nsL_nCS.
rewrite /normal subIset ?sLG //= -{1}defG mulG_subG /=.
rewrite cents_norm ?normal_norm // centsC.
by rewrite (subset_trans sZY) // centsC subsetIr.
Qed.
```

How the parts fit. The glue is the parent's proof, which combines the two project lemmas into the factorization. The lemma graph, in text:

- `Puig_factorization` (parent, lines 483-506) cites `Puig_sub` (lines 492, 493, 498) and `Puig_center_normal` (line 496).
- `Puig_center_normal` (child, lines 428-473) cites `pcore_Sylow_Puig_sub` (line 430), a further project lemma declared in the same file (line 403).

The proof flows through four obligations:

1. *Quotient out the obstruction.* `set D := 'O_p^'(G); set Z := 'Z(_)` fixes the normal subgroup and the center, and `tiSD : S :&: D = 1` (line 488) makes the kernel of the restriction map trivial.
2. *Identify the quotient's center.* `def_Zq : Z / D = 'Z('L(S / D))` (lines 489-493) is where `Puig_sub` does its work, through `injmF` and `morphim_restrm`, commuting the center with the quotient.
3. *Prove normality in the quotient.* `nZq : Z / D <| G / D` (lines 494-497) rewrites `def_Zq` and applies `Puig_center_normal` at the quotient `G / D`, with `morphim_pHall` giving `sylSq` and `trivg_pcore_quotient` discharging the trivial-p-core hypothesis.
4. *Lift back to G.* `sZS`, `sZN`, `nDZ` (lines 498-500) prepare the normalizer, then `Frattini_arg p` with `cosetpre_normal`/`quotientK`/`quotientGK` pull `nZq` back (lines 501-503), and a final coprime count (`TI_cardMg`, `tiSD`) closes the product equality (lines 504-505).

Why each child is a good leaf:

- `Puig_sub` is a one-line lemma closing on `exact: Puig_at_sub`; it states the functoriality fact `'L(G) ⊂ G` the parent reuses in three shapes (identifying the quotient center, and showing `Z ⊂ S` for `sZS` and the Sylow count).
- `Puig_center_normal` is Theorem B.4(b), a self-contained statement under the section hypotheses; its 45-line proof closes on its own from one further project lemma (`pcore_Sylow_Puig_sub`) and library facts, so it can be proved independently and then instantiated at the quotient `G / D`.

## Why it is good

1. `Puig_factorization` is a declaration at `theories/BGappendixAB.v` lines 483-506 (check: `declared(Puig_factorization, theories/BGappendixAB.v, 483-506)`).
2. The parent proof cites `Puig_center_normal` (check: `cites(parent, Puig_center_normal)`).
3. The parent proof cites `Puig_sub` (check: `cites(parent, Puig_sub)`).
4. The theorem-scale shape: 2 direct project lemmas (child sites of 2 and 46 lines), a 24-line glue, and depth 2 — `Puig_factorization` cites `Puig_center_normal`, which cites `pcore_Sylow_Puig_sub` (measurement).
5. The authors tie the two theorems to their paper source, as comments in the file: "This is B & G, Theorem B.4(a)" and "This is B & G, Theorem B.4(b)" (author-statement).

In my opinion the reusable part is the *quotient-and-lift* shape itself: state the theorem you need at the quotient, prove it there where the obstruction (`'O_p^'(G)`) has been killed, and spend the rest of the glue lifting it back with the Frattini argument. The two named children (`Puig_sub`, `Puig_center_normal`) are exactly the two independent units a bounded prover would receive.

## When to use it, and when not

Use the quotient-and-lift move when a theorem about `G` is already proved under the extra hypothesis that a normal subgroup `D` is trivial (here `Puig_center_normal` assumes `'O_p^'(G) = 1`), so the general case reduces to that case by quotienting out `D`; and when the lift back can be carried by a Frattini argument plus the coset-preimage correspondence. Avoid it when the quotient does not actually kill the obstruction (here `trivg_pcore_quotient` must give `'O_p^'(G / D) = 1`), when the lifted subgroup is not determined by its preimage (so `quotientK`/`quotientGK` do not apply), or when the normality to lift is not itself produced by a normality in the quotient plus a Frattini argument.

This move is a finite-group-theory technique, not one of the harness-level decomposition rules of survey F §10 (which covers case splits, induction, `suffices`/witness, calc chains and the like); the entry therefore records `rule: none`.

## Consequences

The move creates three obligations: (i) identify the quotient's center, `Z / D = 'Z('L(S / D))` (here `def_Zq`), discharged by `Puig_sub` through `injmF` and `morphim_restrm`; (ii) prove a normality in the quotient, `Z / D <| G / D` (here `nZq`), discharged by `Puig_center_normal` applied to the quotient whose p-core is trivial; (iii) lift that normality back to `G`, which here needs the Frattini argument (`Frattini_arg p`) plus the coset-preimage correspondence (`cosetpre_normal`, `quotientK`, `quotientGK`). Failure mode: the lift fails if the lifted subgroup is not determined by its preimage, or if the quotient has not actually trivialised the hypothesis `Puig_center_normal` requires (`trivg_pcore_quotient`).

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/coq-action.yml (workflow 'CI'); commit ba734c020d9f7dce5758fa822904dea29e2624ba is the head of default branch master; the opam build runs 'make', which invokes 'rocq makefile -f _CoqProject' and compiles every file in _CoqProject, whose first entry is theories/BGappendixAB.v | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: Puig_sub@theories/BGappendixAB.v:492, Puig_center_normal@theories/BGappendixAB.v:496; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at ba734c020d9f7dce5758fa822904dea29e2624ba | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(Puig_factorization, theories/BGappendixAB.v, 483-506) -> declared: Puig_factorization is declared at theories/BGappendixAB.v:483 | check_claims.py |
| 2 | verified | cites(parent, Puig_center_normal) -> cites: Puig_center_normal occurs at theories/BGappendixAB.v:496 | check_claims.py |
| 3 | verified | cites(parent, Puig_sub) -> cites: Puig_sub occurs at theories/BGappendixAB.v:492 | check_claims.py |
| 4 | verified | checked copied code: child Puig_sub at theories/BGsection1.v:1296-1297 is 2 lines (Lemma + Proof/Qed); child Puig_center_normal at theories/BGappendixAB.v:428-473 is 46 lines; parent 483-506 is 24 lines; depth 2 chain holds: Puig_center_normal cites pcore_Sylow_Puig_sub at BGappendixAB.v:430 ('have [sLiST sLTS] := pcore_Sylow_Puig_sub.') | verifier |
| 5 | verified | grep -n in copied code confirms theories/BGappendixAB.v:427 = '(* This is B & G, Theorem B.4(b). *)' and :482 = '(* This is B & G, Theorem B.4(a). *)', exactly as the claim quotes | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Provenance pass (2 files byte-identical at ba734c020d9f). Read the cited line ranges: parent Puig_factorization at BGappendixAB.v:483-506 matches entry statement and cites Puig_sub (492,493,498) and Puig_center_normal (496); child Puig_sub at BGsection1.v:1296-1297 = 'Lemma Puig_sub G : 'L(G) \subset G. Proof. exact: Puig_at_sub. Qed.' matches statement+closed_by; child Puig_center_normal at BGappendixAB.v:428-473 matches statement and its 45-line proof ends 'by rewrite (subset_trans sZY) // centsC subsetIr.'; all three sites end Qed, no sorry/admit. Shape numbers correct: glue_lines=24 (483-506), child_lines=[2,46] (1296-1297, 428-473), direct_lemmas=2 (the only project lemmas cited directly; quotient_odd/quotient_sol/trivg_pcore_quotient/morphim_pHall/Frattini_arg are mathcomp library lemmas), depth=2 (Puig_factorization -> Puig_center_normal -> pcore_Sylow_Puig_sub, the latter declared at 403 and cited at 430; also Puig_sub -> Puig_at_sub). Author-statement comments confirmed at lines 482 and 427. All 5 claims consistent with the code. | reviewer-correctness |
| generality | accept | Move stated generally: abstracted over a normal subgroup D (quotient out the obstruction, prove the needed normality H/D <| G/D in the quotient, lift back via Frattini argument + coset-preimage), not just the specific 'O_p^'(G); goal_shape/use_when name the real precondition (a theorem about G already proved under the trivial-D hypothesis). When-not-to-use is honest and specific, tied to named facts (trivg_pcore_quotient must give the trivial core; quotientK/quotientGK must determine the lifted subgroup; normality-to-lift must come from a quotient normality + Frattini). Consequences list three code-accurate obligations (def_Zq via Puig_sub/injmF/morphim_restrm; nZq via Puig_center_normal; lift via Frattini_arg p/cosetpre_normal/quotientK/quotientGK) plus an explicit failure mode. README 'Why each child is a good leaf' answers the bounded-prover question: Puig_sub is a one-line reusable functoriality fact, Puig_center_normal is a self-contained statement instantiable independently at the quotient. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are all consistent and traceable. check_provenance.py passes: 2 files (BGappendixAB.v, BGsection1.v) byte-identical at ba734c020d9f7dce5758fa822904dea29e2624ba. The commit is used consistently in entry.json source.commit, files[].permalink and sites[].permalink, in README.md, and in sources/odd-order/SOURCE.md. Licence is CECILL-B throughout (entry.json, README, SOURCE.md, source.json) and matches the copied files' headers 'Distributed under the terms of CeCILL-B' and the repo licence file CeCILL-B (copied as upstream-CeCILL-B). Line ranges cited in sites and claims resolve correctly in the local copies: parent Puig_factorization 483-506, child Puig_sub BGsection1.v 1296-1297, child Puig_center_normal 428-473, author-statement comments at lines 482 ('This is B & G, Theorem B.4(a)') and 427 ('B.4(b)'). | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/math-comp/odd-order at commit `ba734c020d9f7dce5758fa822904dea29e2624ba`, under `CECILL-B`; see the [source note](../../sources/odd-order/SOURCE.md) for the licence text and attribution.
