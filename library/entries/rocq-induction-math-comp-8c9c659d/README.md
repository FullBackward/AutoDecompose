# Well-founded induction on group order for Jordan-Holder uniqueness

| | |
|---|---|
| Kind | instance |
| Move | induction |
| Language | rocq |
| Status | accepted |
| Source | [math-comp](../../sources/math-comp/SOURCE.md) at `3a90d8b65f77` |
| Licence | `CECILL-B` |

## Intent

Prove Jordan-Holder uniqueness — that the factor lists of any two composition
series of a finite group agree up to isomorphism and permutation — by
well-founded induction on the group order `#|G|`, the inductive step assembled
from ten named project lemmas: two base cases, an order decrease, normality of
the maximal subgroups, the product lemma and the second isomorphism theorem, a
common refinement, simplicity of the quotients to feed the induction
hypothesis (`quotient_simple`, `isog_simple`), and a permutation assembly.

## The decomposition

### parent `JordanHolderUniqueness`: [`solvable/jordanholder.v` lines 165-224](https://github.com/math-comp/math-comp/blob/3a90d8b65f77f24e4fd770453c0697233b1c791d/solvable/jordanholder.v#L165-L224) ([local copy](code/solvable/jordanholder.v))

```coq
Lemma JordanHolderUniqueness (G : gTg) (s1 s2 : seq gTg) :
  comps G s1 -> comps G s2 -> perm_eq (mkfactors G s1) (mkfactors G s2).
Proof.
have [n] := ubnP #|G|; elim: n G => // n Hi G in s1 s2 * => /ltnSE-cG cs1 cs2.
have [G1 | ntG] := boolP (G :==: 1).
  have -> : s1 = [::] by apply/eqP; rewrite -(trivg_comps cs1).
  have -> : s2 = [::] by apply/eqP; rewrite -(trivg_comps cs2).
  by rewrite /= perm_refl.
have [sG | nsG] := boolP (simple G).
  by rewrite (simple_compsP cs1 sG) (simple_compsP cs2 sG) perm_refl.
case es1: s1 cs1 => [|N1 st1] cs1.
  by move: (trivg_comps cs1); rewrite eqxx; move/negP:ntG.
case es2: s2 cs2 => [|N2 st2] cs2 {s1 es1}.
  by move: (trivg_comps cs2); rewrite eqxx; move/negP:ntG.
case/andP: cs1 => /= lst1; case/andP=> maxN_1 pst1.
case/andP: cs2 => /= lst2; case/andP=> maxN_2 pst2.
have cN1 : #|N1| < n.
  by rewrite (leq_trans _ cG) ?proper_card ?(maxnormal_proper maxN_1).
have cN2 : #|N2| < n.
  by rewrite (leq_trans _ cG) ?proper_card ?(maxnormal_proper maxN_2).
case: (N1 =P N2) {s2 es2} => [eN12 |].
  by rewrite eN12 /= perm_cons Hi // /comps ?lst2 //= -eN12 lst1.
move/eqP; rewrite -val_eqE /=; move/eqP=> neN12.
have nN1G : N1 <| G by apply: maxnormal_normal.
have nN2G : N2 <| G by apply: maxnormal_normal.
pose N := (N1 :&: N2)%G.
have nNG : N <| G.
  by rewrite /normal subIset ?(normal_sub nN1G) //= normsI ?normal_norm.
have iso1 : (G / N1)%G \isog (N2 / N)%G.
  rewrite isog_sym /= -(maxnormalM maxN_1 maxN_2) //.
  rewrite (@normC _ N1 N2) ?(subset_trans (normal_sub nN1G)) ?normal_norm //.
  by rewrite weak_second_isog ?(subset_trans (normal_sub nN2G)) ?normal_norm.
have iso2 : (G / N2)%G \isog (N1 / N)%G.
  rewrite isog_sym /= -(maxnormalM maxN_1 maxN_2) // setIC.
  by rewrite weak_second_isog ?(subset_trans (normal_sub nN1G)) ?normal_norm.
have [sN /andP[lsN csN]] := exists_comps N.
have i1 : perm_eq (mksrepr G N1 :: mkfactors N1 st1)
                  [:: mksrepr G N1, mksrepr N1 N & mkfactors N sN].
  rewrite perm_cons -[mksrepr _ _ :: _]/(mkfactors N1 [:: N & sN]).
  apply: Hi=> //; rewrite /comps ?lst1 //= lsN csN andbT /=.
  rewrite -quotient_simple.
    by rewrite (normalS (subsetIl N1 N2) (normal_sub nN1G)).
  by rewrite -(isog_simple iso2) quotient_simple.
have i2 : perm_eq (mksrepr G N2 :: mkfactors N2 st2)
                  [:: mksrepr G N2, mksrepr N2 N & mkfactors N sN].
  rewrite perm_cons -[mksrepr _ _ :: _]/(mkfactors N2 [:: N & sN]).
  apply: Hi=> //; rewrite /comps ?lst2 //= lsN csN andbT /=.
  rewrite -quotient_simple.
    by rewrite (normalS (subsetIr N1 N2) (normal_sub nN2G)).
  by rewrite -(isog_simple iso1) quotient_simple.
pose fG1 := [:: mksrepr G N1, mksrepr N1 N & mkfactors N sN].
pose fG2 := [:: mksrepr G N2, mksrepr N2 N & mkfactors N sN].
have i3 : perm_eq fG1 fG2.
  rewrite (@perm_catCA _ [::_] [::_]) /mksrepr.
  rewrite (@section_repr_isog _ (mkSec _ _) (mkSec _ _) iso1).
  rewrite -(@section_repr_isog _ (mkSec _ _) (mkSec _ _) iso2).
  exact: perm_refl.
apply: (perm_trans i1); apply: (perm_trans i3); rewrite perm_sym.
by apply: perm_trans i2; apply: perm_refl.
Qed.
```

### child `trivg_comps`: [`solvable/jordanholder.v` lines 126-131](https://github.com/math-comp/math-comp/blob/3a90d8b65f77f24e4fd770453c0697233b1c791d/solvable/jordanholder.v#L126-L131) ([local copy](code/solvable/jordanholder.v))

```coq
Lemma trivg_comps G s : comps G s -> (G :==: 1) = (s == [::]).
Proof.
case/andP=> ls cs; apply/eqP/eqP=> [G1 | s1]; last first.
  by rewrite s1 /= in ls; apply/eqP.
by case: s {ls} cs => //= H s /andP[/maxgroupp]; rewrite G1 /proper sub1G andbF.
Qed.
```

### child `simple_compsP`: [`solvable/jordanholder.v` lines 136-145](https://github.com/math-comp/math-comp/blob/3a90d8b65f77f24e4fd770453c0697233b1c791d/solvable/jordanholder.v#L136-L145) ([local copy](code/solvable/jordanholder.v))

```coq
Lemma simple_compsP G s : comps G s -> reflect (s = [:: 1%G]) (simple G).
Proof.
move=> cs; apply: (iffP idP) => [|s1]; last first.
  by rewrite s1 /comps eqxx /= andbT -simple_maxnormal in cs.
case: s cs => [/trivg_comps/eqP-> | H s]; first by case/simpleP; rewrite eqxx.
rewrite [comps _ _]andbCA /= => /andP[/maxgroupp maxH /trivg_comps/esym nil_s].
rewrite simple_maxnormal => /maxgroupP[_ simG].
have H1: H = 1%G by apply/val_inj/simG; rewrite // sub1G.
by move: nil_s; rewrite H1 eqxx => /eqP->.
Qed.
```

### child `maxnormal_proper`: [`solvable/gseries.v` lines 389-392](https://github.com/math-comp/math-comp/blob/3a90d8b65f77f24e4fd770453c0697233b1c791d/solvable/gseries.v#L389-L392) ([local copy](code/solvable/gseries.v))

```coq
Lemma maxnormal_proper A B C : maxnormal A B C -> A \proper B.
Proof.
by case/maxsetP=> /and3P[gA pAB _] _; apply: (sub_proper_trans (subset_gen A)).
Qed.
```

### child `maxnormalM`: [`solvable/gseries.v` lines 405-417](https://github.com/math-comp/math-comp/blob/3a90d8b65f77f24e4fd770453c0697233b1c791d/solvable/gseries.v#L405-L417) ([local copy](code/solvable/gseries.v))

```coq
Lemma maxnormalM G H K :
  maxnormal H G G -> maxnormal K G G -> H :<>: K -> H * K = G.
Proof.
move=> maxH maxK /eqP; apply: contraNeq => ltHK_G.
have [nsHG nsKG] := (maxnormal_normal maxH, maxnormal_normal maxK).
have cHK: commute H K.
  exact: normC (subset_trans (normal_sub nsHG) (normal_norm nsKG)).
wlog suffices: H K {maxH} maxK nsHG nsKG cHK ltHK_G / H \subset K.
  by move=> IH; rewrite eqEsubset !IH // -cHK.
have{maxK} /maxgroupP[_ maxK] := maxK.
apply/joing_idPr/maxK; rewrite ?joing_subr //= comm_joingE //.
by rewrite properEneq ltHK_G; apply: normalM.
Qed.
```

### child `weak_second_isog`: [`finite_group/quotient.v` lines 796-797](https://github.com/math-comp/math-comp/blob/3a90d8b65f77f24e4fd770453c0697233b1c791d/finite_group/quotient.v#L796-L797) ([local copy](code/finite_group/quotient.v))

```coq
Lemma weak_second_isog : H / (K :&: H) \isog H * K / K.
Proof. by rewrite quotientMidr; apply: second_isog. Qed.
```

### child `exists_comps`: [`solvable/jordanholder.v` lines 147-158](https://github.com/math-comp/math-comp/blob/3a90d8b65f77f24e4fd770453c0697233b1c791d/solvable/jordanholder.v#L147-L158) ([local copy](code/solvable/jordanholder.v))

```coq
Lemma exists_comps (G : gTg) : exists s, comps G s.
Proof.
elim: {G} #|G| {1 3}G (leqnn #|G|) => [G | n IHn G cG].
  by rewrite leqNgt cardG_gt0.
have [sG | nsG] := boolP (simple G).
  by exists [:: 1%G]; rewrite /comps eqxx /=  -simple_maxnormal andbT.
have [-> | ntG] := eqVneq G 1%G; first by exists [::]; rewrite /comps eqxx.
have [N maxN] := ex_maxnormal_ntrivg ntG.
have [|s /andP[ls cs]] := IHn N.
  by rewrite -ltnS (leq_trans _ cG) // proper_card // (maxnormal_proper maxN).
by exists (N :: s); apply/and3P.
Qed.
```

### child `quotient_simple`: [`solvable/gseries.v` lines 461-466](https://github.com/math-comp/math-comp/blob/3a90d8b65f77f24e4fd770453c0697233b1c791d/solvable/gseries.v#L461-L466) ([local copy](code/solvable/gseries.v))

```coq
Lemma quotient_simple gT (G H : {group gT}) :
  H <| G -> simple (G / H) = maxnormal H G G.
Proof.
move=> nsHG; have nGH := normal_norm nsHG.
by apply/idP/idP; [apply: minnormal_maxnormal | apply: maxnormal_minnormal].
Qed.
```

### child `section_repr_isog`: [`solvable/jordanholder.v` lines 100-104](https://github.com/math-comp/math-comp/blob/3a90d8b65f77f24e4fd770453c0697233b1c791d/solvable/jordanholder.v#L100-L104) ([local copy](code/solvable/jordanholder.v))

```coq
Lemma section_repr_isog s1 s2 :
  s1 \isog s2 -> section_repr s1 = section_repr s2.
Proof.
by move=> iso12; congr (odflt _ _); apply: eq_pick => s; apply: isog_transr.
Qed.
```

### context `header`: [`solvable/jordanholder.v` lines 160-163](https://github.com/math-comp/math-comp/blob/3a90d8b65f77f24e4fd770453c0697233b1c791d/solvable/jordanholder.v#L160-L163) ([local copy](code/solvable/jordanholder.v))

```coq
(******************************************************************************)
(* The factors associated to two composition series of the same group are     *)
(* the same up to isomorphism and permutation                                 *)
(******************************************************************************)
```

How the parts fit. The parent is a well-founded strong induction on `#|G|`
(`ubnP #|G|` then `elim: n G`, with `s1 s2` kept general via `in s1 s2 *`).
The proof opens with two `boolP` case splits: `G :==: 1` (trivial) and
`simple G`, closed by `trivg_comps` and `simple_compsP`. Otherwise it peels
the first subgroup off each series to get maximal normal subgroups `N1`, `N2`,
uses `maxnormal_proper` to get `#|N1| < n` and `#|N2| < n` (the measure
decrease that licenses the induction hypothesis), and `maxnormal_normal` to
know `N1 <| G`, `N2 <| G`. It then builds the common refinement
`N := N1 :&: N2`, obtains a composition series for it with `exists_comps`, and
proves the two second-isomorphism quotients `(G / N1) ~= (N2 / N)` and
`(G / N2) ~= (N1 / N)` via `maxnormalM` and `weak_second_isog`. `quotient_simple`
(helped by `isog_simple`) shows the quotients are simple, which is what lets the
induction hypothesis `Hi` apply to the refined series; `section_repr_isog` then
rewrites the canonical representatives so the three `perm_eq` facts `i1`, `i2`,
`i3` compose by `perm_trans` into the goal.

The lemma graph (each arrow = "is cited by"):

```
JordanHolderUniqueness (induction on #|G|)
├─ trivg_comps            base case G = 1
├─ simple_compsP          base case simple G        ── trivg_comps, simpleP, simple_maxnormal
├─ maxnormal_proper       order decrease N1, N2
├─ maxnormal_normal       normality N1, N2          (listed below, not shown as a site)
├─ maxnormalM             N1 * N2 = G               ── maxnormal_normal, normC, normalM
├─ weak_second_isog       the two quotient isos     ── quotientMidr, second_isog
├─ exists_comps           common refinement N       ── ex_maxnormal_ntrivg, maxnormal_proper
├─ quotient_simple        quotients simple          ── minnormal_maxnormal, maxnormal_minnormal
├─ isog_simple            transfers simplicity      ── isogP, simpleP, morphim_injm_eq1, morphim_invm
└─ section_repr_isog      assemble the permutation  ── eq_pick, isog_transr
```

The ninth and tenth direct lemmas, `maxnormal_normal` (gseries.v lines 384-387)
and `isog_simple` (gseries.v lines 468-478), are shown here as links rather
than sites:
[`solvable/gseries.v#L384-L387`](https://github.com/math-comp/math-comp/blob/3a90d8b65f77f24e4fd770453c0697233b1c791d/solvable/gseries.v#L384-L387)
and
[`solvable/gseries.v#L468-L478`](https://github.com/math-comp/math-comp/blob/3a90d8b65f77f24e4fd770453c0697233b1c791d/solvable/gseries.v#L468-L478).
`maxnormal_normal` is a one-line unpacking of `maxnormal A B B` into `A <| B`;
`isog_simple` transfers simplicity across `iso1`/`iso2`.

Why each lemma is a good leaf: every child is a self-contained statement whose
proof closes on its own or from named siblings — `trivg_comps` and
`simple_compsP` close from `maxgroupp`/`simpleP`; `maxnormal_proper`,
`maxnormal_normal`, `maxnormalM`, `quotient_simple` and `weak_second_isog` are
each one to a few ssreflect lines; `exists_comps` is itself an induction on
`#|G|` closed by the same `maxnormal_proper`; `section_repr_isog` closes from
`eq_pick` and `isog_transr`.

## Why it is good

1. The parent (lines 165-224) and all eight shown children close with `Qed.`;
   none of the three copied files introduces an `admit`, `Admitted`, `sorry` or
   `axiom` to close a goal (check — read of the copied files).
2. The authors state the result in prose beside the proof — "The factors
   associated to two composition series of the same group are the same up to
   isomorphism and permutation" (lines 161-162) — and the formal goal
   `perm_eq (mkfactors G s1) (mkfactors G s2)` is exactly that statement
   (author-statement).
3. The main proof body is 58 lines (167-224) and cites 10 named project lemmas
   directly (the eight shown children plus `maxnormal_normal` and `isog_simple`);
   the deepest checked chain of project lemmas below the main theorem has depth
   2, e.g. `JordanHolderUniqueness -> exists_comps -> maxnormal_proper`
   (measurement).
4. The same skeleton is reused nearly line-for-line for the action-invariant
   `StrongJordanHolderUniqueness` in the same file (lines 575-660), which swaps
   the `comps`/`maxnormal` lemmas for their `acomps`/`maxainv` counterparts
   (known-use).

In my opinion the detail worth copying is the pairing of the induction
variable (`#|G|`) with the generalised hypotheses (`in s1 s2 *`): the induction
is on a measure, and the two series are kept general so the hypothesis applies
to the three smaller groups `N1`, `N2`, `N` that the step constructs.

## When to use it, and when not

Use it when the goal is an equality between two objects built from the same
group, provable by induction on a strictly decreasing measure (here the group
order), the base cases are a trivial and a simple object with a `reflect`
characterisation, and the step can be assembled from an order decrease, a
common refinement, second-isomorphism quotients, and a permutation assembly.
Avoid it when the measure does not strictly decrease into the refinement (so
the induction hypothesis cannot be applied), when the base cases need bespoke
arguments rather than a `reflect` lemma, or when the two series cannot share a
common refinement, which removes the thing the permutation assembly commutes.

## Consequences

The move creates the obligations the induction step must discharge: (a) the
order decreases along each maximal normal subgroup (`maxnormal_proper`,
lines 181-184); (b) a composition series exists for the common refinement
`N1 :&: N2` (`exists_comps`, line 200); (c) the two quotient isomorphisms hold
(`maxnormalM` + `weak_second_isog`, lines 193-199); and (d) the quotients are
simple so the induction hypothesis applies (`quotient_simple` + `isog_simple`,
lines 205-214). The generalisation must keep `s1 s2` free across the induction,
and the base cases must be recognised by `reflect` lemmas. Failure mode: if the
measure does not strictly decrease into the refinement `N`, the induction
hypothesis cannot be applied and the step stalls.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/nix-action-rocq-9.2.yml (also nix-action-rocq-9.1.yml, nix-action-rocq-9.3.yml, nix-action-rocq-master.yml) has a mathcomp-solvable job built via nix-build on push/PR; mathcomp-solvable compiles solvable/jordanholder.v. Commit 3a90d8b65f77f24e4fd770453c0697233b1c791d is on the default branch master (branches-where-head returns master). | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 3 file(s) byte-identical at 3a90d8b65f77f24e4fd770453c0697233b1c791d | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read jordanholder.v 165-224 (parent JordanHolderUniqueness closes Qed. at 224) and the eight child sites: trivg_comps Qed.131, simple_compsP Qed.145, exists_comps Qed.158, section_repr_isog Qed.104 (jordanholder.v); maxnormal_proper Qed.392, maxnormalM Qed.417, quotient_simple Qed.466 (gseries.v); weak_second_isog Qed.797 (quotient.v). Grep for admit|Admitted|sorry|axiom|Axiom|Abort over all three copied files: no matches. | verifier |
| 2 | verified | Read jordanholder.v 160-163: header comment lines 161-162 read "The factors associated to two composition series of the same group are the same up to isomorphism and permutation", matching the goal perm_eq (mkfactors G s1) (mkfactors G s2) at line 166. | verifier |
| 3 | refuted | The 58-line count (167-224) and both depth-2 chains are correct (exists_comps cites maxnormal_proper at 156; simple_compsP cites trivg_comps at 140-141). But "9 named project lemmas cited directly" undercounts: the proof body also cites isog_simple directly at lines 207 and 214 (rewrite -(isog_simple iso1/iso2)), a lemma in gseries.v (line 468) omitted from the listed 9, so the direct count is 10. | verifier |
| 4 | verified | Read jordanholder.v 575-660: StrongJordanHolderUniqueness reuses the same skeleton - have [n] := ubnP #|G|; elim: n G => // n Hi G in s1 s2 * at 579; trivg_acomps/asimple_acompsP base cases; maxainv_proper/maxainv_norm/maxainvM/exists_acomps swap the maxnormal/comps lemmas; identical i1/i2/i3 fG1/fG2 permutation assembly; closes Qed. at 660. | verifier |
| 5 | verified | Read copied code/solvable/jordanholder.v: parent proof body Proof..Qed spans lines 167-224 = 58 lines. Counted the 10 named project lemmas cited directly in the body: trivg_comps (170,171,176,178), simple_compsP (174), maxnormal_proper (182,184), maxnormal_normal (188,189), maxnormalM (194,198), weak_second_isog (196,199), exists_comps (200), quotient_simple (205,207,212,214), section_repr_isog (219,220), isog_simple (207,214). isog_simple is at gseries.v#L468-478 (fetched). Depth-2 chains confirmed: exists_comps cites maxnormal_proper at jordanholder.v:156; simple_compsP cites trivg_comps at jordanholder.v:140-141. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Correctness lens: parent JordanHolderUniqueness (jordanholder.v 165-224) is well-founded induction on #|G| via ubnP+elim with s1 s2 generalised (in s1 s2 *), matching the entry. Proof body 167-224 (58 lines) cites exactly 10 named project lemmas: trivg_comps, simple_compsP, maxnormal_proper, maxnormal_normal, maxnormalM, weak_second_isog, exists_comps, quotient_simple, isog_simple, section_repr_isog; all 10 are named in the entry (8 child sites + 2 links), none missing or extra. All 8 shown children's statements and closed_by match the copied code (checked each site line range). Parent and all 8 children close with Qed; grep found no admit/Admitted/sorry/axiom/Abort in the 3 copied files. Shape numbers correct: direct_lemmas=10, glue_lines=58, child_lines=[5,9,3,11,1,11,4,3]; depth=2 matches the two cited child-to-child chains (exists_comps->maxnormal_proper, simple_compsP->trivg_comps). Known-use StrongJordanHolderUniqueness 575-660 confirmed (same skeleton, acomps/maxainv swap). Minor cosmetic note: trivg_comps closed_by swaps forward/backward labels; substance accurate. | reviewer-correctness |
| generality | accept | Move stated beyond the example: well-founded strong induction on a strictly decreasing measure (#|G|) with auxiliary series s1 s2 kept general via 'in s1 s2 *'; goal_shape/use_when abstract 'group order' to 'a strictly decreasing measure', and the opinion isolates the transferable detail; known-use (StrongJordanHolderUniqueness, same file) honestly scoped as a second instance, not claimed as broad reuse. avoid_when and consequences are honest and specific: each names a real proof dependency (measure decrease via maxnormal_proper, exists_comps for the common refinement, quotient_simple/isog_simple as the IH precondition, reflect base cases) and a concrete failure mode (IH cannot apply if the measure does not strictly decrease into N). Good leaves for a bounded prover are addressed: 'Why each lemma is a good leaf' says each child is a self-contained statement closing in one-to-a-few ssreflect lines from named siblings, with shape depth 2 and small child_lines (5,9,3,11,1,11,4,3) — shallow, independently closable obligations. Minor: use_when/avoid_when mix Jordan-Holder-specific machinery (second isomorphism, permutation assembly) into the general criterion, but the general core is separately flagged, so not an objection. | reviewer-generality |
| provenance-licence | accept | provenance pass: check_provenance.py reports 3/3 files byte-identical at 3a90d8b65f77f24e4fd770453c0697233b1c791d; commit, licence CECILL-B and URL agree across entry.json, source.json and sources/math-comp/SOURCE.md; upstream-LICENCE is the CeCILL-B text; all site/claim permalinks and line ranges verified against local copies (parent L165-224, children L126-131/L136-145/L147-158/L100-104/L389-392/L405-417/L461-466/L796-797, known-use StrongJordanHolderUniqueness L575-660); bytes 28830/20676/33871 match entry.json | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/math-comp/math-comp at commit `3a90d8b65f77f24e4fd770453c0697233b1c791d`, under `CECILL-B`; see the [source note](../../sources/math-comp/SOURCE.md) for the licence text and attribution.
