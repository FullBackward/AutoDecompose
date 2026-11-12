# Case split on the typeP-pair dichotomy for no_minSimple_odd_group

| | |
|---|---|
| Kind | instance |
| Move | case-split |
| Language | rocq |
| Status | accepted |
| Source | [odd-order](../../sources/odd-order/SOURCE.md) at `ba734c020d9f` |
| Licence | `CECILL-B` |

## Intent

This entry records the proof of `no_minSimple_odd_group` — the contradiction
that rules out a minimal simple group of odd order, the last step of the
Feit–Thompson theorem — as a theorem-scale decomposition. Its 37-line glue
proof (lines 1217-1253) does no mathematics itself: it is an exhaustive case
split over the maximal subgroups (`FTtypeP_pair_cases`), a `without loss`
ordering `q < p`, one `have := <named project lemma>` per fact, and a single
final application of `FTtype2_exclusion`. Every named child is a closed lemma
written elsewhere in the project; the glue only assembles them.

## The decomposition

### parent `no_minSimple_odd_group`: [`theories/PFsection14.v` lines 1216-1253](https://github.com/math-comp/odd-order/blob/ba734c020d9f7dce5758fa822904dea29e2624ba/theories/PFsection14.v#L1216-L1253) ([local copy](code/theories/PFsection14.v))

```coq
Lemma no_minSimple_odd_group (gT : minSimpleOddGroupType) : False.
Proof.
have [/forall_inP | [S [T [_ W W1 W2 defW pairST]]]] := FTtypeP_pair_cases gT.
  exact/negP/not_all_FTtype1.
have xdefW: W2 \x W1 = W by rewrite dprodC.
have pairTS := typeP_pair_sym xdefW pairST.
pose p := #|W2|; pose q := #|W1|.
have p'q: q != p.
  have [[[ctiW _ _] _ _ _ _] /mulG_sub[sW1W sW2W]] := (pairST, dprodW defW).
  have [cycW _ _] := ctiW; apply: contraTneq (cycW) => eq_pq.
  rewrite (cyclic_dprod defW) ?(cyclicS _ cycW) // -/q eq_pq.
  by rewrite /coprime gcdnn -trivg_card1; have [] := cycTI_nontrivial ctiW.
without loss{p'q} ltqp: S T W1 W2 defW xdefW pairST pairTS @p @q / q < p.
  move=> IH_ST; rewrite neq_ltn in p'q.
  by case/orP: p'q; [apply: (IH_ST S T) | apply: (IH_ST T S)].
have [[_ maxS maxT] _ _ _ _] := pairST.
have [[U StypeP] [V TtypeP]] := (typeP_pairW pairST, typeP_pairW pairTS).
have Stype2: FTtype S == 2 := FTtypeP_max_typeII maxS StypeP ltqp.
have Ttype2: FTtype T == 2 := FTtypeP_min_typeII maxS maxT StypeP TtypeP ltqp.
have /mmax_exists[L maxNU_L]: 'N(U) \proper setT.
  have [[_ ntU _ _] cUU _ _ _] := compl_of_typeII maxS StypeP Stype2.
  by rewrite mFT_norm_proper // mFT_sol_proper abelian_sol.
have /mmax_exists[M maxNV_M]: 'N(V) \proper setT.
  have [[_ ntV _ _] cVV _ _ _] := compl_of_typeII maxT TtypeP Ttype2.
  by rewrite mFT_norm_proper // mFT_sol_proper abelian_sol.
have [[maxL sNU_L] [maxM sNV_M]] := (setIdP maxNU_L, setIdP maxNV_M).
have [frobL sUH _] := FTtypeII_support_facts maxS StypeP Stype2 pairST maxNU_L.
have [frobM _ _] := FTtypeII_support_facts maxT TtypeP Ttype2 pairTS maxNV_M.
have Ltype1 := FT_Frobenius_type1 maxL frobL.
have Mtype1 := FT_Frobenius_type1 maxM frobM.
have [tau1L cohL] := FTtype1_coherence maxL Ltype1.
have [tau1M cohM] := FTtype1_coherence maxM Mtype1.
have [phi Lphi phi1] := FTtype1_ref_irr maxL.
have [psi Mpsi psi1] := FTtype1_ref_irr maxM.
exact: (FTtype2_exclusion pairST maxS maxT StypeP TtypeP ltqp
                          maxNU_L sNU_L sUH frobL Ltype1 cohL Lphi phi1
                          maxNV_M sNV_M frobM Mtype1 cohM Mpsi psi1).
Qed.
```

### child `FTtypeP_pair_cases`: [`theories/PFsection8.v` lines 443-465](https://github.com/math-comp/odd-order/blob/ba734c020d9f7dce5758fa822904dea29e2624ba/theories/PFsection8.v#L443-L465) ([local copy](code/theories/PFsection8.v))

```coq
Lemma FTtypeP_pair_cases :
     (*a*) {in 'M, forall M, FTtype M == 1%N}
  \/ (*b*) exists S, exists T, exists_typeP (fun _ => typeP_pair S T).
Proof.
have [_ [| [[S T] [[maxS maxT] [[W1 W2] /=]]]]] := BGsummaryI gT; first by left.
set W := W1 <*> W2; set V := W :\: (W1 :|: W2).
case=> [[cycW tiV _] [defS defT tiST]] b4 /orP b2 b3.
have [cWW /joing_sub[sW1W sW2W]] := (cyclic_abelian cycW, erefl W).
have ntV: V != set0 by have [] := andP tiV.
suffices{tiST tiV cWW sW1W sW2W b3 b4} tiW12: W1 :&: W2 = 1%g.
  have defW: W1 \x W2 = W by rewrite dprodEY ?(centSS _ _ cWW).
  right; exists S, T; exists S _ _ _ defW; split=> // [|M _ /b4[] // x].
    by do 2?split; rewrite ?mFT_odd // /normedTI tiV nVW setTI /=.
  by case=> <-; rewrite inE mem_orbit ?orbT // ?in_setT.
wlog {b2 T defT maxT} Stype2: S W1 W2 @W @V maxS defS cycW ntV / FTtype S == 2%N.
  move=> IH; case/orP: b2 cycW ntV => /IH; first exact.
  by rewrite setIC /V /W /= joingC setUC; apply.
have{maxS Stype2 defS} prW1: prime #|W1|.
  have [U ? W1x ? ? [[StypeP _ prW1x _] _ _ _ _]] := FTtypeP 2 maxS Stype2.
  by have /imsetP[x _ ->] := of_typeP_compl_conj StypeP defS; rewrite cardJg.
rewrite prime_TIg //; apply: contra ntV => sW12.
by rewrite setD_eq0 (setUidPr sW12) join_subG sW12 /=.
Qed.
```

### child `not_all_FTtype1`: [`theories/PFsection12.v` lines 1302-1361](https://github.com/math-comp/odd-order/blob/ba734c020d9f7dce5758fa822904dea29e2624ba/theories/PFsection12.v#L1302-L1361) ([local copy](code/theories/PFsection12.v))

```coq
Theorem not_all_FTtype1 : ~~ all_FTtype1 gT.
Proof.
apply/negP=> allT1; pose k := #|'M^G|.
have [partGpi coA1 _ [injA1 /(_ allT1)partG _]] := FT_Dade_support_partition gT.
move/forall_inP in allT1.
have [/subsetP maxMG _ injMG exMG] := mmax_transversalP gT.
have{partGpi exMG} kge2: (k >= 2)%N.
  have [L MG_L]: exists L, L \in 'M^G.
    by have [L maxL] := any_mmax gT; have [x] := exMG L maxL; exists (L :^ x)%G.
  have maxL := maxMG L MG_L; have Ltype1 := allT1 L maxL.
  have /Frobenius_kerP[_ ltHL nsHL _] := FTtype1_Frobenius maxL Ltype1.
  rewrite ltnNge; apply: contra (proper_subn ltHL) => leK1.
  rewrite (sub_normal_Hall (Fcore_Hall L)) // (pgroupS (subsetT L)) //=.
  apply: sub_pgroup (pgroup_pi _) => p; rewrite partGpi => /exists_inP[M maxM].
  have /eqP defMG: [set L] == 'M^G by rewrite eqEcard sub1set MG_L cards1.
  have [x] := exMG M maxM; rewrite -defMG => /set1P/(canRL (actK 'JG _))-> /=.
  by rewrite FTcoreJ cardJg FTcore_type1.
pose L (i : 'I_k) : {group gT} := enum_val i; pose H i := ((L i)`_\F)%G.
have MG_L i: L i \in 'M^G by apply: enum_valP.
have maxL i: L i \in 'M by apply: maxMG.
have defH i: (L i)`_\s = H i by rewrite FTcore_type1 ?allT1.
pose frobL_P i E := [Frobenius L i = H i ><| gval E].
have /fin_all_exists[E frobHE] i: exists E, frobL_P i E.
  by apply/existsP/FTtype1_Frobenius; rewrite ?allT1.
have frobL i: [/\ L i \subset G, solvable (L i) & frobL_P i (E i)].
  by rewrite subsetT mmax_sol.
have{coA1} coH_ i j: i != j -> coprime #|H i| #|H j|.
  move=> j'i; rewrite -!defH coA1 //; apply: contra j'i => /imsetP[x Gx defLj].
  apply/eqP/enum_val_inj; rewrite -/(L i) -/(L j); apply: injMG => //.
  by rewrite defLj; apply/esym/orbit_act.
have tiH i: normedTI (H i)^# G (L i).
  have ntA: (H i)^# != set0 by rewrite setD_eq0 subG1 mmax_Fcore_neq1.
  apply/normedTI_memJ_P=> //=; rewrite subsetT; split=> // x z H1x Gz.
  apply/idP/idP=> [H1xz | Lz]; last first.
    by rewrite memJ_norm // (subsetP _ z Lz) // normD1 gFnorm.
  have /subsetP sH1A0: (H i)^# \subset 'A0(L i) by apply: Fcore_sub_FTsupp0.
  have [/(sub_in2 sH1A0)wccH1 [_ maxN] Nfacts] := FTsupport_facts (maxL i).
  suffices{z Gz H1xz wccH1} sCxLi: 'C[x] \subset L i.
    have /imsetP[y Ly defxz] := wccH1 _ _ H1x H1xz (imset_f _ Gz).
    rewrite -[z](mulgKV y) groupMr // (subsetP sCxLi) // !inE conjg_set1.
    by rewrite conjgM defxz conjgK.
  apply/idPn=> not_sCxM; pose D := [set y in 'A0(L i) | ~~ ('C[y] \subset L i)].
  have Dx: x \in D by rewrite inE sH1A0.
  have{maxN} /mem_uniq_mmax[maxN sCxN] := maxN x Dx.
  have Ntype1 := allT1 _ maxN.
  have [_ _ /setDP[/bigcupP[y NFy /setD1P[ntx cxy]] /negP[]]] := Nfacts x Dx.
  rewrite FTsupp1_type1 Ntype1 // in NFy cxy *.
  have /Frobenius_kerP[_ _ _ regFN] := FTtype1_Frobenius maxN Ntype1.
  by rewrite 2!inE ntx (subsetP (regFN y NFy)).
have /negP[] := no_coherent_Frobenius_partition (mFT_odd _) kge2 frobL tiH coH_.
rewrite eqEsubset sub1set !inE andbT; apply/andP; split; last first.
  apply/bigcupP=> [[i _ /imset2P[x y /setD1P[ntx _] _ Dxy]]].
  by rewrite -(conjg_eq1 x y) -Dxy eqxx in ntx.
rewrite subDset setUC -subDset -(cover_partition partG).
apply/bigcupsP=> _ /imsetP[Li MG_Li ->]; pose i := enum_rank_in MG_Li Li.
rewrite (bigcup_max i) //=; have ->: Li = L i by rewrite /L enum_rankK_in.
rewrite -FT_Dade1_supportE //; apply/bigcupsP=> x A1x; apply: imset2S => //.
move: (FT_Dade1_hyp _) (tiH i); rewrite -defH => _ /Dade_normedTI_P[_ -> //].
by rewrite mul1g sub1set -/(H i) -defH.
Qed.
```

### child `typeP_pair_sym`: [`theories/PFsection8.v` lines 436-440](https://github.com/math-comp/odd-order/blob/ba734c020d9f7dce5758fa822904dea29e2624ba/theories/PFsection8.v#L436-L440) ([local copy](code/theories/PFsection8.v))

```coq
Lemma typeP_pair_sym S T W W1 W2 (defW : W1 \x W2 = W) (xdefW : W2 \x W1 = W) :
  typeP_pair S T defW -> typeP_pair T S xdefW.
Proof.
by case=> [[/cyclicTIhyp_sym ? ? ?] [? ?]]; rewrite setIC setUC orbC => ? ? [].
Qed.
```

### child `FTtypeP_max_typeII`: [`theories/PFsection14.v` lines 491-492](https://github.com/math-comp/odd-order/blob/ba734c020d9f7dce5758fa822904dea29e2624ba/theories/PFsection14.v#L491-L492) ([local copy](code/theories/PFsection14.v))

```coq
Fact FTtypeP_max_typeII : FTtype S == 2%N.
Proof. by have [[_ ->]] := FTtypeP_facts maxS StypeP. Qed.
```

### child `FTtypeP_min_typeII`: [`theories/PFsection14.v` lines 733-854](https://github.com/math-comp/odd-order/blob/ba734c020d9f7dce5758fa822904dea29e2624ba/theories/PFsection14.v#L733-L854) ([local copy](code/theories/PFsection14.v))

```coq
Lemma FTtypeP_min_typeII : FTtype T == 2%N.
Proof.
apply: contraLR v1p_gt_u1q => notTtype2; rewrite -leqNgt -leC_nat.
have [o_betaT0_eta _ [Ttype3 _]] := FTtype34_structure maxT TtypeP notTtype2.
have Ttype_gt2: (2 < FTtype T)%N by rewrite (eqP Ttype3).
have [[_ _ frobVW2 cVV] _ _ _ _] := FTtypeP_facts _ TtypeP.
pose calT1 := seqIndD QV T QV Q; have sT10: cfConjC_subset calT1 calT0.
  by apply/seqInd_conjC_subset1; rewrite /= FTcore_eq_der1.
rewrite (FTtypeP_reg_Fcore maxT TtypeP) (group_inj (joingG1 _)) in o_betaT0_eta.
do [rewrite -/calT1; set eta_0 := \sum_j _] in o_betaT0_eta.
have scohT1: subcoherent calT1 tauT rmR_T := subset_subcoherent scohT0 sT10.
have [nsQQV sVQV _ _ _] := sdprod_context defQV.
have nsQVT: QV <| T := der_normal 1 T.
have calT1_1p zeta: zeta \in calT1 -> zeta 1%g = p%:R.
  case/seqIndP=> s /setDP[kerQs _] -> /=; rewrite inE in kerQs.
  rewrite cfInd1 ?gFsub // -(index_sdprod defT) lin_char1 ?mulr1 //.
  rewrite lin_irr_der1 (subset_trans _ kerQs) // der1_min ?normal_norm //.
  by rewrite -(isog_abelian (sdprod_isog defQV)).
have [tau1T cohT1]: coherent calT1 T^# tauT.
  apply/(uniform_degree_coherence scohT1)/(@all_pred1_constant _ p%:R).
  by apply/allP=> _ /mapP[zeta T1zeta ->]; rewrite /= calT1_1p.
have irrT1: {subset calT1 <= irr T}.
  move=> _ /seqIndP[s /setDP[kerQs nz_s] ->]; rewrite inE in kerQs.
  rewrite inE subGcfker in nz_s; rewrite -(quo_IirrK nsQQV kerQs) mod_IirrE //.
  rewrite cfIndMod ?normal_sub ?cfMod_irr ?gFnormal //.
  rewrite irr_induced_Frobenius_ker ?quo_Iirr_eq0 //=.
  have /sdprod_isom[nQ_VW1 /isomP[injQ <-]] := Ptype_Fcore_sdprod TtypeP.
  have ->: (QV / Q)%g = (V / Q)%g by rewrite -(sdprodW defQV) quotientMidl.
  have ->: (V / Q)%g = restrm nQ_VW1 (coset Q) @* V.
    by rewrite morphim_restrm (setIidPr _) // joing_subl.
  by rewrite injm_Frobenius_ker // (FrobeniusWker frobVW2).
have [[A0betaS PVbetaS] _ [_]] := FTtypeP_bridge_facts maxS StypeP.
rewrite -/q -/u; set Gamma := FTtypeP_bridge_gap _ _ => oGa1 R_Ga lb_Ga _.
have oT1eta: orthogonal (map tau1T calT1) (map sigma (irr W)).
  apply/orthogonalP=> _ _ /mapP[zeta T1zeta ->] /mapP[omega Womega ->].
  have{omega Womega} [i [j ->]] := cycTIirrP defW Womega.
  by rewrite (cycTIisoC _ pddT) (coherent_ortho_cycTIiso _ sT10 cohT1) ?irrT1.
have [[Itau1T Ztau1T] Dtau1T] := cohT1.
have nzT1_Ga zeta: zeta \in calT1 -> `|'[Gamma, tau1T zeta]| ^+ 2 >= 1.
  have Z_Ga: Gamma \in 'Z[irr G].
    rewrite rpredD ?cycTIiso_vchar // rpredB ?rpred1 ?Dade_vchar // zchar_split.
    by rewrite A0betaS ?Iirr1_neq0 // rpredB ?cfInd_vchar ?rpred1 ?irr_vchar.
  move=> T1zeta; rewrite expr_ge1 ?normr_ge0 // norm_intr_ge1 //.
    by rewrite Cint_cfdot_vchar ?Ztau1T ?(mem_zchar T1zeta).
  suffices: ('[Gamma, tau1T zeta] == 1 %[mod 2])%C.
    by apply: contraTneq => ->; rewrite (eqCmod_nat 2 0 1).
  pose betaT0 := nu_ 0 - zeta.
  have{o_betaT0_eta} o_eta0_betaT0 j: '[eta_ 0 j, tauT betaT0] = (j == 0)%:R.
    transitivity '[eta_ 0 j, eta_0]; rewrite (cycTIisoC _ pddT).
      apply/eqP; rewrite -subr_eq0 -cfdotBr cfdotC.
      by rewrite (orthoPl (o_betaT0_eta _ _)) ?conjC0 // map_f ?mem_irr.
    rewrite cfdot_sumr (bigD1 0) //= cfdot_cycTIiso andbT big1 ?addr0 //.
    by move=> i /negPf nz_i; rewrite cfdot_cycTIiso andbC eq_sym nz_i.
  have QVbetaT0: betaT0 \in 'CF(T, QV^#).
    rewrite cfun_onD1 rpredB ?(seqInd_on _ T1zeta) //=.
      by rewrite /nu_ -cfInd_prTIres cfInd_normal.
    by rewrite !cfunE prTIred_1 prTIirr0_1 mulr1 calT1_1p ?subrr.
  have A0betaT0: betaT0 \in 'CF(T, 'A0(T)).
    by rewrite (cfun_onS (FTsupp1_sub0 _)) // /'A1(T) ?FTcore_eq_der1.
  have ZbetaT0: betaT0 \in 'Z[irr T].
    by rewrite rpredB ?char_vchar ?(seqInd_char T1zeta) ?prTIred_char.
  pose Delta := tauT betaT0 - 1 + tau1T zeta.
  have nz_i1: #1 != 0 := Iirr1_neq0 ntW2.
  rewrite -(canLR (addKr _) (erefl Delta)) opprB cfdotDr cfdotBr oGa1 add0r.
  rewrite cfdotDl cfdotBl -/betaS [X in _ - _ + X]o_eta0_betaT0 (negPf nz_i1) // addr0 opprB.
  rewrite -(cycTIiso1 pddS) -(cycTIirr00 defW) {}[X in X + _ + _]o_eta0_betaT0 mulr1n.
  have QV'betaS: tauS betaS \in 'CF(G, ~: class_support QV^# G).
    have [_ [pP _] _ _ [_ ->]] := FTtypeP_facts _ StypeP; rewrite ?A0betaS //.
    apply: cfun_onS (cfInd_on (subsetT S) (PVbetaS _ nz_i1)).
    apply/subsetP=> x PWx; rewrite inE.
    have{PWx}: p \in \pi(#[x]).
      case/imset2P: PWx => {}x y PWx _ ->; rewrite {y}orderJ.
      case/setUP: PWx => [/setD1P[ntx Px] | /imset2P[{}x y Wx _ ->]].
        rewrite -p_rank_gt0 -rank_pgroup ?rank_gt0 ?cycle_eq1 //.
        exact: mem_p_elt (abelem_pgroup pP) Px.
      case/setDP: Wx; rewrite {y}orderJ; have [_ <- cW12 _] := dprodP defW.
      case/mulsgP=> {}x y W1x W2y ->; have cyx := centsP cW12 _ W2y _ W1x.
      have [-> | nty _] := eqVneq y 1%g; first by rewrite inE mulg1 W1x.
      have p'x: p^'.-elt x.
        by rewrite (mem_p_elt _ W1x) /pgroup ?pnatE ?inE ?ltn_eqF.
      have p_y: p.-elt y by rewrite (mem_p_elt (pnat_id _)).
      rewrite -cyx orderM ?(pnat_coprime p_y) // pi_ofM // inE /=.
      by rewrite -p_rank_gt0 -rank_pgroup // rank_gt0 cycle_eq1 nty.
    apply: contraL => /imset2P[z y /setD1P[_ QVz] _ ->]; rewrite {x y}orderJ.
    rewrite -p'natEpi // [_.-nat _](mem_p_elt _ QVz) // /pgroup ?p'natE //.
    rewrite -prime_coprime // coprime_sym (coprime_sdprod_Hall_r defT).
    by have [[]] := TtypeP.
  have [_ _ _ _ [_ -> //]] := FTtypeP_facts _ TtypeP.
  rewrite (cfdotElr QV'betaS (cfInd_on _ QVbetaT0)) ?subsetT //=.
  rewrite setIC setICr big_set0 mulr0 subr0 addrC /eqCmod addrK.
  rewrite cfdot_real_vchar_even ?mFT_odd ?oGa1 ?rpred0 //; split.
    rewrite rpredD ?Ztau1T ?(mem_zchar T1zeta) // rpredB ?rpred1 //.
    by rewrite Dade_vchar // zchar_split ZbetaT0.
  rewrite /cfReal -subr_eq0 opprD opprB rmorphD /= rmorphB rmorph1 /= addrACA.
  rewrite !addrA subrK -Dade_aut -linearB /= -/tauT rmorphB opprB /=.
  rewrite -prTIred_aut aut_Iirr0 -/nu_ [sum in tauT sum]addrC addrA subrK.
  rewrite -Dtau1T.
    by rewrite (zchar_onS _ (seqInd_sub_aut_zchar _ _ _)) // setSD ?der_sub.
  rewrite raddfB -addrA addrC addrA subrK subr_eq0.
  by rewrite (cfConjC_Dade_coherent cohT1) ?mFT_odd ?irrT1.
have [Y T1_Y [X [defGa oYX oXT1]]] := orthogonal_split (map tau1T calT1) Gamma.
apply: le_trans (lb_Ga X Y _ _ _); first 1 last; rewrite 1?addrC //.
- by rewrite cfdotC oYX conjC0.
- by apply/orthoPl=> eta Weta; rewrite (span_orthogonal oT1eta) // memv_span.
have ->: v.-1 = (p * size calT1)%N; last rewrite mulKn ?prime_gt0 //.
  rewrite [p](index_sdprod defT); have isoV := sdprod_isog defQV.
  rewrite [v](card_isog isoV) -card_Iirr_abelian -?(isog_abelian isoV) //.
  rewrite -(card_imset _ (can_inj (mod_IirrK nsQQV))) (cardD1 0) /=.
  rewrite -{1}(mod_Iirr0 QV Q) imset_f //=.
  rewrite (size_irr_subseq_seqInd _ (subseq_refl _)) //=.
  apply: eq_card => s; rewrite !inE mem_seqInd ?gFnormal // !inE subGcfker.
  congr (_ && _); apply/idP/idP=> [/imsetP[r _ ->] | kerQs].
    by rewrite mod_IirrE ?cfker_mod.
  by rewrite -(quo_IirrK nsQQV kerQs) imset_f.
have o1T1: orthonormal (map tau1T calT1).
  rewrite map_orthonormal ?(sub_orthonormal irrT1) ?seqInd_uniq //.
  exact: irr_orthonormal.
have [_ -> ->] := orthonormal_span o1T1 T1_Y.
rewrite cfnorm_sum_orthonormal // big_map -sum1_size natr_sum !big_seq.
apply: ler_sum => // zeta T1zeta; rewrite -(canLR (addrK X) defGa).
by rewrite cfdotBl (orthoPl oXT1) ?subr0 ?nzT1_Ga ?map_f.
Qed.
```

### child `compl_of_typeII`: [`theories/PFsection8.v` lines 387-395](https://github.com/math-comp/odd-order/blob/ba734c020d9f7dce5758fa822904dea29e2624ba/theories/PFsection8.v#L387-L395) ([local copy](code/theories/PFsection8.v))

```coq
Remark compl_of_typeII : FTtype M == 2%N -> of_typeII M U defW.
Proof.
move=> Mtype2.
have [Ux Wx W1x W2x defWx [[MtypePx _ _ _]]] := FTtypeP 2 maxM Mtype2.
have [x [Mx <- _ _ _]] := of_typeP_conj MtypePx; rewrite -/M' -/H.
rewrite abelianJ normJ -{1}(conjGid Mx) conjSg => cUU not_sNUM M'typeF defH.
split=> //; first by apply: compl_of_typeII_IV; rewrite // (eqP Mtype2).
by apply: compl_of_typeF M'typeF; rewrite defH; have [_ []] := MtypeP.
Qed.
```

### child `FTtypeII_support_facts`: [`theories/PFsection13.v` lines 1658-1776](https://github.com/math-comp/odd-order/blob/ba734c020d9f7dce5758fa822904dea29e2624ba/theories/PFsection13.v#L1658-L1776) ([local copy](code/theories/PFsection13.v))

```coq
Lemma FTtypeII_support_facts T L (Q := T`_\F) (H := L`_\F) :
    FTtype S == 2%N -> typeP_pair S T defW -> L \in 'M('N(U)) ->
  [/\ (*a*) [Frobenius L with kernel H],
      (*b*) U \subset H
    & (*c*) H ><| W1 = L \/ (exists2 y, y \in Q & H ><| (W1 <*> W2 :^ y) = L)].
Proof.
move=> Stype2 pairST /setIdP[maxL sNU_L].
have [pgt0 qgt0] := (ltnW (ltnW pgt2), ltnW (ltnW qgt2)).
have [[_ _ maxT] _ _ _ allST] := pairST.
have [[_ ntU _ _] _ not_sNU_S _ _] := compl_of_typeII maxS StypeP Stype2.
have [[_ _ frobUW1 cUU] _ _ _ _] := Sfacts.
have xdefW: W2 \x W1 = W by rewrite dprodC.
have [V TtypeP] := typeP_pairW (typeP_pair_sym xdefW pairST).
have [abelQ oQ]: q.-abelem Q /\ #|Q| = (q ^ p)%N.
  by have [] := FTtypeP_facts maxT TtypeP.
have sUL: U \subset L := subset_trans (normG U) sNU_L.
have [/mulG_sub[sPPU sUPU] sPUS] := (sdprodW defPU, der_sub 1 S).
have nUW1: W1 \subset 'N(U) by have [_ []] := StypeP.
have sW1L := subset_trans nUW1 sNU_L.
have Ltype1: FTtype L == 1%N.
  apply: contraR not_sNU_S => /allST/setUP[]// /imsetP[y _ defL].
    have hallU: \pi(U).-Hall(S) U.
      have /Hall_pi/(subHall_Hall _ (piSg sUPU)): Hall PU U.
        have /pHall_Hall:= pHall_subl sPPU sPUS (Fcore_Hall S).
        by rewrite (sdprod_Hall defPU).
      by apply; rewrite Hall_pi // -(coprime_sdprod_Hall_l defS).
    have hallUy: \pi(U).-Hall(S) (U :^ y^-1).
      by rewrite pHallE sub_conjgV -defL sUL /= cardJg -(card_Hall hallU).
    have [x /conjGid <- ->] := Hall_trans (mmax_sol maxS) hallU hallUy.
    by rewrite !normJ conjSg sub_conjgV -defL.
  have oH: #|H| = (q ^ p)%N by rewrite /H defL FcoreJ cardJg.
  have sW1H: W1 \subset H.
    rewrite (sub_normal_Hall (Fcore_Hall L)) ?gFnormal //=.
    by rewrite oH pi_of_exp ?prime_gt0 // pgroup_pi.
  have regUW1: 'C_U(W1) = 1%g := Frobenius_trivg_cent frobUW1.
  have /negP[] := ntU; rewrite -subG1 -regUW1 subsetIidl (sameP commG1P trivgP).
  have /coprime_TIg <-: coprime #|U| #|H|.
    by rewrite oH coprime_pexpr ?(coprimeSg sUPU).
  rewrite commg_subI //; last by rewrite subsetI sW1H.
  by rewrite subsetIidl (subset_trans sUL) ?gFnorm.
have frobL := FTtype1_Frobenius maxL Ltype1.
have solH: solvable H by rewrite nilpotent_sol ?Fcore_nil.
have coHW1: coprime #|H| #|W1|.
  rewrite -(coprime_pexpr _ _ pgt0) -oQ.
  apply/(coprimegS (Fcore_sub_FTcore maxT))/(coprimeSg (Fcore_sub_FTcore maxL)).
  have [_ -> //] := FT_Dade_support_partition gT.
  have: FTtype T != 1%N := FTtypeP_neq1 maxT TtypeP.
  by apply: contra => /imsetP[y _ ->] /=; rewrite FTtypeJ.
have tiHW1: H :&: W1 = 1%g := coprime_TIg coHW1.
have sUH: U \subset H; last split=> //.
  have [ntH _ /andP[sHL nHL] regHL] := Frobenius_kerP frobL.
  have regHE E: gval E != 1%g -> E \subset L -> H :&: E = 1%g -> 'C_H(E) = 1%g.
    move=> ntE sEL tiHE; apply: contraNeq ntE => /trivgPn[x /setIP[Hx cEx] ntx].
    rewrite -subG1 -tiHE subsetIidr (subset_trans _ (regHL x _)) ?inE ?ntx //.
    by rewrite subsetI sEL sub_cent1.
  suffices /trivgPn[x /setIP[Hx Ux] ntx]: H :&: U != 1%g.
    apply: subset_trans (regHL x _); last by rewrite !inE ntx.
    by rewrite subsetI sUL sub_cent1 (subsetP cUU).
  apply: contraNneq (ntH) => tiHU; rewrite trivg_card1.
  have [nHU nHW1] := (subset_trans sUL nHL, subset_trans sW1L nHL).
  have nHUW1: U <*> W1 \subset 'N(H) by rewrite join_subG nHU.
  have coHUW1: coprime #|H| #|U <*> W1|.
    have [/eqP defUW1 _] := andP frobUW1.
    rewrite (sdprodWY defUW1) -(sdprod_card defUW1) coprimeMr coHW1 andbT.
    have defHU: H ><| U = H <*> U by rewrite sdprodEY.
    rewrite (coprime_sdprod_Hall_l defHU).
    apply: pHall_Hall (pHall_subl (joing_subl _ _) _ (Fcore_Hall L)).
    by rewrite join_subG sHL.
  have [_ _] := Frobenius_Wielandt_fixpoint frobUW1 nHUW1 coHUW1 solH.
  by move->; rewrite regHE // cards1 exp1n.
have [E sW1E frobHE]: exists2 E, W1 \subset gval E & [Frobenius L = H ><| E].
  have [E frobHE] := existsP frobL; have [/eqP defL _] := andP frobHE.
  have hallE: \pi(H)^'.-Hall(L) E.
    by rewrite -(compl_pHall E (Fcore_Hall L)) sdprod_compl.
  have [|x Lx sW1Ex] := Hall_subJ (mmax_sol maxL) hallE sW1L.
    by rewrite /pgroup -coprime_pi' ?cardG_gt0.
  rewrite -(FrobeniusJ x) conjGid // (normsP (gFnorm _ _)) // in frobHE.
  by exists (E :^ x)%G.
have [defL ntH ntE _ _] := Frobenius_context frobHE.
have [_ sEL _ nHE _] := sdprod_context defL.
have solE := solvableS sEL (mmax_sol maxL).
have [regHE regEH] := (Frobenius_reg_ker frobHE, Frobenius_reg_compl frobHE).
have qW1: q.-group W1 by apply: pnat_id.
have cycEr (r : nat) R: r.-group R -> R \subset E -> cyclic R.
  move=> rR sRE; have nHR := subset_trans sRE nHE.
  apply: odd_regular_pgroup_cyclic rR (mFT_odd _) ntH nHR _.
  by move=> y /setD1P[nty Ry]; rewrite regHE // !inE nty (subsetP sRE).
have /normal_norm nW1E: W1 <| E.
  exact: prime_odd_regular_normal (mFT_odd E) _ _ _ (Frobenius_reg_ker frobHE).
have defNW1: Q ><| W2 = 'N(W1).
  by have [] := FTtypeP_norm_cent_compl maxT TtypeP.
have [nsQN sW2N _ _ _] := sdprod_context defNW1.
have sylQ: q.-Sylow('N(W1)) Q.
  rewrite /pHall normal_sub // abelem_pgroup //=.
  by rewrite -(index_sdprod defNW1) pnatE //= !inE eq_sym.
have hallW2: q^'.-Hall('N(W1)) W2 by rewrite -(compl_pHall _ sylQ) sdprod_compl.
pose Q1 := Q :&: E; have sylQ1: q.-Sylow(E) Q1 by apply: setI_normal_Hall nW1E.
have defQ1: Q1 = W1.
  have abelQ1: q.-abelem Q1 := abelemS (subsetIl Q E) abelQ.
  have sW1Q: W1 \subset Q by have [_ _ _ []] := TtypeP.
  have sW1Q1: W1 \subset Q1 by apply/subsetIP.
  have ntQ1: Q1 != 1%g by apply: subG1_contra ntW1.
  apply/esym/eqP; rewrite eqEcard sW1Q1 (cyclic_abelem_prime abelQ1) //=.
  by rewrite (cycEr q) ?(pHall_pgroup sylQ1) ?subsetIr.
have [P2 hallP2] := Hall_exists q^' solE; have [sP2E q'P2 _] := and3P hallP2.
have defE: W1 ><| P2 = E.
  apply/(sdprod_normal_p'HallP _ hallP2); rewrite /= -defQ1 //.
  by rewrite /Q1 setIC norm_normalI // (subset_trans nW1E) ?normal_norm.
have [P2_1 | ntP2] := eqsVneq P2 1%g.
  by left; rewrite -defE P2_1 sdprodg1 in defL.
have solNW1: solvable 'N(W1).
  by rewrite mFT_sol ?mFT_norm_proper // mFT_sol_proper (solvableS sW1E).
have [zy /=] := Hall_subJ solNW1 hallW2 (subset_trans sP2E nW1E) q'P2.
rewrite -{1}(sdprodWC defNW1) => /mulsgP[z y W2z Qy ->{zy}].
rewrite conjsgM (conjGid W2z) {z W2z} => sP2W2y.
right; exists y => //; congr (_ ><| _ = _): defL.
rewrite -(sdprodWY defE); congr (W1 <*> _).
by apply/eqP; rewrite eqEsubset sP2W2y prime_meetG ?cardJg ?(setIidPr _).
Qed.
```

### child `FTtype2_exclusion`: [`theories/PFsection14.v` lines 1211-1212](https://github.com/math-comp/odd-order/blob/ba734c020d9f7dce5758fa822904dea29e2624ba/theories/PFsection14.v#L1211-L1212) ([local copy](code/theories/PFsection14.v))

```coq
Lemma FTtype2_exclusion : False.
Proof. by have /negP[] := not_charUH; rewrite /= defH char_refl. Qed.
```

### The other four direct lemmas (listed, not excerpted)

The glue also applies these named project lemmas directly; they carry the
Frobenius/coherence/character plumbing whose outputs feed the final
`FTtype2_exclusion`, and each is a one-line application of an earlier lemma:

- `typeP_pairW` — [`theories/PFsection8.v` lines 470-498](https://github.com/math-comp/odd-order/blob/ba734c020d9f7dce5758fa822904dea29e2624ba/theories/PFsection8.v#L470-L498):
  `Lemma typeP_pairW S T W W1 W2 (defW : W1 \x W2 = W) : typeP_pair S T defW -> exists U : {group gT}, of_typeP S U defW.`
  Applied at line 1237 to turn the pair into Skolemised `of_typeP` predicates `StypeP`, `TtypeP`.
- `FT_Frobenius_type1` — [`theories/PFsection12.v` lines 491-495](https://github.com/math-comp/odd-order/blob/ba734c020d9f7dce5758fa822904dea29e2624ba/theories/PFsection12.v#L491-L495):
  `Lemma FT_Frobenius_type1 : FTtype L == 1%N.` Applied at lines 1244-1245 for `Ltype1`, `Mtype1`.
- `FTtype1_coherence` — [`theories/PFsection13.v` lines 1963-1969](https://github.com/math-comp/odd-order/blob/ba734c020d9f7dce5758fa822904dea29e2624ba/theories/PFsection13.v#L1963-L1969):
  `Lemma FTtype1_coherence : coherent calL L^# tauL.` Applied at lines 1246-1247 for `cohL`, `cohM`.
- `FTtype1_ref_irr` — [`theories/PFsection12.v` lines 56-60](https://github.com/math-comp/odd-order/blob/ba734c020d9f7dce5758fa822904dea29e2624ba/theories/PFsection12.v#L56-L60):
  `Lemma FTtype1_ref_irr : exists2 phi, phi \in calS & phi 1%g = #|L : H|%:R.` Applied at lines 1248-1249 for `phi`, `psi`.

## How the parts fit

The parent is a pure assembly line. The lemma graph (each arrow is a use in
the glue at the line given):

```
no_minSimple_odd_group                       (PFsection14.v:1216-1253)
├─ FTtypeP_pair_cases :1218        exhaustive split: (a) all maximal subgroups type 1
│   │                                        ∨ (b) exists a typeP pair (S,T)
│   ├─ not_all_FTtype1 :1219        closes arm (a) by contradiction
│   └─ typeP_pair_sym :1221         swaps S/T, W1/W2 → pairTS, for the symmetry below
│       without loss q < p :1228    splits p'q: q != p into q < p ∨ p < q (case/orP)
│       ├─ typeP_pairW :1237        → StypeP, TtypeP (Skolemised)
│       ├─ FTtypeP_max_typeII :1233 → FTtype S == 2  (Stype2)
│       ├─ FTtypeP_min_typeII :1234 → FTtype T == 2  (Ttype2)
│       ├─ compl_of_typeII :1236,39 → abelian U,V ⇒ 'N(U),'N(V) proper ⇒ maximal L,M
│       ├─ FTtypeII_support_facts :1242,43 → [Frobenius L with kernel H] (frobL, frobM)
│       ├─ FT_Frobenius_type1 :1244,45 → Ltype1, Mtype1
│       ├─ FTtype1_coherence :1246,47 → cohL, cohM
│       ├─ FTtype1_ref_irr :1248,49 → phi, psi
│       └─ FTtype2_exclusion :1250-52 → False  (16-argument call)
```

Why each child is a good leaf:

- **`FTtypeP_pair_cases`** is the dichotomy itself, stated and proved as its
  own lemma (Peterfalvi Theorem 8.8). Its statement *is* the disjunction, so
  the parent's exhaustiveness obligation is discharged by importing it rather
  than re-proving it.
- **`not_all_FTtype1`** closes the left arm in one line — it is exactly the
  negation of arm (a), so `exact/negP/not_all_FTtype1` finishes.
- **`typeP_pair_sym`** and **`typeP_pairW`** are the two symmetric plumbing
  facts: one swaps the pair, the other Skolemises it into `of_typeP`. Both
  close by one rewrite/`case`, with no further content.
- **`FTtypeP_max_typeII`** / **`FTtypeP_min_typeII`** pin down the two halves
  of the pair as type II. The max side is a one-liner (`FTtypeP_facts`); the
  min side is the only long proof in the set (121 lines), a contradiction
  against the standing hypothesis `v1p_gt_u1q`.
- **`compl_of_typeII`** and **`FTtypeII_support_facts`** supply the Frobenius
  context (abelian complements `U`, `V`, and `[Frobenius L with kernel H]`)
  that lets the glue introduce maximal `L`, `M`.
- **`FT_Frobenius_type1`**, **`FTtype1_coherence`**, **`FTtype1_ref_irr`** are
  the type-1 character machinery, each a one-line application of a sibling.
- **`FTtype2_exclusion`** is the terminal contradiction, closing from two
  earlier facts of the same section (`not_charUH`, `defH`) in one line.

So the parent is a bounded-prover skeleton: every hole is a `have := <closed
lemma>`, and the single creative step of the glue is the `without loss`
ordering that lets the pair argument be done once.

## Why it is good

1. (check) All 12 lemmas the glue applies directly are closed statements —
   `Lemma`, `Theorem`, `Fact` or `Remark` ending in `Qed.` at the pinned commit
   — and none is an axiom, a hypothesis or an admitted goal. See the 12
   permalinks in claim 1 of `entry.json`.
2. (check) The case split is exhaustive and total: `FTtypeP_pair_cases` returns
   the disjunction `{in 'M, forall M, FTtype M == 1%N} \/ exists S T,
   exists_typeP (fun _ => typeP_pair S T)`, and the parent's single
   `have [...] := FTtypeP_pair_cases gT` covers both arms (left by
   `not_all_FTtype1`, right by the pair argument) — `PFsection8.v#L443-L445`,
   `PFsection14.v#L1218-L1219`.
3. (measurement) The proof body is 37 lines (`PFsection14.v#L1217-L1253`) and
   applies 12 distinct named project lemmas across 4 files; the longest
   dependency chain below the parent that I checked is 4 deep:
   `no_minSimple_odd_group -> FTtype2_exclusion -> not_charUH ->
   no_full_FT_Galois_structure -> prime_dim_normed_finField`.
4. (author-statement) The file states its role plainly — "This file covers
   Peterfalvi, Section 14: Non_existence of G. It completes the proof of the
   Odd Order theorem." (`PFsection14.v#L22-L25`) — and the parent is consumed
   immediately by `Feit_Thompson` via `minSimpleOdd_ind`
   (`PFsection14.v#L1255-L1257`).

In my opinion the detail worth copying is the *single-point assembly*: the glue
accumulates facts under `have` and discharges them in one `exact:` whose
argument is a 16-item positional list. That is exactly the shape AutoDecompose
must produce — a skeleton with one bounded hole per named lemma, and no
creative proof steps in between.

## When to use it, and when not

Use it when an impossibility theorem reduces to a finite, exhaustive dichotomy
that is *already* a proved project lemma (stated as a `\/` or a classification
result), so the parent imports exhaustiveness instead of proving it. It works
best when both arms close by named lemmas, and when a symmetry (`without loss`
/ `wlog`) lets one ordering stand for both branches — here the `q < p` swap via
`typeP_pair_sym`.

Avoid it when the disjunction is not yet proved (then the split itself is a
child carrying its own exhaustiveness obligation — survey F rule 5), when the
arms need genuinely different arguments that do not factor through named
lemmas, or when the closing lemma takes a long positional argument list that a
reshuffle of intermediate facts would silently break.

## Consequences

The split creates two obligations — the left and right arms of the `\/` — plus,
inside the right arm, a `without loss q < p` that swaps `S`/`T` and `W1`/`W2`
via `typeP_pair_sym`, so one ordering stands for both. The exhaustiveness is
carried by `FTtypeP_pair_cases`, so the parent never re-proves it. The final
`FTtype2_exclusion` is applied to a 16-argument list assembled purely by
`have := <lemma>`; if any intermediate fact changes shape (for instance
`FTtypeII_support_facts` returning a different conjunction), the single
`exact:` call fails.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/coq-action.yml (name: CI) builds coq-mathcomp-odd-order.opam via docker-coq-action on push to master and PRs; _CoqProject lists theories/PFsection14.v (line 23). Pinned commit ba734c0 is HEAD of master (default branch, 2026-08-20). nix-action-master.yml also has an odd-order job on push to master. | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 4 file(s) byte-identical at ba734c020d9f7dce5758fa822904dea29e2624ba | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Opened the copied code (byte-identical per provenance) and the 12 named lemmas are closed Lemma/Theorem/Fact/Remark ending in Qed: compl_of_typeII (PFsection8.v L387-395 Qed), typeP_pair_sym (L436-440 Qed), FTtypeP_pair_cases (L443-465 Qed), typeP_pairW (L470-498 Qed), FTtype1_ref_irr (PFsection12.v L56-60 Qed), FT_Frobenius_type1 (L491-495 Qed), not_all_FTtype1 (L1302-1361 Qed), FTtypeII_support_facts (PFsection13.v L1658-1776 Qed), FTtype1_coherence (L1963-1969 Qed), FTtypeP_max_typeII (PFsection14.v L491-492 Qed), FTtypeP_min_typeII (L733-854 Qed), FTtype2_exclusion (L1211-1212 Qed). None is axiom/hypothesis/Admitted. | verifier |
| 2 | verified | PFsection8.v L443-445: FTtypeP_pair_cases returns the disjunction '{in 'M, forall M, FTtype M == 1%N} \/ exists S, exists T, exists_typeP (fun _ => typeP_pair S T)'. Parent at PFsection14.v L1218-1219: 'have [/forall_inP | [S [T [_ W W1 W2 defW pairST]]]] := FTtypeP_pair_cases gT.' with left arm 'exact/negP/not_all_FTtype1.' and right arm carrying the pair; both arms covered, exhaustive. | verifier |
| 3 | verified | Parent proof body is PFsection14.v L1217-1253 (37 lines). The body applies 12 distinct named lemmas (FTtypeP_pair_cases, not_all_FTtype1, typeP_pair_sym, typeP_pairW, FTtypeP_max_typeII, FTtypeP_min_typeII, compl_of_typeII, FTtypeII_support_facts, FT_Frobenius_type1, FTtype1_coherence, FTtype1_ref_irr, FTtype2_exclusion) across 4 files (PFsection8/12/13/14). Chain verified: no_minSimple_odd_group -> FTtype2_exclusion (L1250 'exact: (FTtype2_exclusion ...)'), FTtype2_exclusion -> not_charUH (L1212 ':= not_charUH'), not_charUH -> no_full_FT_Galois_structure (L639 'case: no_full_FT_Galois_structure'), no_full_FT_Galois_structure -> prime_dim_normed_finField (L487 'exact: (prime_dim_normed_finField ...)'). prime_dim_normed_finField is a Theorem at BGappendixC.v L763. | verifier |
| 4 | verified | PFsection14.v L23-24: '(* This file covers Peterfalvi, Section 14: Non_existence of G. *)' and '(* It completes the proof of the Odd Order theorem. *)'. L1255-1257: 'Theorem Feit_Thompson (gT : finGroupType) (G : {group gT}) : odd #|G| -> solvable G. Proof. exact: (minSimpleOdd_ind no_minSimple_odd_group). Qed.' — matches the quoted author statement exactly. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent no_minSimple_odd_group (PFsection14.v:1216-1253) is a 37-line proof that is exactly an exhaustive case split (FTtypeP_pair_cases :1218), a wlog q<p (:1228), and assembly of the 12 listed children ending in FTtype2_exclusion; it closes with Qed and has no admit/axiom. All 12 children are directly applied in the glue, each closes with Qed, their statements match entry.json verbatim, and every closed_by string matches the code (verified against PFsection8.v, PFsection12.v, PFsection13.v, PFsection14.v local copies). Shape numbers check out: glue_lines 37, child_lines [20,59,3,1,121,8,114,1] equal the Proof..Qed body line counts of the 8 shown children, depth 4 = chain no_minSimple_odd_group->FTtype2_exclusion->not_charUH->no_full_FT_Galois_structure->prime_dim_normed_finField (edges at L1212/L639/L487 confirmed). Minor non-blocking note: metrics how_counted and README cite typeP_pairW as applied at line 1237, but it is applied at line 1232 (1237 is mFT_norm_proper); also direct_lemmas=12 counts only the skeleton children while the glue additionally applies generic project helpers (mmax_exists, mFT_norm_proper, mFT_sol_proper). | reviewer-correctness |
| generality | accept | Move generalised beyond the example: applicability.goal_shape abstracts to 'impossibility theorem forall gT, C gT -> False' reduced to a finite exhaustive dichotomy (all-small-kind OR distinguished pair), each arm closed by a named lemma, and also_known_as names the transferable ingredients 'dichotomy on a classification lemma'/'wlog ordering'. use_when/avoid_when are specific and honest: exhaustiveness must already be a proved project lemma; arms must factor through named lemmas; and the closing lemma must not depend on a fragile positional argument list (a real risk here, where FTtype2_exclusion is applied to a long positional list). Consequences are concrete: two obligations from the \/, the wlog swap via typeP_pair_sym carrying one ordering for both, and the single exact: breaking if any intermediate fact changes shape. The entry explicitly answers 'what makes these good leaves': each child's statement is already in the shape the glue needs (the dichotomy IS the disjunction; not_all_FTtype1 IS the negation of arm (a); the one-liners close by a single rewrite/case), and the summary states the parent is a bounded-prover skeleton where every hole is 'have := <closed lemma>' with the wlog ordering as the only creative glue step. | reviewer-generality |
| provenance-licence | accept | Provenance pass: check_provenance.py confirms 4 files byte-identical at ba734c020d9f7dce5758fa822904dea29e2624ba. Commit is consistent everywhere: entry.json source.commit, source.json, SOURCE.md, and every file/site permalink use ba734c020d9f7dce5758fa822904dea29e2624ba; the verifier's ci-record cites it as HEAD of master. Licence CECILL-B is recorded consistently in entry.json, source.json, SOURCE.md, README; the copied upstream-CeCILL-B is genuinely the CeCILL-B licence (Version 1.0 dated 2006-09-05). Source note SOURCE.md matches (repo, commit, language, licence file). All 12 site line ranges resolve to the correct named lemmas in the byte-identical copies (spot-checked: no_minSimple_odd_group 1216, Feit_Thompson 1255, compl_of_typeII 387, typeP_pair_sym 436, FTtypeP_pair_cases 443, typeP_pairW 470, FTtype1_ref_irr 56, FT_Frobenius_type1 491, not_all_FTtype1 1302, FTtypeII_support_facts 1658, FTtype1_coherence 1963, FTtypeP_max_typeII 491, FTtypeP_min_typeII 733, FTtype2_exclusion 1211). Traceable end to end. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/math-comp/odd-order at commit `ba734c020d9f7dce5758fa822904dea29e2624ba`, under `CECILL-B`; see the [source note](../../sources/odd-order/SOURCE.md) for the licence text and attribution.
