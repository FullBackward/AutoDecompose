# calc-chain: X^5 - 4X + 2 is not solvable by radicals

| | |
|---|---|
| Kind | instance |
| Move | calc-chain |
| Language | rocq |
| Status | accepted |
| Source | [abel](../../sources/abel/SOURCE.md) at `8c6194115397` |
| Licence | `CECILL-B` |
| Licence recorded | 2026-11-14T15:26:19Z |

## Intent

A three-line `rewrite` chain refutes solvability of `X^5 - 4X + 2` over the
rationals by radicals. Each link of the chain is one named lemma: `AbelGaloisPolyRat`
turns radical solvability into solvability of the Galois group, `isog_gal` (with
`size_poly_example` supplying the degree) identifies that group with the symmetric
group on five letters, and `solvable_SymF` refutes its solvability; `count_roots_ex`
discharges the two-non-real-roots hypothesis the isomorphism needs.

## The decomposition

### parent `example_not_solvable_by_radicals`: [`theories/abel.v` lines 1337-1343](https://github.com/math-comp/abel/blob/8c6194115397371df63cd6fae7e39009872858fd/theories/abel.v#L1337-L1343) ([local copy](code/theories/abel.v))

```coq
Lemma example_not_solvable_by_radicals :
  ~ solvable_by_radical_poly ('X^5 - 4 *: 'X + 2 : {poly rat}).
Proof.
move=> /AbelGaloisPolyRat; pose sol_gal := isog_sol (PDTNRR.isog_gal _ _ _).
rewrite sol_gal ?size_poly_example ?solvable_SymF ?card_ord//.
by rewrite -(count_map _ [predC Creal]) count_roots_ex.
Qed.
```

### child `AbelGaloisPolyRat`: [`theories/abel.v` lines 854-868](https://github.com/math-comp/abel/blob/8c6194115397371df63cd6fae7e39009872858fd/theories/abel.v#L854-L868) ([local copy](code/theories/abel.v))

```coq
Theorem AbelGaloisPolyRat (p : {poly rat}) :
  reflect (solvable_by_radical_poly p) (solvable 'Gal({: numfield p} / 1)).
Proof.
have [{p}->|p_neq0] := eqVneq p 0.
  rewrite numfield0 regular_fullv galvv solvable1; constructor.
  move=> L rs; rewrite eqp_sym rmorph0 eqp0 prodf_seq_eq0.
  by move=> /hasP[x _ /=]; rewrite polyXsubC_eq0.
have charrat : [pchar rat] =i pred0 by exact: pchar_num.
pose charnumfield := char_ext (numfield p).
apply: (equivP idP); rewrite -AbelGaloisPoly//.
have [rs prs <-] := numfieldP p_neq0.
split; last by move=> /(_ (numfield p) rs prs).
move=> solp; apply/solvable_ext_polyP => //.
by apply/classicW; exists (numfield p); exists rs; split.
Qed.
```

### child `isog_gal`: [`theories/abel.v` lines 1168-1169](https://github.com/math-comp/abel/blob/8c6194115397371df63cd6fae7e39009872858fd/theories/abel.v#L1168-L1169) ([local copy](code/theories/abel.v))

```coq
Lemma isog_gal : 'Gal ({:numfield p} / 1%AS) \isog 'Sym_('I_d).
Proof. by rewrite -adjoin_numfield_roots isog_gal_perm. Qed.
```

### child `size_poly_example`: [`theories/abel.v` lines 1198-1202](https://github.com/math-comp/abel/blob/8c6194115397371df63cd6fae7e39009872858fd/theories/abel.v#L1198-L1202) ([local copy](code/theories/abel.v))

```coq
Lemma size_poly_example : size poly_example = 6%N.
Proof.
rewrite /poly_example -addrA size_polyDl ?size_polyXn//.
by rewrite size_polyDl ?size_polyN ?size_scale ?size_polyX -?polyCn ?size_polyC.
Qed.
```

### child `solvable_SymF`: [`theories/xmathcomp/various.v` lines 730-731](https://github.com/math-comp/abel/blob/8c6194115397371df63cd6fae7e39009872858fd/theories/xmathcomp/various.v#L730-L731) ([local copy](code/theories/xmathcomp/various.v))

```coq
Lemma solvable_SymF : 4 < #|T| -> solvable 'Sym_T = false.
Proof. by rewrite (series_sol (Alt_normal T)) => /solvable_AltF->. Qed.
```

### child `count_roots_ex`: [`theories/abel.v` lines 1297-1335](https://github.com/math-comp/abel/blob/8c6194115397371df63cd6fae7e39009872858fd/theories/abel.v#L1297-L1335) ([local copy](code/theories/abel.v))

```coq
Lemma count_roots_ex : count [predC Creal] example_roots = 2%N.
Proof.
rewrite -!sum1_count; pose pR : {poly algR} := poly_example ^^ ratr.
have pR0 : pR != 0 by rewrite map_poly_eq0.
suff cR : (\sum_(j <- example_roots | j \is Num.real) 1)%N = 3%N.
  have := size_example_roots; rewrite -sum1_size (bigID (mem Num.real))/=.
  by rewrite cR => -[].
rewrite -big_filter (perm_big (map algRval (rootsR pR))); last first.
  rewrite uniq_perm ?filter_uniq ?example_roots_uniq//.
    by rewrite (map_inj_uniq (fmorph_inj _)) uniq_roots.
  move=> x; rewrite mem_filter -root_prod_XsubC -ratr_example_poly.
  rewrite -(eq_map_poly (fmorph_eq_rat (algRval \o ratr)))/=.
  rewrite map_poly_comp/=.
  apply/andP/mapP => [[xR xroot]|[y + ->]].
    exists (in_algR xR); rewrite // mem_rootsR// -topredE/=.
    by rewrite -(mapf_root algRval)/=.
  rewrite mem_rootsR// -[y \in _]topredE/=.
  by split; [apply/algRvalP|rewrite mapf_root].
apply/eqP; rewrite sum1_size size_map eqn_leq.
rewrite (leq_trans (size_root_leSderiv _))//=; last first.
  by rewrite deriv_map rootsR_deriv_poly_example.
have pRE x : Num.sg pR.[x%:~R] = locked ratr (Num.sg poly_example.[x%:~R]).
  by rewrite -lock ratr_sg -horner_map/= ratr_int.
have pN2 : Num.sg pR.[(- 2%:Z)%:~R] = - 1 by rewrite pRE !pesimp -lock rmorphN1.
have pN1 : Num.sg pR.[(- 1%:Z)%:~R] =   1 by rewrite pRE !pesimp -lock rmorph1.
have p1  : Num.sg pR.[1%:~R]        = - 1 by rewrite pRE !pesimp -lock rmorphN1.
have p2  : Num.sg pR.[2%:~R]        =   1 by rewrite pRE !pesimp -lock rmorph1.
have simp := (pN2, pN1, p1, p2, mulN1r, mulrN1).
have [||x0 /andP[_ x0N1] rx0] := @ivt_sign _ pR (- 2%:R) (- 1); rewrite ?simp//.
  by rewrite -subr_ge0 opprK addKr ler01.
have [||x1 /andP[x10 x11] rx1] := @ivt_sign _ pR (-1) 1; rewrite ?simp//.
  by rewrite -subr_ge0 opprK addr_ge0 ?ler01.
have [||x2 /andP[/= x21 _] rx2] := @ivt_sign _ pR 1 2%:R; rewrite ?simp//.
  by rewrite -subr_ge0 addrK ler01.
have: sorted <%R [:: x0; x1; x2] by rewrite /= (lt_trans x0N1) ?(lt_trans x11).
rewrite lt_sorted_uniq_le => /andP[uniqx012 _].
apply: (@uniq_leq_size _ [:: x0; x1; x2]) => //.
by move=> x; rewrite !inE => /or3P[]/eqP->/=; rewrite mem_rootsR.
Qed.
```

How the parts fit. The parent is a negative goal, so `move=> /AbelGaloisPolyRat`
introduces the hypothesis `solvable_by_radical_poly p` and applies the `reflect`
view to it, leaving `solvable 'Gal({:numfield p} / 1)` in context. `pose sol_gal :=
isog_sol (PDTNRR.isog_gal _ _ _)` states `sol_gal : solvable 'Gal(...) = solvable
'Sym_('I_d)` via the library lemma `isog_sol` over the isomorphism `isog_gal`; the
three `_` are the three hypotheses of the module `PrimeDegreeTwoNonRealRoots`
(irreducibility, prime degree, exactly two non-real roots). The `rewrite` line then
applies `sol_gal`, `size_poly_example` (so `d = 5`), `solvable_SymF` (so
`solvable 'Sym_('I_5) = false`) and `card_ord` (so `#|'I_5| = 5`), turning the
context into `false`; the trailing `//` closes the irreducibility and prime-degree
obligations through the local hints `irreducible_example` and `prime_example`. The
last line discharges the remaining two-non-real-roots obligation: `count_roots_ex`
gives `count [predC Creal] example_roots = 2%N`, and `count_map` transports it to
the `count_rp'` form `isog_gal` expects.

Lemma graph (who uses whom, in text):

```
example_not_solvable_by_radicals
├── AbelGaloisPolyRat
├── isog_gal ─ isog_gal_perm ─┬─ injm_gal_perm
│                              └─ surj_gal_perm ─┬─ gen_tperm_cycle
│                                                ├─ gal_perm_cycle_order
│                                                └─ galJ_tperm ─┬─ gal_permP
│                                                                ├─ conj_nth_rp
│                                                                └─ rpK
├── size_poly_example
├── solvable_SymF ─ solvable_AltF
└── count_roots_ex ─┬─ size_example_roots
                    ├─ rootsR_deriv_poly_example
                    ├─ ratr_example_poly
                    ├─ ivt_sign
                    └─ size_root_leSderiv
```

Why each child is a good leaf — a self-contained statement whose proof closes on its
own or from named siblings:

- `AbelGaloisPolyRat` (lines 854-868) is a `reflect` whose two directions close from
  the file's main theorem `AbelGaloisPoly` and `solvable_ext_polyP`; its statement
  names exactly the conversion the parent needs, so the parent never unfolds it.
- `isog_gal` (lines 1168-1169) is a two-line leaf that reduces to the sibling
  `isog_gal_perm`; the whole Galois/splitting-field construction is hidden behind the
  `PrimeDegreeTwoNonRealRoots` module, so the parent cites only the packaged result.
- `size_poly_example` (lines 1198-1202) is a pure size computation closed by
  rewriting, serving as the degree witness `(size p).-1 = 5`.
- `solvable_SymF` (various.v lines 730-731) is a general group fact independent of
  the example polynomial, closed by the sibling `solvable_AltF` via `series_sol`.
- `count_roots_ex` (lines 1297-1335) is the one analytic leaf, closed by an
  intermediate-value sign analysis (`ivt_sign`) plus a derivative bound
  (`size_root_leSderiv` with `rootsR_deriv_poly_example`); it is the root-count
  witness.

The three library lemmas `isog_sol`, `card_ord` and `count_map` are mathcomp
infrastructure, not project lemmas, and are listed here for completeness rather than
as children.

## Why it is good

1. The parent `example_not_solvable_by_radicals` is declared at
   [`theories/abel.v` lines 1337-1343](https://github.com/math-comp/abel/blob/8c6194115397371df63cd6fae7e39009872858fd/theories/abel.v#L1337-L1343)
   (`check`, `declared`).
2. The parent site (lines 1337-1343) contains no `admit`, `Admitted`, `Axiom` or
   `axiom` closing token, so the chain is a proof, not a stub (`check`, `no_sorry`).
3. The parent's proof cites `count_roots_ex` at
   [line 1342](https://github.com/math-comp/abel/blob/8c6194115397371df63cd6fae7e39009872858fd/theories/abel.v#L1342)
   (`check`, `cites`).
4. The parent site is 7 lines and its 3-line proof body (lines 1340-1342) cites the 5
   direct project lemmas; the longest checked chain of project lemmas below it is 5
   deep (`example_not_solvable_by_radicals` → `isog_gal` → `isog_gal_perm` →
   `surj_gal_perm` → `galJ_tperm` → `gal_permP`), so the glue is a shallow skeleton
   whose depth sits in the lemmas, not in the main proof (`measurement`).
5. The authors comment on the analytic leaf's method: "Using the package
   real_closed, we should be able to monitor the sign of the derivative, and find
   that the polynomial has exactly three real roots"
   ([lines 1238-1239](https://github.com/math-comp/abel/blob/8c6194115397371df63cd6fae7e39009872858fd/theories/abel.v#L1238-L1239))
   (`author-statement`).

In my opinion the detail worth copying is the division of labour: the main proof
carries only the shape of the argument (three tactic lines), while every non-trivial
mathematical fact — the Galois correspondence, the isomorphism to Sym_5, the
non-solvability of Sym_5, the real-root count — is a named lemma that closes on its
own. This is exactly the "skeleton with one hole per bounded prover" shape a
theorem-scale decomposition should produce.

## When to use it, and when not

Use it when the goal is `~ P` for a predicate `P` (here
`solvable_by_radical_poly`) that a `reflect`/iff lemma converts into a decidable
group-theoretic predicate (here `solvable 'Gal(...)`), and when the group is
concretely isomorphic to a known non-solvable group (here `Sym_5`) whose
non-solvability is already a library lemma, with the degree and root-count facts
already stated as small lemmas. Avoid it when the isomorphism is not packaged (a raw
splitting-field or Galois argument would swamp the chain), when the root count needs
real analysis you have not already proved, or when the target group's non-solvability
is not a lemma you can cite.

## Consequences

The chain creates side obligations: the three hypotheses of the `isog_gal` module
(irreducibility, prime degree, exactly two non-real roots) must each be discharged,
which the parent does through the local hints `irreducible_example` and
`prime_example` and through `count_roots_ex`. Failure modes: a `rewrite ?lemma //`
chain silently leaves a side condition open if a `?`-rewrite does not fire; and the
degree (`size_poly_example`) must match the group cardinality (`card_ord`) exactly,
or `solvable_SymF` will not apply.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/docker-action.yml builds coq-mathcomp-abel.opam (whole project via _CoqProject, whose first file is theories/abel.v); .github/workflows/nix-action-rocq-9.1.yml job mathcomp-abel also builds it; commit 8c6194115397371df63cd6fae7e39009872858fd is the tip of the default branch master | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: AbelGaloisPolyRat@theories/abel.v:1340, isog_gal@theories/abel.v:1340, size_poly_example@theories/abel.v:1341, solvable_SymF@theories/abel.v:1341, count_roots_ex@theories/abel.v:1342; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at 8c6194115397371df63cd6fae7e39009872858fd | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(example_not_solvable_by_radicals, theories/abel.v, 1337-1343) -> declared: example_not_solvable_by_radicals is declared at theories/abel.v:1337 | check_claims.py |
| 2 | verified | no_sorry(theories/abel.v, 1337-1343) -> no_sorry: none of admit, Admitted, Axiom, axiom in theories/abel.v:1337-1343 | check_claims.py |
| 3 | verified | cites(parent, count_roots_ex) -> cites: count_roots_ex occurs at theories/abel.v:1342 | check_claims.py |
| 4 | verified | parent lines 1337-1343 are 7 lines; proof body 1340-1342 is 3 lines citing the 5 child lemmas (AbelGaloisPolyRat, isog_gal, size_poly_example, solvable_SymF, count_roots_ex); chain confirmed: isog_gal@1168-1169 -> isog_gal_perm@1162-1166 -> surj_gal_perm@1153-1160 -> galJ_tperm@1145-1151 -> gal_permP@1020, each link cited in the preceding lemma's proof | verifier |
| 5 | verified | abel.v lines 1238-1239 are the comment 'Using the package real_closed, we should be able to monitor the sign of the derivative, and find that the polynomial has exactly three real roots.' | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent example_not_solvable_by_radicals (abel.v:1337-1343) proof body cites exactly the 5 children: /AbelGaloisPolyRat and PDTNRR.isog_gal (1340), size_poly_example and solvable_SymF (1341), count_roots_ex (1342); PDTNRR := PrimeDegreeTwoNonRealRoots (line 1173) so PDTNRR.isog_gal is the child isog_gal at 1168-1169. All 5 child statements and closed_by are verbatim in code (AbelGaloisPolyRat 854-868 uses -AbelGaloisPoly/solvable_ext_polyP/witness numfield p; isog_gal = rewrite -adjoin_numfield_roots isog_gal_perm; size_poly_example 1198-1202; solvable_SymF 730-731 = series_sol Alt_normal + solvable_AltF; count_roots_ex 1297-1335 = suff cR + ivt_sign + size_root_leSderiv/rootsR_deriv_poly_example). Sites all end Qed with no sorry token; module has exactly 3 hypotheses (p_irr, d_prime, count_rp') matching the three _ in PDTNRR.isog_gal _ _ _, discharged by // (irreducible_example/prime_example) and count_roots_ex via count_map. Shape numbers right: direct_lemmas=5, depth=5 (example->isog_gal->isog_gal_perm->surj_gal_perm->galJ_tperm->gal_permP, each link cited verbatim), glue_lines=7 (1337-1343), child_lines=[15,2,5,2,39] matching 854-868/1168-1169/1198-1202/730-731/1297-1335. | reviewer-correctness |
| generality | accept | Move generalizes beyond the example: use_when is abstracted to ~P where a reflect/iff lemma converts P into a decidable group predicate refuted by an isomorphism to a known non-solvable group, with degree/cardinality and root-count facts as small lemmas; avoid_when is specific and honest (unpackaged isomorphism, unproved real analysis, uncited non-solvability lemma), and the example itself uses ivt_sign/size_root_leSderiv so the 'already proved' caveat is truthful. Consequences name the three isog_gal side obligations and two real failure modes (silent ?-rewrite via '?size_poly_example ?solvable_SymF ?card_ord//', degree/cardinality mismatch), both visible in the copied parent. 'Why each child is a good leaf' explicitly answers what makes each lemma a self-contained leaf closing on its own or from named siblings, matching the skeleton/one-hole-per-bounded-prover shape. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are consistent and traceable. Commit 8c6194115397371df63cd6fae7e39009872858fd is identical across entry.json source.commit, sources/abel/source.json, sources/abel/SOURCE.md, and every permalink (README's '8c6194115397' is just its 12-char prefix); check_provenance reports the 2 copied files (theories/abel.v, theories/xmathcomp/various.v) byte-identical at that commit. Licence CECILL-B is recorded consistently (entry.json, source.json, SOURCE.md, README) and the copied licence file upstream-CeCILL-B is the genuine CeCILL-B text. All six cited line ranges (parent 1337-1343; children 854-868, 1168-1169, 1198-1202, 730-731, 1297-1335) reproduce the code quoted in README/entry.json, so every permalink resolves to what it claims. Source note (SOURCE.md) matches the copied files and cites the upstream licence file. Everything traceable; no objection. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/math-comp/abel at commit `8c6194115397371df63cd6fae7e39009872858fd`, under `CECILL-B`; see the [source note](../../sources/abel/SOURCE.md) for the licence text and attribution.
