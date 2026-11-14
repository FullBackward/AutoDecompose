# Jordan decomposition as a chain of similarity transitivity steps

| | |
|---|---|
| Kind | instance |
| Move | calc-chain |
| Language | rocq |
| Status | accepted |
| Source | [coqeal](../../sources/coqeal/SOURCE.md) at `8fd26cf416ce` |
| Licence | `MIT` |
| Licence recorded | 2026-11-14T15:37:33Z |

## Intent

Prove the main theorem of the file — that a square matrix `A` over a closed field is similar to its Jordan form — by chaining four similarity lemmas through `similar_trans`: `A` to its Frobenius form (`Frobenius`), that to its closed-field block form (`similar_Frobenius`), then blockwise to `Jordan_form A` (`similar_diag_block`), each companion block becoming a Jordan block per root (`similar_cj`).

## The decomposition

### parent `Jordan`: [`theory/jordan.v` lines 205-227](https://github.com/rocq-community/coqeal/blob/8fd26cf416ce0dfb5e9a9745293bdedf63b56d39/theory/jordan.v#L205-L227) ([local copy](code/theory/jordan.v))

```coq
Lemma Jordan n (A : 'M[R]_n.+1) : similar A (Jordan_form A).
Proof.
apply: (similar_trans (Frobenius _)).
apply: (similar_trans (similar_Frobenius _)).
rewrite /Frobenius_form_CF /Jordan_form /root_seq_poly /linear_factor_seq.
set s1 := flatten _.
set s2 := map _ _.
have Hs: size s1 = size s2.
  rewrite /s1 size_map.
  by do 2! rewrite map_comp -map_flatten size_map.
apply: similar_diag_block=> // i; rewrite /s1.
(do 2! rewrite map_comp -map_flatten size_map) => Hi.
rewrite (nth_map 0) ?size_map //.
rewrite !(nth_map (0,0%N)) ?size_map //.
set x := nth _ _ _.
rewrite -(@prednK x.2); last exact: similar_cj.
have/flattenP [s Hfs Hx] := mem_nth (0,0%N) Hi; move: Hfs.
case/(nthP nil)=> m; rewrite !size_map=> Hm Heq.
move: Heq Hx; rewrite (nth_map 0) // => <-.
apply: root_mu_seq_pos.
apply: (@invariant_factor_neq0 _ _ A).
by rewrite mem_nth.
Qed.
```

### child `similar_cj`: [`theory/jordan.v` lines 128-179](https://github.com/rocq-community/coqeal/blob/8fd26cf416ce0dfb5e9a9745293bdedf63b56d39/theory/jordan.v#L128-L179) ([local copy](code/theory/jordan.v))

```coq
Lemma similar_cj n (lam : R) :
  similar (companion_mx (('X - lam%:P)^+ n.+1)) (Jordan_block lam n.+1).
Proof.
set p := _^+n.+1.
have Hmp: p \is monic by rewrite monic_exp // monicXsubC.
have Hsp: (1 < size p)%N by rewrite size_exp_XsubC.
apply/similar_fundamental.
apply: (equiv_trans  (equiv_Smith _)).
apply: (equiv_trans (Smith_companion Hsp Hmp)).
set M := char_poly_mx _.
apply/equiv_sym/(equiv_trans (equiv_Smith M)).
rewrite /Smith_form -diag_mx_seq_takel.
set s := take _ _.
have Hs1: size s = n.+1.
  rewrite size_Smith_seq // -/(char_poly _) char_poly_Jordan_block.
  by rewrite -size_poly_eq0 size_exp_XsubC.
apply: eqd_equiv; rewrite ?size_exp_XsubC // ?size_rcons ?size_nseq //=.
have Hsort: sorted (@dvdr _) s.
  by apply/(sorted_take (@dvdr_trans _))/sorted_Smith.
move: (equiv_Smith M).
rewrite /Smith_form -diag_mx_seq_takel => Hequiv.
have Hlemin: (n <= minn n.+1 n.+1)%N by rewrite minnn.
move: (Smith_gcdr_spec Hlemin Hsort Hequiv).
set d := \big[_/_]_(_<_) _=> H.
have {H} Hd1: d %= 1.
  apply/(eqd_trans H)/andP; split; last by rewrite dvd1r.
  apply: big_gcdr_def; exists (finfun (lift ord_max)).
  apply: big_gcdr_def; exists (finfun (lift ord0)).
  rewrite /minor.minor /minor.submatrix /=.
  set N := \matrix_(_,_) _.
  have Hut: upper_triangular_mx N^T.
    apply/upper_triangular_mxP=> i j Hij.
    rewrite !mxE !ffunE -(inj_eq (@ord_inj _)) lift0 lift_max.
    rewrite !eqn_leq !(leqNgt _ j) ltnS (ltnW Hij) ltnNge Hij.
    by rewrite andbF addr0 subr0.
  rewrite -det_tr (det_triangular_mx Hut).
  rewrite (eq_bigr (fun _ => -1)) ?prodr_const ?card_ord.
    move=> i; rewrite !mxE !ffunE -(inj_eq (@ord_inj _)) lift0 lift_max.
    by rewrite eqxx !eqn_leq ltnn andbF sub0r add0r.
  by apply/dvdrP; exists ((-1)^+ n); rewrite -expr2 sqrr_sign.
have Hip: s`_n %= p.
  rewrite eqd_sym in Hd1.
  rewrite -(mul1r s`_n) (eqd_ltrans (eqd_mulr _ Hd1)).
  rewrite /p -char_poly_Jordan_block /char_poly -det_Smith.
  rewrite /Smith_form -diag_mx_seq_takel det_diag_mx_seq //.
  by rewrite (big_nth 0) big_mkord Hs1 big_ord_recr.
move/eqd_big_mul1: Hd1 => H i.
case: (ltngtP i n) => Hi.
- by rewrite nth_rcons size_nseq Hi nth_nseq Hi (H (Ordinal Hi)).
- by rewrite !nth_default // ?Hs1 // size_rcons size_nseq.
by rewrite nth_rcons size_nseq Hi ltnn eqxx.
Qed.
```

### child `Frobenius`: [`theory/frobenius_form.v` lines 381-400](https://github.com/rocq-community/coqeal/blob/8fd26cf416ce0dfb5e9a9745293bdedf63b56d39/theory/frobenius_form.v#L381-L400) ([local copy](code/theory/frobenius_form.v))

```coq
Lemma Frobenius n (A : 'M[F]_n.+1) :
  similar A (Frobenius_form A).
Proof.
apply/similar_fundamental; rewrite char_diag_block_mx.
  by rewrite -size_eq0 size_map size_eq0 nnil_inv_factors.
apply: (equiv_trans (equiv_Smith (char_poly_mx A))).
rewrite /Smith_form.
apply/(equiv_trans (equiv_Frobenius_seq A))/equiv_sym.
have Hn := size_Frobenius_seq A.
rewrite /equivalent -{2 4 37 38 43 44}Hn cast_inv.
apply: (equiv_trans _ (equiv_sbc_ssc A)).
apply: equiv_diag_block=>[|i]; first by rewrite !size_map.
rewrite size_map=> Hi.
rewrite !(nth_map 0) //.
set C := char_poly_mx _.
apply: (equiv_trans (equiv_Smith C)).
apply: Smith_companion; move: (mem_nth 0 Hi).
  by rewrite mem_filter=> /andP [].
exact: monic_invariant_factors.
Qed.
```

### child `similar_Frobenius`: [`theory/frobenius_form.v` lines 677-722](https://github.com/rocq-community/coqeal/blob/8fd26cf416ce0dfb5e9a9745293bdedf63b56d39/theory/frobenius_form.v#L677-L722) ([local copy](code/theory/frobenius_form.v))

```coq
Lemma similar_Frobenius n (A : 'M[R]_n.+1) :
 similar (Frobenius_form A) (Frobenius_form_CF A).
Proof.
rewrite /Frobenius_form /Frobenius_form_CF.
move: (@monic_invariant_factors _ _ A).
have: forall p, p \in (invariant_factors A) -> (1 < size p)%N.
  by move=> p; rewrite mem_filter; case/andP.
case: (invariant_factors A)=>[_ _|a l]; first exact: similar_refl.
elim: l a=> /= [a Hsa Hma |b l IHl a Hs Hm].
  rewrite !cats0; apply: similar_poly_inv.
    by rewrite Hsa // mem_head.
  by rewrite Hma // mem_head.
have IHs: forall p : {poly R}, p \in b :: l -> (1 < size p)%N.
  by move=> p Hp; apply: Hs; rewrite mem_behead.
have IHm: forall p : {poly R}, p \in b :: l -> p \is monic.
  by move=> p HP; apply: Hm; rewrite mem_behead.
have Hsa: (1 < size a)%N by rewrite Hs // mem_head.
have Hma: a \is monic by rewrite Hm // mem_head.
set M := companion_mxn _ _.
apply: (similar_trans (similar_drblockmx M (IHl b IHs IHm))).
apply: (similar_trans (similar_ulblockmx _ (similar_poly_inv Hsa Hma))).
have Hnv: forall p, p \in [:: a, b & l] -> linear_factor_seq p != [::].
  move=> p Hp; rewrite /linear_factor_seq -size_eq0 !size_map size_eq0.
  rewrite /root_seq_uniq; apply: contra_neq; first exact: undup_nil.
  by rewrite -root_seq_nil -ltnNge; apply: Hs.
set s1 := _ ++ _.
set s2 := linear_factor_seq _ ++ _.
have: (linear_factor_seq a) != [::] by rewrite Hnv // mem_head.
have t: s2 != [::].
  have: linear_factor_seq b != [::] by rewrite Hnv // mem_behead // mem_head.
  by rewrite /s2; case: (linear_factor_seq b).
clear -t.
have ->: s1 = [seq (size p).-2 | p : {poly R} <- s2].
  by rewrite /s1 map_cat map_flatten; congr (_ ++ _); rewrite [in LHS]map_comp.
case: (linear_factor_seq a)=> //= c s _.
elim: s c=> [c|c s IHs d] /=.
  case: s2 t => // d s2 _ /=.
  exact: similar_refl.
set M := companion_mxn _ _.
apply: similar_sym.
apply: (similar_trans (similar_drblockmx M (similar_sym (IHs c)))).
rewrite /GRing.zero /= -row_mx_const -col_mx_const block_mxA.
apply/similar_sym/similar_cast.
rewrite col_mx_const row_mx_const.
exact: similar_refl.
Qed.
```

### child `similar_diag_block`: [`theory/similar.v` lines 296-311](https://github.com/rocq-community/coqeal/blob/8fd26cf416ce0dfb5e9a9745293bdedf63b56d39/theory/similar.v#L296-L311) ([local copy](code/theory/similar.v))

```coq
Lemma similar_diag_block : forall l1 l2, size l1 = size l2 ->
   forall (F1 F2 : forall n : nat, nat -> 'M[R]_n.+1),
   (forall i, i < size l1 ->
    similar (F1 (nth 0%N l1 i) i) (F2 (nth 0%N l2 i) i)) ->
   similar (diag_block_mx l1 F1) (diag_block_mx l2 F2).
Proof.
case=>[|a l1]; case=> //=.
  by move=> *; apply: similar_refl.
move=> b l2 /eqP; rewrite eqSS=> /eqP Hsl F1 F2 Hl.
have Hab: similar (F1 a 0%N) (F2 b 0%N) by exact: (Hl 0%N).
move: l1 l2 Hsl a b F1 F2 Hab Hl.
apply: seq2_ind=> //= x1 x2 l1 l2 IH a b F1 F2 Hab H.
apply: (similar_dgblockmx Hab).
apply: IH=>[|i]; first exact: (H 1%N).
exact: (H i.+1).
Qed.
```

### How the parts fit

The proof of `Jordan` is a single transitivity chain, one child per link. The lemma graph (arrow = "is applied by"):

```
Jordan (parent, jordan.v 205-227)
├─ Frobenius            (frobenius_form.v 381-400)   — applied at line 207
├─ similar_Frobenius    (frobenius_form.v 677-722)   — applied at line 208
├─ similar_diag_block   (similar.v 296-311)          — applied at line 215
└─ similar_cj           (jordan.v 128-179)           — applied at line 220
```

Reading the glue: line 207 applies `similar_trans (Frobenius _)` to reduce `similar A (Jordan_form A)` to `similar (Frobenius_form A) (Jordan_form A)`. Line 208 applies `similar_trans (similar_Frobenius _)` to step through the closed-field form `Frobenius_form_CF A`. Lines 209-214 unfold `Frobenius_form_CF`/`Jordan_form` and build two block-size lists `s1`/`s2`, proving `size s1 = size s2`. Line 215 applies `similar_diag_block` to reduce the goal to a per-block similarity of the `diag_block_mx`. Lines 216-226 discharge each block: `nth` rewrites turn the two sides at index `i` into `companion_mx (('X - lam%:P)^+ n.+1)` and `Jordan_block lam n.+1`, and line 220 applies `similar_cj` to close that per-block similarity.

Each child is a good leaf because its statement is self-contained and its proof closes from named siblings or imports, never from the parent:

- **`Frobenius`** (20 lines) — `similar A (Frobenius_form A)` over a `fieldType`. Closes by `similar_fundamental` then a chain of char-poly equivalences (`equiv_Smith`, `equiv_Frobenius_seq`, `equiv_sbc_ssc`, `equiv_diag_block`, `Smith_companion`), ending in `exact: monic_invariant_factors`.
- **`similar_Frobenius`** (46 lines) — `similar (Frobenius_form A) (Frobenius_form_CF A)` over a `closedFieldType`. Closes by induction on the `invariant_factors A` list, re-factoring each block with `similar_poly_inv`, `similar_drblockmx`, `similar_ulblockmx`, `similar_cast`; the base cases end in `exact: similar_refl`.
- **`similar_diag_block`** (16 lines) — the generic blockwise lemma that lifts a per-block `similar` to `similar (diag_block_mx l1 F1) (diag_block_mx l2 F2)`. Closes by `seq2_ind`, joining head blocks with `similar_dgblockmx` and tails by the induction hypothesis; the empty case is `similar_refl`.
- **`similar_cj`** (52 lines) — the per-root step `similar (companion_mx (('X - lam%:P)^+ n.+1)) (Jordan_block lam n.+1)`. Closes by `similar_fundamental` and Smith-normal-form equivalences (`equiv_Smith`, `Smith_companion`, `Smith_gcdr_spec`), using `char_poly_Jordan_block` to identify the char poly; the gcd computation ends in `apply/dvdrP; exists ((-1)^+ n); rewrite -expr2 sqrr_sign`.

Two of the children (`Frobenius`, `similar_Frobenius`) live in `frobenius_form.v`, one (`similar_diag_block`) in `similar.v`, and one (`similar_cj`) in the parent's own file; all four are copied whole here.

## Why it is good

1. **No sorry in the glue** (`check`). No closing-by-sorry token (`admit`, `Admitted`, `Axiom`, `axiom`) occurs in the parent site `theory/jordan.v:205-227`; the proof closes with `Qed`. *(Evidence: [theory/jordan.v#L205-L227](https://github.com/rocq-community/coqeal/blob/8fd26cf416ce0dfb5e9a9745293bdedf63b56d39/theory/jordan.v#L205-L227).)*
2. **The glue cites the per-block child** (`check`). The parent site cites `similar_cj` (applied at line 220). *(Evidence: [theory/jordan.v#L220](https://github.com/rocq-community/coqeal/blob/8fd26cf416ce0dfb5e9a9745293bdedf63b56d39/theory/jordan.v#L220).)*
3. **Shape** (`measurement`). The glue `Jordan` is 23 lines and applies 4 direct lemmas; the four child sites span 52, 20, 46 and 16 lines; the longest chain of project lemmas below the parent is 3 (`Jordan` → `similar_cj` → `char_poly_Jordan_block` → `upt_Jordan_block`). *(Evidence: jordan.v 205-227, 128-179, 110-116, 42-46; frobenius_form.v 381-400, 677-722; similar.v 296-311.)*
4. **The authors name it the file's main result** (`author-statement`). The file header says "The main result of this file is the theorem of Jordan decomposition." *(Evidence: [theory/jordan.v#L10-L11](https://github.com/rocq-community/coqeal/blob/8fd26cf416ce0dfb5e9a9745293bdedf63b56d39/theory/jordan.v#L10-L11).)*
5. **Reused, not re-proved** (`known-use`). `Jordan` is consumed by `Jordan_char_poly` (line 232) and `diagonalization` (lines 267, 290) in the same file. *(Evidence: [theory/jordan.v#L232](https://github.com/rocq-community/coqeal/blob/8fd26cf416ce0dfb5e9a9745293bdedf63b56d39/theory/jordan.v#L232), [L267](https://github.com/rocq-community/coqeal/blob/8fd26cf416ce0dfb5e9a9745293bdedf63b56d39/theory/jordan.v#L267), [L290](https://github.com/rocq-community/coqeal/blob/8fd26cf416ce0dfb5e9a9745293bdedf63b56d39/theory/jordan.v#L290).)*

## When to use it, and when not

Use a `similar_trans` chain when an end-to-end normalisation-to-canonical-form splits into stages that each already have a named similarity lemma: here, over the base field (`Frobenius`), then over the algebraic closure (`similar_Frobenius`), then blockwise (`similar_diag_block` + `similar_cj`). It is the right shape when the intermediate forms are few and fixed, and when a generic blockwise lemma already exists so the glue only has to name the stages.

Do not use it when a stage lacks a standalone lemma (the chain forces one lemma per stage before the glue can be written), when the intermediate forms differ in dimension or base field so `similar_trans` cannot bridge them, or when the per-block step needs a different argument per block rather than one uniform lemma.

## Consequences

Turns one large similarity-to-canonical-form goal into one transitivity chain of four named lemmas, so each hole is one stage of the normalisation — the natural unit for a bounded prover. Obligations: each child must be a full `similar` statement with matching dimensions; the glue's application order must match the chain of intermediate forms; the intermediate forms (`Frobenius_form A`, `Frobenius_form_CF A`) must be spelled out so consecutive `similar_trans` instances typecheck; the blockwise step needs the block-size lists to have equal size (proved in the glue at lines 212-214). Failure mode: the glue does no real work itself, so a missing or misshaped stage lemma surfaces as a type error at the `similar_trans` application rather than as a subgoal to prove.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/nix-action-rocq-9.3.yml (push to master; job coqeal builds the project); _CoqProject lists theory/jordan.v; commit 8fd26cf416ce0dfb5e9a9745293bdedf63b56d39 is the master head | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: Frobenius@theory/jordan.v:207, similar_Frobenius@theory/jordan.v:208, similar_diag_block@theory/jordan.v:215, similar_cj@theory/jordan.v:220; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 3 file(s) byte-identical at 8fd26cf416ce0dfb5e9a9745293bdedf63b56d39 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | no_sorry(theory/jordan.v, 205-227) -> no_sorry: none of admit, Admitted, Axiom, axiom in theory/jordan.v:205-227 | check_claims.py |
| 2 | verified | cites(parent, similar_cj) -> cites: similar_cj occurs at theory/jordan.v:220 | check_claims.py |
| 3 | verified | glue Jordan 205-227 = 23 lines (read code/jordan.v 205-227); 4 direct lemmas applied: Frobenius@207, similar_Frobenius@208, similar_diag_block@215, similar_cj@220; child line counts: similar_cj 128-179=52, Frobenius 381-400=20, similar_Frobenius 677-722=46, similar_diag_block 296-311=16; chain Jordan(205)->similar_cj(128)->char_poly_Jordan_block(110)->upt_Jordan_block(42) each link confirmed: line220 'exact: similar_cj', line142/171 char_poly_Jordan_block, line113 'apply: upt_Jordan_block' | verifier |
| 4 | verified | code/theory/jordan.v:10 reads 'The main result of this file is the theorem of Jordan decomposition.' (lines 10-11 header comment) | verifier |
| 5 | verified | Jordan applied at line 232 'rewrite (similar_char_poly (Jordan A))', line 267 'have [Heq _]:= Jordan A', line 290 'apply: (similar_trans (Jordan A))' in code/theory/jordan.v | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent Jordan (jordan.v 205-227) is a right-nested similar_trans chain citing exactly the four named children: Frobenius@207, similar_Frobenius@208, similar_diag_block@215, similar_cj@220; each child statement in entry.json matches its code verbatim and each closes with Qed (no sorry/admit/Admitted/axiom in any site; sorry-scan pass). Closing methods match the code: Frobenius ends in monic_invariant_factors (399); similar_Frobenius in similar_refl at 684/714/721; similar_diag_block in similar_refl at 303; similar_cj uses char_poly_Jordan_block@142 and dvdrP/-expr2 sqrr_sign@167. Shape numbers are right: glue_lines 23 (205-227), child_lines [52,20,46,16] = similar_cj, Frobenius, similar_Frobenius, similar_diag_block matching the sites order, direct_lemmas 4, and depth 3 matches the real chain Jordan->similar_cj->char_poly_Jordan_block->upt_Jordan_block (verified at 220/142/113). Claims 3-5 also verified against code (header 10, reuse at 232/267/290). | reviewer-correctness |
| generality | accept | Generality passes. Move is stated beyond the Jordan example: applicability/use_when abstracts to 'end-to-end normalisation-to-canonical-form that splits into stages each with a named similarity lemma', with transferable conditions (few fixed intermediate forms, generic blockwise lemma so glue only names stages). 'When not to use' is honest and specific: (1) stage lacks a standalone lemma -> chain forces one lemma per stage first; (2) intermediate forms differing in dimension/base field -> similar_trans cannot bridge (true: the transitivity lemma needs a consistent middle type); (3) per-block step needing a different argument per block -> breaks the uniform forall-shape of similar_diag_block. Consequences are honest and specific, including a genuine failure mode: the glue does no new mathematical work, so a missing/misshaped stage lemma surfaces as a type error at the similar_trans application, not a subgoal. It says what makes leaves good for a bounded prover: each child's statement is self-contained and its proof closes from named siblings/imports, never from the parent (verified in the copied excerpts: Frobenius -> monic_invariant_factors, similar_Frobenius -> similar_refl, similar_diag_block -> similar_dgblockmx/similar_refl, similar_cj -> dvdrP), so each hole = one normalisation stage. | reviewer-generality |
| provenance-licence | accept | Commit 8fd26cf416ce0dfb5e9a9745293bdedf63b56d39 is consistent across entry.json, sources/coqeal/source.json, SOURCE.md and every permalink; check_provenance.py reports 3 files byte-identical at that commit. Licence MIT is consistent across entry.json, source.json, SOURCE.md and upstream-LICENSE (MIT text). All permalink line anchors match the cited ranges (jordan.v 205-227, 128-179, 10-11, 220, 232, 267, 290; frobenius_form.v 381-400, 677-722; similar.v 296-311). README source/licence section agrees. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/rocq-community/coqeal at commit `8fd26cf416ce0dfb5e9a9745293bdedf63b56d39`, under `MIT`; see the [source note](../../sources/coqeal/SOURCE.md) for the licence text and attribution.
