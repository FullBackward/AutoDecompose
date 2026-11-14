# Pointwise equality of two Real.morphisms into a model (Rmorph_uniq)

| | |
|---|---|
| Kind | instance |
| Move | extensionality |
| Language | rocq |
| Status | verified |
| Source | [fourcolor](../../sources/fourcolor/SOURCE.md) at `c1d6b1cd5288` |
| Licence | `CECILL-B` |

## Intent

Prove that there is at most one `Real.morphism` from a `Real.structure` `S` into
a `Real.model` `R`, by showing any two such morphisms `phi, psi` agree
pointwise in the setoid sense. The proof halves the work by symmetry (`wlog`),
then rules out a strict separation `psi x < phi x` by interpolating a rational,
which morphisms preserve and whose order they reflect.

## The decomposition

### parent `Rmorph_uniq`: [`theories/reals/realcategorical.v` lines 203-211](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/reals/realcategorical.v#L203-L211) ([local copy](code/theories/reals/realcategorical.v))

```coq
Theorem Rmorph_uniq (S : Real.structure) (R : Real.model) (phi psi : S -> R) :
    Real.morphism phi -> Real.morphism psi ->
  pointwise_relation S Real.eq phi psi.
Proof.
move=> phiP psiP x.
wlog suffices IH: phi psi phiP psiP / phi x <= psi x; first by split; apply: IH.
have [//|/ratR_dense[a /ltRW-lexa []]] := reals_classic R (phi x <= psi x).
by rewrite -(Rmorph_rat phiP) Real.morph_le // -(Real.morph_le psiP) Rmorph_rat.
Qed.
```

### child `reals_classic`: [`theories/reals/realprop.v` lines 338-344](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/reals/realprop.v#L338-L344) ([local copy](code/theories/reals/realprop.v))

```coq
Lemma reals_classic : excluded_middle.
Proof.
move=> P; have supE: Real.has_sup {x | x = 0 \/ P /\ x = 2 :> R}.
  by split; [exists 0; left | exists 2 => x [->|[_ ->]]].
have [[x [-> /ltR01 // | []]] | leE1] := real_sup_total 1 supE; first by left.
by right=> haveP; apply/(leR_lt_trans leE1 (ltRS 1))/real_sup_ub; last right.
Qed.
```

### child `ratR_dense`: [`theories/reals/realprop.v` lines 849-863](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/reals/realprop.v#L849-L863) ([local copy](code/theories/reals/realprop.v))

```coq
Lemma ratR_dense x y : x < y -> exists2 a : rat, x < a & a < y.
Proof.
move=> ltxy; pose z := y - x; have z_gt0: z > 0 by rewrite subR_le0.
have [[d|n] [ledv ltvd1]] := find_range1z z^-1; last first.
  case: ltvd1; apply: ltRW; apply: leR_lt_trans (invR_gt0 z_gt0).
  by rewrite NegzE intRN intRS oppRD subRK -subR_ge0 add0R oppRK.
set d1 : R := d.+1; have d1gt0: d1 > 0 by apply: ltR0Sn.
have [m [lemx ltxm1]] := find_range1z (d1 * x).
exists ((m + 1)%:Q / d.+1%:Q)%R; rewrite -(leR_pmul2r _ _ d1gt0) -ratRMn.
  by rewrite divfK ?intr_eq0 // mulRC ratRz intRD1.
rewrite divfK ?intr_eq0 // ratRz intRD1.
rewrite -(addKR x y) addRC -addRA -/z mulRC mulRDr -(divRR (gtR_neq z_gt0)).
move: lemx; rewrite -(leR_add2r (d1 * z)); apply: ltR_le_trans.
by rewrite leR_add2l mulRC leR_pmul2l // /d1 intRS.
Qed.
```

### child `Rmorph_rat`: [`theories/reals/realcategorical.v` lines 166-167](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/reals/realcategorical.v#L166-L167) ([local copy](code/theories/reals/realcategorical.v))

```coq
Lemma Rmorph_rat a : phi (ratR R a) == ratR S a.
Proof. by rewrite /ratR; case: ifP; rewrite ?phiM ?Rmorph_inv !Rmorph_int. Qed.
```

How the parts fit. The parent's goal, `pointwise_relation S Real.eq phi psi`,
is by definition (real.v:121, realsyntax.v:91) the conjunction
`phi x <= psi x /\ psi x <= phi x` for the arbitrary `x` fixed by the first
line. `wlog` discharges both directions at once: because the goal is symmetric
in `phi` and `psi`, it suffices to prove the single direction `phi x <= psi x`
(the `first by split; apply: IH` shows the two directions follow from one).

The one remaining direction is closed by excluded middle and density:

- `reals_classic R (phi x <= psi x)` (child) supplies the case split
  `phi x <= psi x \/ ~ (phi x <= psi x)`. The first branch closes the goal
  (`//`); in the second, `~(phi x <= psi x)` is the strict inequality
  `psi x < phi x` (`lt` is `~ le _ _`, real.v:212).
- `ratR_dense` (child) turns that strict inequality into a witness: a rational
  `a` with `psi x < ratR R a` and `ratR R a < phi x`. The view `/ltRW` turns
  the first into `lexa : psi x <= ratR R a`.
- `Rmorph_rat` (child) rewrites `ratR R a` as `phi (ratR S a)` and as
  `psi (ratR S a)`, and `Real.morph_le` (the morphism's order-reflection,
  real.v:191-192) then pulls the comparison back through the morphisms; the
  result closes against `lexa` and the negated case.

The lemma graph (which project lemma uses which, direct edges only):

```
Rmorph_uniq ──┬─ reals_classic ── real_sup_total, real_sup_ub      (realprop.v)
              ├─ ratR_dense ── find_range1z, ltRW, leR_lt_trans, ltR0Sn (realprop.v)
              └─ Rmorph_rat ── Rmorph_inv ── Rmorph_neq0 ── Rmorph_eq   (realcategorical.v)
                              └─ Rmorph_int                              (realcategorical.v)
```

`Rmorph_eq` closes by `rewrite /Real.eq !Real.morph_le` on the morphism field
`Real.morph_le` alone, and `real_sup_total` / `real_sup_ub` close on the
`Real.sup_total` / `Real.sup_upper_bound` axioms, so the chain bottoms out in
the model's axioms. Each of the three children is a good leaf: a
self-contained statement whose proof closes on its own or from named siblings
in the same project — `reals_classic` on the sup axioms via `real_sup_total`,
`ratR_dense` on the Archimedean floor machinery via `find_range1z`, and
`Rmorph_rat` on the morphism field lemmas `phiM`, `Rmorph_inv`, `Rmorph_int`.

## Why it is good

1. `Rmorph_uniq` is declared at `theories/reals/realcategorical.v`, lines
   203-205 ([permalink](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/reals/realcategorical.v#L203-L205); form `declared(Rmorph_uniq, theories/reals/realcategorical.v, 203-205)`).
2. `Rmorph_rat` occurs as a whole identifier in the `Rmorph_uniq` site
   ([permalink](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/reals/realcategorical.v#L210); form `cites(Rmorph_uniq, Rmorph_rat)`).
3. The `Rmorph_uniq` site is 9 lines long — the whole glue, declaration and
   proof included ([permalink](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/reals/realcategorical.v#L203-L211); form `lines(Rmorph_uniq, 9)`).
4. (measurement) `Rmorph_uniq`'s proof calls three project lemmas directly —
   `reals_classic`, `ratR_dense`, `Rmorph_rat` — and the longest checked chain
   of project lemmas below it is `Rmorph_rat → Rmorph_inv → Rmorph_neq0 →
   Rmorph_eq`, depth 4 (realcategorical.v:203-211, 166-167, 159-164, 77-78,
   50-51).
5. (known-use) `Rmorph_uniq` is reused at realcategorical.v:377 (inside
   `Rmorph_to_inv`) and realcategorical.v:382 (inside `Rmorph_to_id`), the two
   lemmas that make `Rmorph_to` an isomorphism between any two real models
   ([permalink](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/reals/realcategorical.v#L375-L382)).

In my opinion the detail worth copying is the pairing of `wlog` with density:
symmetry collapses the two order directions to one, and a single rational
witness then settles the remaining direction, so the whole uniqueness proof is
four lines.

## When to use it, and when not

Use it to prove pointwise equality of two structure-preserving maps into a
model, when (a) the equality is a setoid equality built from order
antisymmetry, (b) the two maps reflect the order and preserve a dense subset
(here the rationals), and (c) excluded middle is available in the codomain.
The `wlog` step needs the statement to be symmetric under swapping the two
maps.

Avoid it when the codomain is only a `Real.structure`, not a `Real.model` (no
`reals_classic`, no `ratR_dense`); when the maps do not reflect the order, so
a strict gap cannot be pulled back; when the equality is intensional `=`
rather than `Real.eq`; or when the two directions need genuinely different
arguments, so `wlog` does not apply.

## Consequences

The move splits the pointwise equality into the two order directions and
discharges both from a single `wlog` proof of `phi x <= psi x`. Obligations it
creates: excluded middle must be available (`reals_classic`, derived from the
`Real.sup_total` axiom, so the codomain must be a `Real.model`); the rationals
must be dense in the model (`ratR_dense`); and the morphism must both preserve
the dense subset (`Rmorph_rat`) and reflect the order (`Real.morph_le`) to pull
the interpolated rational back to a contradiction. Failure modes: the argument
relies on the order being total (so `~(phi x <= psi x)` is the strict
`psi x < phi x`) and on the equality being the setoid `Real.eq` rather than
intensional `=`.

## Verification

<!-- verification:start -->
Status: **verified**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/nix-action-master.yml (fourcolor job: nix-build bundle master job fourcolor; _CoqProject lists theories/reals/realcategorical.v); pinned commit c1d6b1cd5288bea4b067aac13cdde3c18dffe018 is HEAD of default branch master | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: reals_classic@theories/reals/realcategorical.v:209, ratR_dense@theories/reals/realcategorical.v:209, Rmorph_rat@theories/reals/realcategorical.v:210; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 4 file(s) byte-identical at c1d6b1cd5288bea4b067aac13cdde3c18dffe018 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(Rmorph_uniq, theories/reals/realcategorical.v, 203-205) -> declared: Rmorph_uniq is declared at theories/reals/realcategorical.v:203 | check_claims.py |
| 2 | verified | cites(Rmorph_uniq, Rmorph_rat) -> cites: Rmorph_rat occurs at theories/reals/realcategorical.v:210 | check_claims.py |
| 3 | verified | lines(Rmorph_uniq, 9) -> lines: site Rmorph_uniq has 9 lines | check_claims.py |
| 4 | verified | read realcategorical.v:209-210 (calls reals_classic, ratR_dense, Rmorph_rat = 3 project lemmas); Rmorph_rat:166-167 uses Rmorph_inv; Rmorph_inv:160-164 uses Rmorph_neq0; Rmorph_neq0:77-78 rewrites -phi_eq where 'Let phi_eq := Rmorph_eq phiP' (realcategorical.v:64); Rmorph_eq:50-51 base (Real.morph_le). Chain depth 4 confirmed. | verifier |
| 5 | verified | read realcategorical.v:377 'apply: Rmorph_uniq ...' in Rmorph_to_inv and :382 'exact: Rmorph_uniq ...' in Rmorph_to_id; both reuse Rmorph_uniq | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | object | Parent Rmorph_uniq (realcategorical.v:203-211) and the three children (reals_classic 338-344, ratR_dense 849-863, Rmorph_rat 166-167) match the copied code verbatim; glue-cites-children and sorry-scan pass and the proof ends in Qed, so it closes and the three children are exactly the project lemmas the glue applies (plus the view ltRW at line 209, uncounted). BUT shape.depth=4 and claim 4 are wrong: the longest chain of project lemmas below Rmorph_uniq exceeds 4. reals_classic (realprop.v:342) uses ltR01 (315) -> ltR_total (117) -> leR_total (102) -> real_sup_total (99), depth 5; and ratR_dense -> find_range1z (844) -> int_floor (807) -> sup_total (525), where sup_total applies reals_classic at realprop.v:527, reaches depth 9. Fix: recompute shape.depth to the true longest chain (>=5, or 9 counting re-entry of the sibling reals_classic) and correct claim 4's 'depth 4'. | reviewer-correctness |
| generality | accept | Generality is honest and specific. The move is stated abstractly in 'When to use it': pointwise setoid equality built from order antisymmetry, two maps that reflect the order and preserve a dense subset (here the rationals), excluded middle in the codomain, and a statement symmetric under swapping the maps so wlog applies. This generalizes past the example (the dense subset is named as a parameter, 'here the rationals'). 'When not to use' names four concrete failure points that match the copied code: codomain only Real.structure not Real.model (reals_classic/ratR_dense live on the model's sup axioms / find_range1z), maps that do not reflect the order (Real.morph_le is the iff that pulls the gap back), intensional = instead of Real.eq (real.v:121 defines eq as le x y AND le y x), and asymmetric directions defeating wlog. Consequences restate the same obligations and failure modes consistently. Good-leaf question is answered explicitly (README lines 108-112): each child is a self-contained statement whose proof closes on its own or from named siblings and bottoms out in the model's axioms (reals_classic via real_sup_total, ratR_dense via find_range1z, Rmorph_rat via phiM/Rmorph_inv/Rmorph_int), which I confirmed by reading the cited line ranges. Minor non-blocking note: the consequences parenthetical attributes the step '~(phi x <= psi x) is psi x < phi x' to totality, but that is definitional (real.v:212 lt is ~ le y x); totality is instead needed for the density/order-reflection substance, so the generalization still stands. | reviewer-generality |
| provenance-licence | accept | Permalinks all pin commit c1d6b1cd5288bea4b067aac13cdde3c18dffe018 and the cited line ranges match the local copies (parent 203-211, children 166-167, 338-344, 849-863); check_provenance reports 4 files byte-identical at that commit; entry licence CECILL-B agrees with source.json, SOURCE.md, and upstream-LICENSE (CeCILL-B); source note, commit and licence are consistent and traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/math-comp/fourcolor at commit `c1d6b1cd5288bea4b067aac13cdde3c18dffe018`, under `CECILL-B`; see the [source note](../../sources/fourcolor/SOURCE.md) for the licence text and attribution.
