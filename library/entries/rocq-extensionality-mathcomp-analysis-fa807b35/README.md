# Extensionality on measurable sets proves associativity of the Giry monad (giry_joinA)

| | |
|---|---|
| Kind | instance |
| Move | extensionality |
| Language | rocq |
| Status | accepted |
| Source | [mathcomp-analysis](../../sources/mathcomp-analysis/SOURCE.md) at `eca10f89bd85` |
| Licence | `CECILL-C` |

## Intent

Two subprobability measures are equal in the sense of `measure_eq` (the notation `≡μ`): they agree on every measurable set. The associativity law of the Giry monad, `(giry_join \o giry_map measurable_giry_join) x ≡μ (giry_join \o giry_join) x`, is proved by reducing the equality to a single generic measurable set `A`, then rewriting each side with an integral lemma so that both sides become the same integral. `giry_int_map` unfolds the outer `giry_map`, `giry_int_join` unfolds one `giry_join`, and `measurable_giry_ev` closes the measurability side conditions.

## The decomposition

### parent `giry_joinA`: [`theories/lebesgue_integral_theory/giry.v` lines 375-382](https://github.com/math-comp/analysis/blob/eca10f89bd852201c8148ff2f597c7c7346d6df2/theories/lebesgue_integral_theory/giry.v#L375-L382) ([local copy](code/theories/lebesgue_integral_theory/giry.v))

```coq
Lemma giry_joinA (x : giry (giry (giry T1 R) R) R) :
  (giry_join \o giry_map measurable_giry_join) x ≡μ
  (giry_join \o giry_join) x.
Proof.
move=> A mA/=.
rewrite giry_int_map//; first exact: measurable_giry_ev.
by rewrite giry_int_join//; exact: measurable_giry_ev.
Qed.
```

### child `giry_int_map`: [`theories/lebesgue_integral_theory/giry.v` lines 201-204](https://github.com/math-comp/analysis/blob/eca10f89bd852201c8148ff2f597c7c7346d6df2/theories/lebesgue_integral_theory/giry.v#L201-L204) ([local copy](code/theories/lebesgue_integral_theory/giry.v))

```coq
Lemma giry_int_map (mu : giry T1 R) (h : T2 -> \bar R) :
  measurable_fun [set: T2] h -> (forall x, 0 <= h x) ->
  giry_int (giry_map mf mu) h = giry_int mu (h \o f).
Proof. by move=> mh h0; exact: ge0_integral_pushforward. Qed.
```

### child `giry_int_join`: [`theories/lebesgue_integral_theory/giry.v` lines 312-339](https://github.com/math-comp/analysis/blob/eca10f89bd852201c8148ff2f597c7c7346d6df2/theories/lebesgue_integral_theory/giry.v#L312-L339) ([local copy](code/theories/lebesgue_integral_theory/giry.v))

```coq
Lemma giry_int_join (M : giry (giry T R) R) (h : T -> \bar R) :
    measurable_fun [set: T] h -> (forall x, 0 <= h x) ->
  giry_int (giry_join M) h = giry_int M (giry_int ^~ h).
Proof.
move=> mh h0.
pose g := nnsfun_approx measurableT mh.
pose gE := fun n => EFin \o g n.
have mgE n : measurable_fun [set: T] (gE n) by exact/measurable_EFinP.
have gE_ge0 n x : 0 <= gE n x by rewrite lee_fin.
have nd_gE x : {homo gE ^~ x : n m / (n <= m)%O >-> n <= m}.
  by move=> *; exact/lefP/nd_nnsfun_approx.
rewrite /giry_int.
transitivity (limn (fun n => \int[giry_join M]_x gE n x)).
  rewrite -monotone_convergence//; apply: eq_integral => t _.
  by apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
transitivity (limn (fun n => \int[M]_mu \int[mu]_x gE n x)).
  apply: congr_lim; apply/funext => n.
  rewrite integralT_nnsfun sintegral_giry_join; apply: eq_integral => x _.
  by rewrite integralT_nnsfun.
rewrite -[LHS]monotone_convergence//.
- by move=> n; exact: measurable_giry_int.
- by move=> n x _; exact: integral_ge0.
- by move=> x _ m n mn; apply: ge0_le_integral => // t _; exact: nd_gE.
apply: eq_integral => mu _.
rewrite -monotone_convergence//.
apply: eq_integral => t _.
by apply/cvg_lim => //; exact: cvg_nnsfun_approx.
Qed.
```

### child `measurable_giry_ev`: [`theories/lebesgue_integral_theory/giry.v` lines 88-96](https://github.com/math-comp/analysis/blob/eca10f89bd852201c8148ff2f597c7c7346d6df2/theories/lebesgue_integral_theory/giry.v#L88-L96) ([local copy](code/theories/lebesgue_integral_theory/giry.v))

```coq
Lemma measurable_giry_ev (A : set T) : measurable A ->
  measurable_fun [set: giry] (giry_ev ^~ A).
Proof.
move=> mS.
apply: (@measurability giry_display _ giry _ setT (giry_ev ^~ A) measurable).
  by rewrite smallest_id//; exact: sigma_algebra_measurable.
apply: subset_trans; last exact: sub_gen_smallest.
exact: (bigcup_sup mS).
Qed.
```

### How the parts fit

The glue is the three-line proof of `giry_joinA` shown above. Its steps and the lemma graph:

```
giry_joinA (parent)
├── giry_int_map        (rewrites the left side; closed by ge0_integral_pushforward)
├── giry_int_join       (rewrites the right side; uses sintegral_giry_join, measurable_giry_int)
│     ├── sintegral_giry_join   (uses measurable_giry_ev)
│     └── measurable_giry_int   (uses measurable_giry_ev)
└── measurable_giry_ev  (closes the measurability side conditions on both sides)
```

1. `move=> A mA` is the extensionality step. Because `≡μ` is `measure_eq`
   (`forall S, measurable S -> m1 S = m2 S`, defined at lines 44-47 of the same
   file), introducing `A` and `mA : measurable A` turns the equality of
   measures into a pointwise equality of the two sides applied to `A`.

2. `rewrite giry_int_map//` rewrites the left side
   `giry_int (giry_map measurable_giry_join x) (giry_ev ^~ A)` into
   `giry_int x ((giry_ev ^~ A) \o measurable_giry_join)`. Its measurability
   hypothesis is closed by `first exact: measurable_giry_ev`; the nonnegativity
   hypothesis is discharged by the `//`.

3. `rewrite giry_int_join//` rewrites the right side
   `giry_int (giry_join x) (giry_ev ^~ A)` into
   `giry_int x (giry_int ^~ (giry_ev ^~ A))`, and
   `exact: measurable_giry_ev` closes its measurability hypothesis. The two
   sides now coincide because `giry_join mu A` is, by definition,
   `giry_int mu (giry_ev ^~ A)`, so `(giry_ev ^~ A) \o measurable_giry_join`
   and `giry_int ^~ (giry_ev ^~ A)` are the same function of `mu`.

Why each direct lemma is a good leaf:

- **`giry_int_map`** is a self-contained statement (integral of a pushforward
  = integral of the composition) whose proof is one line, closed by the
  mathcomp library lemma `ge0_integral_pushforward`. The glue never has to
  reopen integration theory.

- **`giry_int_join`** is the substantial leaf, but its statement is still
  self-contained (integrating over the joined measure = integrating the
  integral), and its 28-line proof closes entirely on its named siblings
  `sintegral_giry_join` and `measurable_giry_int` plus mathcomp facts
  (`monotone_convergence`, `eq_integral`, `cvg_nnsfun_approx`). The glue sees
  only its statement.

- **`measurable_giry_ev`** is a self-contained measurability statement
  (evaluation at a measurable set is a measurable function on measures) closed
  by the sigma-algebra lemmas (`sigma_algebra_measurable`, `sub_gen_smallest`,
  `bigcup_sup`). It is the reusable side-condition leaf: both rewrite lemmas
  and the glue itself cite it.

## Why it is good

1. The parent's proof cites each of the three children directly: `giry_int_map`
   (line 380), `giry_int_join` (line 381) and `measurable_giry_ev` (lines 380
   and 381) — machine-checked, see the claims.
2. The glue is 8 lines and the three children are 4, 28 and 9 lines
   (declaration and proof); the lemma graph below the main theorem is 3 deep —
   a shape measured in the claims.
3. The same extensionality move proves the two other monad laws in the same
   file, `giry_join_id1` and `giry_join_id2` (lines 384-400), each
   `move=> ... /=; rewrite giry_int_map//; exact: measurable_giry_ev`.
4. The side conditions created by the two rewrite lemmas (measurability and
   nonnegativity of the integrand) are discharged without any new proof effort:
   measurability by `measurable_giry_ev`, nonnegativity by the `//` triviality
   of subprobability measures.

In my opinion the detail worth copying is that the extensionality target
(`measure_eq`) makes the two sides of a monad law reduce to the *same* integral,
so the proof is exactly "introduce one generic measurable set, rewrite each
side with the right integral lemma, done" — the associativity content lives in
the already-proved `giry_int_join`, not in the glue.

## When to use it, and when not

Use it when the goal is an equality of measures whose equality relation is
pointwise on measurable sets (`measure_eq`/`≡μ`), and the two sides are the
same monadic combinator at different nesting, so a single generic measurable
set reduces each side to one integral that a pre-proved pushforward or join
lemma resolves. Avoid it when the equality is not pointwise on measurable sets
(the `move=> A mA` step will not reduce it), when the two sides need different
normalisation per set, or when the integral lemmas are not already proved —
without them the pointwise goal is not a leaf and must itself be decomposed.

## Consequences

The extensionality step introduces one generic measurable set `A` and the
obligation `mA : measurable A`, discharged by the side-condition lemma
`measurable_giry_ev` and the `//` that closes the nonnegativity hypotheses of
`giry_int_map` and `giry_int_join`. The proof rests entirely on the two
integral lemmas being proved beforehand; the associativity content is pushed
into `giry_int_join`, so if that lemma were missing the pointwise goal would
reopen the whole integration argument. The move works only because
`measure_eq` unfolds to pointwise equality on measurable sets — under a
different equality notion the same script would not apply.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/nix-action-master.yml builds the mathcomp-analysis package with nix-build; _CoqProject lists theories/lebesgue_integral_theory/giry.v; commit eca10f89bd852201c8148ff2f597c7c7346d6df2 is on master (default branch) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: giry_int_map@theories/lebesgue_integral_theory/giry.v:380, giry_int_join@theories/lebesgue_integral_theory/giry.v:381, measurable_giry_ev@theories/lebesgue_integral_theory/giry.v:380; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at eca10f89bd852201c8148ff2f597c7c7346d6df2 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(giry_joinA, giry_int_map) -> cites: giry_int_map occurs at theories/lebesgue_integral_theory/giry.v:380 | check_claims.py |
| 2 | verified | cites(giry_joinA, giry_int_join) -> cites: giry_int_join occurs at theories/lebesgue_integral_theory/giry.v:381 | check_claims.py |
| 3 | verified | cites(giry_joinA, measurable_giry_ev) -> cites: measurable_giry_ev occurs at theories/lebesgue_integral_theory/giry.v:380 | check_claims.py |
| 4 | verified | Read copied giry.v site spans: parent giry_joinA L375-382 (8 lines); children giry_int_map L201-204 (4), giry_int_join L312-339 (28), measurable_giry_ev L88-96 (9); 3 direct lemmas. Depth chain confirmed: giry_joinA L381 cites giry_int_join; giry_int_join L329 cites sintegral_giry_join; sintegral_giry_join L296-311 cites measurable_giry_ev (L301, L309). | verifier |
| 5 | verified | Read copied giry.v L384-400: giry_join_id1 (L384-392) = move=> A mA/=. then rewrite giry_int_map//; first exact: measurable_giry_ev (plus a giry_int_ret step); giry_join_id2 (L394-400) = by move=> X mS /=; rewrite giry_int_map//; exact: measurable_giry_ev. Both monad laws proved by the same extensionality step with giry_int_map + measurable_giry_ev. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Statements are verbatim copies of the code: parent giry_joinA (giry.v:375-382), children giry_int_map (201-204), giry_int_join (312-339), measurable_giry_ev (88-96) all match entry.json and README exactly. Parent proof (378-382) cites exactly these three children and closes (Qed at 382), with move=> A mA the extensionality step and both sides reduced to giry_int x (giry_ev ^~ A) by the two integral lemmas; side conditions closed by measurable_giry_ev and //. Closing methods match: giry_int_map = exact: ge0_integral_pushforward (204); giry_int_join = transitivity chain via monotone_convergence/eq_integral using sintegral_giry_join (329) and measurable_giry_int (332); measurable_giry_ev = measurability/sigma_algebra_measurable/sub_gen_smallest/bigcup_sup (92-95). Shape numbers correct: 3 direct lemmas, glue 8 lines (375-382), child_lines [4,28,9] = [201-204, 312-339, 88-96]; depth 3 confirmed by chain giry_joinA->giry_int_join->sintegral_giry_join->measurable_giry_ev (sintegral_giry_join cites measurable_giry_ev at 301,306). Children are exactly the lemmas the main proof uses; no extra or missing lemma. Provenance: byte-identical at commit eca10f89. | reviewer-correctness |
| generality | accept | Move stated beyond the example: applicability/use_when generalise to 'equality pointwise on measurable sets (measure_eq) + sides differ in monadic nesting, one generic A reduces each side to the same integral via a pre-proved pushforward/join lemma'. avoid_when and consequences are honest and specific (equality not pointwise-on-measurable-sets; different rewrites per A; integral lemmas not pre-proved -> pointwise goal must be split further; script breaks under a non-measure_eq relation). Leaf-goodness is explicit per child: giry_int_map self-contained 1-line proof closed by library lemma ge0_integral_pushforward; giry_int_join substantial but statement self-contained, closes on named siblings; measurable_giry_ev reusable side-condition leaf cited by both rewrites and the glue. Known-use (claim 5) is genuine: giry_join_id1/id2 at 384-400 reuse move=> A mA/=; rewrite giry_int_map//; exact: measurable_giry_ev. | reviewer-generality |
| provenance-licence | accept | check_provenance pass (1 file byte-identical at eca10f89bd852201c8148ff2f597c7c7346d6df2); commit, licence CECILL-C and file path consistent across entry.json, source.json, SOURCE.md and every permalink; upstream-LICENCE is CeCILL-C matching the recorded licence; copied-file sha256 ebf43e96... matches entry.json; all line-range permalinks resolve to the matching declarations in the copied giry.v | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/math-comp/analysis at commit `eca10f89bd852201c8148ff2f597c7c7346d6df2`, under `CECILL-C`; see the [source note](../../sources/mathcomp-analysis/SOURCE.md) for the licence text and attribution.
