# Witness transfinite_defined proves the function defined by transfinite recursion is unique

| | |
|---|---|
| Kind | instance |
| Move | witness |
| Language | rocq |
| Status | accepted |
| Source | [gaia](../../sources/gaia/SOURCE.md) at `5f54b6ee146e` |
| Licence | `MIT` |

## Intent

Prove the unique existence (`exists!`) of the function defined by transfinite
recursion on a well-ordering by supplying the named witness
`transfinite_defined r T` for the existence half and the lemma
`transfinite_unique` for the uniqueness half.

## The decomposition

### parent `transfinite_definition`: [`theories/sets/sset6.v` lines 2033-2039](https://github.com/rocq-community/gaia/blob/5f54b6ee146e86e938180f8037db411da224bb29/theories/sets/sset6.v#L2033-L2039) ([local copy](code/theories/sets/sset6.v))

```coq
Theorem transfinite_definition r T:
  worder r -> exists! f, (transfinite_def r T f).
Proof. 
move=> wo; apply /unique_existence. 
split; last by move=> x y;apply: (transfinite_unique wo). 
by exists (transfinite_defined r T); apply:transfinite_defined_pr.
Qed.
```

### child `transfinite_defined_pr`: [`theories/sets/sset6.v` lines 2015-2025](https://github.com/rocq-community/gaia/blob/5f54b6ee146e86e938180f8037db411da224bb29/theories/sets/sset6.v#L2015-L2025) ([local copy](code/theories/sets/sset6.v))

```coq
Lemma transfinite_defined_pr r T: worder r ->
  transfinite_def r T  (transfinite_defined r T).
Proof.
move=> wo; rewrite /transfinite_defined.
set T' := (fun f : Set => T (fgraph_to_fun f)).
move/ (transfinite_def_prop1 ):(transfinite_pr1 T' wo).
set f := fgraph_to_fun  _.
move => [ha hb hc]; split => // x xsr; rewrite (hc _ xsr) /T'.
have ss: sub (segment r x) (source f) by rewrite hb; apply: sub_segment.
by rewrite (fgraph_to_fun_restr (proj1 ha) ss) {2}/fgraph_to_fun/=; aw.
Qed.
```

### child `transfinite_unique`: [`theories/sets/sset6.v` lines 1745-1754](https://github.com/rocq-community/gaia/blob/5f54b6ee146e86e938180f8037db411da224bb29/theories/sets/sset6.v#L1745-L1754) ([local copy](code/theories/sets/sset6.v))

```coq
Lemma transfinite_unique r T : worder r -> 
  uniqueness (transfinite_def r T).
Proof.
move => wor f g fp gp.
move: (transfinite_def_prop2 fp) (transfinite_def_prop2 gp) => fp' gp'.
move:(transfiniteg_unique wor fp' gp') => sgr.
move:(proj31 fp)(proj31 gp) => sf sg; move: (proj1 sf)(proj1 sg) => ff fg.
apply: (function_exten1 ff fg sgr).
by rewrite - (surjective_pr0 sf) - (surjective_pr0 sg) (ImfE ff) (ImfE fg) sgr.
Qed.
```

### context `transfinite_defined`: [`theories/sets/sset6.v` lines 2012-2013](https://github.com/rocq-community/gaia/blob/5f54b6ee146e86e938180f8037db411da224bb29/theories/sets/sset6.v#L2012-L2013) ([local copy](code/theories/sets/sset6.v))

```coq
Definition transfinite_defined r T:=
  fgraph_to_fun (transfiniteg_defined r (fun f => T (fgraph_to_fun f))).
```

### context `transfinite_def`: [`theories/sets/sset6.v` lines 1696-1698](https://github.com/rocq-community/gaia/blob/5f54b6ee146e86e938180f8037db411da224bb29/theories/sets/sset6.v#L1696-L1698) ([local copy](code/theories/sets/sset6.v))

```coq
Definition transfinite_def r (T: fterm) f :=
  [/\ surjection f, source f = substrate r &
  forall x, inc x (substrate r) -> Vf f x = T (restriction1 f (segment r x))].
```

### context `transfiniteg_def`: [`theories/sets/sset6.v` lines 1700-1702](https://github.com/rocq-community/gaia/blob/5f54b6ee146e86e938180f8037db411da224bb29/theories/sets/sset6.v#L1700-L1702) ([local copy](code/theories/sets/sset6.v))

```coq
Definition transfiniteg_def r (T: fterm) f :=
  [/\ fgraph f, domain f = substrate r &
  forall x, inc x (substrate r) -> Vg f x = T (restr f (segment r x))].
```

How the parts fit. The parent `transfinite_definition` states
`exists! f, transfinite_def r T f`: the function defined by transfinite
recursion on a well-ordering exists and is unique. `transfinite_def` (context
above) says `f` is so defined when, for every `x` in the substrate,
`Vf f x = T (restriction1 f (segment r x))` — the value at `x` is `T` applied
to `f` restricted to the segment below `x`. The glue is three lines:

- `apply /unique_existence` (line 2036) turns `exists!` into the pair
  `existence /\ uniqueness`;
- the uniqueness half closes by `transfinite_unique` (line 2037);
- the existence half closes by `exists (transfinite_defined r T)` with
  `transfinite_defined_pr` (line 2038).

So the glue is a `split` with one lemma citation per half of the
unique-existence statement. The witness `transfinite_defined r T` is a named
`Definition` (context above), the function form of the graph-level
`transfiniteg_defined`; its property is the child `transfinite_defined_pr`.

How each child closed. `transfinite_defined_pr` (existence) unfolds
`/transfinite_defined`, applies `transfinite_def_prop1` to `transfinite_pr1`
(the graph-level property of `transfiniteg_defined`), and closes the remaining
pointwise goal by rewriting with `fgraph_to_fun_restr`. `transfinite_unique`
(uniqueness) sends the two functions to their graphs via
`transfinite_def_prop2`, obtains graph uniqueness from `transfiniteg_unique`,
and lifts it back to function equality via `function_exten1`.

The lemma graph below the main theorem (longest chain checked, depth 7):
`transfinite_definition` -> `transfinite_defined_pr` -> `transfinite_pr1` ->
`transfinite_exists1` -> `transfinite_aux2` -> `transfiniteg_unique` ->
`worder_prop2` -> `worder_prop`, all in this file. The uniqueness side is a
shorter chain: `transfinite_unique` uses `transfiniteg_unique` directly.

## Why it is good

1. The parent site cites `transfinite_defined_pr` — the existence half — at
   line 2038 (`check`,
   https://github.com/rocq-community/gaia/blob/5f54b6ee146e86e938180f8037db411da224bb29/theories/sets/sset6.v#L2033-L2039).
2. The parent site cites `transfinite_unique` — the uniqueness half — at line
   2037 (`check`, same locator).
3. The parent site, the whole glue, is 7 lines (`check`, same locator); this
   is the `glue_lines` number recorded in the shape.
4. The span 1745-2039 that holds both children and the parent contains no
   `admit`, `Admitted`, `Axiom` or `axiom` (`check`,
   https://github.com/rocq-community/gaia/blob/5f54b6ee146e86e938180f8037db411da224bb29/theories/sets/sset6.v#L1745-L2039).
5. The main proof body is 3 lines (2036-2038): `apply /unique_existence`, then
   a `split` whose uniqueness half closes by `transfinite_unique` and whose
   existence half closes by `exists (transfinite_defined r T)` with
   `transfinite_defined_pr` (`measurement`, same locator as 1).

The authors write the plan just above the definitions: "It exists, its graph
is unique" (comment, lines 1690-1694), matching the two halves. The children
are reused immediately — `transfinite_pr` (lines 2027-2030) and
`transfinite_definition_stable` (lines 2045-2053) both call
`transfinite_defined_pr`; these reuse sites are recorded in `known_uses`.

In my opinion the detail worth copying is that the witness is a named
`Definition` rather than an inline `exists` term, so its property is a
standalone, reusable lemma (`transfinite_defined_pr`) and the parent's proof
shrinks to a two-citation `split`.

## When to use it, and when not

Use it for a unique-existence goal `exists! f, P f` whose two halves are
already proved as named lemmas: a witness `w` with `P w`, and a uniqueness
lemma `forall f g, P f -> P g -> f = g`. It fits best when the witness is a
named definition (here built by `choose` from a graph-level existence theorem)
and `unique_existence` is the view that turns `exists!` into
`existence /\ uniqueness`, so the proof is a two-line `split`.

Avoid it when the witness must be synthesised inline and has no property lemma
yet — state the property as its own lemma first, as this file does. Avoid it
when the uniqueness argument is not a uniform "send to the graph" step and
differs per pair, or when the two halves share a large common core, which
should be proved once before splitting.

## Consequences

The move creates two obligations, one per half of `exists!`: existence,
discharged by the witness `transfinite_defined r T` with `transfinite_defined_pr`,
and uniqueness, discharged by `transfinite_unique`. Existence is deferred one
level: the witness is defined by `choose` from `transfinite_exists1`, so the
real content of existence lives below the glue. Naming the witness keeps its
property a reusable lemma (reused in `transfinite_definition_stable`); an
inline `exists` term would force that property proof to be repeated.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/docker-action.yml builds coq-gaia-theory-of-sets via 'opam install coq-gaia-theory-of-sets', which compiles theories/sets/sset6.v (listed in _CoqProject); workflow runs on push to master; commit 5f54b6ee146e86e938180f8037db411da224bb29 is the default-branch (master) HEAD pinned by register_source.py (ref HEAD) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: transfinite_defined_pr@theories/sets/sset6.v:2038, transfinite_unique@theories/sets/sset6.v:2037; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 5f54b6ee146e86e938180f8037db411da224bb29 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, transfinite_defined_pr) -> cites: transfinite_defined_pr occurs at theories/sets/sset6.v:2038 | check_claims.py |
| 2 | verified | cites(parent, transfinite_unique) -> cites: transfinite_unique occurs at theories/sets/sset6.v:2037 | check_claims.py |
| 3 | verified | lines(parent, 7) -> lines: site parent has 7 lines | check_claims.py |
| 4 | verified | no_sorry(theories/sets/sset6.v, 1745-2039) -> no_sorry: none of admit, Admitted, Axiom, axiom in theories/sets/sset6.v:1745-2039 | check_claims.py |
| 5 | verified | read copied code theories/sets/sset6.v lines 2033-2039: 2036 'move=> wo; apply /unique_existence.', 2037 'split; last by move=> x y;apply: (transfinite_unique wo).' (uniqueness half closes by transfinite_unique), 2038 'by exists (transfinite_defined r T); apply:transfinite_defined_pr.' (existence half closes by the witness with transfinite_defined_pr), 2039 'Qed.'; proof body is indeed 3 lines 2036-2038 | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent site (2033-2039) is verbatim: it views exists! via unique_existence and cites exactly the two children, transfinite_unique (2037, uniqueness half) and transfinite_defined_pr (2038, existence half, witness transfinite_defined). Both child statements in entry.json match code verbatim (2015-2016, 1745-1746); both close with Qed; parent closes with Qed at 2039. Shape numbers all right: direct_lemmas=2, glue_lines=7 (2033-2039), child_lines=[11,10] (2015-2025 and 1745-1754), depth=7 chain verified link-by-link: defined_pr->pr1 (L2020), pr1->exists1 (L1888), exists1->aux2 (L1875), aux2->g_unique (L1792), g_unique->worder_prop2 (L1737), worder_prop2->worder_prop (L92). | reviewer-correctness |
| generality | accept | Move stated generically: applicability.goal_shape is 'exists! f, P f' with a named witness w (P w) and a uniqueness lemma (forall f g, P f -> P g -> f = g), not tied to well-orderings; use_when names the reusable view unique_existence. avoid_when gives three concrete, honest conditions (inline witness with no property lemma yet; per-pair non-uniform uniqueness; large shared core). Consequences are specific and honest: they name the two obligations, admit existence is deferred below the glue (witness via choose from transfinite_exists1, depth-7 chain) and cite the reuse in transfinite_definition_stable. Verified in the copied file: the author comment 'It exists, its graph is unique' at 1690-1694, the named Definition transfinite_defined (2012-2013), the 3-line glue (2036-2038), and reuse in transfinite_pr (2030) and transfinite_definition_stable (2053). Leaf lesson is present in substance — named witness makes its property a standalone reusable lemma so the parent shrinks to a two-citation split, and the entry records child_lines 11/10 — though it is phrased as 'named standalone lemma' rather than 'bounded prover'. | reviewer-generality |
| provenance-licence | accept | commit 5f54b6ee146e86e938180f8037db411da224bb29 is consistent across entry.json, source.json, SOURCE.md and every permalink; licence MIT is consistent across entry.json, source.json, SOURCE.md and upstream-LICENSE (MIT License, Copyright Yves Bertot); check_provenance.py passes (1 file byte-identical at the pinned commit); all cited line ranges (parent 2033-2039, children 2015-2025 and 1745-1754, contexts 2012-2013/1696-1698/1700-1702, known_uses 2027-2030/2045-2053) in code/theories/sets/sset6.v match the README excerpts and entry.json statements verbatim | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/rocq-community/gaia at commit `5f54b6ee146e86e938180f8037db411da224bb29`, under `MIT`; see the [source note](../../sources/gaia/SOURCE.md) for the licence text and attribution.
