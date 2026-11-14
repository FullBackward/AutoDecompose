# Induction on the hybrid count for the PRF-to-PRG advantage bound

| | |
|---|---|
| Kind | instance |
| Move | induction |
| Language | rocq |
| Status | accepted |
| Source | [ssprove](../../sources/ssprove/SOURCE.md) at `9a37fe0ab79d` |
| Licence | `MIT` |

## Intent

Turn the PRF-to-PRG advantage bound into a telescoping sum of per-step PRF
advantages by induction on the number of hybrid steps `q`, so that the only
remaining content is two named per-step equivalences between adjacent hybrids.

## The decomposition

### parent `hyb_security_based_on_prf`: [`theories/Crypt/examples/PRFPRG.v` lines 314-339](https://github.com/SSProve/ssprove/blob/9a37fe0ab79d041f8d835e6cf18e37614b16a791/theories/Crypt/examples/PRFPRG.v#L314-L339) ([local copy](code/theories/Crypt/examples/PRFPRG.v))

```coq
Theorem hyb_security_based_on_prf LA A q:
  ValidPackage LA
    [interface #val #[query]: 'unit → 'word × 'word ]
    A_export A ->
  fseparate LA EVAL_locs_tt ->
  fseparate LA EVAL_locs_ff ->
  fseparate LA GEN_HYB_locs ->
  AdvantageE (GEN_HYB_pkg 0) (GEN_HYB_pkg q) A <=
  \sum_(i < q) prf_epsilon (A ∘ GEN_HYB_EVAL_pkg i).
Proof.
  move=> vA d1 d2 d3.
  elim: q => [|q IHq].
  1: by rewrite big_ord0 /AdvantageE GRing.subrr normr0.
  ssprove triangle (GEN_HYB_pkg 0) [::
    pack (GEN_HYB_pkg q) ;
    GEN_HYB_EVAL_pkg q ∘ EVAL true ;
    GEN_HYB_EVAL_pkg q ∘ EVAL false
  ] (GEN_HYB_pkg q.+1) A
  as ineq.
  apply: le_trans.
  1: by apply: ineq.
  rewrite -> GEN_GEN_HYB_equiv by ssprove_valid.
  rewrite -> GEN_GEN_HYB_EVAL_equiv by ssprove_valid.
  rewrite 2!GRing.addr0 big_ord_recr lerD //.
  by rewrite /prf_epsilon Advantage_E Advantage_link Advantage_sym.
Qed.
```

### child `GEN_GEN_HYB_equiv`: [`theories/Crypt/examples/PRFPRG.v` lines 218-253](https://github.com/SSProve/ssprove/blob/9a37fe0ab79d041f8d835e6cf18e37614b16a791/theories/Crypt/examples/PRFPRG.v#L218-L253) ([local copy](code/theories/Crypt/examples/PRFPRG.v))

```coq
Lemma GEN_GEN_HYB_equiv i:
  GEN_HYB_pkg i ≈₀ GEN_HYB_EVAL_pkg i ∘ EVAL true.
Proof.
  apply eq_rel_perf_ind with (
    (heap_ignore [fmap k_loc]) ⋊
    couple_rhs count_loc k_loc
      (fun count k => count <= i -> k = None)
    ).
  1: ssprove_invariant => //.
  simplify_eq_rel m.
  ssprove_code_simpl.
  apply: r_get_vs_get_remember => count.
  case: (eq_dec count i) => Heq.
  - rewrite Heq eq_refl ltnn /=.
    ssprove_swap_rhs 0.
    apply: r_get_remember_rhs => k.
    ssprove_rem_rel 0%N => Hinv.
    rewrite Hinv //.
    apply: r_put_vs_put.
    ssprove_sync=> s.
    eapply r_transR; [ apply: r_put_get |].
    apply: r_put_rhs.
    ssprove_restore_mem;
      last by apply: r_ret.
    ssprove_invariant.
    by rewrite ltnn.
  - move /eqP /negPf in Heq.
    rewrite Heq /=.
    destruct (count < i) eqn:Hlt.
    all: apply: r_put_vs_put.
    all: ssprove_sync=> x.
    1: ssprove_sync=> y.
    all: ssprove_restore_mem;
      last by apply: r_ret.
    all: ssprove_invariant.
Qed.
```

### child `GEN_GEN_HYB_EVAL_equiv`: [`theories/Crypt/examples/PRFPRG.v` lines 259-299](https://github.com/SSProve/ssprove/blob/9a37fe0ab79d041f8d835e6cf18e37614b16a791/theories/Crypt/examples/PRFPRG.v#L259-L299) ([local copy](code/theories/Crypt/examples/PRFPRG.v))

```coq
Lemma GEN_GEN_HYB_EVAL_equiv i:
  GEN_HYB_EVAL_pkg i ∘ EVAL false ≈₀ GEN_HYB_pkg i.+1.
Proof.
  apply eq_rel_perf_ind with (
    (heap_ignore [fmap T_loc]) ⋊
    couple_lhs count_loc T_loc
      (fun count T => count <= i -> T = emptym)
    ).
  1: ssprove_invariant => //=; fmap_solve.
  simplify_eq_rel m.
  ssprove_code_simpl.
  apply: r_get_vs_get_remember => count.
  case: (eq_dec count i) => Heq.
  - rewrite Heq eq_refl ltnn ltnSn /=.
    ssprove_swap_lhs 0.
    apply: r_get_remember_lhs => T.
    ssprove_rem_rel 0%N => Hinv.
    rewrite Hinv //=.
    apply: r_put_vs_put.
    ssprove_sync=> x.
    eapply r_transL; [ apply: r_put_get |].
    apply: r_put_lhs.
    rewrite setmE /=.
    ssprove_sync=> y.
    apply: r_put_lhs.
    ssprove_restore_mem;
      last by apply: r_ret.
    ssprove_invariant.
    by rewrite ltnn.
  - move /eqP /negPf in Heq.
    rewrite Heq /=.
    destruct (count < i) eqn:Hlt.
    all: apply: r_put_vs_put.
    1: rewrite ltnW //.
    2: rewrite ltnS leq_eqVlt Heq Hlt /=.
    all: ssprove_sync => x.
    1: ssprove_sync => y.
    all: ssprove_restore_mem;
      last by apply: r_ret.
    all: ssprove_invariant.
Qed.
```

How the parts fit. The parent `hyb_security_based_on_prf` proves, by induction
on `q`, that the advantage between the first hybrid `GEN_HYB_pkg 0` and the
`q`-th hybrid `GEN_HYB_pkg q` is at most the sum over `i < q` of the per-step
PRF advantages.

- **Base case** (`q = 0`, line 326): `big_ord0` empties the sum and
  `AdvantageE`'s self-distance is `0`.
- **Step**: `ssprove triangle` (lines 327-331) inserts the three intermediate
  hybrids and returns `ineq`, the triangle inequality bounding the `0 → q.+1`
  advantage by the sum of the three adjacent advantages. After `le_trans`, the
  two child lemmas collapse the two non-trivial adjacent edges to `0`:
  - line 335 `rewrite -> GEN_GEN_HYB_equiv by ssprove_valid.` uses child
    `GEN_GEN_HYB_equiv` to turn `GEN_HYB_pkg q ≈₀ GEN_HYB_EVAL_pkg q ∘ EVAL true`
    into a zero advantage (the PRF edge);
  - line 336 `rewrite -> GEN_GEN_HYB_EVAL_equiv by ssprove_valid.` uses child
    `GEN_GEN_HYB_EVAL_equiv` to turn `GEN_HYB_EVAL_pkg q ∘ EVAL false ≈₀
    GEN_HYB_pkg q.+1` into a zero advantage (the random-function edge).
  What remains telescopes: `big_ord_recr` peels the last summand and `IHq` plus
  the per-step `prf_epsilon` definition close the step (lines 337-338).

Lemma graph (who uses whom, in text):

    security_based_on_prf (347)          ← the final theorem, not a child
         └─ uses hyb_security_based_on_prf (368)
    hyb_security_based_on_prf (314)      ← parent / glue
         ├─ uses GEN_GEN_HYB_equiv        (218)
         └─ uses GEN_GEN_HYB_EVAL_equiv   (259)
    GEN_GEN_HYB_equiv, GEN_GEN_HYB_EVAL_equiv use no further project lemma —
    they close on SSProve library tactics — so the chain below the main theorem
    has depth 1.

Why each lemma is a good leaf.

- `GEN_GEN_HYB_equiv` is a self-contained `≈₀` statement whose proof closes on
  its own: `apply eq_rel_perf_ind` with the coupling
  `count <= i -> k = None`, then a `case: (eq_dec count i)`. The authors note
  the idea in a comment (lines 214-217): "The main trick is to realise that `k`
  is uninitialised when `count <= i`."
- `GEN_GEN_HYB_EVAL_equiv` is the mirror image, with the coupling
  `count <= i -> T = emptym`; its comment (lines 255-258) says "This proof is
  very similar to the previous proof, except it is `T` that is uninitialised
  when `count <= i`." Neither references the other: each is an independent leaf
  that closes on library tactics alone.

The glue (the parent's proof) is the `induction` move: it picks `q` as the
induction variable, leaves the two per-step equivalences as named holes, and
combines them with a triangle inequality and a telescoping `big_ord_recr`.


## Why it is good

1. The parent theorem `hyb_security_based_on_prf` is declared at
   [`theories/Crypt/examples/PRFPRG.v` lines 314-339](https://github.com/SSProve/ssprove/blob/9a37fe0ab79d041f8d835e6cf18e37614b16a791/theories/Crypt/examples/PRFPRG.v#L314-L339)
   ([check, `declared`]).
2. The glue (parent site) cites the child `GEN_GEN_HYB_equiv` ([check,
   `cites`](https://github.com/SSProve/ssprove/blob/9a37fe0ab79d041f8d835e6cf18e37614b16a791/theories/Crypt/examples/PRFPRG.v#L314-L339)).
3. The glue cites the child `GEN_GEN_HYB_EVAL_equiv` ([check,
   `cites`](https://github.com/SSProve/ssprove/blob/9a37fe0ab79d041f8d835e6cf18e37614b16a791/theories/Crypt/examples/PRFPRG.v#L314-L339)).
4. The glue is 26 lines and the two children 36 and 41 lines, with 2 direct
   lemmas and depth 1 ([measurement](https://github.com/SSProve/ssprove/blob/9a37fe0ab79d041f8d835e6cf18e37614b16a791/theories/Crypt/examples/PRFPRG.v#L314-L339)
   and [218-253](https://github.com/SSProve/ssprove/blob/9a37fe0ab79d041f8d835e6cf18e37614b16a791/theories/Crypt/examples/PRFPRG.v#L218-L253),
   [259-299](https://github.com/SSProve/ssprove/blob/9a37fe0ab79d041f8d835e6cf18e37614b16a791/theories/Crypt/examples/PRFPRG.v#L259-L299)).
5. The authors state the induction plan in a comment: "First we prove a bound
   on the hybrid packages. Since `q` can be any number the bound is a sum of
   `prf_epsilon`, and the proof is by induction"
   ([author-statement](https://github.com/SSProve/ssprove/blob/9a37fe0ab79d041f8d835e6cf18e37614b16a791/theories/Crypt/examples/PRFPRG.v#L310-L313)).

In my opinion the reusable part is the two-leaf shape: a hybrid argument whose
step reduces to *exactly two* named per-step equivalences, one per "edge" of the
triangle (`EVAL true` and `EVAL false`), so the glue never opens either child.

## When to use it, and when not

Use this when the goal is an advantage bound between two end hybrids that
differs only through a count parameter `q` under a `\sum_(i < q)`, and every
adjacent pair of hybrids is related by an equivalence already stated as its own
lemma. Here the two edges are `GEN_GEN_HYB_equiv` (PRF edge) and
`GEN_GEN_HYB_EVAL_equiv` (random-function edge), and the base case is the empty
sum `big_ord0`. Avoid it when the per-step advantage is not uniform enough to
be one reusable equivalence, when each step needs a different coupling, when
the base case is not the empty sum, or when `q` is not a natural-number
induction variable.

## Consequences

The move creates a base obligation (`q = 0`, discharged by `big_ord0` plus
`AdvantageE`'s self-distance being `0`) and a step obligation. The step relies
on `ssprove triangle` to insert the intermediate hybrids, then two rewrites
`GEN_GEN_HYB_equiv` and `GEN_GEN_HYB_EVAL_equiv`, each with a validity side
condition discharged by `ssprove_valid`. If either equivalence is missing or
its package is not valid the rewrite fails. The bound transfers to the full PRG
only through the final theorem `security_based_on_prf` (line 347), which
additionally needs the unformalised hypothesis that the last hybrid is
perfectly indistinguishable from `GEN false` (comment at lines 341-346).

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/opam-build.yml runs 'opam exec -- make' on push/PR to main; _RocqProject lists theories/Crypt/examples/PRFPRG.v; commit 9a37fe0ab79d041f8d835e6cf18e37614b16a791 on default branch main | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: GEN_GEN_HYB_equiv@theories/Crypt/examples/PRFPRG.v:335, GEN_GEN_HYB_EVAL_equiv@theories/Crypt/examples/PRFPRG.v:336; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 9a37fe0ab79d041f8d835e6cf18e37614b16a791 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(hyb_security_based_on_prf, theories/Crypt/examples/PRFPRG.v, 314-339) -> declared: hyb_security_based_on_prf is declared at theories/Crypt/examples/PRFPRG.v:314 | check_claims.py |
| 2 | verified | cites(parent, GEN_GEN_HYB_equiv) -> cites: GEN_GEN_HYB_equiv occurs at theories/Crypt/examples/PRFPRG.v:335 | check_claims.py |
| 3 | verified | cites(parent, GEN_GEN_HYB_EVAL_equiv) -> cites: GEN_GEN_HYB_EVAL_equiv occurs at theories/Crypt/examples/PRFPRG.v:336 | check_claims.py |
| 4 | verified | glue lines 314-339 = 26 lines (Theorem 314, Qed 339); child GEN_GEN_HYB_equiv 218-253 = 36 lines; child GEN_GEN_HYB_EVAL_equiv 259-299 = 41 lines; proof cites only GEN_GEN_HYB_equiv (line 335) and GEN_GEN_HYB_EVAL_equiv (line 336), both Qed-closed on library tactics, depth 1 | verifier |
| 5 | verified | comment at lines 310-313: 'First we prove a bound on the hybrid packages. Since [q] can be any number the bound is a sum of [prf_epsilon], and the proof is by induction.' | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent statement verbatim matches code lines 314-322; both child statements verbatim (GEN_GEN_HYB_equiv 218, GEN_GEN_HYB_EVAL_equiv 259); glue cites each child exactly once (rewrite at 335 and 336); children are exactly the two project lemmas the parent uses (remaining citations are library tactics/lemmas); children close on library tactics so depth=1; shape numbers correct (glue 339-314+1=26, child_lines 253-218+1=36 and 299-259+1=41, direct_lemmas=2, depth=1); proof ends Qed (no sorry/admit); base case at 326, ssprove triangle 327-332, telescoping 337-338 all as described. | reviewer-correctness |
| generality | accept | Generality lens: the move is stated beyond the example — applicability.goal_shape and use_when describe induction on a count parameter q under a sum unfolded by big_ord_recr, with per-step equivalence lemmas as leaves and a triangle inequality as glue, and also_known_as names the general pattern (hybrid argument / game hopping). avoid_when is honest and specific (non-uniform per-step advantage, per-step couplings, non-empty base case, q not a nat induction variable). Consequences are honest: it names the base and step obligations, the ssprove triangle/rewrite+ssprove_valid failure mode, and that the bound transfers to the full PRG only through security_based_on_prf with the AdvantageE(...)=0 hypothesis left unproved (comment 341-346 confirmed). Good-leaf rationale is present and concrete: both children are self-contained ≈₀ statements closing on their own couplings plus a case split, independent of each other, closing on library tactics alone, depth 1, 36/41 lines — verified against the copied code ranges. | reviewer-generality |
| provenance-licence | accept | check_provenance passes: 1 file byte-identical at commit 9a37fe0ab79d041f8d835e6cf18e37614b16a791; commit and licence MIT are recorded consistently across entry.json source, sources/ssprove/source.json, and sources/ssprove/SOURCE.md; upstream-LICENSE is 'MIT License, Copyright (c) 2021 SSProve'; every permalink uses the pinned commit and its cited line ranges match the copied PRFPRG.v (parent 314-339, children 218-253 and 259-299, author comment 310-313). | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/SSProve/ssprove at commit `9a37fe0ab79d041f8d835e6cf18e37614b16a791`, under `MIT`; see the [source note](../../sources/ssprove/SOURCE.md) for the licence text and attribution.
