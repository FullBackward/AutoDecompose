# Hybrid game-hop chain bounds CCA advantage by the MAC and CPA epsilons

| | |
|---|---|
| Kind | instance |
| Move | calc-chain |
| Language | rocq |
| Status | accepted |
| Source | [ssprove](../../sources/ssprove/SOURCE.md) at `9a37fe0ab79d` |
| Licence | `MIT` |
| Licence recorded | 2026-11-14T15:39:15Z |

## Intent

Prove the CCA-security bound of the MAC-then-CPA construction (`CCA_EVAL`) as
a chain of game hops: one `ssprove triangle` turns `Advantage CCA_EVAL A` into
a sum over six intermediate packages, and four named program-equivalence
lemmas — one per hop — collapse that chain to `mac_epsilon (A ∘
CCA_EVAL_TAG_pkg_tt) + cpa_epsilon (A ∘ CCA_EVAL_HYB_pkg) + mac_epsilon (A ∘
CCA_EVAL_TAG_pkg_ff)`.

## The decomposition

### parent `security_based_on_mac`: [`theories/Crypt/examples/MACCCA.v` lines 434-470](https://github.com/SSProve/ssprove/blob/9a37fe0ab79d041f8d835e6cf18e37614b16a791/theories/Crypt/examples/MACCCA.v#L434-L470) ([local copy](code/theories/Crypt/examples/MACCCA.v))

```coq
Theorem security_based_on_mac LA A:
  ValidPackage LA
    [interface
      #val #[eavesdrop]: 'word × 'word → 'word × 'word ;
      #val #[decrypt]: 'word × 'word → 'option 'word ]
    A_export A ->
  fseparate LA TAG_locs_tt ->
  fseparate LA TAG_locs_ff ->
  fseparate LA CPA_EVAL_locs ->
  fseparate LA CCA_EVAL_locs ->
  fseparate LA CCA_EVAL_TAG_locs ->
  fseparate LA CCA_EVAL_HYB_locs ->
  Advantage CCA_EVAL A <=
  mac_epsilon (A ∘ CCA_EVAL_TAG_pkg_tt) +
  cpa_epsilon (A ∘ CCA_EVAL_HYB_pkg) +
  mac_epsilon (A ∘ CCA_EVAL_TAG_pkg_ff).
Proof.
  move=> vA d1 d2 d3 d4 d5 d6.
  rewrite Advantage_E Advantage_sym.
  ssprove triangle (CCA_EVAL true) [::
    CCA_EVAL_TAG_pkg_tt ∘ TAG true ;
    CCA_EVAL_TAG_pkg_tt ∘ TAG false ;
    CCA_EVAL_HYB_pkg ∘ CPA_EVAL true ;
    CCA_EVAL_HYB_pkg ∘ CPA_EVAL false ;
    CCA_EVAL_TAG_pkg_ff ∘ TAG false ;
    CCA_EVAL_TAG_pkg_ff ∘ TAG true
  ] (CCA_EVAL false) A as ineq.
  apply: le_trans.
  1: by apply: ineq.
  rewrite -> CCA_EVAL_equiv_true by ssprove_valid.
  rewrite -> CCA_EVAL_HYB_equiv_true by ssprove_valid.
  rewrite -> CCA_EVAL_HYB_equiv_false by ssprove_valid.
  rewrite -> CCA_EVAL_equiv_false by ssprove_valid.
  rewrite GRing.add0r 3!GRing.addr0.
  rewrite /mac_epsilon /cpa_epsilon !Advantage_E -!Advantage_link.
  by rewrite (Advantage_sym (TAG true)) (Advantage_sym (CPA_EVAL true)).
Qed.
```

### child `CCA_EVAL_equiv_true`: [`theories/Crypt/examples/MACCCA.v` lines 303-314](https://github.com/SSProve/ssprove/blob/9a37fe0ab79d041f8d835e6cf18e37614b16a791/theories/Crypt/examples/MACCCA.v#L303-L314) ([local copy](code/theories/Crypt/examples/MACCCA.v))

```coq
Lemma CCA_EVAL_equiv_true:
  CCA_EVAL true ≈₀ CCA_EVAL_TAG_pkg_tt ∘ TAG true.
Proof.
  apply: eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  all: apply rpost_weaken_rule with eq;
    last by move=> [? ?] [? ?] [].
  all: simplify_linking.
  all: ssprove_code_simpl.
  all: ssprove_code_simpl.
  all: by apply: rreflexivity_rule.
Qed.
```

### child `CCA_EVAL_HYB_equiv_true`: [`theories/Crypt/examples/MACCCA.v` lines 316-358](https://github.com/SSProve/ssprove/blob/9a37fe0ab79d041f8d835e6cf18e37614b16a791/theories/Crypt/examples/MACCCA.v#L316-L358) ([local copy](code/theories/Crypt/examples/MACCCA.v))

```coq
Lemma CCA_EVAL_HYB_equiv_true:
  CCA_EVAL_TAG_pkg_tt ∘ TAG false ≈₀ CCA_EVAL_HYB_pkg ∘ CPA_EVAL true.
Proof.
  apply eq_rel_perf_ind with (
    (fun '(h0, h1) => h0 = h1) ⋊
    couple_lhs S_loc T_loc
      (fun S T => S = T)
  ).
  1: ssprove_invariant=> //=.
  simplify_eq_rel m.
  all: simplify_linking.
  all: ssprove_code_simpl.
  all: ssprove_code_simpl.
  - case: m => [ml mr].
    apply: r_get_vs_get_remember => S.
    ssprove_sync=> [|[ke|]];
      first by move=> ? ? ->.
    2: ssprove_sync=> ke;
      ssprove_sync;
      first by move=> ? ? ->.
    all: apply: r_get_vs_get_remember => T.
    all: ssprove_sync=> [|[km|]];
      first by move=> ? ? ->.
    2,4: ssprove_sync=> km;
      ssprove_sync;
      first by move=> ? ? ->.
    all: ssprove_rem_rel 0%N => Hinv.
    all: apply: r_put_vs_put.
    all: apply: r_put_vs_put.
    all: ssprove_restore_mem;
      last by apply: r_ret.
    all: ssprove_invariant.
    all: by rewrite Hinv.
  - case: m => [c t].
    apply: r_get_remember_lhs => S.
    destruct ((c, t) \in domm S) eqn:Heq.
    all: rewrite Heq.
    1: by apply: r_ret => ? ? [].
    apply: r_get_remember_lhs => T.
    ssprove_rem_rel 0%N => Hinv.
    rewrite -Hinv Heq /=.
    by apply: r_ret => ? ? [] [].
Qed.
```

### child `CCA_EVAL_HYB_equiv_false`: [`theories/Crypt/examples/MACCCA.v` lines 360-402](https://github.com/SSProve/ssprove/blob/9a37fe0ab79d041f8d835e6cf18e37614b16a791/theories/Crypt/examples/MACCCA.v#L360-L402) ([local copy](code/theories/Crypt/examples/MACCCA.v))

```coq
Lemma CCA_EVAL_HYB_equiv_false:
  CCA_EVAL_HYB_pkg ∘ CPA_EVAL false ≈₀ CCA_EVAL_TAG_pkg_ff ∘ TAG false.
Proof.
  apply eq_rel_perf_ind with (
    (fun '(h0, h1) => h0 = h1) ⋊
    couple_rhs S_loc T_loc
      (fun S T => S = T)
  ).
  1: ssprove_invariant=> //=.
  simplify_eq_rel m.
  all: simplify_linking.
  all: ssprove_code_simpl.
  all: ssprove_code_simpl.
  - case: m => [ml mr].
    apply: r_get_vs_get_remember => S.
    ssprove_sync=> [|[ke|]];
      first by move=> ? ? ->.
    2: ssprove_sync=> ke;
      ssprove_sync;
      first by move=> ? ? ->.
    all: apply: r_get_vs_get_remember => T.
    all: ssprove_sync=> [|[km|]];
      first by move=> ? ? ->.
    2,4: ssprove_sync=> km;
      ssprove_sync;
      first by move=> ? ? ->.
    all: ssprove_rem_rel 0%N => Hinv.
    all: apply: r_put_vs_put.
    all: apply: r_put_vs_put.
    all: ssprove_restore_mem;
      last by apply: r_ret.
    all: ssprove_invariant.
    all: by rewrite Hinv.
  - case: m => [c t].
    apply: r_get_remember_rhs => S.
    destruct ((c, t) \in domm S) eqn:Heq.
    all: rewrite Heq.
    1: by apply: r_ret => ? ? [].
    apply: r_get_remember_rhs => T.
    ssprove_rem_rel 0%N => Hinv.
    rewrite -Hinv Heq /=.
    by apply: r_ret => ? ? [] [].
Qed.
```

### child `CCA_EVAL_equiv_false`: [`theories/Crypt/examples/MACCCA.v` lines 404-415](https://github.com/SSProve/ssprove/blob/9a37fe0ab79d041f8d835e6cf18e37614b16a791/theories/Crypt/examples/MACCCA.v#L404-L415) ([local copy](code/theories/Crypt/examples/MACCCA.v))

```coq
Lemma CCA_EVAL_equiv_false:
  CCA_EVAL_TAG_pkg_ff ∘ TAG true ≈₀ CCA_EVAL false.
Proof.
  apply: eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  all: apply rpost_weaken_rule with eq;
    last by move=> [? ?] [? ?] [].
  all: simplify_linking.
  all: ssprove_code_simpl.
  all: ssprove_code_simpl.
  all: by apply: rreflexivity_rule.
Qed.
```

The glue is the parent's proof (lines 450-470). It first rewrites the goal
into advantage form (`rewrite Advantage_E Advantage_sym`) and runs
`ssprove triangle`, which produces the hybrid bound `ineq` over the six
intermediate packages listed in the triangle (lines 453-459). Then four
`rewrite ->` steps, one per hop lemma, replace each adjacent pair by its
equivalent package, so the six terms collapse to the three epsilon terms.
The final `rewrite /mac_epsilon /cpa_epsilon !Advantage_E -!Advantage_link`
and `Advantage_sym` discharge the definitional equalities.

The four children are the hops, and each is cited by name in the glue
(`rewrite -> CCA_EVAL_* by ssprove_valid`, lines 463-466):

- `CCA_EVAL_equiv_true` (303-314): `CCA_EVAL true ≈₀ CCA_EVAL_TAG_pkg_tt ∘
  TAG true` — the first hop, replacing the real CCA package by the
  tagged composition.
- `CCA_EVAL_HYB_equiv_true` (316-358): `CCA_EVAL_TAG_pkg_tt ∘ TAG false ≈₀
  CCA_EVAL_HYB_pkg ∘ CPA_EVAL true` — the CPA hop, swapping the MAC for the
  CPA oracle.
- `CCA_EVAL_HYB_equiv_false` (360-402): `CCA_EVAL_HYB_pkg ∘ CPA_EVAL false ≈₀
  CCA_EVAL_TAG_pkg_ff ∘ TAG false` — the mirror CPA hop.
- `CCA_EVAL_equiv_false` (404-415): `CCA_EVAL_TAG_pkg_ff ∘ TAG true ≈₀
  CCA_EVAL false` — the last hop back to the real CCA package with the
  swapped message.

Why each is a good leaf. The two reflexive hops (`CCA_EVAL_equiv_true`,
`CCA_EVAL_equiv_false`) close by `apply: eq_rel_perf_ind_eq`, then
`simplify_eq_rel m`, two `ssprove_code_simpl` unfoldings, and
`all: by apply: rreflexivity_rule`: after unfolding, the two packages are the
same program, so reflexivity discharges every goal — self-contained, 12 lines
each. The two hybrid hops (`CCA_EVAL_HYB_equiv_true`,
`CCA_EVAL_HYB_equiv_false`) are the only ones that need an invariant. Each
closes by `apply eq_rel_perf_ind` with the invariant that the two memory
locations `S_loc`/`T_loc` stay equal, then a `case: m` on the message,
stepping through `r_get_vs_get_remember` / `r_put_vs_put` / `r_ret` and
rewriting by the invariant `Hinv` — self-contained, 43 lines each, and neither
cites another project lemma.

The lemma graph (which lemma uses which):

```text
security_based_on_mac (434-470)          -- the glue
  ├─ ssprove triangle → advantage sum over six packages
  ├─ CCA_EVAL_equiv_true        (303-314, leaf)
  ├─ CCA_EVAL_HYB_equiv_true    (316-358, leaf)
  ├─ CCA_EVAL_HYB_equiv_false   (360-402, leaf)
  └─ CCA_EVAL_equiv_false       (404-415, leaf)
```

No child cites another, so the longest chain of project lemmas below the main
theorem is 1.

## Why it is good

1. The main theorem `security_based_on_mac` is declared in
   `theories/Crypt/examples/MACCCA.v`, in lines 434-470 (check,
   `declared`; [permalink](https://github.com/SSProve/ssprove/blob/9a37fe0ab79d041f8d835e6cf18e37614b16a791/theories/Crypt/examples/MACCCA.v#L434-L470)).
2. The parent's proof cites the child `CCA_EVAL_equiv_true` by name at
   line 463 (`rewrite -> CCA_EVAL_equiv_true by ssprove_valid`), and likewise
   cites the other three hops at lines 464-466 (check, `cites`).
3. No `admit`, `Admitted` or `Axiom` closes any goal in the whole
   decomposition: none in lines 303-470 of `MACCCA.v` (check, `no_sorry`).
4. The decomposition has 4 direct lemmas, depth 1 below the main theorem,
   37 glue lines and child proof lines [12, 43, 43, 12] (measurement; the
   shape field records the same numbers).
5. The authors state the plan in the file header: "It shows an alternate way
   to gain CCA security, by augmenting a CPA-secure encryption scheme with a
   MAC", and "The advantage is at most a sum of the MAC and CPA epsilons,
   which are negligible by assumption, hence the scheme is secure"
   (author-statement; [lines 1-11](https://github.com/SSProve/ssprove/blob/9a37fe0ab79d041f8d835e6cf18e37614b16a791/theories/Crypt/examples/MACCCA.v#L1-L11)).

In my opinion the detail worth copying is that the six packages of the hybrid
argument split into two kinds of leaf: two of the four hops close by
reflexivity after unfolding, and only the two CPA hops
(`CCA_EVAL_HYB_equiv_true`, `CCA_EVAL_HYB_equiv_false`) need a real
invariant. The `ssprove triangle` tactic carries all of the transitivity,
so the glue is nothing but the triangle plus one rewrite per hop.

## When to use it, and when not

Use it when a cryptographic advantage is bounded by a hybrid argument: you can
list a chain of intermediate games (packages) whose adjacent pairs are
equivalent by reflexivity after unfolding or by a small memory invariant, and
whose boundary terms are definitionally the sub-advantages (`mac_epsilon`,
`cpa_epsilon`). The triangle tactic provides the transitivity, so the proof is
a flat list of hops rather than a nested `le_trans` chain.

Avoid it when a hop needs a non-trivial reduction or an event-based
(bad-event) bound rather than an exact `≈₀` equivalence — that hop is a
separate child that changes a summand, not a rewrite; when the intermediate
packages are not definitionally equal to the advantage terms, so the closing
`rewrite /mac_epsilon /cpa_epsilon` will not fire; or when a hop is not
between adjacent terms of the triangle list, so the rewrites and the list do
not line up.

## Consequences

The move creates one obligation per hop: each hop lemma must be an exact `≈₀`
equivalence between the adjacent packages named by the triangle. The
triangle's package list, the four rewrites, and the `mac_epsilon`/`cpa_epsilon`
definitions must all agree exactly, or a `rewrite` fails. The two reflexive
hops depend on both `ssprove_code_simpl` passes unfolding the two sides to the
same program; dropping one leaves a non-reflexive residual that
`rreflexivity_rule` cannot close. The two hybrid hops each carry their own
invariant (`couple_lhs`/`couple_rhs` on `S_loc`/`T_loc`), and getting the
invariant or its side wrong breaks the `r_get`/`r_put` bookkeeping. A hop
lemma stated over the wrong `b` flag or composition order leaves a residual
term that no later rewrite removes.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/opam-build.yml runs 'opam exec -- make' on push/PR to branch main; make compiles the files of _RocqProject, which lists theories/Crypt/examples/MACCCA.v at line 116; commit 9a37fe0ab79d041f8d835e6cf18e37614b16a791 is on the default branch main | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: CCA_EVAL_equiv_true@theories/Crypt/examples/MACCCA.v:463, CCA_EVAL_HYB_equiv_true@theories/Crypt/examples/MACCCA.v:464, CCA_EVAL_HYB_equiv_false@theories/Crypt/examples/MACCCA.v:465, CCA_EVAL_equiv_false@theories/Crypt/examples/MACCCA.v:466; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 9a37fe0ab79d041f8d835e6cf18e37614b16a791 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(security_based_on_mac, theories/Crypt/examples/MACCCA.v, 434-470) -> declared: security_based_on_mac is declared at theories/Crypt/examples/MACCCA.v:434 | check_claims.py |
| 2 | verified | cites(parent, CCA_EVAL_equiv_true) -> cites: CCA_EVAL_equiv_true occurs at theories/Crypt/examples/MACCCA.v:463 | check_claims.py |
| 3 | verified | no_sorry(theories/Crypt/examples/MACCCA.v, 303-470) -> no_sorry: none of admit, Admitted, Axiom, axiom in theories/Crypt/examples/MACCCA.v:303-470 | check_claims.py |
| 4 | verified | Checked code/MACCCA.v: the four hop rewrites (rewrite -> CCA_EVAL_equiv_true / CCA_EVAL_HYB_equiv_true / CCA_EVAL_HYB_equiv_false / CCA_EVAL_equiv_false by ssprove_valid) are at lines 463-466 = 4 direct lemmas; parent site 434-470 = 37 glue lines; child sites 303-314 (12), 316-358 (43), 360-402 (43), 404-415 (12); each child proof uses only ssprove library tactics and cites no further project lemma, so depth 1 | verifier |
| 5 | verified | Checked code/MACCCA.v lines 1-11: header comment reads verbatim 'It shows an alternate way to gain CCA security, by augmenting a CPA-secure encryption scheme with a MAC.' (line 6) and 'The advantage is at most a sum of the MAC and CPA epsilons, which are negligible by assumption, hence the scheme is secure.' (lines 9-10) | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Verified against the local copy code/theories/Crypt/examples/MACCCA.v: parent security_based_on_mac is exactly lines 434-470 (Qed. at 470); the four children are declared at 303-314, 316-358, 360-402, 404-415 with statements matching entry.json verbatim; the glue cites all four by name (rewrite -> CCA_EVAL_equiv_true/HYB_equiv_true/HYB_equiv_false/equiv_false by ssprove_valid) and no other project lemma, so children are exactly the lemmas used; closing methods match (reflexive hops close by eq_rel_perf_ind_eq + rreflexivity_rule, hybrid hops by eq_rel_perf_ind with couple_lhs/couple_rhs invariant + r_get/r_put + rewrite Hinv); all proofs end in Qed. with no admit/Admitted/Axiom in 303-470, so it closes. Shape numbers are right: direct_lemmas=4, depth=1, glue_lines=37 (parent site 434-470), child_lines=[12,43,43,12], all matching fields.md's definition and validate_entry's recomputation. | reviewer-correctness |
| generality | accept | Leaf-quality summary fixed and now matches the copied code: 'two of the four hops close by reflexivity after unfolding, and only the two CPA hops (CCA_EVAL_HYB_equiv_true, CCA_EVAL_HYB_equiv_false) need a real invariant' — confirmed by grep of the local copy: equiv_true/equiv_false use eq_rel_perf_ind_eq + rreflexivity_rule (2 reflexive), HYB_equiv_true/false use eq_rel_perf_ind with couple_lhs/couple_rhs (2 invariant). The 'Why each is a good leaf' prose agrees (two reflexive 12-line, two hybrid 43-line, self-contained, depth 1, no cross-citation). Move is abstracted beyond the example via also_known_as (hybrid argument, game hopping, triangle inequality over advantages) and use_when's 'ssprove triangle (or the equivalent triangle inequality) lists a chain of intermediate packages...'; avoid_when is honest and specific (bad-event/non-trivial reduction hops, non-definitional advantage terms, non-adjacent hops); consequences name concrete failure modes (exact ≈₀ per hop, rewrite/list/definitions must agree, ssprove_code_simpl needed, wrong b flag or composition order). Leaf-quality for a bounded prover is stated: each hop is one bounded ≈₀ program-equivalence proof, self-contained with no other project-lemma citation. | reviewer-generality |
| provenance-licence | accept | Provenance pass: check_provenance.py reports 1 file byte-identical at 9a37fe0ab79d041f8d835e6cf18e37614b16a791. All permalinks (files, 5 sites, 5 claim evidence URLs) use the same commit and the correct path theories/Crypt/examples/MACCCA.v; line ranges match the copied file (theorem at 434-470, four lemmas at 303-314/316-358/360-402/404-415, header comment at 1-11). Licence recorded MIT in entry.json, README, source.json and SOURCE.md, and sources/ssprove/upstream-LICENSE is the MIT text (Copyright 2021 SSProve) matching source.json licence_files [LICENSE]. Local copy is 14016 bytes matching the entry's files[0].bytes. Everything traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/SSProve/ssprove at commit `9a37fe0ab79d041f8d835e6cf18e37614b16a791`, under `MIT`; see the [source note](../../sources/ssprove/SOURCE.md) for the licence text and attribution.
