# Hybrid argument for HMAC-DRBG non-adaptive PRG via the adjacent-hybrids invariant

| | |
|---|---|
| Kind | instance |
| Move | key-invariant |
| Language | rocq |
| Status | draft |
| Source | [vst](../../sources/vst/SOURCE.md) at `c082fe210ec5` |
| Licence | `BSD-2-Clause` |

## Intent

Close the final theorem of the HMAC-DRBG non-adaptive PRG security proof —
the game distance `| Pr[G_real] - Pr[G_ideal] |` is at most `numCalls` times a
per-step bound — by three game-equivalence rewrites that put the distance into
hybrid form (`G_real == Gi_prg O`, `G_ideal == Gi_prg numCalls`), then one
instantiation of the generic hybrid argument `distance_le_prod_f` on the single
invariant `Gi_adjacent_hybrids_close`.

## The decomposition

### parent `G1_G2_close`: [`hmacdrbg/HMAC_DRBG_nonadaptive.v` lines 4548-4556](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/hmacdrbg/HMAC_DRBG_nonadaptive.v#L4548-L4556) ([local copy](code/hmacdrbg/HMAC_DRBG_nonadaptive.v))

```coq
Theorem G1_G2_close :
  | Pr[G_real] - Pr[G_ideal] | <= (numCalls / 1) * Gi_Gi_plus_1_bound.
Proof.
  rewrite Generate_move_v_update.
  rewrite G_real_is_first_hybrid.
  rewrite G_ideal_is_last_hybrid.
  specialize (hybrid_argument (fun i => Pr[Gi_prg i]) Gi_adjacent_hybrids_close numCalls).
  intuition.
Qed.
```

### child `Generate_move_v_update`: [`hmacdrbg/HMAC_DRBG_nonadaptive.v` lines 407-433](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/hmacdrbg/HMAC_DRBG_nonadaptive.v#L407-L433) ([local copy](code/hmacdrbg/HMAC_DRBG_nonadaptive.v))

```coq
Theorem Generate_move_v_update :
  Pr[G_real] == Pr[G1_prg].
Proof.
  rewrite Generate_v_split_close.
  unfold G_real_split, G1_prg.
  fcf_to_prhl_eq.
  fcf_skip.
  fcf_simp.
  remember b as k. remember b0 as v. clear Heqk Heqv.
  simpl.
  fcf_inline_first.
  fcf_simp.
  remember (to_list b1 ++ zeroes) as v1_pad.
  unfold requestList.

  destruct numCalls as [ | numCalls'].

  * inversion H_numCalls.
  * simpl.
    fcf_skip.
    instantiate (1 := (fun x y => fst x = fst y)).
    unfold oracleMap.

    - apply comp_spec_acc_2.

    - fcf_simp. simpl in *. subst. fcf_reflexivity.
Qed.
```

### child `G_real_is_first_hybrid`: [`hmacdrbg/HMAC_DRBG_nonadaptive.v` lines 578-612](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/hmacdrbg/HMAC_DRBG_nonadaptive.v#L578-L612) ([local copy](code/hmacdrbg/HMAC_DRBG_nonadaptive.v))

```coq
Lemma G_real_is_first_hybrid :
  Pr[G1_prg] == Pr[Gi_prg O].
Proof.
  rewrite G1_G1_acc_equal.
  fcf_to_prhl_eq.
  unfold G1_prg_fold.
  unfold Gi_prg.

  (* choose_Generate 0 is ~ Generate_noV, Generate_v, Generate_v, ...? *)
  unfold requestList.
  destruct numCalls.

  * inversion H_numCalls.

  * simpl.
    comp_skip.
    unfold oracleMap.
    simpl. (* break up latter oracleMap *)
    fs.
    fif.
    fs.
    (* maybe I can get the l out of the compFold? forgot how it works *)
    fcf_skip.
    instantiate (1 := (fun x y => x = (fst y, snd (snd y)))).
    (* simple generalize + induction *)
    apply compFold_Generate_v_choose_Generate.
    auto.

    simpl in H3.
    inversion H3.
    subst.
    destruct b3.
    simpl.
    fcf_reflexivity.
Qed.
```

### child `G_ideal_is_last_hybrid`: [`hmacdrbg/HMAC_DRBG_nonadaptive.v` lines 816-840](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/hmacdrbg/HMAC_DRBG_nonadaptive.v#L816-L840) ([local copy](code/hmacdrbg/HMAC_DRBG_nonadaptive.v))

```coq
Lemma G_ideal_is_last_hybrid :
  Pr[G_ideal] == Pr[Gi_prg numCalls].
Proof.
(*  Print G_ideal.*)
  rewrite G2_oracle_eq.
  rewrite G2_oracle_eq_v_sampling.
  fcf_to_prhl_eq.
  unfold G_ideal''.
  unfold Gi_prg.
  fcf_skip_eq. simplify.

  rename b into k. rename b0 into v.
  fcf_skip.
  instantiate (1 := (fun x y => fst x = fst y)).

  (* note: switching between windows is C-x o *)
  - unfold oracleMap.
    apply oracleMap_rb_eq.
    simpl.
    unfold requestList.
    apply length_replicate.

  - simpl in *. subst.
    simplify. fcf_reflexivity.
Qed.
```

### child `Gi_adjacent_hybrids_close`: [`hmacdrbg/HMAC_DRBG_nonadaptive.v` lines 4519-4541](https://github.com/PrincetonUniversity/VST/blob/c082fe210ec501219abe52b9d0f25541d7c97e59/hmacdrbg/HMAC_DRBG_nonadaptive.v#L4519-L4541) ([local copy](code/hmacdrbg/HMAC_DRBG_nonadaptive.v))

The declaration `Theorem Gi_adjacent_hybrids_close :` (line 4519) is followed by
an author comment on line 4520 before the `forall`; the excerpt below shows the
proposition and its proof (lines 4521-4541).

```coq
  forall (n : nat),
  | Pr[Gi_prg n] - Pr[Gi_prg (S n)] | <= Gi_Gi_plus_1_bound.
Proof.
  intros n.
  assert (n_dec : (n <= numCalls)%nat \/ (n > numCalls)%nat) by lia.
  destruct n_dec as [ n_lte | n_gt ].

  -  unfold Gi_Gi_plus_1_bound. intros.
     eapply ratDistance_le_trans. (* do the PRF advantage and collision bound separately *)
     rewrite Gi_prog_equiv_prf_oracle.    (* changed this *)
     apply Gi_replace_prf_with_rf_oracle; auto.        (* Basically already proven via PRF_Advantage magic *)
     apply Gi_replace_rf_with_rb_oracle.

  - rewrite Gi_adjacent_hybrids_close_outofbounds.
    assert (Heq : | Pr  [Gi_prg (S n) ] - Pr  [Gi_prg (S n) ] | == 0).
    { rewrite <- ratIdentityIndiscernables. reflexivity. }
    rewrite Heq.
    unfold Gi_Gi_plus_1_bound. unfold PRF_Advantage_Max. unfold Pr_collisions.
    apply rat0_le_all.
    auto.
Qed.
```

### How the parts fit

The parent is nine lines of glue. The three `rewrite` lines put the distance
into hybrid form, and the `specialize` line hands the result to the generic
hybrid argument. In order:

1. `rewrite Generate_move_v_update` (line 4551) replaces `G_real` by `G1_prg`
   — the child moves the `v`-update to the front of the game so that the PRF is
   queried exactly once per call.
2. `rewrite G_real_is_first_hybrid` (line 4552) replaces `G1_prg` by the first
   hybrid `Gi_prg O`.
3. `rewrite G_ideal_is_last_hybrid` (line 4553) replaces `G_ideal` by the last
   hybrid `Gi_prg numCalls`. After these three rewrites the goal is
   `| Pr[Gi_prg O] - Pr[Gi_prg numCalls] | <= numCalls * Gi_Gi_plus_1_bound`.
4. `specialize (hybrid_argument (fun i => Pr[Gi_prg i]) Gi_adjacent_hybrids_close
   numCalls)` (line 4554) instantiates `hybrid_argument`, which is the alias
   `Definition hybrid_argument := distance_le_prod_f` at line 4545, a library
   lemma from `FCF.OracleHybrid`. Given that adjacent hybrids are close
   (`Gi_adjacent_hybrids_close`), it telescopes the per-step bound into the
   end-to-end bound. `intuition` (line 4555) closes the remaining trivial goal.

Lemma graph (which child uses which):

```
G1_G2_close
├── Generate_move_v_update            G_real == G1_prg            (uses comp_spec_acc_2)
├── G_real_is_first_hybrid            G1_prg == Gi_prg O          (uses G1_G1_acc_equal,
│                                                                  compFold_Generate_v_choose_Generate)
├── G_ideal_is_last_hybrid            G_ideal == Gi_prg numCalls  (uses G2_oracle_eq,
│                                                                  G2_oracle_eq_v_sampling,
│                                                                  oracleMap_rb_eq)
└── Gi_adjacent_hybrids_close         | Gi_prg n − Gi_prg (S n) | ≤ Gi_Gi_plus_1_bound
     ├── Gi_prog_equiv_prf_oracle
     ├── Gi_replace_prf_with_rf_oracle ── Gi_replace_prf_with_rf_oracle_i, PRF_Advantage_max_exists
     ├── Gi_replace_rf_with_rb_oracle ── Gi_Pr_bad_event_collisions ── Gi_rb_bad_eq_2'
     └── Gi_adjacent_hybrids_close_outofbounds ── comp_same_after_numCalls
```

Each child is a good leaf: a self-contained statement whose proof closes on its
own (the three endpoint equivalences by the FCF program-equivalence tactics and
one or two same-file helpers; the invariant by a two-way case split on
`n <= numCalls`). The endpoint children are pure rewrites into the hybrid
family, so they carry no cryptographic content; all the work is the invariant
`Gi_adjacent_hybrids_close`, which is why the move is `key-invariant`: the glue
does nothing but name the invariant and let `distance_le_prod_f` do the
telescoping.

## Why it is good

1. The key invariant `Gi_adjacent_hybrids_close` occurs in the parent site
   `G1_G2_close` (a check, decided by `check_claims.py`).
2. The whole span covering the parent and all four children,
   `hmacdrbg/HMAC_DRBG_nonadaptive.v` lines 407-4556, contains no
   `admit`/`Admitted`/`Axiom`/`axiom` (a check, decided by `check_claims.py`).
   The file's only live `Admitted` is the abandoned backtracking-resistance
   variant `G1_G2_close_b2` at line 4652, outside this cone.
3. The shape: 4 direct lemmas, a 9-line glue (the parent site 4548-4556), child
   proofs of 27, 35, 25 and 23 lines (declaration through `Qed`), and a longest
   checked chain of 4 project lemmas below the main theorem
   (`G1_G2_close -> Gi_adjacent_hybrids_close -> Gi_replace_rf_with_rb_oracle ->
   Gi_Pr_bad_event_collisions -> Gi_rb_bad_eq_2'`).
4. The authors lay out the hybrid structure in a comment beside the game family:
   "number of calls: first call is 0, last call is (numCalls - 1) ... G0: PRF
   PRF PRF, G1: RB PRF PRF, G2: RB RB PRF, G3: RB RB RB; there should be
   (S numCalls) games, so games are numbered from 0 through numCalls"
   (lines 457-463).

In my opinion the detail worth copying is the *uniformity*: the theorem's proof
never names an index `i` — the three endpoints are one rewrite each and the
whole family is summed by one `specialize` of a library lemma. The theorem is
the skeleton AutoDecompose should produce, with the single hard hole
(`Gi_adjacent_hybrids_close`) left for one bounded prover.

## When to use it, and when not

Use it when a game/advantage inequality is between two objects that differ by a
parameter stepped one unit at a time through a family `Gi 0 ... Gi numCalls`,
the endpoints are genuine `==` (so `rewrite` applies, not a one-sided bound),
a uniform per-step bound holds for every adjacent pair, and a generic hybrid
lemma (`distance_le_prod_f` here) is available to telescope it.

Avoid it when the adjacent-hybrids bound is not uniform in the index (that
bound is the whole difficulty and must be one statement); when an endpoint only
gives a one-sided inequality so the three rewrites cannot put the distance into
hybrid form; or when a hybrid step needs an adversary that does not factor into
one uniform invariant.

## Consequences

The move concentrates all the difficulty into one invariant,
`Gi_adjacent_hybrids_close`, which must bound every adjacent pair uniformly; the
glue is then a wrapper. The three endpoint lemmas must each be a genuine `==`
so `rewrite` applies; if an endpoint only gives `<=` the telescope does not go
through. Failure mode: the per-step bound must be independent of `i` (a fixed
`Gi_Gi_plus_1_bound`); a non-uniform or endpoint-dependent bound forces the
proof back into an explicit induction over `i`, and the single `specialize`
step breaks.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: Generate_move_v_update@hmacdrbg/HMAC_DRBG_nonadaptive.v:4551, G_real_is_first_hybrid@hmacdrbg/HMAC_DRBG_nonadaptive.v:4552, G_ideal_is_last_hybrid@hmacdrbg/HMAC_DRBG_nonadaptive.v:4553, Gi_adjacent_hybrids_close@hmacdrbg/HMAC_DRBG_nonadaptive.v:4554; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(G1_G2_close, Gi_adjacent_hybrids_close) -> cites: Gi_adjacent_hybrids_close occurs at hmacdrbg/HMAC_DRBG_nonadaptive.v:4554 | check_claims.py |
| 2 | verified | no_sorry(hmacdrbg/HMAC_DRBG_nonadaptive.v, 407-4556) -> no_sorry: none of admit, Admitted, Axiom, axiom in hmacdrbg/HMAC_DRBG_nonadaptive.v:407-4556 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/PrincetonUniversity/VST at commit `c082fe210ec501219abe52b9d0f25541d7c97e59`, under `BSD-2-Clause`; see the [source note](../../sources/vst/SOURCE.md) for the licence text and attribution.
