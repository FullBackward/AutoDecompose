# Key invariant locks_correct for Verdi's LiveLockServ mutual exclusion

| | |
|---|---|
| Kind | instance |
| Move | key-invariant |
| Language | rocq |
| Status | verified |
| Source | [verdi](../../sources/verdi/SOURCE.md) at `7e1641b758d8` |
| Licence | `BSD-2-Clause` |

## Intent

The safety proof of Verdi's LiveLockServ system — "no two clients can think
they hold the lock at once" — is reduced to a single key invariant,
`locks_correct` (any client that believes it holds the lock is at the head of
the server's queue). The main theorem instantiates the project's generic
`decomposition_invariant` at that predicate, then converts the predicate to
the safety goal with `locks_correct_implies_mutex`, in 13 lines that never
unfold the network or the handlers.

## The decomposition

### parent `true_in_reachable_mutual_exclusion`: [`theories/Systems/LiveLockServ.v` lines 866-878](https://github.com/uwplse/verdi/blob/7e1641b758d8f0032aa7de63620bc115330e0a6b/theories/Systems/LiveLockServ.v#L866-L878) ([local copy](code/theories/Systems/LiveLockServ.v))

```coq
  Theorem true_in_reachable_mutual_exclusion :
    true_in_reachable step_async step_async_init (fun net => mutual_exclusion (nwState net)).
  Proof using.
    pose proof decomposition_invariant.
    find_apply_lem_hyp inductive_invariant_true_in_reachable.
    unfold true_in_reachable in *.
    intros.
    apply locks_correct_implies_mutex.
    match goal with
    | [ H : _ |- _ ] => apply H
    end.
    auto.
  Qed.
```

### child `decomposition_invariant`: [`theories/Core/StatePacketPacketDecomposition.v` lines 172-207](https://github.com/uwplse/verdi/blob/7e1641b758d8f0032aa7de63620bc115330e0a6b/theories/Core/StatePacketPacketDecomposition.v#L172-L207) ([local copy](code/theories/Core/StatePacketPacketDecomposition.v))

```coq
  Theorem decomposition_invariant :
    inductive_invariant step_async step_async_init composed_invariant.
  Proof using.
    unfold inductive_invariant. intuition.
    - unfold composed_invariant. simpl.
      intuition auto using state_invariant_init.
    - unfold inductive, composed_invariant. intros.
      match goal with H : step_async _ _ _ |- _ => invcs H end; intuition; simpl in *.
      + eauto using state_invariant_maintained_deliver.
      + find_apply_lem_hyp post_net_analyze_sent_packet.
        intuition
          eauto 10 using
              network_invariant_maintained_deliver_new,
              network_invariant_maintained_deliver_old,
              nw_nw_distinct_pairs_and_elim,
              network_network_invariant_sym.
      + apply distinct_pairs_and_app;
        eauto using network_network_invariant_maintained_deliver_new, distinct_pairs_and_app_cons.

        intros. do_in_map. subst.
        eapply network_network_invariant_maintained_deliver_old;
          eauto using nw_nw_distinct_pairs_and_elim.
        simpl; now rewrite <- surjective_pairing.
      + eauto using state_invariant_maintained_input.
      + find_apply_lem_hyp post_input_analyze_sent_packet.
        intuition
          eauto using network_invariant_maintained_input_new,
                      network_invariant_maintained_input_old.
      + apply distinct_pairs_and_app;
            eauto using network_network_invariant_maintained_input_new.
        intros.
        do_in_map. subst.
        apply network_network_invariant_sym.
        eapply network_network_invariant_maintained_input_old; eauto.
        simpl. now rewrite <- surjective_pairing.
  Qed.
```

### child `locks_correct_implies_mutex`: [`theories/Systems/LiveLockServ.v` lines 190-201](https://github.com/uwplse/verdi/blob/7e1641b758d8f0032aa7de63620bc115330e0a6b/theories/Systems/LiveLockServ.v#L190-L201) ([local copy](code/theories/Systems/LiveLockServ.v))

```coq
  Lemma locks_correct_implies_mutex :
    forall sigma,
      locks_correct sigma ->
      mutual_exclusion sigma.
  Proof using.
    unfold locks_correct, mutual_exclusion.
    intros.
    repeat find_apply_hyp_hyp.
    break_exists.
    find_rewrite. find_inversion.
    auto.
  Qed.
```

How the parts fit. The lemma graph, in text:

```
true_in_reachable_mutual_exclusion (parent)
├── decomposition_invariant (child)                     ── the key invariant holds
│     └── state_invariant_init → locks_correct_init      (LiveLockServ.v:241-245)
│         and the other Decomposition fields             (LiveLockServ.v:838-864)
└── locks_correct_implies_mutex (child, a leaf)          ── the invariant implies the goal
```

The parent's 13 lines do four things, each a delegation rather than a step of
network reasoning. Line 869 `pose proof decomposition_invariant` gets the fact
that the *composed invariant* — state, per-packet and packet-pair invariants,
with `state_invariant` instantiated to `locks_correct` — is inductive. Line 870
`find_apply_lem_hyp inductive_invariant_true_in_reachable` (Core/Net.v:174-183)
turns that into `true_in_reachable step_async step_async_init composed_invariant`,
so that any reachable state carries the invariant. After unfolding and
introducing a reachable state, line 873 `apply locks_correct_implies_mutex`
changes the goal to `locks_correct (nwState st)`, which the `composed_invariant`
hypothesis supplies in its first conjunct (the `match goal with [H : _ |- _] =>
apply H end. auto.` at lines 874-877). No handler, packet or queue is unfolded
anywhere in the glue.

Why each child is a good leaf:

- `decomposition_invariant` is a self-contained, project-level statement
  ("the composed invariant is inductive") whose proof closes from named
  siblings — the `Decomposition` typeclass fields, which `eauto` discharges,
  plus four helper lemmas in the same file (`post_net_analyze_sent_packet`,
  `post_input_analyze_sent_packet`, `nw_nw_distinct_pairs_and_elim`,
  `distinct_pairs_and_app(_cons)`). It never mentions `locks_correct`, so it is
  reusable by every system that builds a `Decomposition` instance.
- `locks_correct_implies_mutex` closes on its own — `unfold`, `intros`,
  `repeat find_apply_hyp_hyp`, `break_exists`, `find_rewrite`,
  `find_inversion`, `auto` — with no named lemma. It is the only place the
  syntactic invariant is converted to the safety property.

## Why it is good

1. The parent site (the glue) is 13 lines long (`check`, lines 866-878).
2. `decomposition_invariant` is declared in the copied file
   `theories/Core/StatePacketPacketDecomposition.v` (`check`, lines 172-207).
3. `locks_correct_implies_mutex` is declared in the copied file
   `theories/Systems/LiveLockServ.v` (`check`, lines 190-201).
4. The parent site contains no `admit`, `Admitted`, `sorry` or `axiom`
   (`check`, lines 866-878).
5. The decomposition is thin glue over two children: the parent is 13 lines and
   the two children 36 and 12 lines, declaration-inclusive, with the longest
   chain below the main theorem being two lemmas (`measurement`, the three site
   ranges; the chain is `decomposition_invariant` → `state_invariant_init` →
   `locks_correct_init` at StatePacketPacketDecomposition.v:176-177,
   LiveLockServ.v:844 and LiveLockServ.v:241-245).

The reuse that makes this a key invariant, stated here rather than as a claim:
the single `decomposition_invariant` instantiation is reused by three other
theorems in the same file — `decomposition_reachable_nw_invariant` (964-976),
`locks_correct_locked_invariant` (998-1008) and `locks_correct_invariant`
(1010-1019) — each doing the same `pose proof decomposition_invariant;
find_apply_lem_hyp inductive_invariant_true_in_reachable` preamble, so one
invariant serves every reachability property of the system.

## When to use it, and when not

Use the key-invariant move when a `true_in_reachable step init P` (or
`reachable step init st -> P st`) safety property follows from a single state
predicate that is inductive — closed under every input and network handler —
and that implies the property, and when the project already provides a generic
invariant framework (Verdi's `Decomposition` typeclass here) to instantiate at
that predicate. The payoff is that the main proof stays a short delegation:
instantiate the framework at the invariant, then convert the invariant to the
goal.

Do not use it when no single state predicate is both inductive and strong
enough (the invariant may have to mention in-flight packets, or be split into
state / network / network-network parts as `composed_invariant` is); or when
the invariant's own inductiveness is the hard theorem rather than a framework's
routine check, because then the thin glue is hiding the real work and the entry
misleads about where the effort goes.

## Consequences

The move commits to one invariant that must both be inductive and imply the
goal. Inductiveness is delegated to the generic `Decomposition` framework, but
that framework still needs one proof per handler — the fields of the
`LockServ_Decompositition` instance (LiveLockServ.v:838-864); a new or changed
handler needs a new field proof, so the invariant's cost is paid once per
transition case, not in the main theorem. The glue also relies on the generic
reachability lemma `inductive_invariant_true_in_reachable` (Core/Net.v:174-183)
to turn `inductive_invariant` into `true_in_reachable`, and on the syntactic
conversion `locks_correct_implies_mutex`. If the invariant is too weak to imply
the goal, the conversion step fails; if it is too strong to be inductive, a
field proof fails; either way the invariant itself must be corrected.

## Verification

<!-- verification:start -->
Status: **verified**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/docker-action.yml (Docker CI) triggers on push to master (default branch) and pull_request, and runs coq-community/docker-coq-action@v1 with opam_file 'coq-verdi.opam', which installs and builds the opam package (running make); the Makefile runs 'coq_makefile -f _CoqProject' and builds every file listed in _CoqProject, including theories/Systems/LiveLockServ.v (line 34) and theories/Core/StatePacketPacketDecomposition.v (line 17). Pinned commit 7e1641b758d8f0032aa7de63620bc115330e0a6b is the default-branch HEAD (source registered with ref HEAD, resolved via git ls-remote). | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: decomposition_invariant@theories/Systems/LiveLockServ.v:869, locks_correct_implies_mutex@theories/Systems/LiveLockServ.v:873; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 3 file(s) byte-identical at 7e1641b758d8f0032aa7de63620bc115330e0a6b | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(parent, 13) -> lines: site parent has 13 lines | check_claims.py |
| 2 | verified | declared(decomposition_invariant, theories/Core/StatePacketPacketDecomposition.v, 172-207) -> declared: decomposition_invariant is declared at theories/Core/StatePacketPacketDecomposition.v:172 | check_claims.py |
| 3 | verified | declared(locks_correct_implies_mutex, theories/Systems/LiveLockServ.v, 190-201) -> declared: locks_correct_implies_mutex is declared at theories/Systems/LiveLockServ.v:190 | check_claims.py |
| 4 | verified | no_sorry(theories/Systems/LiveLockServ.v, 866-878) -> no_sorry: none of admit, Admitted, Axiom, axiom in theories/Systems/LiveLockServ.v:866-878 | check_claims.py |
| 5 | verified | Counted from the copied code: parent site theories/Systems/LiveLockServ.v:866-878 is 13 lines (878-866+1); child decomposition_invariant theories/Core/StatePacketPacketDecomposition.v:172-207 is 36 lines; child locks_correct_implies_mutex theories/Systems/LiveLockServ.v:190-201 is 12 lines. Chain verified: StatePacketPacketDecomposition.v:176-177 (inside decomposition_invariant, line 172) discharges the init case with 'intuition auto using state_invariant_init'; LiveLockServ.v:844 is the state_invariant_init field of the LockServ_Decompositition instance (state_invariant := locks_correct at line 839), closed by 'auto using locks_correct_init'; locks_correct_init is declared at LiveLockServ.v:241-245. So the chain below the main theorem is decomposition_invariant -> state_invariant_init field -> locks_correct_init = two lemmas. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | object | Provenance pass (3 files byte-identical at 7e1641b7). Statements verbatim; closing methods match the code; parent (866-878) is 13 lines ending in Qed, no admit/Admitted/sorry/axiom; depth-2 chain decomposition_invariant->state_invariant_init->locks_correct_init (StatePacketPacketDecomposition.v:177, LiveLockServ.v:844, 241-245) checks out; glue_lines=13 and child_lines=[36,12] are right. Objection: shape.direct_lemmas=2 is wrong. The main proof directly uses THREE named Verdi lemmas: decomposition_invariant (LiveLockServ.v:869), inductive_invariant_true_in_reachable (Core/Net.v:174-183, applied at LiveLockServ.v:870), and locks_correct_implies_mutex (LiveLockServ.v:873). The entry lists only two children and counts direct_lemmas=2, so the children are not exactly the lemmas the main proof uses and the shape number undercounts by one. Fix: either add inductive_invariant_true_in_reachable as a third child (with its statement and closed_by) or otherwise account for it, and set direct_lemmas=3. | reviewer-correctness |
| generality | accept | Generality lens: the move is stated beyond the example via applicability.goal_shape ('true_in_reachable step init P safety property') plus use_when/avoid_when, which abstract to 'any distributed system with a generic invariant framework to instantiate'. When-not-to-use is honest and specific: it flags the case where the invariant must mention in-flight packets / split into state/network/network-network parts, and where inductiveness is the hard theorem so thin glue hides the real work. Consequences are honest and code-verified: the Decomposition instance (LiveLockServ.v 838-864) still needs one field proof per handler, and a too-weak/too-strong invariant fails the conversion or a field proof. Leaf quality for a bounded prover is stated: decomposition_invariant closes by eauto over a finite named sibling set (typeclass fields + 4 helper lemmas) and never mentions locks_correct (reusable); locks_correct_implies_mutex closes on its own via unfold+auto with no named lemma and is the only conversion site. Verified cited ranges 190-201, 241-245, 838-864, 866-878, 964-976, 998-1008, 1010-1019, StatePacketPacketDecomposition.v 172-207, Net.v 174-183 all match the entry. | reviewer-generality |
| provenance-licence | accept | Provenance check passes (3 files byte-identical at 7e1641b758d8f0032aa7de63620bc115330e0a6b); commit pinned identically in source.json, SOURCE.md and entry.json; all permalinks use the full pinned commit; licence BSD-2-Clause consistent across entry.json, source.json, SOURCE.md, and upstream-LICENSE is genuine BSD-2-Clause text; code/ holds exactly the 3 files listed in entry.json. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/uwplse/verdi at commit `7e1641b758d8f0032aa7de63620bc115330e0a6b`, under `BSD-2-Clause`; see the [source note](../../sources/verdi/SOURCE.md) for the licence text and attribution.
