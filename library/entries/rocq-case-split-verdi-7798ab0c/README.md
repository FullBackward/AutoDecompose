# Case split on step_async proves composed_invariant inductive

| | |
|---|---|
| Kind | instance |
| Move | case-split |
| Language | rocq |
| Status | accepted |
| Source | [verdi](../../sources/verdi/SOURCE.md) at `7e1641b758d8` |
| Licence | `BSD-2-Clause` |

## Intent

A proof of `inductive_invariant step_async step_async_init composed_invariant`
is reduced to an exhaustive split on the constructor of the `step_async`
relation. Each of the six resulting cases is closed from one `Decomposition`
class field (a hypothesis already supplied by the class) or one of five
same-file list lemmas, so no case needs its own argument.

## The decomposition

### parent `decomposition_invariant`: [`theories/Core/StatePacketPacketDecomposition.v` lines 172-207](https://github.com/uwplse/verdi/blob/7e1641b758d8f0032aa7de63620bc115330e0a6b/theories/Core/StatePacketPacketDecomposition.v#L172-L207) ([local copy](code/theories/Core/StatePacketPacketDecomposition.v))

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

### child `post_net_analyze_sent_packet`: [`theories/Core/StatePacketPacketDecomposition.v` lines 117-124](https://github.com/uwplse/verdi/blob/7e1641b758d8f0032aa7de63620bc115330e0a6b/theories/Core/StatePacketPacketDecomposition.v#L117-L124) ([local copy](code/theories/Core/StatePacketPacketDecomposition.v))

```coq
  Lemma post_net_analyze_sent_packet :
    forall h p ms xs ys,
      In p (map (fun m => mkPacket h (fst m) (snd m)) ms ++ xs ++ ys) ->
      (In (pDst p, pBody p) ms /\ h = pSrc p) \/ In p (xs ++ ys).
  Proof using.
    intros.
    in_crush. destruct x; simpl in *; eauto.
  Qed.
```

### child `post_input_analyze_sent_packet`: [`theories/Core/StatePacketPacketDecomposition.v` lines 126-133](https://github.com/uwplse/verdi/blob/7e1641b758d8f0032aa7de63620bc115330e0a6b/theories/Core/StatePacketPacketDecomposition.v#L126-L133) ([local copy](code/theories/Core/StatePacketPacketDecomposition.v))

```coq
  Lemma post_input_analyze_sent_packet :
    forall h p ms l,
      In p (map (fun m => mkPacket h (fst m) (snd m)) ms ++ l) ->
      (In (pDst p, pBody p) ms /\ h = pSrc p) \/ In p l.
  Proof using.
    intros.
    in_crush; destruct x; simpl in *; eauto.
  Qed.
```

### child `nw_nw_distinct_pairs_and_elim`: [`theories/Core/StatePacketPacketDecomposition.v` lines 137-146](https://github.com/uwplse/verdi/blob/7e1641b758d8f0032aa7de63620bc115330e0a6b/theories/Core/StatePacketPacketDecomposition.v#L137-L146) ([local copy](code/theories/Core/StatePacketPacketDecomposition.v))

```coq
  Lemma nw_nw_distinct_pairs_and_elim :
    forall xs a b ys l,
      l = xs ++ a :: ys ->
      In b (xs ++ ys) ->
      distinct_pairs_and network_network_invariant l ->
      network_network_invariant a b.
  Proof using.
    induction xs; intros; subst; simpl in *; intuition eauto; subst; eauto.
    apply network_network_invariant_sym. eauto.
  Qed.
```

### child `distinct_pairs_and_app_cons`: [`theories/Core/StatePacketPacketDecomposition.v` lines 148-155](https://github.com/uwplse/verdi/blob/7e1641b758d8f0032aa7de63620bc115330e0a6b/theories/Core/StatePacketPacketDecomposition.v#L148-L155) ([local copy](code/theories/Core/StatePacketPacketDecomposition.v))

```coq
  Lemma distinct_pairs_and_app_cons :
    forall A R xs p ys l,
      l = (xs ++ p :: ys) ->
      distinct_pairs_and (A:=A) R l ->
      distinct_pairs_and R (xs ++ ys).
  Proof using.
    induction xs; intros; subst; simpl in *; intuition eauto.
  Qed.
```

### child `distinct_pairs_and_app`: [`theories/Core/StatePacketPacketDecomposition.v` lines 157-170](https://github.com/uwplse/verdi/blob/7e1641b758d8f0032aa7de63620bc115330e0a6b/theories/Core/StatePacketPacketDecomposition.v#L157-L170) ([local copy](code/theories/Core/StatePacketPacketDecomposition.v))

```coq
  Lemma distinct_pairs_and_app :
    forall A R l1 l2,
      distinct_pairs_and (A := A) R l1 ->
      distinct_pairs_and R l2 ->
      (forall x y,
         In x l1 ->
         In y l2 ->
         R x y) ->
      distinct_pairs_and R (l1 ++ l2).
  Proof using.
    induction l1; intros; simpl in *; intuition.
    find_apply_lem_hyp in_app_or.
    intuition eauto.
  Qed.
```

### context `distinct_pairs_and`: [`theories/Core/StatePacketPacketDecomposition.v` lines 5-9](https://github.com/uwplse/verdi/blob/7e1641b758d8f0032aa7de63620bc115330e0a6b/theories/Core/StatePacketPacketDecomposition.v#L5-L9) ([local copy](code/theories/Core/StatePacketPacketDecomposition.v))

```coq
Fixpoint distinct_pairs_and {A} (R : A -> A -> Prop) (l : list A) : Prop :=
  match l with
    | [] => True
    | x :: xs => (forall y, In y xs -> R x y) /\ distinct_pairs_and R xs
  end.
```

### context `Decomposition`: [`theories/Core/StatePacketPacketDecomposition.v` lines 11-99](https://github.com/uwplse/verdi/blob/7e1641b758d8f0032aa7de63620bc115330e0a6b/theories/Core/StatePacketPacketDecomposition.v#L11-L99) ([local copy](code/theories/Core/StatePacketPacketDecomposition.v))

```coq
Class Decomposition (B : BaseParams) (M : MultiParams B) :=
  {
    state_invariant : (name -> data) -> Prop;
    network_invariant : (name -> data) -> packet -> Prop;
    network_network_invariant : packet -> packet -> Prop;

    network_network_invariant_sym :
      forall p1 p2,
        network_network_invariant p1 p2 ->
        network_network_invariant p2 p1 ;

    state_invariant_init : state_invariant init_handlers;

    state_invariant_maintained_input :
      forall h inp sigma st' out ps,
        input_handlers h inp (sigma h) = (out, st', ps) ->
        state_invariant sigma ->
        state_invariant (update name_eq_dec sigma h st');
    state_invariant_maintained_deliver :
      forall p sigma st' out ps,
        net_handlers (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (out, st', ps) ->
        state_invariant sigma ->
        network_invariant sigma p ->
        state_invariant (update name_eq_dec sigma (pDst p) st');

    network_invariant_maintained_input_old :
      forall h inp sigma st' out ps p,
        input_handlers h inp (sigma h) = (out, st', ps) ->
        state_invariant sigma ->
        network_invariant sigma p ->
        network_invariant (update name_eq_dec sigma h st') p;
    network_invariant_maintained_input_new :
      forall h inp sigma st' out ps p,
        input_handlers h inp (sigma h) = (out, st', ps) ->
        state_invariant sigma ->
        In (pDst p, pBody p) ps ->
        pSrc p = h ->
        network_invariant (update name_eq_dec sigma h st') p;

    network_invariant_maintained_deliver_old :
      forall sigma st' out ps p q,
        net_handlers (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (out, st', ps) ->
        state_invariant sigma ->
        network_invariant sigma p ->
        network_invariant sigma q ->
        network_network_invariant p q ->
        network_invariant (update name_eq_dec sigma (pDst p) st') q;
    network_invariant_maintained_deliver_new :
      forall sigma st' out ps p p',
        net_handlers (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (out, st', ps) ->
        state_invariant sigma ->
        network_invariant sigma p ->
        In (pDst p', pBody p') ps ->
        pSrc p' = pDst p ->
        network_invariant (update name_eq_dec sigma (pDst p) st') p';

    network_network_invariant_maintained_input_old :
      forall h inp sigma st' out ps p p',
        input_handlers h inp (sigma h) = (out, st', ps) ->
        state_invariant sigma ->
        network_invariant sigma p ->
        In (pDst p', pBody p') ps ->
        pSrc p' = h ->
        network_network_invariant p p';

    network_network_invariant_maintained_input_new :
      forall h inp sigma st' out ps,
        input_handlers h inp (sigma h) = (out, st', ps) ->
        state_invariant sigma ->
        distinct_pairs_and network_network_invariant (map (fun m => mkPacket h (fst m) (snd m)) ps);

    network_network_invariant_maintained_deliver_old :
      forall sigma st' out ps p p' q,
        net_handlers (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (out, st', ps) ->
        state_invariant sigma ->
        network_invariant sigma p ->
        network_invariant sigma q ->
        network_network_invariant p q ->
        In (pDst p', pBody p') ps ->
        pSrc p' = pDst p ->
        network_network_invariant p' q;

    network_network_invariant_maintained_deliver_new :
      forall sigma st' out ps p,
        net_handlers (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (out, st', ps) ->
        state_invariant sigma ->
        network_invariant sigma p ->
        distinct_pairs_and network_network_invariant (map (fun m => mkPacket (pDst p) (fst m) (snd m)) ps)
  }.
```

### context `composed_invariant`: [`theories/Core/StatePacketPacketDecomposition.v` lines 112-115](https://github.com/uwplse/verdi/blob/7e1641b758d8f0032aa7de63620bc115330e0a6b/theories/Core/StatePacketPacketDecomposition.v#L112-L115) ([local copy](code/theories/Core/StatePacketPacketDecomposition.v))

```coq
  Definition composed_invariant net :=
    (state_invariant (nwState net)) /\
    (forall p, In p (nwPackets net) -> network_invariant (nwState net) p) /\
    (distinct_pairs_and network_network_invariant (nwPackets net)).
```

How the parts fit. `decomposition_invariant` unfolds `inductive_invariant`
into two obligations. The init obligation is closed by the class field
`state_invariant_init` (the other two conjuncts of `composed_invariant` are
vacuous on the empty initial packet list). The step obligation unfolds
`inductive, composed_invariant`, introduces the step, then `invcs H` on
`step_async` splits into one goal per constructor, which `intuition` fans into
the three conjuncts of `composed_invariant`. The six cases and what closes
them:

```text
decomposition_invariant (172-207)
  ├─ init: composed_invariant (init state)
  │     └─ state_invariant_init                          [class field]
  └─ step: for each constructor of step_async, each conjunct of composed_invariant
        invcs H on step_async  →  6 cases (2 handlers × 3 conjuncts)
        1. deliver, state_invariant
             └─ state_invariant_maintained_deliver        [class field]
        2. deliver, network_invariant (carried packets)
             └─ post_net_analyze_sent_packet  +  nw_nw_distinct_pairs_and_elim
                + network_invariant_maintained_deliver_new/_old,
                  network_network_invariant_sym           [class fields]
        3. deliver, network_network_invariant
             └─ distinct_pairs_and_app  +  distinct_pairs_and_app_cons
                +  nw_nw_distinct_pairs_and_elim
                + network_network_invariant_maintained_deliver_new/_old  [class fields]
        4. input, state_invariant
             └─ state_invariant_maintained_input          [class field]
        5. input, network_invariant (carried packets)
             └─ post_input_analyze_sent_packet
                + network_invariant_maintained_input_new/_old  [class fields]
        6. input, network_network_invariant
             └─ distinct_pairs_and_app
                + network_network_invariant_maintained_input_new/_old,
                  network_network_invariant_sym           [class fields]
```

Each of the five children is a self-contained leaf about list membership or
the `distinct_pairs_and` predicate, and each closes on its own by a single
induction plus automation, never by citing another child:

- `post_net_analyze_sent_packet` and `post_input_analyze_sent_packet` decide,
  for a packet present in the post-state packet list, whether it is a
  newly-sent packet (extracting `In (pDst p, pBody p) ms` and `h = pSrc p`) or
  a carried-over one. Closed by `in_crush; destruct x; simpl in *; eauto`.
- `nw_nw_distinct_pairs_and_elim` recovers `network_network_invariant a b`
  from a `distinct_pairs_and network_network_invariant` list in which `a`
  precedes `b`. Closed by induction on `xs`, with the other direction handled
  by the class field `network_network_invariant_sym`.
- `distinct_pairs_and_app_cons` says removing one element from the middle of a
  `distinct_pairs_and` list preserves the predicate. Closed by induction on
  `xs` and `intuition eauto`.
- `distinct_pairs_and_app` composes `distinct_pairs_and R l1` and
  `distinct_pairs_and R l2` into `distinct_pairs_and R (l1 ++ l2)` given
  cross-pairwise `R`. Closed by induction on `l1` plus `in_app_or`.

Why each is a good leaf: none of the five mentions `step_async`, the network
semantics, or any other child, so the lemma tree below `decomposition_invariant`
is exactly depth 1 — the parent calls the leaves directly. The only facts the
leaves need beyond the standard library are the class fields of `Decomposition`
(`network_network_invariant_sym`), which are assumptions of the class, not
further lemmas.

## Why it is good

1. The file is compiled by the project's CI: `.github/workflows/docker-action.yml`
   runs docker-coq-action on `coq-verdi.opam` (`build: [make …]`), the `Makefile`
   generates `Makefile.coq` from `_CoqProject`, and `_CoqProject` line 17 lists
   `theories/Core/StatePacketPacketDecomposition.v` (`check`).
2. No `admit`, `Admitted`, `axiom` or `sorry` appears anywhere in the file, and
   the parent and all five children end in `Qed` (`check`, grep of the copied
   file).
3. The main proof is 34 lines (174-207) and, via `invcs H`, splits into 6 cases
   calling directly on 5 same-file lemmas; no lemma calls another, so the depth
   is 1 (`measurement`).
4. The author explains why `nw_nw_distinct_pairs_and_elim` is not generalised
   over the relation: "NB: generalizing this over R makes it useless to
   [eauto using] because the conclusion is too general" (comment, lines
   135-136) (`author-statement`).

In my opinion the detail worth copying is the division of labour: the split
(`invcs` + `intuition`) and the case facts (class fields + list lemmas) are
kept strictly apart. The glue never proves anything itself; it only routes each
of the six cases to a fact already stated above it. That is precisely the shape
an automated prover would want to emit — a skeleton of `eauto using` calls with
one hole per field/lemma.

## When to use it, and when not

Use this when the goal is `inductive_invariant step init I` for a step relation
with a small fixed set of constructors, and `I` is a conjunction of invariants
whose preservation under each constructor has already been stated as class
fields or small list lemmas. Then the split is the whole proof, and every case
closes by `eauto using`.

Avoid it when `I` is not a conjunction (so `intuition` cannot fan the goal
into the conjuncts), or when one constructor's case needs a genuinely new
argument not already packaged as a field or lemma. In that situation the real
content is a strengthened invariant or a key lemma, and the split by itself
will not close; forcing it produces a stuck `eauto` and a rewrite of the class
interface.

## Consequences

`invcs H` creates one goal per constructor of `step_async`, and `intuition`
further fans each into the three conjuncts of `composed_invariant`, so the case
count is constructors × conjuncts (here 6). Exhaustiveness is the whole
obligation: the split is sound only because `invcs` enumerates every
constructor of `step_async`; adding a constructor later breaks the `Qed`. The
glue carries no mathematics of its own — every `eauto using` names a class
field or one of the five lemmas — so it is brittle to reworded field statements
or to generalised lemmas (the comment at lines 135-136 warns of exactly this).

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/docker-action.yml: docker-coq-action builds coq-verdi.opam (opam_file at L31) whose build is 'make' (L19); Makefile.coq target (Makefile L8-L9) runs coq_makefile on _CoqProject, which lists theories/Core/StatePacketPacketDecomposition.v at line 17. Workflow triggers on push to master (default branch); pinned commit 7e1641b758d8f0032aa7de63620bc115330e0a6b. | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 7e1641b758d8f0032aa7de63620bc115330e0a6b | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Fetched at commit 7e1641b: _CoqProject L17 = 'theories/Core/StatePacketPacketDecomposition.v'; coq-verdi.opam L19 = 'build: [make "-j%{jobs}%"]'; .github/workflows/docker-action.yml L29-L32 = docker-coq-action with opam_file: 'coq-verdi.opam'; Makefile L8-L9 = 'Makefile.coq: _CoqProject' / 'coq_makefile -f _CoqProject'. | verifier |
| 2 | verified | grep -nE 'admit|Admitted|axiom|Axiom|sorry' over the copied file returned no matches; parent Theorem decomposition_invariant (172-207) and the 5 children (117-124, 126-133, 137-146, 148-155, 157-170) each end in 'Qed.' (packet_eq_dec ends in Defined, but it is not among parent+children). | verifier |
| 3 | verified | Counted in copied file: proof body 174-207 = 34 lines (Proof using. at 174, Qed. at 207). Line 179 has 'match goal with H : step_async _ _ _ |- _ => invcs H end; intuition; simpl in *'. Six '+' bullets at 180, 181, 188, 195, 196, 200. Proof cites the 5 same-file lemmas (post_net_analyze_sent_packet L181, nw_nw_distinct_pairs_and_elim L186/193, distinct_pairs_and_app_cons L189, distinct_pairs_and_app L188/200, post_input_analyze_sent_packet L196). None of the 5 lemmas' bodies cites another of the 5 (they use in_crush/in_app_or/network_network_invariant_sym only), so depth=1. | verifier |
| 4 | verified | Lines 135-136 of the copied file read: '(* NB: generalizing this over R makes it useless to [eauto using]' / 'because the conclusion is too general. *)', matching the quoted author statement above nw_nw_distinct_pairs_and_elim. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent statement matches code lines 172-173 verbatim. All 5 children (post_net_analyze_sent_packet 117-124, post_input_analyze_sent_packet 126-133, nw_nw_distinct_pairs_and_elim 137-146, distinct_pairs_and_app_cons 148-155, distinct_pairs_and_app 157-170) have statements and closed_by matching the copied code exactly, and each is cited directly by the parent proof (lines 181, 186/193, 188/200, 189, 196). The 5 children are exactly the lemmas the proof uses: the remaining proof citations are Decomposition class fields, and packet_eq_dec is unused. No admit/Admitted/axiom/sorry anywhere; parent and all 5 children end in Qed. invcs H is at line 179 and opens the 6 '+' bullets at 180/181/188/195/196/200. Shape numbers verified: direct_lemmas=5, depth=1 (no child cites another; network_network_invariant_sym and in_app_or are a class field and a stdlib lemma), glue_lines=34 (174-207), child_lines=[4,4,4,3,5] (Proof using through Qed inclusive for each child). Author comment quote at 135-136 verbatim. | reviewer-correctness |
| generality | accept | Generality passes. Move stated beyond the example: applicability.use_when and README 'When to use it' generalise to 'any inductive_invariant step init I with a small fixed constructor set and a conjunctive I whose per-constructor preservation is already packaged as class fields/small list lemmas, closed by invcs+intuition+eauto'. avoid_when names two concrete, honest failure modes (I not a conjunction so intuition cannot fan; a case needing a genuinely new argument, whose real content is a strengthened invariant/key lemma). Consequences are specific and honest (case count = constructors x conjuncts; adding a constructor breaks the Qed; glue is brittle to reworded/generalised lemmas, tied to the author's actual 135-136 comment). Good-leaves-for-a-bounded-prover is explicit: children mention no step_async/network semantics/each other, depth is exactly 1, each closes by one induction + automation, and depend only on class-field assumptions, described as the skeleton an automated prover wants to emit. | reviewer-generality |
| provenance-licence | accept | Commit 7e1641b758d8f0032aa7de63620bc115330e0a6b is identical in entry.json source.commit, sources/verdi/source.json, and SOURCE.md; check_provenance.py reports the copied file byte-identical at that commit, so the commit resolves and every permalink (correct commit + path theories/Core/StatePacketPacketDecomposition.v + line ranges) matches the copied file (verified parent 172-207, children 117-124/126-133/137-146/148-155/157-170, contexts 5-9/11-99/112-115, author comment 135-136). Licence BSD-2-Clause is consistent across entry.json, source.json, SOURCE.md, and the upstream-LICENSE copy, which matches the actual LICENSE at the pinned commit (Copyright 2014-2019 Verdi Team, two redistribution conditions, AS-IS disclaimer). Source note records the correct repo URL, commit, rocq language, licence and attribution. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/uwplse/verdi at commit `7e1641b758d8f0032aa7de63620bc115330e0a6b`, under `BSD-2-Clause`; see the [source note](../../sources/verdi/SOURCE.md) for the licence text and attribution.
