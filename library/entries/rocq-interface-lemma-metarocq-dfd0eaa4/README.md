# Interface lemmas expose PCUIC lift_typing to bidirectional-checker clients

| | |
|---|---|
| Kind | instance |
| Move | interface-lemma |
| Language | rocq |
| Status | accepted |
| Source | [metarocq](../../sources/metarocq/SOURCE.md) at `51b14e4bb5f4` |
| Licence | `MIT` |
| Licence recorded | 2026-11-14T15:37:44Z |

## Intent

Close the abstraction boundary between the bidirectional checker's
`checking`/`infering_sort` relations and PCUIC's `typing`/`lift_typing`: the
parent `lift_sorting_lift_typing` assembles four already-proved interface
lemmas into one theorem that turns any bidirectional sorting judgment into a
PCUIC `lift_typing` fact, so clients read off PCUIC facts without unfolding
the checker.

## The decomposition

### parent `lift_sorting_lift_typing`: [`pcuic/theories/Bidirectional/BDToPCUIC.v` lines 465-474](https://github.com/MetaRocq/metarocq/blob/51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56/pcuic/theories/Bidirectional/BDToPCUIC.v#L465-L474) ([local copy](code/pcuic/theories/Bidirectional/BDToPCUIC.v))

```coq
Theorem lift_sorting_lift_typing `{cf : checker_flags} (Σ : global_env_ext) Γ j (wfΣ : wf Σ) :
  wf_local Σ Γ -> lift_sorting (checking Σ Γ) (infering_sort Σ Γ) j -> lift_typing typing Σ Γ j.
Proof.
  intros wfΓ Hj.
  apply lift_sorting_it_impl with Hj.
  2: intros H; now apply infering_sort_typing, H.
  destruct j_term => //=.
  intros H; apply checking_typing; tas.
  now apply isTypebd_isType in Hj.
Qed.
```

### child `lift_sorting_it_impl`: [`common/theories/EnvironmentTyping.v` lines 540-550](https://github.com/MetaRocq/metarocq/blob/51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56/common/theories/EnvironmentTyping.v#L540-L550) ([local copy](code/common/theories/EnvironmentTyping.v))

```coq
  Lemma lift_sorting_it_impl {Pc Qc Ps Qs} {j} :
    forall tu: lift_sorting Pc Ps j,
    let s := tu.2.π1 in
    option_default (fun tm => Pc tm (j_typ j) -> Qc tm (j_typ j)) (j_term j) unit ->
    (Ps (j_typ j) s -> Qs (j_typ j) s) ->
    lift_sorting Qc Qs j.
  Proof.
    relativize (lift_sorting Qc Qs j).
    1: apply lift_sorting_f_it_impl with (f := id).
    destruct j, j_term => //.
  Qed.
```

### child `infering_sort_typing`: [`pcuic/theories/Bidirectional/BDToPCUIC.v` lines 427-433](https://github.com/MetaRocq/metarocq/blob/51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56/pcuic/theories/Bidirectional/BDToPCUIC.v#L427-L433) ([local copy](code/pcuic/theories/Bidirectional/BDToPCUIC.v))

```coq
Theorem infering_sort_typing `{checker_flags} (Σ : global_env_ext) Γ t u (wfΣ : wf Σ) :
  wf_local Σ Γ -> Σ ;;; Γ |- t ▹□ u -> Σ ;;; Γ |- t : tSort u.
Proof.
  intros wfΓ Ht. revert Ht wfΓ.
  apply bidirectional_to_pcuic.
  assumption.
Qed.
```

### child `checking_typing`: [`pcuic/theories/Bidirectional/BDToPCUIC.v` lines 419-425](https://github.com/MetaRocq/metarocq/blob/51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56/pcuic/theories/Bidirectional/BDToPCUIC.v#L419-L425) ([local copy](code/pcuic/theories/Bidirectional/BDToPCUIC.v))

```coq
Theorem checking_typing `{checker_flags} (Σ : global_env_ext) Γ t T (wfΣ : wf Σ) :
  wf_local Σ Γ -> isType Σ Γ T -> Σ ;;; Γ |- t ◃ T -> Σ ;;; Γ |- t : T.
Proof.
  intros wfΓ HT Ht. revert wfΓ HT.
  apply bidirectional_to_pcuic.
  all: assumption.
Qed.
```

### child `isTypebd_isType`: [`pcuic/theories/Bidirectional/BDToPCUIC.v` lines 458-463](https://github.com/MetaRocq/metarocq/blob/51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56/pcuic/theories/Bidirectional/BDToPCUIC.v#L458-L463) ([local copy](code/pcuic/theories/Bidirectional/BDToPCUIC.v))

```coq
Theorem isTypebd_isType `{checker_flags} (Σ : global_env_ext) Γ j (wfΣ : wf Σ) :
  wf_local Σ Γ -> lift_sorting (checking Σ Γ) (infering_sort Σ Γ) j -> isType Σ Γ (j_typ j).
Proof.
  intros wfΓ (_ & s & Hs & _).
  now eapply infering_sort_isType.
Qed.
```

How the parts fit. The parent's proof is a four-step composition of the
four children, one per line of the glue. It first applies the generic lifting
lemma `lift_sorting_it_impl` to `Hj`, which turns the goal
`lift_typing typing Σ Γ j` into two componentwise obligations: a sort side
`infering_sort ... -> typing_sort ...` (the `2:` branch, line 470) and a term
side `checking ... -> typing ...` (line 472). The sort side is discharged by
`infering_sort_typing`, and the term side by `checking_typing` — except that
`checking_typing` demands an `isType Σ Γ (j_typ j)` well-formedness premise,
which line 473 supplies from the same hypothesis by `isTypebd_isType`.

The lemma graph (which lemma the glue uses, and which each child uses):

```
lift_sorting_lift_typing
 ├─ lift_sorting_it_impl        (BDToPCUIC.v:469)  ── lift_sorting_f_it_impl (EnvironmentTyping.v:548)
 ├─ infering_sort_typing        (BDToPCUIC.v:470)  ── bidirectional_to_pcuic  (BDToPCUIC.v:431)
 ├─ checking_typing             (BDToPCUIC.v:472)  ── bidirectional_to_pcuic  (BDToPCUIC.v:423)
 └─ isTypebd_isType             (BDToPCUIC.v:473)  ── infering_sort_isType    (BDToPCUIC.v:462)
                                                      └─ infering_sort_typing (BDToPCUIC.v:440)
                                                         └─ bidirectional_to_pcuic
```

Why each child is a good leaf:

- `lift_sorting_it_impl` is fully generic over the four relations
  `Pc Qc Ps Qs` and mentions no checker-specifics; its proof closes on its own
  by relativising and applying its sibling `lift_sorting_f_it_impl`, then
  destructing the judgment. It is the single reusable lemma that carries the
  whole componentwise-lifting pattern.
- `infering_sort_typing` is a self-contained bidirectional-to-PCUIC
  implication for sort inference; its proof closes by applying the big
  mutual-induction theorem `bidirectional_to_pcuic` (BDToPCUIC.v:206) and one
  `assumption`.
- `checking_typing` is the same shape for term checking; it also closes by
  applying `bidirectional_to_pcuic`.
- `isTypebd_isType` is self-contained and closes by `eapply`ing its sibling
  `infering_sort_isType` from the same block.

The `bidirectional_to_pcuic` theorem they all bottom out in is itself a
`Theorem` proved by mutual induction (its comment at BDToPCUIC.v:205 reads
"The big theorem, proven by mutual induction using the custom induction
principle"); it is imported into this entry only as a name, not a site, since
the glue's content is the composition above it, not that induction. The
definitions `checking`/`infering_sort` live in the copied
[`BDTyping.v`](code/pcuic/theories/Bidirectional/BDTyping.v) (mutual inductive
at line 130), and `lift_sorting`/`lift_typing` in the copied
[`EnvironmentTyping.v`](code/common/theories/EnvironmentTyping.v) (lines 348,
361); the PCUIC `typing` and `isType` relations themselves come from
`PCUICTyping.v`, which is not copied.

## Why it is good

1. The parent closes without `admit`/`Admitted`/`Axiom`/`axiom` in its ten
   lines (BDToPCUIC.v 465-474); it ends in `Qed` (check claim 1).
2. The glue is a pure composition: its first step is the generic interface
   lemma `lift_sorting_it_impl` (line 469), which the parent site cites (check
   claim 2).
3. The shape is a thin skeleton: a 10-line parent (2 statement + 8 proof) over
   4 direct lemmas whose sites span 11, 7, 7 and 6 lines, with a checked lemma
   chain of depth 4 below the parent (measurement claim 3).
4. The authors label the block this theorem ends: "The user-facing theorems,
   directly following from the previous one" (BDToPCUIC.v line 409), i.e. these
   interface lemmas are the published surface of the checker, not internal
   plumbing (author-statement claim 4).

In my opinion the detail worth copying is that the parent never mentions the
internal structure of `checking`/`infering_sort`: it only names the four
already-proved lemmas and lets `lift_sorting_it_impl` state once, generically,
what "lift every component" means. That is what makes it a boundary rather
than a window into the checker.

## When to use it, and when not

Use it when a development defines its own algorithmic relation (here the
mutual inductive `checking`/`infering_sort`) and wants a one-shot bridge to
the semantic relation (`typing`/`lift_typing`), with the componentwise
implications already proved separately, so clients consume semantic facts
without unfolding the algorithmic definitions. The signature is a goal
`lift_typing typing ...` (or a component `|- t : T`, `isType ... t`) whose
hypotheses are the algorithmic judgments.

Avoid it when the bridge itself is the hard content — here that work lives in
`bidirectional_to_pcuic` (BDToPCUIC.v:206), proved by mutual induction, and
the glue merely composes it; when clients genuinely need the algorithmic
structure rather than the semantic conclusion; or when there is no single
generic lifting lemma like `lift_sorting_it_impl`, so each component would
need its own ad-hoc glue and the move stops being one lemma at a boundary.

## Consequences

The move creates the obligation to have the componentwise implications ready,
and to hide the extra premises they carry. `checking_typing` needs an
`isType Σ Γ (j_typ j)` premise; the parent hides it by deriving it from the
same bidirectional hypothesis with `isTypebd_isType`, but a client calling
`checking_typing` directly must supply that `isType` themselves. A failure mode
is applying `lift_sorting_it_impl` when the sort side `Ps -> Qs` is not
available for every sort, in which case the `2:` branch of the parent's
`apply` would not close.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml builds make ci-local (Makefile: all -> pcuic -> pcuic/theories/Bidirectional/BDToPCUIC.v); commit 51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56 is HEAD of default branch 9.1 | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: lift_sorting_it_impl@pcuic/theories/Bidirectional/BDToPCUIC.v:469, infering_sort_typing@pcuic/theories/Bidirectional/BDToPCUIC.v:470, checking_typing@pcuic/theories/Bidirectional/BDToPCUIC.v:472, isTypebd_isType@pcuic/theories/Bidirectional/BDToPCUIC.v:473; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 3 file(s) byte-identical at 51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | no_sorry(pcuic/theories/Bidirectional/BDToPCUIC.v, 465-474) -> no_sorry: none of admit, Admitted, Axiom, axiom in pcuic/theories/Bidirectional/BDToPCUIC.v:465-474 | check_claims.py |
| 2 | verified | cites(parent, lift_sorting_it_impl) -> cites: lift_sorting_it_impl occurs at pcuic/theories/Bidirectional/BDToPCUIC.v:469 | check_claims.py |
| 3 | verified | Parent BDToPCUIC.v 465-474 = 10 lines (2-line statement 465-466, 8-line Proof..Qed 467-474); glue cites 4 lemmas at 469 (lift_sorting_it_impl), 470 (infering_sort_typing), 472 (checking_typing), 473 (isTypebd_isType). Child spans: EnvironmentTyping.v 540-550=11, BDToPCUIC.v 427-433=7, 419-425=7, 458-463=6. Chain depth 4: isTypebd_isType(458) -> infering_sort_isType(435, 'eapply infering_sort_isType') -> infering_sort_typing(427, 'apply bidirectional_to_pcuic') -> bidirectional_to_pcuic(206). | verifier |
| 4 | verified | BDToPCUIC.v line 409 reads '(** The user-facing theorems, directly following from the previous one *)', immediately before Theorem infering_typing and the group that includes checking_typing, infering_sort_typing, infering_sort_isType, isTypebd_isType, lift_sorting_lift_typing. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent lift_sorting_lift_typing (BDToPCUIC.v 465-474, ends in Qed, no sorry/admit) applies exactly the four children and no other named lemmas: lift_sorting_it_impl (469), infering_sort_typing (470), checking_typing (472), isTypebd_isType (473). Each child site and closed_by match the code verbatim: lift_sorting_it_impl EnvironmentTyping.v 540-550 closed by lift_sorting_f_it_impl (548); infering_sort_typing 427-433 closed by bidirectional_to_pcuic (431); checking_typing 419-425 closed by bidirectional_to_pcuic (423); isTypebd_isType 458-463 closed by infering_sort_isType (462). Shape numbers correct: scale theorem, direct_lemmas 4, depth 4 via the verified chain isTypebd_isType->infering_sort_isType->infering_sort_typing->bidirectional_to_pcuic (462->440->431->206), glue_lines 10 (465-474), child_lines [11,7,7,6]. Provenance passes (3 files byte-identical). | reviewer-correctness |
| generality | accept | Generality stated beyond the example: use_when/avoid_when frame the move as 'algorithmic relation -> semantic relation' one-shot bridge with componentwise implications already proved, not MetaRocq-specific; goal_shape + also_known_as (abstraction-boundary/API/facade lemma) carry the abstract form. 'When not to use' is honest and specific: it names bidirectional_to_pcuic (BDToPCUIC.v:206, confirmed 'The big theorem, proven by mutual induction'), the thin-glue vs hard-bridge distinction, and the no-single-generic-lifting-lemma case. Consequences are honest and specific: checking_typing's isType premise (verified in its statement) is discharged by isTypebd_isType (line 473), and the failure mode of lift_sorting_it_impl's Ps->Qs side (the 2: branch, line 470) is real and matches the code. It does say what makes good leaves: each child is self-contained and closes by applying one named lemma (lift_sorting_f_it_impl, bidirectional_to_pcuic x2, infering_sort_isType), the property a bounded prover needs. All cited ranges (BDToPCUIC.v 409/411-417/419-425/427-433/458-463/465-474; EnvironmentTyping.v 348/361/540-550; BDTyping.v 130) verified against local copies. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are all consistent. check_provenance.py passes (3 files byte-identical at 51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56). Commit is identical across entry.json, README (abbrev 51b14e4bb5f4), sources/metarocq/SOURCE.md and source.json. Licence MIT is recorded in entry.json, README, SOURCE.md and source.json; upstream-LICENSE is copied and is the MIT text. Every permalink in entry.json (files and sites) points to the pinned commit with the correct path and line range; the cited line ranges were checked against the local copies (parent 465-474, children 540-550/427-433/419-425/458-463, author comment 409) and all match the verbatim excerpts. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/MetaRocq/metarocq at commit `51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56`, under `MIT`; see the [source note](../../sources/metarocq/SOURCE.md) for the licence text and attribution.
