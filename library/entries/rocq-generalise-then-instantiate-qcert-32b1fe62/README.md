# General annotated NNRC to DNNRC correctness specialised to the top translation

| | |
|---|---|
| Kind | instance |
| Move | generalise-then-instantiate |
| Language | rocq |
| Status | accepted |
| Source | [qcert](../../sources/qcert/SOURCE.md) at `e112de6d7fda` |
| Licence | `Apache-2.0` |

## Intent

The NNRC-to-DNNRC translation is proved correct once, over the general base
translation `nnrc_to_dnnrc_base` parameterised by the annotation `annot`, the
plug type `plug_type` and both environments (`ctenv`, `tenv`, `cdenv`,
`denv`). The top-level compiler theorem `nnrc_to_dnnrc_top_correct` then falls
out as a trivial specialisation of that general lemma: unfold the top-level
evaluators, fill in `annot = tt`, `plug_type = dataframe`, `ctenv = rec_sort
tenv`, `tenv = nil`, and apply the general lemma.

## The decomposition

### parent `nnrc_to_dnnrc_top_correct`: [`compiler/core/Translation/Lang/NNRCtoDNNRC.v` lines 532-557](https://github.com/querycert/qcert/blob/e112de6d7fda1b916244a1feb08bedd7f8a96bc1/compiler/core/Translation/Lang/NNRCtoDNNRC.v#L532-L557) ([local copy](code/compiler/core/Translation/Lang/NNRCtoDNNRC.v))

```coq
    Theorem nnrc_to_dnnrc_top_correct h (tenv:vdbindings) (q:nnrc) :
      forall cdenv:dbindings,
        wf_cdenv tenv cdenv ->
        nnrc_eval_top h q (unlocalize_constants cdenv) =
        dnnrc_eval_top h (nnrc_to_dnnrc_top tenv q) cdenv.
    Proof.
      unfold nnrc_to_dnnrc_top.
      unfold nnrc_eval_top.
      unfold nnrc_eval.
      unfold nnrc_to_dnnrc.
      unfold dnnrc_eval_top.
      intros.
      unfold lift_nnrc_core.
      assert (nil = unlocalize_constants nil) by reflexivity.
      rewrite H0.
      rewrite rec_sort_unlocalize_constants_comm.
      generalize (wf_cdenv_rec_sort tenv cdenv H); intros; clear H.
      apply (nnrc_to_dnnrc_base_correct_lift tt).
      assumption.
      unfold wf_denv.
      split; [reflexivity| ].
      intros.
      unfold wf_localization.
      simpl.
      trivial.
    Qed.
```

### child `nnrc_to_dnnrc_base_correct_lift`: [`compiler/core/Translation/Lang/NNRCtoDNNRC.v` lines 473-485](https://github.com/querycert/qcert/blob/e112de6d7fda1b916244a1feb08bedd7f8a96bc1/compiler/core/Translation/Lang/NNRCtoDNNRC.v#L473-L485) ([local copy](code/compiler/core/Translation/Lang/NNRCtoDNNRC.v))

```coq
  Lemma nnrc_to_dnnrc_base_correct_lift {A plug_type:Set} (annot:A) {plug:AlgPlug plug_type} h (ctenv tenv:list (var*dlocalization)) (n:nnrc) :
    forall cdenv denv:list (var*ddata),
      wf_cdenv ctenv cdenv ->
      wf_denv tenv denv ->
      nnrc_core_eval h (unlocalize_constants cdenv) (unlocalize_constants denv) n
      = lift unlocalize_data (dnnrc_base_eval h cdenv denv (nnrc_to_dnnrc_base annot ctenv tenv n)).
  Proof.
    intros.
    rewrite <- nnrc_to_dnnrc_base_correct; auto.
    unfold unlocalize_data.
    unfold lift; simpl.
    destruct (nnrc_core_eval h (unlocalize_constants cdenv) (unlocalize_constants denv)); auto.
  Qed.
```

### child `rec_sort_unlocalize_constants_comm`: [`compiler/core/Translation/Lang/NNRCtoDNNRC.v` lines 497-509](https://github.com/querycert/qcert/blob/e112de6d7fda1b916244a1feb08bedd7f8a96bc1/compiler/core/Translation/Lang/NNRCtoDNNRC.v#L497-L509) ([local copy](code/compiler/core/Translation/Lang/NNRCtoDNNRC.v))

```coq
    Lemma rec_sort_unlocalize_constants_comm l :
      (rec_sort (unlocalize_constants l) = (unlocalize_constants (rec_sort l))).
    Proof.
      unfold unlocalize_constants.
      rewrite map_rec_sort.
      reflexivity.
      intros.
      split.
      destruct x; simpl in *.
      auto.
      simpl.
      auto.
    Qed.
```

### child `wf_cdenv_rec_sort`: [`compiler/core/Translation/Lang/NNRCtoDNNRC.v` lines 511-530](https://github.com/querycert/qcert/blob/e112de6d7fda1b916244a1feb08bedd7f8a96bc1/compiler/core/Translation/Lang/NNRCtoDNNRC.v#L511-L530) ([local copy](code/compiler/core/Translation/Lang/NNRCtoDNNRC.v))

```coq
    Lemma wf_cdenv_rec_sort tenv cdenv :
      wf_cdenv tenv cdenv -> wf_cdenv (rec_sort tenv) (rec_sort cdenv).
    Proof.
      intros.
      unfold wf_cdenv in *.
      elim H; clear H; intros.
      split.
      - apply same_domain_rec_sort; assumption.
      - intros.
        specialize (H0 v).
        assert (assoc_lookupr ODT_eqdec (rec_sort tenv) v =
                assoc_lookupr equiv_dec (rec_sort tenv) v) by reflexivity.
        rewrite <- H1; clear H1.
        rewrite assoc_lookupr_drec_sort.
        assert (assoc_lookupr ODT_eqdec (rec_sort cdenv) v =
                assoc_lookupr equiv_dec (rec_sort cdenv) v) by reflexivity.
        rewrite <- H1; clear H1.
        rewrite assoc_lookupr_drec_sort.
        assumption.
    Qed.
```

### How the parts fit

The general lemma is `nnrc_to_dnnrc_base_correct_lift`: correctness of the
*base* translation `nnrc_to_dnnrc_base` over arbitrary `annot`, `plug_type`,
`ctenv`, `tenv`, `cdenv`, `denv` and `n`. The top theorem instantiates it by
unfolding `nnrc_to_dnnrc_top` (which fixes `annot = tt`, `plug_type =
dataframe`, `ctenv = rec_sort tenv`, `tenv = nil` through `nnrc_to_dnnrc`) and
by unfolding `nnrc_eval_top`/`nnrc_eval` and `dnnrc_eval_top` so that both
sides of the goal are the core evaluations the general lemma talks about.

The glue then discharges the general lemma's two side conditions and one
syntactic mismatch, each with its own small lemma:

```
nnrc_to_dnnrc_top_correct            (parent, 532-557)
├── nnrc_to_dnnrc_base_correct_lift   (473-485)   applied at 549  ← the general lemma
│     └── nnrc_to_dnnrc_base_correct  (357-471)   rewritten at 481  ← the 115-line induction, hidden behind one identifier
│           ├── nnrc_to_dnnrc_base_get_constant_correct  (306-354)  at 367
│           ├── lift_map_nnrc_to_dnnrc_base_correct      (238-275)  at 431
│           └── lookup_denv_local / lookup_denv_distr    (190 / 225) at 379, 385
├── rec_sort_unlocalize_constants_comm (497-509)  rewritten at 547  ← reconciles the top evaluator's rec_sort with the general lemma's unlocalized constants
└── wf_cdenv_rec_sort                 (511-530)  generalized at 548 ← turns wf_cdenv tenv cdenv into wf_cdenv (rec_sort tenv) (rec_sort cdenv)
```

Reading the glue line by line: `unfold nnrc_to_dnnrc_top / nnrc_eval_top /
nnrc_eval / nnrc_to_dnnrc / dnnrc_eval_top` reduces both sides of the goal to
`nnrc_core_eval` and `dnnrc_base_eval` on the base translation; the `assert
(nil = unlocalize_constants nil)` plus `rewrite H0` fixes the empty local
environment; `rewrite rec_sort_unlocalize_constants_comm` moves the
`rec_sort` on the left past `unlocalize_constants` so the left side matches
the general lemma's `unlocalize_constants (rec_sort cdenv)`; `generalize
(wf_cdenv_rec_sort tenv cdenv H)` supplies the general lemma's `wf_cdenv`
premise for the sorted environments; `apply
(nnrc_to_dnnrc_base_correct_lift tt)` is the instantiation; `assumption`
discharges the `wf_cdenv` premise; and the final six lines prove `wf_denv nil
(unlocalize_constants nil)` (the empty local environment), which is trivial.

Why each child is a good leaf:

- `nnrc_to_dnnrc_base_correct_lift` is a self-contained statement whose proof
  closes with one rewrite to `nnrc_to_dnnrc_base_correct` followed by `auto`
  and a `destruct` on the evaluation. Its job is to package the whole
  115-line induction (`nnrc_to_dnnrc_base_correct`, lines 357-471) behind a
  single identifier so the top theorem does not re-derive it.
- `rec_sort_unlocalize_constants_comm` is a self-contained commutation of two
  environment functions; it closes by the library lemma `map_rec_sort` and
  `reflexivity`.
- `wf_cdenv_rec_sort` is a self-contained well-formedness preservation; it
  closes by two library lemmas, `same_domain_rec_sort` and
  `assoc_lookupr_drec_sort`.

The glue cites all three directly (lines 549, 547, 548), so none of them is a
subgoal; each is a named lemma with its own declaration and proof.

## Why it is good

1. The general annotated, localisation-parameterised lemma
   `nnrc_to_dnnrc_base_correct_lift` is declared at `NNRCtoDNNRC.v:473-485`
   (check, `declared`).
2. The top theorem is exactly an instantiation of it: the glue applies
   `nnrc_to_dnnrc_base_correct_lift` at line 549 after fixing the parameters
   by unfolding (check, `cites`).
3. The parent and its three children close with no `admit`, `Admitted`,
   `Axiom` or `axiom` in lines 473-557 (check, `no_sorry`).
4. The move hides the real cost one level down: the checked chain of project
   lemmas below the main theorem is 3 deep — `nnrc_to_dnnrc_top_correct`
   applies `nnrc_to_dnnrc_base_correct_lift` (line 549), which rewrites by
   `nnrc_to_dnnrc_base_correct` (line 481), which rewrites by
   `nnrc_to_dnnrc_base_get_constant_correct` (line 367) (measurement).
5. The same generalise-then-instantiate pattern closes the NRAEnv-to-NNRC
   pass, where `nraenv_to_nnrc_top_correct` unfolds the top evaluators and
   applies the general `nraenv_sem_correct` (known-use).

In my opinion the detail worth copying is the pairing of *two* bridge lemmas
with the general lemma: the instantiation is not definitionally free, because
the top-level evaluator wraps the core evaluator with `rec_sort` and
`unlocalize_data`. The move is "generalise, then pay the small wrapping cost
with one commutation lemma per wrapper" — not "generalise and instantiate for
free".

## When to use it, and when not

Use it when a translation or evaluation is defined in a general, parameterised
form (an annotation type, a plug type, section variables) and the public
entry point only fixes those parameters and the environments. Then prove the
general lemma once and make the top theorem a specialisation.

Avoid it when the top entry point does more than fill parameters — when it
wraps the core with extra normalisation (`rec_sort`, `unlocalize_data`) the
general lemma does not share, each wrapper needs its own commutation lemma
before the instantiation applies. Also avoid it when the general lemma is not
yet proved: its proof (here the 115-line induction `nnrc_to_dnnrc_base_correct`)
is the real cost, and the top theorem's brevity is an illusion bought by
pushing work down, not by removing it. Finally, avoid it when the parameter
substitution is not definitional and needs a non-trivial rewrite between two
representations, because then the "instantiation" is itself a substantive
proof.

## Consequences

The move concentrates the proof burden in the general lemma; the top theorem
inherits it as an obligation (the `apply (nnrc_to_dnnrc_base_correct_lift
tt)` only fires once that lemma and its `wf_cdenv`/`wf_denv` premises exist).
The top-level wrappers create side obligations — `rec_sort` commutes with
`unlocalize_constants`, `wf_cdenv` survives `rec_sort`, the empty environment
is well-formed — that the general lemma cannot absorb. A known failure mode:
if a later pass adds a top-level wrapper the general lemma does not know
about, the instantiation silently stops applying and the proof must grow a new
commutation lemma; the `generalise` step does not make that cost disappear.

## Survey F section 10

The move is not one of the 18 candidate rules in survey F §10. It appears in
§8's comparison table as "Generalise / strengthen (free)" with evidence
"none". This entry supplies one concrete, checkable instance of that move
(Rocq, verified at the pinned commit), which could seed a §10 rule. My
judgement: it is closest in spirit to rule 6's "strengthen the hypothesis",
but it is not the same — here the generalisation is the *statement*, not an
induction's `arbitrary:` set.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .circleci/config.yml runs 'make -j' which via build -> qcert-compiler -> qcert-coq -> 'make -f Makefile.coq' (coq_makefile over Makefile.coq_modules, which lists Translation/Lang/NNRCtoDNNRC at line 376) compiles the file; commit e112de6d is the head of default branch master | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: nnrc_to_dnnrc_base_correct_lift@compiler/core/Translation/Lang/NNRCtoDNNRC.v:549, rec_sort_unlocalize_constants_comm@compiler/core/Translation/Lang/NNRCtoDNNRC.v:547, wf_cdenv_rec_sort@compiler/core/Translation/Lang/NNRCtoDNNRC.v:548; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 3 file(s) byte-identical at e112de6d7fda1b916244a1feb08bedd7f8a96bc1 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(nnrc_to_dnnrc_base_correct_lift, compiler/core/Translation/Lang/NNRCtoDNNRC.v, 473-485) -> declared: nnrc_to_dnnrc_base_correct_lift is declared at compiler/core/Translation/Lang/NNRCtoDNNRC.v:473 | check_claims.py |
| 2 | verified | cites(parent, nnrc_to_dnnrc_base_correct_lift) -> cites: nnrc_to_dnnrc_base_correct_lift occurs at compiler/core/Translation/Lang/NNRCtoDNNRC.v:549 | check_claims.py |
| 3 | verified | no_sorry(compiler/core/Translation/Lang/NNRCtoDNNRC.v, 473-557) -> no_sorry: none of admit, Admitted, Axiom, axiom in compiler/core/Translation/Lang/NNRCtoDNNRC.v:473-557 | check_claims.py |
| 4 | verified | copied NNRCtoDNNRC.v:549 'apply (nnrc_to_dnnrc_base_correct_lift tt).'; :481 'rewrite <- nnrc_to_dnnrc_base_correct; auto.' (inside nnrc_to_dnnrc_base_correct_lift, decl at 473); :367 'rewrite (nnrc_to_dnnrc_base_get_constant_correct h A plug_type plug annot v ctenv cdenv denv).' (inside nnrc_to_dnnrc_base_correct, decl at 357) — chain of 3 confirmed | verifier |
| 5 | verified | fetched NRAEnvtoNNRC.v: Theorem nraenv_to_nnrc_top_correct at 617-636 unfolds nnrc_eval_top/nraenv_eval_top/nraenv_to_nnrc_top and 'rewrite (nraenv_sem_correct ...)'; nraenv_sem_correct declared at line 281 (Theorem nraenv_sem_correct ...) | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Read local copy code/compiler/core/Translation/Lang/NNRCtoDNNRC.v. Parent nnrc_to_dnnrc_top_correct is exactly lines 532-557 (Theorem at 532, Qed at 557); glue cites all three children and nothing else: apply (nnrc_to_dnnrc_base_correct_lift tt) at 549, rewrite rec_sort_unlocalize_constants_comm at 547, generalize (wf_cdenv_rec_sort ...) at 548, then assumption + wf_denv/trivial closes. Children sites match: base_correct_lift 473-485 (Lemma at 473, Qed 485), rec_sort_unlocalize_constants_comm 497-509, wf_cdenv_rec_sort 511-530; closed_by paraphrases match the code (rewrite <- nnrc_to_dnnrc_base_correct;auto + unfold/destruct; rewrite map_rec_sort; apply same_domain_rec_sort + rewrite assoc_lookupr_drec_sort). Statements in entry.json match declarations verbatim. Shape numbers correct: glue_lines 26 (=532-557), child_lines [13,13,20] (=473-485, 497-509, 511-530), direct_lemmas 3, depth 3 (top_correct -> base_correct_lift:549 -> base_correct:481 -> get_constant_correct:367). No admit/Admitted/Axiom in 473-557; all Qed-terminated, so it closes. | reviewer-correctness |
| generality | accept | Move is stated generically: applicability.goal_shape gives a reusable template and use_when names annotation/plug types and section variables, not this file's constants; the opinion paragraph distils the transferable rule ('generalise, then pay one commutation lemma per wrapper'). avoid_when and consequences are honest and specific, tied to real facts I confirmed in code/ (rec_sort/unlocalize_constants wrappers at 547, wf_cdenv survives rec_sort at 548, the 115-line induction nnrc_to_dnnrc_base_correct at 357-471 that the top theorem does not cite), and they explicitly undercut the naive 'free' framing. Good-leaf rationale is explicit: each child is a self-contained statement closing by rewrite+auto (473-485), map_rec_sort+reflexivity (497-509), or two library lemmas (511-530), with no manual induction, and the lift lemma packages the big induction behind one identifier. | reviewer-generality |
| provenance-licence | accept | Commit e112de6d7fda1b916244a1feb08bedd7f8a96bc1 is consistent across entry.json, source.json and SOURCE.md (README short form e112de6d7fda is a valid prefix). check_provenance passes: 3 files byte-identical at the pinned commit; local sha256 matches entry.json. All permalinks use the pinned commit with correct paths; line ranges 473-485, 497-509, 511-530, 532-557 verified against the copied file and match the cited declarations/excerpts. Licence Apache-2.0 recorded in entry.json/README/SOURCE.md/source.json and confirmed by upstream-LICENSE (Apache 2.0 text). Source note records repo, commit, licence and attribution. Everything traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/querycert/qcert at commit `e112de6d7fda1b916244a1feb08bedd7f8a96bc1`, under `Apache-2.0`; see the [source note](../../sources/qcert/SOURCE.md) for the licence text and attribution.
