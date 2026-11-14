# Per-pass soundness lemmas for micromega's tauto_checker

| | |
|---|---|
| Kind | instance |
| Move | per-callee-lemma |
| Language | rocq |
| Status | accepted |
| Source | [rocq-stdlib](../../sources/rocq-stdlib/SOURCE.md) at `22fcaa27d17b` |
| Licence | `LGPL-2.1-only` |

## Intent

Soundness of micromega's `tauto_checker` is reduced to the two pass lemmas the
checker is built from — `xcnf_correct` for the formula-to-CNF translation and
`cnf_checker_sound` for the per-clause oracle — so the top-level theorem is a
two-step composition with no case analysis of its own.

## The decomposition

### parent `tauto_checker_sound`: [`theories/micromega/Tauto.v` lines 2060-2067](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/micromega/Tauto.v#L2060-L2067) ([local copy](code/theories/micromega/Tauto.v))

```coq
  Lemma tauto_checker_sound : forall t  w, tauto_checker t w = true -> forall env, eval_f e_rtyp (eval env)  t.
  Proof.
    unfold tauto_checker.
    intros t w H env.
    change (eval_f e_rtyp (eval env) t) with (eval_f e_rtyp (eval env) (if true then t else TT isProp)).
    apply (xcnf_correct t true).
    eapply cnf_checker_sound ; eauto.
  Qed.
```

### child `xcnf_correct`: [`theories/micromega/Tauto.v` lines 1894-2016](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/micromega/Tauto.v#L1894-L2016) ([local copy](code/theories/micromega/Tauto.v))

```coq
  Lemma xcnf_correct : forall (k: kind) (f : @GFormula Term rtyp Annot unit k)  pol env,
      eval_cnf env (xcnf pol f) -> hold k (eval_f e_rtyp (eval env) (if pol then f else NOT f)).
  Proof.
    intros k f;
     induction f as [| | | |? ? IHf1 ? IHf2|? ? IHf1 ? IHf2|? ? IHf
       |? ? IHf1 ? ? IHf2|? ? IHf1 f2 IHf2|f1 IHf1 f2 IHf2];
     intros pol env H.
    - (* TT *)
      unfold eval_cnf.
      simpl.
      destruct pol ; intros; simpl; auto with tauto.
      rewrite eval_cnf_ff in H. tauto.
    - (* FF *)
      destruct pol ; simpl in *; intros; auto with tauto.
      + rewrite eval_cnf_ff in H. tauto.
    - (* P *)
      simpl.
      destruct pol ; intros ;simpl.
      + rewrite eval_cnf_ff in H. tauto.
      + rewrite eval_cnf_ff in H. tauto.
    - (* A *)
      simpl.
      destruct pol ; simpl.
      + intros.
        eapply normalise_correct  ; eauto.
      + (* A 2 *)
        intros.
        eapply  negate_correct ; eauto.
    - (* AND *)
      destruct pol ; simpl in H.
      + (* pol = true *)
        intros.
        rewrite eval_cnf_and_opt in H.
        unfold and_cnf in H.
        rewrite eval_cnf_app  in H.
        destruct H as [H H0].
        apply hold_eAND; split.
        * apply (IHf1 _ _ H).
        * apply (IHf2 _ _ H0).
      +  (* pol = false *)
        intros.
        apply hold_eNOT.
        rewrite hold_eAND.
        rewrite or_cnf_opt_correct in H.
        rewrite or_cnf_correct in H.
        destruct H as [H | H].
        * generalize (IHf1 false  env H).
          simpl.
          rewrite hold_eNOT.
          tauto.
        * generalize (IHf2 false  env H).
          simpl.
          rewrite hold_eNOT.
          tauto.
    - (* OR *)
      simpl in H.
      destruct pol.
      + (* pol = true *)
        intros. unfold mk_or in H.
        rewrite or_cnf_opt_correct in H.
        rewrite or_cnf_correct in H.
        destruct H as [H | H].
        * generalize (IHf1 _  env H).
          simpl.
          rewrite hold_eOR.
          tauto.
        * generalize (IHf2 _  env H).
          simpl.
          rewrite hold_eOR.
          tauto.
      + (* pol = true *)
        intros. unfold mk_or in H.
        rewrite eval_cnf_and_opt in H.
        unfold and_cnf.
        rewrite eval_cnf_app in H.
        destruct H as [H0 H1].
        simpl.
        generalize (IHf1 _ _ H0).
        generalize (IHf2 _ _ H1).
        simpl.
        rewrite ! hold_eNOT.
        rewrite ! hold_eOR.
        tauto.
    - (**)
      simpl.
      destruct pol ; simpl.
      + intros.
        apply (IHf false) ; auto.
      + intros.
        generalize (IHf _ _ H).
        rewrite ! hold_eNOT.
        tauto.
    - (* IMPL *)
      apply xcnf_impl; auto.
    - apply xcnf_iff ; auto.
    - simpl in H.
      destruct (is_bool f2) as [b|] eqn:EQ.
      + apply is_bool_inv in EQ.
        destruct b; subst; intros;
          apply IHf1 in H;
          destruct pol ; simpl in * ; auto.
        * unfold is_true in H.
          rewrite negb_true_iff in H.
          congruence.
        *
          unfold is_true in H.
          rewrite negb_true_iff in H.
          congruence.
        * unfold is_true in H.
          congruence.
      + intros.
        rewrite <- mk_iff_is_bool in H.
        apply xcnf_iff in H; auto.
        simpl in H.
        destruct pol ; simpl in *.
        * rewrite <- hold_eEQ.
          simpl; auto.
        * rewrite <- hold_eEQ.
          simpl; auto.
          unfold is_true in *.
          rewrite negb_true_iff in H.
          congruence.
  Qed.
```

### child `cnf_checker_sound`: [`theories/micromega/Tauto.v` lines 2035-2055](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/micromega/Tauto.v#L2035-L2055) ([local copy](code/theories/micromega/Tauto.v))

```coq
  Lemma cnf_checker_sound : forall t  w, cnf_checker t w = true -> forall env, eval_cnf  env  t.
  Proof.
    unfold eval_cnf.
    intros t; induction t as [|a t IHt].
    - (* bc *)
      simpl.
      auto.
    - (* ic *)
      simpl.
      intros w; destruct w as [|w ?].
      + intros ; discriminate.
      + case_eq (checker a w) ; intros H H0 env ** ; try discriminate.
        generalize (@checker_sound _ _ H env).
        generalize (IHt _ H0 env) ; intros H1 H2.
        destruct t.
        * red ; intro.
          rewrite <- make_conj_impl in H2.
          tauto.
        * rewrite <- make_conj_impl in H2.
          tauto.
  Qed.
```

How the parts fit. `tauto_checker` is the composition of two passes, and each
pass is proved correct by its own lemma:

```
tauto_checker_sound (glue, 2060-2067)
├── xcnf_correct (pass 1, 1894-2016)
│   ├── xcnf_impl (IMPL case helper, 1791)
│   ├── xcnf_iff (IFF case helper, 1853)
│   └── hold_e* / or_cnf_correct / eval_cnf_* (rewriting lemmas)
│       └── or_cnf_correct → or_clause_cnf_correct → or_clause_correct → add_term_correct
└── cnf_checker_sound (pass 2, 2035-2055)
    └── checker_sound (section hypothesis, 2021) + make_conj_impl (Refl.v)
```

The glue unfolds [`tauto_checker`](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/micromega/Tauto.v#L2057-L2058),
which is `cnf_checker (xcnf true f) w`, and then `change`s the goal's `eval_f …
t` into `eval_f … (if true then t else TT isProp)` — the `TT isProp` branch is
never taken, but the rewrite makes the goal match `xcnf_correct`'s conclusion
for `pol = true`. Then `apply (xcnf_correct t true)` swaps the goal for pass 1's
hypothesis `eval_cnf env (xcnf true t)`, and `eapply cnf_checker_sound ; eauto`
swaps that for pass 2's hypothesis `cnf_checker (xcnf true t) w = true`, which
is exactly the assumption `H`. The two passes meet at the single intermediate
predicate `eval_cnf env (xcnf true t)`: `xcnf_correct` produces it,
`cnf_checker_sound` consumes it.

Each child is a good leaf because it is a self-contained statement whose proof
closes on its own, without naming the other child or the parent:

- **`xcnf_correct`** (pass 1) is closed by `induction f` over the formula; the
  atom case applies the section hypotheses `normalise_correct`/`negate_correct`,
  the boolean cases close by rewriting with `eval_cnf_ff` and the `hold_e*`
  lemmas, and the two structural cases `IMPL` and `IFF` are delegated to the
  induction helpers `xcnf_impl` and `xcnf_iff`, which carry the IHs. It ends
  `Qed` and never mentions the checker.
- **`cnf_checker_sound`** (pass 2) is closed by `induction t` over the clause
  list; for each clause it does `case_eq (checker a w)`, generalises the
  per-clause hypothesis `checker_sound` and the IH, and rewrites with
  `make_conj_impl` (from `Refl.v`) to turn `make_impl … False` into
  `~ make_conj …` — i.e. `eval_clause`. It ends `Qed` and never mentions `xcnf`.

Both children are parametric in the oracle: `cnf_checker_sound` needs the
section hypothesis [`checker_sound`](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/micromega/Tauto.v#L2021)
(`checker t w = true -> forall env, make_impl (eval_tt env) t False`), so the
checker itself is *assumed* sound and the proof here only shows the lifting from
one clause to a whole CNF.

## Why it is good

1. The top-level theorem is 8 lines of glue composing 2 direct lemmas, whose
   child sites span 123 and 21 lines; below the main theorem is a chain of 6
   project lemmas, `xcnf_correct` down to `add_term_correct` (*measurement*; see
   claim 1 in `entry.json` for the exact line pointers).
2. `tauto_checker_sound` is declared at line 2060 of
   `theories/micromega/Tauto.v` (*check*,
   [permalink](https://github.com/rocq-prover/stdlib/blob/22fcaa27d17bc28ab4be728ed10a1fb73afb23ee/theories/micromega/Tauto.v#L2060)).
3. The parent site cites `xcnf_correct` (*check*; line 2065).
4. The parent site cites `cnf_checker_sound` (*check*; line 2066).
5. CompCert's `transf_c_program_match` chains one per-pass
   `transf_program_match` lemma per compilation pass — `SimplExprproof` through
   `Asmgenproof` — the same per-callee-lemma composition this entry records
   (*known-use*,
   [permalink](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/driver/Compiler.v#L265-L318)).

In my opinion the detail worth copying is the polarity trick in the glue: the
one-line `change` (`if true then t else TT isProp`) is the whole cost of making
pass 1's conclusion line up with the goal, and it is far cheaper than re-proving
anything — which is exactly what makes the per-pass structure pay.

## When to use it, and when not

Use it when a certified or reflexive procedure is a composition of passes, each
pass has (or deserves) its own correctness lemma stated over the intermediate
representation it shares with the next pass, and the top-level proof only has to
line the passes up (`unfold`, a `change`, then `apply`/`eapply`). This is the
shape of a compiler's correctness theorem and of reflective procedures that
turn a goal into a certificate the oracle then checks.

Avoid it when the passes' correctness statements do not share an intermediate
predicate, so the glue has to reason *inside* a pass rather than compose two
lemmas; when a pass has no independent, reusable statement worth naming (then
there is no "callee" to give a lemma); or when the top-level proof must do real
work in the middle (a non-trivial invariant over the intermediate result)
instead of only composing.

## Consequences

The glue concentrates everything into aligning the two pass lemmas: it unfolds
`tauto_checker` and `change`s `eval_f … t` into `eval_f … (if true then t else
TT isProp)` so that `xcnf_correct`'s conclusion and `cnf_checker_sound`'s
hypothesis both mention `eval_cnf env (xcnf true t)`. The obligations move down:
`xcnf_correct` must hold for the polarity `true` that `tauto_checker` fixes (the
`pol` parameter generalises to both polarities, but the glue only needs one),
and `cnf_checker_sound` is parametric in the oracle's soundness, which is the
section hypothesis `checker_sound` — the checker itself is *assumed* sound here,
not proved. Known failure mode: if a pass's correctness statement does not line
up with the next pass's input, the glue gains a pile of `change`/rewrites, or
the composition breaks and the top-level proof is no longer just two applies.
This entry also supports survey F §10 rule 4 (extract a `have` into a standalone
lemma): each pass *is* the standalone lemma that rule wants, and the glue cites
both by name with nothing added — the fidelity that rule 4's check enforces.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/nix-action-rocq-9.3.yml (name 'Nix CI for bundle rocq-9.3') runs on push to master (default branch; on: push: branches: [master]) and builds the stdlib job via 'nix-build --argstr bundle rocq-9.3 --argstr job stdlib', which compiles the whole standard library including theories/micromega/Tauto.v; pinned commit 22fcaa27 is on master (compare master...22fcaa27: ahead_by 0, behind_by 2) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: xcnf_correct@theories/micromega/Tauto.v:2065, cnf_checker_sound@theories/micromega/Tauto.v:2066; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at 22fcaa27d17bc28ab4be728ed10a1fb73afb23ee | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | parent site Tauto.v:2060-2067 is 8 lines (read verbatim: Lemma..Qed); xcnf_correct declared 1894, Qed 2016 = 123 lines; cnf_checker_sound declared 2035, Qed 2055 = 21 lines; chain citations at 2065 (xcnf_correct), 1987 (xcnf_impl), 1813 (or_cnf_correct), 1681 (or_clause_cnf_correct), 1634 (or_clause_correct), 1598 (add_term_correct) all confirmed by sed of copied code | verifier |
| 2 | verified | declared(tauto_checker_sound, theories/micromega/Tauto.v, 2060-2060) -> declared: tauto_checker_sound is declared at theories/micromega/Tauto.v:2060 | check_claims.py |
| 3 | verified | cites(parent, xcnf_correct) -> cites: xcnf_correct occurs at theories/micromega/Tauto.v:2065 | check_claims.py |
| 4 | verified | cites(parent, cnf_checker_sound) -> cites: cnf_checker_sound occurs at theories/micromega/Tauto.v:2066 | check_claims.py |
| 5 | verified | fetched AbsInt/CompCert@2685140 driver/Compiler.v: transf_c_program_match proof composes per-pass transf_program_match lemmas via nested exists p; split / apply ...transf_program_match, from SimplExprproof through Asmgenproof (21 passes), ending with reflexivity | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent site (Tauto.v 2060-2067) verbatim matches the copied code: unfold tauto_checker; intros; change to (if true then t else TT isProp); apply (xcnf_correct t true); eapply cnf_checker_sound; eauto; Qed. The two children are exactly the two lemmas the glue cites (xcnf_correct @2065, cnf_checker_sound @2066), and no other lemma is cited directly. Child sites xcnf_correct (1894-2016) and cnf_checker_sound (2035-2055) match the copied code, and their closing methods match: xcnf_correct ends by induction f with IMPL/IFF delegated to xcnf_impl/xcnf_iff (apply xcnf_impl @1987), cnf_checker_sound by induction t + case_eq (checker a w) + generalize checker_sound (@2021) + rewrite make_conj_impl, both ending Qed (no sorry/admit). Shape numbers correct: glue_lines=8 (2060-2067), child_lines=[123,21], direct_lemmas=2, depth=6. Claim 1's depth-6 chain pointers all check out: 2065 (apply xcnf_correct), 1987 (apply xcnf_impl), 1813 (rewrite or_cnf_correct), 1681 (rewrite or_clause_cnf_correct), 1634 (generalize or_clause_correct), 1598 (assert add_term_correct). Statements in entry.json match the declarations verbatim. | reviewer-correctness |
| generality | accept | Move stated beyond the example: applicability.goal_shape and use_when frame it as per-pass soundness lemmas over a shared intermediate predicate, and known-use/claim 5 anchors it to CompCert's per-pass transf_program_match chain, so it generalises from the 2-pass micromega case to N-pass compilers. 'When not to use' (avoid_when) is honest and specific: no shared intermediate predicate, no independently reusable statement per pass, or the top-level proof doing real work mid-composition -- each a genuine failure mode, not a platitude. Consequences are honest: they admit the oracle checker is assumed sound via section hypothesis checker_sound (verified at Tauto.v:2021), and name a concrete failure mode (misaligned pass statements pile up change/rewrites). Good leaves for a bounded prover are named: 'Each child is a good leaf because it is a self-contained statement whose proof closes on its own, without naming the other child or the parent' -- xcnf_correct (induction over the formula, IMPL/IFF delegated to xcnf_impl:1791 / xcnf_iff:1853) and cnf_checker_sound (induction over the clause list) are mutually independent, each Qed without citing the other; metrics.children_closed_by_automation:0 honestly notes neither is a one-tactic leaf. Depth-6 chain line pointers (2065->1987->1813->1681->1634->1598) all verified present. | reviewer-generality |
| provenance-licence | accept | check_provenance passes (2 files byte-identical at 22fcaa27d17bc28ab4be728ed10a1fb73afb23ee); local sha256 matches entry.json (Tauto.v 8688f102…, Refl.v 7fd79640…); entry.json source.commit and all permalinks use 22fcaa27d17bc28ab4be728ed10a1fb73afb23ee, matching sources/rocq-stdlib/SOURCE.md and source.json; licence LGPL-2.1 consistent across entry, source note, source.json and upstream-LICENSE; README source/licence section matches | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/rocq-prover/stdlib at commit `22fcaa27d17bc28ab4be728ed10a1fb73afb23ee`, under `LGPL-2.1-only`; see the [source note](../../sources/rocq-stdlib/SOURCE.md) for the licence text and attribution.
