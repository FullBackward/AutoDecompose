# Interface lemma lifts per-expression refinement to the CFG level (I2F_denote_exp')

| | |
|---|---|
| Kind | instance |
| Move | interface-lemma |
| Language | rocq |
| Status | accepted |
| Source | [vellvm](../../sources/vellvm/SOURCE.md) at `e25dad9af332` |
| Licence | `MIT` |

## Intent

The per-expression refinement `I2F_denote_exp` is stated at the MCFG level
(`I2F_refine` over `denote_exp`), but the client-facing obligation files work
at the CFG level (`I2F_refine_CFG` over `denote_exp' := withCall (denote_exp
…)`). This entry records the one interface lemma, `I2F_denote_exp'`, that
lifts the lower-level result across that boundary, so every later file applies
the lemma instead of unfolding `denote_exp`/`withCall` and re-assembling the
UB/OOM cut predicates by hand.

## The decomposition

### parent `I2F_denote_exp'`: [`src/rocq/Theory/I2F/I2F_exp.v` lines 3292-3312](https://github.com/vellvm/vellvm/blob/e25dad9af33281b2edd3c16c027f3717546a09d7/src/rocq/Theory/I2F/I2F_exp.v#L3292-L3312) ([local copy](code/src/rocq/Theory/I2F/I2F_exp.v))

```coq
Lemma I2F_denote_exp' :
  forall e τ,
    I2F_refine_CFG I2F_dvalue (@denote_exp' PInf τ e) (@denote_exp' PFin τ e).
Proof. 
  unfold denote_exp', withCall.
  intros.
  unfold I2F_refine_CFG.
  eapply ruttc_translate_inr'; cycle -1.
  apply I2F_denote_exp.
  all:clear.
  - exact I2F_cutUB_CFG.
  - exact I2F_cutOOM_CFG.
  (* [rutt_cutoff.inr_prerel] of the (computing) sum is definitionally
       its right component *)
  - intros A B; split; intros e1 e2 HR.
    + now destruct HR.
    + now constructor.
  - intros A B; split; intros [e1 a] [e2 b] HR.
    + now destruct HR.
    + now constructor.
Qed.
```

### child `I2F_denote_exp`: [`src/rocq/Theory/I2F/I2F_exp.v` lines 3167-3290](https://github.com/vellvm/vellvm/blob/e25dad9af33281b2edd3c16c027f3717546a09d7/src/rocq/Theory/I2F/I2F_exp.v#L3167-L3290) ([local copy](code/src/rocq/Theory/I2F/I2F_exp.v))

```coq
Lemma I2F_denote_exp :
  forall (e : exp dtyp) τ, I2F_refine (@denote_exp PInf τ e) (@denote_exp PFin τ e).
Proof with try (rstep || cbnn; simp I2FE_Failure; reflexivity).
  induction e.
  - destruct id; intros; cbn...
  - intros [d|]; cbn...
    apply I2F_refine_lift, I2F_denote_int_syntax_as_int.
  - intros [d|]; cbn...
    apply I2F_refine_lift, I2F_denote_float_syntax_as_float.
  - destruct b; intros ?; cbn...
  - intros; cbn...
  - (* initializer *)
    intros [d|]; cbn...
    apply I2F_refine_lift, I2F_default_dvalue_of_dtyp.
  - cbn; intros.
    erbind.
    + apply ruttc_map_monad.
      intros [d e] HIN; now apply (H (d,e)).
    + intros * HF...
  - cbn; intros []...
  - cbn; intros []...
  - cbn; intros. 
    erbind.
    + apply ruttc_map_monad.
      intros [d e] HIN; now apply (H (d,e)).
    + intros * HF...
  - (* EXP_Packed_struct: the [dtyp] guard is a pure, parameter-free
         computation, related to itself by reflexivity of [I2F_EOU] ---
         no case analysis on the type. *)
    cbn; intros.
    erbind.
    + apply I2F_refine_lift, I2F_EOU_refl.
    + intros [] [] _.
      erbind.
      * apply ruttc_map_monad.
        intros [d e] HIN; now apply (H (d,e)).
      * intros * HF...
  - cbn; intros.
    erbind.
    + apply ruttc_map_monad.
      intros [d e] HIN; now apply (H (d,e)).
    + intros * HF...
  - cbn; intros.
    erbind.
    + apply ruttc_map_monad.
      intros [d e] HIN; now apply (H (d,e)).
    + (* the literal is canonicalised: [canonicalize_agg] *)
      intros * HF; rstep; apply I2F_canonicalize_agg; [| constructor]; auto.
  - cbn; intros.
    erbind; [apply IHe1 | intros].
    erbind; [apply IHe2 | intros].
    apply I2F_refine_lift, I2F_eval_iop...
  - destruct v; cbn; intros.
    erbind; [apply IHe | intros].
    apply I2F_refine_lift, I2F_eval_fneg...
  - cbn; intros.
    erbind; [apply IHe1 | intros].
    erbind; [apply IHe2 | intros].
    apply I2F_refine_lift, I2F_eval_icmp; eauto.
  - cbn; intros.
    erbind; [apply IHe1 | intros].
    erbind; [apply IHe2 | intros].
    apply I2F_refine_lift, I2F_eval_fop; eauto.
  - cbn; intros.
    erbind; [apply IHe1 | intros].
    erbind; [apply IHe2 | intros].
    apply I2F_refine_lift, I2F_eval_fcmp; eauto.
  - cbn; intros _.
    erbind; [apply IHe | intros].
    apply I2F_convert; eauto.
  - destruct ptrval; cbn; intros _.
    erbind; [apply IHe | intros].
    erbind.
    + apply ruttc_map_monad.
      intros [x y] HIN; now apply (H (x,y)).
    + intros; apply I2F_refine_lift, I2F_eval_gep; eauto.
  - destruct vec, idx; cbn; intros _.
    erbind; [apply IHe | intros].
    erbind; [apply IHe0 | intros].
    apply I2F_refine_lift, I2F_extract_element; eauto.
  - destruct vec, elt, idx; cbn; intros _.
    erbind; [apply IHe | intros].
    erbind; [erbind; [apply IHe0 | intros] | intros].
    apply I2F_refine_lift,I2F_dvalue_to_dvalue_base; auto.
    erbind; [apply IHe1 | intros].
    apply I2F_refine_lift, I2F_insert_element; auto.
  - destruct vec1,vec2,idxmask; cbn; intros _.
    erbind; [apply IHe | intros].
    erbind; [apply IHe0 | intros].
    erbind; [apply IHe1 | intros].
    apply I2F_refine_lift, I2F_shuffle_vector; auto.
  - destruct vec; cbn; intros _.
    erbind; [apply IHe | intros].
    apply I2F_refine_lift, I2F_extract_value; eauto.
  - destruct vec, elt; cbn; intros _.
    erbind; [apply IHe | intros].
    erbind; [apply IHe0 | intros].
    apply I2F_refine_lift, I2F_insert_value; eauto.
  - destruct cnd,v1,v2; cbn; intros _.
    erbind; [apply IHe | intros].
    erbind; [apply IHe0 | intros].
    erbind; [apply IHe1 | intros].
    apply I2F_refine_lift, I2F_eval_select; auto.
  - destruct v; cbn; intros _.
    erbind; [apply IHe | intros].
    apply I2F_freeze; auto.
  - cbn; intros _...
  - cbn; intros _; destruct m...
    all: try now rstep; constructor; eauto.
    destruct tv; cbn.
    eapply H; eauto.
  - (* EXP_Splat: the vector-type accessor is a pure, parameter-free
         computation, related to itself by reflexivity of [I2F_EOU] ---
         no case analysis on the type. *)
    destruct elt; cbn; intros.
    erbind.
    + apply I2F_refine_lift, I2F_EOU_refl.
    + intros [sz t'] ? <-; cbn.
      erbind; [apply IHe |].
      intros ? ? HR; rstep.
      apply I2F_canonicalize_agg; [| constructor]; apply Forall2_repeat; auto.
  - (* EXP_BlockAddress: a global read, like [EXP_Ident] *)
    intros; cbn...
Qed.
```

### child `I2F_cutUB_CFG`: [`src/rocq/Theory/I2F/Refinement.v` lines 472-480](https://github.com/vellvm/vellvm/blob/e25dad9af33281b2edd3c16c027f3717546a09d7/src/rocq/Theory/I2F/Refinement.v#L472-L480) ([local copy](code/src/rocq/Theory/I2F/Refinement.v))

```coq
Lemma I2F_cutUB_CFG :
  eqp1 (@cutUB (@CFGEtop PInf) _) (sum_pred1 FF1 (@cutUB (@MCFGEtop PInf) _)).
Proof.
  intros A e; split; intros CUT.
  - depelim CUT; now do 2 constructor.
  - (* [constructor] fails: unification refuses to unfold the
         [subevent] instance chain, but the two forms are convertible *)
    destruct CUT as [? ? [] | ? ? HC]; depelim HC; exact (CutUB v).
Qed.
```

### child `I2F_cutOOM_CFG`: [`src/rocq/Theory/I2F/Refinement.v` lines 482-488](https://github.com/vellvm/vellvm/blob/e25dad9af33281b2edd3c16c027f3717546a09d7/src/rocq/Theory/I2F/Refinement.v#L482-L488) ([local copy](code/src/rocq/Theory/I2F/Refinement.v))

```coq
Lemma I2F_cutOOM_CFG :
  eqp1 (@cutOOM (@CFGEtop PFin) _) (sum_pred1 FF1 (@cutOOM (@MCFGEtop PFin) _)).
Proof.
  intros A e; split; intros CUT.
  - depelim CUT; now do 2 constructor.
  - destruct CUT as [? ? [] | ? ? HC]; depelim HC; exact (CutOOM v).
Qed.
```

How the parts fit. The glue of `I2F_denote_exp'` first unfolds the two
definitions it is an interface *to* (`denote_exp'`, `withCall`) and the one it
is an interface *in terms of* (`I2F_refine_CFG`), then applies one library
reasoning principle and three project lemmas:

```
I2F_denote_exp'
├── I2F_denote_exp      (MCFG-level per-expression refinement)
├── I2F_cutUB_CFG       (UB cut: CFG-level ≡ structural MCFG-level form)
└── I2F_cutOOM_CFG      (OOM cut: CFG-level ≡ structural MCFG-level form)
```

Concretely: `eapply ruttc_translate_inr'` (line 3299, from the `rutt_cutoff`
library) turns the CFG-level `ruttc cutUB cutOOM …` into three obligations —
the left component, the two cut predicates, and two trivial sum-rel side
conditions. `apply I2F_denote_exp` (line 3300) discharges the left component
(the MCFG-level refinement, already proved); `exact I2F_cutUB_CFG` and
`exact I2F_cutOOM_CFG` (lines 3302-3303) discharge the cut predicates with the
two structural lemmas from `Refinement.v`; the last two bullets (lines
3306-3311) close the sum-rel side conditions by definitional computation.

Why each child is a good leaf:

- `I2F_denote_exp` is self-contained at the MCFG level: its statement mentions
  only `denote_exp` and `I2F_refine`, none of the CFG/`withCall` machinery. Its
  proof is an induction over the expression `e`, each constructor case closed by
  `erbind` plus `I2F_refine_lift` and the per-constructor `I2F_eval_*` /
  `I2F_denote_*` / `I2F_canonicalize_agg` lemmas, so it closes on its own and
  from its own siblings, not from the parent.
- `I2F_cutUB_CFG` is a structural equivalence between the CFG-level and
  MCFG-level UB cut predicates; it closes in four proof lines by case analysis
  and the `CutUB` constructor, with no further project lemma.
- `I2F_cutOOM_CFG` is the same equivalence for the OOM cut, closed in four lines
  by `CutOOM`.

The reader's context: `denote_exp'` is defined in `Semantics/Denotation.v`
(lines 377-378) as `withCall (denote_exp t e)`, and the comment there (lines
75-83) explains the two event signatures the interface lemma bridges. The three
named lemmas all live in the copied files, so their statements are shown
verbatim above.

## Why it is good

1. The parent site (the glue) is 21 lines long (check; permalink
   [I2F_exp.v#L3292-L3312](https://github.com/vellvm/vellvm/blob/e25dad9af33281b2edd3c16c027f3717546a09d7/src/rocq/Theory/I2F/I2F_exp.v#L3292-L3312)).
2. `I2F_denote_exp'` occurs 3 times in `src/rocq/Theory/I2F/I2F_denotation.v`
   (check; the count tool found it at lines 34, 266 and 284).
3. No closing-without-proof token (`admit`/`Admitted`/`Axiom`/`axiom`) occurs in
   `I2F_exp.v` lines 3167-3312 (check).
4. The longest chain of project lemmas below `I2F_denote_exp'` has depth 3:
   `I2F_denote_exp'` → `I2F_denote_exp` → `I2F_refine_lift` →
   `I2F_refine_lift_gen`, which bottoms out in `rutt_cutoff` constructors rather
   than further project lemmas (measurement; [I2F_exp.v#L3300](https://github.com/vellvm/vellvm/blob/e25dad9af33281b2edd3c16c027f3717546a09d7/src/rocq/Theory/I2F/I2F_exp.v#L3300), [I2F_exp.v#L3173](https://github.com/vellvm/vellvm/blob/e25dad9af33281b2edd3c16c027f3717546a09d7/src/rocq/Theory/I2F/I2F_exp.v#L3173), [Refinement.v#L578](https://github.com/vellvm/vellvm/blob/e25dad9af33281b2edd3c16c027f3717546a09d7/src/rocq/Theory/I2F/Refinement.v#L578), [Refinement.v#L550-L558](https://github.com/vellvm/vellvm/blob/e25dad9af33281b2edd3c16c027f3717546a09d7/src/rocq/Theory/I2F/Refinement.v#L550-L558)).
5. The authors document the two-signature boundary this lemma crosses:
   expressions "are also denoted at the [mcfg] level", and "[withCall] injects
   an expression's [MCFGtop] tree into it (see [denote_exp'])" (author-statement;
   [Denotation.v#L75-L83](https://github.com/vellvm/vellvm/blob/e25dad9af33281b2edd3c16c027f3717546a09d7/src/rocq/Semantics/Denotation.v#L75-L83)).

In my opinion the detail worth copying is the *shape* of the glue, not its
content: five lines of rule application, of which three are `apply`/`exact` of
named lemmas and two are inline trivialities. The interface lemma earns its
name by being the only place the CFG-level definition is unfolded, so the
boundary is crossed exactly once.

## When to use it, and when not

Use it when a per-component refinement is already proved at one signature level
and the client-facing statements live at another that is related to the first
by a definitional injection (here `denote_exp' := withCall (denote_exp …)`), so
the boundary lemma is a few `apply`/`exact` steps over already-proved lemmas.
State it once and let every downstream file cite it.

Avoid it when the two signature levels are not definitionally related, when the
higher-level cut predicates are not the structural decomposition of the
lower-level ones (then the lemma would need a substantive proof rather than
`exact`), or when no downstream client reuses the lemma — an interface lemma
with a single caller is just indirection.

## Consequences

The move creates one obligation: that the higher-signature refinement is
exactly the lower refinement composed with the cut predicates. Here it is
discharged by `ruttc_translate_inr'` plus the two `I2F_cut*_CFG` structural
lemmas and two inline sum-rel side conditions. The boundary lemma becomes the
single point clients cite, so a change to the higher signature (a new event)
breaks only this lemma and its cut side conditions, not the client files. The
failure mode is over-unfolding: if a client unfolds `denote_exp'` and re-proves
the lifting, the decomposition stops being a single boundary and the cut
lemmas get duplicated across files.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/vellvm.yml (Vellvm Compilation Test) triggers on push to main (default branch); its coq-community/docker-coq-action builds rocq-vellvm.opam whose build is 'make -C src all', which compiles src/rocq/Theory/I2F/I2F_exp.v; pinned commit e25dad9af33281b2edd3c16c027f3717546a09d7 is an ancestor of main (compare base...main: status ahead, behind_by 0) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: I2F_denote_exp@src/rocq/Theory/I2F/I2F_exp.v:3300, I2F_cutUB_CFG@src/rocq/Theory/I2F/I2F_exp.v:3302, I2F_cutOOM_CFG@src/rocq/Theory/I2F/I2F_exp.v:3303; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 4 file(s) byte-identical at e25dad9af33281b2edd3c16c027f3717546a09d7 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(parent, 21) -> lines: site parent has 21 lines | check_claims.py |
| 2 | verified | count(I2F_denote_exp', 3, src/rocq/Theory/I2F/I2F_denotation.v) -> count: I2F_denote_exp' occurs 3 times in 1 file(s) matching src/rocq/Theory/I2F/I2F_denotation.v | check_claims.py |
| 3 | verified | no_sorry(src/rocq/Theory/I2F/I2F_exp.v, 3167-3312) -> no_sorry: none of admit, Admitted, Axiom, axiom in src/rocq/Theory/I2F/I2F_exp.v:3167-3312 | check_claims.py |
| 4 | verified | Read copied code: I2F_exp.v L3300 'apply I2F_denote_exp.' (in parent glue L3292-3312); L3173 'apply I2F_refine_lift, I2F_denote_int_syntax_as_int.' (in child I2F_denote_exp L3167-3290); Refinement.v L578 'apply (I2F_refine_lift_gen I2FE_MCFG_Throw)' inside I2F_refine_lift (L575); I2F_refine_lift_gen proof L552-558 uses pfold/constructor, ruttc_trigger_cast, EqCutL/EqCutR (library constructors, no project lemma). Chain I2F_denote_exp' -> I2F_denote_exp -> I2F_refine_lift -> I2F_refine_lift_gen = depth 3, matching claim. | verifier |
| 5 | verified | Read copied code Denotation.v L75-83: 'Two signatures are used' comment documents MCFGEtop (expressions 'are also denoted at the [mcfg] level') vs CFGEtop ('[withCall] injects an expression's [MCFGtop] tree into it (see [denote_exp'])'). Both quoted phrases present verbatim. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Decomposition matches code: parent I2F_denote_exp' (I2F_exp.v 3292-3312, 21 lines) applies exactly the three named project lemmas that are its children -- apply I2F_denote_exp at 3300, exact I2F_cutUB_CFG at 3302, exact I2F_cutOOM_CFG at 3303 -- plus the library principle ruttc_translate_inr' (3299) and two inline sum-rel side conditions; no other named lemma is cited. Child statements and closed_by fields match the code verbatim (I2F_denote_exp 3167-3290 induction on e; I2F_cutUB_CFG 472-480; I2F_cutOOM_CFG 482-488). Every site ends in Qed and no_sorry covers 3167-3312, so it closes. Shape numbers are right: glue_lines 21 (3292-3312), child_lines [124,9,7] (=3167-3290, 472-480, 482-488), direct_lemmas 3, depth 3 (chain I2F_denote_exp'->I2F_denote_exp at 3300 ->I2F_refine_lift at 3173 ->I2F_refine_lift_gen at Refinement.v 578, bottoming in constructors at 550-558). | reviewer-correctness |
| generality | accept | Move generalises beyond the example: use/avoid conditions are stated at the level of signature levels, definitional injection (denote_exp' := withCall (denote_exp ...), confirmed at Denotation.v 377-378), and structural cut predicates, not tied to I2F. 'When not to use' gives three concrete, honest failure conditions (not definitionally related; cuts not the structural decomposition so a substantive proof is needed; no downstream reuse = indirection). Consequences are specific and honest: one obligation (higher refinement = lower composed with cuts), the lemma becomes the single point clients cite (confirmed by the 3 known uses at I2F_denotation.v 34/266/284 all applying I2F_denote_exp'), and the over-unfolding failure mode is named. The 'Why each child is a good leaf' section says what makes each leaf fit a bounded prover: I2F_denote_exp is self-contained at the MCFG level and closes from its own siblings (not the parent), while the two cut lemmas are structural equivalences closing in ~4 lines with no further project lemma. Author-statement about the two-signature boundary matches Denotation.v 75-83. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are all consistent and traceable. check_provenance passes: 4 files byte-identical at e25dad9af33281b2edd3c16c027f3717546a09d7. The copied code/ tree holds exactly the 4 files listed in entry.json files[]. Commit e25dad9af332... is identical in entry.json (files, sites, known_uses, permalinks), source.json, and README.md. Licence MIT is consistent across entry.json, README.md, sources/vellvm/SOURCE.md, source.json, and the copied upstream-LICENSE.md (verbatim MIT text). SOURCE.md correctly records the LICENSE.md -> upstream-LICENSE.md copy and attribution; README's Source-and-licence section links to ../../sources/vellvm/SOURCE.md, which resolves. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/vellvm/vellvm at commit `e25dad9af33281b2edd3c16c027f3717546a09d7`, under `MIT`; see the [source note](../../sources/vellvm/SOURCE.md) for the licence text and attribution.
