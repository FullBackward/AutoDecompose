# Soundness of the I2F interpreter, generalised over the argument generator

| | |
|---|---|
| Kind | instance |
| Move | generalise-then-instantiate |
| Language | rocq |
| Status | accepted |
| Source | [vellvm](../../sources/vellvm/SOURCE.md) at `e25dad9af332` |
| Licence | `MIT` |

## Intent

The headline I2F soundness theorem `I2F_interpreter_param` — the reference
interpreter over infinite memory (`PInf`) refines the interpreter over finite
memory (`PFin`) — is proved in one tactic line by proving the refinement once
for an arbitrary argument-generating computation and then specialising it.
`I2F_interpreter_gen` generalises `interpreter_param` over the argument
generator `arg_gen` (any two generators related by `I2F_refine_MCFG (Forall2
I2F_dvalue)`), and `I2F_build_main_args` discharges the one premise that results
for the concrete generator `build_main_args`.

## The decomposition

### parent `I2F_interpreter_param`: [`src/rocq/Theory/I2F/I2F_toplevel.v` lines 455-463](https://github.com/vellvm/vellvm/blob/e25dad9af33281b2edd3c16c027f3717546a09d7/src/rocq/Theory/I2F/I2F_toplevel.v#L455-L463) ([local copy](code/src/rocq/Theory/I2F/I2F_toplevel.v))

```coq
Theorem I2F_interpreter_param :
  forall (args : list string) (prog : ll_toplevel_entities),
    I2F_refine_MCFGbot (prod_rel I2F_FusedS I2F_dvalue)
      (@interpreter_param PInf args prog)
      (@interpreter_param PFin args prog).
Proof.
  intros.
  apply I2F_interpreter_gen, I2F_build_main_args.
Qed.
```

### child `I2F_interpreter_gen`: [`src/rocq/Theory/I2F/I2F_toplevel.v` lines 437-453](https://github.com/vellvm/vellvm/blob/e25dad9af33281b2edd3c16c027f3717546a09d7/src/rocq/Theory/I2F/I2F_toplevel.v#L437-L453) ([local copy](code/src/rocq/Theory/I2F/I2F_toplevel.v))

```coq
Lemma I2F_interpreter_gen :
  forall (ret_typ : dtyp) (entry : function_id)
    (arg_gen1 : @MCFGtop PInf (list (@dvalue PInf)))
    (arg_gen2 : @MCFGtop PFin (list (@dvalue PFin)))
    (prog : ll_toplevel_entities),
    I2F_refine_MCFG (Forall2 I2F_dvalue) arg_gen1 arg_gen2 ->
    I2F_refine_MCFGbot (prod_rel I2F_FusedS I2F_dvalue)
      (@interpreter_gen PInf ret_typ entry arg_gen1 prog)
      (@interpreter_gen PFin ret_typ entry arg_gen2 prog).
Proof.
  intros.
  unfold interpreter_gen.
  eapply I2F_interp_mcfg_bind; eauto; cycle -1.
  { apply I2F_initial_FusedS. }
  intros.
  now apply I2F_denote_vellvm.
Qed.
```

### child `I2F_build_main_args`: [`src/rocq/Theory/I2F/I2F_toplevel.v` lines 231-239](https://github.com/vellvm/vellvm/blob/e25dad9af33281b2edd3c16c027f3717546a09d7/src/rocq/Theory/I2F/I2F_toplevel.v#L231-L239) ([local copy](code/src/rocq/Theory/I2F/I2F_toplevel.v))

```coq
Lemma I2F_build_main_args : forall (args : list string),
    I2F_refine_MCFG (Forall2 I2F_dvalue)
      (@build_main_args PInf args) (@build_main_args PFin args).
Proof.
  intros args; unfold build_main_args.
  rbind I2F_dvalue; [apply I2F_allocate_args | ].
  intros v1 v2 Hv; apply ruttc_ret.
  repeat constructor; auto.
Qed.
```

### context `interpreter_param_def`: [`src/rocq/Semantics/TopLevel.v` lines 313-332](https://github.com/vellvm/vellvm/blob/e25dad9af33281b2edd3c16c027f3717546a09d7/src/rocq/Semantics/TopLevel.v#L313-L332) ([local copy](code/src/rocq/Semantics/TopLevel.v))

```coq
  Definition interpreter_gen
    (ret_typ : dtyp)
    (entry : function_id)
    (arg_gen : MCFGtop (list dvalue))
    (prog: ll_toplevel_entities) : MCFGbot (Res dvalue) :=
    let t :=
      args <- arg_gen;;
      denote_vellvm ret_typ entry args
        (convert_types (mcfg_of_tle (link PREDEFINED_FUNCTIONS prog)))
    in interp_mcfg t (initial_state, ((Build_stack_frame Maps.empty None None,[]), Maps.empty)).

  (**
     Finally, the reference interpreter assumes no user-defined intrinsics and starts
     from "main" using bogus initial inputs.
   *)
  Definition interpreter_param
             (args : list string)
             (prog : ll_toplevel_entities)
              : MCFGbot _ 
    := interpreter_gen (DTYPE_I 32%positive) (Name "main") (build_main_args args) prog.
```

How the parts fit. `interpreter_param` is defined (`TopLevel.v:328-332`, shown
in context) as `interpreter_gen (DTYPE_I 32%positive) (Name "main")
(build_main_args args) prog` — the general interpreter applied to one fixed
argument generator, `build_main_args`. The decomposition proves the general
statement once and then specialises it:

```
I2F_interpreter_param (parent, 455-463) — the glue, 2 tactic lines
  ├─ I2F_interpreter_gen (437-453)      general: any arg_gen1/arg_gen2 related
  │    │                                by I2F_refine_MCFG (Forall2 I2F_dvalue)
  │    ├─ I2F_interp_mcfg_bind          bind congruence of interp_mcfg (I2F_interp.v:756)
  │    ├─ I2F_initial_FusedS (50-68)    the initial fused states refine
  │    └─ I2F_denote_vellvm (404-433)   whole-program denotation refines
  │         └─ I2F_denote_mcfg          (I2F_denotation.v:779)
  └─ I2F_build_main_args (231-239)      the instance: build_main_args refines
       │                                itself under Forall2 I2F_dvalue
       └─ I2F_allocate_args (213-229)   each command-line arg allocates alike
```

The glue `apply I2F_interpreter_gen, I2F_build_main_args` (line 462) is forward
reasoning: `apply I2F_interpreter_gen` turns the goal into the single premise of
the general lemma, namely `I2F_refine_MCFG (Forall2 I2F_dvalue) (build_main_args
PInf args) (build_main_args PFin args)`, and `apply I2F_build_main_args` closes
that premise exactly. The general lemma is the skeleton; the instance is the one
hole it leaves.

Each child is a good leaf because it closes on its own from named siblings, not
from the other child:

- `I2F_interpreter_gen` unfolds `interpreter_gen`, then `eapply
  I2F_interp_mcfg_bind` splits the goal into the initial-state branch (closed by
  `apply I2F_initial_FusedS`) and the continuation branch (closed by `now apply
  I2F_denote_vellvm`). It never mentions `build_main_args`.
- `I2F_build_main_args` unfolds `build_main_args`, then `rbind I2F_dvalue`
  dispatches the allocation to `I2F_allocate_args` and closes the value relation
  with `apply ruttc_ret; repeat constructor; auto`. It never mentions
  `interpreter_gen`.

## Why it is good

1. (`check`, `declared`) `I2F_interpreter_param` is declared in
   `src/rocq/Theory/I2F/I2F_toplevel.v` within lines 455-463.
2. (`check`, `cites`) `I2F_interpreter_gen` occurs in the parent site — the
   general lemma is the one the glue applies.
3. (`check`, `cites`) `I2F_build_main_args` occurs in the parent site — the
   concrete argument generator is the instantiation the glue supplies.
4. (`check`, `no_sorry`) No `admit`, `Admitted`, `Axiom` or `axiom` token occurs
   in `src/rocq/Theory/I2F/I2F_toplevel.v` lines 231-463, the span that holds
   the parent and its two children.
5. (`measurement`) The theorem-scale shape: 2 direct lemmas, a longest
   project-lemma chain of depth 3 below `I2F_interpreter_param`, a 9-line parent
   site and child sites of 17 and 9 lines (see the depth chain in "How the parts
   fit").

In my opinion the move worth copying is the *generalisation, not the
soundness argument*: the parent is a two-tactic-line assembly
(`intros; apply I2F_interpreter_gen, I2F_build_main_args`) that is nearly
trivial given the children, and the real content lives in `I2F_interpreter_gen`
(which is itself re-usable for any other argument generator) and in the one
instantiation `I2F_build_main_args`. That is exactly the shape AutoDecompose is
meant to produce, and what survey F §10 rule 14 targets ("one key theorem or a
few tactics").

## When to use it, and when not

Use it when the concrete statement is a *pure* specialisation of a general one —
here `interpreter_param := interpreter_gen … (build_main_args args) prog` — so
that proving the general refinement leaves exactly one premise, the statement of
a helper about the shared sub-computation, and the whole proof becomes
`apply general_lemma, instance_helper`. The pattern pays off when the general
statement is no harder than the special one (the argument generator appears only
as an opaque `arg_gen` in the general proof) and the instance helper is easy.

Avoid it when the concrete function is not a plain instantiation of the general
one (there are steps between the general result and the target), when the
premise the instance needs is itself as hard as the target, or when the
generalisation forces you to carry a hypothesis (here `I2F_refine_MCFG (Forall2
I2F_dvalue) arg_gen1 arg_gen2`) that is hard to discharge at the single use site.

## Consequences

The move creates exactly one obligation: the premise of `I2F_interpreter_gen`,
that the two concrete argument generators are related (`I2F_refine_MCFG (Forall2
I2F_dvalue) (build_main_args PInf args) (build_main_args PFin args)`), discharged
by `I2F_build_main_args`. The saving rests on `interpreter_param` being a pure
instantiation (`TopLevel.v:332`); if the top-level function did anything after
`interpreter_gen`, the glue's `apply … , I2F_build_main_args` would no longer
match and the one-line assembly would break. The theorem is only as strong as
`I2F_interpreter_gen`, which rests on `I2F_interp_mcfg_bind` (bind congruence of
`interp_mcfg`, `I2F_interp.v:756`), `I2F_initial_FusedS` and `I2F_denote_vellvm`
(whole-program denotation refinement); a change to the denotation or the
interpreter monad has to be re-proven there, not in this glue.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/vellvm.yml (Vellvm Compilation Test) triggers on push to main (default branch) and builds rocq-vellvm.opam via 'make -C src all', which compiles src/rocq/Theory/I2F/I2F_toplevel.v; pinned commit e25dad9af33281b2edd3c16c027f3717546a09d7 is on the default branch | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: I2F_interpreter_gen@src/rocq/Theory/I2F/I2F_toplevel.v:462, I2F_build_main_args@src/rocq/Theory/I2F/I2F_toplevel.v:462; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at e25dad9af33281b2edd3c16c027f3717546a09d7 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(I2F_interpreter_param, src/rocq/Theory/I2F/I2F_toplevel.v, 455-463) -> declared: I2F_interpreter_param is declared at src/rocq/Theory/I2F/I2F_toplevel.v:455 | check_claims.py |
| 2 | verified | cites(parent, I2F_interpreter_gen) -> cites: I2F_interpreter_gen occurs at src/rocq/Theory/I2F/I2F_toplevel.v:462 | check_claims.py |
| 3 | verified | cites(parent, I2F_build_main_args) -> cites: I2F_build_main_args occurs at src/rocq/Theory/I2F/I2F_toplevel.v:462 | check_claims.py |
| 4 | verified | no_sorry(src/rocq/Theory/I2F/I2F_toplevel.v, 231-463) -> no_sorry: none of admit, Admitted, Axiom, axiom in src/rocq/Theory/I2F/I2F_toplevel.v:231-463 | check_claims.py |
| 5 | verified | Checked copied code src/rocq/Theory/I2F/I2F_toplevel.v: parent site L455-463 is 9 lines (Theorem I2F_interpreter_param, L462 'apply I2F_interpreter_gen, I2F_build_main_args.'); child I2F_interpreter_gen L437-453 is 17 lines (L452 'now apply I2F_denote_vellvm.'); child I2F_build_main_args L231-239 is 9 lines; I2F_denote_vellvm declared at L404 and applies I2F_denote_mcfg at L428 -> chain I2F_interpreter_param -> I2F_interpreter_gen -> I2F_denote_vellvm -> I2F_denote_mcfg is depth 3; 2 direct lemmas and site lengths 9/17/9 all match | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent I2F_interpreter_param (455-463) is proved by 'apply I2F_interpreter_gen, I2F_build_main_args', and interpreter_param is defined (TopLevel.v:328-332) as interpreter_gen (DTYPE_I 32) (Name main) (build_main_args args) prog, so the general-then-instantiate decomposition is exactly as stated. Children are verbatim: I2F_interpreter_gen (437-453) and I2F_build_main_args (231-239), and their closed_by matches the code (gen: eapply I2F_interp_mcfg_bind; apply I2F_initial_FusedS; now apply I2F_denote_vellvm; build_main_args: rbind I2F_dvalue; apply I2F_allocate_args; apply ruttc_ret; repeat constructor; auto). Both close with Qed; the glue's apply leaves exactly the I2F_build_main_args conclusion as the remaining premise, so it closes. The parent uses exactly these two lemmas. Shape numbers correct: glue_lines=9 (455-463), child_lines=[17,9] (437-453, 231-239), direct_lemmas=2, depth=3 (param->gen->denote_vellvm at 404-433 -> I2F_denote_mcfg applied at 428). | reviewer-correctness |
| generality | accept | Move stated beyond the example: applicability.goal_shape, use_when/avoid_when, and the 'When to use it, and when not' section generalise to 'any pure specialisation of a general refinement' rather than I2F alone; the saving criterion ('general statement no harder than special; instance helper easy') is concrete and matched by the code (arg_gen1/2 appear only as opaque values, the relation hypothesis being the sole premise). When-not-to-use is specific (three conditions: not a plain instantiation; premise as hard as target; hypothesis hard to discharge at the single use site) and honest; consequences name the single obligation, the fragility if the top-level did anything after interpreter_gen, and the strength limit (only as strong as I2F_interpreter_gen's dependencies). Good leaves are explained: each child closes from named siblings and never mentions the other child, so each is an independent bounded-prover hole (verified against sed of I2F_toplevel.v 231-239, 437-463 and TopLevel.v 313-332). Minor nit outside this lens: intent says 'one tactic line' while the glue is two (intros; apply). | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are consistent and traceable. check_provenance passes: 2 files byte-identical at e25dad9af33281b2edd3c16c027f3717546a09d7. Commit hash is identical across entry.json, README, source.json and SOURCE.md; all four site permalinks and both file permalinks pin the same commit and the cited line ranges (I2F_toplevel.v 231-239, 437-453, 455-463; TopLevel.v 313-332) reproduce the copied excerpts verbatim. Licence recorded as MIT in entry.json/README/source.json, and sources/vellvm/upstream-LICENSE.md (copied from LICENSE.md at the pinned commit) is the MIT text. Source note names the same commit and MIT licence. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/vellvm/vellvm at commit `e25dad9af33281b2edd3c16c027f3717546a09d7`, under `MIT`; see the [source note](../../sources/vellvm/SOURCE.md) for the licence text and attribution.
