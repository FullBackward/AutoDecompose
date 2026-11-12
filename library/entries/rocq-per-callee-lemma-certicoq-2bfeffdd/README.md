# One simulation lemma per evaluation rule for the LambdaANF-to-Wasm correctness theorem

| | |
|---|---|
| Kind | instance |
| Move | per-callee-lemma |
| Language | rocq |
| Status | accepted |
| Source | [certicoq](../../sources/certicoq/SOURCE.md) at `943b52ae6547` |
| Licence | `MIT` |

## Intent

Prove the Wasm backend's main correctness theorem — every LambdaANF evaluation
`bstep_e pfs cenv rho e v n` is simulated by a related Wasm execution
(`bs_wasm_related`) — by induction on the source derivation, delegating each of
the nine evaluation rules to its own self-contained lemma that carries the
induction hypothesis as an explicit premise.

## The decomposition

### parent `repr_bs_LambdaANF_Wasm_related`: [`theories/CodegenWasm/LambdaANF_to_Wasm_correct.v` lines 6030-6047](https://github.com/CertiCoq/certicoq/blob/943b52ae654708130f241ccf8a50ecb95a7956e2/theories/CodegenWasm/LambdaANF_to_Wasm_correct.v#L6030-L6047) ([local copy](code/theories/CodegenWasm/LambdaANF_to_Wasm_correct.v))

```coq
Theorem repr_bs_LambdaANF_Wasm_related : forall pfs fds,
  bs_wasm_assumptions pfs fds ->
  forall (rho : eval.env) (e : exp) (v : term.val) (n : nat),
    bstep_e pfs cenv rho e v n ->
    bs_wasm_related fds rho e v.
Proof.
  intros pfs fds Hassms rho e v n Hev.
  induction Hev.
  - eapply bs_wasm_related_Econstr; eassumption.
  - eapply bs_wasm_related_Eproj; eassumption.
  - eapply bs_wasm_related_Ecase; eassumption.
  - eapply bs_wasm_related_Eapp; eassumption.
  - eapply bs_wasm_related_Eletapp; eassumption.
  - eapply bs_wasm_related_Efun; eassumption.
  - eapply bs_wasm_related_Eprim_val; eassumption.
  - eapply bs_wasm_related_Eprim; eassumption.
  - eapply bs_wasm_related_Ehalt; eassumption.
Qed.
```

### child `bs_wasm_related_Econstr`: [`theories/CodegenWasm/LambdaANF_to_Wasm_correct.v` lines 3800-3808](https://github.com/CertiCoq/certicoq/blob/943b52ae654708130f241ccf8a50ecb95a7956e2/theories/CodegenWasm/LambdaANF_to_Wasm_correct.v#L3800-L3808) ([local copy](code/theories/CodegenWasm/LambdaANF_to_Wasm_correct.v))

```coq
Lemma bs_wasm_related_Econstr : forall pfs fds,
  bs_wasm_assumptions pfs fds ->
  forall (x : term.var) (t : term.ctor_tag) (ys : list term.var) (e : exp)
         (rho rho' : eval.env) (vs : list term.val) (v : term.val) (c : nat),
    get_list ys rho = Some vs ->
    M.set x (Vconstr t vs) rho = rho' ->
    bstep_e pfs cenv rho' e v c ->
    bs_wasm_related fds rho' e v ->
    bs_wasm_related fds rho (Econstr x t ys e) v.
```

### child `bs_wasm_related_Eproj`: [`theories/CodegenWasm/LambdaANF_to_Wasm_correct.v` lines 4206-4214](https://github.com/CertiCoq/certicoq/blob/943b52ae654708130f241ccf8a50ecb95a7956e2/theories/CodegenWasm/LambdaANF_to_Wasm_correct.v#L4206-L4214) ([local copy](code/theories/CodegenWasm/LambdaANF_to_Wasm_correct.v))

```coq
Lemma bs_wasm_related_Eproj : forall pfs fds,
  bs_wasm_assumptions pfs fds ->
  forall (t : term.ctor_tag) (vs : list term.val) (v : term.val) (rho : eval.env)
         (x : term.var) (n : N) (y : term.var) (e : exp) (ov : term.val) (c : nat),
    M.get y rho = Some (Vconstr t vs) ->
    nthN vs n = Some v ->
    bstep_e pfs cenv (M.set x v rho) e ov c ->
    bs_wasm_related fds (M.set x v rho) e ov ->
    bs_wasm_related fds rho (Eproj x t n y e) ov.
```

### child `bs_wasm_related_Ecase`: [`theories/CodegenWasm/LambdaANF_to_Wasm_correct.v` lines 4393-4402](https://github.com/CertiCoq/certicoq/blob/943b52ae654708130f241ccf8a50ecb95a7956e2/theories/CodegenWasm/LambdaANF_to_Wasm_correct.v#L4393-L4402) ([local copy](code/theories/CodegenWasm/LambdaANF_to_Wasm_correct.v))

```coq
Lemma bs_wasm_related_Ecase : forall pfs fds,
  bs_wasm_assumptions pfs fds ->
  forall (y : term.var) (v : term.val) (e : exp) (t : term.ctor_tag)
         (cl : list (term.ctor_tag * exp)) (vl : list term.val) (rho : eval.env) (c : nat),
    M.get y rho = Some (Vconstr t vl) ->
    caseConsistent cenv cl t ->
    findtag cl t = Some e ->
    bstep_e pfs cenv rho e v c ->
    bs_wasm_related fds rho e v ->
    bs_wasm_related fds rho (Ecase y cl) v.
```

### child `bs_wasm_related_Eapp`: [`theories/CodegenWasm/LambdaANF_to_Wasm_correct.v` lines 4598-4609](https://github.com/CertiCoq/certicoq/blob/943b52ae654708130f241ccf8a50ecb95a7956e2/theories/CodegenWasm/LambdaANF_to_Wasm_correct.v#L4598-L4609) ([local copy](code/theories/CodegenWasm/LambdaANF_to_Wasm_correct.v))

```coq
Lemma bs_wasm_related_Eapp : forall pfs fds,
  bs_wasm_assumptions pfs fds ->
  forall (rho' : eval.env) (fl : fundefs) (f' : term.var) (vs : list term.val)
         (xs : list term.var) (e : exp) (rho'' rho : eval.env) (f : term.var)
         (t : term.ctor_tag) (ys : list term.var) (v : term.val) (c : nat),
    M.get f rho = Some (Vfun rho' fl f') ->
    get_list ys rho = Some vs ->
    find_def f' fl = Some (t, xs, e) ->
    set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
    bstep_e pfs cenv rho'' e v c ->
    bs_wasm_related fds rho'' e v ->
    bs_wasm_related fds rho (Eapp f t ys) v.
```

### child `bs_wasm_related_Eletapp`: [`theories/CodegenWasm/LambdaANF_to_Wasm_correct.v` lines 4882-4896](https://github.com/CertiCoq/certicoq/blob/943b52ae654708130f241ccf8a50ecb95a7956e2/theories/CodegenWasm/LambdaANF_to_Wasm_correct.v#L4882-L4896) ([local copy](code/theories/CodegenWasm/LambdaANF_to_Wasm_correct.v))

```coq
Lemma bs_wasm_related_Eletapp : forall pfs fds,
  bs_wasm_assumptions pfs fds ->
  forall (rho' : eval.env) (fl : fundefs) (f' : term.var) (vs : list term.val)
         (xs : list term.var) (e_body e : exp) (rho'' rho : eval.env)
         (x f : term.var) (t : term.ctor_tag) (ys : list term.var)
         (v v' : term.val) (c c' : nat),
    M.get f rho = Some (Vfun rho' fl f') ->
    get_list ys rho = Some vs ->
    find_def f' fl = Some (t, xs, e_body) ->
    set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
    bstep_e pfs cenv rho'' e_body v c ->
    bs_wasm_related fds rho'' e_body v ->
    bstep_e pfs cenv (M.set x v rho) e v' c' ->
    bs_wasm_related fds (M.set x v rho) e v' ->
    bs_wasm_related fds rho (Eletapp x f t ys e) v'.
```

### child `bs_wasm_related_Efun`: [`theories/CodegenWasm/LambdaANF_to_Wasm_correct.v` lines 5410-5415](https://github.com/CertiCoq/certicoq/blob/943b52ae654708130f241ccf8a50ecb95a7956e2/theories/CodegenWasm/LambdaANF_to_Wasm_correct.v#L5410-L5415) ([local copy](code/theories/CodegenWasm/LambdaANF_to_Wasm_correct.v))

```coq
Lemma bs_wasm_related_Efun : forall pfs fds,
  bs_wasm_assumptions pfs fds ->
  forall (rho : eval.env) (fl : fundefs) (e : exp) (v : term.val) (c : nat),
    bstep_e pfs cenv (def_funs fl fl rho rho) e v c ->
    bs_wasm_related fds (def_funs fl fl rho rho) e v ->
    bs_wasm_related fds rho (Efun fl e) v.
```

### child `bs_wasm_related_Eprim_val`: [`theories/CodegenWasm/LambdaANF_to_Wasm_correct.v` lines 5426-5432](https://github.com/CertiCoq/certicoq/blob/943b52ae654708130f241ccf8a50ecb95a7956e2/theories/CodegenWasm/LambdaANF_to_Wasm_correct.v#L5426-L5432) ([local copy](code/theories/CodegenWasm/LambdaANF_to_Wasm_correct.v))

```coq
Lemma bs_wasm_related_Eprim_val : forall pfs fds,
  bs_wasm_assumptions pfs fds ->
  forall (rho' rho : eval.env) (x : term.var) p (e : exp) (v : term.val) (c : nat),
    M.set x (Vprim p) rho = rho' ->
    bstep_e pfs cenv rho' e v c ->
    bs_wasm_related fds rho' e v ->
    bs_wasm_related fds rho (Eprim_val x p e) v.
```

### child `bs_wasm_related_Eprim`: [`theories/CodegenWasm/LambdaANF_to_Wasm_correct.v` lines 5771-5782](https://github.com/CertiCoq/certicoq/blob/943b52ae654708130f241ccf8a50ecb95a7956e2/theories/CodegenWasm/LambdaANF_to_Wasm_correct.v#L5771-L5782) ([local copy](code/theories/CodegenWasm/LambdaANF_to_Wasm_correct.v))

```coq
Lemma bs_wasm_related_Eprim : forall pfs fds,
  bs_wasm_assumptions pfs fds ->
  forall (vs : list term.val) (rho' rho : eval.env) (x : term.var) (f : term.prim)
         (f' : list term.val -> option term.val) (ys : list term.var) (e : exp)
         (v v' : term.val) (c : nat),
    get_list ys rho = Some vs ->
    M.get f pfs = Some f' ->
    f' vs = Some v ->
    M.set x v rho = rho' ->
    bstep_e pfs cenv rho' e v' c ->
    bs_wasm_related fds rho' e v' ->
    bs_wasm_related fds rho (Eprim x f ys e) v'.
```

### context `bs_wasm_related_definition`: [`theories/CodegenWasm/LambdaANF_to_Wasm_correct.v` lines 3739-3741](https://github.com/CertiCoq/certicoq/blob/943b52ae654708130f241ccf8a50ecb95a7956e2/theories/CodegenWasm/LambdaANF_to_Wasm_correct.v#L3739-L3741) ([local copy](code/theories/CodegenWasm/LambdaANF_to_Wasm_correct.v))

```coq
(* The main correctness theorem below is proved by induction on [bstep_e].  The
   per-constructor lemmas and the induction hypotheses all share this statement. *)
Definition bs_wasm_related (fds : fundefs) (rho : eval.env) (e : exp) (v : term.val) : Prop :=
```

How the parts fit. `bstep_e pfs cenv rho e v n` is the big-step operational
semantics of the source language; its nine constructors are `Econstr`,
`Eproj`, `Ecase`, `Eapp`, `Eletapp`, `Efun`, `Eprim_val`, `Eprim`, `Ehalt`.
`bs_wasm_related` (defined just above the theorem, lines 3741-3789) is a single
uniform predicate: a conjunction of preconditions (globally unique variables,
`expression_restricted`, SSA form, environment translation, an invariant) that
imply the existence of a related Wasm execution producing `v`.

The parent is a pure dispatcher. `induction Hev.` produces one goal per
constructor, and each is closed by `eapply bs_wasm_related_E<ctor>;
eassumption.`. The name after `eapply` is the whole argument: the matching
per-constructor lemma has exactly that constructor's premises plus — crucially —
the induction hypothesis as an explicit premise `bs_wasm_related fds … e v ->`
(visible in every child statement above). `eassumption` then discharges
`bs_wasm_assumptions pfs fds`, which the parent holds as `Hassms`.

The lemma graph is flat: each child closes on its own and none calls another
(grep for `bs_wasm_related_E` returns only the nine declarations and the nine
parent dispatches).

```text
repr_bs_LambdaANF_Wasm_related
 ├─ bs_wasm_related_Econstr    (case Econstr)
 ├─ bs_wasm_related_Eproj      (case Eproj)
 ├─ bs_wasm_related_Ecase      (case Ecase)
 ├─ bs_wasm_related_Eapp       (case Eapp)
 ├─ bs_wasm_related_Eletapp    (case Eletapp)
 ├─ bs_wasm_related_Efun       (case Efun)
 ├─ bs_wasm_related_Eprim_val  (case Eprim_val)
 ├─ bs_wasm_related_Eprim      (case Eprim)
 └─ bs_wasm_related_Ehalt      (case Ehalt, base case: no sub-derivation, no IH premise)
```

The ninth direct lemma, `bs_wasm_related_Ehalt`, is the terminating base case
(no recursive sub-expression, so no IH premise). It is recorded in
`entry.json → children` but not shown as a child site here; its full statement
and proof are at
[`LambdaANF_to_Wasm_correct.v` lines 5957-6027](https://github.com/CertiCoq/certicoq/blob/943b52ae654708130f241ccf8a50ecb95a7956e2/theories/CodegenWasm/LambdaANF_to_Wasm_correct.v#L5957-L6027).

Why each child is a good leaf. Each child states, for one constructor, "if the
sub-evaluation(s) are related (the IH premise(s)), then the whole expression is
related". The statement is self-contained: it carries `bs_wasm_assumptions` and
the entire `bs_wasm_related` preamble, so its proof needs nothing from the
parent. Each proof closes on its own from the translation relation
`repr_expr_LambdaANF_Wasm` (inverted via `inversion Hrepr_e` to recover the
exact Wasm instruction sequence for that constructor) plus the Wasm
step-semantics lemmas; the IH premise is applied with `apply Hred` (in
`Eletapp`, the two IH premises via `apply Hred` and `eapply rt_trans; apply
Hred_final`). Two leaves are degenerate: `Efun` closes by `inv Hrepr_e.` alone
(an `Efun` is never translated below the top level, so the hypothesis is
contradictory — see the in-proof comment "absurd, fn defs only on topmost
level"), and `Ehalt` is the base case with no IH.

## Why it is good

1. **Check** — the parent is closed in 12 lines, all of them dispatch:
   `induction Hev.` plus nine `eapply bs_wasm_related_E<ctor>; eassumption.`
   bullets, one per evaluation rule, ending in `Qed.` (lines 6036-6047).
2. **Measurement** — 9 direct lemmas, depth 1 (no child uses another child),
   12 lines of glue, and child proof lengths 396 / 177 / 194 / 271 / 512 / 9 /
   337 / 173 lines for the eight shown children (counted from `Proof with
   eauto.` through `Qed.` inclusive).
3. **Author-statement** — the authors name the plan in a comment: "The main
   correctness theorem below is proved by induction on [bstep_e]. The
   per-constructor lemmas and the induction hypotheses all share this
   statement." (lines 3739-3741).
4. **Known-use** — the generalized theorem is the interface consumed by the
   top-level correctness statement: `toplevel_theorem.v` instantiates it with
   `have HMAIN := repr_bs_LambdaANF_Wasm_related …` (line 258).

In my opinion the detail worth copying is that the induction hypothesis is
*written into the lemma statement* as an ordinary premise, rather than left
implicit. That single choice is what makes the parent a pure dispatcher and
each leaf provable in isolation, and it is the authors' own words above that
call it out.

## When to use it, and when not

Use it when you are proving a statement `P e v` for every derivation of an
inductively-defined relation with one constructor per syntactic form, and the
relation you are establishing is defined uniformly (here `bs_wasm_related` is a
single `Definition`, so every per-constructor lemma shares the same conclusion
and the IH can be a plain premise). It is the standard shape for
compiler/simulation correctness proofs (CompCert's per-pass simulation lemmas
are the same idea at pass granularity). Avoid it when the invariant is not a
uniform predicate over sub-derivations, when the rules genuinely need different
statements, or when a per-case proof needs facts proved inside a sibling's
proof — then the near-identical-lemma factor disappears and the mechanical
dispatch breaks.

## Consequences

The move creates one leaf per constructor (9 here), each carrying the induction
hypothesis as an explicit premise, so the parent is pure dispatch and every
leaf is provable in isolation. The cost is a fixed, repeated preamble:
`bs_wasm_assumptions pfs fds` and the whole `bs_wasm_related` hypothesis
structure are copied verbatim into every lemma's statement, so changing the
invariant means editing all 9 statements. The parent has no independent
content: if a child's statement is wrong the parent still compiles and
dispatches, so correctness rests entirely on the children. Failure mode: when
the invariant must be strengthened for one rule only, the uniform-statement
premise breaks and the per-callee factoring stops paying (the lemma statements
diverge).

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/nix-action-default.yml: CertiRocq job builds the full project (theories/CodegenWasm listed in _CoqProject) on push to main; pinned commit 943b52a is identical to main HEAD | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 2 file(s) byte-identical at 943b52ae654708130f241ccf8a50ecb95a7956e2 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Local copy (byte-identical) lines 6030-6047: Proof block 6036-6047 = intros; induction Hev.; nine 'eapply bs_wasm_related_E(ctor); eassumption.' bullets (6038-6046), Qed at 6047 with no goal left; the 9 lemma names match the 9 bstep_e constructors | verifier |
| 2 | verified | grep bs_wasm_related_E returns 9 Lemma declarations (L3800,4206,4393,4598,4882,5410,5426,5771,5957) plus the 9 parent dispatches only (depth 1); Proof/Qed spans 3809-4204=396, 4215-4391=177, 4403-4596=194, 4610-4880=271, 4897-5408=512, 5416-5424=9, 5433-5769=337, 5783-5955=173 | verifier |
| 3 | verified | Comment at lines 3739-3740 reads verbatim: 'The main correctness theorem below is proved by induction on [bstep_e]. The per-constructor lemmas and the induction hypotheses all share this statement.' | verifier |
| 4 | verified | toplevel_theorem.v line 258 instantiates repr_bs_LambdaANF_Wasm_related via 'have HMAIN := repr_bs_LambdaANF_Wasm_related cenv fenv penv _ _ Hassms ...' (lines 258-261) | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent theorem (L6030-6047) closes in 12 proof lines: induction Hev. then nine eapply bs_wasm_related_E<ctor>; eassumption. bullets, ending Qed.; the 9 eapply targets are exactly the 9 children listed (Econstr, Eproj, Ecase, Eapp, Eletapp, Efun, Eprim_val, Eprim, Ehalt), with no other lemma used. All 9 child statements in entry.json match the code verbatim, and each child proof ends in Qed (L4204, 4391, 4596, 4880, 5408, 5424, 5769, 5955, 6027); grep finds no admit/Admitted/axiom. Shape numbers verified: direct_lemmas=9 (grep bs_wasm_related_E returns exactly 9 declarations + 9 parent dispatches, depth 1), glue_lines=12 (L6036-6047), child_lines [396,177,194,271,512,9,337,173] match Proof..Qed ranges L3809-4204 etc., and Ehalt=66 (L5962-6027). Closing methods match: inversion Hrepr_e, memory_grow_reduce, r_load_success, r_call/r_invoke_native, apply Hred / rt_trans-apply Hred_final, inv Hrepr_e (Efun). Claim 4 known-use confirmed at toplevel_theorem.v L258. Provenance pass (2 files byte-identical). | reviewer-correctness |
| generality | accept | Generality holds. The move is stated beyond the example: applicability.goal_shape abstracts to 'a theorem about every derivation of an inductively-defined relation with one constructor per syntactic form, each constructor becoming one lemma with the IH as explicit premise', and also_known_as/use_when map it to the standard CompCert per-pass simulation shape. avoid_when and consequences are honest and specific, and I confirmed them against the copied code: every child statement repeats the bs_wasm_assumptions/bs_wasm_related preamble (so editing the invariant touches all 9), the parent is pure dispatch (verified lines 6030-6047), and the failure mode (per-rule invariant strengthening diverges the statements) is real. The 'Why each child is a good leaf' section names what makes the leaves bounded-prover-friendly: self-contained statement carrying assumptions + IH premise, closing on its own from inversion + step lemmas. | reviewer-generality |
| provenance-licence | accept | Provenance check passes: 2 files byte-identical at pinned commit 943b52ae654708130f241ccf8a50ecb95a7956e2 (theories/CodegenWasm/LambdaANF_to_Wasm_correct.v, theories/CodegenWasm/toplevel_theorem.v). Commit is recorded consistently across entry.json source.commit, sources.jsonl, source.json, and SOURCE.md. Licence MIT is consistent: entry.json licence=MIT, source.json licence=MIT, SOURCE.md 'MIT', and upstream-LICENSE.md contains verbatim MIT text (copyright lines + MIT permission grant). Permalinks all use the pinned commit and paths matching the copied files; source URL https://github.com/CertiCoq/certicoq matches. README source-note links resolve to ../../sources/certicoq/SOURCE.md which carries the licence file and attribution. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/CertiCoq/certicoq at commit `943b52ae654708130f241ccf8a50ecb95a7956e2`, under `MIT`; see the [source note](../../sources/certicoq/SOURCE.md) for the licence text and attribution.
