# Per-field lemmas assemble the compiler_t record in generic_compiler

| | |
|---|---|
| Kind | instance |
| Move | per-callee-lemma |
| Language | rocq |
| Status | accepted |
| Source | [coq-library-undecidability](../../sources/coq-library-undecidability/SOURCE.md) at `c7257b736763` |
| Licence | `MPL-2.0` |
| Licence recorded | 2026-11-14T12:41:37Z |

## Intent

Build a value of the `compiler_t` record — whose four propositional fields are
the start-address, end-address, soundness and completeness obligations — by
proving each field as its own `Local Fact`, then closing all four at once with
a single `exists link code; auto.` whose `auto` resolves each field through a
`Hint Resolve`.

## The decomposition

### parent `generic_compiler`: [`theories/Shared/Libs/DLW/Code/compiler_correction.v` lines 309-312](https://github.com/uds-psl/coq-library-undecidability/blob/c7257b736763d7b2bc3bd25ac47d5fb7ce749c9c/theories/Shared/Libs/DLW/Code/compiler_correction.v#L309-L312) ([local copy](code/theories/Shared/Libs/DLW/Code/compiler_correction.v))

```coq
    Theorem generic_compiler : compiler_t.
    Proof using Hilen Hicomp step_Y_fun step_X_tot.
      exists link code; auto. 
    Defined.
```

### skeleton `hint-resolve`: [`theories/Shared/Libs/DLW/Code/compiler_correction.v` lines 307-307](https://github.com/uds-psl/coq-library-undecidability/blob/c7257b736763d7b2bc3bd25ac47d5fb7ce749c9c/theories/Shared/Libs/DLW/Code/compiler_correction.v#L307-L307) ([local copy](code/theories/Shared/Libs/DLW/Code/compiler_correction.v))

```coq
    Hint Resolve fst_ok out_ok sound complete : core.
```

### child `fst_ok`: [`theories/Shared/Libs/DLW/Code/compiler_correction.v` lines 271-272](https://github.com/uds-psl/coq-library-undecidability/blob/c7257b736763d7b2bc3bd25ac47d5fb7ce749c9c/theories/Shared/Libs/DLW/Code/compiler_correction.v#L271-L272) ([local copy](code/theories/Shared/Libs/DLW/Code/compiler_correction.v))

```coq
    Local Fact fst_ok : forall P i, link P i (fst P) = i.
    Proof. intros [] ?; apply linker_code_start. Qed.
```

### child `out_ok`: [`theories/Shared/Libs/DLW/Code/compiler_correction.v` lines 274-281](https://github.com/uds-psl/coq-library-undecidability/blob/c7257b736763d7b2bc3bd25ac47d5fb7ce749c9c/theories/Shared/Libs/DLW/Code/compiler_correction.v#L274-L281) ([local copy](code/theories/Shared/Libs/DLW/Code/compiler_correction.v))

```coq
    Local Fact out_ok : forall P i j, out_code j P -> link P i j = code_end(i,code P i).
    Proof using Hilen.
      intros (iP,cP) iQ j H.
      unfold link, code_end.
      rewrite linker_out_err; unfold err; simpl; auto.
      * unfold code; rewrite compiler_length; auto.
      * lia.
    Qed.
```

### child `sound`: [`theories/Shared/Libs/DLW/Code/compiler_correction.v` lines 283-287](https://github.com/uds-psl/coq-library-undecidability/blob/c7257b736763d7b2bc3bd25ac47d5fb7ce749c9c/theories/Shared/Libs/DLW/Code/compiler_correction.v#L283-L287) ([local copy](code/theories/Shared/Libs/DLW/Code/compiler_correction.v))

```coq
    Local Fact sound : forall P i, compiled_sound (link P i) P (i,code P i).
    Proof using Hilen Hicomp.
      intros (iP,cP) iQ; apply compiler_sound.
      intros; apply compiler_subcode; auto.
    Qed.
```

### child `complete`: [`theories/Shared/Libs/DLW/Code/compiler_correction.v` lines 289-305](https://github.com/uds-psl/coq-library-undecidability/blob/c7257b736763d7b2bc3bd25ac47d5fb7ce749c9c/theories/Shared/Libs/DLW/Code/compiler_correction.v#L289-L305) ([local copy](code/theories/Shared/Libs/DLW/Code/compiler_correction.v))

```coq
    Local Fact complete : forall P i, compiled_complete (link P i) P (i,code P i).
    Proof using Hilen Hicomp step_Y_fun step_X_tot.
      intros (iP,cP) iQ; unfold link, code.
      intros i1 v1 w1 j2 w2 H1.
      destruct compiler_complete' with (2 := H1) (P := (iP,cP))
        as (i2 & v2 & w2' & H2 & H3 & H4 & H5); auto.
      + intros; apply compiler_subcode; auto.
      + exists i2, v2.
        match type of H4 with _ /Y/ (?a,?b) ->> (?c,?d) => assert (a = c /\ b = d) as E end.
        1:{ apply sss_compute_stop in H4.
            * inversion H4; auto.
            * simpl fst.
              apply linker_out_code; auto.
              - right; unfold err; lia.
              - apply H3. }
        destruct E as [ E -> ]; auto.
    Qed.
```

How the parts fit. The goal `compiler_t` is a record (lines 252-259) whose
constructor `MkGenComp` takes two data fields — `gc_link`, `gc_code` — and four
propositional fields — `gc_fst`, `gc_out`, `gc_sound`, `gc_complete`. The glue
`exists link code; auto.` supplies the data fields as the explicit witnesses
`link` and `code` (the section `Let`s at lines 267-269), leaving the four
propositional fields as subgoals. `auto` closes each one because the preceding
skeleton line registered the four children in the `core` hint database:

```
generic_compiler  (309-312)
  └─ exists link code; auto.  —  fills gc_link := link, gc_code := code, then
     `auto` resolves the four fields via Hint Resolve (line 307):
        ├─ gc_fst      ← fst_ok   (271-272)  ── apply linker_code_start
        ├─ gc_out      ← out_ok   (274-281)  ── rewrite linker_out_err; compiler_length; lia
        ├─ gc_sound    ← sound    (283-287)  ── apply compiler_sound (143-163) + compiler_subcode
        └─ gc_complete ← complete (289-305)  ── compiler_complete' (230-244)
                                                 → compiler_complete (212-228)
                                                 → compiler_complete_step (168-208)
```

Each child is a good leaf because it is a self-contained statement whose proof
closes on its own or from a named sibling proved earlier in the same file:

- `fst_ok` states that the linker maps the source program's start address to
  the compiled entry address, and closes in one line by `apply
  linker_code_start` (a library lemma about `linker`).
- `out_ok` states that at an exit position of `P` the linker points to the end
  of the compiled code, and closes by `rewrite linker_out_err` plus the length
  lemma `compiler_length`, the remaining arithmetic discharged by `lia`.
- `sound` states `compiled_sound` for the concrete linker and code, and closes
  by delegating to the abstract soundness theorem `compiler_sound` (proved at
  143-163), using `compiler_subcode` to discharge the syntactic side condition
  `HPQ`. Its proof is two tactic lines.
- `complete` states `compiled_complete` for the concrete linker and code, and
  closes by delegating to `compiler_complete'` (the corollary at 230-244),
  itself built on `compiler_complete` (212-228) and its step lemma
  `compiler_complete_step` (168-208). This is the longest chain below the main
  theorem: `complete → compiler_complete' → compiler_complete →
  compiler_complete_step` (depth 4).

Note the direction of dependency: the four `Local Fact`s are proved *before* the
record is assembled, and the skeleton line `Hint Resolve ... : core.` is what
turns "one lemma per field" into a one-line record assembly. The `auto` in the
glue resolves the fields in the record's field order, which is how `fst_ok`
closes `gc_fst`, `out_ok` closes `gc_out`, and so on.

## Why it is good

1. The parent site (`generic_compiler`) is 4 lines long — the entire record
   assembly is the single line `exists link code; auto.` (claim 1, check).
2. No `admit`, `Admitted` or `Axiom` appears anywhere in the compiler section,
   lines 168-312 — the four fields and the glue close without a hole (claim 2,
   check).
3. The decomposition is theorem-scale with 4 direct lemmas, a 4-line glue, and
   children of 2/8/5/17 lines, the deepest lemma chain below the theorem being
   `complete → compiler_complete' → compiler_complete →
   compiler_complete_step` (claim 3, measurement).
4. The authors frame the argument as two halves — "soundness and completeness of
   the compiled program Q wrt the source program P" — matching the `sound` and
   `complete` children (claim 4, author-statement).
5. The same record assembly is reused in `compiler_t_simul_equiv` (lines
   375-390), where `exists gc_link gc_code; auto.` assembles the record a second
   time (claim 5, known-use).

In my opinion the detail worth copying is the `Hint Resolve` line: it is what
makes "one lemma per record field" collapse into a single `auto`. Without it,
the glue would have to name each field's lemma explicitly, and the one-line
assembly would not go through.

## When to use it, and when not

Use it when the goal is to inhabit a record or structure with a small, fixed set
of propositional fields whose statements are independent — each can be stated
and proved as its own lemma — and when the record is assembled more than once so
the per-field lemmas pay for themselves. The assembly is then a uniform
`exists <ctor args>; auto` with the per-field lemmas registered in a `Hint
Resolve` database.

Avoid it when the fields share an invariant that must be threaded from one to
the next (then a single `key-invariant` lemma carries the argument better than
four leaves), when one field's proof needs another field's statement, or when
the hint database is too broad for `auto` to resolve the fields reliably.

## Consequences

The move turns the record into one obligation per propositional field, each
closed by a named `Local Fact`, so the parent is a bare `exists link code;
auto.`. It creates a hidden dependency: `auto` discharges the fields only
because `Hint Resolve fst_ok out_ok sound complete : core.` (line 307)
registered them, so removing the hint silently breaks the glue. It also obscures
which lemma closes which field — the reader must consult the record's field
order (lines 252-259) to map `fst_ok → gc_fst`, `out_ok → gc_out`, `sound →
gc_sound`, `complete → gc_complete`. Failure modes: a field whose statement is
not exactly the record field's type will not resolve under `auto`;
interdependent fields cannot be split into independent leaves.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml (coq-library-undecidability CI) runs 'opam exec -- make -j 2 all TIMED=1' (Rocq 9.2) on default branch rocq-9.2; theories/_CoqProject explicitly lists Shared/Libs/DLW/Code/compiler_correction.v; pinned commit c7257b736763d7b2bc3bd25ac47d5fb7ce749c9c is head of rocq-9.2 | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: fst_ok@theories/Shared/Libs/DLW/Code/compiler_correction.v:307, out_ok@theories/Shared/Libs/DLW/Code/compiler_correction.v:307, sound@theories/Shared/Libs/DLW/Code/compiler_correction.v:307, complete@theories/Shared/Libs/DLW/Code/compiler_correction.v:307; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at c7257b736763d7b2bc3bd25ac47d5fb7ce749c9c | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(parent, 4) -> lines: site parent has 4 lines | check_claims.py |
| 2 | verified | no_sorry(theories/Shared/Libs/DLW/Code/compiler_correction.v, 168-312) -> no_sorry: none of admit, Admitted, Axiom, axiom in theories/Shared/Libs/DLW/Code/compiler_correction.v:168-312 | check_claims.py |
| 3 | verified | Copied file line numbers confirm: parent 309-312 = 4 lines (309 Theorem generic_compiler, 310 Proof using, 311 'exists link code; auto.', 312 Defined); children 271-272 (2), 274-281 (8), 283-287 (5), 289-305 (17); chain: complete@293 'destruct compiler_complete''', compiler_complete'@236 'destruct compiler_complete', compiler_complete@220 'destruct compiler_complete_step' (depth 4) | verifier |
| 4 | verified | Lines 134-137 comment verbatim: 'From semantic correctness of individually compiled instructions and syntactic correctness of the whole compiled program, we derive soundness and completeness of the compiled program Q wrt the source program P' | verifier |
| 5 | verified | Lines 375-390: Theorem compiler_t_simul_equiv; 380 'intros E [ gc_link gc_code gc_fst gc_out gc_sound gc_complete ].' destructs the record; 381 'exists gc_link gc_code; auto.'; two non-auto fields proved explicitly: gc_sound (382-385) and gc_complete (386-389) | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent (309-312) is exactly 'Theorem generic_compiler : compiler_t.' with body 'exists link code; auto.'; skeleton (307) is the Hint Resolve registering all four children; children fst_ok/out_ok/sound/complete (271-272,274-281,283-287,289-305) have statements and closing tactics matching entry.json, and their statements are exactly the four propositional record fields after gc_link:=link, gc_code:=code, so auto closes each via the hint and the proof is Defined (no admit). Shape numbers confirmed: glue_lines=4, child_lines=[2,8,5,17], direct_lemmas=4, depth=4 (complete->compiler_complete' at 293->236->compiler_complete at 220->compiler_complete_step). | reviewer-correctness |
| generality | accept | Move stated generally: one lemma per propositional field of a record, registered in a Hint Resolve db, closed by a single exists/auto — 'When to use' and applicability.use_when abstract to any record/structure with a small fixed set of independent propositional fields, not just compiler_t. Avoid-when is specific and honest (shared invariant -> key-invariant; one field's proof needs another's statement; hint db too broad for auto). Consequences are honest and specific (hidden Hint Resolve dependency breaks glue silently; field-order obscures which lemma closes which field; exact-type-match and independence failure modes). Says what makes leaves good for a bounded prover: self-contained statements closing on their own or from a named sibling, quantified (1/8/5/17 proof lines; 4 children closed by automation). Minor caveat, not blocking: known-use at 375-390 is a parameterized compiler_t where auto closes only the 2 sim-independent fields (2 explicit), and the four Local Facts are used once, so 'per-field lemmas pay for themselves' is aspirational rather than demonstrated by this example. | reviewer-generality |
| provenance-licence | accept | Provenance is fully consistent and traceable. check_provenance.py passes (1 file byte-identical at c7257b736763d7b2bc3bd25ac47d5fb7ce749c9c). Copied file sha256 4e3719b0... matches entry.json files[0].sha256 and bytes 17450 matches. Commit c7257b7... is identical in entry.json source.commit, SOURCE.md, and every permalink. Licence MPL-2.0 is consistent across entry.json, README, SOURCE.md, and sources/coq-library-undecidability/upstream-LICENSE (Mozilla Public License Version 2.0). All cited line ranges verified verbatim in the copied file (parent 309-312, skeleton 307, children 271-272/274-281/283-287/289-305, record 252-259, Lets 267-269, author-statement 134-137, known-use 375-390). | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/uds-psl/coq-library-undecidability at commit `c7257b736763d7b2bc3bd25ac47d5fb7ce749c9c`, under `MPL-2.0`; see the [source note](../../sources/coq-library-undecidability/SOURCE.md) for the licence text and attribution.
