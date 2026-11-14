# WordByWordMontgomery mulmod_correct from the stronger raw congruence mulmod_correct0

| | |
|---|---|
| Kind | instance |
| Move | suffices-or-strengthen |
| Language | rocq |
| Status | accepted |
| Source | [fiat-crypto](../../sources/fiat-crypto/SOURCE.md) at `3d2880ef2803` |
| Licence | `MIT OR Apache-2.0 OR BSD-1-Clause` |

## Intent

`mulmod_correct` states the interface for Montgomery multiplication in
`from_montgomerymod` form: the product of the wrapped values, and the validity
of `mulmod a b`. The proof does not re-run the reduction. It rewrites the
wrapper away with `eval_from_montgomerymod` and reduces to `mulmod_correct0`,
the stronger, raw congruence about `eval (mulmod a b)` that is already proved.
That is the `suffices-or-strengthen` move: prove the raw statement first, then
derive the wrapped interface from it.

## The decomposition

### parent `mulmod_correct`: [`src/Arithmetic/WordByWordMontgomery.v` lines 1156-1167](https://github.com/mit-plv/fiat-crypto/blob/3d2880ef2803faa9385589a81a835d5828eb3d38/src/Arithmetic/WordByWordMontgomery.v#L1156-L1167) ([local copy](code/src/Arithmetic/WordByWordMontgomery.v))

```coq
    Lemma mulmod_correct
      : (forall a (_ : valid a) b (_ : valid b), eval (from_montgomerymod (mulmod a b)) mod m
                                            = (eval (from_montgomerymod a) * eval (from_montgomerymod b)) mod m)
        /\ (forall a (_ : valid a) b (_ : valid b), valid (mulmod a b)).
    Proof using r'_correct r' n_nz m_small m_big m'_correct bitwidth_big.
      repeat rapply conj; intros;
        push_Zmod; rewrite ?eval_from_montgomerymod; pull_Zmod; repeat rapply conj;
          try apply mulmod_correct0; cbv [valid] in *; destruct_head'_and; auto; [].
      rewrite !Z.mul_assoc.
      rapply Z.mul_mod_Proper; [ | reflexivity ].
      cbv [Z.equiv_modulo]; etransitivity; [ (*proj*)apply mulmod_correct0 | rapply @f_equal2; lia ]; auto.
    Qed.
```

### child `mulmod_correct0`: [`src/Arithmetic/WordByWordMontgomery.v` lines 1095-1107](https://github.com/mit-plv/fiat-crypto/blob/3d2880ef2803faa9385589a81a835d5828eb3d38/src/Arithmetic/WordByWordMontgomery.v#L1095-L1107) ([local copy](code/src/Arithmetic/WordByWordMontgomery.v))

```coq
    Lemma mulmod_correct0
      : forall a b : list Z,
        small a -> small b
        -> small (mulmod a b)
          /\ (eval b < m -> 0 <= eval (mulmod a b) < m)
          /\ (eval (mulmod a b) mod m = (eval a * eval b * r'^n) mod m).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      intros a b Ha Hb; repeat rapply conj; cbv [small mulmod eval];
        [ rapply small_redc
        | rewrite m_enc_correct_montgomery; rapply redc_bound_N
        | rewrite !m_enc_correct_montgomery; rapply redc_mod_N ];
        t_fin.
    Qed.
```

### child `eval_from_montgomerymod`: [`src/Arithmetic/WordByWordMontgomery.v` lines 1146-1149](https://github.com/mit-plv/fiat-crypto/blob/3d2880ef2803faa9385589a81a835d5828eb3d38/src/Arithmetic/WordByWordMontgomery.v#L1146-L1149) ([local copy](code/src/Arithmetic/WordByWordMontgomery.v))

```coq
    Lemma eval_from_montgomerymod (v : list Z) : valid v -> eval (from_montgomerymod v) mod m = (eval v * r'^n) mod m.
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      intros; (*proj*)apply from_montgomerymod_correct; assumption.
    Qed.
```

### context `from_montgomerymod`: [`src/Arithmetic/WordByWordMontgomery.v` lines 1133-1134](https://github.com/mit-plv/fiat-crypto/blob/3d2880ef2803faa9385589a81a835d5828eb3d38/src/Arithmetic/WordByWordMontgomery.v#L1133-L1134) ([local copy](code/src/Arithmetic/WordByWordMontgomery.v))

```coq
    Definition from_montgomerymod (v : list Z) : list Z
      := mulmod v onemod.
```

### context `mulmod-and-valid`: [`src/Arithmetic/WordByWordMontgomery.v` lines 1084-1093](https://github.com/mit-plv/fiat-crypto/blob/3d2880ef2803faa9385589a81a835d5828eb3d38/src/Arithmetic/WordByWordMontgomery.v#L1084-L1093) ([local copy](code/src/Arithmetic/WordByWordMontgomery.v))

```coq
    Definition mulmod (a b : list Z) : list Z := @redc bitwidth n m_enc n a b m'.
    Definition redc_step (b s : list Z) (a : Z) : list Z := @redc_body_alt bitwidth n m_enc b m' (a, s).
    Definition squaremod (a : list Z) : list Z := mulmod a a.
    Definition addmod (a b : list Z) : list Z := @add bitwidth n m_enc a b.
    Definition submod (a b : list Z) : list Z := @sub bitwidth n m_enc a b.
    Definition oppmod (a : list Z) : list Z := @opp bitwidth n m_enc a.
    Definition nonzeromod (a : list Z) : Z := @nonzero a.
    Definition to_bytesmod (a : list Z) : list Z := @to_bytesmod bitwidth 1 (2^Z.log2_up m) n a.

    Definition valid (a : list Z) := small a /\ 0 <= eval a < m.
```

How the parts fit. The lemma graph, in text (an arrow `A -> B` reads "the proof
of A applies B"):

```
mulmod_correct (parent, 1156-1167)
├─> eval_from_montgomerymod          (rewrite ?eval_from_montgomerymod, line 1162)
│     └─> from_montgomerymod_correct (apply, line 1148)
│           ├─> mulmod_correct0      (apply, line 1143)
│           └─> onemod_correct       (apply, line 1143)
└─> mulmod_correct0                  (try apply, line 1163; apply inside etransitivity, line 1166)
      ├─> small_redc                 (rapply, line 1103)
      ├─> m_enc_correct_montgomery; redc_bound_N  (line 1104)
      └─> m_enc_correct_montgomery; redc_mod_N    (line 1105)
```

The glue works in two passes. First `repeat rapply conj; intros` turns the
top-level conjunction into two goals, one per conjunct, and the second conjunct
(validity of `mulmod a b`) is discharged by `try apply mulmod_correct0` after
unfolding `valid`. The first conjunct (value equality) is then rewritten with
`eval_from_montgomerymod` on both sides, so the wrapper disappears and the goal
becomes the raw congruence, closed by `etransitivity` through
`mulmod_correct0` and a `rapply @f_equal2; lia` step that reassociates the
product `eval a * eval b * r'^n`.

Why each child is a good leaf:

- `mulmod_correct0` (1095-1107) is self-contained: `small a -> small b` yields
  smallness, a bound, and the raw congruence `eval (mulmod a b) mod m =
  (eval a * eval b * r'^n) mod m`. Its proof splits the conjunction with
  `repeat rapply conj` and closes each conjunct by a named prior lemma
  (`small_redc`, `redc_bound_N`, `redc_mod_N`) followed by `t_fin` — no manual
  arithmetic. It carries the whole idea of the reduction.
- `eval_from_montgomerymod` (1146-1149) is a one-line projection of
  `from_montgomerymod_correct` (`apply from_montgomerymod_correct;
  assumption`), and states exactly the unwrapping the parent needs: a valid
  input evaluates through `from_montgomerymod` to `eval v * r'^n mod m`.

The parent is the *only* place these two are combined into the wrapped
interface statement, so it is the skeleton: its proof is the glue, the two
lemmas are the holes.

## Why it is good

1. `mulmod_correct` is declared at lines 1156-1167 of the file (`check`,
   `declared(mulmod_correct, src/Arithmetic/WordByWordMontgomery.v, 1156-1167)`).
2. The parent proof cites `mulmod_correct0` (`check`, `cites(parent,
   mulmod_correct0)`), so the raw congruence is a genuine dependency, not a
   convenience.
3. The parent proof cites `eval_from_montgomerymod` (`check`, `cites(parent,
   eval_from_montgomerymod)`), so the wrapper rewrite is a genuine dependency.
4. The glue is 12 lines (`check`, `lines(parent, 12)`): the whole interface
   theorem is assembled in a dozen lines because both children already exist.
5. The shape is 2 direct lemmas, glue 12 lines, children 13 and 4 lines (each
   declaration through `Qed`), and a longest checked lemma chain of depth 3
   (`eval_from_montgomerymod -> from_montgomerymod_correct -> mulmod_correct0`)
   (`measurement`; counted in the copied file at lines 1156-1167, 1095-1107,
   1146-1149, 1136-1144).

In my opinion the detail worth copying is that the raw congruence lemma
`mulmod_correct0` is stated *before* and *independently of* the wrapper, so
`mulmod_correct` is reusable glue rather than a re-proof: the same raw lemma is
also consumed by `from_montgomerymod_correct` (line 1143) and by the validity
side of `mulmod_correct` itself.

## When to use it, and when not

Use it when an operation has a raw form whose congruence you can prove once as
a standalone lemma (here `mulmod_correct0`), and a wrapper (here
`from_montgomerymod`) with its own rewrite lemma that unwraps it to exactly the
raw form. The interface theorem then falls out by rewriting the wrapper away
and applying the raw lemma, and the same raw lemma serves every later client.

Avoid it when the raw lemma does not already exist — then the raw statement is
the real content and must be proved first, on its own; when the wrapper's
rewrite does not land on the form the raw lemma expects, so the residual
reassociation step (here `f_equal2` + `lia`) becomes the actual argument; and
when the validity side needs a different argument than the value side, so a
single raw lemma cannot close both conjuncts.

## Consequences

The move creates two obligations for the wrapper: it must rewrite to exactly
the raw form the congruence lemma states, and the resulting goal must be
congruent with the product of the two wrapped values. Here the second is not
automatic — the proof still runs `etransitivity` + `rapply @f_equal2; lia` to
reassociate `eval a * eval b * r'^n` — so the glue is not pure rewriting. A
known failure mode is getting stuck at that residual arithmetic step when the
raw lemma is stated with a different association than the wrapper produces; the
fix is to state the raw lemma in the association the wrapper needs (or add the
rewrite `!Z.mul_assoc`, as this proof does at line 1164).

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/coq-debian.yml (push branches: master, sp2019latest) runs 'etc/ci/github-actions-make.sh -j2 all-except-generated-and-js-of-ocaml'; Makefile target 'coq' (line 169) depends on REGULAR_VOFILES = src/**/*.v from coq_makefile over 'find src -type f -name *.v', which includes src/Arithmetic/WordByWordMontgomery.v (not in SPECIAL_VOFILES/EXCLUDE_PATTERN); pinned commit 3d2880ef is HEAD of default branch master (source.json ref=HEAD) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: mulmod_correct0@src/Arithmetic/WordByWordMontgomery.v:1163, eval_from_montgomerymod@src/Arithmetic/WordByWordMontgomery.v:1162; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 3d2880ef2803faa9385589a81a835d5828eb3d38 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(mulmod_correct, src/Arithmetic/WordByWordMontgomery.v, 1156-1167) -> declared: mulmod_correct is declared at src/Arithmetic/WordByWordMontgomery.v:1156 | check_claims.py |
| 2 | verified | cites(parent, mulmod_correct0) -> cites: mulmod_correct0 occurs at src/Arithmetic/WordByWordMontgomery.v:1163 | check_claims.py |
| 3 | verified | cites(parent, eval_from_montgomerymod) -> cites: eval_from_montgomerymod occurs at src/Arithmetic/WordByWordMontgomery.v:1162 | check_claims.py |
| 4 | verified | lines(parent, 12) -> lines: site parent has 12 lines | check_claims.py |
| 5 | verified | Read byte-identical local copy code/src/Arithmetic/WordByWordMontgomery.v: mulmod_correct0 at 1095-1107 (13 lines, declaration through Qed), eval_from_montgomerymod at 1146-1149 (4 lines), glue mulmod_correct at 1156-1167 (12 lines). Depth-3 chain: eval_from_montgomerymod proof line 1148 'apply from_montgomerymod_correct', whose proof line 1143 'apply mulmod_correct0'. 2 direct lemmas confirmed (glue cites both). All numbers match. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Opened the local code copy at the cited ranges. Parent mulmod_correct (1156-1167, 12 lines, Qed at 1167) is exactly as quoted and cites both children: eval_from_montgomerymod at line 1162 (rewrite ?eval_from_montgomerymod) and mulmod_correct0 at 1163 (try apply) and 1166 (apply inside etransitivity). Child mulmod_correct0 (1095-1107, 13 lines) and eval_from_montgomerymod (1146-1149, 4 lines) match the quoted statements verbatim; their closed_by matches the code (small_redc/redc_bound_N/redc_mod_N+t_fin; apply from_montgomerymod_correct; assumption). All three close with Qed. The children are exactly the two project lemmas the glue uses. Shape is right: direct_lemmas 2, glue_lines 12, child_lines [13,4], depth 3 = chain eval_from_montgomerymod(1148)->from_montgomerymod_correct(1136-1144, applies mulmod_correct0 at 1143)->mulmod_correct0, verified in code. No correctness defect found. | reviewer-correctness |
| generality | accept | Move is stated abstractly (operation/raw form/wrapper/rewrite lemma), not just about Montgomery: applicability.goal_shape/use_when/avoid_when generalise to any wrapped operation with a pre-proved raw congruence. When-not-to-use is specific and honest (raw lemma missing; wrapper rewrite not landing on the raw form; validity vs value side needing different arguments; residual f_equal2/lia reassociation), and Consequences admits the glue is not pure rewriting, naming the concrete fix (state raw lemma in the association the wrapper needs, or rewrite !Z.mul_assoc at line 1164). Leaves-good-for-a-bounded-prover is addressed: mulmod_correct0 is self-contained and closes by named prior lemmas + t_fin with no manual arithmetic; eval_from_montgomerymod is a one-line projection of from_montgomerymod_correct; metrics records children_closed_by_automation=2. Code at 1095-1107, 1136-1149, 1156-1167 confirms the cited structure. | reviewer-generality |
| provenance-licence | accept | Prior objection fixed: sources/fiat-crypto/SOURCE.md line 7 and sources/fiat-crypto/source.json 'licence' now record 'MIT OR Apache-2.0 OR BSD-1-Clause' (no BSD-2-Clause, no AND framing). source.json's remaining 'licence_detected' field keeps the detector's raw output but is now paired with licence_note 'there is no BSD-2-Clause file (the file is LICENSE-BSD-1)', so it is a labelled historical record, not the entry's licence. Consistency confirmed across all four records: entry.json source.licence, README header row and 'Source and licence' section, source.json licence, SOURCE.md line 7 all read MIT OR Apache-2.0 OR BSD-1-Clause. Copied licence files corroborate: upstream-COPYRIGHT SPDX-License-Identifier 'MIT OR Apache-2.0 OR BSD-1-Clause', upstream-LICENSE-MIT ('The MIT License (MIT)'), upstream-LICENSE-APACHE ('Apache-2.0'), upstream-LICENSE-BSD-1 ('The BSD 1-Clause License (BSD-1-Clause)'); no BSD-2-Clause file exists. Provenance: check_provenance.py passes (1 file byte-identical at 3d2880ef2803faa9385589a81a835d5828eb3d38); local copy 66865 bytes, sha256 ea50cdb5a1f725a759b79cf7403b43123db4aa23f5ed28a640c9d9b1521ac572 matches entry.json files[].sha256. All permalinks and known_uses carry the full commit; the cited line ranges (1156-1167, 1095-1107, 1146-1149, 1133-1134, 1084-1093, and known_uses 1136-1144, 1175-1181) read verbatim as quoted in the README. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/mit-plv/fiat-crypto at commit `3d2880ef2803faa9385589a81a835d5828eb3d38`, under `MIT OR Apache-2.0 OR BSD-1-Clause`; see the [source note](../../sources/fiat-crypto/SOURCE.md) for the licence text and attribution.
