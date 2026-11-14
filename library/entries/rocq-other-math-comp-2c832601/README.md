# Transport non-solvability from the normal subgroup 'Alt_T to 'Sym_T via series_sol

| | |
|---|---|
| Kind | instance |
| Move | other |
| Language | rocq |
| Status | verified |
| Source | [math-comp](../../sources/math-comp/SOURCE.md) at `3a90d8b65f77` |
| Licence | `CECILL-B` |

## Intent

To prove `'Sym_T` is not solvable for `4 < #|T|`, the proof reduces solvability of
the whole symmetric group to solvability of its normal subgroup `'Alt_T` through
the normal-series equivalence `series_sol`, then supplies the already-proved
non-solvability of `'Alt_T`. The one-line glue never analyses the quotient
`'Sym_T / 'Alt_T`, which is dropped by `false && _`.

## The decomposition

### parent `solvable_SymF`: [`solvable/alt.v` lines 592-593](https://github.com/math-comp/math-comp/blob/3a90d8b65f77f24e4fd770453c0697233b1c791d/solvable/alt.v#L592-L593) ([local copy](code/solvable/alt.v))

```coq
Lemma solvable_SymF : 4 < #|T| -> solvable 'Sym_T = false.
Proof. by rewrite (series_sol (Alt_normal T)) => /solvable_AltF->. Qed.
```

### child `Alt_normal`: [`solvable/alt.v` lines 54-55](https://github.com/math-comp/math-comp/blob/3a90d8b65f77f24e4fd770453c0697233b1c791d/solvable/alt.v#L54-L55) ([local copy](code/solvable/alt.v))

```coq
Lemma Alt_normal : 'Alt_T <| 'Sym_T.
Proof. exact: ker_normal. Qed.
```

### child `solvable_AltF`: [`solvable/alt.v` lines 579-590](https://github.com/math-comp/math-comp/blob/3a90d8b65f77f24e4fd770453c0697233b1c791d/solvable/alt.v#L579-L590) ([local copy](code/solvable/alt.v))

```coq
Lemma solvable_AltF : 4 < #|T| -> solvable 'Alt_T = false.
Proof.
move=> card_T; apply/negP => Alt_solvable.
have/simple_Alt5 Alt_simple := card_T.
have := simple_sol_prime Alt_solvable Alt_simple.
have lt_T n : n <= 4 -> n < #|T| by move/leq_ltn_trans; apply.
have -> : #|('Alt_T)%G| = #|T|`! %/ 2 by rewrite -card_Alt ?mulKn ?lt_T.
move/even_prime => [/eqP|]; apply/negP.
  rewrite neq_ltn leq_divRL // mulnC -[2 * 3]/(3`!).
  by apply/orP; right; apply/ltnW/ltn_fact/lt_T.
by rewrite -dvdn2 dvdn_divRL dvdn_fact //=; apply/ltnW/lt_T.
Qed.
```

### How the parts fit

The glue is the single tactic line of `solvable_SymF`:

`rewrite (series_sol (Alt_normal T)) => /solvable_AltF->`.

It does three things, in order.

1. `(Alt_normal T)` supplies the premise `'Alt_T <| 'Sym_T` that `series_sol`
   needs. `Alt_normal` is closed by `exact: ker_normal`: `'Alt_T` is the kernel
   of the sign morphism `odd_perm`, hence normal in `'Sym_T`.
2. `series_sol` (a library lemma, not proved in this file — its statement is at
   `solvable/nilpotent.v:735`) rewrites `solvable 'Sym_T` into
   `solvable 'Alt_T && solvable ('Sym_T / 'Alt_T)`. That is the transport step:
   solvability of the whole group is the conjunction of solvability of the
   normal subgroup and of the quotient.
3. `=> /solvable_AltF->` introduces the hypothesis `4 < #|T|`, applies
   `solvable_AltF` to it as a view to obtain `solvable 'Alt_T = false`, and
   rewrites. The goal becomes `false && solvable ('Sym_T / 'Alt_T) = false`,
   which closes by computation: the quotient is never examined.

Lemma graph (which project lemma uses which), line numbers in `solvable/alt.v`:

```
solvable_SymF (592)  — the glue applies series_sol and cites both children
 ├── Alt_normal (54)          closed by exact: ker_normal
 └── solvable_AltF (579)      closed by simple_Alt5, simple_sol_prime, card_Alt, even_prime
      ├── simple_Alt5 (395)   -> simple_Alt5_base (186) -> Alt_trans (98) -> Sym_trans (86)
      └── card_Alt (81)
```

Both children are good leaves — self-contained statements whose proofs close on
their own or from named siblings, not from `solvable_SymF`:

- `Alt_normal` closes in one line by `ker_normal`, a library fact about kernels
  of morphisms; it names no project lemma.
- `solvable_AltF` depends only on earlier lemmas of the same file (`simple_Alt5`,
  `card_Alt`) and library lemmas (`simple_sol_prime`, `even_prime`). Its chain
  bottoms out at `Sym_trans` (line 86), which is proved from library facts
  alone. So the two children could be discharged by independent provers and
  recombined by the one-line glue.

The only non-project lemma the glue applies is `series_sol`; it is the mechanism
of the move and is not counted as a child.

## Why it is good

1. The parent lemma `solvable_SymF` is declared at `solvable/alt.v:592-593`
   (check, permalink above).
2. The glue cites the child `Alt_normal` (check, permalink above).
3. The glue cites the child `solvable_AltF` (check, permalink above).
4. The library lemma `series_sol` that the glue applies is declared at
   `solvable/nilpotent.v:735` (check, permalink above).
5. No `admit`, `Admitted` or `Axiom` closes a goal in the section holding the
   parent and its children (`solvable/alt.v:54-593`) (check, permalink above).
6. The parent site is 2 lines long (check, permalink above).
7. The theorem is assembled from two direct project lemmas, and the work sits in
   the children, not the glue: one proof line (593) versus 2 and 12 lines for
   the children (54-55, 579-590) (measurement).
8. The same `series_sol` transport is reused elsewhere in the library:
   `metacyclic_sol` (`nilpotent.v:749`) and `setXn_sol` (`nilpotent.v:768`) both
   rewrite with `series_sol` to build solvability from a normal subgroup and its
   quotient (known-use).

In my opinion the detail worth copying is the *direction* of the transport:
because the goal is `solvable 'Sym_T = false`, the `false` in
`solvable 'Alt_T && …` swallows the quotient, so the hard `'Sym_T / 'Alt_T`
factor never has to be proved at all — the decomposition gets away with one
normal-subgroup fact and one non-solvability fact.

## When to use it, and when not

Use it when you can exhibit a normal subgroup `H <| G` of the target group that
is already known non-solvable, stated as `solvable H = false`. `series_sol`
rewrites `solvable G` to `solvable H && solvable (G / H)`, and the `false`
collapses the conjunction, so the quotient never has to be analysed.

Avoid it when the quotient matters — in particular the downward direction
`solvable G -> solvable H` forces you to prove `solvable (G / H)` as well and the
one-line glue no longer closes. Avoid it when the subgroup is not normal (then
`series_sol` does not apply), or when the subgroup's non-solvability is not yet a
rewrite lemma of the shape `solvable H = false` that a view such as
`/solvable_AltF->` can fire on.

## Consequences

The move creates no exhaustiveness or side-condition obligation beyond the
normality `H <| G` (`Alt_normal`) and the non-solvability of the subgroup
(`solvable_AltF`). It relies on `series_sol` being an equivalence, so that the
quotient factor can be dropped by `false && _`. Failure modes: without an
equation `solvable H = false`, the view `=> /solvable_AltF->` does not fire; and
for the upward direction you must also prove the quotient solvable, so the glue
is no longer a single line.

## Verification

<!-- verification:start -->
Status: **verified**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/nix-action-rocq-9.3.yml builds job mathcomp-solvable (which compiles solvable/alt.v) on default branch master; pinned commit 3a90d8b65f77f24e4fd770453c0697233b1c791d reachable from master (0 behind) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: Alt_normal@solvable/alt.v:593, solvable_AltF@solvable/alt.v:593; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at 3a90d8b65f77f24e4fd770453c0697233b1c791d | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(solvable_SymF, solvable/alt.v, 592-593) -> declared: solvable_SymF is declared at solvable/alt.v:592 | check_claims.py |
| 2 | verified | cites(solvable_SymF, Alt_normal) -> cites: Alt_normal occurs at solvable/alt.v:593 | check_claims.py |
| 3 | verified | cites(solvable_SymF, solvable_AltF) -> cites: solvable_AltF occurs at solvable/alt.v:593 | check_claims.py |
| 4 | verified | declared(series_sol, solvable/nilpotent.v, 735-735) -> declared: series_sol is declared at solvable/nilpotent.v:735 | check_claims.py |
| 5 | verified | no_sorry(solvable/alt.v, 54-593) -> no_sorry: none of admit, Admitted, Axiom, axiom in solvable/alt.v:54-593 | check_claims.py |
| 6 | verified | lines(solvable_SymF, 2) -> lines: site solvable_SymF has 2 lines | check_claims.py |
| 7 | verified | checked code/solvable/alt.v: parent site 592-593 (Lemma solvable_SymF at 592, one-line proof at 593); Alt_normal 54-55 (2 lines); solvable_AltF 579-590 (12 lines). Glue is one proof line citing the two children, work sits in children. | verifier |
| 8 | verified | checked code/solvable/nilpotent.v: metacyclic_sol at 746, its series_sol rewrite at 749 (rewrite (series_sol nsKG) !abelian_sol); setXn_sol at 757, its series_sol rewrite at 768 (rewrite (@series_sol ... ker ...) ?ker_normal). Both build solvability from normal subgroup + quotient. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | object | Decomposition matches the code and closes: glue 'rewrite (series_sol (Alt_normal T)) => /solvable_AltF->' with series_sol G H : H <| G -> solvable G = solvable H && solvable (G / H) (nilpotent.v:735) rewrites solvable 'Sym_T to solvable 'Alt_T && solvable ('Sym_T/'Alt_T); solvable_AltF view turns solvable 'Alt_T into false, so 'false && _ = false' closes. Children are exactly the two lemmas the glue cites (Alt_normal, solvable_AltF); their statements and closed_by are verbatim-correct. However shape.depth=5 is wrong: the longest chain of project lemmas below solvable_SymF is 7, not 5, via solvable_AltF(579)->simple_Alt5(582 'have/simple_Alt5')->simple_Alt5_base(397 'exact: simple_Alt5_base')->card_Alt(189 'rewrite -mul2n card_Alt')->Alt_index(82 'move/Alt_index')->Alt_norm(62 '?Alt_norm')->Alt_normal(57 'case/andP: Alt_normal'). The README lemma graph also mislabels card_Alt(81) as a leaf and omits the simple_Alt5_base->card_Alt and card_Alt->Alt_index->Alt_norm->Alt_normal edges. Fix: recompute depth=7 and correct the graph. | reviewer-correctness |
| generality | object | Move is stated generally (goal_shape and use_when in terms of arbitrary G, H) and the good-leaves question is answered (children close from siblings/library, not the parent). But 'when not to use' misstates the costly direction: it says 'downward direction solvable G -> solvable H forces proving solvable (G / H)', yet series_sol G H : H <| G -> solvable G = solvable H && solvable (G / H) gives solvable (G/H) as a free conjunct of the rewritten hypothesis, so that direction needs no quotient proof. The costly direction is the upward one (solvable H && solvable (G/H) -> solvable G), which the Consequences section already states correctly — so avoid_when contradicts Consequences. Fix: in README 'When to use' and entry.json applicability.avoid_when, replace the downward-direction claim with the upward/positive direction (proving solvable G) as the case where the quotient must be proved. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are consistent and traceable: check_provenance passed (2 files byte-identical at 3a90d8b65f77f24e4fd770453c0697233b1c791d); that commit matches SOURCE.md and source.json; licence CECILL-B matches the source note and the copied upstream-LICENCE (CeCILL-B text); every cited line range verified in the local copies (alt.v:592-593, 54-55, 579-590; nilpotent.v:735, 749, 768) shows exactly the quoted code. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/math-comp/math-comp at commit `3a90d8b65f77f24e4fd770453c0697233b1c791d`, under `CECILL-B`; see the [source note](../../sources/math-comp/SOURCE.md) for the licence text and attribution.
