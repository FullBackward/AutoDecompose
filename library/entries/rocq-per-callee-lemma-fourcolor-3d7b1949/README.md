# Per-block C-reducibility lemmas collated into the four-colour the_reducibility

| | |
|---|---|
| Kind | instance |
| Move | per-callee-lemma |
| Language | rocq |
| Status | verified |
| Source | [fourcolor](../../sources/fourcolor/SOURCE.md) at `c1d6b1cd5288` |
| Licence | `CECILL-B` |

## Intent

Prove that all 633 configurations of `the_configs` are C-reducible — the
`reducibility` half of the four-colour theorem — by partitioning the index
range `[0, 633)` into ten contiguous blocks and giving each block its own
lemma (`red000to214` … `red588to633`). Each block lemma is itself a
`CatReducible` chain of smaller generated block lemmas, and every leaf closes
by the single computational-reflection tactic `CheckReducible`. Nothing in the
proof is argued by hand: the whole tree is generated per block and catenated.

## The decomposition

### parent `the_reducibility`: [`theories/proof/reducibility.v` lines 16-21](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/reducibility.v#L16-L21) ([local copy](code/theories/proof/reducibility.v))

```coq
Lemma the_reducibility : reducibility.
Proof.
rewrite /reducibility; apply cat_reducible_range with 322.
  CatReducible red000to214 red214to234 red234to282 red282to302 red302to322.
CatReducible red322to485 red485to506 red506to541 red541to588 red588to633.
Qed.
```

### child `red000to214`: [`theories/proof/task001to214.v` lines 14-17](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/task001to214.v#L14-L17) ([local copy](code/theories/proof/task001to214.v))

```coq
Lemma red000to214 : reducible_in_range 0 214 the_configs.
Proof.
CatReducible red000to106 red106to164 red164to189 red189to206 red206to214.
Qed.
```

### child `red214to234`: [`theories/proof/task215to234.v` lines 14-17](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/task215to234.v#L14-L17) ([local copy](code/theories/proof/task215to234.v))

```coq
Lemma red214to234 : reducible_in_range 214 234 the_configs.
Proof.
CatReducible red214to218 red218to222 red222to226 red226to230 red230to234.
Qed.
```

### child `red234to282`: [`theories/proof/task235to282.v` lines 14-17](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/task235to282.v#L14-L17) ([local copy](code/theories/proof/task235to282.v))

```coq
Lemma red234to282 : reducible_in_range 234 282 the_configs.
Proof.
CatReducible red234to238 red238to253 red253to270 red270to278 red278to282.
Qed.
```

### child `red282to302`: [`theories/proof/task283to302.v` lines 14-17](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/task283to302.v#L14-L17) ([local copy](code/theories/proof/task283to302.v))

```coq
Lemma red282to302 : reducible_in_range 282 302 the_configs.
Proof.
CatReducible red282to286 red286to290 red290to294 red294to298 red298to302.
Qed.
```

### child `red302to322`: [`theories/proof/task303to322.v` lines 14-17](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/task303to322.v#L14-L17) ([local copy](code/theories/proof/task303to322.v))

```coq
Lemma red302to322 : reducible_in_range 302 322 the_configs.
Proof.
CatReducible red302to306 red306to310 red310to314 red314to318 red318to322.
Qed.
```

### child `red322to485`: [`theories/proof/task323to485.v` lines 14-17](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/task323to485.v#L14-L17) ([local copy](code/theories/proof/task323to485.v))

```coq
Lemma red322to485 : reducible_in_range 322 485 the_configs.
Proof.
CatReducible red322to383 red383to398 red398to438 red438to465 red465to485.
Qed.
```

### child `red485to506`: [`theories/proof/task486to506.v` lines 14-17](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/task486to506.v#L14-L17) ([local copy](code/theories/proof/task486to506.v))

```coq
Lemma red485to506 : reducible_in_range 485 506 the_configs.
Proof.
CatReducible red485to489 red489to494 red494to498 red498to502 red502to506.
Qed.
```

### child `red588to633`: [`theories/proof/task589to633.v` lines 13-18](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/task589to633.v#L13-L18) ([local copy](code/theories/proof/task589to633.v))

```coq
Lemma red588to633 : reducible_in_range 588 633 the_configs.
Proof.
have red633: reducible_in_range 633 633 the_configs.
  by apply check_reducible_in_range; left.
CatReducible red588to610 red610to617 red617to622 red622to633 red633.
Qed.
```

Two of the ten direct lemmas are shown only by permalink here (their files are
copied in [`code/`](code/)): `red506to541`
([`task507to541.v` L14-L17](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/task507to541.v#L14-L17))
and `red541to588`
([`task542to588.v` L14-L17](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/task542to588.v#L14-L17));
they are `CatReducible` chains of five sub-blocks exactly like their siblings.

How the parts fit. The parent `the_reducibility : reducibility` unfolds (line
18) to `reducible_in_range 0 (size the_configs) the_configs`, i.e. every
configuration in the 633-element `the_configs` is C-reducible. The glue then
splits that range once, at 322, with `apply cat_reducible_range with 322`, and
closes the two halves by two `CatReducible` chains. The lemma graph is:

```
the_reducibility  (reducibility := reducible_in_range 0 633 the_configs)
 ├─ [0,322)  red000to214 ── red000to106 ── CheckReducible        (leaf)
 │            red214to234 ── red214to218 … red230to234 ── CheckReducible
 │            red234to282 ── red234to238 … red278to282 ── CheckReducible
 │            red282to302 ── red282to286 … red298to302 ── CheckReducible
 │            red302to322 ── red302to306 … red318to322 ── CheckReducible
 └─ [322,633) red322to485 ── red322to383 … red465to485 ── CheckReducible
              red485to506 ── red485to489 … red502to506 ── CheckReducible
              red506to541 ── red506to510 … red534to541 ── CheckReducible
              red541to588 ── red541to545 … red562to588 ── CheckReducible
              red588to633 ── red588to610 … red622to633, red633 ── CheckReducible
```

Each of the ten direct lemmas is a self-contained statement
`reducible_in_range MMM NNN the_configs` whose proof closes on its own — it is
a single `CatReducible` line naming its five contiguous sub-block lemmas, each
of which lives in its own `jobMMMtoNNN.v` file and closes with
`Proof. CheckReducible. Qed.` (see `job001to106.v` L12-L13). `CheckReducible`
and `CatReducible` are defined once in [`cfreducible.v`](code/theories/proof/cfreducible.v)
(L97-L99 and L109-L112): `CheckReducible` discharges a whole range by
computational reflection, and `CatReducible` applies `cat_reducible_range` four
times to catenate five contiguous sub-range proofs.

Why each lemma is a good leaf. A `redMMMtoNNN` block lemma is exactly the hole
AutoDecompose wants to hand to a bounded prover: its statement mentions only
its two numeric bounds and `the_configs`, its proof is a single mechanical
tactic with no free variables left over, and it closes either by reflection
alone (the job leaves) or from five named siblings in the same directory (the
task lemmas). The only irregularity is the final block: `red588to633` first
proves the empty end range `red633 : reducible_in_range 633 633 the_configs`
by `check_reducible_in_range; left`, because `CatReducible` always wants five
arguments but the last group has only four job files.

## Why it is good

1. (`check`) The parent closes from the ten direct lemmas in three tactic
   lines: `rewrite /reducibility; apply cat_reducible_range with 322` then two
   `CatReducible` chains, nothing else between `Proof.` and `Qed.`
   ([`reducibility.v` L16-L21](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/reducibility.v#L16-L21)).
2. (`check`) Every direct lemma is a `CatReducible` chain of five contiguous
   sub-blocks, and every job-level sub-block closes by `CheckReducible` alone:
   `red000to214` cites `red000to106`, which `job001to106.v` closes with
   `Proof. CheckReducible. Qed.`; the one non-job argument, `red633` in
   `red588to633`, is the empty end range closed by `check_reducible_in_range;
   left`.
   ([`task001to214.v` L14-L17](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/task001to214.v#L14-L17),
   [`job001to106.v` L12-L13](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/job001to106.v#L12-L13)).
3. (`measurement`) The `shape` is measured from the copied files:
   `direct_lemmas = 10` (the ten names on `reducibility.v` L19-L20),
   `depth = 2` (`the_reducibility → red000to214 → red000to106`, the last a
   reflection leaf), `glue_lines = 5` (`reducibility.v` L17-L21), and the
   eight shown children have `child_lines = [3, 3, 3, 3, 3, 3, 3, 5]` (their
   `Proof … Qed` blocks; `red588to633` is 5 because it also proves the empty
   end range `red633`).
4. (`measurement`) The 633 configurations are covered by 49 job files grouped
   into the 10 task files — a two-level tree of 60 lemmas (1 theorem + 10 task
   + 49 job) whose leaves all close by `CheckReducible`; `the_configs :=
   @seqn config 633` is stated at
   [`configurations.v` L2076](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/configurations.v#L2076)
   and the 49 job files are counted by `list_files.py fourcolor`.
5. (`author-statement`) The authors spell out the collation move in the header
   of `cfreducible.v`: "CatReducible lem1 .. lem5 :: tactic for proving a
   reducible_in_range i j cfs subgoal by combining proofs lem[1-5] of
   reducible_in_range for five contiguous subranges covering [i, j)."
   ([`cfreducible.v` L25-L28](https://github.com/math-comp/fourcolor/blob/c1d6b1cd5288bea4b067aac13cdde3c18dffe018/theories/proof/cfreducible.v#L25-L28)).

In my opinion the detail worth copying is the two-level generated tree: the
per-block lemma is repeated with only its numeric bounds changing, so the move
scales by *generation*, not by writing proofs — the same reason CompCert chains
per-pass simulation lemmas and seL4's `crunch` emits per-function lemmas.

## When to use it, and when not

Use it when one headline goal is a large, homogeneous family of cases (one per
configuration, compiler pass, or function) that can be put in a contiguous
order, and when every case is discharged by the same mechanical procedure — a
reflection tactic, a computation, or a per-pass simulation — so that a single
tactic (`CheckReducible` here) proves every leaf and a transitivity-like
combinator (`cat_reducible_range`) catenates the blocks.

Avoid it when the cases are few (the block-and-catenate scaffolding is
overhead), when the cases are heterogeneous (each needs its own argument, so
the shared per-block tactic buys nothing), when the blocks cannot tile the
parent range exactly (the combinator requires the end of one block to equal the
start of the next), or when the per-case check is expensive and must be cached
per component anyway, which is the situation the block lemma already encodes.

## Consequences

The move creates one leaf obligation per block (each must prove
`reducible_in_range MMM NNN the_configs`), a contiguity obligation (the blocks
must tile the parent range exactly — `cat_reducible_range` needs the end of one
block to equal the start of the next), and a fixed arity (`CatReducible` takes
exactly five sub-lemmas, which is why `red588to633` introduces an inline `have
red633` for the empty end range `[633, 633)`). Failure modes: a missing or
overlapping block, or a bound that is off by one, surfaces only as an opaque
unification error at the catenation point, not a pointed message; and a block
whose cases are not all checkable by the one `CheckReducible` reflection breaks
the uniform one-tactic leaf and has to be split again by hand.

This decomposition supports survey F §10 rule 15 ("shallow and wide, depth cap
2-3"): it is a landmark proof whose reducibility part is exactly depth 2 and
width 49, with every leaf closed mechanically, so a depth cap of 2-3 loses
nothing here. It is silent on the rule's second half (global replan), since the
block boundaries are fixed up front rather than discovered.

## Verification

<!-- verification:start -->
Status: **verified**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/docker-action.yml builds coq-fourcolor on push to master (opam install coq-fourcolor builds the whole library incl. theories/proof/reducibility.v, listed in _CoqProject line 127); default branch is master and pinned commit c1d6b1cd5288bea4b067aac13cdde3c18dffe018 is the master HEAD | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 13 file(s) byte-identical at c1d6b1cd5288bea4b067aac13cdde3c18dffe018 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | reducibility.v L16-21: L18 'rewrite /reducibility; apply cat_reducible_range with 322.', L19-20 two CatReducible chains (red000to214..red302to322 over [0,322); red322to485..red588to633 over [322,633)); nothing between Proof(17) and Qed(21) | verifier |
| 2 | verified | all ten task*.v files show 'CatReducible' with five sub-block lemmas; job001to106.v/job107to164.v/job563to588.v/job623to633.v all close 'Proof. CheckReducible. Qed.'; task589to633.v closes red633 (empty [633,633)) with 'by apply check_reducible_in_range; left.' | verifier |
| 3 | verified | reducibility.v L19-20 name 10 direct lemmas; glue block L17-21 = 5 lines; depth the_reducibility->red000to214->red000to106 = 2 (job closed by CheckReducible); child_lines from 8 child sites: 7 with 3-line Proof..Qed, red588to633 with 5 (adds 'have red633' + 'by apply') | verifier |
| 4 | verified | list_files.py fourcolor --glob theories/proof/job*.v returns exactly 49 job files; configurations.v L2076 'Definition the_configs := @seqn config 633'; 1 theorem + 10 task + 49 job = 60; sampled job files all close with CheckReducible | verifier |
| 5 | verified | cfreducible.v L25-28 header: 'CatReducible lem1 .. lem5 :: tactic for proving a reducible_in_range i j subgoal by combining proofs lem[1-5] of reducible_in_range for five contiguous subranges covering [i, j).' (quote matches; 'cfs' in the claim comes from the reducible_in_range signature documented at L21) | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Opened copied code and upstream: parent reducibility.v L16-21 is Lemma the_reducibility : reducibility., whose L18 rewrite /reducibility; apply cat_reducible_range with 322 splits [0,633) at 322 (present.v L73: reducibility := reducible_in_range 0 (size the_configs) the_configs; configurations.v L2076: the_configs := @seqn config 633), closed by two CatReducible chains L19-20 naming exactly the 10 children. All 10 children's statements and closed_by match their task files verbatim (task001to214..task589to633); each is a 5-arg CatReducible chain of contiguous sub-blocks, and job leaves (e.g. job001to106, job563to588, job623to633) close with Proof. CheckReducible. Qed.; red588to633's red633 inline closes by apply check_reducible_in_range; left. Tiling is exact at every level (no gaps/overlaps). Shape numbers verified from code: direct_lemmas=10 (L19-20), depth=2 (the_reducibility->red000to214->red000to106), glue_lines=5 (L17-21), child_lines=[3,3,3,3,3,3,3,5] for the 8 shown child sites (red588to633=5 incl. red633). Provenance passes (13 files byte-identical); list_files.py confirms 49 job files, 60 total lemmas. | reviewer-correctness |
| generality | object | Move is stated beyond the example (also_known_as: CompCert per-pass simulation, seL4 crunch; known_uses: lean equational-theories entry) and the 'Why each lemma is a good leaf' paragraph does name what makes leaves bounded-prover-sized (statement = two numeric bounds + the_configs, one mechanical tactic, no free variables). Consequences are honest/specific and match the copied code: CatReducible is fixed arity 5 (cfreducible.v L109-112), cat_reducible_range needs contiguous tiling (L101-103), red588to633 pads the empty end range (task589to633.v L15-16). But the README 'when not to use' is not honest: its 4th clause 'avoid when the per-case check is expensive and must be cached per component anyway, which is the situation the block lemma already encodes' is self-contradictory -- it warns against the move in exactly the per-component-caching situation the block lemmas provide (cfreducible.v L72 'hides the expensive reducibility evaluation'). It also diverges from entry.json avoid_when, whose 3rd clause ('per-case check not uniform enough for one generated tactic') is the honest converse and is missing from the README. Fix: replace that 4th README clause with the uniformity converse, or reword so expensive per-case checks read as a reason to use, not avoid. | reviewer-generality |
| provenance-licence | accept | Provenance passes: 13 files byte-identical at c1d6b1cd5288bea4b067aac13cdde3c18dffe018 (check_provenance.py). Commit c1d6b1cd5288bea4b067aac13cdde3c18dffe018 is consistent across entry.json source, sources/fourcolor/source.json, sources/fourcolor/SOURCE.md, and every file/site permalink (all blob/c1d6b1cd.../theories/proof/*.v). Licence CECILL-B is recorded consistently in entry.json source.licence, source.json licence, and SOURCE.md, and the copied upstream-LICENSE is the CeCILL-B licence text (matches). Source note records the pinned commit, browse URL, detected licence, and licence file LICENSE->upstream-LICENSE, with attribution. All 13 code/ files match the entry files array; permalink line anchors are consistent with the copied files. Everything traceable; no gaps. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/math-comp/fourcolor at commit `c1d6b1cd5288bea4b067aac13cdde3c18dffe018`, under `CECILL-B`; see the [source note](../../sources/fourcolor/SOURCE.md) for the licence text and attribution.
