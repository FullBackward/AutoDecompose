# Extensionality for shareable red-black maps via rbt_ext_eqI and shareable_value_option_inj

| | |
|---|---|
| Kind | instance |
| Move | extensionality |
| Language | isabelle |
| Status | accepted |
| Source | [autocorrode](../../sources/autocorrode/SOURCE.md) at `200f1acf2d26` |
| Licence | `MIT` |

## Intent

Reduce the user-facing equality `rm0 = rm1` of two share maps to the pointwise
equality of their `rbt_share_map_\<alpha>` abstraction, then close it with two
lemmas — the injectivity of the `shareable_value_option` wrap and the quotient
extensionality `rbt_ext_eqI` of the underlying red-black tree — so that every
later equality of share maps is proved by `intro!: rbt_share_map_eqI` instead of
unfolding the representation.

## The decomposition

### parent `rbt_share_map_eqI`: [`Shallow_Separation_Logic/Share_Map.thy` lines 117-121](https://github.com/awslabs/AutoCorrode/blob/200f1acf2d264f2dedee33792b986ebe73c224a3/Shallow_Separation_Logic/Share_Map.thy#L117-L121) ([local copy](code/Shallow_Separation_Logic/Share_Map.thy))

```isabelle
lemma rbt_share_map_eqI:
  assumes \<open>rbt_share_map_\<alpha> rm0 = rbt_share_map_\<alpha> rm1\<close>
  shows \<open>rm0 = rm1\<close>
  using assms unfolding rbt_share_map_\<alpha>_def
  by (metis (lifting) ext rbt_ext_eqI rbt_share_map.expand  shareable_value_option_inj)
```

### child `rbt_ext_eqI`: [`Data_Structures/RedBlackTree_Extensional.thy` lines 157-160](https://github.com/awslabs/AutoCorrode/blob/200f1acf2d264f2dedee33792b986ebe73c224a3/Data_Structures/RedBlackTree_Extensional.thy#L157-L160) ([local copy](code/Data_Structures/RedBlackTree_Extensional.thy))

```isabelle
lemma rbt_ext_eqI:
  assumes \<open>rbt_ext_\<alpha> rm0 = rbt_ext_\<alpha> rm1\<close>
    shows \<open>rm0 = rm1\<close>
using assms by transfer (simp add: rbt_ext_eq_def)
```

### child `shareable_value_option_inj`: [`Shallow_Separation_Logic/Share_Map.thy` lines 77-80](https://github.com/awslabs/AutoCorrode/blob/200f1acf2d264f2dedee33792b986ebe73c224a3/Shallow_Separation_Logic/Share_Map.thy#L77-L80) ([local copy](code/Shallow_Separation_Logic/Share_Map.thy))

```isabelle
lemma shareable_value_option_inj:
  assumes \<open>shareable_value_option a = shareable_value_option b\<close>
    shows \<open>a = b\<close>
using assms by (auto simp add: shareable_value_option_def split!: option.splits)
```

### How the parts fit

The glue is the single `metis` line (120-121). After `unfolding
rbt_share_map_\<alpha>_def`, the assumption `rbt_share_map_\<alpha> rm0 =
rbt_share_map_\<alpha> rm1` is the pointwise equality of `\<lambda>a.
shareable_value_option (rbt_ext_\<alpha> (rbt_share_map rm) a)`. `metis` then
assembles the conclusion by one lemma after another:

1. `ext` (HOL function extensionality) turns the function equality into
   pointwise equality of the two wrapped values;
2. `shareable_value_option_inj` cancels the injective `shareable_value_option`
   wrap, leaving `rbt_ext_\<alpha> (rbt_share_map rm0) a = rbt_ext_\<alpha>
   (rbt_share_map rm1) a` for every key `a`;
3. `rbt_ext_eqI` collapses that to `rbt_share_map rm0 = rbt_share_map rm1`,
   equality of the two wrapped `rbt_ext` trees;
4. `rbt_share_map.expand` (the datatype-package generator) lifts it to
   `rm0 = rm1`.

Lemma graph:

```
rbt_share_map_eqI            (parent, Share_Map.thy 117-121)
 ├─ rbt_ext_eqI              (child, RedBlackTree_Extensional.thy 157-160)
 └─ shareable_value_option_inj (child, Share_Map.thy 77-80)
```

`ext`, `rbt_share_map.expand` and the unfolding of `rbt_share_map_\<alpha>_def`
are also steps of the glue, but they are library or datatype-package theorems,
not project lemmas, so the two named children are the ones the decomposition
carries.

Each child is a good leaf — a self-contained statement whose proof closes on
its own:

- `shareable_value_option_inj` states that the case-function
  `shareable_value_option` is injective, and closes with `auto` plus
  `option.splits`, a one-step case analysis on the `option` argument; it cites
  no other lemma.
- `rbt_ext_eqI` states the extensionality principle for the quotient type
  `rbt_ext`, and closes with `transfer` back to the defining
  `rbt_ext_eq_def`; it also cites no other lemma.

So the whole theorem is two independent leaves joined by one `metis` call: the
shape a bounded prover would be asked to produce (one hole per leaf).

## Why it is good

1. (check) `rbt_share_map_eqI` is declared in `Shallow_Separation_Logic/Share_Map.thy`
   at lines 117-121 — the parent site is exactly the lemma and its 4-line proof.
2. (check) The parent's glue cites `rbt_ext_eqI` (line 121).
3. (check) The parent's glue cites `shareable_value_option_inj` (line 121).
4. (check) `rbt_share_map_eqI` occurs 13 times in `Shallow_Separation_Logic/Share_Map.thy`:
   once as its declaration and 12 more as an `intro!:` / `metis` target, so the
   once-proved principle is reused across the whole file (lens laws, the `apart`,
   `sepalg`, `strong_sepalg` and `cancellative_sepalg` instances, and the domain
   decomposition lemmas).
5. (measurement) The move is theorem-scale: 2 direct lemmas, depth 1, a 5-line glue
   and 4-line children (see the `shape` in `entry.json`).

In my opinion the detail worth copying is not `ext` itself but the choice to
name the extensionality principle `rbt_share_map_eqI` once and then let every
subsequent equality of share maps close by `intro!: rbt_share_map_eqI` — the
abstraction does the unfolding, so clients never touch `RmShareMap`.

## When to use it, and when not

Use it when an equality `x = y` of a record- or quotient-wrapped map-like type
is decided by pointwise equality of an abstraction `\<alpha> :: T \<Rightarrow> 'k
\<Rightarrow> 'v`, the abstraction is injective (or has an extensionality
principle for the underlying representation), and the equality is needed many
times so a once-proved principle pays off. This is the same move as proving set
or function equality with `ext`/`set_eqI`, lifted to a named interface lemma.

Avoid it when the abstraction is not injective — two distinct structures can
then share one abstraction and the principle is false; when the underlying type
has no quotient or extensionality lemma to rest on; or when the equality is
needed only once, where the named lemma is overhead and an inline `ext` suffices.

## Consequences

The move creates two soundness obligations: injectivity of the value-option
wrap (`shareable_value_option_inj`) and extensionality of the underlying
red-black-tree quotient (`rbt_ext_eqI`, itself resting on the `rbt_ext_eq`
quotient of `rbt_ext`). Once proved, every client equality closes by `intro!:
rbt_share_map_eqI` plus `ext` and the abstraction's `simp` lemmas, without
unfolding `RmShareMap` or `rbt_ext`. Failure modes: the principle gives the
forward direction only (`rbt_share_map_eqE`, the reverse, is a separate lemma
stated right after); and it applies only to goals already shaped as
`rbt_share_map_\<alpha> x = rbt_share_map_\<alpha> y`, so a goal of any other
shape must unfold the representation instead.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/ci.yml (build job runs 'isabelle build -v -b -d . AutoCorrode', which builds the AutoCorrode session; ROOT lists Data_Structures and Shallow_Separation_Logic sessions, so RedBlackTree_Extensional.thy and Share_Map.thy are built); commit 200f1acf2d264f2dedee33792b986ebe73c224a3 is the tip of default branch main | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: rbt_ext_eqI@Shallow_Separation_Logic/Share_Map.thy:121, shareable_value_option_inj@Shallow_Separation_Logic/Share_Map.thy:121; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at 200f1acf2d264f2dedee33792b986ebe73c224a3 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(rbt_share_map_eqI, Shallow_Separation_Logic/Share_Map.thy, 117-121) -> declared: rbt_share_map_eqI is declared at Shallow_Separation_Logic/Share_Map.thy:117 | check_claims.py |
| 2 | verified | cites(parent, rbt_ext_eqI) -> cites: rbt_ext_eqI occurs at Shallow_Separation_Logic/Share_Map.thy:121 | check_claims.py |
| 3 | verified | cites(parent, shareable_value_option_inj) -> cites: shareable_value_option_inj occurs at Shallow_Separation_Logic/Share_Map.thy:121 | check_claims.py |
| 4 | verified | count(rbt_share_map_eqI, 13, Shallow_Separation_Logic/Share_Map.thy) -> count: rbt_share_map_eqI occurs 13 times in 1 file(s) matching Shallow_Separation_Logic/Share_Map.thy | check_claims.py |
| 5 | verified | read the three site line ranges in code/: parent rbt_share_map_eqI spans 117-121 (5 lines, 'lemma rbt_share_map_eqI:' through 'by (metis (lifting) ext rbt_ext_eqI rbt_share_map.expand shareable_value_option_inj)'); child rbt_ext_eqI spans 157-160 (4 lines); child shareable_value_option_inj spans 77-80 (4 lines). Both children are the only two direct lemmas and are cited in the parent's proof line; neither child depends on a further project lemma (rbt_ext_eqI closes by transfer/simp with rbt_ext_eq_def, shareable_value_option_inj by auto), so longest chain below the parent is 1 | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent rbt_share_map_eqI (Share_Map.thy 117-121) and children rbt_ext_eqI (RedBlackTree_Extensional.thy 157-160) and shareable_value_option_inj (Share_Map.thy 77-80) match the code verbatim; closing methods match (transfer (simp add: rbt_ext_eq_def) / auto simp add: shareable_value_option_def split!: option.splits); all three close with by-proofs and no sorry; the glue (metis (lifting) ext rbt_ext_eqI rbt_share_map.expand shareable_value_option_inj) cites exactly the two project-lemma children, with ext and rbt_share_map.expand correctly treated as library/datatype theorems, not children; shape numbers right per fields.md convention (glue_lines=parent site span 5, child_lines=4/4, direct_lemmas=2, depth=1); count rbt_share_map_eqI=13 confirmed (1 declaration + 12 uses). | reviewer-correctness |
| generality | accept | Generality holds. The move is generalized beyond the example: 'When to use it' states it for any equality on a record-/quotient-wrapped map-like type decided by pointwise equality of an injective abstraction alpha::T=>'k=>'v, and names the analogue (ext/set_eqI). 'When not to use' is honest and specific: non-injective abstraction makes the principle false; no underlying quotient/extensionality lemma; single-use where the named lemma is overhead vs inline ext. Consequences are concrete: two soundness obligations (injectivity shareable_value_option_inj, quotient extensionality rbt_ext_eqI), forward direction only (rbt_share_map_eqE is separate, confirmed at lines 123-127), and applies only to alpha-shaped goals. It says explicitly what makes the leaves good for a bounded prover: each child is self-contained, closes on its own (auto+option.splits; transfer to rbt_ext_eq_def), cites no other lemma, so the theorem is two independent leaves joined by one metis call - one hole per leaf. | reviewer-generality |
| provenance-licence | accept | Permalinks (files and sites) all pin commit 200f1acf2d264f2dedee33792b986ebe73c224a3 and paths Shallow_Separation_Logic/Share_Map.thy and Data_Structures/RedBlackTree_Extensional.thy; the cited line ranges 117-121, 77-80, 157-160 match the statements in the copied code. Commit agrees across entry.json source.commit, sources/autocorrode/SOURCE.md and source.json. Licence MIT is recorded in entry.json and SOURCE.md, and sources/autocorrode/upstream-LICENSE is the MIT text. check_provenance passes: 2 files byte-identical at the pinned commit. Everything traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/awslabs/AutoCorrode at commit `200f1acf2d264f2dedee33792b986ebe73c224a3`, under `MIT`; see the [source note](../../sources/autocorrode/SOURCE.md) for the licence text and attribution.
