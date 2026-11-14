# Transport a composition structure along homotopies of all three edges

| | |
|---|---|
| Kind | instance |
| Move | calc-chain |
| Language | lean |
| Status | accepted |
| Source | [infinity-cosmos](../../sources/infinity-cosmos/SOURCE.md) at `89d7dc3ed861` |
| Licence | `Apache-2.0` |

## Intent

The corollary `transport_all_edges` turns a single composition structure
`CompStruct f g h` (a 2-simplex with spine `f`, `g` and diagonal `h`) into one
for the homotopic triple `f'`, `g'`, `h'`. It does this by transporting along one
edge at a time, each step a one-line `have`/`rcases` that reuses a named
single-edge transport lemma, so the whole proof is a chain of three
`Nonempty (CompStruct …)` statements rather than one large construction.

## The decomposition

### parent `transport_all_edges`: [`InfinityCosmos/ForMathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean` lines 574-583](https://github.com/emilyriehl/infinity-cosmos/blob/89d7dc3ed861824535e540da489a46469dcc8e56/InfinityCosmos/ForMathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean#L574-L583) ([local copy](code/InfinityCosmos/ForMathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean))

```lean
lemma transport_all_edges {f f' : Truncated.Edge x y} {g g' : Truncated.Edge y z}
    {h h' : Truncated.Edge x z} (hf : HomotopicL f f') (hg : HomotopicL g g') (hh : HomotopicL h h')
    (s : CompStruct f g h) :
    Nonempty (CompStruct f' g' h') := by
  have a : Nonempty (CompStruct f' g h) := transport_edge₂ s hf
  have b : Nonempty (CompStruct f' g' h) := by
    rcases a with ⟨a⟩
    exact transport_edge₀ a hg
  rcases b with ⟨b⟩
  exact transport_edge₁ b hh
```

### child `transport_edge₀`: [`InfinityCosmos/ForMathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean` lines 545-548](https://github.com/emilyriehl/infinity-cosmos/blob/89d7dc3ed861824535e540da489a46469dcc8e56/InfinityCosmos/ForMathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean#L545-L548) ([local copy](code/InfinityCosmos/ForMathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean))

```lean
lemma transport_edge₀ {f : Truncated.Edge x y} {g g' : Truncated.Edge y z} {h : Truncated.Edge x z}
    (s : CompStruct f g h) (htpy : HomotopicL g g') : Nonempty (CompStruct f g' h) := by
  rcases htpy with ⟨htpy⟩
  exact Quasicategory₂.fill32 s htpy (compId h)
```

### child `transport_edge₁`: [`InfinityCosmos/ForMathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean` lines 550-554](https://github.com/emilyriehl/infinity-cosmos/blob/89d7dc3ed861824535e540da489a46469dcc8e56/InfinityCosmos/ForMathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean#L550-L554) ([local copy](code/InfinityCosmos/ForMathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean))

```lean
@[blueprint "lem:2-truncated-qcat-htpy-comp"]
lemma transport_edge₁ {f : Truncated.Edge x y} {g : Truncated.Edge y z} {h h' : Truncated.Edge x z}
    (s : CompStruct f g h) (htpy : HomotopicL h h') : Nonempty (CompStruct f g h') := by
  rcases (HomotopicL_iff_HomotopicR.mp htpy) with ⟨htpy⟩
  exact Quasicategory₂.fill31 (idComp f) s htpy
```

### child `transport_edge₂`: [`InfinityCosmos/ForMathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean` lines 556-560](https://github.com/emilyriehl/infinity-cosmos/blob/89d7dc3ed861824535e540da489a46469dcc8e56/InfinityCosmos/ForMathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean#L556-L560) ([local copy](code/InfinityCosmos/ForMathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean))

```lean
@[blueprint "lem:2-truncated-qcat-htpy-comp"]
lemma transport_edge₂ {f f' : Truncated.Edge x y} {g : Truncated.Edge y z} {h : Truncated.Edge x z}
    (s : CompStruct f g h) (htpy : HomotopicL f f') : Nonempty (CompStruct f' g h) := by
  rcases (HomotopicL_iff_HomotopicR.mp htpy) with ⟨htpy⟩
  exact Quasicategory₂.fill31 htpy s (idComp h)
```

The glue is a chain, one child per link (survey F §10 rule 9). The parent
`transport_all_edges` holds a simplex `s : CompStruct f g h` and three homotopies
`hf : f ~ f'`, `hg : g ~ g'`, `hh : h ~ h'`, and must produce a simplex
`CompStruct f' g' h'`. It threads them one edge at a time:

1. `have a : Nonempty (CompStruct f' g h) := transport_edge₂ s hf` — transport the
   first spine edge `f` along `hf` (child `transport_edge₂`).
2. `have b : Nonempty (CompStruct f' g' h) := by rcases a with ⟨a⟩; exact transport_edge₀ a hg`
   — transport the second spine edge `g` along `hg` (child `transport_edge₀`); it
   first opens the `Nonempty` from step 1 with `rcases`.
3. `rcases b with ⟨b⟩; exact transport_edge₁ b hh` — transport the diagonal `h`
   along `hh` (child `transport_edge₁`).

Each child is a good leaf: a self-contained statement whose proof is one
`rcases` (open the homotopy) plus one horn filling `Quasicategory₂.fill31` /
`fill32`. `transport_edge₁` and `transport_edge₂` first rewrite their
`HomotopicL` hypothesis to `HomotopicR` via `HomotopicL_iff_HomotopicR` (line
498), which itself closes directly with a `constructor` and two horn fillings —
that is the depth-2 chain recorded in the `shape`.

The lemma graph (text):

```
transport_all_edges
 ├─ transport_edge₂  → HomotopicL_iff_HomotopicR
 ├─ transport_edge₀
 └─ transport_edge₁  → HomotopicL_iff_HomotopicR
```

In my opinion the detail worth copying is that the three children are not
equalities but three `Nonempty (CompStruct …)` statements, and the "chain" is
the plumbing of one lemma's output into the next lemma's `s` argument rather
than a `calc` block; the one-lemma-per-edge split is what makes each link a
one-horn-fill leaf.

## Why it is good

1. **check** — the parent site cites `transport_edge₂` (the first link of the
   chain). Form `cites(parent, transport_edge₂)`; verified by `check_claims.py`.
2. **check** — the parent site cites `transport_edge₀` (the second link). Form
   `cites(parent, transport_edge₀)`.
3. **check** — the parent site cites `transport_edge₁` (the third link). Form
   `cites(parent, transport_edge₁)`.
4. **measurement** — the theorem-scale shape: 3 direct child lemmas, glue
   (parent site) 10 lines, children 4, 5 and 5 lines, and each child's proof is
   one `rcases` plus one `Quasicategory₂.fill*` horn-filling line. Counted over
   the four site spans of the copied file.
5. **author-statement** — the authors' blueprint `proof` for the corollary says
   to "Apply the three conclusions of Lemma
   \ref{lem:2-truncated-qcat-htpy-comp} one at a time to transform the given
   2-simplex." (lines 569-572), matching the formal proof step for step.

## When to use it, and when not

Use it when a goal must transport a structured object along several independent
homotopies/equivalences/equalities, each transport being a one-line construction
over the previous one. The pattern fits any goal of shape
`(s : R f g h) → R f' g' h'` with homotopies between `f`/`f'`, `g`/`g'`, `h`/`h'`,
where `R` is a structure that composes horn-by-horn (here `CompStruct`, a
2-simplex) and each untouched edge has an identity/degenerate filler (`compId`,
`idComp`).

Avoid it when the transports are not independent (a later step needs more than
one earlier output), when an edge transport is not a one-line horn fill but a
nontrivial construction (then that edge is its own sub-decomposition), or when
the structure's own composition must commute with the transports, which may call
for a single joint lemma instead of per-edge transport.

## Consequences

The move creates one leaf per edge of the structure (here three), and a linear
plumbing obligation: each step must open the previous `Nonempty` with `rcases`
before applying the next lemma, so the glue is O(edges) `have`/`rcases` steps. If
an edge's homotopy is stated in the opposite relation (here `HomotopicL` against
the fillers' `HomotopicR`), the leaf converts it first via
`HomotopicL_iff_HomotopicR`, which adds one project lemma below the children (the
depth-2 chain). The chain has no side conditions of its own, but it relies on
the degenerate fillers `idComp`/`compId` for the edges not yet transported; a
failure mode is an edge whose transport does not preserve the other edges'
degeneracies, which would break the single-horn-fill leaf.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/blueprint.yml builds the project with lean-action (build-args ':blueprint --wfail') on push to main; pinned commit 89d7dc3ed861824535e540da489a46469dcc8e56 is on default branch main | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: transport_edge₀@InfinityCosmos/ForMathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean:581, transport_edge₁@InfinityCosmos/ForMathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean:583, transport_edge₂@InfinityCosmos/ForMathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean:578; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 89d7dc3ed861824535e540da489a46469dcc8e56 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, transport_edge₂) -> cites: transport_edge₂ occurs at InfinityCosmos/ForMathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean:578 | check_claims.py |
| 2 | verified | cites(parent, transport_edge₀) -> cites: transport_edge₀ occurs at InfinityCosmos/ForMathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean:581 | check_claims.py |
| 3 | verified | cites(parent, transport_edge₁) -> cites: transport_edge₁ occurs at InfinityCosmos/ForMathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean:583 | check_claims.py |
| 4 | verified | Copied code TwoTruncated.lean: transport_edge0 at 545-548 (4 lines), transport_edge1 at 550-554 (5 lines), transport_edge2 at 556-560 (5 lines), parent transport_all_edges at 574-583 (10 lines); each child proof is one rcases plus one exact Quasicategory2.fill31/fill32 line (lines 547-548, 553-554, 559-560) | verifier |
| 5 | verified | Copied code TwoTruncated.lean lines 569-572: (proof := /-- 'Apply the three conclusions of Lemma \ref{lem:2-truncated-qcat-htpy-comp} one at a time to transform the given 2-simplex.' -/) matches the quoted blueprint proof verbatim | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Opened local copy TwoTruncated.lean lines 545-583 and 490-500. Parent transport_all_edges (574-583, 10 lines) cites exactly transport_edge2 (line 578), transport_edge0 (line 581), transport_edge1 (line 583) and no other named lemma; entry.json statements and closed_by match the copied code verbatim; the proof closes: transport_edge2 s hf : Nonempty (CompStruct f' g h), transport_edge0 a hg : Nonempty (CompStruct f' g' h), transport_edge1 b hh : Nonempty (CompStruct f' g' h') = goal. Shape numbers correct: direct_lemmas 3, glue 10 lines (574-583), child sites 4/5/5 lines (545-548, 550-554, 556-560); depth 2 matches transport_edge1/2 using HomotopicL_iff_HomotopicR at line 498. Author-statement quote matches lines 570-571. | reviewer-correctness |
| generality | accept | Generality holds. The move is stated beyond this example via a goal-shape (s : R e0 e1 e2) -> R e0' e1' e2' with per-edge homotopies/equalities and per-edge horn-fill transports; use_when/avoid_when are honest and specific (independence of transports, one-line horn fills, degenerate fillers idComp/compId, relation conversion HomotopicL->HomotopicR, O(edges) plumbing, failure mode where a transport breaks degeneracies). It says each child is a good leaf because it is self-contained and closes with one rcases plus one Quasicategory2.fill31/fill32 horn filling, matching the bounded-prover shape. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are consistent and traceable. Copied file TwoTruncated.lean sha256 99a9422899f0a27157ea495288dba673ae571b06937584b3b69b1ed29b0329bd and 39808 bytes match entry.json; line ranges in the permalinks match the copied file exactly (parent 574-583, children 545-548/550-554/556-560, HomotopicL_iff_HomotopicR at 498). Commit 89d7dc3ed861824535e540da489a46469dcc8e56 is identical across README, entry.json, SOURCE.md and source.json; fetch_file.py retrieved the file at that commit and check_provenance recorded it byte-identical. Licence Apache-2.0 in entry.json/README/SOURCE.md/source.json, and the upstream LICENSE fetched at the pinned commit is Apache License 2.0 and byte-identical to the recorded upstream-LICENSE. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/emilyriehl/infinity-cosmos at commit `89d7dc3ed861824535e540da489a46469dcc8e56`, under `Apache-2.0`; see the [source note](../../sources/infinity-cosmos/SOURCE.md) for the licence text and attribution.
