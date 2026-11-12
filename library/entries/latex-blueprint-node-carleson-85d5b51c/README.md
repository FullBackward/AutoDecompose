# Blueprint node finitary-Carleson: finitary Carleson bound proved from four upstream nodes

| | |
|---|---|
| Kind | instance |
| Move | blueprint-node |
| Language | latex |
| Status | accepted |
| Source | [carleson](../../sources/carleson/SOURCE.md) at `d75f54374f7f` |
| Licence | `Apache-2.0` |

## Intent

The blueprint node `finitary-Carleson` freezes its statement and Lean name
(`finitary_carleson`) before any proof text, then proves the finitary Carleson
bound by composing four already-stated upstream nodes, each declared in one
`\uses{}` line: `grid-existence` and `tile-structure` carry the continuous
operator to a dyadic model, `discrete-Carleson` supplies the dyadic bound, and
`tile-sum-operator` carries the dyadic estimate back to the original operator.

## The decomposition

### parent `finitary-Carleson`: [`blueprint/src/chapter/main.tex` lines 444-458](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/blueprint/src/chapter/main.tex#L444-L458) ([local copy](code/blueprint/src/chapter/main.tex))

```latex
\begin{proposition}[finitary Carleson]
\label{finitary-Carleson}
\leanok
\lean{finitary_carleson}
\uses{discrete-Carleson, grid-existence, tile-structure, tile-sum-operator}
Let ${\sigma_1},\sigma_2\colon X\to \mathbb{Z}$ be measurable functions with finite range and ${\sigma_1}\leq \sigma_2$.  Let $F,G$ be bounded Borel sets in $X$. Then there is a Borel set $G'$ in $X$ with $2\mu(G')\leq \mu(G)$ such that
for all Borel functions $f:X\to \C$ with $|f|\le \mathbf{1}_F$.
\begin{equation*}
    \int_{G \setminus G'} \left|\sum_{s={\sigma_1}(x)}^{{\sigma_2}(x)} \int K_s(x,y) f(y) e(\tQ(x)(y)) \, \mathrm{d}\mu(y) \right| \mathrm{d}\mu(x)
\end{equation*}
\begin{equation}
    \label{eq-linearized}
    \le \frac{2^{442a^3}}{(q-1)^5} \mu(G)^{1-\frac{1}{q}} \mu(F)^{\frac 1 q}\,.
\end{equation}
\end{proposition}
```

### skeleton `finitary-Carleson-proof`: [`blueprint/src/chapter/main.tex` lines 1303-1320](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/blueprint/src/chapter/main.tex#L1303-L1320) ([local copy](code/blueprint/src/chapter/main.tex))

```latex
We use this to prove \Cref{finitary-Carleson}.
\begin{proof}[Proof of \Cref{finitary-Carleson}]
\proves{finitary-Carleson}
\leanok
We now estimate with \Cref{tile-sum-operator} and \Cref{discrete-Carleson}
\begin{equation}
 \int_{G \setminus G'} \left|\sum_{s={\sigma_1}(x)}^{{\sigma_2}(x)} \int K_s(x,y) f(y) e(\tQ(x)(y)) \, \mathrm{d}\mu(y)\right| \mathrm{d}\mu(x)
\end{equation}
\begin{equation}
 =\int_{G \setminus G'} \left|\sum_{s={\sigma_1}(x)}^{{\sigma_2}(x)} \int K_s(x,y) f(y) e(\tQ(x)(y) - \tQ(x)(x))\mathrm{d}\mu(y)\right| \mathrm{d}\mu(x)
\end{equation}
\begin{equation}
 =\int_{G \setminus G'} \left|\sum_{\fp\in \fP}T_{\fp} f(x)\right| \mathrm{d}\mu(x)
 \le \frac{2^{442a^3}}{(q-1)^5} \mu(G)^{1 - \frac{1}{q}} \mu(F)^{\frac{1}{q}} \,.
\end{equation}
This proves \eqref{eq-linearized} for the chosen set $G'$ and arbitrary $f$ and thus completes the proof of Proposition
\ref{finitary-Carleson}.
\end{proof}
```

### context `finitary-Carleson-setup`: [`blueprint/src/chapter/main.tex` lines 1261-1264](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/blueprint/src/chapter/main.tex#L1261-L1264) ([local copy](code/blueprint/src/chapter/main.tex))

```latex
Choose a grid structure $(\mathcal{D}, c,s)$ with \Cref{grid-existence} and a tile structure for this
grid structure $(\fP,\scI,\fc,\fcc,\pc,\ps)$ with \Cref{tile-structure}.
Applying \Cref{discrete-Carleson}, we obtain a Borel set $G'$ in $X$ with $2\mu(G')\leq \mu(G)$ such that for all Borel functions $f:X\to \C$ with $|f|\le \mathbf{1}_F$
we have \eqref{disclesssim}.
```

How the parts fit. The parent `finitary-Carleson` is declared with its
statement, Lean name `finitary_carleson` and `\leanok` before any proof is
written; its `\uses{}` line then names the four upstream nodes it depends on.
The proof (deferred to `\Cref{christsection}`, the section "Proof of Finitary
Carleson") composes those four nodes:

- `grid-existence` supplies a grid structure `(𝒟, c, s)`, and `tile-structure`
  supplies a tile structure for that grid (the setup excerpt above, lines
  1261-1262).
- `discrete-Carleson` (the dyadic-model theorem) is applied to those structures
  to obtain the set `G'` with `2μ(G') ≤ μ(G)` and the dyadic bound
  `(disclesssim)` (line 1263).
- `tile-sum-operator` rewrites the tile sum back into the original operator
  (line 1307), so the dyadic estimate becomes the desired bound
  `(eq-linearized)`, closing the proposition (lines 1307-1320).

Every step closes by citing an upstream node whose statement was fixed earlier
elsewhere in the graph; no new lemma is introduced inside this proof. The
separate Lean proof `finitary_carleson` in [`Carleson/FinitaryCarleson.lean`](code/Carleson/FinitaryCarleson.lean) mirrors the same four facts by the same
names: `grid_existence X`, `tile_existence X`,
`rcases discrete_carleson X with ⟨G', hG', h2G', hfG'⟩`, and
`tile_sum_operator hx`.

## Why it is good

1. The parent node is stated with `\lean{finitary_carleson}\leanok` (line 447)
   and a `\uses{discrete-Carleson, grid-existence, tile-structure,
   tile-sum-operator}` line (line 448) naming four upstream nodes, before its
   proof (lines 1303-1320)
   ([lines 444-458](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/blueprint/src/chapter/main.tex#L444-L458)).
   Evidence kind: `check`.
2. The proof (lines 1303-1320) closes the bound by citing
   `\Cref{tile-sum-operator}` and `\Cref{discrete-Carleson}` at line 1307 and
   ends "This proves … and thus completes the proof of Proposition
   finitary-Carleson", introducing no new node
   ([lines 1303-1320](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/blueprint/src/chapter/main.tex#L1303-L1320)).
   Evidence kind: `check`.
3. Each of the four labels in `\uses{}` is defined at its own site in the same
   file with a `\label{}` and a `\lean{}` name — `discrete-Carleson` (L552-556),
   `grid-existence` (L1239-1243), `tile-structure` (L1252-1256),
   `tile-sum-operator` (L1266-1269) — so the dependency cone is a set of named
   nodes, not inline proof text. Evidence kind: `check`.
4. The node cites 4 upstream nodes, with a statement of 15 lines (444-458) and
   a proof of 18 lines (1303-1320), counted from the `\uses{}` list and the
   line ranges at the pinned commit. Evidence kind: `measurement`.
5. The lemma `linearized-truncation` (lines 1179-1196) consumes
   `finitary-Carleson` via `\uses{finitary-Carleson}` on line 1183 and applies
   it recursively in its proof (lines 1198-1222), so the node is a reusable
   dependency, not a one-off
   ([lines 1179-1222](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/blueprint/src/chapter/main.tex#L1179-L1222)).
   Evidence kind: `known-use`.

In my opinion the detail worth copying is the discipline of the `\uses{}` line:
the four dependencies are named up front, and the proof body is then just a
chain of `\Cref{}` calls, so a reader can check the node's sufficiency against
a fixed list rather than re-reading the whole proof.

## When to use it, and when not

Use it when the result is a known combination of already-stated (or
already-proved) nodes and the proof is a sequence in which each step invokes
exactly one upstream node; when the statement can be frozen, with its Lean name
and `\leanok`, before the proof is written; and when you want the node's
dependencies listed up front (`\uses{}`) so sufficiency is checkable against a
fixed list. The proof may live elsewhere — here in a later section, and again
as a separate Lean file — and only cite the nodes.

Avoid it when the proof needs a new construction or a new lemma that must itself
be stated and proved — that belongs as its own node in the graph, not inline in
this one; when the statement may still change (then do not fix the Lean name
yet); or when the cited nodes' hypotheses do not line up into a single
composition, in which case forcing them into a linear citation chain leaves
gaps.

## Consequences

Freezing the statement first means the Lean name `finitary_carleson` must
correspond to a provable Lean statement; if the statement later changes, the
name and the `\lean{}` marker change with it. The four children are discharged
in a fixed order — `grid-existence` and `tile-structure` produce the grid and
tile structures, `discrete-Carleson` consumes them to give the set `G'` and the
dyadic bound, and `tile-sum-operator` rewrites the tile sum back to the
original operator — so each citation's hypotheses are met only in that state;
invoking one earlier leaves a gap. A citation whose hypotheses do not line up
leaves a silent gap, because `\leanok` is a claim the project's build verifies,
not something the LaTeX text itself enforces. The proof is split across two
places (the LaTeX proof and `Carleson/FinitaryCarleson.lean`), so the two must
be kept in correspondence.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push.yml build_project job runs leanprover/lean-action with build:true, build-args 'Carleson Challenge Solution' on push to master; commit d75f54374f7f930e70a86b443f20d0e0935c275e is HEAD of default branch master (api default_branch=master) | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 2 file(s) byte-identical at d75f54374f7f930e70a86b443f20d0e0935c275e | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | main.tex L446=\leanok, L447=\lean{finitary_carleson}, L448=\uses{discrete-Carleson, grid-existence, tile-structure, tile-sum-operator} (4 upstream nodes), proof at L1303-1320; verified against local byte-identical copy | verifier |
| 2 | verified | main.tex L1307 'We now estimate with \Cref{tile-sum-operator} and \Cref{discrete-Carleson}', L1318-1319 'This proves ... and thus completes the proof of Proposition finitary-Carleson'; no new node introduced | verifier |
| 3 | verified | main.tex discrete-Carleson L552-556 (\label{discrete-Carleson}+\lean{discrete_carleson}), grid-existence L1239-1243 (\label{grid-existence}+\lean{grid_existence}), tile-structure L1252-1256 (\label{tile-structure}+\lean{tile_existence}), tile-sum-operator L1266-1269 (\label{tile-sum-operator}+\lean{tile_sum_operator, integrable_tile_sum_operator}) | verifier |
| 4 | verified | main.tex L448 \uses{} list has 4 comma-separated labels; statement L444-458 = 15 lines (444..458 inclusive); proof L1303-1320 = 18 lines (1303..1320 inclusive) | verifier |
| 5 | verified | main.tex linearized-truncation lemma L1179-1196, L1183 \uses{finitary-Carleson}; proof L1198-1222 with L1200 'Applying \Cref{finitary-Carleson} recursively' | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent finitary-Carleson (main.tex L444-458) matches the entry: \label/\leanok/\lean{finitary_carleson} and \uses{discrete-Carleson, grid-existence, tile-structure, tile-sum-operator}. Proof (L1303-1320) cites tile-sum-operator and discrete-Carleson and closes the proposition. All four children match their closing in code: grid_existence X (FinitaryCarleson.lean L114), tile_existence X (L115), rcases discrete_carleson X with G' (L117), tile_sum_operator hx (L120); setup L1261-1264 confirms the same order. Lean theorem finitary_carleson closes (existential G' + three conjuncts, no sorry). | reviewer-correctness |
| generality | accept | Move is stated generically: goal_shape/use_when/avoid_when name the blueprint-node discipline (freeze statement+Lean name+\leanok before proof, declare deps in one \uses{} line, close by citation) with no Carleson-specific math. When-not-to-use and consequences are honest and specific: new construction belongs as its own node; don't fix the name while the statement may change; mismatched citation hypotheses leave silent gaps because \leanok is build-verified not LaTeX-enforced; proof split across LaTeX+Lean must stay in correspondence. Checked against local code/ (main.tex L444-458, L1261-1269, L1303-1320; FinitaryCarleson.lean L114-124). | reviewer-generality |
| provenance-licence | accept | check_provenance passes (2 files byte-identical at d75f54374f7f930e70a86b443f20d0e0935c275e); commit hash identical across entry.json source.commit, sources/carleson/source.json, sources/carleson/SOURCE.md and every permalink; licence Apache-2.0 recorded consistently in entry.json, source.json, SOURCE.md and matches sources/carleson/upstream-LICENSE (Apache 2.0 text); README Source-and-licence note names the same commit/licence and matches the copied code/ files; validate_entry --strict passes (excerpt hashes and permalink line anchors consistent). Everything traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/fpvandoorn/carleson at commit `d75f54374f7f930e70a86b443f20d0e0935c275e`, under `Apache-2.0`; see the [source note](../../sources/carleson/SOURCE.md) for the licence text and attribution.
