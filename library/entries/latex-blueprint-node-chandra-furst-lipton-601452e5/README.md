# Blueprint node: lower bound for D(eval) via the corner-colouring number

| | |
|---|---|
| Kind | instance |
| Move | blueprint-node |
| Language | latex |
| Status | accepted |
| Source | [chandra-furst-lipton](../../sources/chandra-furst-lipton/SOURCE.md) at `95c7ea0802c1` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T15:17:29Z |

## Intent

The paper's lower bound `D(eval) ≥ ⌈log₂ χ_d(G)⌉` is stated as a node of the
published blueprint dependency graph *before* it is formalised (the theorem's
own `\lean{}` is commented out), and its proof is a two-sentence glue that
names exactly two lemmas. The decomposition's whole content is in those two
named lemmas, each a self-contained statement with its own proof and a
`\lean{}`/`\leanok` marker.

## The decomposition

### parent `thm:det-fun-complex-eval-ge-corner-color-num`: [`blueprint/src/chapter/2-lower-bound-eval.tex` lines 49-62](https://github.com/yaeldillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/blueprint/src/chapter/2-lower-bound-eval.tex#L49-L62) ([local copy](code/blueprint/src/chapter/2-lower-bound-eval.tex))

```latex
\begin{theorem}[Lower bound for $D(\eval)$ in terms of $\chi_d(G)$]
  \label{thm:det-fun-complex-eval-ge-corner-color-num}
  \uses{def:det-fun-complex, def:eval, def:corner-color-num}
  % \lean{}
  % \leanok

  $$D(\eval) \ge \lceil\log_2\chi_d(G)\rceil$$
\end{theorem}
\begin{proof}
  \uses{lem:mono-forbidden-pattern-trivial, lem:forbidden-pattern-project-multicorner}
  % \leanok

  Let $P$ be a protocol valid in time $t$ for $\eval$. By Lemma \ref{lem:mono-forbidden-pattern-trivial}, $\broad(\cdot, t)$ is a coloring of $\{x \mid \sum_i x_i = 0\}$ in at most $2^t$ colors (since $t$ bits were broadcasted) such that all monochromatic forbidden patterns are trivial. By Lemma \ref{lem:forbidden-pattern-project-multicorner}, this yields a coloring of $G^{d - 1}$ in at most $2^t$ colors such all monochromatic corners are trivial. Hence $2^t \ge \chi_d(G)$, as wanted.
\end{proof}
```

### child `lem:forbidden-pattern-project-multicorner`: [`blueprint/src/chapter/2-lower-bound-eval.tex` lines 18-32](https://github.com/yaeldillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/blueprint/src/chapter/2-lower-bound-eval.tex#L18-L32) ([local copy](code/blueprint/src/chapter/2-lower-bound-eval.tex))

```latex
\begin{lemma}[Forbidden patterns project to multidimensional corners]
  \label{lem:forbidden-pattern-project-multicorner}
  \uses{def:forbidden-pattern, def:multicorner, def:forget, def:eval}
  \lean{NOF.isMultidimCorner_forget_of_isForbiddenPattern}
  \leanok

  If $(a_1, \dots, a_d)$ is a forbidden pattern such that $\eval(a_i) = 1$ for all $i$, then
  $$(\forget_i(a_1), \dots, \forget_i(a_d))$$
  is a multidimensional corner for all index $i$.
\end{lemma}
\begin{proof}
  \uses{}
  \leanok
  Let $v$ be the tip of $(a_1, \dots, a_d)$. Then, using that $\sum_k a_{j, k} = 0$ and $v_k = a_{j, k}$ for all $k \ne j$, we see that $v_j = a_{j, j} + \sum_k v_k$. This means that $(\forget_i(a_1), \dots, \forget_i(a_d)$ is a multidimensional corner by setting $x = \forget_i(a_i)$ and $c = \sum_k v_k$.
\end{proof}
```

### child `lem:mono-forbidden-pattern-trivial`: [`blueprint/src/chapter/2-lower-bound-eval.tex` lines 34-47](https://github.com/yaeldillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/blueprint/src/chapter/2-lower-bound-eval.tex#L34-L47) ([local copy](code/blueprint/src/chapter/2-lower-bound-eval.tex))

```latex
\begin{lemma}[Monochromatic forbidden patterns are trivial]
  \label{lem:mono-forbidden-pattern-trivial}
  \uses{def:forbidden-pattern, def:valid-protocol, def:eval}
  \lean{NOF.trivial_of_isForbiddenPattern_of_isValid_eval}
  \leanok

  Given $P$ a NOF protocol valid in time $t$ for $\eval$, all monochromatic forbidden patterns are trivial.
\end{lemma}
\begin{proof}
  \uses{lem:length-broadcast, lem:mono-forbidden-pattern-tip}
  \leanok

  Assume $(a_1, \dots, a_d)$ is a monochromatic forbidden pattern with tip $v$, say $\broad(a_i, t) = b$ for all $i$. By Lemma \ref{lem:mono-forbidden-pattern-tip}, we also have $\broad(v, t) = b$. Since $P$ is a valid NOF protocol for $\eval$, we get $\eval(a_i) = \eval(v)$ for all $i$, meaning that $(a_1, \dots, a_d) = (v, \dots, v)$ is trivial.
\end{proof}
```

How the parts fit. The parent theorem `thm:det-fun-complex-eval-ge-corner-color-num`
(statement lines 49-56, proof lines 57-62) is the glue. Its proof `\uses{}`
(line 58) cites the two children and its prose combines them in two sentences:
first `lem:mono-forbidden-pattern-trivial` turns a protocol valid in time `t`
into a colouring `broad(·, t)` of `{x | Σᵢ xᵢ = 0}` in at most `2^t` colours
whose monochromatic forbidden patterns are trivial; then
`lem:forbidden-pattern-project-multicorner` projects that colouring to a
colouring of `G^(d-1)` with no non-trivial monochromatic corner; minimality of
`χ_d(G)` then gives `2^t ≥ χ_d(G)`, hence `D(eval) ≥ ⌈log₂ χ_d(G)⌉`. The two
children close on their own, so the proof above them is exactly two citations.

Lemma graph (which lemma uses which, read from the `\uses{}` lines):

- `thm:det-fun-complex-eval-ge-corner-color-num` (49-62) uses
  `lem:mono-forbidden-pattern-trivial` and
  `lem:forbidden-pattern-project-multicorner` (line 58).
- `lem:mono-forbidden-pattern-trivial` (34-47) uses `lem:length-broadcast` and
  `lem:mono-forbidden-pattern-tip` (line 43), both declared in
  `blueprint/src/chapter/1-nof-model.tex`.
- `lem:forbidden-pattern-project-multicorner` (18-32) uses only definitions
  (`def:forbidden-pattern, def:multicorner, def:forget, def:eval`, line 20); its
  proof `\uses{}` is empty.

Why each child is a good leaf. `lem:forbidden-pattern-project-multicorner` is a
self-contained statement whose proof (lines 28-32) closes directly from the
definitions with no further lemma — it is a true leaf. `lem:mono-forbidden-pattern-trivial`
is self-contained in statement, and its proof closes from two named siblings
(`lem:length-broadcast`, a one-line induction, and
`lem:mono-forbidden-pattern-tip`), so it is "nearly trivial given its
dependencies" rather than a long inline argument.

Both children carry `\lean{}` and `\leanok` markers (lines 21-22 and 37-38),
pointing at their Lean declarations: `NOF.isMultidimCorner_forget_of_isForbiddenPattern`
(`ChandraFurstLipton/MultidimCorners.lean:40-55`) and
`NOF.trivial_of_isForbiddenPattern_of_isValid_eval`
(`ChandraFurstLipton/LowerBoundEval.lean:31-52`), both copied here. The parent
theorem, by contrast, has its `\lean{}` and `\leanok` commented out (lines
52-53), which is the "stated before proved" signature of a blueprint node: the
top of the graph is not yet formalised while its two lemmas are.

## Why it is good

1. The parent site cites `lem:mono-forbidden-pattern-trivial` — the first of the
   two lemmas the glue combines (`check`, lines 49-62).
2. The parent site cites `lem:forbidden-pattern-project-multicorner` — the
   second lemma (`check`, lines 49-62).
3. The Lean declaration of `lem:mono-forbidden-pattern-trivial`
   (`ChandraFurstLipton/LowerBoundEval.lean` lines 31-52) contains no `sorry`,
   `admit` or `axiom` (`check`, lines 31-52).
4. The Lean declaration of `lem:forbidden-pattern-project-multicorner`
   (`ChandraFurstLipton/MultidimCorners.lean` lines 40-55) contains no `sorry`,
   `admit` or `axiom` (`check`, lines 40-55).
5. The main proof's `\uses{}` names exactly 2 lemmas
   (`shape.direct_lemmas = 2`), counted at line 58
   (`measurement`, [line 58](https://github.com/yaeldillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/blueprint/src/chapter/2-lower-bound-eval.tex#L58)).

In my opinion the detail worth copying is the two-sentence glue: the theorem is
stated as a node whose entire proof is two citations, so the *decomposition* is
the theorem, and the *proof* is distributed to the two named lemmas. The
author's own prose makes the composition explicit — "By Lemma … this yields a
coloring of G^{d-1} … such all monochromatic corners are trivial. Hence
2^t ≥ χ_d(G), as wanted" (line 61) — which is exactly the skeleton shape
AutoDecompose must produce.

## When to use it, and when not

Use the `blueprint-node` shape when a project publishes a dependency graph
(`\label{}` + `\uses{}` edges) whose headline theorem is stated before it is
proved, and whose proof is a short glue over a small number of named lemmas
each with its own statement, proof and `\lean{}` marker. It fits when the
content of the argument lives in the lemmas, not in the glue — here the glue is
two sentences.

Avoid it when the "proof" is one long inline argument with no named
intermediate lemmas, when the supposed children are not separate labelled nodes
(with their own `\label` and `\uses`), or when the top theorem is already fully
formalised (no "stated before proved" gap to record). It also does not by itself
show *why* the split is good — that is the lemmas' short, self-contained proofs,
which is a separate fact to check.

## Consequences

The top node's `\lean{}`/`\leanok` are commented out (lines 52-53), so the
decomposition is "stated before proved": closing the node still requires a
future formalisation of the theorem from its two lemmas. The glue needs the two
children to be *exactly* sufficient — `lem:mono-forbidden-pattern-trivial` must
deliver a colouring with trivial monochromatic forbidden patterns, and
`lem:forbidden-pattern-project-multicorner` must project it to a corner-free
colouring of `G^(d-1)`; weakening either breaks the minimality step
`2^t ≥ χ_d(G)`. The second child is not a leaf in the strict sense: its proof
defers to two further project lemmas (`lem:length-broadcast`,
`lem:mono-forbidden-pattern-tip` in `1-nof-model.tex`), so its closure is
carried by named siblings rather than self-contained.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push.yml: 'build' job runs leanprover/lean-action (builds all ChandraFurstLipton/*.lean incl. LowerBoundEval.lean and MultidimCorners.lean) and 'build-docgen' runs docgen-action with blueprint:true (builds blueprint/src/chapter/2-lower-bound-eval.tex); commit 95c7ea0802c195bef2238ad962873c0907f1f8a9 on default branch master | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| provenance | pass | 4 file(s) byte-identical at 95c7ea0802c195bef2238ad962873c0907f1f8a9 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, lem:mono-forbidden-pattern-trivial) -> cites: lem:mono-forbidden-pattern-trivial occurs at blueprint/src/chapter/2-lower-bound-eval.tex:58 | check_claims.py |
| 2 | verified | cites(parent, lem:forbidden-pattern-project-multicorner) -> cites: lem:forbidden-pattern-project-multicorner occurs at blueprint/src/chapter/2-lower-bound-eval.tex:58 | check_claims.py |
| 3 | verified | no_sorry(ChandraFurstLipton/LowerBoundEval.lean, 31-52) -> no_sorry: none of sorry, admit, axiom in ChandraFurstLipton/LowerBoundEval.lean:31-52 | check_claims.py |
| 4 | verified | no_sorry(ChandraFurstLipton/MultidimCorners.lean, 40-55) -> no_sorry: none of sorry, admit, axiom in ChandraFurstLipton/MultidimCorners.lean:40-55 | check_claims.py |
| 5 | verified | read copied code/blueprint/src/chapter/2-lower-bound-eval.tex line 58: \uses{lem:mono-forbidden-pattern-trivial, lem:forbidden-pattern-project-multicorner} — exactly the two named lemmas, matching the claim | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Shape numbers and decomposition all check against the copied code. Parent site = 2-lower-bound-eval.tex 49-62 (14 lines = glue_lines), child1 = 18-32 (15 lines), child2 = 34-47 (14 lines), matching child_lines [15,14]. Proof \uses{} at line 58 names exactly lem:mono-forbidden-pattern-trivial and lem:forbidden-pattern-project-multicorner (direct_lemmas=2); those two are exactly the children and no other lemma is cited in the glue. depth=3 verified from 1-nof-model.tex: mono-forbidden-pattern-trivial -> mono-forbidden-pattern-tip -> length-broadcast is a 3-lemma chain below the theorem. Children close: child1 proof 28-32 with empty \uses{}; child2 proof 42-47 citing lem:length-broadcast and lem:mono-forbidden-pattern-tip; both carry \lean{}/\leanok and their Lean declarations exist at LowerBoundEval.lean:31-52 and MultidimCorners.lean:40-55 with no sorry/admit/axiom. Parent's \lean{}/\leanok commented out (52-53) matches the stated-before-proved node as documented. No correctness defect. | reviewer-correctness |
| generality | accept | Move is stated generally (applicability.goal_shape/use_when/avoid_when and README 'When to use it' describe a blueprint-node as a headline theorem stated before proved, glued from a small number of named self-contained lemmas with \lean{} markers, not tied to this example). avoid_when names concrete failure modes: one long inline argument, children not separate labelled nodes, or the theorem already fully formalised. Consequences are honest and specific: top node's \lean{}/\leanok commented out (lines 52-53) so closure still needs future formalisation; glue needs the two children exactly sufficient or the minimality step 2^t >= chi_d(G) breaks; and it admits the second child is not a strict leaf (its proof cites lem:length-broadcast and lem:mono-forbidden-pattern-tip). It says what makes the lemmas good leaves ('Why each child is a good leaf', README 104-110): one closes directly from definitions with empty \uses{}, the other from two named siblings, i.e. short self-contained statements rather than a long inline argument. Confirmed against copied code lines 18-62. | reviewer-generality |
| provenance-licence | accept | Provenance and licence fully consistent: check_provenance reports 4 file(s) byte-identical at commit 95c7ea0802c195bef2238ad962873c0907f1f8a9; entry.json files[4] match the code/ tree exactly (LowerBoundEval.lean, MultidimCorners.lean, NOFModel.lean, blueprint/src/chapter/2-lower-bound-eval.tex); all permalinks point at that commit and path; README short commit 95c7ea0802c1 is the 12-char prefix of the pinned full hash; licence Apache-2.0 agrees across entry.json, source.json, SOURCE.md and the copied upstream-LICENSE (Apache 2.0 text); README's line citations (parent 49-62, children 18-32 and 34-47) match the copied .tex verbatim; SOURCE.md licence_files=[LICENSE] and the relative source-note link resolves to library/sources/chandra-furst-lipton/SOURCE.md. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/yaeldillies/chandra-furst-lipton at commit `95c7ea0802c195bef2238ad962873c0907f1f8a9`, under `Apache-2.0`; see the [source note](../../sources/chandra-furst-lipton/SOURCE.md) for the licence text and attribution.
