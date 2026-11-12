# Blueprint node pfr_aux (PFR_conjecture_aux): fixed statement proved from eight labelled upstream nodes

| | |
|---|---|
| Kind | instance |
| Move | blueprint-node |
| Language | latex |
| Status | verified |
| Source | [pfr](../../sources/pfr/SOURCE.md) at `1ef23c3c5a83` |
| Licence | `Apache-2.0` |

## Intent

The blueprint node `pfr_aux` freezes its statement and Lean name
(`PFR_conjecture_aux`) before any proof text, then proves the statement by
composing eight already-stated upstream nodes, each cited by label and declared
in one `\uses{}` line. The proof is a linear chain of `\Cref{}` citations that
turns the doubling hypothesis `|A+A| ≤ K|A|` into a covering bound by a
subspace.

## The decomposition

### parent `pfr_aux`: [`blueprint/src/chapter/pfr.tex` lines 14-22](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/blueprint/src/chapter/pfr.tex#L14-L22) ([local copy](code/blueprint/src/chapter/pfr.tex))

```latex
\begin{lemma}\label{pfr_aux}
  \lean{PFR_conjecture_aux}\leanok If $A \subset {\bf F}_2^n$ is non-empty and
  $|A+A| \leq K|A|$, then $A$ can be covered by at most $K ^
  {13/2}|A|^{1/2}/|H|^{1/2}$ translates of a subspace $H$ of ${\bf F}_2^n$ with
  \begin{equation}
    \label{ah}
    |H|/|A| \in [K^{-11}, K^{11}].
  \end{equation}
  \end{lemma}
```

### skeleton `pfr_aux-proof`: [`blueprint/src/chapter/pfr.tex` lines 24-47](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/blueprint/src/chapter/pfr.tex#L24-L47) ([local copy](code/blueprint/src/chapter/pfr.tex))

```latex
\begin{proof}
\uses{entropy-pfr, unif-exist, uniform-entropy-II, jensen-bound,ruz-dist-def,ruzsa-diff,bound-conc,ruz-cov}\leanok
  Let $U_A$ be the uniform distribution on $A$ (which exists by \Cref{unif-exist}), thus $\bbH[U_A] = \log |A|$ by \Cref{uniform-entropy-II}. By \Cref{jensen-bound} and the fact that $U_A + U_A$ is supported on $A + A$, $\bbH[U_A + U_A] \leq \log|A+A|$. By \Cref{ruz-dist-def}, the doubling condition $|A+A| \leq K|A|$ therefore gives
  \[d[U_A;U_A] \leq \log K.\]
  By \Cref{entropy-pfr}, we may thus find a subspace $H$ of $\F_2^n$ such that
  \begin{equation}\label{uauh} d[U_A;U_H] \leq \tfrac{1}{2} C' \log K\end{equation}
  with $C' = 11$.
  By \Cref{ruzsa-diff} we conclude that
  \begin{equation*}
    |\log |H| - \log |A|| \leq C' \log K,
  \end{equation*}
  proving~\eqref{ah}.
  From \Cref{ruz-dist-def},~\eqref{uauh} is equivalent to
  \[\bbH[U_A - U_H] \leq \log( |A|^{1/2} |H|^{1/2}) + \tfrac{1}{2} C' \log K.\]
  By \Cref{bound-conc} we conclude the existence of a point $x_0 \in \F_p^n$ such that
  \[p_{U_A-U_H}(x_0) \geq |A|^{-1/2} |H|^{-1/2} K^{-C'/2},\]
  or equivalently
  \[|A \cap (H + x_0)| \geq K^{-C'/2} |A|^{1/2} |H|^{1/2}.\]
  Applying \Cref{ruz-cov}, we may thus cover $A$ by at most
  \[\frac{|A + (A \cap (H+x_0))|}{|A \cap (H + x_0)|} \leq \frac{K|A|}{K^{-C'/2} |A|^{1/2} |H|^{1/2}} = K^{C'/2+1} \frac{|A|^{1/2}}{|H|^{1/2}}\]
  translates of
  \[\bigl(A \cap (H + x_0)\bigr) - \bigl(A \cap (H + x_0)\bigr) \subseteq H.\]
  This proves the claim.
\end{proof}
```

### context `ruz-cov`: [`blueprint/src/chapter/pfr.tex` lines 3-12](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/blueprint/src/chapter/pfr.tex#L3-L12) ([local copy](code/blueprint/src/chapter/pfr.tex))

```latex
\begin{lemma}[Ruzsa covering lemma]
\label{ruz-cov}
\lean{Finset.ruzsa_covering_add}
\leanok
If $A,B$ are finite non-empty subsets of a group $G$, then $A$ can be covered by at most $|A+B|/|B|$ translates of $B-B$.
\end{lemma}
\begin{proof}
\leanok
Cover $A$ greedily by disjoint translates of $B$.
\end{proof}
```

How the parts fit. The parent `pfr_aux` is declared with its statement, Lean
name `PFR_conjecture_aux` and `\leanok` before any proof is written; the
`\uses{}` line of the proof then names the eight upstream nodes it depends on.
The proof is a chain in which each step invokes exactly one of those nodes:

- `unif-exist` supplies the uniform distribution `U_A` on `A`, and
  `uniform-entropy-II` gives `H[U_A] = log |A|`.
- `jensen-bound` (using that `U_A + U_A` is supported on `A + A`) gives
  `H[U_A + U_A] ≤ log |A + A|`; `ruz-dist-def` turns the doubling hypothesis
  into `d[U_A;U_A] ≤ log K`.
- `entropy-pfr` (the entropic PFR theorem, applied at `X^0_1 = X^0_2 = U_A`)
  produces the subspace `H` with `d[U_A;U_H] ≤ (1/2) C' log K`, `C' = 11`.
- `ruzsa-diff` converts that into `|log |H| - log |A|| ≤ C' log K`, closing the
  size bound (ah).
- `ruz-dist-def` again rewrites (uauh) as an entropy bound on `U_A - U_H`, and
  `bound-conc` extracts the point `x_0` where the difference concentrates,
  giving a lower bound on `|A ∩ (H + x_0)|`.
- `ruz-cov` (the Ruzsa covering lemma, shown above as context) covers `A` by
  translates of `(A ∩ (H + x_0)) - (A ∩ (H + x_0)) ⊆ H`, closing the covering
  bound.

Every step closes by citing an upstream node whose statement was fixed earlier
elsewhere in the graph; no new lemma is introduced inside this proof.

## Why it is good

1. The proof cites exactly the eight labels declared in `\uses{...}` (nine
   `\Cref{}` calls, with `ruz-dist-def` twice) and ends with "This proves the
   claim" without introducing any new node
   ([lines 24-47](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/blueprint/src/chapter/pfr.tex#L24-L47)).
   Evidence kind: `check`.
2. The statement and its Lean name are fixed before the proof and both marked
   checked — `\lean{PFR_conjecture_aux}\leanok` on line 15, `\leanok` on line 25
   ([lines 14-25](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/blueprint/src/chapter/pfr.tex#L14-L25)).
   Evidence kind: `author-statement`.
3. Each of the eight cited labels is defined at its own site with a `\label{}`
   and a `\lean{}` name, so the dependency cone is a set of named, already-stated
   nodes (see `entropy.tex`, `distance.tex`, `entropy_pfr.tex` at the cited
   lines in entry.json). Evidence kind: `check`.
4. The node cites 8 upstream nodes, a statement of 9 lines and a proof of 24
   lines (counted from the `\uses{}` list and the line ranges at the pinned
   commit). Evidence kind: `measurement`.
5. The sibling theorem `pfr` is the next node in the graph and consumes
   `pfr_aux` via `\uses{pfr_aux}` on line 56 before applying it, so the node is
   a reusable dependency
   ([lines 50-61](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/blueprint/src/chapter/pfr.tex#L50-L61)).
   Evidence kind: `known-use`.

In my opinion the detail worth copying is the discipline of the `\uses{}` line:
the eight dependencies are named up front, and the proof body is then just a
chain of `\Cref{}` calls, so a reader can check the node's sufficiency against a
fixed list rather than re-reading the whole proof.

## When to use it, and when not

Use it when the result is a known combination of already-proved (or
already-stated) lemmas and the proof is a sequence in which each step invokes
exactly one upstream node; when the statement can be frozen, with its Lean name
and `\leanok`, before the proof is written; and when you want the node's
dependencies listed up front (`\uses{}`) so sufficiency is checkable against a
fixed list.

Avoid it when the proof needs a new construction or a new lemma that must itself
be stated and proved — that belongs as its own node in the graph, not inline in
this one; when the statement may still change (then do not fix the Lean name
yet); or when the hypotheses of the cited lemmas do not line up into a single
chain, in which case forcing them into a linear citation sequence will leave
gaps.

## Consequences

Freezing the statement first means the Lean name `PFR_conjecture_aux` must
correspond to a provable Lean statement; if the statement later changes, the
name and the `\lean{}` marker change with it. The proof carries the obligation
that each cited node's hypotheses are discharged in the state where it is
invoked — for example `entropy-pfr` is applied only after `ruz-dist-def` has
turned the doubling bound into `d[U_A;U_A] ≤ log K`. A citation whose hypotheses
do not line up leaves a silent gap, because the blueprint's `\leanok` is a claim
verified by the project's build, not something the LaTeX text itself enforces.

## Verification

<!-- verification:start -->
Status: **verified**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push.yml build job -> build-docgen step (leanprover-community/docgen-action@main, blueprint:true, homepage website) compiles blueprint/src/print.tex and web.tex, which input chapter/pfr (pfr.tex); workflow runs on default branch master and commit 1ef23c3 is HEAD of master | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | read local copy pfr.tex lines 24-47: line 25 \uses{entropy-pfr, unif-exist, uniform-entropy-II, jensen-bound,ruz-dist-def,ruzsa-diff,bound-conc,ruz-cov} = 8 labels; counted 9 \Cref{} calls in body (unif-exist, uniform-entropy-II, jensen-bound, ruz-dist-def, entropy-pfr, ruzsa-diff, ruz-dist-def, bound-conc, ruz-cov), ruz-dist-def twice; ends line 46 'This proves the claim.'; no new \label/lemma inside proof | verifier |
| 2 | verified | local copy pfr.tex line 15 '\lean{PFR_conjecture_aux}\leanok' and line 25 '\uses{...}\leanok'; statement (lines 14-22) precedes proof (24-47) | verifier |
| 3 | verified | fetched entropy.tex (jensen-bound L24-29 label+\lean, unif-exist L42-46, uniform-entropy-II L66-70, bound-conc L75-79), distance.tex (ruz-dist-def L85-91, ruzsa-diff L133-138), entropy_pfr.tex (entropy-pfr L417-426), pfr.tex ruz-cov L3-12: all eight labels carry \label{} and \lean{} | verifier |
| 4 | verified | line 25 \uses{} list has 8 comma-separated labels; statement lines 14-22 inclusive = 9 lines; proof lines 24-47 inclusive = 24 lines | verifier |
| 5 | verified | local copy pfr.tex lines 50-61: theorem pfr \label{pfr} at L50, proof \uses{pfr_aux} at L56 then 'Let H be given by \Cref{pfr_aux}' at L57 | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Read the local code/blueprint/src/chapter/pfr.tex (the whole copied file). Parent (L14-22) matches entry.json: \lean{PFR_conjecture_aux}\leanok, hypothesis |A+A|<=K|A|, conclusion K^{13/2}|A|^{1/2}/|H|^{1/2} and |H|/|A| in [K^{-11},K^{11}]. Proof \uses{} list (L25) names exactly 8 labels; the body has exactly 9 \Cref{} calls all to those 8 (ruz-dist-def twice), matching claim 1, ending 'This proves the claim.' with no new node. Each child's closed_by matches the code: unif-exist/uniform-entropy-II/jensen-bound/ruz-dist-def at L26; entropy-pfr at L28 giving d[U_A;U_H]<=1/2 C' log K (C'=11); ruzsa-diff at L31 closing eq(ah); ruz-dist-def again at L36; bound-conc at L38; ruz-cov at L42. The covering bound closes as K^{C'/2+1}=K^{13/2}|A|^{1/2}/|H|^{1/2}. Sibling theorem pfr consumes pfr_aux via \uses{pfr_aux} at L56. Decomposition is faithful and closes. | reviewer-correctness |
| generality | object | use_when, avoid_when and consequences are general, honest and specific (new-construction/statement-still-changing/hypotheses-don't-line-up as avoid conditions; silent-gap failure mode as consequence). But the applicability.goal_shape field states the move applies to 'a covering/transfer theorem whose hypotheses are about a set A (non-empty, doubling |A+A| ≤ K|A|) and whose conclusion quantifies over a witness H (existence of a subspace with a size bound)' — that is the concrete math of this one instance, not the shape of the blueprint-node move, which is 'a lemma/theorem stated as a node with a frozen Lean name, whose proof is a chain of citations to already-stated upstream nodes declared in one \uses{} line'. As written it would wrongly imply the move is limited to covering/transfer theorems with a doubling hypothesis. Fix: rewrite goal_shape to the general goal class and drop (or clearly mark as this instance) the covering/transfer/doubling/subspace content. | reviewer-generality |
| provenance-licence | accept | Provenance check passes (check_provenance.py: 1 file byte-identical at 1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a); recorded sha256 a827deb5... matches local copy. Commit 1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a is identical in entry.json, sources/pfr/source.json and sources/pfr/SOURCE.md. Licence Apache-2.0 recorded consistently in entry.json, README, SOURCE.md, source.json; upstream-LICENSE is genuine Apache 2.0 text. Permalinks use the pinned commit and correct path blueprint/src/chapter/pfr.tex (local code path matches). Source note SOURCE.md present with repo URL, browse-at-commit, licence files and attribution. Everything traceable and consistent. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/teorth/pfr at commit `1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a`, under `Apache-2.0`; see the [source note](../../sources/pfr/SOURCE.md) for the licence text and attribution.
