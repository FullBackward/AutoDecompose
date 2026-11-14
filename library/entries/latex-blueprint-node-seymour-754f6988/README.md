# Blueprint node: the canonical signing of a 3-sum of matrices is TU

| | |
|---|---|
| Kind | instance |
| Move | blueprint-node |
| Language | latex |
| Status | accepted |
| Source | [seymour](../../sources/seymour/SOURCE.md) at `2769b10cb73f` |
| Licence | `Apache-2.0` |

## Intent

This is a single node of the Seymour blueprint's published dependency graph
(the `\uses{}` graph): the lemma that the canonical signing `B''` of a 3-sum of
matrices is totally unimodular (TU). Its proof is one sentence that combines two
earlier nodes — the membership lemma `toMatrixLikeSum3` places `B''` in the
3-sum-like matrix family, and the family lemma `MatrixLikeSum3.isTotallyUnimodular`
says every member of that family is TU — so the node is exactly the step that
turns a structure-membership fact into a TU fact.

## The decomposition

### parent `MatrixSum3.IsCanonicalSigning.isTotallyUnimodular`: [`blueprint/src/sum_3.tex` lines 591-604](https://github.com/Ivan-Sergeyev/seymour/blob/2769b10cb73fda17bafc0f13890dc057a2f4ff2a/blueprint/src/sum_3.tex#L591-L604) ([local copy](code/blueprint/src/sum_3.tex))

```latex
\begin{lemma}
    \label{MatrixSum3.IsCanonicalSigning.isTotallyUnimodular}
    \uses{MatrixSum3.toCanonicalSigning,Matrix.IsTotallyUnimodular}
    % \lean{}
    \leanok
    $B''$ from Definition~\ref{MatrixSum3.toCanonicalSigning} is TU.
\end{lemma}

\begin{proof}
    \uses{MatrixSum3.IsCanonicalSigning.toMatrixLikeSum3,MatrixLikeSum3.isTotallyUnimodular}
    \leanok
    Combine the results of Lemmas~\ref{MatrixSum3.IsCanonicalSigning.toMatrixLikeSum3} and~\ref{MatrixLikeSum3.isTotallyUnimodular}.
    % By Lemma~\ref{MatrixSum3.IsCanonicalSigning.toMatrixLikeSum3}, $B'' \in \mathcal{C} (X_{\ell}', Y_{\ell}', X_{r}', Y_{r}'; c_{0}'', c_{1}'')$, and by Lemma~\ref{MatrixLikeSum3.isTotallyUnimodular}, every matrix in $\mathcal{C} (X_{\ell}', Y_{\ell}', X_{r}', Y_{r}'; c_{0}'', c_{1}'')$ is TU.
\end{proof}
```

### child `MatrixSum3.IsCanonicalSigning.toMatrixLikeSum3`: [`blueprint/src/sum_3.tex` lines 528-540](https://github.com/Ivan-Sergeyev/seymour/blob/2769b10cb73fda17bafc0f13890dc057a2f4ff2a/blueprint/src/sum_3.tex#L528-L540) ([local copy](code/blueprint/src/sum_3.tex))

```latex
\begin{lemma}
    \label{MatrixSum3.IsCanonicalSigning.toMatrixLikeSum3}
    \uses{MatrixSum3.toCanonicalSigning,MatrixLikeSum3}
    % \lean{}
    \leanok
    Let $B''$ be from Definition~\ref{MatrixSum3.toCanonicalSigning}. Then $B'' \in \mathcal{C} (X_{\ell}', Y_{\ell}', X_{r}', Y_{r}'; c_{0}'', c_{1}'')$ with $X_{\ell}' = X_{\ell} \setminus \{x_{1}, x_{0}\}$, $X_{r}' = X_{r} \setminus \{x_{2}, x_{1}, x_{0}\}$, $Y_{\ell}' = Y_{\ell} \setminus \{y_{2}\}$, $Y_{r}' = Y_{r} \setminus \{y_{0}, y_{1}\}$, $x_{0}$ and $x_{1}$ are the same, $c_{0}'' = B'' (X_{r}', y_{0})$, and $c_{1}'' = B'' (X_{r}', y_{1})$.
\end{lemma}

\begin{proof}
    \uses{MatrixSum3.IsCanonicalSigning.Al_D_isTotallyUnimodular,MatrixLikeSum3}
    \leanok
    Recall that $c_{0}'' - c_{1}'' \in \{0, \pm 1\}^{X_{r}'}$ by Lemma~\ref{MatrixSum3.IsCanonicalSigning.Al_D_isTotallyUnimodular}.\ref{item:tss_Bp_c2}, so $\mathcal{C} (X_{\ell}', Y_{\ell}', X_{r}', Y_{r}'; c_{0}'', c_{1}'')$ is well-defined. To see that $B'' \in \mathcal{C} (X_{\ell}', Y_{\ell}', X_{r}', Y_{r}'; c_{0}'', c_{1}'')$, note that all properties from Definition~\ref{MatrixLikeSum3} are satisfied: property~\ref{item:mls3_Parallels} holds by Lemma~\ref{MatrixSum3.IsCanonicalSigning.Al_D_isTotallyUnimodular}.\ref{item:tss_Bp_Dcols}, property~\ref{item:mls3_BottomTU} holds by Lemma~\ref{MatrixSum3.HasTuBr.cccAr_isTotallyUnimodular}.\ref{item:tss_Brp_tu3}, and property~\ref{item:mls3_LeftTU} holds by Lemma~\ref{MatrixSum3.IsCanonicalSigning.Al_D_isTotallyUnimodular}.\ref{item:tss_Bp_AlD}.
\end{proof}
```

### child `MatrixLikeSum3.isTotallyUnimodular`: [`blueprint/src/sum_3.tex` lines 569-589](https://github.com/Ivan-Sergeyev/seymour/blob/2769b10cb73fda17bafc0f13890dc057a2f4ff2a/blueprint/src/sum_3.tex#L569-L589) ([local copy](code/blueprint/src/sum_3.tex))

```latex
\begin{lemma}
    \label{MatrixLikeSum3.isTotallyUnimodular}
    \uses{MatrixLikeSum3,Matrix.IsTotallyUnimodular}
    % \lean{}
    \leanok
    Let $C \in \mathcal{C} (X_{\ell}', Y_{\ell}', X_{r}', Y_{r}'; c_{0}, c_{1})$ from Definition~\ref{MatrixLikeSum3}. Then $C$ is TU.
\end{lemma}

\begin{proof}
    \uses{MatrixLikeSum3,Matrix.isTotallyUnimodular_iff_forall_isPartiallyUnimodular,shortTableauPivot_submatrix_det_abs_eq_div,MatrixLikeSum3.shortTableauPivot}
    \leanok
    By Lemma~\ref{Matrix.isTotallyUnimodular_iff_forall_isPartiallyUnimodular}, it suffices to show that $C$ is $k$-PU for every $k \in \mathbb{N}$. We prove this claim by induction on $k$. The base case with $k = 1$ holds, since properties~\ref{item:mls3_BottomTU} and~\ref{item:mls3_LeftTU} in Definition~\ref{MatrixLikeSum3} imply that $A_{\ell}$, $A_{r}$, and $D$ are TU, so all their entries of $C = \begin{bmatrix} A_{\ell} & 0 \\ D & A_{r} \end{bmatrix}$ are in $\{0, \pm 1\}$, as desired.

    Suppose that for some $k \in \mathbb{N}$ we know that every $C' \in \mathcal{C} (X_{\ell}', Y_{\ell}', X_{r}', Y_{r}'; c_{0}, c_{1})$ is $k$-PU. Our goal is to show that $C$ is $(k + 1)$-PU, i.e., that every $(k + 1) \times (k + 1)$ submatrix $S$ of $C$ has $\det V \in \{0, \pm 1\}$.

    First, suppose that $V$ has no rows in $X_{\ell}'$. Then $V$ is a submatrix of $\begin{bmatrix} D & A_{r} \end{bmatrix}$, which is TU by property~\ref{item:mls3_BottomTU} in Definition~\ref{MatrixLikeSum3}, so $\det V \in \{0, \pm 1\}$. Thus, we may assume that $S$ contains a row $x_{\ell} \in X_{\ell}'$.

    Next, note that without loss of generality we may assume that there exists $y_{\ell} \in Y_{\ell}'$ such that $V (x_{\ell}, y_{\ell}) \neq 0$. Indeed, if $V (x_{\ell}, y) = 0$ for all $y$, then $\det V = 0$ and we are done, and $V (x_{\ell}, y) = 0$ holds whenever $y \in Y_{r}'$.

    Since $C$ is $1$-PU, all entries of $V$ are in $\{0, \pm 1\}$, and hence $V (x_{\ell}, y_{\ell}) \in \{\pm 1\}$. Thus, by Lemma~\ref{shortTableauPivot_submatrix_det_abs_eq_div}, performing a short tableau pivot in $V$ on $(x_{\ell}, y_{\ell})$ yields a matrix that contains a $k \times k$ submatrix $S''$ such that $|\det V| = |\det V''|$. Since $V$ is a submatrix of $C$, matrix $V''$ is a submatrix of the matrix $C'$ resulting from performing a short tableau pivot in $C$ on the same entry $(x_{\ell}, y_{\ell})$. By Lemma~\ref{MatrixLikeSum3.shortTableauPivot}, we have $C' \in \mathcal{C} (X_{\ell}', Y_{\ell}', X_{r}', Y_{r}'; c_{0}, c_{1})$. Thus, by the inductive hypothesis applied to $V''$ and $C'$, we have $\det V'' \in \{0, \pm 1\}$. Since $|\det V| = |\det V''|$, we conclude that $\det V \in \{0, \pm 1\}$.
\end{proof}
```

How the parts fit. The parent is a pure composition: its proof (the glue,
lines 599-604) is the single sentence "Combine the results of
`MatrixSum3.IsCanonicalSigning.toMatrixLikeSum3` and
`MatrixLikeSum3.isTotallyUnimodular`", i.e. modus ponens across the two children.
Child 1 gives the antecedent (`B'' ∈ C(...)`) and child 2 the conditional
(every `C ∈ C(...)` is TU); together they yield `B''` is TU. Each child closes on
its own, so the parent introduces no new reasoning.

Lemma graph (arrows are `\uses{}`/`\ref{}` citations, read from the copied file):

```text
MatrixSum3.IsCanonicalSigning.isTotallyUnimodular   (node, lines 591-604)
 ├─ MatrixSum3.IsCanonicalSigning.toMatrixLikeSum3   (membership, 528-540)
 │    └─ MatrixSum3.IsCanonicalSigning.Al_D_isTotallyUnimodular   (451-506)
 │         └─ MatrixSum3.HasTuBr.cccAr_isTotallyUnimodular        (358-428)
 │              └─ Matrix.HasTuCanonicalSigning.toCanonicalSigning (291-303)
 │                   └─ Matrix.HasTuCanonicalSigning.toCanonicalSigning_submatrix3x3 (200-265)
 └─ MatrixLikeSum3.isTotallyUnimodular               (family TU, 569-589)
      └─ MatrixLikeSum3.shortTableauPivot            (542-567)
           └─ Matrix.shortTableauPivot_zero, Matrix.IsTotallyUnimodular.shortTableauPivot
```

Why each child is a good leaf:

- **`toMatrixLikeSum3`** is a self-contained membership statement: `B''` lies in
  the family `C(X_ℓ', Y_ℓ', X_r', Y_r'; c₀'', c₁'')` with the stated parameters.
  Its proof (lines 536-540) closes by verifying the family's properties against
  the earlier lemma `Al_D_isTotallyUnimodular` (items `tss_Bp_c2`, `tss_Bp_Dcols`,
  `tss_Bp_AlD`) and `HasTuBr.cccAr_isTotallyUnimodular` (item `tss_Brp_tu3`). It
  does not need the TU result itself, only the block structure.

- **`MatrixLikeSum3.isTotallyUnimodular`** is a self-contained universal
  statement: every member of the family is TU. Its proof (lines 577-589) is an
  induction on `k` that pivots a `k×k` submatrix to a `(k−1)×(k−1)` one and
  applies the induction hypothesis, using only `MatrixLikeSum3.shortTableauPivot`
  and the partially-unimodular characterisation. It never mentions `B''`
  specifically — it only needs the family's axioms, so it is reusable for any
  member.

## Why it is good

1. The parent site cites its two children by name, and only them: line 600 lists
   `toMatrixLikeSum3` and `MatrixLikeSum3.isTotallyUnimodular` (check claim 1-2,
   form `cites(parent, …)`).
2. The node combines exactly 2 direct lemmas in a 14-line site, and the longest
   lemma chain below it (through `toMatrixLikeSum3` → `Al_D_isTotallyUnimodular`
   → `HasTuBr.cccAr_isTotallyUnimodular` → `HasTuCanonicalSigning.toCanonicalSigning`
   → `toCanonicalSigning_submatrix3x3`) has depth 5 (measurement claim 3).
3. The authors write the whole proof as one sentence — "Combine the results of
   Lemmas … and …" (line 602) — stating explicitly that the node is nothing more
   than the combination of its two parents (author-statement claim 4).

In my opinion the detail worth copying is the *type of the node*: it is a
`P(x)` fact obtained by pairing a membership lemma `x ∈ F` with a family lemma
`∀y ∈ F, P(y)`. The membership side is structural and reusable, and the family
side never names `x`, so neither parent depends on the other — the node is a
truly shallow join of two already-proved facts.

## When to use it, and when not

Use it when a published dependency graph (or a proof plan) already factors a
target `P(x)` into (a) a membership fact `x ∈ F` for a defined family `F`, and
(b) a universal fact `∀y ∈ F, P(y)`, so that the node only needs to state `P(x)`
as a nameable fact other nodes can cite. This is the natural shape for
"canonical object belongs to a family whose members share the property".

Avoid it when either parent is still open (the node then does not close), when
membership genuinely fails, or when the property is not closed under the family
(the family lemma would be false). It is also not the move to use when the real
work is *inside* one parent — here both parents are substantial lemmas with their
own proofs, and the node contributes no reasoning of its own.

## Consequences

The node creates no new obligation: it is a pure composition of two already-proved
parents, so its only consequence is a named TU fact. That fact is consumed
immediately by the final theorem `Matroid.IsSum3of.isRegular` (lines 606-618),
which cites it together with `MatrixSum3.HasCanonicalSigning.toCanonicalSigning`
to conclude a 3-sum of regular matroids is regular. Failure modes: if either
parent is weakened or re-stated, the one-sentence proof breaks; and the node
inherits its parents' hypotheses, so it holds only for the canonical signing
`B''` from `MatrixSum3.toCanonicalSigning` (which assumes the `D₀` block is one
of the two canonical 2×2 forms of `Matrix.isUnit_2x2`).

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/blueprint.yml 'Compile blueprint' job uses docgen-action with blueprint:true, which builds the blueprint including blueprint/src/sum_3.tex; workflow triggers on push to main (paths include blueprint/**); pinned commit 2769b10cb73fda17bafc0f13890dc057a2f4ff2a on default branch main | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 2769b10cb73fda17bafc0f13890dc057a2f4ff2a | check_provenance.py | 2026-11-14 |
| sorry-scan | not-run | no Lean, Rocq or Isabelle file among the copied files | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, MatrixSum3.IsCanonicalSigning.toMatrixLikeSum3) -> cites: MatrixSum3.IsCanonicalSigning.toMatrixLikeSum3 occurs at blueprint/src/sum_3.tex:600 | check_claims.py |
| 2 | verified | cites(parent, MatrixLikeSum3.isTotallyUnimodular) -> cites: MatrixLikeSum3.isTotallyUnimodular occurs at blueprint/src/sum_3.tex:592 | check_claims.py |
| 3 | verified | parent site 591-604 is 14 lines (glue_lines=14); line 600 \uses{toMatrixLikeSum3,isTotallyUnimodular} lists exactly 2 children (direct_lemmas=2). Depth-5 chain confirmed along \uses{} lines: 537 toMatrixLikeSum3->Al_D_isTotallyUnimodular, 468 Al_D->cccAr_isTotallyUnimodular, 374 cccAr->HasTuCanonicalSigning.toCanonicalSigning, 300 toCanonicalSigning->toCanonicalSigning_submatrix3x3, 223 submatrix3x3 uses only Matrix-namespace facts. Child sites 528-540 (13) and 569-589 (21) match child_lines [13,21]. | verifier |
| 4 | verified | sum_3.tex:602 reads exactly 'Combine the results of Lemmas~\ref{MatrixSum3.IsCanonicalSigning.toMatrixLikeSum3} and~\ref{MatrixLikeSum3.isTotallyUnimodular}.' inside the parent's proof block (599-604). | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent proof (sum_3.tex:600) uses exactly the two children MatrixSum3.IsCanonicalSigning.toMatrixLikeSum3 and MatrixLikeSum3.isTotallyUnimodular; child statements at :533 and :574 match entry.json; both children close via their own proofs (:536-540 cites Al_D_isTotallyUnimodular+cccAr; :577-589 induction via shortTableauPivot); node closes as modus ponens. Shape numbers verified against code: direct_lemmas=2, glue_lines=14 (591-604), child_lines [13 (528-540), 21 (569-589)], depth=5 chain 537->468->374->300->223 all confirmed (223 uses only Matrix-namespace facts). | reviewer-correctness |
| generality | accept | Move is stated generally as P(x) = membership(x in F) x family-universal(forall y in F, P(y)); avoid_when and consequences name concrete, honest failure modes (open parent, failed membership, non-closed property, node adds no reasoning); 'Why each child is a good leaf' gives the bounded-prover-relevant properties (self-contained proof over the family's own axioms, never names B'' so reusable, parents mutually independent). | reviewer-generality |
| provenance-licence | accept | check_provenance passes (1 file byte-identical at pinned commit 2769b10cb73fda17bafc0f13890dc057a2f4ff2a). Commit is consistent across entry.json, README (short 2769b10cb73f), sources/seymour/SOURCE.md and source.json. Licence Apache-2.0 is consistent in entry.json, README and SOURCE.md, and upstream-LICENSE is the Apache License 2.0 text. Permalinks use the full commit hash and line ranges 591-604/528-540/569-589, which match the copied code/blueprint/src/sum_3.tex and the shape numbers (14/13/21). All traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/Ivan-Sergeyev/seymour at commit `2769b10cb73fda17bafc0f13890dc057a2f4ff2a`, under `Apache-2.0`; see the [source note](../../sources/seymour/SOURCE.md) for the licence text and attribution.
