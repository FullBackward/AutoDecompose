# Blueprint node: paths of Brownian motion are locally Holder of all orders below 1/2

| | |
|---|---|
| Kind | instance |
| Move | blueprint-node |
| Language | latex |
| Status | accepted |
| Source | [brownian-motion](../../sources/brownian-motion/SOURCE.md) at `8fd8dc52830c` |
| Licence | `Apache-2.0` |

## Intent

A statement about the Brownian motion (that its paths are locally Hölder
continuous of every order below 1/2) is derived from three named project nodes
by a proof that does nothing but instantiate them: it picks a cover of the
index space with bounded covering numbers (exponent $d = 1$), quotes the
pre-Brownian process's Kolmogorov condition, feeds both into the localized
Kolmogorov-Chentsov modification theorem, and finishes with the arithmetic
$\sup_n (n+1)/(2n+4) = 1/2$.

## The decomposition

### parent `lem:isHolderWith_brownian`: [`blueprint/src/chapters/brownian.tex` lines 101-113](https://github.com/RemyDegenne/brownian-motion/blob/8fd8dc52830cdd07cf9cc8eadd533e284425fa6f/blueprint/src/chapters/brownian.tex#L101-L113) ([local copy](code/blueprint/src/chapters/brownian.tex))

```latex
\begin{lemma}\label{lem:isHolderWith_brownian}
  \uses{def:brownian}
  \leanok
  \lean{ProbabilityTheory.memHolder_brownian}
The paths of the Brownian motion are locally Hölder continuous of all orders $\gamma \in (0, 1/2)$.
\end{lemma}

\begin{proof}\leanok
  \uses{lem:hasBoundedCoveringNumberCover_nnreal, lem:isKolmogorovProcess_preBrownian, thm:localized_holder_modification_sup}
Consider the cover of $\mathbb{R}_+$ given by $T_n := [0, n + 1)$. By Lemma~\ref{lem:hasBoundedCoveringNumberCover_nnreal}, this cover has bounded covering numbers with exponent $1$. Moreover, by Lemma~\ref{lem:isKolmogorovProcess_preBrownian}, the pre-Brownian process satisfies the Kolmogorov condition with exponents $(2n + 4, n + 2)$ for all $n \in \mathbb{N}$.
In particular, for all $n \in \mathbb{N}$, $2n + 4 > 1$. Applying Theorem~\ref{thm:localized_holder_modification_sup} we deduce that the modification used in Definition~\ref{def:brownian} has locally Hölder continuous paths for all orders $\gamma \in (0, \sup_n (n + 1) / (2n + 4))$.
Clearly for all $n \in \mathbb{N}$ we have $(n + 1) / (2n + 4) \leqslant 2$, and this quantity tends to $2$ as $n$ goes to infinity. Therefore the Brownian motion has Hölder continuous paths of order $\gamma$ for all $\gamma \in (0, 1 / 2)$.
\end{proof}
```

### child `lem:hasBoundedCoveringNumberCover_nnreal`: [`blueprint/src/chapters/kolmogorov_chentsov.tex` lines 1786-1798](https://github.com/RemyDegenne/brownian-motion/blob/8fd8dc52830cdd07cf9cc8eadd533e284425fa6f/blueprint/src/chapters/kolmogorov_chentsov.tex#L1786-L1798) ([local copy](code/blueprint/src/chapters/kolmogorov_chentsov.tex))

```latex
\begin{lemma}\label{lem:hasBoundedCoveringNumberCover_nnreal}
  \uses{def:HasBoundedCoveringNumberCover}
  \leanok
  \lean{isCoverWithBoundedCoveringNumber_Ico_nnreal}
$\mathbb{R}_+$ has a cover with bounded covering numbers for the sets $T_n = [0,n)$, constants $c_n = n$ and exponents $d_n = 1$.
\end{lemma}

Note: in the Lean code, we proved this result for weaker constants: $c_n = 3n$.

\begin{proof}\leanok
  \uses{lem:hasBoundedInternalCoveringNumber_unitInterval}

\end{proof}
```

### child `lem:isKolmogorovProcess_preBrownian`: [`blueprint/src/chapters/brownian.tex` lines 53-74](https://github.com/RemyDegenne/brownian-motion/blob/8fd8dc52830cdd07cf9cc8eadd533e284425fa6f/blueprint/src/chapters/brownian.tex#L53-L74) ([local copy](code/blueprint/src/chapters/brownian.tex))

```latex
\begin{lemma}\label{lem:isKolmogorovProcess_preBrownian}
  \uses{def:preBrownian}
  \leanok
  \lean{ProbabilityTheory.isKolmogorovProcess_preBrownian}
The pre-Brownian process $X$ of Definition~\ref{def:preBrownian} satisfies the Kolmogorov condition for exponents $(2n,n)$ with constant $(2n - 1)!!$ for all $n \in \mathbb{N}$.
That is, for all $s, t \in \mathbb{R}_+$, we have
\begin{align*}
  \mathbb{E} \left[ |X_t - X_s|^{2n} \right] \le (2n - 1)!! |t - s|^n
  \: .
\end{align*}
\end{lemma}

\begin{proof}\leanok
  \uses{lem:centralMoment_two_mul_gaussianReal, lem:hasLaw_preBrownian_sub}
$X_t - X_s$ is a Gaussian random variable with mean $0$ and variance $|t - s|$ (Lemma~\ref{lem:hasLaw_preBrownian_sub}).
Thus, by Lemma~\ref{lem:centralMoment_two_mul_gaussianReal}, we have
\begin{align*}
  \mathbb{E} \left[ |X_t - X_s|^{2n} \right]
  = (2n - 1)!! |t - s|^n
  \: .
\end{align*}
\end{proof}
```

### child `thm:localized_holder_modification_sup`: [`blueprint/src/chapters/kolmogorov_chentsov.tex` lines 1830-1849](https://github.com/RemyDegenne/brownian-motion/blob/8fd8dc52830cdd07cf9cc8eadd533e284425fa6f/blueprint/src/chapters/kolmogorov_chentsov.tex#L1830-L1849) ([local copy](code/blueprint/src/chapters/kolmogorov_chentsov.tex))

```latex
\begin{theorem}\label{thm:localized_holder_modification_sup}
  \uses{def:IsKolmogorovProcess, def:HasBoundedCoveringNumberCover}
  \leanok
  \lean{ProbabilityTheory.exists_modification_holder_iSup}
Let $T$ be a metric space with a cover $(T_n)$ with bounded covering numbers with constants $c_n$ and the same exponent $d$.
Let $(p_n, q_n)_{n \in \mathbb{N}}$ be a sequence of pairs of positive numbers such that $q_n > d$ for all $n \in \mathbb{N}$.
Let $X : T \to \Omega \to E$ be a process that satisfies the Kolmogorov condition with exponents $(p_n, q_n)$ for all $n \in \mathbb{N}$.
Then $X$ has a modification $Y$ such that almost surely the paths of $Y$ are locally Hölder continuous of all orders $\gamma \in (0, \sup_n (q_n - d)/p_n)$.
\end{theorem}

\begin{proof}\leanok
  \uses{thm:localized_holder_modification}
For each $n$, by Theorem~\ref{thm:localized_holder_modification} there is a modification $Y_n$ of $X$ such that the paths of $Y_n$ are locally Hölder continuous of all orders $\gamma \in (0, (q_n - d)/p_n)$.
By Lemma~\ref{lem:indistinguishable_of_modification_of_continuous}, any two processes $Y_n, Y_m$ are indistinguishable.
That is, almost surely $Y_n = Y_m$.
Since there are countably many such almost sure equalities, we get that almost surely there is equality for all $n, m$.
Let then $Y$ be the process equal to $Y_0$ on the event that the equalities hold, and equal to an arbitrary point $x_0 \in E$ otherwise.
Then first, $Y$ is a modification of $X$.
Then for any $\gamma < \sup_n (q_n - d)/p_n$ there is $n$ such that $\gamma < (q_n - d)/p_n$ and thus since $Y = Y_n$ the paths of $Y$ are locally Hölder continuous of order $\gamma$ almost surely.
\end{proof}
```

How the parts fit. The parent `lem:isHolderWith_brownian` is a blueprint node:
a labelled statement carrying a `\uses{}` dependency edge and a `\lean{}`
marker (`ProbabilityTheory.memHolder_brownian`) plus `\leanok`, so the graph
records it as stated-and-formalised. Its proof is the glue, and it cites
exactly three named nodes:

```
lem:hasBoundedCoveringNumberCover_nnreal ─┐
lem:isKolmogorovProcess_preBrownian ──────┼──▶ lem:isHolderWith_brownian
thm:localized_holder_modification_sup ────┘
```

The glue has three obligations, and one child closes each:

1. *A cover of the index space with bounded covering numbers.* The proof takes
   the cover $T_n := [0, n+1)$ of $\mathbb{R}_+$ and cites
   `lem:hasBoundedCoveringNumberCover_nnreal` (exponent $d = 1$).
2. *The process satisfies the Kolmogorov condition.* The proof cites
   `lem:isKolmogorovProcess_preBrownian`, reading it at exponents
   $(2n+4, n+2)$ (a reindexing of the lemma's $(2n, n)$).
3. *A localized modification exists.* The proof cites
   `thm:localized_holder_modification_sup` with $p_n = 2n+4$, $q_n = n+2$,
   $d = 1$, obtaining locally Hölder paths of every order
   $\gamma < \sup_n (n+1)/(2n+4)$.

The glue then closes by the arithmetic $\sup_n (n+1)/(2n+4) = 1/2$. Note the
source's sentence at line 112 writes "$\leqslant 2$" and "tends to $2$" where
the correct bound is $1/2$: a transcription slip in the blueprint, and the
correct value $1/2$ is what makes the node's statement (orders in $(0,1/2)$)
true.

Why each child is a good leaf (a self-contained statement whose proof closes
on its own or from named siblings):

- `lem:hasBoundedCoveringNumberCover_nnreal` is a concrete, self-contained
  fact (the cover $[0,n)$, constants $c_n=n$, exponent $d_n=1$). Its proof body
  is empty — it closes by a single `\uses{}` to
  `lem:hasBoundedInternalCoveringNumber_unitInterval`, the unit interval's
  covering-number bound.
- `lem:isKolmogorovProcess_preBrownian` is self-contained (the Kolmogorov
  condition for the pre-Brownian process) and closes from two named siblings,
  `lem:centralMoment_two_mul_gaussianReal` and `lem:hasLaw_preBrownian_sub`.
- `thm:localized_holder_modification_sup` is the generic localisation of
  Kolmogorov-Chentsov with a sup over exponents; it closes from one named
  sibling `thm:localized_holder_modification` (the single-exponent version)
  plus `lem:indistinguishable_of_modification_of_continuous`.

## Why it is good

1. The parent site cites `lem:hasBoundedCoveringNumberCover_nnreal`
   (`check`, machine-decided: `cites(parent, lem:hasBoundedCoveringNumberCover_nnreal)`,
   brownian.tex:101-113).
2. The parent site cites `lem:isKolmogorovProcess_preBrownian`
   (`check`, `cites(parent, lem:isKolmogorovProcess_preBrownian)`).
3. The parent site cites `thm:localized_holder_modification_sup`
   (`check`, `cites(parent, thm:localized_holder_modification_sup)`).
4. The parent site is 13 lines long, declaration and proof together
   (`check`, `lines(parent, 13)`).
5. The glue combines exactly 3 direct lemmas, the longest checked dependency
   chain below the node has depth 7, and the three child sites span 13, 22 and
   20 lines (`measurement`, counted along the `\uses{}` lines at brownian.tex:109
   and kolmogorov_chentsov.tex:1841, :1812, :1764, :1716, :1688, :1639).

In my opinion the detail worth copying is that the parent node is *pure
instantiation*: it proves no new argument, only the choice of parameters
($d=1$, $p_n=2n+4$, $q_n=n+2$) and the sup computation, so the mathematical
content lives entirely in the three children and the arithmetic — which is
exactly the shape a bounded prover should fill as three lemma holes.

## When to use it, and when not

Use it when a headline property of a constructed object follows from a known
universal theorem by instantiating parameters (a cover of the index space, an
exponent sequence), and the project's blueprint already has those ingredients
as named nodes. The node then exists only to record the instantiation and the
final arithmetic. Avoid it when any ingredient is still an open node (then the
node does not close), when the sup or limit computation is the real content
rather than a routine reindexing, or when the process's Kolmogorov exponents
cannot be pushed up by a uniform reindexing of a single lemma.

## Consequences

The node creates no new mathematical obligation: it is a pure instantiation of
three already-proved nodes plus a sup computation, so its only consequence is a
named fact (`lem:isHolderWith_brownian`) that `lem:continuous_brownian` cites
(brownian.tex:124) and that definition `def:brownian` already foreshadowed
(brownian.tex:78). Failure modes: the arithmetic step is mis-stated in the
blueprint — line 112 writes "$\leqslant 2$" and "tends to $2$" where the
correct bound is $1/2$ ($\sup_n (n+1)/(2n+4) = 1/2$) — so a reader copying the
node verbatim must recompute the sup rather than trust that sentence. The
instantiation also silently reindexes both ingredients: the cover
$T_n = [0, n+1)$ against the lemma's $T_n = [0, n)$, and the Kolmogorov
exponents $(2n+4, n+2)$ against the lemma's $(2n, n)$.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/blueprint.yml 'Compile blueprint and documentation' step runs docgen-action with blueprint:true, compiling the blueprint LaTeX (incl. blueprint/src/chapters/brownian.tex) on pushes to the default branch master; commit 8fd8dc52830cdd07cf9cc8eadd533e284425fa6f is the source's pinned HEAD | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at 8fd8dc52830cdd07cf9cc8eadd533e284425fa6f | check_provenance.py | 2026-11-14 |
| sorry-scan | not-run | no Lean, Rocq or Isabelle file among the copied files | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, lem:hasBoundedCoveringNumberCover_nnreal) -> cites: lem:hasBoundedCoveringNumberCover_nnreal occurs at blueprint/src/chapters/brownian.tex:109 | check_claims.py |
| 2 | verified | cites(parent, lem:isKolmogorovProcess_preBrownian) -> cites: lem:isKolmogorovProcess_preBrownian occurs at blueprint/src/chapters/brownian.tex:109 | check_claims.py |
| 3 | verified | cites(parent, thm:localized_holder_modification_sup) -> cites: thm:localized_holder_modification_sup occurs at blueprint/src/chapters/brownian.tex:109 | check_claims.py |
| 4 | verified | lines(parent, 13) -> lines: site parent has 13 lines | check_claims.py |
| 5 | verified | direct_lemmas=3 confirmed from proof \uses{} at brownian.tex:109 listing lem:hasBoundedCoveringNumberCover_nnreal, lem:isKolmogorovProcess_preBrownian, thm:localized_holder_modification_sup; depth-7 chain confirmed edge by edge: 1841 uses thm:localized_holder_modification -> 1812 uses thm:holder_modification -> 1764 uses lem:holder_modification_single -> 1716 uses thm:countable_set_bound -> 1688 uses lem:finite_set_bound -> 1639 uses cor:finite_set_bound_of_dist_le (7 nodes); child_lines [13,22,20] confirmed: 1786-1798=13, 53-74=22, 1830-1849=20 | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Correctness verified against the copied code. Parent lem:isHolderWith_brownian (brownian.tex:101-113) has a proof whose \uses{} (line 109) cites exactly the three children: lem:hasBoundedCoveringNumberCover_nnreal, lem:isKolmogorovProcess_preBrownian, thm:localized_holder_modification_sup — no more, no fewer. Each child's closing method matches: child1 (kolmogorov_chentsov.tex:1786-1798) empty body with \uses{lem:hasBoundedInternalCoveringNumber_unitInterval}; child2 (brownian.tex:53-74) cites centralMoment_two_mul_gaussianReal and hasLaw_preBrownian_sub; child3 (kolmogorov_chentsov.tex:1830-1849) cites thm:localized_holder_modification and lem:indistinguishable_of_modification_of_continuous. The node closes: the proof ends with the arithmetic sup_n (n+1)/(2n+4)=1/2, and the entry correctly flags the blueprint's transcription slip at line 112 (writes '<=2 / tends to 2' where 1/2 is correct). Shape numbers are right: glue_lines=13 (101-113), child_lines=[13,22,20] (1786-1798, 53-74, 1830-1849), direct_lemmas=3, depth=7 confirmed along the uses chain 1841->1812->1764->1716->1688->1639->finite_set_bound_of_dist_le. | reviewer-correctness |
| generality | accept | Move generalises: applicability.goal_shape and README 'When to use' state the general shape (a canonically-constructed object whose property follows from a universal theorem by instantiating parameters, plus a one-line sup/limit computation), not just Brownian motion. When-not-to-use is honest and specific (ingredient still an open node; the sup/limit is the real content; exponents not uniformly reindexable), and consequences flag real failure modes I confirmed in the copied code: the line-112 transcription slip writes '<= 2'/'tends to 2' where the correct sup is 1/2, and the silent reindexing of both the cover [0,n+1) vs [0,n) and exponents (2n+4,n+2) vs (2n,n). 'Why each child is a good leaf' names what makes them bounded-prover leaves: each is self-contained and closes on its own or from named siblings, and the opinion paragraph names the three-lemma-hole shape. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note all consistent. check_provenance.py passes: both files byte-identical at pinned commit 8fd8dc52830cdd07cf9cc8eadd533e284425fa6f, so permalinks resolve. The commit hash matches across source.json, SOURCE.md, entry.json, README and every permalink. Entry licence Apache-2.0 matches source.json/source note; upstream-LICENSE is the Apache-2.0 text. Cited line ranges (brownian.tex 101-113, 53-74; kolmogorov_chentsov.tex 1786-1798, 1830-1849) match the copied files verbatim. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/RemyDegenne/brownian-motion at commit `8fd8dc52830cdd07cf9cc8eadd533e284425fa6f`, under `Apache-2.0`; see the [source note](../../sources/brownian-motion/SOURCE.md) for the licence text and attribution.
