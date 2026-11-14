# Sliced infinity-cosmoi: one named lemma per nontrivial component of the cosmos structure

| | |
|---|---|
| Kind | instance |
| Move | per-callee-lemma |
| Language | latex |
| Status | accepted |
| Source | [infinity-cosmos](../../sources/infinity-cosmos/SOURCE.md) at `89d7dc3ed861` |
| Licence | `Apache-2.0` |

## Intent

State that the isofibrations over a fixed base `B` form an ∞-cosmos `𝒦_{/B}`
by listing its seven defining items, then prove it by a survey that verifies
each item in turn and hands the three nontrivial verifications — the
pullback-stability of equivalences, and its converse — to three named lemmas
stated earlier in the same blueprint.

## The decomposition

### parent `prop:sliced-cosmoi`: [`blueprint/src/content.tex` lines 845-901](https://github.com/emilyriehl/infinity-cosmos/blob/89d7dc3ed861824535e540da489a46469dcc8e56/blueprint/src/content.tex#L845-L901) ([local copy](code/blueprint/src/content.tex))

```latex
\begin{proposition}[sliced $\infty$-cosmoi]\label{prop:sliced-cosmoi} \uses{defn:cosmos}
  For any $\infty$-cosmos $\cK$ and any $\infty$-cat\-e\-gory $B \in \cK$ there is an \textbf{$\infty$-cosmos $\cK_{/B}$ of isofibrations over $B$} whose
\begin{enumerate}
\item\label{itm:sliced-objects} objects are isofibrations $p \colon E \fib B$ with codomain $B$
\item\label{itm:sliced-functor-space} functor spaces, say from $p \colon E \fib B$ to $q \colon F \fib B$, are defined by pullback
\begin{center}
\begin{tikzcd}[column sep=small] \Fun_B(p \colon E \fib B,q\colon F\fib B) \arrow[r] \arrow[d, two heads] \arrow[dr, phantom, "\lrcorner" very near start] & \Fun(E,F) \arrow[d, two heads, "{q_*}"] \\ \catone \arrow[r, "p"] & \Fun(E,B)
\end{tikzcd}
\end{center}
and abbreviated to $\Fun_B(E,F)$ when the specified isofibrations are clear from context
\item\label{itm:sliced-isofibrations} isofibrations are commutative triangles of isofibrations over $B$
\begin{center}
\begin{tikzcd}[row sep=small, column sep=small]
E \arrow[rr,two heads, "r"] \arrow[dr, two heads, "p"'] & & F \arrow[dl, two heads, "q"] \\ & B
\end{tikzcd}
\end{center}
\item\label{itm:sliced-products} terminal object is $\id \colon B \fib B$ and products are defined by the pullback along the diagonal
\begin{center}
\begin{tikzcd} \times^B_i E_i \arrow[r] \arrow[d, two heads] \arrow[dr, phantom, "\lrcorner" very near start] & \prod_i E_i \arrow[d, two heads, "\prod_i p_i"] \\ B \arrow[r, "\Delta"] & \prod_i B
\end{tikzcd}
\end{center}
\item\label{itm:sliced-pullbacks} pullbacks and limits of towers of isofibrations are created by the forgetful functor $\cK_{/B} \to \cK$
\item\label{itm:sliced-cotensors} simplicial cotensor of $p \colon E \fib B$ with $U \in \sSet$ is constructed by the pullback
\begin{center}
\begin{tikzcd} U \pwr_B p \arrow[d, two heads] \arrow[r] \arrow[dr, phantom, "\lrcorner" very near start] & E^U \arrow[d, two heads, "p^U"] \\ B \arrow[r, "\Delta"] & B^U
\end{tikzcd}
\end{center}
\item\label{itm:fibered-equivalence} and in which a map over $B$
\begin{center}
\begin{tikzcd}[row sep=small, column sep=small]
E \arrow[rr, "f"] \arrow[dr, two heads, "p"'] & & F \arrow[dl, two heads, "q"] \\ & B
\end{tikzcd}
\end{center}
is an equivalence in the $\infty$-cosmos $\cK_{/B}$ if and only if $f$ is an equivalence in $\cK$.
\end{enumerate}
\end{proposition}
\begin{proof}
  \uses{lem:trivial-fib-conical, lem:brown-fact}
The functor spaces are quasi-categories since axiom \ref{defn:cosmos}\ref{itm:cosmos-isofib} asserts that for any isofibration $q \colon F \fib B$ in $\cK$ the map $q_* \colon \Fun(E,F) \fib \Fun(E,B)$ is an isofibration of quasi-categories. Other parts of this axiom imply that each of the limit constructions --- such as the products and cotensors constructed in \ref{itm:sliced-products} and \ref{itm:sliced-cotensors} --- define isofibrations over $B$. The closure properties of the isofibrations in $\cK_{/B}$ follow from the corresponding ones in $\cK$. The most complicated of these is the Leibniz cotensor stability of the isofibrations in $\cK_{/B}$, which follows from the corresponding property in $\cK$, since for a monomorphism of simplicial sets $i \colon X\inc Y$ and an isofibration $r$ over $B$ as in \ref{itm:sliced-isofibrations} above, the map $i \leib{\pwr_B} r$ is constructed by pulling back $\widehat{\{i , r\}}$ along $\Delta \colon B \to B^Y$.

The fact that the above constructions define simplicially enriched limits in a simplicially enriched slice category are standard from enriched category theory. It remains only to verify that the equivalences in the $\infty$-cosmos of isofibrations are created by the forgetful functor $\cK_{/B} \to \cK$. Suppose first that the map $f$ displayed in \ref{itm:fibered-equivalence} defines an equivalence in $\cK$. Then for any isofibration $s \colon A \fib B$ the induced map on functor spaces in $\cK_{/B}$ is defined by the pullback:
\begin{center}
\begin{tikzcd}
\Fun_B(A,E) \arrow[dr, "{f_*}", dashed, "\sim"'] \arrow[dd, two heads] \arrow[ddr, phantom, "\lrcorner" pos=.001] \arrow[rr] & & \Fun(A,E) \arrow[dd, two heads, "{p_*}"' near start] \arrow[dr, "{f_*}", "\sim"'] \\ & \Fun_B(A,F) \arrow[dl, two heads] \arrow[dr, phantom, "\lrcorner" very near start] \arrow[rr, crossing over] & & \Fun(A,F) \arrow[dl, two heads, "{q_*}"] \\ \catone \arrow[rr, "s"'] & ~& \Fun(A,B)
\end{tikzcd}
\end{center}
Since $f$ is an equivalence in $\cK$, the map $f_* \colon \Fun(A,E) \to \Fun(A,F)$ is an equivalence, and so it follows that the induced map on fibers over $s$ is an equivalence as well.\footnote{The stability of equivalences between isofibrations under pullback can be proven either as a consequence of Lemmas \ref{lem:trivial-fib-conical} and \ref{lem:brown-fact} using standard techniques from simplicial homotopy theory %(see Lemma \ref{lem:pullback-of-fibered-equiv})
 or by arguing 2-categorically.} %(see Proposition \ref{prop:dual-gluing-lemma}).}

For the converse implication, we appeal to  Lemma \ref{lem:equiv-htpy-equiv}. If $f \colon E \to F$ is an equivalence in $\cK_{/B}$ then it admits a homotopy inverse in $\cK_{/B}$. The inverse equivalence $g \colon F \to E$ also defines an inverse equivalence in $\cK$ and the required simplicial homotopies in $\cK$
\begin{center}
\begin{tikzcd}
E \arrow[r, "\alpha"] & \iso\pwr_Bp \arrow[r] & E^\iso & F \arrow[r, "\beta"] & \iso \pwr_Bq \to F^\iso
\end{tikzcd}
\end{center}
are defined by composing with the top horizontal leg of the pullback defining the cotensor in $\cK_{/B}$.
\end{proof}
```

### child `lem:trivial-fib-conical`: [`blueprint/src/content.tex` lines 421-427](https://github.com/emilyriehl/infinity-cosmos/blob/89d7dc3ed861824535e540da489a46469dcc8e56/blueprint/src/content.tex#L421-L427) ([local copy](code/blueprint/src/content.tex))

```latex
\begin{lemma}[trivial fibrations and conical limits]\label{lem:trivial-fib-conical}
  \uses{defn:cosmos, defn:trivial-fibration}
  The trivial fibrations in an $\infty$-cosmos define a subcategory containing the isomorphisms and are stable under product, pullback, and forming inverse limits of towers.
\end{lemma}
\begin{proof}
  We know in each case that the maps in question are isofibrations in the $\infty$-cosmos; it remains to show only that the maps are also equivalences. The equivalences in an $\infty$-cosmos are defined to be the maps that $\Fun(X,-)$ carries to equivalences of quasi-categories, so it suffices to verify that trivial fibrations of quasi-categories satisfy the corresponding stability properties. These stability properties hold of any class defined by a right lifting property.
\end{proof}
```

### child `lem:brown-fact`: [`blueprint/src/content.tex` lines 546-567](https://github.com/emilyriehl/infinity-cosmos/blob/89d7dc3ed861824535e540da489a46469dcc8e56/blueprint/src/content.tex#L546-L567) ([local copy](code/blueprint/src/content.tex))

```latex
\begin{lemma}[Brown factorization lemma]\label{lem:brown-fact}
  \uses{defn:cosmos, defn:equivalence, defn:trivial-fibration}
  Any functor $f\colon A \to B$ in an $\infty$-cosmos may be factored as an equivalence followed by an isofibration, where this equivalence is constructed as a section of a trivial fibration.
\begin{center}
\begin{tikzcd}
  & Pf \arrow[dr, two heads, "p"] \arrow[dl, two heads, bend right, start anchor=190, end anchor=70, "q"'] & \\ A \arrow[rr, "f"'] \arrow[ur, bend right=25, start anchor=30, end anchor=230, "\sim", "s"' pos = 0.6] & & B
\end{tikzcd}
\end{center}
Moreover, $f$ is an equivalence if and only if the isofibration $p$ is a trivial fibration.
\end{lemma}


\begin{proof}
The displayed factorization is constructed by the pullback of an isofibration formed by the simplicial cotensor of the inclusion $\catone+\catone\inc\iso$ into the $\infty$-category $B$.
\begin{center}
\begin{tikzcd}
& A^\iso \arrow[dr, "f^\iso"] & \\
A \arrow[r, "\sim", "s"'] \arrow[ur, "\Delta"] \arrow[dr, "{(A,f)}"'] &  Pf \arrow[r] \arrow[d, two heads, "{(q,p)}"' pos=.4] \arrow[dr, phantom, "\lrcorner" very near start] & B^\iso \arrow[d, two heads, "{(\ev_0,\ev_1)}"] \\  & A \times B \arrow[r, "f \times B"'] & B \times B
\end{tikzcd}
\end{center}
Note the map $q$ is a pullback of the trivial fibration $\ev_0 \colon B^\iso \trvfib B$ and is hence a trivial fibration. Its section $s$, constructed by applying the universal property of the pullback to the displayed cone with summit $A$, is thus an equivalence by the 2-of-3 property. Again by 2-of-3, it follows that $f$ is an equivalence if and only if $p$ is.
\end{proof}
```

### child `lem:equiv-htpy-equiv`: [`blueprint/src/content.tex` lines 451-466](https://github.com/emilyriehl/infinity-cosmos/blob/89d7dc3ed861824535e540da489a46469dcc8e56/blueprint/src/content.tex#L451-L466) ([local copy](code/blueprint/src/content.tex))

```latex
\begin{lemma}[equivalences are homotopy equivalences]\label{lem:equiv-htpy-equiv}
  \uses{defn:cosmos, defn:coherent-isomorphism, defn:equivalence}
A map $f \colon A \to B$ between $\infty$-categories in an $\infty$-cosmos $\cK$ is an equivalence if and only if it extends to the data of a ``homotopy equivalence'' with the free-living isomorphism $\iso$ serving as the interval: that is, if there exist maps $g \colon B \to A$
\begin{center}
\begin{tikzcd} & A & &  & B \\ A \arrow[ur, equals] \arrow[dr, "gf"'] \arrow[r, "\alpha"] & A^\iso   \arrow[u, two heads, "\sim", "\ev_0"'] \arrow[d, two heads, "\sim"',  "\ev_1"] & \text{and} &  B \arrow[dr, equals] \arrow[r, "\beta"] \arrow[ur, "fg"] & B^\iso  \arrow[u, two heads, "\sim", "\ev_0"'] \arrow[d, two heads, "\sim"', "\ev_1"] \\ & A & &  & B
\end{tikzcd}
\end{center}
in the $\infty$-cosmos.
\end{lemma}
\begin{proof}
By hypothesis, if $f \colon A \to B$ defines an equivalence in the $\infty$-cosmos $\cK$ then the induced map on post-composition $f_* \colon \Fun(B,A) \we \Fun(B,B)$ is an equivalence of quasi-categories in the sense of Definition \ref{defn:qcat-equivalence}. Evaluating the inverse equivalence $\tilde{g} \colon \Fun(B,B) \we \Fun(B,A)$ and homotopy $\tilde{\beta} \colon \Fun(B,B) \to \Fun(B,B)^\iso$ at the 0-arrow $\id_B \in \Fun(B,B)$, we obtain a 0-arrow $g \colon B \to A$ together with an isomorphism $\beta \colon \iso\to\Fun(B,B)$ from the composite $fg$ to $\id_B$. By the defining universal property of the cotensor \eqref{eq:cotensor-defn}, this isomorphism internalizes to define the map $\beta \colon B \to B^\iso$ in $\cK$ displayed on the right of the displayed equation in the statement.

Now the hypothesis that $f$ is an equivalence also provides an equivalence of quasi-categories $f_* \colon \Fun(A,A) \we \Fun(A,B)$, and the map $\beta f \colon A \to B^\iso$ represents an isomorphism in $\Fun(A,B)$ from $fgf$ to $f$. Since $f_*$ is an equivalence, we conclude from Lemma \ref{lem:qcat-htpy-cat-equiv} that $\id_A$ and $gf$ are isomorphic in the quasi-category $\Fun(A,A)$: explicitly, such an isomorphism may be defined by applying the inverse equivalence $\tilde{h} \colon \Fun(A,B) \to \Fun(A,A)$ and composing with the components at $\id_A, gf \in \Fun(A,A)$ of the isomorphism $\tilde{\alpha} \colon \Fun(A,A) \to \Fun(A,A)^\iso$ from $\id_{\Fun(A,A)}$ to $\tilde{h}f_*$. Now by Proposition \ref{prop:coherent-iso} this isomorphism is represented by a map $\iso \to \Fun(A,A)$ from $\id_A$ to $gf$, which internalizes to a map $\alpha \colon A \to A^\iso$ in $\cK$ displayed on the left of the displayed equation in the statement.

The converse is easy: the simplicial cotensor construction commutes with $\Fun(X,-)$, so a homotopy equivalence induces a  homotopy equivalence of quasi-categories as in Definition \ref{defn:qcat-equivalence}.
\end{proof}
```

How the parts fit. The proposition `prop:sliced-cosmoi` states that, for any
∞-cosmos `𝒦` and any `B ∈ 𝒦`, the isofibrations over `B` form an ∞-cosmos
`𝒦_{/B}`, by defining seven items (objects, functor spaces, isofibrations,
terminal object + products, pullbacks/towers, cotensors, equivalences). The
proof — the glue, lines 881-901 — verifies each item in turn and delegates the
nontrivial ones to three named lemmas:

- The forward direction of item `itm:fibered-equivalence` (an equivalence in
  `𝒦` induces one in `𝒦_{/B}`) needs that equivalences between isofibrations
  are stable under pullback. The glue's footnote (line 891) says this follows
  from `lem:trivial-fib-conical` and `lem:brown-fact` (both declared in the
  `\uses{}` line 882). `lem:trivial-fib-conical` closes by its own proof
  (425-427): trivial fibrations of quasi-categories form a
  right-lifting-property class, so their stability is automatic.
  `lem:brown-fact` closes by its own proof (558-567), constructing the
  path-object factorisation as a pullback and using the 2-of-3 property.
- The converse (an equivalence in `𝒦_{/B}` induces one in `𝒦`) is handled by
  `lem:equiv-htpy-equiv` (cited at line 894): an equivalence is a homotopy
  equivalence with the free-living isomorphism `𝕀` as interval, and the
  homotopy data over `B` already provide homotopy data in `𝒦`. It closes by
  its own proof (460-466), which constructs the inverse and homotopies by
  evaluating the induced equivalence on functor spaces and internalising via
  the cotensor.

Lemma graph (text): `prop:sliced-cosmoi` → {`lem:trivial-fib-conical`,
`lem:brown-fact`} (paired, pullback stability) and → `lem:equiv-htpy-equiv`
(converse); `lem:equiv-htpy-equiv` → `lem:qcat-htpy-cat-equiv` (depth 2). The
three children do not cite each other.

Why each is a good leaf: each is a self-contained statement — its hypotheses
are just `defn:cosmos` plus the class being studied — whose proof closes on
its own from the axioms, without depending on the slice construction.
`lem:equiv-htpy-equiv` is the reusable bridge (used seven more times in the
chapter); `lem:trivial-fib-conical` and `lem:brown-fact` are general
stability/factorisation facts stated once and reused by citation.

Note the `\uses{}` clause (line 882) names only two of the three lemmas:
`lem:equiv-htpy-equiv` is cited inline at line 894 but is absent from the
`\uses{}` list, so a reader following the `\uses{}` dependency graph alone
would miss the converse direction.

## Why it is good

1. The parent site cites `lem:trivial-fib-conical` (check; lines 882 and 891).
2. The parent site cites `lem:brown-fact` (check; lines 882 and 891).
3. The parent site cites `lem:equiv-htpy-equiv` (check; line 894).
4. The shape is a measurement: a 57-line parent site (845-901) whose proof
   cites 3 direct lemmas delegates the three nontrivial components to child
   proofs of 7 (421-427), 22 (546-567) and 16 (451-466) lines, and the longest
   chain of project lemmas below the proposition has depth 2
   (`lem:equiv-htpy-equiv` cites `lem:qcat-htpy-cat-equiv` at line 463, a
   lemma stated without a blueprint proof at 307-312).
5. `lem:equiv-htpy-equiv`, the converse-direction child, is reused as the
   equivalence/homotopy-equivalence bridge at seven other places in the same
   blueprint (lines 480, 486, 496, 541, 1048, 1063, 1067), so it is a reusable
   component rather than a one-off for the slice construction.

## When to use it, and when not

Use it when the goal is to exhibit a structure with a finite, known list of
components, and the hard verification of each component is a self-contained
statement that can be stated and proved independently of the others — then the
parent proof is a thin glue that walks the components and cites one lemma per
nontrivial component. Avoid it when the components share a genuinely common
sub-argument (factor that into a third shared lemma first, as the proof's
footnote pairs `lem:trivial-fib-conical` with `lem:brown-fact`), when the
components are so trivial that inline verification is clearer than a named
lemma, or when the per-component lemmas only re-state the parent's burden and
are not reusable elsewhere.

## Consequences

The parent proof walks the seven items of the cosmos structure and delegates
the hard verifications to named lemmas, so the parent is a survey; a missing
lemma, or a lemma whose statement does not cover the exact construction used
in the slice, leaves a silent gap in the parent. The blueprint's `\uses{}`
clause (line 882) names only two of the three lemmas (`lem:trivial-fib-conical`
and `lem:brown-fact`); `lem:equiv-htpy-equiv` is cited inline at line 894 but
absent from the `\uses{}` list, so a reader following the `\uses{}` dependency
graph alone misses the converse direction. Two of the three children
(`lem:trivial-fib-conical` and `lem:brown-fact`) are paired for the
pullback-stability footnote, so neither alone suffices for that step. The
children are independent (none cites a sibling), but `lem:equiv-htpy-equiv` is
the single shared bridge reused throughout the chapter, so a defect in it
breaks every later argument that routes through it.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/blueprint.yml 'Compile blueprint' runs on push/PR to main with paths 'blueprint/**' (covers blueprint/src/content.tex) and builds the blueprint via lean-action build-args ':blueprint --wfail' + docgen-action blueprint:true; pinned commit 89d7dc3 is HEAD of the default branch (register_source.py git ls-remote HEAD) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 89d7dc3ed861824535e540da489a46469dcc8e56 | check_provenance.py | 2026-11-14 |
| sorry-scan | not-run | no Lean, Rocq or Isabelle file among the copied files | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(prop:sliced-cosmoi, lem:trivial-fib-conical) -> cites: lem:trivial-fib-conical occurs at blueprint/src/content.tex:882 | check_claims.py |
| 2 | verified | cites(prop:sliced-cosmoi, lem:brown-fact) -> cites: lem:brown-fact occurs at blueprint/src/content.tex:882 | check_claims.py |
| 3 | verified | cites(prop:sliced-cosmoi, lem:equiv-htpy-equiv) -> cites: lem:equiv-htpy-equiv occurs at blueprint/src/content.tex:894 | check_claims.py |
| 4 | verified | line counts confirmed in code/blueprint/src/content.tex: parent 845-901 = 57 lines; children 421-427 = 7, 546-567 = 22, 451-466 = 16; lem:equiv-htpy-equiv cites lem:qcat-htpy-cat-equiv at line 463 (grep); lem:qcat-htpy-cat-equiv stated at 307-312 ending \end{lemma} with no proof; prop:coherent-iso (line 277, also cited by lem:equiv-htpy-equiv) is itself proofless (proof commented out), so longest chain below prop has depth 2 | verifier |
| 5 | verified | grep lem:equiv-htpy-equiv in code/blueprint/src/content.tex: all seven listed lines cite it (480 \uses, 486/496/541/1048/1063/1067 \ref) outside the parent proof at 894; note 481 and 502 also cite it, so 'seven' is a slight undercount, but every listed line is a genuine reuse | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent prop:sliced-cosmoi (845-901, 57 lines) states the seven-item cosmo K_{/B}; its proof (881-901) cites exactly the three children: lem:trivial-fib-conical and lem:brown-fact (line 882 uses + line 891 footnote, paired for pullback stability) and lem:equiv-htpy-equiv (line 894, converse). Each child is a lemma node closed by its own proof (425-427, 558-567, 460-466). Shape numbers match the copied code: direct_lemmas=3, depth=2 (lem:equiv-htpy-equiv -> lem:qcat-htpy-cat-equiv at 463, a proofless leaf at 307-312), glue_lines=57 (parent site 845-901), child_lines=[7,22,16] = 421-427, 546-567, 451-466. No sibling cross-citations; children are exactly the lemmas the glue uses. | reviewer-correctness |
| generality | accept | Move is stated generally: 'exhibit a structure with a finite, known list of components' -> 'one named lemma per nontrivial component' -> thin survey glue, not the specific slice. avoid_when is concrete and grounded (shared sub-argument, too-trivial components, non-reusable lemmas). Consequences are honest and specific, verified in source: line 882 \uses names only two lemmas while lem:equiv-htpy-equiv is cited inline at 894 (a real caveat for \uses-graph-guided tools); the two pullback-stability children are paired in the line-891 footnote so neither alone suffices; children are sibling-independent. 'Why each is a good leaf' states the leaf properties a bounded prover needs: self-contained statements (hypotheses are defn:cosmos + the class under study) whose proofs close without depending on the slice construction, plus small sizes (7/22/16 lines, depth 2) and the reuse of lem:equiv-htpy-equiv. Minor: avoid_when's 'factor into a third shared lemma' parenthetical cites the footnote, which actually shows two lemmas paired for one step, not a factored-out sub-argument; and 'one lemma per component' is looser than reality (all three children serve one item's two directions), but the README self-corrects in intent/how-the-parts-fit. Neither undermines the stated generality. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit and licence are consistent and traceable: check_provenance.py reports the single copied file blueprint/src/content.tex is byte-identical at commit 89d7dc3ed861824535e540da489a46469dcc8e56; local sha256 (205fea82...) matches entry.json's files[].sha256; the four site line ranges (845-901, 421-427, 546-567, 451-466) each begin with the cited \label; upstream LICENSE is Apache-2.0, matching source.json and entry.json licence. All cited refs (lem:trivial-fib-conical, lem:brown-fact at 882/891; lem:equiv-htpy-equiv at 894) appear in the cited range. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/emilyriehl/infinity-cosmos at commit `89d7dc3ed861824535e540da489a46469dcc8e56`, under `Apache-2.0`; see the [source note](../../sources/infinity-cosmos/SOURCE.md) for the licence text and attribution.
