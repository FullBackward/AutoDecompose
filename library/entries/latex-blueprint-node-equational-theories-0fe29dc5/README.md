# Blueprint node greedy-iterate: iterating the greedy extension to a complete 1323 magma

| | |
|---|---|
| Kind | instance |
| Move | blueprint-node |
| Language | latex |
| Status | accepted |
| Source | [equational-theories](../../sources/equational-theories/SOURCE.md) at `8b87204d5b20` |
| Licence | `Apache-2.0` |

## Intent

The blueprint node `greedy-iterate` closes the chapter's construction by citing
three already-stated nodes (`greedy-1323`, `build-magma`,
`partial-1323-sound`) and adding one sentence of glue, so every partial
solution extends to a complete 1323 magma with no new argument.

## The decomposition

### parent `greedy-iterate`: [`blueprint/src/chapter/1323.tex` lines 111-115](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/blueprint/src/chapter/1323.tex#L111-L115) ([local copy](code/blueprint/src/chapter/1323.tex))

```latex
\begin{corollary}[Iterated greedy extension]\label{greedy-iterate}\leanok\lean{Eq1323.exists_complete_function}  Every partial solution can be extended to a complete solution that satisfies \Cref{lr} and \Cref{lr-simp}, and hence 1323.
\end{corollary}

\begin{proof}\uses{greedy-1323, build-magma, partial-1323-sound} Apply the usual greedy algorithm.
\end{proof}
```

### child `greedy-1323`: [`blueprint/src/chapter/1323.tex` lines 101-109](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/blueprint/src/chapter/1323.tex#L101-L109) ([local copy](code/blueprint/src/chapter/1323.tex))

```latex
\begin{lemma}[Greedy extension]\label{greedy-1323}\uses{partial-1323-sound}\leanok\lean{Eq1323.extend}  If $\op$ is defined by a partial solution, and $(x,a) \op (y,b)$ is undefined for some $x,y \in \Q^\times$ and distinct $a,b \in G \backslash \{0\}$, then it is possible to extend the partial solution so that $(x,a) \op (y,b)$ is now defined.
\end{lemma}

\begin{proof} We select a $c \in G \backslash \{0\}$ that has not previously been used by the partial solution, let $z \in \Q^\times$ be arbitrary, (e.g., one could take $z=1$ if desired), and add $(x,y,z,a,b,c)$ to ${\mathcal F}$, thus we now also assign
$$ (\phi_a(b)^n x,a) \op (\phi_b(c)^n y,b) = (\phi_c(a)^n z,c)$$
$$ (\phi_b(c)^n y,b) \op (\phi_c(a)^n z,c) = (\phi_a(b)^{n+1} x, a)$$
$$ (\phi_c(a)^n z,c) \op (\phi_a(b)^{n+1} x, a) = (\phi_b(c)^{n+1} y,b)$$
for all natural numbers $n$.  As the $a,b,c$ are distinct, the $\phi_a(b), \phi_b(c), \phi_c(a)$ are not equal to $\pm 1$, and the members of this infinite sequence do not collide with each other.  The second and third equations in this family cannot collide with previous assignments because $c$ is novel.  If we arrange matters so that $\phi_b(c)$ involves primes in the numerator or denominator that do not appear in any previous $\phi_a(b), \phi_b(c), \phi_c(a), x, y, z$ used by the greedy algorithm, or the current $x,y,z$, then we also see that the first infinite sequence does not collide with any previously assigned value of $\op$ either.
\end{proof}
```

### child `build-magma`: [`blueprint/src/chapter/1323.tex` lines 37-85](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/blueprint/src/chapter/1323.tex#L37-L85) ([local copy](code/blueprint/src/chapter/1323.tex))

```latex
 \begin{lemma}[Building a magma]\label{build-magma}\leanok\lean{Eq1323.op}\lean{Eq1323.op_RSy_LSy_eq_Id}\lean{Eq1323.op_Ly_Ry_eq_LSy}  Let $G$ be a countably infinite abelian torsion group of exponent $2$, and let $\phi_a$ be as in the previous lemma.  Let $N$ be the set of pairs $(x,a)$ with $x \in \Q^\times$ and $a \in G \backslash \{0\}$, and let $M = G \uplus N$ be the disjoint union of $G$ and $N$.  Suppose that we have an operation $\op : M \times M \to M$ satisfying the following axioms:
\begin{itemize}
\item (i) We have
\begin{equation}\label{op-0}
  a \op b = a+b
\end{equation}
for $a,b \in G$.
\item (ii) We have
 \begin{equation}\label{op-1}
  (x,a) \op b = (\phi_a(b) x, a)
 \end{equation}
 \begin{equation}\label{op-2}
   b \op (x,a) = (x / \phi_a(b), a)
 \end{equation}
 and
 \begin{equation}\label{op-3}
   (\phi_a(b) x,a) \op (x,a) = a+b
 \end{equation}
 for $x \in \Q^\times$, $b \in G$, and $a \in G \backslash \{0\}$.
\item (iii) If $a,b,0 \in G$ are distinct and
$(x,a) \op (y,b) = (z,c)$ for some $x,y,z \in \Q^\times$ and $c \in G$, then $(y,b) \op (z,c) = (\phi_a(b) x,a)$.
\end{itemize}
Then \Cref{lr}, \Cref{lr-simp} and hence \Cref{1323} holds.
\end{lemma}

\begin{proof}\uses{bij}
  With these rules, $0$ is a unit, and the squaring operator is given by $Sa = 0$ and $S(x,a) = a$, so the set of squares is $G$.  If $a \in G$ is a square number, we have
  $$ L_a b = R_a b = a+b$$
  and
  $$ L_a (x,b) = (x/\phi_b(a), b); \quad R_a (x,b) = (x \phi_b(a), b)$$
  so \Cref{lr} is satisfied.

Now we verify \Cref{lr-simp}.
If $y$ is a square, then the claim already follows from \Cref{lr} since $Sy=0$ is a unit.  Otherwise, for $y \in \Q^\times$ and $b \in G \backslash \{0\}$, we have to show that
$$ L_{(y,b)} R_{(y,b)} a = R_b a = a+b$$
for $a \in G$ and
$$ L_{(y,b)} R_{(y,b)} (x,a) = R_b (x,a) = (\phi_a(b) x, a) $$
for $x \in \Q^\times$ and $a \in G \backslash \{0\}$.  In the first case, we have from \Cref{op-2} that
$$ R_{(y,b)} a = (y/\phi_a(b), b)$$
and then from \Cref{op-3} we have
$$L_{(y,b)} R_{(y,b)} a = a+b$$
as required.  In the second case, if $a=b$, then by the bijective nature of $\phi_a$, we can write $x = \phi_a(c) y$ for some $c \in G$, then from \Cref{op-3} we have
$$ R_{(y,b)} (x,a) = a+c$$
and then by \Cref{op-1}
$$ L_{(y,b)} R_{(y,b)} (x,a) = (\phi_a(a+c) y, a)$$
but from construction we have $\phi_a(a+c)=-\phi_a(c) = \phi_a(b)\phi_a(c)$ and hence $\phi_a(a+c) y = \phi_a(b) x$ as required.

It remains to handle the case when $a,b$ are distinct elements of $G \backslash \{0\}$.  But this follows from (iii).
\end{proof}
```

### child `partial-1323-sound`: [`blueprint/src/chapter/1323.tex` lines 91-99](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/blueprint/src/chapter/1323.tex#L91-L99) ([local copy](code/blueprint/src/chapter/1323.tex))

```latex
\begin{lemma}[Soundness]\label{partial-1323-sound}\uses{partial-1323}  Let ${\mathcal F}$ be a partial solution.  Then if one defines a partial operation $\op$ on $M$ by requiring axioms (i), (ii), imposing the additional operations
$$ (\phi_a(b)^n x,a) \op (\phi_b(c)^n y,b) = (\phi_c(a)^n z,c)$$
$$ (\phi_b(c)^n y,b) \op (\phi_c(a)^n z,c) = (\phi_a(b)^{n+1} x, a)$$
$$ (\phi_c(a)^n z,c) \op (\phi_a(b)^{n+1} x, a) = (\phi_b(c)^{n+1} y,b)$$
for all $n \geq 0$ and $(x,y,z,a,b,c) \in {\mathcal F}$, and no other operations, then this is a well-defined partial operation that satisfies axiom (iii) whenever it is defined.
\end{lemma}

\begin{proof} Routine.
\end{proof}
```

How the parts fit. The glue is a single `\uses{}` clause plus one sentence
(lines 114-115): the corollary holds because `greedy-1323` lets us define any
still-undefined pair, `build-magma` turns a complete operation satisfying the
axioms into a magma that satisfies 1323, and `partial-1323-sound` says each
greedy step stays a well-defined partial operation. The lemma graph is:

```
greedy-iterate (corollary, 111-115)
 ├─ greedy-1323 (101-109)      ──uses── partial-1323-sound (91-99)
 ├─ build-magma (37-85)        ──uses── bij (27-34)
 └─ partial-1323-sound (91-99) ──uses── partial-1323 (definition, 87-89)
```

Each child is a good leaf because its statement is self-contained and its proof
closes on its own or from a named sibling:

- `greedy-1323` states that any undefined pair can be defined, and its proof
  (104-108) selects a fresh `c` and arbitrary `z`, adds one tuple, and argues
  the new infinite orbit cannot collide — using only `partial-1323-sound` to
  know the existing partial operation already satisfies axiom (iii).
- `build-magma` states that any operation satisfying axioms (i)-(iii) makes
  the magma satisfy (lr) and (lr-simp); its proof (62-85) is a direct case
  analysis that uses `bij` for the bijectivity step and discharges the
  distinct-pair case by axiom (iii).
- `partial-1323-sound` states that a partial solution yields a well-defined
  partial operation; its proof is literally "Routine." (98), so it closes from
  the definition of partial solution (87-89).

The `\lean{}` annotations carry each node to its Lean counterpart in
[`equational_theories/ManuallyProved/Equation1323.lean`](code/equational_theories/ManuallyProved/Equation1323.lean):
`greedy-iterate` → `exists_complete_function` (536-560), `greedy-1323` →
`extend` (523-530), `build-magma` → `op` / `op_RSy_LSy_eq_Id` /
`op_Ly_Ry_eq_LSy` (570-577, 579-580, 595-610). `partial-1323-sound` has no
`\lean{}`; its content is folded into the `Axiom3` definition (533-534) and the
`Axiom3 f` conclusion of `exists_complete_function`.

## Why it is good

1. The parent site `greedy-iterate` (the corollary and its proof) is 5 lines
   long (`check`, `lines(greedy-iterate, 5)`).
2. The glue cites `greedy-1323` (`check`, `cites(greedy-iterate, greedy-1323)`).
3. The glue cites `build-magma` (`check`, `cites(greedy-iterate, build-magma)`).
4. The glue cites `partial-1323-sound` (`check`, `cites(greedy-iterate, partial-1323-sound)`).
5. The corollary's glue directly cites 3 project lemmas, and the longest chain
   of project lemmas below the corollary has depth 2 (`measurement`; the three
   names in the `\uses{}` clause at line 114, `greedy-1323`'s
   `\uses{partial-1323-sound}` at line 101, and `build-magma`'s `\uses{bij}` at
   line 62).

In my opinion the detail worth copying is the one-line glue: the node's proof
is nothing but the `\uses{}` clause plus "Apply the usual greedy algorithm",
which is exactly the skeleton-with-holes shape a theorem-scale decomposition
should produce.

## When to use it, and when not

Use it when the published dependency graph (`\uses{}` edges and `\lean{}`
annotations) is the source of truth and a node's proof names its children
without adding a new argument; then the node is honest as a one-line glue and
each child closes on its own. Avoid it when the `\uses{}` edges are missing or
wrong, when the proof carries real content that deserves its own node rather
than a glue line, or when a child has no `\lean{}` mapping and its formal
counterpart is not otherwise locatable.

## Consequences

Each node must state its children before it is proved and keep the `\uses{}`
edges acyclic and complete: every lemma the proof uses must be named. A child
whose `\lean{}` annotation is missing (`partial-1323-sound` here) leaves its
formal counterpart implicit, so a reader cannot navigate straight to the code.
If the one-sentence glue is wrong about which siblings suffice, the node fails
even though every child is true.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/blueprint-paper.yml (Compile blueprint and paper); triggers on push/PR to default branch main with path filter 'blueprint/**', and its 'Build project documentation' step runs docgen-action with blueprint:true; 'Build project' step runs lake build equational_theories (compiles Equation1323.lean). Covers blueprint/src/chapter/1323.tex. | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at 8b87204d5b201e1cf6c69b8dcabb0558109bee00 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(greedy-iterate, 5) -> lines: site greedy-iterate has 5 lines | check_claims.py |
| 2 | verified | cites(greedy-iterate, greedy-1323) -> cites: greedy-1323 occurs at blueprint/src/chapter/1323.tex:114 | check_claims.py |
| 3 | verified | cites(greedy-iterate, build-magma) -> cites: build-magma occurs at blueprint/src/chapter/1323.tex:114 | check_claims.py |
| 4 | verified | cites(greedy-iterate, partial-1323-sound) -> cites: partial-1323-sound occurs at blueprint/src/chapter/1323.tex:114 | check_claims.py |
| 5 | verified | Read copied code/blueprint/src/chapter/1323.tex: line 114 = \begin{proof}\uses{greedy-1323, build-magma, partial-1323-sound} (3 direct lemmas); line 101 = greedy-1323 lemma with \uses{partial-1323-sound}; line 62 = build-magma proof opening \begin{proof}\uses{bij}. Depth 2 (corollary -> greedy-1323/build-magma -> partial-1323-sound/bij) confirmed. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent site greedy-iterate is 1323.tex:111-115 (5 lines), its proof at :114 cites exactly \uses{greedy-1323, build-magma, partial-1323-sound} = the entry's three children, nothing else. Children match the code: greedy-1323 101-109 (9 lines), build-magma 37-85 (49 lines, \uses{bij} at :62), partial-1323-sound 91-99 (9 lines). Closing methods match: greedy-1323 proof 104-108, build-magma proof 62-85, partial-1323-sound 'Routine.' at :98. Shape numbers right: direct_lemmas=3, depth=2 (greedy-iterate->greedy-1323->partial-1323-sound, and ->build-magma->bij), glue_lines=5, child_lines=[9,49,9]. Lean \lean{} mappings verified at cited ranges (extend 523-530, Axiom3 533-534, exists_complete_function 536-560, op 570-577, op_RSy_LSy_eq_Id 579-580, op_Ly_Ry_eq_LSy 595-610). Provenance: 2 files byte-identical. | reviewer-correctness |
| generality | accept | Move stated beyond the example via goal_shape/use_when/avoid_when plus three named analogues in also_known_as; when-not-to-use and consequences are specific and honest, flagging the missing lean-annotation child (partial-1323-sound) that the entry itself contains and locating its folded-in Lean counterpart; the good-leaf section names the bounded-prover-relevant property (self-contained statement, closes on its own or from a named sibling), confirmed in the cited tex ranges. | reviewer-generality |
| provenance-licence | accept | Permalinks use full pinned commit 8b87204d5b201e1cf6c69b8dcabb0558109bee00 matching source.json/SOURCE.md; check_provenance passes (2 files byte-identical at that commit); licence Apache-2.0 consistent across entry.json, README, SOURCE.md, source.json and upstream-LICENSE (Apache-2.0 text present); SOURCE.md records licence files and attribution; all cited line ranges in 1323.tex (111-115,101-109,37-85,91-99,87-89,27-34) and Equation1323.lean (536-560,523-530,533-534,570-577,579-580,595-610) match the copied files. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/teorth/equational_theories at commit `8b87204d5b201e1cf6c69b8dcabb0558109bee00`, under `Apache-2.0`; see the [source note](../../sources/equational-theories/SOURCE.md) for the licence text and attribution.
