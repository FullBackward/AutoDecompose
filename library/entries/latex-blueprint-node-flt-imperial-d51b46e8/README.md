# The l-torsion of the Frey curve is hardly ramified: a blueprint node assembled from four lemmas

| | |
|---|---|
| Kind | instance |
| Move | blueprint-node |
| Language | latex |
| Status | accepted |
| Source | [flt-imperial](../../sources/flt-imperial/SOURCE.md) at `a3210204ad88` |
| Licence | `Apache-2.0` |

## Intent

Prove the chapter's first main result — that the ℓ-torsion of the Frey curve is
hardly ramified — by unfolding the definition `hardly_ramified` (a conjunction
of four axioms) and discharging each axiom with one named theorem, so the proof
is a one-to-one match of axiom to lemma with no other content.

## The decomposition

### parent `frey_curve_hardly_ramified`: [`blueprint/src/chapter/ch03freyold.tex` lines 290-299](https://github.com/ImperialCollegeLondon/FLT/blob/a3210204ad8876e851e32f73dd97d882bf1ccd0a/blueprint/src/chapter/ch03freyold.tex#L290-L299) ([local copy](code/blueprint/src/chapter/ch03freyold.tex))

```latex
\begin{theorem}\label{frey_curve_hardly_ramified}\uses{hardly_ramified}\notready Let $\rho$ be the Galois representation on the
  $\ell$-torsion of the Frey curve coming from a Frey package $(a,b,c,\ell)$. Then $\rho$ is hardly
  ramified.
\end{theorem}
\begin{proof}\uses{Elliptic_curve_det_n_torsion, frey_curve_unramified, frey_curve_at_2, Frey_curve_mod_ell_rep_at_ell}
  This follows from the results above. The fact that $\ell\geq 5$ follows from the definition of
  a Frey package. The first condition is theorem~\ref{Elliptic_curve_det_n_torsion},
  and the second is theorem~\ref{frey_curve_unramified}. The third condition is
  theorem~\ref{frey_curve_at_2}, and the fourth is theorem~\ref{Frey_curve_mod_ell_rep_at_ell}.
\end{proof}
```

### context `hardly_ramified`: [`blueprint/src/chapter/ch03freyold.tex` lines 184-193](https://github.com/ImperialCollegeLondon/FLT/blob/a3210204ad8876e851e32f73dd97d882bf1ccd0a/blueprint/src/chapter/ch03freyold.tex#L184-L193) ([local copy](code/blueprint/src/chapter/ch03freyold.tex))

```latex
\begin{definition}\label{hardly_ramified}\notready Let $\ell\geq5$ be a prime and let $V$ be a
  2-dimensional vector space over $\Z/\ell\Z$. A representation
  $\rho: \GQ\to \GL(V)$ is said to be \emph{hardly ramified} if it satisfies the following four axioms:
  \begin{enumerate}
  \item $\det(\rho)$ is the mod $\ell$ cyclotomic character;
  \item $\rho$ is unramified outside $2\ell$;
  \item The semisimplification of the restriction of $\rho$ to $\Gal(\Qbar_2/\Q_2)$ is unramified;
  \item The restriction of $\rho$ to $\GQl$ comes from a finite flat group scheme.
  \end{enumerate}
\end{definition}
```

### child `Elliptic_curve_det_n_torsion`: [`blueprint/src/chapter/ch03freyold.tex` lines 44-48](https://github.com/ImperialCollegeLondon/FLT/blob/a3210204ad8876e851e32f73dd97d882bf1ccd0a/blueprint/src/chapter/ch03freyold.tex#L44-L48) ([local copy](code/blueprint/src/chapter/ch03freyold.tex))

```latex
\begin{theorem}\label{Elliptic_curve_det_n_torsion}\uses{Elliptic_curve_n_torsion_2d} If $E$ is an elliptic curve over a field $k$, and $n$ is a positive integer which is nonzero in $k$, then the determinant of the 2-dimensional representation of $\Gal(k^{\sep}/k)$ on $E(k^{\sep})[n]$ is the mod $n$ cyclotomic character.
\end{theorem}
\begin{proof}
  This presumably should be done via the Weil pairing. I have not yet put any thought into a feasible way to formalise this.
\end{proof}
```

### child `frey_curve_unramified`: [`blueprint/src/chapter/ch03freyold.tex` lines 255-258](https://github.com/ImperialCollegeLondon/FLT/blob/a3210204ad8876e851e32f73dd97d882bf1ccd0a/blueprint/src/chapter/ch03freyold.tex#L255-L258) ([local copy](code/blueprint/src/chapter/ch03freyold.tex))

```latex
\begin{corollary}\label{frey_curve_unramified}\notready If $(a,b,c,\ell)$ is a Frey package, then the $\ell$-torsion in the Frey curve is unramified at all primes $p\not=2,\ell$.
\end{corollary}
\begin{proof}\uses{Frey_curve_good, Frey_curve_unram} Follows from~\ref{Frey_curve_good} and~\ref{Frey_curve_unram}.
\end{proof}
```

### child `frey_curve_at_2`: [`blueprint/src/chapter/ch03freyold.tex` lines 264-272](https://github.com/ImperialCollegeLondon/FLT/blob/a3210204ad8876e851e32f73dd97d882bf1ccd0a/blueprint/src/chapter/ch03freyold.tex#L264-L272) ([local copy](code/blueprint/src/chapter/ch03freyold.tex))

```latex
\begin{corollary}\label{frey_curve_at_2}\notready If $(a,b,c,\ell)$ is a Frey package, then the
  semisimplification of the restriction of the $\ell$-torsion $\rho$ in the associated Frey curve
  to $\Gal(\Qbar_2/\Q_2)$ is unramified.
\end{corollary}
\begin{proof}\uses{multiplicative_reduction_torsion} After a quadratic twist to make the curve have split multiplicative
  reduction, the theory of the Tate curve shows us that $\rho$ is an extension
  of the trivial character by the cyclotomic character. Hence the semisimplification of this representation is the direct sum of two
  unramified characters and is hence unramified.
\end{proof}
```

### child `Frey_curve_mod_ell_rep_at_ell`: [`blueprint/src/chapter/ch03freyold.tex` lines 274-286](https://github.com/ImperialCollegeLondon/FLT/blob/a3210204ad8876e851e32f73dd97d882bf1ccd0a/blueprint/src/chapter/ch03freyold.tex#L274-L286) ([local copy](code/blueprint/src/chapter/ch03freyold.tex))

```latex
\begin{theorem}\label{Frey_curve_mod_ell_rep_at_ell}\uses{finite_flat_group_scheme}\notready Let $\rho$ be the $\ell$-torsion in the
  Frey curve associated to a Frey package $(a,b,c,\ell)$. Then the restriction of $\rho$ to $\GQl$ comes from a finite flat group scheme.
\end{theorem}
\begin{proof}\uses{good_reduction_implies_flat, multiplicative_reduction_torsion} The Frey curve either has good reduction at $\ell$ (case 1 of FLT) or multiplicative
  reduction at $\ell$ (case 2 of FLT). In the first case the $\ell$-torsion is finite and flat
  at $\ell$ by theorem~\ref{good_reduction_implies_flat}. In the second case the theory of the Tate
   curve shows that the $\ell$-torsion is (up to quadratic twist) an extension of
    the trivial character by the cyclotomic character corresponding (via Hilbert 90)
    to the $\ell$th power of an $\ell$-adic unit. This extension is known to be finite and flat;
  see for example Proposition~8.2 of~\cite{edix}. Note that the proof in~\cite{edix} uses
  fppf cohomology, although one can write down a much more elementary proof of this using
  arguments in~\cite{katz-mazur}.
\end{proof}
```

How the parts fit. The parent theorem unfolds the definition `hardly_ramified`,
which is a conjunction of four axioms plus the standing hypothesis that ℓ ≥ 5 is
a prime. The proof is the glue: it cites one named theorem per axiom, in order,
and discharges the remaining input ℓ ≥ 5 for free from the definition of a Frey
package (`ch02reductions.tex` lines 59-61: a Frey package has a prime p ≥ 5).
The lemma graph (arrows = "cites in its `\uses{}` / proof") is:

```
frey_curve_hardly_ramified  (parent; unfolds hardly_ramified)
├─ axiom 1: det ρ = mod ℓ cyclotomic  ← Elliptic_curve_det_n_torsion
│      └─ Elliptic_curve_n_torsion_2d
├─ axiom 2: ρ unramified outside 2ℓ   ← frey_curve_unramified
│      ├─ Frey_curve_good ── Frey_curve_good_reduction, good_reduction_implies_unramified
│      └─ Frey_curve_unram ── multiplicative_reduction_torsion,
│                             FreyCurve.j_valuation_of_bad_prime ── Frey_curve_j
├─ axiom 3: semisimplification at 2   ← frey_curve_at_2
│      └─ multiplicative_reduction_torsion
└─ axiom 4: finite flat at ℓ          ← Frey_curve_mod_ell_rep_at_ell
       └─ good_reduction_implies_flat, multiplicative_reduction_torsion
  (+ free input ℓ ≥ 5, from the Frey package definition)
```

Each child is a good leaf because it is a self-contained named statement whose
own proof closes on its own or from named siblings, independent of the parent:

- `Elliptic_curve_det_n_torsion` is a general fact about any elliptic curve over
  a field (no Frey-package hypothesis), so it closes separately from the
  Frey-specific children; its own `\uses` is `Elliptic_curve_n_torsion_2d`.
- `frey_curve_unramified` is the "unramified outside 2ℓ" half, itself the join of
  two cases — primes not dividing abc (`Frey_curve_good`) and odd primes dividing
  abc (`Frey_curve_unram`) — so it closes from two siblings that do not mention
  the other three axioms.
- `frey_curve_at_2` is the "what happens at the prime 2" half, closed from the
  Tate-curve description `multiplicative_reduction_torsion`; it is deliberately
  separated from `frey_curve_unramified` because at 2 one only gets the
  semisimplification, not full unramification.
- `Frey_curve_mod_ell_rep_at_ell` is the "finite flat at ℓ" half, closed by a case
  split on good vs. multiplicative reduction at ℓ; it does not share hypotheses
  with the other three, so it can be proved in isolation.

The move is thus exactly the shape the protocol calls *theorem scale*: a
10-line parent whose proof is a list of four citations, each child a bounded
hole to be filled by its own sub-decomposition. Note the node is marked
`notready`, so nothing here is yet checked by Lean; the corresponding Lean
statement `FreyCurve.torsion_isHardlyRamified` is still `sorry`
(`FLT/GaloisRepresentation/HardlyRamified/Frey.lean` lines 37-41 at this
commit). This is the defining feature of a `blueprint-node` move: the node is
stated before it is proved, and its value is the decomposition it fixes, not the
proof.

## Why it is good

1. The glue cites `Elliptic_curve_det_n_torsion` among its four conditions; a
   tool check confirms the name occurs in the parent's lines (`check`, lines
   290-299).
2. The four-axiom structure is machine-visible: the file contains exactly four
   `\item` entries, the four axioms of `hardly_ramified` (`check`, lines
   184-193).
3. The shape is small and front-loaded: the glue is 10 lines and the four child
   sites are 5, 4, 9 and 13 lines (31 lines of lemma holes under a 10-line
   glue), so every bit of difficulty lives in the children, not the assembly
   (`measurement`).
4. The authors themselves frame it as a definition-plus-four-axioms and as "the
   first main result of this chapter" (`author-statement`, lines 186 and 288).
5. The split is reused: the next section's proof of
   `Frey_characters_are_unramified` re-cites two of the children,
   `frey_curve_unramified` and `frey_curve_at_2` (`known-use`, lines 323-331).

In my opinion the detail worth copying is the *one-to-one match*: the proof
prose literally walks the axioms ("the first condition is …, the second is …")
so the four citations and the four `\item`s stay in lockstep. That lockstep is
what makes the node safe to hand to separate provers, one per hole.

## When to use it, and when not

Use it when the goal is "ρ has property P" and P is a definition written as a
short conjunction of named axioms, and a named theorem already exists for each
axiom. Then the proof is a pure match: one citation per axiom, and the only
extra work is discharging the definition's side conditions (here ℓ ≥ 5, from
the Frey package). Avoid it when the axioms overlap or share hypotheses that
must be established together (they cannot then be discharged by independent
citations), or when a single axiom carries all the difficulty and the rest are
trivial, in which case the decomposition is noise, not structure.

## Consequences

Unfolding `hardly_ramified` creates four obligations plus the side condition
ℓ ≥ 5, discharged for free from the Frey package definition. Each obligation is
handed to a single named theorem, so the glue has no mathematical content of its
own: if one of the four cited theorems is wrong or too weak for its axiom, the
node fails silently (it is `notready`, so Lean checks nothing). The four
children are themselves deep and only sketched, so the node is a promise to the
dependency graph, not a proof; the real cost is deferred to the children's own
sub-decompositions.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/blueprint.yml (workflow 'Build project', step 'Compile documentation' uses leanprover-community/docgen-action with blueprint:true, triggered on push/PR to main for paths blueprint/**) builds the blueprint including blueprint/src/chapter/ch03freyold.tex on the default branch main; pinned commit a3210204ad8876e851e32f73dd97d882bf1ccd0a is the tip of default branch main (GitHub compare main...a3210204 identical, established for this source) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at a3210204ad8876e851e32f73dd97d882bf1ccd0a | check_provenance.py | 2026-11-14 |
| sorry-scan | not-run | no Lean, Rocq or Isabelle file among the copied files | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(frey_curve_hardly_ramified, Elliptic_curve_det_n_torsion) -> cites: Elliptic_curve_det_n_torsion occurs at blueprint/src/chapter/ch03freyold.tex:294 | check_claims.py |
| 2 | verified | count(\item, 4, blueprint/src/chapter/ch03freyold.tex) -> count: \item occurs 4 times in 1 file(s) matching blueprint/src/chapter/ch03freyold.tex | check_claims.py |
| 3 | verified | Line counts read from copied ch03freyold.tex: parent frey_curve_hardly_ramified L290-L299 = 10 lines (theorem 290-293 + proof 294-299); children Elliptic_curve_det_n_torsion L44-L48 = 5, frey_curve_unramified L255-L258 = 4, frey_curve_at_2 L264-L272 = 9, Frey_curve_mod_ell_rep_at_ell L274-L286 = 13; child sum 31 under a 10-line glue | verifier |
| 4 | verified | Read copied ch03freyold.tex: L186 reads 'is said to be hardly ramified if it satisfies the following four axioms' (definition hardly_ramified, within L184-L193 context site); L288 reads 'We have now proved the first main result of this chapter.' Both quoted sentences present at the cited lines | verifier |
| 5 | verified | Read copied ch03freyold.tex L323-L331: theorem Frey_characters_are_unramified begins L323, its proof (L326) opens with \uses{frey_curve_unramified, frey_curve_at_2} and cites both by \ref in the body; both are children of the entry, confirming the known-use | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Decomposition matches the code: the parent theorem frey_curve_hardly_ramified (L290-299) is marked notready and its proof \uses{} exactly the four children Elliptic_curve_det_n_torsion, frey_curve_unramified, frey_curve_at_2, Frey_curve_mod_ell_rep_at_ell, one per axiom of hardly_ramified (L184-193, four \item entries). Each child's closed_by matches its proof \uses{} verbatim (Weil-pairing sketch; Frey_curve_good+Frey_curve_unram; multiplicative_reduction_torsion; good_reduction_implies_flat+multiplicative_reduction_torsion), and the side condition l>=5 follows from FreyPackage (ch02reductions.tex L59-61). Shape numbers verified: direct_lemmas=4, glue_lines=10 (L290-299), child_lines=[5,4,9,13] (L44-48, L255-258, L264-272, L274-286); depth=4 matches the documented chain frey_curve_unramified->Frey_curve_unram->FreyCurve.j_valuation_of_bad_prime->Frey_curve_j read off the \uses lines. Entry is honest that the node is notready/unformalised, so it closes in blueprint terms only. | reviewer-correctness |
| generality | accept | Move generalizes to 'rho has P' where P is a short conjunction of named axioms with a theorem per axiom; avoid_when is specific (overlapping/shared hypotheses that must be proved together; or one axiom carrying all the difficulty makes the split noise). Consequences are honest: node is notready so a wrong/too-weak cited theorem fails silently, and the children are deep/sketched so the cost is deferred to their sub-decompositions. Good leaves are explained: each child is self-contained with hypotheses independent of the other axioms and closes from its own dependencies (one is a general field-level fact with no Frey hypothesis, one joins two cases, one is separated because at 2 only the semisimplification holds, one case-splits good vs multiplicative reduction), and the one-to-one axiom-to-citation lockstep is what makes it safe to hand one hole per bounded prover. | reviewer-generality |
| provenance-licence | accept | Provenance-licence consistent: check_provenance.py passes (2 files byte-identical at a3210204ad8876e851e32f73dd97d882bf1ccd0a). Both copied files' sha256 match entry.json (ch03freyold.tex ace6e25e..., ch02reductions.tex ea42852a...). All six site permalinks use the pinned commit and path blueprint/src/chapter/ch03freyold.tex with line ranges that match the local copies verbatim (parent L290-299, context L184-193, children L44-48/255-258/264-272/274-286); claim locators L186/L288/L323-331/L326 and ch02reductions.tex L59-61 also match. Licence Apache-2.0 is consistent across SOURCE.md (detected + upstream-LICENSE, whose text I confirmed is Apache 2.0), source.json, entry.json and README. All traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/ImperialCollegeLondon/FLT at commit `a3210204ad8876e851e32f73dd97d882bf1ccd0a`, under `Apache-2.0`; see the [source note](../../sources/flt-imperial/SOURCE.md) for the licence text and attribution.
