# Blueprint node hom-pfr: homomorphism form of PFR glued from goursat and pfr-9-aux'

| | |
|---|---|
| Kind | instance |
| Move | blueprint-node |
| Language | latex |
| Status | accepted |
| Source | [pfr](../../sources/pfr/SOURCE.md) at `1ef23c3c5a83` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T09:12:30Z |

## Intent

The chapter headline node `hom-pfr` freezes its statement and Lean name
(`homomorphism_pfr`) before any proof text, then proves it with a
covering-and-counting argument over the graph of `f` that composes exactly two
already-stated nodes — `goursat`, which factorises a subspace of `G × G'`, and
`pfr-9-aux'`, which covers a set by a subgroup `H`. The proof is a short glue
between these two named lemma holes.

## The decomposition

### parent `hom-pfr`: [`blueprint/src/chapter/hom_pfr.tex` lines 19-47](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/blueprint/src/chapter/hom_pfr.tex#L19-L47) ([local copy](code/blueprint/src/chapter/hom_pfr.tex))

```latex
\begin{theorem}[Homomorphism form of PFR]\label{hom-pfr}\lean{homomorphism_pfr}\leanok  Let $f: G \to G'$ be a function, and let $S$ denote the set
$$ S := \{ f(x+y)-f(x)-f(y): x,y \in G \}.$$
Then there exists a homomorphism $\phi: G \to G'$ such that
$$ |\{ f(x) - \phi(x): x \in G \}| \leq |S|^{10}.$$
\end{theorem}

\begin{proof}\uses{goursat, pfr-9-aux'}\leanok
Consider the graph $A \subset G \times G'$ defined by
$$ A := \{ (x,f(x)): x \in G \}.$$
Clearly, $|A| = |G|$.  By hypothesis, we have
$$ A+A \subset \{ (x,f(x)+s): x \in G, s \in S\}$$
and hence $|A+A| \leq |S| |A|$.  Applying \Cref{pfr-9-aux'}, we may find a
subspace $H \subset G \times G'$ such that $|H|/ |A| \in [|S|^{-8}, |S|^{8}]$
and $A$ is covered by $c + H$ with $|c| \le |S|^5|A|^{1/2} / |H|^{1/2}$. If
we let $H_0, H_1$ be as in \Cref{goursat}, this implies on taking projections
that $G$ is covered by at most $|c|$ translates of $H_0$. This implies that
$$ |c| |H_0| \geq |G|;$$
since $|H_0| |H_1| = |H|$, we conclude that
$$ |H_1| \leq |c| |H|/|G| = |c| |H|/|A|.$$
By hypothesis, $A$ is covered by at most $|c|$ translates of $H$, and hence
by at most $|c| |H_1|$ translates of $\{ (x,\phi(x)): x \in G \}$. As $\phi$
is a homomorphism, each such translate can be written in the form $\{
(x,\phi(x)+d): x \in G \}$ for some $d \in G'$. Since
$$
|c| |H_1| \le |c|^2 \frac{|H|}{|A|} \le \left(|S|^5 \frac{|A|^{1/2}}{|H|^{1/2}}\right)^2 \frac{|H|}{|A|}
= |S|^{10},
$$
the result follows.
\end{proof}
```

### child `goursat`: [`blueprint/src/chapter/hom_pfr.tex` lines 11-17](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/blueprint/src/chapter/hom_pfr.tex#L11-L17) ([local copy](code/blueprint/src/chapter/hom_pfr.tex))

```latex
\begin{lemma}[Goursat type theorem]\label{goursat}\lean{goursat}\leanok  Let $H$ be a subgroup of $G \times G'$.  Then there exists a subgroup $H_0$ of $G$, a subgroup $H_1$ of $G'$, and a homomorphism $\phi: G \to G'$ such that
$$ H := \{ (x, \phi(x) + y): x \in H_0, y \in H_1 \}.$$
In particular, $|H| = |H_0| |H_1|$.
\end{lemma}

\begin{proof}\uses{hb-thm}\leanok We can take $H_0$ to be the projection of $H$ to $G$, and $H_1$ to be the slice $H_1 := \{ y: (0,y) \in H \}$.  One can construct $\phi$ on $H_0$ one generator at a time by the greedy algorithm, and then extend to $G$ by \Cref{hb-thm}.  The cardinality bound is clear from direct counting.
\end{proof}
```

### child `pfr-9-aux'`: [`blueprint/src/chapter/further_improvement.tex` lines 363-373](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/blueprint/src/chapter/further_improvement.tex#L363-L373) ([local copy](code/blueprint/src/chapter/further_improvement.tex))

```latex
\begin{corollary}\label{pfr-9-aux'}\lean{better_PFR_conjecture_aux}\leanok
If $|A+A| \leq K|A|$, then there exist a subgroup $H$ and a subset $c$ of $G$
with $A \subseteq c + H$, such that $|c| \leq K^{5} |A|^{1/2}/|H|^{1/2}$ and
$|H|/|A|\in[K^{-8},K^8]$.
\end{corollary}

\begin{proof}\leanok
  \uses{pfr-9-aux, ruz-cov}
Apply \Cref{pfr-9-aux} and \Cref{ruz-cov} to get the result, as in the proof
of \Cref{pfr_aux}.
\end{proof}
```

How the parts fit. The parent `hom-pfr` is declared with its statement, Lean
name `homomorphism_pfr` and `\leanok` before any proof is written; the
`\uses{goursat, pfr-9-aux'}` line of its proof names its two direct
dependencies up front. The glue then runs a covering-and-counting argument:

```
hom-pfr ──uses──▶ goursat (hom_pfr.tex:11-17) ──uses──▶ hb-thm (hom_pfr.tex:5-9)
   │
   └──uses──▶ pfr-9-aux' (further_improvement.tex:363-373)
                  ├──uses──▶ pfr-9-aux (further_improvement.tex:352-360)
                  │               └──uses──▶ pfr-rho, rho-init, rho-subgroup
                  └──uses──▶ ruz-cov
```

- `pfr-9-aux'` is applied to the graph `A` with doubling constant `K = |S|`
  (since `A+A` is contained in `{ (x, f(x)+s) }`, of size `|S||A|`), supplying
  a subspace `H` with `|H|/|A| ∈ [|S|^{-8}, |S|^8]` and a covering set `c` with
  `A ⊆ c + H` and `|c| ≤ |S|^5 |A|^{1/2}/|H|^{1/2}`.
- `goursat` then factorises `H` into `H₀`, `H₁` and `φ` with
  `|H| = |H₀| |H₁|`; projecting `A ⊆ c + H` shows `G` is covered by at most
  `|c|` translates of `H₀`, hence `|c| |H₀| ≥ |G|`, hence
  `|H₁| ≤ |c| |H|/|A|`.
- the final calc squares the covering bound and divides by `|A|`:
  `|c| |H₁| ≤ |c|² |H|/|A| ≤ (|S|^5 |A|^{1/2}/|H|^{1/2})² |H|/|A| = |S|^{10}`,
  which is the claimed bound on the number of translates of
  `{ (x, φ(x)) }`.

Each child is a good leaf because it is a self-contained statement whose proof
closes on its own from named siblings, independent of the parent:
`goursat`'s proof closes from `hb-thm` (the Hahn–Banach extension lemma, proved
by induction in the same file) plus direct counting, and in Lean
(`PFR/HomPFR.lean:46-65`) by `obtain`/`use`/`constructor`;
`pfr-9-aux'`'s proof closes from `pfr-9-aux` and `ruz-cov`, and in Lean
(`PFR/RhoFunctional.lean:2003-2043`) from `better_PFR_conjecture_aux0` and
`Set.ruzsa_covering_add`. Neither leaf needs the parent's hypotheses.

## Why it is good

1. `goursat` occurs in the parent site `hom-pfr` (`\uses{goursat, pfr-9-aux'}`
   on line 25, `\Cref{goursat}` on line 33). Evidence kind: check (form
   `cites(hom-pfr, goursat)`).
2. `pfr-9-aux'` occurs in the parent site `hom-pfr` (`\uses{goursat,
   pfr-9-aux'}` on line 25, `\Cref{pfr-9-aux'}` on line 30). Evidence kind:
   check (form `cites(hom-pfr, pfr-9-aux')`).
3. `PFR/HomPFR.lean` lines 46-176 — the Lean proofs of the child `goursat`
   (46-65) and the parent `homomorphism_pfr` (75-176) — contain no `sorry`,
   `admit`, or `axiom`. Evidence kind: check (form
   `no_sorry(PFR/HomPFR.lean, 46-176)`).
4. The node is stated before proved and both are marked checked:
   `\lean{homomorphism_pfr}\leanok` on the theorem (line 19) and
   `\uses{goursat, pfr-9-aux'}\leanok` on the proof (line 25), the former before
   the proof body. Evidence kind: author-statement.
5. The theorem-scale shape is measurable: 2 direct lemmas, a parent site of 29
   lines, child sites of 7 and 11 lines, and a checked dependency chain of depth
   4 below the theorem (`pfr-9-aux'` → `pfr-9-aux` → `pfr-rho` →
   `phi-minimizer-zero-distance`). Evidence kind: measurement.

In my opinion the detail worth copying is the discipline of freezing two
independent named lemmas and then writing the proof as a calculation over
their outputs: the parent never constructs `H`, `H₀`, `H₁`, `φ` or `c` itself,
it only combines what the two leaves supply, which is exactly the skeleton
with lemma holes that a bounded prover fills.

The same two-node glue is reused: the sibling node `approx-hom-pfr`
([`blueprint/src/chapter/approx_hom_pfr.tex:62-97`](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/blueprint/src/chapter/approx_hom_pfr.tex#L62-L97))
runs the identical covering-and-counting argument with `\uses{goursat,
cs-bound, bsg, pfr-9-aux'}`, so `goursat` and `pfr-9-aux'` are reusable
dependencies, not one-offs (recorded under `known_uses`).

## When to use it, and when not

Use it when the result is the combination of two independent, already-stated
lemmas whose hypotheses line up into one chain — here a covering lemma
(`pfr-9-aux'`) supplying `H` and `c`, and a factorisation lemma (`goursat`)
supplying `H₀`, `H₁`, `φ`; when the statement can be frozen with a Lean name
and `\leanok` before the proof; and when the proof is a covering-and-counting
calculation over the graph of a function rather than a new construction.

Avoid it when the two lemmas' hypotheses do not line up into a single chain;
when a further lemma must be stated and proved (that belongs as its own node in
the graph); when the constants matter and any of them might change (the
exponent 10 is exactly twice the covering lemma's exponent 5, so the parent's
conclusion moves with it); or when the statement may still change (then do not
freeze the Lean name).

## Consequences

The glue's correctness rests on two hypotheses: that `pfr-9-aux'` supplies a
subspace `H` and a covering set `c` with the stated bounds (`A ⊆ c+H`,
`|c| ≤ K^5 |A|^{1/2}/|H|^{1/2}`, `|H|/|A| ∈ [K^{-8}, K^8]`), and that `goursat`
factorises `H` into `H₀`, `H₁` with `|H| = |H₀| |H₁|`. The final estimate
`|c| |H₁| ≤ |S|^{10}` squares the covering bound `|c| ≤ |S|^5
|A|^{1/2}/|H|^{1/2}` and divides by `|A|`, so the exponent 10 is exactly twice
the exponent 5; if that constant changes, the parent's conclusion changes with
it. The step "`G` is covered by at most `|c|` translates of `H₀`" uses that
`A ⊆ c+H` projects onto `G` as `c' + H₀`; it fails if the projection is not
surjective. In the blueprint, `\leanok` is a claim the project's build
verifies, not something the LaTeX text enforces, so a citation whose
hypotheses do not line up leaves a silent gap.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push.yml: job 'build' runs leanprover/lean-action (v1.2.0) which builds and lints the whole project on push to master (default branch), covering PFR/**/*.lean incl. PFR/HomPFR.lean; pinned commit 1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| provenance | pass | 4 file(s) byte-identical at 1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(hom-pfr, goursat) -> cites: goursat occurs at blueprint/src/chapter/hom_pfr.tex:25 | check_claims.py |
| 2 | verified | cites(hom-pfr, pfr-9-aux') -> cites: pfr-9-aux' occurs at blueprint/src/chapter/hom_pfr.tex:25 | check_claims.py |
| 3 | verified | no_sorry(PFR/HomPFR.lean, 46-176) -> no_sorry: none of sorry, admit, axiom in PFR/HomPFR.lean:46-176 | check_claims.py |
| 4 | verified | hom_pfr.tex:19 = '\begin{theorem}...\label{hom-pfr}\lean{homomorphism_pfr}\leanok'; hom_pfr.tex:25 = '\begin{proof}\uses{goursat, pfr-9-aux'}\leanok'. Stated (thm L19) before proved (proof L25), both marked \leanok. | verifier |
| 5 | verified | hom_pfr.tex:25 uses{goursat, pfr-9-aux'} = 2 labels; parent site hom_pfr.tex:19-47 = 29 lines (file is 47 lines, L47=end proof); goursat hom_pfr.tex:11-17 = 7 lines; pfr-9-aux' further_improvement.tex:363-373 = 11 lines (L363 label, L373 end proof); chain: L370 uses{pfr-9-aux,ruz-cov}, L358 uses{pfr-rho,...}, L346 uses{phi-min-exist,phi-minimizer-zero-distance,...}; all four nodes marked leanok (L363,352,341,320). | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent hom-pfr (hom_pfr.tex:19-47, 29 lines) is theorem homomorphism_pfr: \lean{homomorphism_pfr}\leanok at line 19, proof \uses{goursat, pfr-9-aux'} \leanok at line 25; its two direct children are exactly these two. Child goursat (hom_pfr.tex:11-17, 7 lines) closes via \uses{hb-thm} (line 16) and in Lean by obtain/use/constructor (HomPFR.lean:46-65). Child pfr-9-aux' (further_improvement.tex:363-373, 11 lines) closes via \uses{pfr-9-aux, ruz-cov} (line 370) and in Lean better_PFR_conjecture_aux (RhoFunctional.lean:2003-2043) via better_PFR_conjecture_aux0 + Set.ruzsa_covering_add. Shape numbers right: direct_lemmas=2, glue_lines=29, child_lines=[7,11], depth=4 chain pfr-9-aux'->pfr-9-aux(370)->pfr-rho(358)->phi-minimizer-zero-distance(346). No sorry/admit/axiom; all proofs close. Minor non-blocking: metrics.lean_parent_lines=102 cites 75-176 but HomPFR.lean has 175 lines (theorem is 75-175 = 101 lines). | reviewer-correctness |
| generality | accept | Generality is well-covered. (1) Applies beyond the example: use_when/avoid_when give general conditions (two independent already-stated lemmas whose hypotheses line up into one chain; statement freezable with a Lean name + \leanok; covering-and-counting calc over a function graph), and the sibling approx-hom-pfr reuses the identical glue (fetched raw: \uses{goursat, cs-bound, bsg, pfr-9-aux'}), so goursat/pfr-9-aux' are reusable, not one-offs. (2) 'When not to use' and consequences are honest and specific: exponent 10 = 2x the covering lemma's 5 is verifiable in the calc ((|S|^5 ...)^2 = |S|^10, hom_pfr.tex:50); the 'don't freeze the Lean name if the statement may change' caveat is apt; consequences name both hypotheses and honestly flag the projection-surjectivity step ('on taking projections G is covered by at most |c| translates of H0', and in Lean hG_cover/h_fstH) and the silent-gap risk of \leanok being build-checked, not LaTeX-enforced. (3) Good-leaves-for-a-bounded-prover is stated explicitly: each child is a self-contained statement closing from named siblings with none of the parent's hypotheses, and the parent never constructs H/H0/H1/phi/c but only combines the leaves' outputs, 'the skeleton with lemma holes that a bounded prover fills'. | reviewer-generality |
| provenance-licence | accept | check_provenance.py passes: 4 files byte-identical at commit 1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a. Commit is consistent across entry.json source.commit, all file/site/claim/known_uses permalinks, sources/pfr/SOURCE.md and source.json. Licence Apache-2.0 is consistent across entry.json, README header and Source-and-licence section, source.json, SOURCE.md, and the copied upstream-LICENSE (Apache License 2.0). Cited line ranges verified in local copies: hom_pfr.tex:19-47 (theorem homomorphism_pfr at 19, \uses{goursat,pfr-9-aux'}\leanok at 25), goursat hom_pfr.tex:11-17, pfr-9-aux' further_improvement.tex:363-373 (\uses{pfr-9-aux,ruz-cov} at 370). code/ contains exactly the 4 listed files. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/teorth/pfr at commit `1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a`, under `Apache-2.0`; see the [source note](../../sources/pfr/SOURCE.md) for the licence text and attribution.
