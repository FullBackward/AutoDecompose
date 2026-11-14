# Halting reduces to the game value: the MIP* = RE target assembled from four blueprint lemmas

| | |
|---|---|
| Kind | instance |
| Move | blueprint-node |
| Language | latex |
| Status | accepted |
| Source | [mipre-formalization](../../sources/mipre-formalization/SOURCE.md) at `5926bdff5db6` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T16:02:57Z |

## Intent

Prove the project's headline node `thm:main` — halting reduces to the synchronous
game value, the formalization target of MIP\* = RE — with a proof that is pure
glue: apply the conditional lemma `halting_reduces_to_gameValue_of` and discharge
its two inputs (a `GapCompression` and a universal machine) from four named
blueprint lemmas, one hole per stage of the pipeline.

## The decomposition

### parent `thm:main`: [`blueprint/src/content/07_main_theorem.tex` lines 12-34](https://github.com/vidick/mipre-formalization/blob/5926bdff5db621f44682a101007ef2fe3ae8d970/blueprint/src/content/07_main_theorem.tex#L12-L34) ([local copy](code/blueprint/src/content/07_main_theorem.tex))

```latex
\begin{theorem}[Halting reduces to the game value; Theorem 12.2 of~\cite{JNVWY20},
synchronous form]
\label{thm:main}
\uses{thm:halting,def:game-description,def:sync-value,def:re}
\lean{HaltingGameValue.halting_reduces_to_gameValue, HaltingGameValue.HaltingReducesToGameValue}
\leanok
There is a computable map $g$ from Turing machines to game descriptions such that for
every Turing machine $\machine$:
\begin{enumerate}
\item (\textbf{Completeness}) if $\machine$ halts on the empty input, then
  $\synval(\game_{g(\machine)}) = 1$;
\item (\textbf{Soundness}) if $\machine$ does not halt on the empty input, then
  $\synval(\game_{g(\machine)}) \leq \tfrac12$.
\end{enumerate}
\end{theorem}

\begin{proof}
\uses{thm:halting,cor:compression-from-answer-reduction,thm:answer-reduction}
\leanok
\texttt{MIPRE.Halting.halting\_reduces\_to\_gameValue\_of} takes a
\texttt{MIPRE.GapCompression} and a universal machine and concludes exactly this statement;
Theorem~\ref{thm:compression-target} supplies the compression.
\end{proof}
```

### child `thm:halting`: [`blueprint/src/content/06_proof_structure.tex` lines 7378-7425](https://github.com/vidick/mipre-formalization/blob/5926bdff5db621f44682a101007ef2fe3ae8d970/blueprint/src/content/06_proof_structure.tex#L7378-L7425) ([local copy](code/blueprint/src/content/06_proof_structure.tex))

```latex
\begin{theorem}[Halting reduction]
\label{thm:halting}
\ledgernode{1.6, 1.6.6}
\uses{thm:compression,lem:compressible-criterion,lem:value-lower-approx,lem:kleene,
  def:game-description,lem:sync-le-valstar,lem:dhalt-values,lem:lambda,def:mipstar,
  def:value-model,lem:class-sampler}
\lean{MIPRE.Halting.halting_reduction, MIPRE.Halting.halting_reduction_of,
  MIPRE.Halting.halting_reduction_lower, MIPRE.Halting.halting_reduction_lower_strings,
  MIPRE.Halting.halting_reduction_lower_of,
  MIPRE.Halting.exists_obligations, MIPRE.Halting.halting_reduces_to_gameValue_of,
  MIPRE.Halting.halting_reduction_both_of,
  MIPRE.Halting.halting_paper, MIPRE.Halting.halting_paper_valStar, MIPRE.Halting.Vpaper,
  MIPRE.Halting.semL, MIPRE.Halting.hasPerfectPCC_of_halts,
  MIPRE.Halting.valStar_le_of_not_halts,
  MIPRE.Halting.classV, MIPRE.Halting.classV_efficient, MIPRE.Halting.classV_value,
  MIPRE.Halting.classV_values, MIPRE.Halting.sampProg, MIPRE.Halting.decProg,
  MIPRE.Halting.sampProg_runs, MIPRE.Halting.decProg_accepts, MIPRE.Halting.decProg_runs,
  MIPRE.GapCompression.samplerFamily}
\leanok
Assume an ambient \texttt{MIPRE.GapCompression}. There is a computable map
$\machine \mapsto \game_{\machine}$ from Turing machines
to explicit synchronous game descriptions (Definition~\ref{def:game-description}),
such that:
\begin{enumerate}
\item if $\machine$ halts on the empty input then $\game_\machine$ has a value-$1$ PCC
  strategy, so $\synval(\game_\machine) = \valstar(\game_\machine) = 1$;
\item if $\machine$ does not halt on the empty input then
  $\valstar(\game_\machine) \leq \tfrac12$, and hence also
  $\synval(\game_\machine) \leq \tfrac12$ (Lemma~\ref{lem:sync-le-valstar}).
\end{enumerate}
Moreover the reduction is polynomial-time: for every polynomial-time map $z \mapsto
\machine_z$ from strings to machines there is a polynomial-time verifier in the sense of
Definition~\ref{def:mipstar}, efficient on every input, whose game on $z$ has a value-$1$ PCC
strategy if $\machine_z$ halts on the empty input and quantum value at most $\tfrac12$ if it
does not.
\end{theorem}

\begin{proof}
\uses{lem:halting-semidecider,lem:mipstar-sub-re}
\leanok
\texttt{MIPRE.Halting.halting\_reduction\_of} in $\valstar$ and
\texttt{halting\_reduces\_to\_gameValue\_of} in $\synval$, from
Theorem~\ref{thm:compression} as a \texttt{GapCompression}: Lemma~\ref{lem:compressible-criterion}
at the classes of Remark~\ref{rem:compression-abstract}, whose four obligations are the
theorems named below, the last through \texttt{exists\_obligations}. This proves
computability of the explicit tabulation. It does not assert polynomial-time
enumeration of that table.
\end{proof}
```

### child `cor:compression-from-answer-reduction`: [`blueprint/src/content/06_proof_structure.tex` lines 6404-6429](https://github.com/vidick/mipre-formalization/blob/5926bdff5db621f44682a101007ef2fe3ae8d970/blueprint/src/content/06_proof_structure.tex#L6404-L6429) ([local copy](code/blueprint/src/content/06_proof_structure.tex))

```latex
\begin{corollary}[Compression, and $\MIPstar = \RE$, from answer reduction alone]
\label{cor:compression-from-answer-reduction}
\uses{thm:compression,lem:introspection-supply,thm:parallel-repetition,lem:universal-tm}
\lean{MIPRE.GapCompression.ofAnswerReduction,
  MIPRE.Halting.halting_reduces_to_gameValue_of_answerReduction,
  MIPRE.Halting.halting_reduction_quantum_of_answerReduction,
  MIPRE.Halting.gameValue_uncomputable_of_answerReduction,
  MIPRE.Halting.quantumValue_uncomputable_of_answerReduction,
  MIPRE.Halting.re_subset_mipstarComputable_of_answerReduction,
  MIPRE.Halting.mipstarComputable_eq_re_of_answerReduction}
\leanok
From an inhabitant of \texttt{MIPRE.AnswerReduction 5} alone there is a
\texttt{MIPRE.GapCompression}, and consequently Theorem~\ref{thm:main},
Corollary~\ref{cor:main-quantum}, Corollary~\ref{cor:value-uncomputable} and
Theorem~\ref{thm:mipstar-eq-re} hold with no other hypothesis.
\end{corollary}

\begin{proof}
\uses{cor:halting-consequences}
\leanok
Theorem~\ref{thm:compression} applied to the introspection instance of
Lemma~\ref{lem:introspection-supply}, the given answer reduction, and the repetition
construction of Theorem~\ref{thm:parallel-repetition}; the universal machine is the one of
Lemma~\ref{lem:universal-tm}. The chapter~7 results are then their conditional forms at this
compression.
\end{proof}
```

### child `thm:answer-reduction`: [`blueprint/src/content/06_proof_structure.tex` lines 6032-6063](https://github.com/vidick/mipre-formalization/blob/5926bdff5db621f44682a101007ef2fe3ae8d970/blueprint/src/content/06_proof_structure.tex#L6032-L6063) ([local copy](code/blueprint/src/content/06_proof_structure.tex))

```latex
\begin{theorem}[Answer reduction]
\label{thm:answer-reduction}
\ledgernode{1.3, 1.3.4}
\uses{def:normal-verifier,def:pcc,lem:ar-construction,lem:ar-completeness,lem:ar-error-assembly}
\lean{MIPRE.AnswerReduction.answerReduction}
\leanok
In the source model there is a polynomial-time Turing machine $\ComputeAnsVerifier$ that on input
$(\verifier, \lambda, \ell, \mu, \sigma)$, for $\verifier$ an $\ell$-level normal form
verifier whose decider is in standard timeout-counter form, with
$\abs{\decider} \leq \sigma$, $\TIME_\sampler(n) \leq (\lambda n)^\mu$
and $\TIME_\decider(n) \leq (2^{\lambda n})^\mu$ for $n \geq 2$, outputs a
$\max\{\ell + 2, 5\}$-level normal form verifier $\vans$ whose decider is in standard
timeout-counter form with $B_{\dans}(n)=\poly(\sigma,(\lambda n)^\mu)$, with
$\TIME_{\sans}(n), \TIME_{\dans}(n) = \poly\bigl( (\lambda n)^\mu, \sigma \bigr)$,
whose sampler depends only on $(\sampler, \lambda, \ell, \mu, \sigma)$, and such that for
some $\delta(\eps, n) = \sigma^a \bigl( (\lambda n)^{\mu a} \eps^b + (\lambda
n)^{-\mu b} \bigr)$ (universal constants $a, b$) and a universal constant
$C_{\mathrm{ar}}$, for all $n \geq C_{\mathrm{ar}}$:
\begin{enumerate}
\item (\textbf{Completeness}) If $\verifier_n$ has a value-$1$ PCC strategy
  then $\vans_n$ has a value-$1$ PCC strategy.
\item (\textbf{Soundness}) If $\valstar(\vans_n) > 1 - \eps$ then
  $\valstar(\verifier_n) \geq 1 - \delta(\eps, n)$.
\end{enumerate}
\end{theorem}

\begin{proof}
\uses{lem:answer-reduction-supply,def:answer-reduction-contract,lem:pcp-complexity}
\leanok
In the ambient form of Definition~\ref{def:answer-reduction-contract}, at $\ell=5$, this is
Lemma~\ref{lem:answer-reduction-supply}.
\end{proof}
```

### child `thm:compression-target`: [`blueprint/src/content/06_proof_structure.tex` lines 6388-6402](https://github.com/vidick/mipre-formalization/blob/5926bdff5db621f44682a101007ef2fe3ae8d970/blueprint/src/content/06_proof_structure.tex#L6388-L6402) ([local copy](code/blueprint/src/content/06_proof_structure.tex))

```latex
\begin{theorem}[Ambient compression inhabitation target]
\label{thm:compression-target}
\uses{lem:introspection-supply,lem:answer-reduction-supply,thm:compression,thm:answer-reduction}
\lean{MIPRE.gapCompression}
\leanok
The type \texttt{MIPRE.GapCompression} is inhabited.
\end{theorem}

\begin{proof}
\uses{cor:compression-from-answer-reduction,lem:answer-reduction-supply}
\leanok
Corollary~\ref{cor:compression-from-answer-reduction} at the answer reduction of
Lemma~\ref{lem:answer-reduction-supply}: Theorem~\ref{thm:compression} applied to the three
supplied stages.
\end{proof}
```

### context `MainTheorem-lean`: [`MIPRE/MainTheorem.lean` lines 28-38](https://github.com/vidick/mipre-formalization/blob/5926bdff5db621f44682a101007ef2fe3ae8d970/MIPRE/MainTheorem.lean#L28-L38) ([local copy](code/MIPRE/MainTheorem.lean))

```lean
/-- **Gap-preserving compression** (blueprint `thm:compression-target`), inhabited. -/
noncomputable def MIPRE.gapCompression : MIPRE.GapCompression :=
  MIPRE.GapCompression.ofAnswerReduction MIPRE.AnswerReduction.answerReduction

namespace HaltingGameValue

/-- **Theorem 12.2 of "MIP* = RE"** (blueprint `thm:main`): halting reduces to the synchronous
game value. -/
theorem halting_reduces_to_gameValue : HaltingReducesToGameValue :=
  MIPRE.Halting.halting_reduces_to_gameValue_of_answerReduction
    MIPRE.AnswerReduction.answerReduction
```

How the parts fit. The parent theorem `thm:main` states the headline result: a
computable map from Turing machines to game descriptions with a completeness
clause (value 1 when the machine halts) and a soundness clause (value at most
1/2 when it does not). Its proof (the glue, lines 28-34) does no mathematics: it
names the conditional lemma `halting_reduces_to_gameValue_of`, which concludes
"exactly this statement" once it is given a `MIPRE.GapCompression` and a
universal machine, and then says where those two inputs come from:
`thm:compression-target` supplies the compression. The three lemmas the proof
declares in its `\uses{}` are `thm:halting` (the conditional reduction), and the
two lemmas that build the compression from its stages:
`cor:compression-from-answer-reduction` and `thm:answer-reduction`.

The lemma graph (arrows = "cites in its `\uses{}` or proof body"):

```
thm:main  (parent; proof applies halting_reduces_to_gameValue_of)
├─ thm:halting          ← the conditional reduction, from a GapCompression
│     └─ thm:compression ── thm:parallel-repetition
│        └─ (via lem:compressible-criterion; four obligations via exists_obligations)
├─ thm:answer-reduction ← one stage: answer-reduced verifier
│     └─ lem:answer-reduction-supply (via def:answer-reduction-contract)
├─ cor:compression-from-answer-reduction  ← assembles the stages
│     ├─ thm:compression
│     ├─ lem:introspection-supply
│     ├─ thm:parallel-repetition
│     └─ lem:universal-tm
└─ thm:compression-target  ← inhabits GapCompression, removing the hypothesis
      └─ cor:compression-from-answer-reduction, lem:answer-reduction-supply
```

Each child is a good leaf because it is a self-contained named statement whose
own proof closes from named siblings, independent of the parent:

- `thm:halting` is the reduction itself, stated under the single ambient
  hypothesis `MIPRE.GapCompression`; its proof derives the two readings of the
  reduction from `thm:compression` through `lem:compressible-criterion`, so it
  closes as soon as a compression exists.
- `thm:answer-reduction` is the answer-reduction stage, closed by the supplied
  instance `lem:answer-reduction-supply` in the ambient contract; it does not
  mention the other stages.
- `cor:compression-from-answer-reduction` is the assembly step: it takes the
  three stage instances (introspection via `lem:introspection-supply`, answer
  reduction, repetition via `thm:parallel-repetition`) plus the universal
  machine `lem:universal-tm` and returns a `GapCompression`, closing from
  `thm:compression`.
- `thm:compression-target` is the inhabitation that deletes the last hypothesis;
  its proof is the one-line instantiation of
  `cor:compression-from-answer-reduction` at `lem:answer-reduction-supply`.

The context excerpt (`MIPRE/MainTheorem.lean` lines 28-38) shows the Lean
counterpart: both `thm:compression-target` (`MIPRE.gapCompression`) and
`thm:main` (`halting_reduces_to_gameValue`) are one-line applications of
`..._of_answerReduction AnswerReduction.answerReduction`, so the node is not
just stated but proved, and the glue in Lean is exactly as thin as the blueprint
glue.

## Why it is good

1. The proof of `thm:main` names `thm:compression-target` (`check`, lines 12-34).
2. The proof of `thm:main` cites `thm:answer-reduction` (`check`, lines 12-34).
3. The shape is front-loaded: a 23-line glue sits over four children of 48, 26,
   32 and 15 lines (121 lines of lemma under a 23-line glue), and the longest
   chain below `thm:main` is 4 project lemmas deep (`measurement`, site line
   counts plus the `\uses{}` chain in `06_proof_structure.tex`).
4. The authors describe `thm:main` as "the formalization target of the whole
   project" and record that the proof is the conditional
   `halting_reduces_to_gameValue_of` at the compression of
   `thm:compression-target` (`author-statement`, lines 4 and 36-44).
5. The same assemble-from-named-lemmas move proves the chapter's other headline
   node `thm:mipstar-eq-re`, whose proof is also a list of citations
   (`known-use`, lines 183-220).

In my opinion the detail worth copying is that the glue is a *type-directed
instantiation*, not an argument: the conditional lemma's two inputs (a
compression, a universal machine) are each handed to a named child, so the proof
of the headline theorem is exactly "fill the two holes". That is the shape a
bounded-prover decomposition wants, and here the blueprint and the Lean proof
agree on it line for line.

## When to use it, and when not

Use it when the goal is a headline theorem of the form "there is a computable
map with a completeness clause and a soundness clause", and its proof is the
instantiation of a conditional lemma at a named supply of that lemma's
hypothesis (here `GapCompression`). The shape is right when the theorem is a
node of a published dependency graph (`\uses{}` in the blueprint) and each named
dependency is itself a node with its own proof, so the glue is a list of
citations and the difficulty is distributed one hole per bounded prover. Avoid
it when the glue itself must do mathematics (prove a property rather than cite
a lemma), or when the dependencies are not named statements, so the
one-hole-per-lemma shape does not arise.

## Consequences

The glue creates no proof obligation of its own beyond the citations: it
inherits the inputs of the cited conditional lemma (a `GapCompression`,
discharged by `thm:compression-target`, and a universal machine, discharged
inside the compression assembly). Because every node here is `\leanok` and the
Lean proof is a one-line application, a wrong or too-weak child would surface as
a type error rather than a silent gap; but the node's own proof defers all
difficulty to the children, each of which is itself a large node with its own
`\uses{}` cone. The assembly records a fixed choice of stages (introspection,
the classical-PCP answer reduction, repetition, the self-universal machine), so
changing any stage changes the cited supply, not the glue.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/blueprint.yml compiles the blueprint via docgen-action (blueprint: true) on push to main, which builds blueprint/src/content/07_main_theorem.tex; pinned commit 5926bdff5db621f44682a101007ef2fe3ae8d970 is head of default branch main | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| provenance | pass | 3 file(s) byte-identical at 5926bdff5db621f44682a101007ef2fe3ae8d970 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(thm:main, thm:compression-target) -> cites: thm:compression-target occurs at blueprint/src/content/07_main_theorem.tex:33 | check_claims.py |
| 2 | verified | cites(thm:main, thm:answer-reduction) -> cites: thm:answer-reduction occurs at blueprint/src/content/07_main_theorem.tex:29 | check_claims.py |
| 3 | verified | line counts: parent L12-L34=23, thm:halting L7378-L7425=48, cor:compression-from-answer-reduction L6404-L6429=26, thm:answer-reduction L6032-L6063=32, thm:compression-target L6388-L6402=15 (sum 121), all match entry sites; depth chain verified by reading 06_proof_structure.tex: thm:compression-target label L6389 proof \uses cor:compression-from-answer-reduction at L6397; cor proof cites thm:compression at L6424; thm:compression label L6282 \uses thm:parallel-repetition at L6284; thm:parallel-repetition label L6184 = 4 lemmas | verifier |
| 4 | verified | 07_main_theorem.tex L4 = 'The statement below is the formalization target of the whole project. It matches,'; L36-L44 Status remark (L41-L42) = 'it is the conditional MIPRE.Halting.halting_reduces_to_gameValue_of at the compression of Theorem~\ref{thm:compression-target}' | verifier |
| 5 | verified | 07_main_theorem.tex L183-L220: thm:mipstar-eq-re at L184; its proof \uses{cor:compression-from-answer-reduction,thm:answer-reduction} at L198 (claim cites L197, off by one); body cites thm:halting-undecidable at L201 and lem:mipstar-sub-re at L205 | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent site 07_main_theorem.tex L12-34 is 23 lines and matches the entry excerpt verbatim; its proof \uses (L29) = {thm:halting,cor:compression-from-answer-reduction,thm:answer-reduction} and the body L33 cites thm:compression-target, so exactly the four listed children are the lemmas the glue uses (direct_lemmas=4 correct). Child sites and counts match the code: thm:halting L7378-7425 (48), cor:compression-from-answer-reduction L6404-6429 (26), thm:answer-reduction L6032-6063 (32), thm:compression-target L6388-6402 (15). Each closed_by matches its proof body: thm:halting from thm:compression via lem:compressible-criterion + exists_obligations (L7418-7424); cor:compression-from-answer-reduction from thm:compression/lem:introspection-supply/thm:parallel-repetition/lem:universal-tm (+cor:halting-consequences); thm:answer-reduction = lem:answer-reduction-supply at the answer-reduction-contract; thm:compression-target = cor:compression-from-answer-reduction at lem:answer-reduction-supply (L6399-6401). Shape numbers verified: glue 23, child_lines [48,26,32,15], depth 4 via compression-target L6389 -> cor:compression L6397 -> thm:compression L6282(cited L6424) -> thm:parallel-repetition L6184(in thm:compression \uses L6284). Lean context MainTheorem.lean L28-38 shows one-line proofs (MIPRE.gapCompression, halting_reduces_to_gameValue), so the node closes with no hypothesis. Author-statement (L4, L36-44) and known-use (thm:mipstar-eq-re L183-220, proof \uses L197) check out. | reviewer-correctness |
| generality | accept | Generality holds. The move is stated beyond the example: use_when = a node of a published dependency graph (blueprint \uses{}) whose named dependencies are themselves nodes with their own proofs, so the glue is a list of citations and the difficulty is one hole per child; avoid_when = glue carries real mathematical content to prove, or dependencies are not named statements. Consequences are honest and specific: glue creates no obligation beyond citations, a weak child surfaces as a type error, and it honestly notes each child is itself a large node with its own \uses{} cone and that the fixed stage choice makes the assembly brittle. The leaf property is stated explicitly (README L237-254): each child is a self-contained named statement whose proof closes from named siblings independent of the parent, with per-child closure (one-line instantiation, no mention of sibling stages). Evidence for the generality narrative checks out: claim 4 (07_main_theorem.tex L4 'formalization target of the whole project'; L36-44 the proof is the conditional halting_reduces_to_gameValue_of at thm:compression-target) and claim 5 (L197 proof \uses{} {cor:compression-from-answer-reduction,thm:answer-reduction} for thm:mipstar-eq-re) both say what is claimed. | reviewer-generality |
| provenance-licence | accept | Commit 5926bdff5db621f44682a101007ef2fe3ae8d970 is consistent across entry.json, README.md, source.json and SOURCE.md; every permalink (files and sites) pins that same commit on github.com/vidick/mipre-formalization. Licence recorded as Apache-2.0 in all four places, and sources/mipre-formalization/upstream-LICENSE is the verbatim Apache 2.0 text. check_provenance.py reports pass: 3 files byte-identical at the pinned commit; entry.json bytes match the local copies (13560/445887/3829). Spot-checked the cited line anchors in the local copies (07_main_theorem.tex 12-34, 06_proof_structure.tex 6032-6063/6388-6429/7378-7425, MainTheorem.lean 28-38) and each resolves to the labelled node the entry claims. Source note records commit, licence, LICENSE file and attribution. All traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/vidick/mipre-formalization at commit `5926bdff5db621f44682a101007ef2fe3ae8d970`, under `Apache-2.0`; see the [source note](../../sources/mipre-formalization/SOURCE.md) for the licence text and attribution.
