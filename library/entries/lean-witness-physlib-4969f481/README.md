# Witness d = 𝑅ᵣ∞ ρ for the generalized quantum Stein's lemma (Theorem 4)

| | |
|---|---|
| Kind | instance |
| Move | witness |
| Language | lean |
| Status | accepted |
| Source | [physlib](../../sources/physlib/SOURCE.md) at `ca577bfd34ef` |
| Licence | `Apache-2.0` |

## Intent

This decomposition closes the file's headline theorem, Theorem 4 (the
generalized quantum Stein's lemma of Hayashi & Yamasaki), stated as the
existence of one number to which both the hypothesis-testing rate and the
regularized relative entropy of resource converge. The glue names the witness
`d := 𝑅ᵣ∞ ρ` and discharges the two convergences of the conjunction with two
named project lemmas that already prove them.

## The decomposition

### parent `limit_hypotesting_eq_limit_rel_entropy`: [`QuantumInfo/ResourceTheory/SteinsLemma.lean` lines 2114-2123](https://github.com/leanprover-community/physlib/blob/ca577bfd34ef356be2595528da1ef13a4a405816/QuantumInfo/ResourceTheory/SteinsLemma.lean#L2114-L2123) ([local copy](code/QuantumInfo/ResourceTheory/SteinsLemma.lean))

```lean
theorem limit_hypotesting_eq_limit_rel_entropy (ρ : MState (H i)) (ε : Prob) (hε : 0 < ε ∧ ε < 1) :
    ∃ d : ℝ≥0,
      Filter.atTop.Tendsto (fun n ↦ —log β_ ε(ρ ⊗ᵣ^[n]‖IsFree) / n) (𝓝 d)
      ∧
      Filter.atTop.Tendsto (fun n ↦ (⨅ σ ∈ IsFree, 𝐃(ρ ⊗ᵣ^[n]‖σ)) / n) (𝓝 d)
      := by
  use 𝑅ᵣ∞ ρ -- Regularized relative entropy of resource (RegularizedRelativeEntResource) as an NNReal
  constructor
  · exact GeneralizedQSteinsLemma ρ hε -- Theorem 1 in Hayashi & Yamasaki
  · exact RelativeEntResource.tendsto_ennreal ρ -- The regularized relative entropy of resource is not infinity
```

### child `GeneralizedQSteinsLemma`: [`QuantumInfo/ResourceTheory/SteinsLemma.lean` lines 1980-1981](https://github.com/leanprover-community/physlib/blob/ca577bfd34ef356be2595528da1ef13a4a405816/QuantumInfo/ResourceTheory/SteinsLemma.lean#L1980-L1981) ([local copy](code/QuantumInfo/ResourceTheory/SteinsLemma.lean))

```lean
theorem GeneralizedQSteinsLemma {i : ι} (ρ : MState (H i)) {ε : Prob} (hε : 0 < ε ∧ ε < 1) :
    Filter.atTop.Tendsto (fun n ↦ —log β_ ε(ρ ⊗ᵣ^[n]‖IsFree) / n) (𝓝 (𝑅ᵣ∞ ρ)) := by
```

### child `RelativeEntResource.tendsto_ennreal`: [`QuantumInfo/ResourceTheory/FreeState.lean` lines 481-488](https://github.com/leanprover-community/physlib/blob/ca577bfd34ef356be2595528da1ef13a4a405816/QuantumInfo/ResourceTheory/FreeState.lean#L481-L488) ([local copy](code/QuantumInfo/ResourceTheory/FreeState.lean))

```lean
theorem RelativeEntResource.tendsto_ennreal (ρ : MState (H i)) :
    Filter.atTop.Tendsto (fun n ↦ (⨅ σ ∈ IsFree, 𝐃(ρ ⊗ᵣ^[n]‖σ)) / ↑n) (𝓝 (𝑅ᵣ∞ ρ)) := by
  refine Filter.Tendsto.congr' ?_ (ENNReal.tendsto_coe.mpr <| RelativeEntResource.tendsto ρ)
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  use 1; intros
  rw [RelativeEntResource, ENNReal.coe_div (by positivity), ENNReal.coe_natCast]
  congr
  apply WithTop.coe_untop
```

### context `theorem4-doc`: [`QuantumInfo/ResourceTheory/SteinsLemma.lean` lines 2110-2113](https://github.com/leanprover-community/physlib/blob/ca577bfd34ef356be2595528da1ef13a4a405816/QuantumInfo/ResourceTheory/SteinsLemma.lean#L2110-L2113) ([local copy](code/QuantumInfo/ResourceTheory/SteinsLemma.lean))

```lean
/-- Theorem 4, which is also called the Generalized quantum Stein's lemma in Hayashi & Yamasaki.
What they state as an equality of limits, which don't exist per se in Mathlib, we state as the existence
of a number (which happens to be `RegularizedRelativeEntResource`) to which both sides converge.
-/
```

How the parts fit. The parent is an `∃ d : ℝ≥0, P d ∧ Q d` goal. Its
proof is five lines of glue:

1. `use 𝑅ᵣ∞ ρ` introduces the witness `d := 𝑅ᵣ∞ ρ` — the regularized relative
   entropy of resource, defined in `FreeState.lean` lines 461-468;
2. `constructor` splits the conjunction into its two convergences;
3. `· exact GeneralizedQSteinsLemma ρ hε` closes the first convergence — the
   hypothesis-testing rate tends to `𝑅ᵣ∞ ρ` — by Theorem 1, proved above in the
   same file;
4. `· exact RelativeEntResource.tendsto_ennreal ρ` closes the second
   convergence — `(⨅ σ ∈ IsFree, 𝐃(ρ ⊗ᵣ^[n]‖σ)) / n` tends to `𝑅ᵣ∞ ρ` — by the
   project's "alternate version of Lemma 5" in `FreeState.lean`.

Lemma graph (`→` reads "is cited by"; the two direct children are marked):

```
limit_hypotesting_eq_limit_rel_entropy (2114-2123)
├─→ GeneralizedQSteinsLemma (1980-2108)                                  [child]
│    ├─→ Lemma7_improver (1953-1961)  ──→ Lemma7 (1752-1948)
│    ├─→ Lemma7_gap (1964-1974)       ──→ Lemma7 (1752-1948)  ──→ EquationS62 (1093)
│    └─→ Lemma6 (46-180), Lemma6_σn_IsFree (34-40), RelativeEntResource.tendsto_ennreal
└─→ RelativeEntResource.tendsto_ennreal (FreeState.lean 481-488)          [child]
     └─→ RelativeEntResource.tendsto (FreeState.lean 471-477)
          └─→ RelativeEntResource.Subadditive (FreeState.lean 441-459)
```

Each child is a good leaf: a self-contained statement whose proof closes on
its own or from named siblings.

- `GeneralizedQSteinsLemma` is exactly the first conjunct with `d`
  instantiated to `𝑅ᵣ∞ ρ`. Its proof (`tendsto_of_le_liminf_of_limsup_le`)
  splits into a "key part" closed through the `Lemma7_improver`/`Lemma7_gap`
  pair and a "strong converse" closed through `Lemma6`; all of these are named
  siblings in the same file.
- `RelativeEntResource.tendsto_ennreal` is exactly the second conjunct with
  `d = 𝑅ᵣ∞ ρ`. It closes in one line, `Filter.Tendsto.congr'` against its named
  sibling `RelativeEntResource.tendsto` (Lemma 5), which itself closes from
  `RelativeEntResource.Subadditive`.

The context excerpt is the doc comment immediately above the theorem, which
explains why the goal is an existence of a number rather than the paper's
equality of two limits.

## Why it is good

1. The parent site cites `GeneralizedQSteinsLemma` (line 2122) — the first
   conjunct of the conjunction is discharged by the named child. (*check*)
2. The parent site cites `RelativeEntResource.tendsto_ennreal` (line 2123) —
   the second conjunct is discharged by the named child. (*check*)
3. No `sorry`/`admit`/`axiom` occurs in the parent and first-child range
   `SteinsLemma.lean` lines 1980-2123. (*check*)
4. The witness move closes the parent in 5 lines of proof (2119-2123: one
   `use`, one `constructor`, one `exact` per conjunct) from two named project
   lemmas whose proofs are 129 lines (`GeneralizedQSteinsLemma`, 1980-2108)
   and 8 lines (`RelativeEntResource.tendsto_ennreal`, FreeState.lean
   481-488); the checked lemma chain below the parent is 4 deep
   (`limit_hypotesting_eq_limit_rel_entropy → GeneralizedQSteinsLemma →
   Lemma7_gap → Lemma7 → EquationS62`). (*measurement*)
5. The authors say why the goal is an existence statement rather than an
   equality of limits, which is exactly what licenses the witness move: "What
   they state as an equality of limits, which don't exist per se in Mathlib, we
   state as the existence of a number (which happens to be
   `RegularizedRelativeEntResource`) to which both sides converge." (doc
   comment, lines 2110-2113). (*author-statement*)

In my opinion the detail worth copying is that the `use` supplies not an
arbitrary placeholder but the actual value `𝑅ᵣ∞ ρ` that both lemmas already
converge to, so the conjunction closes by two bare `exact`s with no arithmetic
left in the glue.

## When to use it, and when not

Use it when a goal is `∃ d, P d ∧ Q d` (or more generally `∃ x, P₁ x ∧ … ∧
Pₙ x`) and each conjunct is already a named lemma about the same concrete
candidate, so the only remaining work is to exhibit the witness and conjoin
the facts. It is the natural decomposition for a "two sides converge to one
number" headline where each side's convergence is its own theorem.

Avoid it when the common limit is not a concrete term (then there is nothing
to `use`, and the existence has to come from completeness or a compactness
argument); when the two limits are not yet known to coincide (then the real
work is the equality of limits, not the witness); or when a conjunct must be
proved from scratch, since the witness move only relocates that burden into a
child it does not itself provide.

## Consequences

The `use` commits to one witness and `constructor` creates the two conjuncts
as obligations, each discharged by a lemma that must prove convergence to
exactly that `d`; a lemma that converges to a different spelling of the same
limit needs a `convert`/`congr`. There is no exhaustiveness obligation (that
belongs to case-split) and no induction. The honesty of the move rests
entirely on the two child lemmas being closed and about the same limit; if the
second conjunct (the `⨅ σ ∈ IsFree, 𝐃(ρ ⊗ᵣ^[n]‖σ) / n` side) were unproved,
the witness move would reduce the theorem to a still-hard child rather than
close it.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml (triggered on push to master) runs 'lake build -KCI --iofail', which builds the default targets Physlib and QuantumInfo (lakefile.toml defaultTargets = [Physlib, QuantumInfo]); QuantumInfo/ResourceTheory/SteinsLemma.lean lives in the QuantumInfo package. Pinned commit ca577bfd34ef356be2595528da1ef13a4a405816 is on the default branch master (compare ca577bfd...master: ahead 1, behind 0, so it is an ancestor of the master tip a11dadd3). | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: GeneralizedQSteinsLemma@QuantumInfo/ResourceTheory/SteinsLemma.lean:2122, RelativeEntResource.tendsto_ennreal@QuantumInfo/ResourceTheory/SteinsLemma.lean:2123; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at ca577bfd34ef356be2595528da1ef13a4a405816 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, GeneralizedQSteinsLemma) -> cites: GeneralizedQSteinsLemma occurs at QuantumInfo/ResourceTheory/SteinsLemma.lean:2122 | check_claims.py |
| 2 | verified | cites(parent, RelativeEntResource.tendsto_ennreal) -> cites: RelativeEntResource.tendsto_ennreal occurs at QuantumInfo/ResourceTheory/SteinsLemma.lean:2123 | check_claims.py |
| 3 | verified | no_sorry(QuantumInfo/ResourceTheory/SteinsLemma.lean, 1980-2123) -> no_sorry: none of sorry, admit, axiom in QuantumInfo/ResourceTheory/SteinsLemma.lean:1980-2123 | check_claims.py |
| 4 | verified | Read copied SteinsLemma.lean and FreeState.lean. Parent by-block is 5 lines (2119 ':= by', 2120 'use 𝑅ᵣ∞ ρ', 2121 'constructor', 2122 'exact GeneralizedQSteinsLemma ρ hε', 2123 'exact RelativeEntResource.tendsto_ennreal ρ') = one use, one constructor, one exact per conjunct. GeneralizedQSteinsLemma declaration at 1980, proof ends 2108 ('apply iInf_subtype'''), span 1980-2108 = 129 lines. RelativeEntResource.tendsto_ennreal declaration at 480, site 481-488 = 8 lines. Chain citations: 2122 parent->GeneralizedQSteinsLemma, 2032 'grw [Lemma7_gap ...]' inside GeneralizedQSteinsLemma, 1971 'exact (SteinsLemma.Lemma7 ...).choose_spec' inside Lemma7_gap (declared 1964), 1948 'exact EquationS62 ...' inside Lemma7 (declared 1752) = 4 edges deep. | verifier |
| 5 | verified | Read doc comment at SteinsLemma.lean 2110-2113. Lines 2111-2112 read verbatim: "What they state as an equality of limits, which don't exist per se in Mathlib, we state as the existence of a number (which happens to be RegularizedRelativeEntResource) to which both sides converge." — matches the claim quote exactly; the paraphrase (existence of one number rather than equality of limits) is faithful. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent is '∃ d : ℝ≥0, P d ∧ Q d' (SteinsLemma.lean 2114-2123); glue is exactly 'use 𝑅ᵣ∞ ρ; constructor; · exact GeneralizedQSteinsLemma ρ hε; · exact RelativeEntResource.tendsto_ennreal ρ'. Children are exactly the two lemmas cited: GeneralizedQSteinsLemma (1980-1981) = first conjunct with d:=𝑅ᵣ∞ ρ, closing via tendsto_of_le_liminf_of_limsup_le with Lemma7_improver/Lemma7_gap (key part, lines 2029-2032) and Lemma6 (strong converse, line 2083); RelativeEntResource.tendsto_ennreal (FreeState.lean 481-488) = second conjunct with d:=𝑅ᵣ∞ ρ, closing via Filter.Tendsto.congr' with RelativeEntResource.tendsto (471-477, which rests on Subadditive 441-459). No sorry/admit/axiom in 1980-2123. Shape numbers correct: direct_lemmas=2, glue_lines=10 (site 2114-2123), child_lines=[2,8] (1980-1981, 481-488); depth=4 chain limit_hypotesting_eq_limit_rel_entropy→GeneralizedQSteinsLemma→Lemma7_gap→Lemma7→EquationS62 confirmed at citations 2122, 2032, 1971, 1948. Minor nit only: metrics.glue_body_lines=5 counts the ':= by' line (2119) among proof lines; actual commands are 4 (2120-2123), but the range is explicit and does not affect the shape numbers. | reviewer-correctness |
| generality | accept | Move is stated generally (∃ x, P₁ x ∧ … ∧ Pₙ x with each conjunct already a named lemma about the same concrete candidate; the 'two sides converge to one number' pattern). 'When not to use' gives three specific honest cases (no concrete term -> completeness, limits not yet coincident -> equality is the work, conjunct from scratch -> burden relocated not closed). Consequences are specific and borne out by the example (convert/congr for a different spelling; the second child literally bridges /n vs /↑n via Tendsto.congr' and congr). Leaves are described as self-contained statements exactly matching a conjunct that close from named siblings (tendsto_of_le_liminf_of_limsup_le, Lemma7_improver/Lemma7_gap/Lemma6, RelativeEntResource.tendsto), which I confirmed in the copied code. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit (ca577bfd34ef356be2595528da1ef13a4a405816), licence (Apache-2.0) and source note are mutually consistent and traceable: check_provenance passes (2 files byte-identical at the pinned commit); sha256 in entry.json matches the copied SteinsLemma.lean and FreeState.lean exactly; the upstream-LICENSE is the Apache 2.0 text; source.json and SOURCE.md pin the same commit and licence; and each cited line range (SteinsLemma.lean 2110-2123, 1980-1981; FreeState.lean 481-488) matches the copied file content and the README excerpts. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover-community/physlib at commit `ca577bfd34ef356be2595528da1ef13a4a405816`, under `Apache-2.0`; see the [source note](../../sources/physlib/SOURCE.md) for the licence text and attribution.
