# Comparator-boundary adapter for whole-space R3 Theorem 1.1

| | |
|---|---|
| Kind | instance |
| Move | interface-lemma |
| Language | lean |
| Status | draft |
| Source | [navierstokesandeuler](../../sources/navierstokesandeuler/SOURCE.md) at `f9e8bc5b38b6` |
| Licence | `Apache-2.0` |

## Intent

Re-expose the project's internal whole-space Theorem 1.1 under the reference
Comparator's exact quantifiers and decay predicates, so a comparator client
calls `navier_stokes_breakdown_R3` and never unfolds the internal
`ProblemStatement`. The parent is an `interface-lemma`: its proof is two lines
of plumbing between two named lemmas, and it is the file's "full whole-space
theorem implies option (C)" result.

## The decomposition

### parent `navier_stokes_breakdown_R3`: [`NavierStokes/ComparatorR3Theorem.lean` lines 38-44](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/ComparatorR3Theorem.lean#L38-L44) ([local copy](code/NavierStokes/ComparatorR3Theorem.lean))

```lean
theorem navier_stokes_breakdown_R3 (ν : ℝ) (hν : ν > 0) :
    ∃ (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (f : EuclideanSpace ℝ (Fin 3) → ℝ → EuclideanSpace ℝ (Fin 3)),
      Comparator.InitialVelocityConditionDecay u₀ ∧ Comparator.ForceConditionDecay f ∧
      ¬ (∃ v p, Comparator.NavierStokesExistenceAndSmoothnessRn ν u₀ f v p) := by
  obtain ⟨u, p, f, K, h, hglobal⟩ := NavierStokesR3.theorem_1_1 ν hν
  exact NavierStokesR3.comparator_of_breakdown h hglobal
```

### child `theorem_1_1`: [`NavierStokes/R3/Theorem.lean` lines 46-49](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/R3/Theorem.lean#L46-L49) ([local copy](code/NavierStokes/R3/Theorem.lean))

```lean
theorem theorem_1_1 : ProblemStatement.breakdownStatement := by
  intro ν hν
  obtain ⟨u, p, f, K, hc, hg, _⟩ := theorem_1_1_with_initial_rest ν hν
  exact ⟨u, p, f, K, hc, hg⟩
```

### child `comparator_of_breakdown`: [`NavierStokes/R3/ComparatorBridge.lean` lines 77-88](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/R3/ComparatorBridge.lean#L77-L88) ([local copy](code/NavierStokes/R3/ComparatorBridge.lean))

```lean
theorem comparator_of_breakdown {ν : ℝ}
    {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (h : CandidateProperties ν u p f K)
    (hglobal : ¬ Nonempty (GlobalFiniteEnergySolution ν f)) :
    ∃ (u₀ : Space → Space) (f : Space → ℝ → Space),
      NavierStokes.Comparator.InitialVelocityConditionDecay u₀ ∧
      NavierStokes.Comparator.ForceConditionDecay f ∧
      ¬ (∃ v p, NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessRn ν u₀ f v p) := by
  refine ⟨fun _ => 0, toComparator f, zero_initial_condition_decay,
    forceConditionDecay_of_compact h.force_smooth h.force_support.1, ?_⟩
  rintro ⟨v, q, hv⟩
  exact hglobal ⟨globalSolutionOfComparator hv⟩
```

How the parts fit. The parent's proof is two lines. Line 43 destructures the
internal theorem's witness (`obtain ⟨u, p, f, K, h, hglobal⟩ :=
NavierStokesR3.theorem_1_1 ν hν`) and line 44 feeds exactly the two fields the
conversion lemma needs (`exact NavierStokesR3.comparator_of_breakdown h
hglobal`). The parent does no mathematics of its own: it re-types the internal
`ProblemStatement.breakdownStatement` into the comparator's
`InitialVelocityConditionDecay ∧ ForceConditionDecay ∧ ¬
NavierStokesExistenceAndSmoothnessRn`.

The lemma graph, in text:

```
navier_stokes_breakdown_R3 (parent; glue = lines 43-44)
├── NavierStokesR3.theorem_1_1                (child 1, internal headline result)
│   └── NavierStokesR3.theorem_1_1_with_initial_rest
│       └── NavierStokesR3.ActualCandidate.selected_candidate_one_with_initial_rest
│           └── NavierStokesR3.ActualCandidate.of_localized_fields (…)
└── NavierStokesR3.comparator_of_breakdown    (child 2, the conversion lemma)
    ├── forceConditionDecay_of_compact        (same file, ComparatorBridge.lean)
    ├── globalSolutionOfComparator            (same file)
    ├── zero_initial_condition_decay          (ComparatorR3Bridge.lean)
    └── toComparator                          (ComparatorBridge.lean)
```

Why each child is a good leaf:

- `theorem_1_1` is a self-contained statement (`ProblemStatement.breakdownStatement`,
  a bundle) whose proof closes from a named sibling in the same file:
  `intro ν hν; obtain ⟨u, p, f, K, hc, hg, _⟩ := theorem_1_1_with_initial_rest ν hν;
  exact ⟨u, p, f, K, hc, hg⟩`. The parent never unfolds it — it only destructures
  its witness.
- `comparator_of_breakdown` is a self-contained conversion lemma: it takes the
  internal `CandidateProperties ν u p f K` plus `¬ Nonempty
  (GlobalFiniteEnergySolution ν f)` and produces the comparator witness. Its proof
  closes from named siblings in the same file (`forceConditionDecay_of_compact`,
  `globalSolutionOfComparator`) plus two bridge helpers (`zero_initial_condition_decay`
  from `ComparatorR3Bridge.lean`, `toComparator` from `ComparatorBridge.lean`).

The file header (lines 6-12) states the same thing in prose: the unconditional
whole-space theorem's "same force and zero initial data satisfy the exact
comparator conditions".

## Why it is good

1. The parent's proof cites the internal theorem `theorem_1_1` (kind `check`,
   form `cites(parent, theorem_1_1)`; [lines 38-44](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/ComparatorR3Theorem.lean#L38-L44)).
2. The parent's proof cites the conversion lemma `comparator_of_breakdown` (kind
   `check`, form `cites(parent, comparator_of_breakdown)`; same lines).
3. The file header states the adapter's purpose — "Its same force and zero
   initial data satisfy the exact comparator conditions" (kind
   `author-statement`; [lines 6-12](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/ComparatorR3Theorem.lean#L6-L12)).
4. The shape is a two-line glue over two named lemmas: `direct_lemmas = 2`,
   parent site 7 lines (38-44), children 4 and 12 lines, and the longest
   project-lemma chain below the parent that I checked is 4 deep (kind
   `measurement`; counted from the copied files listed in `entry.json`).

In my opinion the detail worth copying is that the boundary is stated once, in
`comparator_of_breakdown`, and the public entry point `navier_stokes_breakdown_R3`
adds nothing but the type change from `Space`/`VelocityField` to the comparator's
`EuclideanSpace ℝ (Fin 3)` and its predicate names.

## When to use it, and when not

Use it when a project-internal theorem is proved over an internal vocabulary (a
`ProblemStatement` bundle of predicates such as `CandidateProperties` and
`GlobalFiniteEnergySolution`) and a harness or challenge grader expects the
conclusion in its own predicate vocabulary, over its own types. The move pays
when the adapter's proof is pure plumbing — obtain the internal witness, then
apply one conversion lemma — and the two vocabularies are inter-derivable by
that single conversion lemma.

Avoid it when the two vocabularies are not inter-derivable by one lemma (each
field would then need its own proof, and the conversion lemma is the real
content that should be stated and named separately), when the adapter would
need nontrivial mathematics, or when the reference boundary changes often, so
the adapter must be updated in lockstep.

## Consequences

The move splits the work into two named lemmas: the internal theorem (which
carries the mathematics) and the conversion lemma (which carries the vocabulary
translation). The adapter itself is then trivial — two lines — and stays in sync
for free, but any change to either the internal
`CandidateProperties`/`GlobalFiniteEnergySolution` or the comparator's
`Comparator.*` predicates silently breaks the glue. The comparator's decay
predicates are strictly stronger than the internal whole-space conditions, so
the real work hides inside the conversion lemma (`forceConditionDecay_of_compact`,
`zero_initial_condition_decay`), not in the adapter.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: theorem_1_1@NavierStokes/ComparatorR3Theorem.lean:43, comparator_of_breakdown@NavierStokes/ComparatorR3Theorem.lean:44; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, theorem_1_1) -> cites: theorem_1_1 occurs at NavierStokes/ComparatorR3Theorem.lean:43 | check_claims.py |
| 2 | verified | cites(parent, comparator_of_breakdown) -> cites: comparator_of_breakdown occurs at NavierStokes/ComparatorR3Theorem.lean:44 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/openai/NavierStokesAndEuler at commit `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`, under `Apache-2.0`; see the [source note](../../sources/navierstokesandeuler/SOURCE.md) for the licence text and attribution.
