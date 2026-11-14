# Generalise over the schedule, then instantiate at the certified one: Navier-Stokes local theorem

| | |
|---|---|
| Kind | instance |
| Move | generalise-then-instantiate |
| Language | lean |
| Status | draft |
| Source | [navierstokesandeuler](../../sources/navierstokesandeuler/SOURCE.md) at `f9e8bc5b38b6` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T12:24:05Z |

## Intent

The parent `local_theorem` asserts the existence of fields realising the
paper's full `Properties` structure with no schedule hypotheses left. The
decomposition proves that structure once for an arbitrary schedule
(`properties_of_schedule`), obtains one concrete certified schedule
(`selected_schedule`), and instantiates the general result at it.

## The decomposition

### parent `local_theorem`: [`NavierStokes/LocalPaperTheorem.lean` lines 178-184](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/LocalPaperTheorem.lean#L178-L184) ([local copy](code/NavierStokes/LocalPaperTheorem.lean))

```lean
/-- The complete local theorem, with no finite-stage or schedule hypotheses. -/
theorem local_theorem :
    ∃ h qstar Xa Xext heatNormalization : ℝ,
      ∃ A D u : VelocityField, ∃ p : PressureField,
        Properties h qstar Xa Xext heatNormalization A D u p := by
  obtain ⟨a, hs, _, hr⟩ := LocalResidualFlatness.selected_schedule
  exact ⟨_, _, _, _, _, _, _, _, _, properties_of_schedule hs hr⟩
```

### child `properties_of_schedule`: [`NavierStokes/LocalPaperTheorem.lean` lines 126-176](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/LocalPaperTheorem.lean#L126-L176) ([local copy](code/NavierStokes/LocalPaperTheorem.lean))

```lean
/-- All local properties are retained by any actual schedule with the proved
all-order residual bounds. -/
theorem properties_of_schedule {a : ℕ → ℕ} (hs : LocalScheduleWitness.Selected a)
    (hr : LocalResidualFlatness.AllResidualJetRates ActualPrimary.h
      ActualCandidateAssembly.selectedPotentialStages ActualCandidateAssembly.selectedDirectStages
      ActualCandidateAssembly.selectedPressureStages a) :
    Properties ActualPrimary.h (LocalPaperDomain.qstar a) LocalPaperDomain.innerEdge
      LocalPaperDomain.outerEdge (BaseExterior.nominalHeatNormalization ActualPrimary.nominal)
      (LocalPotentialRebundle.potential a) (LocalPotentialRebundle.direct a)
      (LocalAngularGrowth.selectedRawVelocity a) (LocalPotentialRebundle.pressure a) := by
  have hat := hs.2.2.2.2.1
  have hsm := hs.2.2.2.2.2.2.1
  obtain ⟨eA, eD, eP⟩ := LocalScheduleWitness.selected_awayExtensions hs
  obtain ⟨eA', eD'⟩ := LocalPotentialRebundle.awayExtensions eA eD
  have hAs := LocalPotentialRebundle.potential_smooth hsm
  have hDs := LocalPotentialRebundle.direct_smooth hsm
  refine {
    exponent_small := LocalAngularGrowth.selected_exponent_small
    scale_positive := LocalPaperDomain.qstar_pos a
    edges_ordered := ⟨LocalPaperDomain.innerEdge_pos, LocalPaperDomain.innerEdge_lt_outerEdge⟩
    potential_smooth := hAs
    direct_smooth := hDs
    velocity_smooth := MixedDiagonalResidual.velocity_smooth_of_sums hsm
    pressure_smooth := hsm.pressure
    direct_angular := ?_
    decomposition := fun w hw => (LocalPotentialRebundle.velocity_eq_original hsm hw).symm
    divergence_free := fun w hw => LocalScheduleAngular.mixed_divergence hs hw
    potential_extensions := eA'
    direct_extensions := eD'
    pressure_extensions := eP
    potential_jets_bounded := uniformJetsOnScaleStrips_of_extensions
      ActualPrimary.outgoing.data.h_pos ActualPrimary.outgoing.data.h_lt_half hAs eA'
    direct_jets_bounded := uniformJetsOnScaleStrips_of_extensions
      ActualPrimary.outgoing.data.h_pos ActualPrimary.outgoing.data.h_lt_half hDs eD'
    pressure_jets_bounded := uniformJetsOnScaleStrips_of_extensions
      ActualPrimary.outgoing.data.h_pos ActualPrimary.outgoing.data.h_lt_half hsm.pressure eP
    residual_flatness := ?_
    exterior := ?_
    angular_growth := ?_
  }
  · exact ⟨LocalPotentialRebundle.angularScalar a,
      fun w hw => LocalPotentialRebundle.direct_eq_angularField hat hw⟩
  · intro m r hr0 X hX
    exact LocalScaleApproach.jetRate_uniform_small_scale ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half (hr m r hr0) X hX
  · intro w ht hq hX
    obtain ⟨hw, he, hc⟩ := LocalPaperDomain.exterior_conditions ht hq hX
    obtain ⟨hA, hD, hP⟩ := LocalPotentialRebundle.exterior hw he hc
    exact ⟨hA, hD, hP, selected_exterior_residual_zero hat hw he hc⟩
  · exact ⟨LocalAngularGrowth.innerRadius, LocalAngularGrowth.innerRadius_pos,
      LocalAngularGrowth.innerRadius_lt_left, LocalAngularGrowth.selectedRawVelocity_angularGrowth hat⟩
```

### child `selected_schedule`: [`NavierStokes/LocalResidualFlatness.lean` lines 111-129](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/LocalResidualFlatness.lean#L111-L129) ([local copy](code/NavierStokes/LocalResidualFlatness.lean))

```lean
/-- Closed all-order flatness for one common actual schedule. No raw-stage,
finite-stage, smoothness, or rate assumption remains. -/
theorem selected_schedule :
    ∃ a : ℕ → ℕ,
      MixedCandidateWitness.SelectedSchedule CorrectionInitialization.ActualPrimary.h
        ActualCandidateConstruction.selectedQbig ActualCandidateAssembly.selectedPotentialStages
        ActualCandidateAssembly.selectedDirectStages ActualCandidateAssembly.selectedPressureStages a ∧
      MixedDiagonalSchedule.ThreeCutBounds a CorrectionInitialization.ActualPrimary.h
        ActualCandidateAssembly.selectedPotentialStages ActualCandidateAssembly.selectedDirectStages
        ActualCandidateAssembly.selectedPressureStages (fun j => selectedEstimates.gain j / 2)
        (MixedDiagonalSchedule.commonLoss selectedEstimates.potentialLoss selectedEstimates.directLoss
          selectedEstimates.pressureLoss) PhysicalWaveSum.preterminal ∧
      AllResidualJetRates CorrectionInitialization.ActualPrimary.h
        ActualCandidateAssembly.selectedPotentialStages ActualCandidateAssembly.selectedDirectStages
        ActualCandidateAssembly.selectedPressureStages a :=
  exists_schedule_all_jetRates selectedEstimates
    CorrectionInitialization.ActualPrimary.outgoing.data.h_pos
    CorrectionInitialization.ActualPrimary.outgoing.data.h_lt_half
    (ActualCandidateConstruction.qbig_pos _ _)
```

How the parts fit. The parent `local_theorem` is an existence goal with no
schedule hypotheses left. Its two-line proof is the instantiation step: line
183 turns the certificate into context
(`obtain ⟨a, hs, _, hr⟩ := LocalResidualFlatness.selected_schedule`), and line
184 applies the general lemma to that context
(`exact ⟨…, properties_of_schedule hs hr⟩`). The glue names the two children
and nothing else.

The lemma graph, in text:

```
local_theorem (parent, the glue)
├── properties_of_schedule   ← generalisation: builds `Properties` for an
│        arbitrary schedule `a`; uses selected_exterior_residual_zero,
│        uniformJetsOnScaleStrips_of_extensions and the imported
│        LocalScheduleWitness / LocalPotentialRebundle / LocalScaleApproach
│        / LocalPaperDomain lemmas
└── selected_schedule        ← certificate: one schedule satisfying the two
         hypotheses; uses exists_schedule_all_jetRates
```

The two children are the two halves the move separates.

- `properties_of_schedule` (lines 126-176) is the *generalisation*: it builds
  the whole `Properties` structure for an *arbitrary* schedule `a`, needing
  only `hs : LocalScheduleWitness.Selected a` and
  `hr : LocalResidualFlatness.AllResidualJetRates … a`. Its proof is a
  `refine { … }` that fills each of the twenty `Properties` fields from an
  imported lemma, closing the four `?_` holes (`direct_angular`,
  `residual_flatness`, `exterior`, `angular_growth`) with bulleted sub-proofs.
  It closes on its own from named siblings, which is what makes it a good
  leaf: a self-contained statement over a free variable.

- `selected_schedule` (lines 111-129) is the *certificate*: it proves the
  existence of one schedule `a` satisfying exactly the hypotheses
  `properties_of_schedule` needs (`SelectedSchedule` entails `Selected`, and
  `AllResidualJetRates` appears in the conclusion), for the repository's fixed
  `selectedEstimates`. Its proof is one line applying
  `exists_schedule_all_jetRates` to those concrete estimates, so it too closes
  on its own from a named sibling.

One level down the same move recurs: `selected_schedule` is itself the
general lemma `exists_schedule_all_jetRates` (parameterised over arbitrary
`h qbig A B P`) instantiated at the fixed `selectedEstimates`.

## Why it is good

1. `properties_of_schedule` occurs in the `local_theorem` site (kind `check`,
   form `cites(local_theorem, properties_of_schedule)`, decided by
   `check_claims.py`; the citation is line 184).
2. `selected_schedule` occurs in the `local_theorem` site (kind `check`, form
   `cites(local_theorem, selected_schedule)`, decided by `check_claims.py`;
   the citation is line 183).
3. No `sorry`/`admit`/`axiom` closes a goal in the glue or the generalised
   child — `NavierStokes/LocalPaperTheorem.lean` lines 126-184 (kind `check`,
   form `no_sorry`).
4. The shape is two direct lemmas: glue 7 lines, child proofs 51 and 19 lines,
   depth 2 (kind `measurement`, line counts of the copied files).
5. The authors state the generalisation's design in the doc comment on
   `properties_of_schedule`: "All local properties are retained by any actual
   schedule with the proved all-order residual bounds" (kind
   `author-statement`, lines 126-127).

This entry supports survey F §10 rule 8 ("Backward rule, `suffices`, and
witnesses as templates"): the glue's
`obtain ⟨a, hs, _, hr⟩ := LocalResidualFlatness.selected_schedule` turns the
existence certificate into context, and the general lemma is then applied at
that witness as a template. In my opinion the detail worth copying is that the
generalised child carries *all* the mathematics over a free variable, so the
parent's proof is two lines and the two halves can be proved and checked
independently.

## When to use it, and when not

Use it when the target is an existence goal `∃ x : σ, P x` whose predicate `P`
is a big conjunction that can be built uniformly for any element of a class
(here: the `Properties` structure for any schedule with a `Selected` witness
and all-order residual rates). Pull all the construction into one generalised
lemma over a free variable, certify one concrete element in a second lemma,
and let the parent be an `obtain` plus one application.

Avoid it when the class is too weak to carry the proof (the generalised
statement will not close), when the concrete element has to be used in
incompatible ways in different clauses (generalising then loses the
instance-specific information), or when the certificate's conclusion is not
shaped exactly like the generalised lemma's hypotheses, in which case the glue
must re-derive hypotheses by hand and the clean two-line instantiation breaks.

## Consequences

The move splits the existence proof into a general lemma (all the mathematics,
over a free variable `a`) and a certificate lemma (existence of one concrete
instance). Obligations: the general lemma's hypotheses must be discharged
exactly once at the instantiation site, and the certified element must satisfy
the same hypothesis type as the general lemma's parameter (here `Selected a`
and `AllResidualJetRates`). Failure modes: a certificate whose conclusion is
weaker than, or differently shaped from, the general lemma's hypotheses makes
the `obtain` pattern break; and over-generalising (quantifying over more than
the proof actually uses) can push instance-specific side conditions into the
certificate where they do not belong.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: properties_of_schedule@NavierStokes/LocalPaperTheorem.lean:184, selected_schedule@NavierStokes/LocalPaperTheorem.lean:183; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(local_theorem, properties_of_schedule) -> cites: properties_of_schedule occurs at NavierStokes/LocalPaperTheorem.lean:184 | check_claims.py |
| 2 | verified | cites(local_theorem, selected_schedule) -> cites: selected_schedule occurs at NavierStokes/LocalPaperTheorem.lean:183 | check_claims.py |
| 3 | verified | no_sorry(NavierStokes/LocalPaperTheorem.lean, 126-184) -> no_sorry: none of sorry, admit, axiom in NavierStokes/LocalPaperTheorem.lean:126-184 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/openai/NavierStokesAndEuler at commit `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`, under `Apache-2.0`; see the [source note](../../sources/navierstokesandeuler/SOURCE.md) for the licence text and attribution.
