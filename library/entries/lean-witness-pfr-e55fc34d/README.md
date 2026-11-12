# Witness the tau-minimiser and its uniform subgroup for the entropic PFR conjecture

| | |
|---|---|
| Kind | instance |
| Move | witness |
| Language | lean |
| Status | accepted |
| Source | [pfr](../../sources/pfr/SOURCE.md) at `1ef23c3c5a83` |
| Licence | `Apache-2.0` |

## Intent

A statement about two G-valued random variables is proved by introducing a
single witness: obtain a τ-minimiser (a pair `X₁, X₂` minimising
`τ = d[X₁;X₂] + η·d[X⁰₁;X₁] + η·d[X⁰₂;X₂]`), prove its two variables have Ruzsa
distance zero, turn that into a uniform subgroup `H` and variable `U`, and close
the three distance bounds about `U` with the triangle inequality and `linarith`.

## The decomposition

### parent `entropic_PFR_conjecture`: [`PFR/EntropyPFR.lean` lines 54-73](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/EntropyPFR.lean#L54-L73) ([local copy](code/PFR/EntropyPFR.lean))

```lean
theorem entropic_PFR_conjecture (hpη : p.η = 1 / 9) :
    ∃ H : Submodule (ZMod 2) G, ∃ Ω : Type uG, ∃ mΩ : MeasureSpace Ω, ∃ U : Ω → G,
    IsProbabilityMeasure (ℙ : Measure Ω) ∧ Measurable U ∧
    IsUniform H U ∧ d[p.X₀₁ # U] + d[p.X₀₂ # U] ≤ 11 * d[p.X₀₁ # p.X₀₂] ∧
      d[p.X₀₁ # U] ≤ 6 * d[p.X₀₁ # p.X₀₂] ∧
      d[p.X₀₂ # U] ≤ 6 * d[p.X₀₁ # p.X₀₂] := by
  cases nonempty_fintype G
  obtain ⟨Ω', mΩ', X₁, X₂, hX₁, hX₂, _, htau_min⟩ := tau_minimizer_exists p
  have hdist : d[X₁ # X₂] = 0 := tau_strictly_decreases p hX₁ hX₂ htau_min hpη
  obtain ⟨H, U, hU, hH_unif, hdistX₁, hdistX₂⟩ := exists_isUniform_of_rdist_eq_zero hX₁ hX₂ hdist
  have : d[p.X₀₁ # p.X₀₂] = d[p.X₀₂ # p.X₀₁] := rdist_symm
  have h : τ[X₁ # X₂ | p] ≤ τ[p.X₀₂ # p.X₀₁ | p] := is_tau_min p htau_min p.hmeas2 p.hmeas1
  rw [tau, tau, hpη] at h
  norm_num at h
  have : d[p.X₀₁ # U] ≤ d[p.X₀₁ # X₁] + d[X₁ # U] := rdist_triangle p.hmeas1 hX₁ hU
  have : d[p.X₀₂ # U] ≤ d[p.X₀₂ # X₂] + d[X₂ # U] := rdist_triangle p.hmeas2 hX₂ hU
  have : d[p.X₀₁ # U] ≤ d[p.X₀₁ # p.X₀₂] + d[p.X₀₂ # U] := rdist_triangle p.hmeas1 p.hmeas2 hU
  have : d[p.X₀₂ # U] ≤ d[p.X₀₂ # p.X₀₁] + d[p.X₀₁ # U] := rdist_triangle p.hmeas2 p.hmeas1 hU
  exact ⟨H.toZModSubmodule _, Ω', inferInstance, U, inferInstance, hU, hH_unif,
    by linarith, by linarith, by linarith⟩
```

### child `tau_minimizer_exists`: [`PFR/TauFunctional.lean` lines 147-160](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/TauFunctional.lean#L147-L160) ([local copy](code/PFR/TauFunctional.lean))

```lean
lemma tau_minimizer_exists [MeasurableSingletonClass G] :
    ∃ (Ω : Type uG) (_ : MeasureSpace Ω) (X₁ : Ω → G) (X₂ : Ω → G),
    Measurable X₁ ∧ Measurable X₂ ∧ IsProbabilityMeasure (ℙ : Measure Ω) ∧
    TauMinimizes p X₁ X₂ := by
  let μ := (tau_min_exists_measure p).choose
  have : IsProbabilityMeasure μ.1 := (tau_min_exists_measure p).choose_spec.1
  have : IsProbabilityMeasure μ.2 := (tau_min_exists_measure p).choose_spec.2.1
  have P : IsProbabilityMeasure (μ.1.prod μ.2) := by infer_instance
  let M : MeasureSpace (G × G) := ⟨μ.1.prod μ.2⟩
  refine ⟨G × G, M, Prod.fst, Prod.snd, measurable_fst, measurable_snd, P, ?_⟩
  intro ν₁ h₁ ν₂ h₂
  have A : τ[@Prod.fst G G # @Prod.snd G G | p] = τ[id ; μ.1 # id ; μ.2 | p] :=
    ProbabilityTheory.IdentDistrib.tau_eq p IdentDistrib.fst_id IdentDistrib.snd_id
  convert (tau_min_exists_measure p).choose_spec.2.2 ν₁ ν₂
```

### child `tau_strictly_decreases`: [`PFR/EntropyPFR.lean` lines 39-49](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/EntropyPFR.lean#L39-L49) ([local copy](code/PFR/EntropyPFR.lean))

```lean
theorem tau_strictly_decreases (h_min : TauMinimizes p X₁ X₂) (hpη : p.η = 1 / 9) :
    d[X₁ # X₂] = 0 := by
  cases nonempty_fintype G
  let ⟨A, mA, μ, Y₁, Y₂, Y₁', Y₂', hμ, h_indep, hY₁, hY₂, hY₁', hY₂', h_id1, h_id2, h_id1', h_id2'⟩
    := independent_copies4_nondep hX₁ hX₂ hX₁ hX₂ ℙ ℙ ℙ ℙ
  rw [← h_id1.rdist_congr h_id2]
  let : MeasureSpace A := ⟨μ⟩
  have : IsProbabilityMeasure (ℙ : Measure A) := hμ
  rw [← h_id1.tauMinimizes p h_id2] at h_min
  apply tau_strictly_decreases_aux p Y₁ Y₂ Y₁' Y₂' hY₁ hY₂ hY₁' hY₂' (h_id1.trans h_id1'.symm)
    (h_id2.trans h_id2'.symm) h_indep h_min hpη
```

### child `exists_isUniform_of_rdist_eq_zero`: [`PFR/HundredPercent.lean` lines 160-175](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/HundredPercent.lean#L160-L175) ([local copy](code/PFR/HundredPercent.lean))

```lean
theorem exists_isUniform_of_rdist_eq_zero
    {Ω' : Type*} [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')] {X' : Ω' → G}
    (hX : Measurable X) (hX' : Measurable X') (hdist : d[X # X'] = 0) :
    ∃ H : AddSubgroup G, ∃ U : Ω → G,
      Measurable U ∧ IsUniform H U ∧ d[X # U] = 0 ∧ d[X' # U] = 0 := by
  have h' : d[X # X] = 0 := by
    apply le_antisymm _ (rdist_nonneg hX hX)
    calc
      d[X # X] ≤ d[X # X'] + d[X' # X] := rdist_triangle hX hX' hX
      _ = 0 := by rw [hdist, rdist_symm, hdist, zero_add]
  rcases exists_isUniform_of_rdist_self_eq_zero hX h' with ⟨H, U, hmeas, hunif, hd⟩
  refine ⟨H, U, hmeas, hunif, hd, ?_⟩
  apply le_antisymm _ (rdist_nonneg hX' hmeas)
  calc
    d[X' # U] ≤ d[X' # X] + d[X # U] := rdist_triangle hX' hX hmeas
    _ = 0 := by rw [hd, rdist_symm, hdist, zero_add]
```

### child `rdist_symm`: [`PFR/ForMathlib/Entropy/RuzsaDist.lean` lines 238-245](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/ForMathlib/Entropy/RuzsaDist.lean#L238-L245) ([local copy](code/PFR/ForMathlib/Entropy/RuzsaDist.lean))

```lean
lemma rdist_symm [IsFiniteMeasure μ] [IsFiniteMeasure μ'] :
    d[X ; μ # Y ; μ'] = d[Y ; μ' # X ; μ] := by
  rw [rdist_def, rdist_def, sub_sub, sub_sub, add_comm]
  congr 1
  rw [← entropy_neg (by fun_prop)]
  have : (-fun x : G × G ↦ x.1 - x.2) = (fun x ↦ x.1 - x.2) ∘ Prod.swap := by ext ; simp
  rw [this, entropy_def, ← map_map (by fun_prop) measurable_swap, prod_swap]
  rfl
```

### child `is_tau_min`: [`PFR/TauFunctional.lean` lines 169-175](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/TauFunctional.lean#L169-L175) ([local copy](code/PFR/TauFunctional.lean))

```lean
lemma is_tau_min (h : TauMinimizes p X₁ X₂) (h1 : Measurable X₁') (h2 : Measurable X₂') :
    τ[X₁ # X₂ | p] ≤ τ[X₁' # X₂' | p] := by
  let ν₁ := (ℙ : Measure Ω'₁).map X₁'
  let ν₂ := (ℙ : Measure Ω'₂).map X₂'
  have B : τ[X₁' # X₂' | p] = τ[id ; ν₁ # id ; ν₂ | p] :=
    (identDistrib_id_right h1.aemeasurable).tau_eq p (identDistrib_id_right h2.aemeasurable)
  convert h ν₁ ν₂
```

### child `rdist_triangle`: [`PFR/ForMathlib/Entropy/RuzsaDist.lean` lines 443-465](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/ForMathlib/Entropy/RuzsaDist.lean#L443-L465) ([local copy](code/PFR/ForMathlib/Entropy/RuzsaDist.lean))

```lean
lemma rdist_triangle {X : Ω → G} {Y : Ω' → G} {Z : Ω'' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [hμ : IsProbabilityMeasure μ] [hμ' : IsProbabilityMeasure μ']
    [hμ'' : IsProbabilityMeasure μ''] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    d[X ; μ # Z ; μ''] ≤ d[X ; μ # Y ; μ'] + d[Y ; μ' # Z ; μ''] := by
  obtain ⟨A, mA, μA, X', Y', Z', hμA, hInd, hX', hY', hZ', HX, HY, HZ, _, _, _⟩ :=
    independent_copies3_nondep_finiteRange hX hY hZ μ μ' μ''
  suffices d[X' ; μA # Z' ; μA] ≤ d[X' ; μA # Y' ; μA] + d[Y' ; μA # Z' ; μA] by
    rwa [HX.rdist_congr HY, HY.rdist_congr HZ, HX.rdist_congr HZ] at this
  have IndepLem : IndepFun (⟨X', Z'⟩) Y' μA :=
    iIndepFun.indepFun_prodMk hInd (fun i => by fin_cases i ; all_goals { simpa }) 0 2 1
      (by norm_cast) (by norm_cast)
  calc d[X' ; μA # Z' ; μA] = H[X' - Z'; μA] - (H[X'; μA] / 2 + H[Z'; μA] / 2) := by
        rw [ProbabilityTheory.IndepFun.rdist_eq
          (by simpa using hInd.indepFun (show 0 ≠ 2 by norm_cast)) hX' hZ'] ; ring
    _ ≤ (H[X' - Y' ; μA] + H[Y' - Z' ; μA] - H[Y' ; μA]) - (H[X'; μA] / 2 + H[Z'; μA] / 2) :=
          sub_le_sub_right (ent_of_diff_le _ _ _ hX' hZ' hY' IndepLem) _
    _ = (H[X' - Y' ; μA] - H[X'; μA] / 2 - H[Y' ; μA] / 2) +
          (H[Y' - Z' ; μA] - H[Y' ; μA] / 2 - H[Z'; μA] / 2) := by ring
    _ = d[X' ; μA # Y' ; μA] + d[Y' ; μA # Z' ; μA] := by
        rw [ProbabilityTheory.IndepFun.rdist_eq (by simpa using (iIndepFun.indepFun hInd
          (show 0 ≠ 1 by norm_cast))) hX' hY', ProbabilityTheory.IndepFun.rdist_eq
          (by simpa using (iIndepFun.indepFun hInd (show 1 ≠ 2 by norm_cast))) hY' hZ']
```

How the parts fit. The glue (lines 60-73) runs one `obtain`/`have` per lemma.
`obtain ⟨Ω', mΩ', X₁, X₂, hX₁, hX₂, _, htau_min⟩ := tau_minimizer_exists p`
(line 61) introduces the witness: a pair of random variables minimising τ,
together with their measurability and `TauMinimizes p X₁ X₂`.
`tau_strictly_decreases` then proves the witness has `d[X₁ # X₂] = 0` (line 62),
and `exists_isUniform_of_rdist_eq_zero` turns that zero distance into the
subgroup `H` and uniform variable `U` with `d[X₁ # U] = d[X₂ # U] = 0` (line 63).
The rest of the glue only compares the reference variables to `U`: `rdist_symm`
(line 64) and `is_tau_min` (line 65, unfolded with `rw [tau, tau, hpη]` and
`norm_num`) give the key inequality `h`, and four applications of `rdist_triangle`
(lines 68-71) plus `linarith` (line 73) discharge the three distance bounds. The
lemma graph:

```text
entropic_PFR_conjecture
├─ tau_minimizer_exists          (→ tau_min_exists_measure → IsCompact.exists_isMinOn)
├─ tau_strictly_decreases        (→ tau_strictly_decreases_aux → cond_construct_good,
│                                  sum_condMutual_le, sum_dist_diff_le, first_estimate)
├─ exists_isUniform_of_rdist_eq_zero (→ rdist_triangle ×2, rdist_symm,
│                                  exists_isUniform_of_rdist_self_eq_zero)
├─ rdist_symm                    (leaf)
├─ is_tau_min                    (leaf: `convert h ν₁ ν₂`)
└─ rdist_triangle                (leaf: calc through ent_of_diff_le)
```

Each child is a good leaf: a self-contained statement whose proof closes on its
own or from named siblings. `tau_minimizer_exists` closes from the measure-level
minimiser `tau_min_exists_measure` and the `IdentDistrib.tau_eq` transfer;
`tau_strictly_decreases` is a one-shot `apply tau_strictly_decreases_aux` after
transferring to independent copies; `exists_isUniform_of_rdist_eq_zero` closes
from the named sibling `exists_isUniform_of_rdist_self_eq_zero` plus two
`rdist_triangle` steps; `rdist_symm`, `is_tau_min` and `rdist_triangle` are
library lemmas each closed by a short rewrite/`convert`/`calc` argument. No leaf
repeats the parent's work: the parent never reasons about the internals of τ or
of the uniform subgroup, only about what the lemmas return.

## Why it is good

1. The glue closes from six named lemmas and `linarith` — the parent's own
   argument is 14 lines, with no `sorry` in the file — and the file is built by
   the project's CI (`check`; [PFR/EntropyPFR.lean#L60-L73](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/EntropyPFR.lean#L60-L73)
   and [.github/workflows/push.yml](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/.github/workflows/push.yml)).
2. The authors say the zero-distance-to-uniform step "Follows from the preceding
   claim by the triangle inequality", and the proof does exactly that
   (`author-statement`; [PFR/HundredPercent.lean#L158-L175](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/HundredPercent.lean#L158-L175)).
3. The shape is flat: parent proof 14 lines, six children of 10/9/11/6/5/18
   proof lines, longest checked lemma chain depth 3 (`measurement`; line ranges
   in entry.json `shape` and `metrics`).
4. The same assembly is reused nearly verbatim in `entropic_PFR_conjecture_improv`
   (`known-use`; [PFR/ImprovedPFR.lean#L819-L832](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/ImprovedPFR.lean#L819-L832)).

In my opinion the detail worth copying is the discipline of the last three
lines: the proof never re-derives a bound for `U` from `H`'s structure; it feeds
`d[X₁ # U] = 0` and `d[X₂ # U] = 0` into `rdist_triangle` and lets `linarith`
assemble the four facts into the three target inequalities.

## When to use it, and when not

Use it when the goal is an existence statement whose witness is picked by an
optimisation (a minimiser or maximiser of some functional) or by a zero-distance
condition, and the remaining properties of the witness are inequalities that
follow from generic distance facts (a triangle inequality, a minimiser
comparison) closed by linear arithmetic. Avoid it when the witness has to be
built explicitly and no existence lemma is already available, when a property of
the witness needs its internal construction rather than generic facts, or when
the distance bounds are not linear combinations that `linarith` can close.

## Consequences

The move creates one obligation per property of the witness, each to be closed
by a named lemma, plus the exhaustiveness of the `obtain` (discharged by the
existence lemma itself). The witness must be available under the ambient
hypotheses — here `nonempty_fintype G` and the `refPackage p`, so the minimiser
lemma applies — and if a property needs the witness's internal structure it has
to return through a lemma such as `is_tau_min`. Failure mode: if one of the
three distance bounds is not a `linarith` consequence of the `rdist_triangle`
facts, the clean one-lemma-per-goal shape breaks and the witness must be
unfolded.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push.yml (leanprover/lean-action builds the whole project incl. PFR/EntropyPFR.lean); default branch master; pinned commit 1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 4 file(s) byte-identical at 1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | code/PFR/EntropyPFR.lean lines 60-73: line 61 calls tau_minimizer_exists, 62 tau_strictly_decreases, 63 exists_isUniform_of_rdist_eq_zero, 64 rdist_symm, 65 is_tau_min, 68-71 rdist_triangle four times, 73 closes three bounds by linarith | verifier |
| 2 | verified | code/PFR/HundredPercent.lean lines 158-159 doc comment 'Follows from the preceding claim by the triangle inequality'; proof 165-175 uses rdist_triangle at 168 and 174 plus rdist_symm at 169 and 175 | verifier |
| 3 | verified | parent EntropyPFR.lean 60-73 = 14 lines; children TauFunctional.lean 151-160=10, EntropyPFR.lean 41-49=9, HundredPercent.lean 165-175=11, RuzsaDist.lean 240-245=6, TauFunctional.lean 171-175=5, RuzsaDist.lean 448-465=18; depth chain EntropyPFR.lean:62->:48 tau_strictly_decreases_aux -> Endgame.lean:468 tau_strictly_decreases_aux -> FirstEstimate.lean:143 first_estimate | verifier |
| 4 | verified | PFR/ImprovedPFR.lean lines 819-832 (fetched): 819 obtains minimiser+d=0, 820 exists_isUniform_of_rdist_eq_zero, 823 is_tau_min, 826-831 rdist_triangle, 828/832 linarith | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent glue (EntropyPFR.lean 60-73) obtains a tau-minimiser witness (obtain, line 61) then proves its properties, matching move=witness. It uses exactly six named lemmas: tau_minimizer_exists (61), tau_strictly_decreases (62), exists_isUniform_of_rdist_eq_zero (63), rdist_symm (64), is_tau_min (65), rdist_triangle (68-71, four times); the three target bounds close by linarith (73), rest by inferInstance/hU/hH_unif. All six children match the code: statements and closed_by descriptions verified against copied files; no sorry/admit. Shape numbers correct: direct_lemmas=6, glue_lines=14 (60-73), child_lines=[10,9,11,6,5,18] (TauFunctional 151-160, EntropyPFR 41-49, HundredPercent 165-175, RuzsaDist 240-245, TauFunctional 171-175, RuzsaDist 448-465), depth=3 confirmed chain entropic_PFR_conjecture->tau_strictly_decreases->tau_strictly_decreases_aux (Endgame.lean)->first_estimate (FirstEstimate.lean:143). | reviewer-correctness |
| generality | accept | Generality is stated so it applies beyond the example and is honest. applicability/use_when generalise the move to an existence goal whose witness is an optimisation or zero-distance object, with the remaining properties being distance/functional inequalities closed by generic facts (triangle inequality, minimiser comparison) plus linear arithmetic; avoid_when is specific (witness must be built explicitly with no existence lemma available; a property needs the witness's internal construction; the bounds are not linarith-closable). consequences name the real obligations (one named lemma per property, exhaustiveness of the obtain discharged by the existence lemma, ambient hypotheses nonempty_fintype G and refPackage p) and a concrete failure mode (a non-linarith bound forces unfolding the witness, breaking the one-lemma-per-goal shape). The 'good leaf' paragraph answers the bounded-prover question: each child is a self-contained statement whose proof closes on its own or from named siblings, has a short proof (5-18 lines), and no leaf repeats the parent's work (the parent never reasons about tau or the subgroup internals). Local code/PFR/EntropyPFR.lean confirms the glue is 14 lines invoking the six named lemmas with linarith closing the three bounds. | reviewer-generality |
| provenance-licence | accept | check_provenance.py pass: 4 files byte-identical at 1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a; commit consistent across entry.json/source.json/SOURCE.md; licence Apache-2.0 in entry, source.json and SOURCE.md matches upstream-LICENSE (Apache 2.0 text); permalinks all point to github.com/teorth/pfr/blob/<commit>/<path> with correct paths and line ranges | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/teorth/pfr at commit `1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a`, under `Apache-2.0`; see the [source note](../../sources/pfr/SOURCE.md) for the licence text and attribution.
