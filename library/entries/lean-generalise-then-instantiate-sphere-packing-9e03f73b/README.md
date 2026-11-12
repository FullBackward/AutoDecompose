# Instantiate the periodic-density formula to compute the E8 packing density

| | |
|---|---|
| Kind | instance |
| Move | generalise-then-instantiate |
| Language | lean |
| Status | accepted |
| Source | [sphere-packing](../../sources/sphere-packing/SOURCE.md) at `efe3bbbc1ece` |
| Licence | `Apache-2.0` |

## Intent

Assemble the E8 packing density π⁴/384 from the general periodic-density formula
`PeriodicSpherePacking.density_eq`, instantiated at `d = 8`, lattice `E8Lattice`,
basis `E8_ℤBasis` and bound `L = 16`, by substituting the three E8-specific
ingredients (`numReps = 1`, covolume `= 1`, and the per-basis-vector norm bound
`≤ 2`).

## The decomposition

### parent `E8Packing_density`: [`SpherePacking/Basic/E8.lean` lines 671-694](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/Basic/E8.lean#L671-L694) ([local copy](code/SpherePacking/Basic/E8.lean))

```lean
theorem E8Packing_density : E8Packing.density = ENNReal.ofReal π ^ 4 / 384 := by
  rw [PeriodicSpherePacking.density_eq E8_ℤBasis ?_ (by omega) (L := 16)]
  · rw [E8Packing_numReps, Nat.cast_one, one_mul, volume_ball, finrank_euclideanSpace,
      Fintype.card_fin, Nat.cast_ofNat]
    simp only [E8Packing]
    have {x : ℝ} (hx : 0 ≤ x := by positivity) : √x ^ 8 = x ^ 4 := calc
      √x ^ 8 = (√x ^ 2) ^ 4 := by rw [← pow_mul]
      _ = x ^ 4 := by rw [Real.sq_sqrt hx]
    rw [← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul, div_pow, this, this, ← mul_div_assoc,
      div_mul_eq_mul_div, mul_comm, mul_div_assoc, mul_div_assoc]
    · norm_num [Nat.factorial, mul_one_div]
      convert div_one _
      · rw [E8_ℤBasis_ofZLatticeBasis_volume]
      · rw [← ENNReal.ofReal_pow, ENNReal.ofReal_div_of_pos, ENNReal.ofReal_ofNat] <;> positivity
    · positivity
    · positivity
  · intro x hx
    change x ∈ fundamentalDomain (E8_ℤBasis.ofZLatticeBasis ℝ E8Lattice) at hx
    trans ∑ i, ‖E8_ℤBasis i‖
    · rw [← fract_eq_self.mpr hx]
      convert norm_fract_le (K := ℝ) _ _
      simp [Basis.ofZLatticeBasis_apply]
    · refine (Finset.sum_le_sum (fun i hi ↦ E8_ℤBasis_apply_norm i)).trans ?_
      norm_num
```

### child `PeriodicSpherePacking.density_eq`: [`SpherePacking/Basic/PeriodicPacking.lean` lines 967-972](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/Basic/PeriodicPacking.lean#L967-L972) ([local copy](code/SpherePacking/Basic/PeriodicPacking.lean))

```lean
theorem PeriodicSpherePacking.density_eq
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    S.density
      = S.numReps * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) :=
  limsSup_eq_of_le_nhds (S.tendsto_finiteDensity b hL hd)
```

### child `E8Packing_numReps`: [`SpherePacking/Basic/E8.lean` lines 631-632](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/Basic/E8.lean#L631-L632) ([local copy](code/SpherePacking/Basic/E8.lean))

```lean
lemma E8Packing_numReps : E8Packing.numReps = 1 :=
  PeriodicSpherePacking.numReps_eq_one _ rfl
```

### child `E8_ℤBasis_apply_norm`: [`SpherePacking/Basic/E8.lean` lines 641-643](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/Basic/E8.lean#L641-L643) ([local copy](code/SpherePacking/Basic/E8.lean))

```lean
lemma E8_ℤBasis_apply_norm : ∀ i : Fin 8, ‖E8_ℤBasis i‖ ≤ 2 := by
  intro i
  simpa [coe_E8_ℤBasis_apply, E8Basis_apply] using E8Basis_apply_norm i
```

### child `E8_ℤBasis_ofZLatticeBasis_volume`: [`SpherePacking/Basic/E8.lean` lines 666-668](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/efe3bbbc1ece548f4672a772b94d8f621c10fdda/SpherePacking/Basic/E8.lean#L666-L668) ([local copy](code/SpherePacking/Basic/E8.lean))

```lean
lemma E8_ℤBasis_ofZLatticeBasis_volume :
    volume (fundamentalDomain (E8_ℤBasis.ofZLatticeBasis ℝ E8Lattice)) = 1 := by
  rw [← volume_preimage_toLp_symm, preimage_fundamentalDomain_E8_ℤBasis, E8Basis_volume]
```

How the parts fit. The parent has the shape "the density of the *E8 packing*
equals π⁴/384". Its proof is a single instantiation rewrite followed by two
subgoal branches:

1. `rw [PeriodicSpherePacking.density_eq E8_ℤBasis ?_ (by omega) (L := 16)]`
   (line 672) is the *instantiate* step. `density_eq` is the *generalise* half,
   proved once over any `PeriodicSpherePacking d` and any ℤ-basis `b`; it
   expresses `S.density` as `S.numReps * volume (ball (separation / 2)) /
   volume (fundamentalDomain …)`. The rewrite supplies the concrete dimension
   `d = 8` (inferred), the packing `E8Packing`, the basis `E8_ℤBasis` (defined
   at E8.lean:582) and the bound `L = 16`. It also leaves two side conditions
   as goals: `hd : 0 < d` (closed inline by `omega`) and `hL` (the `?_`).

2. The first `·` (lines 673-686) is the arithmetic. It substitutes the two
   scalar ingredients `E8Packing_numReps` (`numReps = 1`) and
   `E8_ℤBasis_ofZLatticeBasis_volume` (covolume `= 1`), unfolds `E8Packing`
   (separation `√2`), then closes with `volume_ball`/`finrank_euclideanSpace`
   and `norm_num`/`convert` for the ball-volume identity `√x ^ 8 = x ^ 4`.

3. The second `·` (lines 687-694) discharges `hL`: for `x` in the fundamental
   domain, `‖x‖ ≤ ∑ i, ‖E8_ℤBasis i‖ ≤ 8 · 2 = 16`, using `norm_fract_le` and
   `E8_ℤBasis_apply_norm` for the per-basis-vector bound.

Lemma graph (who uses whom, all in the copied files):

```
E8Packing_density
├── PeriodicSpherePacking.density_eq   (PeriodicPacking.lean:967)
├── E8Packing_numReps                  ── PeriodicSpherePacking.numReps_eq_one (PeriodicPacking.lean:304) + rfl
├── E8_ℤBasis_apply_norm               ── E8Basis_apply_norm (E8.lean:634, self-contained)
│                                         + coe_E8_ℤBasis_apply (594) + E8Basis_apply (314)
└── E8_ℤBasis_ofZLatticeBasis_volume   ── E8Basis_volume (E8.lean:646)
                                            └── E8Matrix_unimodular (294)
                                                └── lowerTriangular_E8Matrix (290, self-contained)
                                          + volume_preimage_toLp_symm (649, private)
                                          + preimage_fundamentalDomain_E8_ℤBasis (656, private)
```

Why each child is a good leaf:

- `PeriodicSpherePacking.density_eq` is self-contained as a statement: its
  proof is one line, `limsSup_eq_of_le_nhds (S.tendsto_finiteDensity b hL hd)`,
  closing from the previously-proved `tendsto_finiteDensity`.
- `E8Packing_numReps` closes by `PeriodicSpherePacking.numReps_eq_one _ rfl`:
  the single hypothesis `S.centers = S.lattice` holds by `rfl` because
  `E8Packing.centers := E8Lattice`.
- `E8_ℤBasis_apply_norm` closes by forwarding to `E8Basis_apply_norm`, which
  is a finite `Fin 8` computation (`simp` + `norm_num`) over the explicit
  `E8Matrix`.
- `E8_ℤBasis_ofZLatticeBasis_volume` closes by one `rw` chain that reduces the
  `E8Lattice` fundamental-domain volume to `E8Basis_volume` (`= 1`).

## Why it is good

1. The parent closes in 23 lines from the four named lemmas, with no `sorry` in
   its dependency cone, and the file is built by the project's CI
   (`check`; E8.lean#L671-L694, `.github/workflows/build.yml` runs `lake build`
   on pushes to main and `SpherePacking.lean` line 3 imports `SpherePacking.Basic.E8`).
2. The blueprint node `E8Packing-density` declares the same two ingredients,
   `\uses{theorem:psp-density,E8Packing-covol}`, and its prose proof is the same
   two-step argument — "By \cref{theorem:psp-density}, we have … where the last
   equality follows from \cref{E8Packing-covol} and the formula for volume of a
   ball" (`author-statement`; E8-defs.tex#L110-L115).
3. The dependency cone below the main theorem is at least depth 5: the
   `density_eq` branch reaches `E8Packing_density → PeriodicSpherePacking.density_eq →
   tendsto_finiteDensity → aux_big_le → SpherePacking.finiteDensity_le →
   inter_ball_encard_ge`, and the volume branch (`E8_ℤBasis_ofZLatticeBasis_volume →
   E8Basis_volume → E8Matrix_unimodular → lowerTriangular_E8Matrix`) is depth 4
   (`measurement`; PeriodicPacking.lean#L967→#L945→#L753, SpherePacking.lean#L458→#L411,
   E8.lean#L668→#L646→#L294→#L290).
4. `PeriodicSpherePacking.density_eq` is reused at two sites in the project — the
   E8 instance and the covolume-free `density_eq'` — so one general statement
   serves two theorems (`measurement`; E8.lean:672 and PeriodicPacking.lean:1152).

In my opinion the detail worth copying is the *choice of bound*: `L = 16` is
picked so that the second branch reduces to `8 · 2 = 16`, the `2` coming from
`E8_ℤBasis_apply_norm`. The instantiation is only as clean as the ingredients it
can substitute, and each ingredient is a separate leaf.

## When to use it, and when not

Use it when a general formula over a whole structure class (here
`PeriodicSpherePacking d`) already exists, and the concrete goal is a
specialisation to one member plus a small number of concrete ingredient values
(`numReps`, covolume, a norm bound) that each have short proofs. The general
lemma's parameters must be supplyable syntactically, and the goal must match the
general formula's left-hand side up to unfolding.

Avoid it when the general statement does not yet exist and has to be proved as
part of the job — then the general proof is the real content and the
"instantiation" is a red herring. Also avoid it when the ingredient values are
many or deep (the short glue hides a large dependency cone), or when the bound
(such as `L`) has to be found by search rather than read off a proved norm lemma.

## Consequences

Instantiating the general formula creates two kinds of obligation: the side
conditions of `density_eq` (`hL`, a norm bound over the fundamental domain, and
`hd : 0 < d`) become subgoals of the rewrite, and each concrete ingredient must
be a separately named, proved lemma. Failure modes: choosing `L` too small makes
`hL` unprovable by the available norm lemmas; the `rw` fires only if the goal's
head matches the general formula's left-hand side; and a deceptively short glue
can hide a dependency cone of depth ≥ 5.

Note: the move `generalise-then-instantiate` is not one of survey F §10's
candidate rules 1-18, so this entry records `rule: none`. That absence is worth
flagging — real projects do assemble headline results this way, and the closest
F §10 rule (17, "memoise canonical statements") captures only the reuse of the
general lemma, not the instantiation step.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml at efe3bbbc (default branch main; commit is HEAD of main per GitHub compare API): push to main runs job build_project -> leanprover/lean-action 'Build the project' (lake build); SpherePacking.lean:3 'public import SpherePacking.Basic.E8' pulls E8.lean into the build | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 3 file(s) byte-identical at efe3bbbc1ece548f4672a772b94d8f621c10fdda | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read E8.lean L671-694: proof body L672-694 = 23 lines; L672 rw [PeriodicSpherePacking.density_eq E8_ℤBasis ?_ (by omega) (L := 16)]; substitutes E8Packing_numReps (L673), E8_ℤBasis_ofZLatticeBasis_volume (L683), E8_ℤBasis_apply_norm (L693). grep for sorry in copied files: only PeriodicPacking.lean:1220 (periodic_constant_eq_constant, not in E8Packing_density dependency cone) and commented '-- sorry' at :1067. build.yml runs lake build on push to main; SpherePacking.lean:3 imports E8 | verifier |
| 2 | verified | Read blueprint/src/subsections/E8-defs.tex L110-L115: L110 '\uses{theorem:psp-density,E8Packing-covol}'; L114 proof reads 'By \cref{theorem:psp-density}, ... where the last equality follows from \cref{E8Packing-covol} and the formula for volume of a ball' | verifier |
| 3 | refuted | The named depth-4 chain does exist (E8.lean:668 -> E8Basis_volume :646-647 -> E8Matrix_unimodular :294-296 -> lowerTriangular_E8Matrix :290-292), but it is not the longest chain below E8Packing_density. The density_eq branch is deeper: E8Packing_density -> PeriodicSpherePacking.density_eq (PeriodicPacking.lean:967-972) -> tendsto_finiteDensity (:945-965) -> aux_big_le (:753, :764) -> SpherePacking.finiteDensity_le (SpherePacking.lean:458, :467) -> inter_ball_encard_ge ..., giving depth >= 5 | verifier |
| 4 | verified | E8.lean:672 'rw [PeriodicSpherePacking.density_eq ...]'; PeriodicPacking.lean:1152 'rw [S.density_eq b hL hd]' (inside density_eq', :1143) — two reuse sites of the one general lemma | verifier |
| 5 | verified | Read copied code. Density branch: E8.lean:671 E8Packing_density calls PeriodicSpherePacking.density_eq at :672; PeriodicPacking.lean:967 density_eq calls S.tendsto_finiteDensity at :972; :945 tendsto_finiteDensity (private) calls aux_big_le at :951; :753 aux_big_le calls S.finiteDensity_le at :764; SpherePacking.lean:458 finiteDensity_le calls S.inter_ball_encard_ge at :467; :411 inter_ball_encard_ge is a leaf => depth 5. Volume branch: E8.lean:666 E8_ZBasis_ofZLatticeBasis_volume calls E8Basis_volume at :668; :646 E8Basis_volume calls E8Matrix_unimodular at :647; :294 E8Matrix_unimodular calls lowerTriangular_E8Matrix at :295; :290 lowerTriangular_E8Matrix is a leaf => depth 4. All line numbers match the claim. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Opened the three copied files. Parent E8Packing_density (E8.lean:671-694) is a single rw [PeriodicSpherePacking.density_eq E8_ℤBasis ?_ (by omega) (L := 16)] (line 672) followed by two closing branches; statement matches entry.json verbatim. The four children are exactly the four project lemmas the glue invokes: density_eq (PeriodicPacking.lean:967-972, used L672), E8Packing_numReps (E8.lean:631-632, used L673), E8_ℤBasis_ofZLatticeBasis_volume (E8.lean:666-668, used L683), E8_ℤBasis_apply_norm (E8.lean:641-643, used L693); no other project lemma is invoked directly. Each closed_by string matches the child proof verbatim: limsSup_eq_of_le_nhds (S.tendsto_finiteDensity b hL hd) (L972), PeriodicSpherePacking.numReps_eq_one _ rfl (L632), the simpa ... E8Basis_apply_norm i (L642-643), and the rw [←volume_preimage_toLp_symm, preimage_fundamentalDomain_E8_ℤBasis, E8Basis_volume] (L668). No sorry/admit in the dependency cone (the only sorry is periodic_constant_eq_constant at PeriodicPacking.lean:1220, outside the cone, and a commented-out block). Shape numbers correct: direct_lemmas=4, depth=5 (verified chain E8Packing_density→density_eq:972→tendsto_finiteDensity:951→aux_big_le:764→finiteDensity_le:467→inter_ball_encard_ge:411; volume branch :668→:647→:295→:292 is depth 4), glue_lines=23 (proof body 672-694), child_lines=[1,1,2,1] (density_eq proof L972, numReps L632, apply_norm L642-643, volume L668). | reviewer-correctness |
| generality | accept | Generality is stated beyond the E8 example: applicability.goal_shape abstracts to 'rw [general_formula c args] then substitute a small number of named concrete ingredient lemmas', and use_when/avoid_when generalise to 'any general formula over a structure class'. 'When not to use' is honest and specific: the avoid_when 'the general statement has to be proved as part of the job' explicitly concedes the entry only captures the instantiate half; 'ingredient values are many or deep' matches the consequence that a short glue hides a depth>=5 dependency cone. Consequences name the two concrete obligations (hL/hd side conditions; one named lemma per ingredient) and concrete failure modes (L too small -> hL unprovable; rw needs syntactic head match). README 'Why each child is a good leaf' states per leaf why it is bounded: 1-2-line proofs closing via a known general lemma or a finite Fin 8 computation. | reviewer-generality |
| provenance-licence | accept | Commit efe3bbbc1ece548f4672a772b94d8f621c10fdda is consistent across entry.json source.commit, sources/sphere-packing/source.json, and SOURCE.md; every permalink (files and sites) points to that same commit with the correct path; licence Apache-2.0 matches entry.json, source.json and SOURCE.md, and upstream-LICENSE is the Apache-2.0 text; check_provenance.py passes (3 files byte-identical at the pinned commit) and local sha256 of E8.lean/PeriodicPacking.lean/SpherePacking.lean equals the entry.json sha256 values. All traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean at commit `efe3bbbc1ece548f4672a772b94d8f621c10fdda`, under `Apache-2.0`; see the [source note](../../sources/sphere-packing/SOURCE.md) for the licence text and attribution.
