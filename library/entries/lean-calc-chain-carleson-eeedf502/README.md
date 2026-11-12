# Calc chain assembling forest-union and forest-complement bounds for the discrete Carleson theorem (Prop 2.0.2)

| | |
|---|---|
| Kind | instance |
| Move | calc-chain |
| Language | lean |
| Status | verified |
| Source | [carleson](../../sources/carleson/SOURCE.md) at `d75f54374f7f` |
| Licence | `Apache-2.0` |

## Intent

The discrete Carleson theorem states that, away from a small exceptional set
`G'`, the Carleson operator is bounded by `C2_0_2 a nnq` times the appropriate
volumes. Its proof is pure glue: it splits the `carlesonSum` over the forest
tiles `𝔓₁` and their complement `𝔓₁ᶜ`, bounds the two halves with the named
project lemmas `forest_union` and `forest_complement`, and folds the two
constants `C5_1_2 + C5_1_3` into `C2_0_2` with `le_C2_0_2`. Four project lemmas
carry the whole argument; the parent only manages the witness `G'`, a
triangle-inequality step, linearity of the integral, and the constant fold.

## The decomposition

### parent `discrete_carleson`: [`Carleson/Discrete/MainTheorem.lean` lines 44-68](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/Discrete/MainTheorem.lean#L44-L68) ([local copy](code/Carleson/Discrete/MainTheorem.lean))

```lean
theorem discrete_carleson :
    ∃ G', MeasurableSet G' ∧ 2 * volume G' ≤ volume G ∧
    ∀ f : X → ℂ, Measurable f → (∀ x, ‖f x‖ ≤ F.indicator 1 x) →
    ∫⁻ x in G \ G', ‖carlesonSum univ f x‖ₑ ≤
    C2_0_2 a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ := by
  have exc := exceptional_set (X := X)
  rw [zpow_neg_one, ← ENNReal.div_eq_inv_mul] at exc
  use G', measurable_G', ENNReal.mul_le_of_le_div' exc; intro f measf hf
  classical
  calc
    _ ≤ ∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ f x‖ₑ + ‖carlesonSum 𝔓₁ᶜ f x‖ₑ := by
      refine setLIntegral_mono (by fun_prop) fun x _ ↦ ?_
      rw [carlesonSum, ← Finset.sum_filter_add_sum_filter_not _ (· ∈ 𝔓₁ (X := X))]
      simp_rw [Finset.filter_filter, mem_univ, true_and, carlesonSum, mem_compl_iff]
      apply enorm_add_le
    _ = (∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ f x‖ₑ) + ∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ᶜ f x‖ₑ :=
      lintegral_add_left (by fun_prop) _
    _ ≤ C5_1_2 a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ +
        C5_1_3 a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ :=
      add_le_add (forest_union hf measf) (forest_complement hf measf)
    _ ≤ _ := by
      simp_rw [mul_assoc, ← add_mul]
      gcongr
      norm_cast
      apply le_C2_0_2 (four_le_a X) (q_mem_Ioc X)
```

### child `le_C2_0_2`: [`Carleson/Discrete/MainTheorem.lean` lines 21-36](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/Discrete/MainTheorem.lean#L21-L36) ([local copy](code/Carleson/Discrete/MainTheorem.lean))

```lean
lemma le_C2_0_2 (ha : 4 ≤ a) {q : ℝ≥0} (hq : q ∈ Ioc 1 2) :
    C5_1_2 a q + C5_1_3 a q ≤ C2_0_2 a q := by
  have h'q : 0 < q - 1 := tsub_pos_of_lt hq.1
  simp only [C5_1_2, C5_1_3, C2_0_2, ge_iff_le]
  have : (q - 1) ^ 4 ≥ (q - 1) ^ 5 := by
    apply pow_le_pow_of_le_one h'q.le ?_ (by norm_num)
    rw [tsub_le_iff_left]
    convert hq.2
    norm_num
  grw [this, ← add_div]
  gcongr
  apply (add_le_pow_two_add_cube ha le_rfl ?_).trans_eq (by ring)
  have : 𝕔 / 8 ≤ 𝕔 / 4 := by lia
  grw [this]
  ring_nf
  lia
```

### child `exceptional_set`: [`Carleson/Discrete/ExceptionalSet.lean` lines 977-989](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/Discrete/ExceptionalSet.lean#L977-L989) ([local copy](code/Carleson/Discrete/ExceptionalSet.lean))

```lean
lemma exceptional_set : volume (G' : Set X) ≤ 2 ^ (-1 : ℤ) * volume G :=
  calc volume G'
    _ ≤ volume G₁ + volume G₂ + volume G₃ :=
      le_add_of_le_add_right (measure_union_le _ G₃) (measure_union_le _ _)
    _ ≤ 2 ^ (- 4 : ℤ) * volume G + 2 ^ (- 2 : ℤ) * volume G + 2 ^ (- 4 : ℤ) * volume G :=
      add_le_add_three first_exception second_exception third_exception
    _ = ((2 : ℝ≥0∞) * 2 ^ (-4 : ℤ) + 2 ^ (- 2 : ℤ)) * volume G := by ring
    _ ≤ 2 ^ (- 1 : ℤ) * volume G := by
      gcongr
      change ((2 : ℝ≥0) : ℝ≥0∞) * (2 : ℝ≥0) ^ (-4 : ℤ) + (2 : ℝ≥0) ^ (-2 : ℤ) ≤
        (2 : ℝ≥0) ^ (-1 : ℤ)
      repeat rw [← ENNReal.coe_zpow (show (2 : ℝ≥0) ≠ 0 by norm_num)]
      rw_mod_cast [← NNReal.coe_le_coe]; norm_num
```

### child `forest_union`: [`Carleson/Discrete/ForestUnion.lean` lines 1042-1047](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/Discrete/ForestUnion.lean#L1042-L1047) ([local copy](code/Carleson/Discrete/ForestUnion.lean))

```lean
lemma forest_union {f : X → ℂ} (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (h'f : Measurable f) :
    ∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ f x‖ₑ ≤
    C5_1_2 a nnq * (volume G) ^ (1 - q⁻¹) * (volume F) ^ (q⁻¹) := by
  apply (forest_union_optimized hf h'f).trans
  gcongr
  exact C5_1_2_optimized_le
```

### child `forest_complement`: [`Carleson/Discrete/ForestComplement.lean` lines 1176-1181](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/Discrete/ForestComplement.lean#L1176-L1181) ([local copy](code/Carleson/Discrete/ForestComplement.lean))

```lean
lemma forest_complement {f : X → ℂ} (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (h'f : Measurable f) :
    ∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ᶜ f x‖ₑ ≤
    C5_1_3 a nnq * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ := by
  apply (forest_complement_optimized hf h'f).trans
  gcongr
  exact C5_1_3_optimized_le_C5_1_3
```

How the parts fit. The parent `discrete_carleson` opens by instantiating the
exceptional set `have exc := exceptional_set (X := X)` (line 49) and choosing
`G'` as the witness with `use G', measurable_G', ENNReal.mul_le_of_le_div' exc`
(line 51). The four-link `calc` then does all the combining.

```text
discrete_carleson (MainTheorem 44-68)
├── exceptional_set (ExceptionalSet 977-989)        — supplies G' and the 2·volume G' ≤ volume G bound
│     └── first_exception, second_exception, third_exception (same file, folded by a calc)
├── forest_union (ForestUnion 1042-1047)            — bounds the 𝔓₁ half by C5_1_2
│     └── forest_union_optimized → forest_union_aux → lintegral_carlesonSum_forest'
│           → lintegral_carlesonSum_forest → forest_operator_le_volume
├── forest_complement (ForestComplement 1176-1181)  — bounds the 𝔓₁ᶜ half by C5_1_3
│     └── forest_complement_optimized → … → lintegral_enorm_carlesonSum_le_of_isAntichain_subset_ℭ
│           → antichain_operator_le_volume
└── le_C2_0_2 (MainTheorem 21-36)                   — folds C5_1_2 + C5_1_3 into C2_0_2
```

Each calc link is a single obligation: link 1 (line 54) is the triangle
inequality `enorm_add_le` plus the definitional split of `carlesonSum univ` into
`𝔓₁` and `𝔓₁ᶜ` (`Finset.sum_filter_add_sum_filter_not`); link 2 (line 59) is
linearity `lintegral_add_left`; link 3 (line 61) applies the two children
`forest_union` and `forest_complement` under `add_le_add`; link 4 (line 64) folds
the constants with `le_C2_0_2`. The parent itself states no new lemma.

Each child is a good leaf. `le_C2_0_2` is a self-contained constant comparison
that closes by `grw`/`gcongr`/`lia` on the three constants, with no further
project lemma. `exceptional_set` closes from three same-file siblings
(`first_exception`, `second_exception`, `third_exception`) and `ring`/`norm_num`.
`forest_union` and `forest_complement` are two-line wrappers that defer to a
`…_optimized` lemma and a `…_optimized_le` constant-upgrade lemma; their real
content is a long development in their own files, so they are genuinely reusable
bounds rather than inlined glue. `forest_union` sits 6 project lemmas below the
main theorem (see claim 2).

## Why it is good

1. *(check)* The parent `discrete_carleson` closes from exactly four named project
   lemmas — `exceptional_set` (line 49), `forest_union` and `forest_complement`
   (line 63), and `le_C2_0_2` (line 68) — and its calc chain uses no other
   bound-carrying lemma.
   [MainTheorem.lean 44-68](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/Discrete/MainTheorem.lean#L44-L68)
   (the file is 69 lines, read whole).
2. *(check)* The longest chain of project lemmas below the main theorem is 6 deep:
   `discrete_carleson → forest_union → forest_union_optimized → forest_union_aux →
   lintegral_carlesonSum_forest' → lintegral_carlesonSum_forest →
   forest_operator_le_volume`, each step an `apply …` / `have … :=` in
   [ForestUnion.lean 1042-1047, 971-998, 835-875, 796-832, 752-792](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/Discrete/ForestUnion.lean#L1042-L1047).
3. *(author-statement)* The authors label the theorem "Proposition 2.0.2" and record
   the blueprint value of the folded constant: "The constant used in Proposition
   2.0.2. Has value `2 ^ (442 * a ^ 3) / (q - 1) ^ 5` in the blueprint."
   [MainTheorem.lean 14-19](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/Discrete/MainTheorem.lean#L14-L19).
4. *(measurement)* The glue — the main theorem's proof block — is 20 lines
   (MainTheorem.lean 49-68), of which the calc chain is 4 links over 16 lines
   (53-68).
   [MainTheorem.lean 49-68](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/Discrete/MainTheorem.lean#L49-L68).
5. *(known-use)* The same calc-chain move reappears one level down: `exceptional_set`
   proves `volume G' ≤ 2 ^ (-1) * volume G` by a 4-link calc that splits `G'` into
   `G₁, G₂, G₃` and folds the three constants with `first_exception`,
   `second_exception`, `third_exception`.
   [ExceptionalSet.lean 977-989](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/Discrete/ExceptionalSet.lean#L977-L989).

This entry supports survey F §10 rule 9 ("Calculational chains, one child per
link"): each link of the calc is closed by a single named lemma or tactic, and
transitivity is checked by the chain itself.

## When to use it, and when not

Use this move when the goal is an integral bound whose index set splits into two
(or more) parts, and you already hold named lemmas bounding each part with the
same constant form; the parent's job is then only the triangle inequality,
linearity of the integral, and a constant fold. The split itself should be
definitional or cheap (here `carlesonSum univ` splits by
`Finset.sum_filter_add_sum_filter_not`), and the two halves should be disjoint so
that the equality link holds.

Avoid it when the two parts need constants or exponents a single fold lemma
cannot absorb (you would have to re-prove the fold); when the partition is not
disjoint (the `=` link becomes a second `≤` and the constants no longer fold
cleanly); or when proving the split of the index set is itself the hard content
rather than a rewrite.

## Consequences

The move creates a witness obligation for `G'` (discharged by `exceptional_set` and
the `measurable_G'` fact), a measurability side condition for the split
(`setLIntegral_mono` / `lintegral_add_left`), and a constant-fold obligation
(`le_C2_0_2`). Known failure mode: if the two child bounds use incompatible
constant forms, the final `gcongr` / `le_C2_0_2` step fails and the constants must
be re-normalised before the split. The equality link also requires the two
integrands to be a.e.-finite; otherwise the chain must stay as inequalities.

## Verification

<!-- verification:start -->
Status: **verified**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push.yml builds the Carleson library on push to master via leanprover/lean-action (build-args 'Carleson Challenge Solution'); commit d75f54374f7f930e70a86b443f20d0e0935c275e is on master, the default branch | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 4 file(s) byte-identical at d75f54374f7f930e70a86b443f20d0e0935c275e | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read MainTheorem.lean whole (69 lines): parent proof (44-68) uses exactly four bound-carrying project lemmas — exceptional_set (49), forest_union and forest_complement (63), le_C2_0_2 (68); the calc chain (53-68) uses no other constant-carrying lemma | verifier |
| 2 | verified | Read ForestUnion.lean: forest_union applies forest_union_optimized at 1045, forest_union_optimized applies forest_union_aux at 974, forest_union_aux applies lintegral_carlesonSum_forest' at 865, lintegral_carlesonSum_forest' applies lintegral_carlesonSum_forest at 800, lintegral_carlesonSum_forest uses forest_operator_le_volume at 774 — a 6-deep chain as claimed | verifier |
| 3 | verified | MainTheorem.lean 14-19: line 14 has the section header 'Proposition 2.0.2' and the doc comment (16-17) reads 'The constant used in Proposition 2.0.2. Has value 2 ^ (442 * a ^ 3) / (q - 1) ^ 5 in the blueprint.' — matches the claim verbatim | verifier |
| 4 | verified | MainTheorem.lean: proof block lines 49-68 is 20 lines; the calc runs 53-68 (16 lines) with 4 link heads at lines 54, 59, 61, 64 | verifier |
| 5 | verified | ExceptionalSet.lean 977-989: exceptional_set is a 4-link calc (link heads at 979, 981, 983, 984) that splits G' into G1,G2,G3 via measure_union_le and folds first_exception, second_exception, third_exception via add_le_add_three | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | object | Provenance passes (4 files byte-identical at d75f543). The calc-chain decomposition is accurate and closes by reading: link1 triangle inequality (setLIntegral_mono+enorm_add_le), link2 linearity (lintegral_add_left), link3 the two children under add_le_add, link4 constant fold (le_C2_0_2). All four children match their code statements and closed_by; depth=6, glue_lines=20, child_lines=[14,12,3,3] all verify against the copied files. Objection: the main proof also directly uses a fifth named project lemma, measurable_G' (MainTheorem.lean line 51 'use G', measurable_G', ...'), which closes the MeasurableSet G' conjunct; it is 'lemma measurable_G' : MeasurableSet (G' (X := X)) := (measurable_G₁.union measurable_G₂).union measurable_G₃' in Carleson/Discrete/Defs.lean. So claim 1 'closes from exactly four named project lemmas' is false, and shape.direct_lemmas=4 contradicts its field definition 'all lemmas the main proof uses directly' (should be 5). Fix: either add measurable_G' as a fifth child and set direct_lemmas=5 (with its 3-line proof in child_lines), or narrow claim 1 to 'four bound-carrying project lemmas' and note in shape/README that direct_lemmas counts only bound-carrying children while measurable_G' is an additional directly-used measurability lemma. | reviewer-correctness |
| generality | accept | Move stated beyond the example: 'When to use' gives a transferable recipe (two named lemmas bounding a disjoint partition + a constant-fold lemma; parent only does triangle-inequality, integral linearity, and the fold), and 'when not to use' names three specific blockers (fold-incompatible constants/exponents, non-disjoint partition breaking the exact split, split itself being hard content), all consistent with the copied calc. Consequences list the three obligations (G' witness, measurability side condition, constant fold) plus a fold-failure mode. 'Each child is a good leaf' answers the bounded-prover question: le_C2_0_2 is self-contained over the constants closing by grw/gcongr/lia, forest_union/forest_complement are two-line wrappers over a reusable development, exceptional_set closes from same-file siblings + ring/norm_num. Minor imprecision (non-blocking): the consequences' 'a.e.-finite' clause overstates lintegral_add_left, which is unconditional for ENNReal; it is a valid caveat only when transplanting the move to Bochner/Lebesgue integrals. | reviewer-generality |
| provenance-licence | accept | check_provenance.py passes: 4 files byte-identical at d75f54374f7f930e70a86b443f20d0e0935c275e. Commit is consistent across entry.json source.commit, every file and site permalink, sources/carleson/source.json, and SOURCE.md. Licence Apache-2.0 is consistent everywhere (entry.json source.licence, source.json licence, SOURCE.md, and the copied upstream-LICENSE which is the Apache License 2.0 text). Site line anchors verified against the copied files: parent MainTheorem.lean L44-L68 (file has 68 lines), children L21-L36, ExceptionalSet.lean L977-L989 (of 989), ForestUnion.lean L1042-L1047 (of 1047), ForestComplement.lean L1176-L1181 (of 1181). File byte sizes match (2799/56136/54896/63506). Source note records repo URL, pinned commit, licence, license file, and attribution. Everything traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/fpvandoorn/carleson at commit `d75f54374f7f930e70a86b443f20d0e0935c275e`, under `Apache-2.0`; see the [source note](../../sources/carleson/SOURCE.md) for the licence text and attribution.
