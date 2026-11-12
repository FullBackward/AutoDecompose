# Interface lemma is_zero_iff_epi_and_is_iso turns Ext-vanishing into epi + is_iso (Liquid Tensor Theorem 1.1)

| | |
|---|---|
| Kind | instance |
| Move | interface-lemma |
| Language | lean |
| Status | accepted |
| Source | [lean-liquid](../../sources/lean-liquid/SOURCE.md) at `ee4795874a99` |
| Licence | `LicenseRef-unknown` |

## Intent

Reduce the main theorem of the Liquid Tensor Experiment — `Ext i (ℳ_{p'} S) V ≅ 0`
for every `i > 0` — to two separate facts by applying the interface lemma
`is_zero_iff_epi_and_is_iso` to the short exact sequence
`laurent_measures.short_exact`: the Ext-vanishing goal becomes "epi at 0 and
is_iso above 0", which `laurent_measures.epi_and_is_iso` supplies exactly,
leaving only its `T-inv` hypothesis for the glue to discharge.

## The decomposition

### parent `liquid_tensor_experiment`: [`src/challenge.lean` lines 28-43](https://github.com/leanprover-community/lean-liquid/blob/ee4795874a99ea5f9d85bd0b364425f07b932377/src/challenge.lean#L28-L43) ([local copy](code/src/challenge.lean))

```lean
theorem liquid_tensor_experiment (S : Profinite.{0}) (V : pBanach.{0} p) :
  ∀ i > 0, Ext i (ℳ_{p'} S) V ≅ 0 :=
begin
  intros i hi,
  apply is_zero.iso_zero,
  revert i,
  haveI : fact (0 < (p:ℝ)) := ⟨lt_trans (fact.out _ : 0 < p') (fact.out _)⟩,
  haveI : fact (p' < 1) := ⟨lt_of_lt_of_le (fact.out _ : p' < p) (fact.out _)⟩,
  erw is_zero_iff_epi_and_is_iso _ _ (V : Condensed.{0 1 2} Ab) (laurent_measures.short_exact p' S),
  let := pBanach.choose_seminormed_add_comm_group V,
  let := pBanach.choose_normed_with_aut V 2⁻¹,
  haveI : fact (0 < (2⁻¹ : ℝ≥0) ^ (p : ℝ)) := r_pos',
  convert laurent_measures.epi_and_is_iso p' p S ⟨V⟩ _ using 1,
  intro v,
  rw [pBanach.choose_normed_with_aut_T_inv, inv_inv, two_smul, two_nsmul],
end
```

### child `is_zero_iff_epi_and_is_iso`: [`src/for_mathlib/derived/les_facts.lean` lines 77-106](https://github.com/leanprover-community/lean-liquid/blob/ee4795874a99ea5f9d85bd0b364425f07b932377/src/for_mathlib/derived/les_facts.lean#L77-L106) ([local copy](code/src/for_mathlib/derived/les_facts.lean))

```lean
lemma is_zero_iff_epi_and_is_iso
  {A₁ A₂ A₃ : C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (B : C) (h : short_exact f g) :
  (∀ i > 0, is_zero (((Ext' i).obj (op A₃)).obj B)) ↔
  (epi (((Ext' 0).map f.op).app B) ∧ ∀ i > 0, is_iso (((Ext' i).map f.op).app B)) :=
begin
  have LES := λ i, h.Ext'_five_term_exact_seq B i,
  split,
  { intro H,
    split,
    { have := ((LES 0).drop 1).pair,
      refine this.epi_iff_eq_zero.mpr _,
      refine is_zero.eq_of_tgt _ _ _,
      exact H 1 zero_lt_one, },
    { rintro i (hi : 0 < i),
      apply (LES i).is_iso_of_zero_of_zero,
      { refine is_zero.eq_of_src _ _ _,
        exact H i hi, },
      { refine is_zero.eq_of_tgt _ _ _,
        exact H (i+1) (hi.trans $ lt_add_one _), }, } },
  { intros H i hi,
    obtain ⟨i, rfl⟩ : ∃ j, j + 1 = i := ⟨i-1, sub_add_cancel _ _⟩,
    refine is_zero_of_exact_zero_zero' _ _ ((LES i).drop 2).pair _ _,
    { refine ((LES i).drop 1).pair.epi_iff_eq_zero.mp _,
      rw [gt_iff_lt, int.lt_add_one_iff] at hi,
      obtain (rfl|hi) := hi.eq_or_lt,
      { exact H.1 },
      { exact @is_iso.epi_of_iso _ _ _ _ _ (H.2 _ hi), } },
    { refine (LES (i+1)).pair.mono_iff_eq_zero.mp _,
      exact @is_iso.mono_of_iso _ _ _ _ _ (H.2 _ hi), } }
end
```

### child `epi_and_is_iso`: [`src/laurent_measures/ext.lean` lines 28-57](https://github.com/leanprover-community/lean-liquid/blob/ee4795874a99ea5f9d85bd0b364425f07b932377/src/laurent_measures/ext.lean#L28-L57) ([local copy](code/src/laurent_measures/ext.lean))

```lean
lemma epi_and_is_iso
  (V : SemiNormedGroup.{0}) [normed_with_aut r V] [complete_space V] [separated_space V]
  (hV : ∀ (v : V), (normed_with_aut.T.inv v) = 2 • v) :
  epi (((Ext' 0).map ((condensify_Tinv2 (Fintype_LaurentMeasures r')).app S).op).app
    (Condensed.of_top_ab V)) ∧
  ∀ i > 0, is_iso (((Ext' i).map ((condensify_Tinv2 (Fintype_LaurentMeasures r')).app S).op).app
    (Condensed.of_top_ab V)) :=
begin
  have SES := Lbar.short_exact.{0 0} r' S,
  haveI : fact (r < r'),
  { refine ⟨nnreal.rpow_lt_rpow_of_exponent_gt _ _ _⟩,
    { exact fact.out _ },
    { apply nnreal.two_inv_lt_one },
    { norm_cast, exact fact.out _ },
  },
  haveI : fact (r < 1) := ⟨(fact.out _ : r < r').trans (fact.out _)⟩,
  haveI : fact (p' ≤ 1) := ⟨(fact.out _ : p' < p).le.trans (fact.out _)⟩,
  haveI : fact (p' < 1) := ⟨lt_of_lt_of_le (fact.out _ : p' < p) (fact.out _ : p ≤ 1)⟩,
  rw ← epi_and_is_iso_iff_of_is_iso _ _ _ _
    ((condensify_Tinv2 _).app S) ((condensify_Tinv2 _).app S) ((condensify_Tinv2 _).app S)
    _ _ (Condensed.of_top_ab V) SES SES (Lbar.is_iso_Tinv2 r r' S V hV),
  { rw ← is_zero_iff_epi_and_is_iso _ _ (Condensed.of_top_ab V) (invpoly.short_exact p' S),
    intros i hi,
    apply (free_pfpng_acyclic S V i hi).of_iso _,
    apply iso.app _ _,
    refine (Ext' i).map_iso _,
    exact (as_iso ((cond_free_pfpng_to_normed_free_pfpng.{0 0} p').app S)).op, },
  { rw [← nat_trans.comp_app, condensify_map_comp_Tinv2, nat_trans.comp_app], },
  { rw [← nat_trans.comp_app, condensify_map_comp_Tinv2, nat_trans.comp_app], }
end
```

### child `short_exact`: [`src/laurent_measures/ses2.lean` lines 71-155](https://github.com/leanprover-community/lean-liquid/blob/ee4795874a99ea5f9d85bd0b364425f07b932377/src/laurent_measures/ses2.lean#L71-L155) ([local copy](code/src/laurent_measures/ses2.lean))

```lean
theorem short_exact (S : Profinite) :
  short_exact ((condensify_Tinv2 _).app S) ((condensify_map $ Θ_fintype_nat_trans p).app S) :=
begin
  refine condensify_nonstrict_exact _ _ (r⁻¹ + 2) (Tinv2_bound_by _)
    -- C₂ bound (note that `2⁻¹ < r < 1` implies the max is always the left term)
    (λ c, max (c * ( r⁻¹ + 2) * ( 2 - r⁻¹)⁻¹) c)
    -- C₄ bound (note that `2⁻¹ < r < 1` implies that the max is always the left term)
    (λ c, max ((1 - r)⁻¹ * c) c)
    -- if you want to remove `max` from C₂ then you do that here
    (λ c, le_max_right _ c)
    -- if you want to remove `max` from C₄ then you do that here
    (λ c, le_max_right _ c)
    (λ S, injective_ϕ')
    (λ S, by { ext1 F, apply θ_ϕ_complex }) _ _ _,

    -- now two goals left, basically corresponding to
    -- existence of a bounded splitting of ϕ (namely ψ)
    -- and existence of a bounded splitting of θ
    -- (namely binary expansion).

    -- Here's a proof of the ϕ goal using ψ.
    { clear S,
      -- change to unbundled language
      rintros S c' (F : laurent_measures r S) ⟨(hF1 : Θ p S F = 0),
        (hF2 : ∥F∥₊ ≤ c')⟩,
      simp only [set.mem_image],
      refine ⟨ψ F hF1, _, θ_ϕ_split_exact F hF1⟩,
      change (∥_∥₊ : ℝ≥0) ≤ _,
      -- because of silly definition of `C₂` involving max :-)
      refine le_trans _ (mul_le_mul_right' (le_max_left _ _) _),
      convert psi_bound p S c' hF1 hF2 using 1,
      have h1 : 2⁻¹ < r := half_lt_r,
      have h2 : (2 - 1 / r) ≠ 0 := ne_of_gt (tsub_pos_of_lt
        (by { rw [one_div], exact r_inv_lt_2 })),
      have h3 : r ≠ 0 := ne_of_gt r_pos,
      field_simp,
      simp [mul_tsub, tsub_mul, one_div, mul_assoc, mul_inv_cancel h3],
      ring_nf, },
  -- Now here's a proof of the θ goal using binary expansions
    { clear S,
      rintros S c' (f : real_measures p S) (hf : _ ≤ _),
      let measure_aux : laurent_measures r S :=
      { to_fun := λ s n,
        if 0 ≤ f s then nnreal.int.binary (∥f s∥₊) n
        else -nnreal.int.binary (∥f s∥₊) n,
        summable' := λ s, begin
          convert nnreal.int.binary_summable (∥f s∥₊) (r_lt_one : r < 1),
          ext,
          split_ifs;
          simp,
        end },
      refine ⟨measure_aux, _⟩,
      change _ ≤ _ ∧ _,
      split,
      { refine le_trans _ (le_max_left _ _),
        refine le_trans _ (mul_le_mul_of_nonneg_left hf zero_le'),
        change finset.sum _ _ ≤ _ * finset.sum _ _,
        rw finset.mul_sum,
        refine finset.sum_le_sum (λ s _, _),
        rcases (eq_zero_or_pos : ∥f s∥₊ = 0 ∨ _) with (h0 | hpos),
        { simp [h0, measure_aux] },
        { convert le_trans (theta_aux_lemma.tsum_le
            (∥f s∥₊) (r_pos : 0 < r) (r_lt_one : r < 1)) _,
          { ext n, congr', dsimp [measure_aux], split_ifs; simp },
          { rw mul_comm,
            apply nnreal.mul_le_mul_left,
            rw ← nnreal.rpow_int_cast,
            convert nnreal.rpow_le_rpow_of_exponent_ge
              (r_pos : 0 < r) (r_lt_one.le) (int.le_ceil _) using 1,
            delta «r»,
            rw [← nnreal.rpow_mul, mul_comm, nnreal.rpow_mul],
            congr', symmetry,
            rw ← nnreal.coe_eq,
            exact nnreal.pow_log_div_log_self hpos (by norm_num) (by norm_num), } } },
      { delta Θ_fintype_nat_trans Θ θ_to_add θ theta.ϑ,
        dsimp,
        ext s,
        split_ifs,
        { convert nnreal.coe_eq.2 (nnreal.int.binary_sum ∥f s∥₊),
          push_cast, rw real.nnnorm_of_nonneg h, refl, },
        { convert neg_inj.2 (nnreal.coe_eq.2 (nnreal.int.binary_sum ∥f s∥₊)),
          { push_cast, rw ← tsum_neg, congr', ext, simp },
          { push_neg at h,
            rw real.neg_nnnorm_of_neg h, } } } },
end
```

### context `notations`: [`src/challenge_notations.lean` lines 36-43](https://github.com/leanprover-community/lean-liquid/blob/ee4795874a99ea5f9d85bd0b364425f07b932377/src/challenge_notations.lean#L36-L43) ([local copy](code/src/challenge_notations.lean))

```lean
localized "notation `ℳ_{` p' `}` S := (@real_measures.condensed p' _ (by fact_arith)).obj S"
  in liquid_tensor_experiment

abbreviation liquid_tensor_experiment.Ext (i : ℤ) (A B : Condensed.{u} Ab.{u+1}) :=
((Ext' i).obj (op A)).obj B

instance : has_coe (pBanach.{u} p) (Condensed.{u} Ab.{u+1}) :=
{ coe := λ V, Condensed.of_top_ab V }
```

How the parts fit. The parent `liquid_tensor_experiment` (`src/challenge.lean:28`)
is Theorem 1.1 of the blogpost; `ℳ_{p'} S` is the condensed space of p'-measures
(`challenge_notations.lean:36`) and `Ext` abbreviates `((Ext' i).obj (op A)).obj B`
(`challenge_notations.lean:39`). The glue (14 lines, `challenge.lean:30-43`) first
turns the `≅ 0` into `is_zero` (`apply is_zero.iso_zero`, line 32), then — this is
the interface step — rewrites the whole goal with `erw is_zero_iff_epi_and_is_iso …
(laurent_measures.short_exact p' S)` (line 36). That one step changes the goal from
"all Ext^i vanish" into "`epi` at 0 and `is_iso` above 0", using `short_exact` to
supply the `h : short_exact f g` the interface lemma demands. The glue then hands
that exact goal to `laurent_measures.epi_and_is_iso` (`convert … using 1`, line 40)
and discharges the one remaining hypothesis `hV : ∀ v, T.inv v = 2 • v` in lines
41-42. The `let :=`/`haveI` lines 34-39 are instance plumbing (the `p`-Banach
space's seminorm and normed-with-automorphism structures) so that `epi_and_is_iso`
applies.

The lemma graph (which lemma uses which, one level down from the main theorem):

```
liquid_tensor_experiment (challenge.lean:28)
├── is_zero_iff_epi_and_is_iso (les_facts.lean:77)   the interface lemma
│     └── h.Ext'_five_term_exact_seq (defined les3.lean:420)
├── laurent_measures.short_exact (ses2.lean:71)       supplies h : short_exact f g
└── laurent_measures.epi_and_is_iso (ext.lean:28)     supplies epi + is_iso
      ├── epi_and_is_iso_iff_of_is_iso (les_facts.lean:108)
      ├── Lbar.short_exact / Lbar.is_iso_Tinv2 / invpoly.short_exact
      ├── is_zero_iff_epi_and_is_iso (les_facts.lean:77)   reused, on invpoly.short_exact
      └── free_pfpng_acyclic
```

Why each child is a good leaf. `is_zero_iff_epi_and_is_iso` is a self-contained
statement over an abelian category with enough projectives: its proof builds the
five-term exact sequence from `h` and chases it in both directions, closing on its
own with no further project lemma. `short_exact` is a self-contained statement that
the two condensified maps form a short exact sequence, closed by
`condensify_nonstrict_exact` plus two bounded-splitting sub-proofs (via `ψ` and via
binary expansion). `epi_and_is_iso` closes from named siblings — `Lbar.short_exact`,
`Lbar.is_iso_Tinv2`, `epi_and_is_iso_iff_of_is_iso`, `invpoly.short_exact`,
`free_pfpng_acyclic` — and the same interface lemma. So each leaf either closes on
its own or from named project siblings, which is the shape AutoDecompose must
produce: a skeleton with one hole per bounded prover.

## Why it is good

1. The parent closes from the three named children in 14 proof lines: line 36
   applies the interface lemma to `short_exact`, line 40 hands the result to
   `epi_and_is_iso`, and lines 41-42 discharge the `hV` side condition
   (`check`, `challenge.lean#L28-L43`; CI builds it with `lean --json --make src`
   and runs `ensure_lte_sorry_free.py`).
2. The interface lemma is applied at two sites, not one: in the main theorem
   (`challenge.lean:36`) and inside its own sibling `epi_and_is_iso`
   (`ext.lean:49`), on two different short exact sequences (`measurement`, grep
   for `is_zero_iff_epi_and_is_iso`).
3. The project README names this theorem as the project's main target — "The
   formal statement of `Theorem 1.1` … can be found in
   [`src/challenge.lean`](…#L28)" (`author-statement`, `README.md#L45-L54`).
4. None of the four files carries `sorry`, `admit` or `axiom`, so the glue and
   all three children close without holes (`check`, grep over the copied files;
   the CI `test` job enforces the same).
5. The longest chain of project lemmas below the main theorem has depth at least
   3: `liquid_tensor_experiment` → `epi_and_is_iso` → `epi_and_is_iso_iff_of_is_iso`
   → `Ext'_five_term_exact_seq` (`measurement`, the call chain
   `challenge.lean#L40` → `ext.lean#L46` → `les_facts.lean#L120` → `les3.lean#L420`).

In my opinion the detail worth copying is that the interface lemma is an *iff* that
lets the glue stop reasoning about `Ext`/`is_zero` altogether and instead target an
`epi`/`is_iso` statement a dedicated lemma already proves; the reuse at `ext.lean:49`
is what makes it a genuine interface rather than a one-off restatement.

## When to use it, and when not

Use it when the goal is an Ext-vanishing (or any "all terms of a cohomology theory
vanish") statement for which you already have, or can prove, a short exact sequence,
and a separate argument proves the epi + is_iso form. The interface lemma is an iff,
so it pays for itself the second time it is applied (here: `challenge.lean:36` and
`ext.lean:49`). Avoid it when no short exact sequence is available to supply the
`h : short_exact f g` argument; when the epi/is_iso form is no easier than the
original vanishing (you would just re-derive it by the same five-term chase); or when
the Ext-vanishing is itself the object of study rather than a stepping stone to a
concrete epi/is_iso fact.

## Consequences

The move changes the goal from a quantified Ext-vanishing to an epi/is_iso
statement, so it creates obligations: a short exact sequence (`short_exact`), a lemma
that proves the epi/is_iso form (`epi_and_is_iso`), and every hypothesis that lemma
needs (`hV : T.inv v = 2 • v`, discharged by two lines of rewriting). The interface
only speaks for `i > 0`, so the `i = 0` term is split out as `epi` rather than
`is_iso` — a client must not read "is_iso above 0" as "is_iso everywhere". Finally,
because `epi_and_is_iso` reuses the same interface lemma on a different short exact
sequence (`invpoly.short_exact`), the three children are not independent: changing
the interface lemma changes both the glue and the `epi_and_is_iso` child.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml build job runs 'lean --json --make src' (line 86), which compiles src/challenge.lean and the other copied files; commit ee4795874a99ea5f9d85bd0b364425f07b932377 is the HEAD/default-branch (master) tip at registration; 'test' job runs scripts/ensure_lte_sorry_free.py | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 6 file(s) byte-identical at ee4795874a99ea5f9d85bd0b364425f07b932377 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read local copy code/src/challenge.lean: line 28 states liquid_tensor_experiment; proof block is lines 30-43 (14 lines); line 36 'erw is_zero_iff_epi_and_is_iso ... (laurent_measures.short_exact p' S)'; line 40 'convert laurent_measures.epi_and_is_iso p' p S ⟨V⟩ _ using 1'; lines 41-42 'intro v' then rw discharge hV. CI build.yml line 86 'lean --json --make src' builds the file. | verifier |
| 2 | verified | Grep of code/ for 'is_zero_iff_epi_and_is_iso' returns exactly two call sites: code/src/challenge.lean:36 (with laurent_measures.short_exact) and code/src/laurent_measures/ext.lean:49 (with invpoly.short_exact); the definition is code/src/for_mathlib/derived/les_facts.lean:77. | verifier |
| 3 | verified | Fetched README.md at ee4795874: line 45 section 'The formal statement of Theorem 1.1', line 47 'The statement can be found in [src/challenge.lean](.../blob/master/src/challenge.lean#L28)'; line 20 'The challenge in the blog post is to formalise its Theorem 1.1, a variant of Analytic 9.1'. | verifier |
| 4 | verified | Grep for 'sorry|admit|axiom' over code/ returned no matches (covers challenge.lean, les_facts.lean, ext.lean, ses2.lean). CI .github/workflows/build.yml 'test' job runs 'python scripts/ensure_lte_sorry_free.py' (line 176). | verifier |
| 5 | verified | Chain confirmed: challenge.lean:40 calls laurent_measures.epi_and_is_iso (ext.lean:28); ext.lean:46 'rw ← epi_and_is_iso_iff_of_is_iso' (les_facts.lean:108); les_facts.lean:120 'have H1 := λ i, hf.Ext'_five_term_exact_seq Z i'; definition at les3.lean:420 'lemma Ext'_five_term_exact_seq'. Depth 3 edges. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Shape numbers verified against code: direct_lemmas=3 (glue uses is_zero_iff_epi_and_is_iso at challenge.lean:36, laurent_measures.short_exact at :36, laurent_measures.epi_and_is_iso at :40 — exactly the three children, no other project lemma used); depth=3 (challenge.lean:40 -> ext.lean:46 epi_and_is_iso_iff_of_is_iso -> les_facts.lean:120 Ext'_five_term_exact_seq); glue_lines=14 (challenge.lean begin..end 30-43); child_lines=[26,23,83] (les_facts.lean:81-106, ext.lean:35-57, ses2.lean:73-155). Children statements and closed_by match code: is_zero_iff_epi_and_is_iso chased via h.Ext'_five_term_exact_seq with epi_iff_eq_zero/is_iso_of_zero_of_zero/is_zero_of_exact_zero_zero'/epi_of_iso/mono_of_iso; epi_and_is_iso via epi_and_is_iso_iff_of_is_iso + Lbar.short_exact + Lbar.is_iso_Tinv2 + invpoly.short_exact + free_pfpng_acyclic + condensify_map_comp_Tinv2; short_exact via condensify_nonstrict_exact + psi/theta_aux_lemma.tsum_le/nnreal.int.binary_sum. All four files close with no sorry/admit/axiom. | reviewer-correctness |
| generality | accept | Move generalises beyond the example: applicability.goal_shape/use_when restate it as 'an Ext-vanishing (or any all-terms-of-a-cohomology-theory-vanish) statement' with a short exact sequence in hand, and the reuse measurement (claim 2: two call sites) grounds the 'pays for itself on the second use' advice. when-not-to-use is honest and specific (no SES available; epi/iso form no easier than the same five-term chase; vanishing is the object of study not a stepping stone). Consequences are honest and specific: the i=0 term splits as epi not is_iso (client must not read 'is_iso everywhere'), and the three children are non-independent because epi_and_is_iso reuses the same interface lemma. 'Why each child is a good leaf' states what makes them good bounded-prover leaves: each closes on its own (five-term chase) or from named project siblings, one hole per bounded prover. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are all consistent and traceable. check_provenance.py passes: the 6 copied files are byte-identical at the pinned commit ee4795874a99ea5f9d85bd0b364425f07b932377, matching both entry.json (source.commit, file permalinks, sha256) and sources/lean-liquid/SOURCE.md (same commit, same repository URL). Licence is recorded as LicenseRef-unknown in entry.json, README 'Source and licence', and SOURCE.md consistently; I confirmed via list_files.py lean-liquid that no LICENSE/COPYING file exists at the root or anywhere in the tree, so 'unknown' is the honest tag per protocol decision 1. Every file and site permalink points at the pinned commit with line anchors, and the entry README states files are copied whole/unmodified from that commit, matching the provenance result. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover-community/lean-liquid at commit `ee4795874a99ea5f9d85bd0b364425f07b932377`, under `LicenseRef-unknown`; see the [source note](../../sources/lean-liquid/SOURCE.md) for the licence text and attribution.
