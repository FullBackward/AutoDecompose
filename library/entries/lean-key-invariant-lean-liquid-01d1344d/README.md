# Key invariant: dual normed snake lemma for column exactness (Theorem 9.5)

| | |
|---|---|
| Kind | instance |
| Move | key-invariant |
| Language | lean |
| Status | accepted |
| Source | [lean-liquid](../../sources/lean-liquid/SOURCE.md) at `ee4795874a99` |
| Licence | `LicenseRef-unknown` |
| Licence recorded | 2026-11-14T09:32:32Z |

## Intent

Prove that the column complex `double_complex.col'` is weakly bounded-exact by
reducing to one key auxiliary statement, `weak_normed_snake_dual` (the dual
normed snake lemma). The glue assembles that lemma's seven hypotheses from
named lemmas — the scaled column complex, the isometry and
surjectivity-with-bound of `T_inv_sub_Tinv`, and the connecting morphism
`col_ι` — then weakens the resulting constants to the target ones with
`is_weak_bounded_exact.of_le`.

## The decomposition

### parent `col_exact'`: [`src/thm95/col_exact.lean` lines 1257-1302](https://github.com/leanprover-community/lean-liquid/blob/ee4795874a99ea5f9d85bd0b364425f07b932377/src/thm95/col_exact.lean#L1257-L1302) ([local copy](code/src/thm95/col_exact.lean))

```lean
lemma col_exact' [normed_with_aut r V] [fact (r < 1)]
  (d : ℝ≥0) [pseudo_normed_group.splittable (Λ →+ M) N d]
  (k : ℝ≥0) [fact (1 ≤ k)] (m : ℕ) (c₀ : ℝ≥0) (hdkc₀N : d ≤ (k - 1) * c₀ / N)
  (k' K' : ℝ≥0) [fact (1 ≤ k')] (hk' : k * k ≤ k')
  (hK' : (m + 2 + (r + 1) / (r * (1 - r)) * (m + 2)^2 : ℝ≥0) ≤ K')
  (c₁ c₂ : ℝ≥0) [fact (c₀ ≤ r' * c₁)] [fact (c₀ ≤ κ n * c₂)] [fact (c₁ ≤ κ n * c₂)] :
  (double_complex.col'.{u} BD κ r r' V Λ M N n).is_weak_bounded_exact k' K' m c₂ :=
begin
  have adm := (col_complex_rescaled.admissible.{u} r' V Λ M N (BD.X n)),
  have adm2 := adm.scale_index_left r',
  let T_T := col_complex_rescaled.T_inv_sub_Tinv' r r' V Λ M N (BD.X n) (κ n),
  have H := (col_complex_rescaled.is_weak_bounded_exact.{u}
    r' V Λ M N (BD.X n) d k (m+1) c₀ hdkc₀N),
  have H1 := H.scale_index_right _ c₂ (κ n) adm,
  have H2 := (H.scale_index_left _ c₁ r' adm).scale_index_right _ c₂ (κ n) adm2,
  have key := weak_normed_snake_dual
    (double_complex.col'.{u} BD κ r r' V Λ M N n) _ _
    (double_complex.col_ι BD κ r r' V Λ M N n) T_T
    k _ ((m + 1) + 1) _ (1 + r⁻¹) (r / (1 - r) + 1) (by simpa using H1) H2 (adm.scale_index_right _),
  have h_isom : _ := _,
  apply (key _ _ _ h_isom).of_le _ ⟨hk'⟩ _ le_rfl ⟨le_rfl⟩,
  any_goals { clear key adm2 H1 H2 },
  { intros, apply col_exact'_aux1 },
  { intros, apply col_exact'_aux2 },
  { intros c i, apply double_complex.col_ι_range },
  { apply system_of_complexes.admissible_of_isometry (adm.scale_index_right _) h_isom, },
  { refine ⟨le_trans (le_of_eq _) hK'⟩,
    rw [pow_two, ← mul_assoc],
    simp only [nat.cast_add, nat.cast_one, bit0, ← add_assoc, or_false, add_eq_zero_iff,
      one_ne_zero, add_right_inj, mul_eq_mul_right_iff, and_false, div_eq_mul_inv],
    have hr0 : r ≠ 0, { exact ne_of_gt (fact.out _) },
    have h1r : 1 - r ≠ 0,
    { rw [← nnreal.coe_injective.ne_iff, nnreal.coe_sub, nnreal.coe_zero, sub_ne_zero],
      { norm_cast, exact ne_of_gt (fact.out _) },
      { exact fact.out _ } },
    calc (1 + r⁻¹) * (r * (1 - r)⁻¹ + 1)
        = (1 + r⁻¹) * (r * (1 - r)⁻¹ + (1 - r) * (1 - r)⁻¹) : by rw [mul_inv_cancel h1r]
    ... = (1 + r⁻¹) * (1 - r)⁻¹ : congr_arg _ _
    ... = (1 + r⁻¹) * (r * r⁻¹) * (1 - r)⁻¹ : by rw [mul_inv_cancel hr0, mul_one]
    ... = ((1 + r⁻¹) * r) * (r⁻¹ * (1 - r)⁻¹) : by simp only [mul_assoc]
    ... = (r + 1) * (r * (1 - r))⁻¹ : _,
    { rw [← add_mul, add_comm, tsub_add_cancel_of_le, one_mul], exact fact.out _ },
    { rw [add_mul, one_mul, inv_mul_cancel, mul_inv],
      exact ne_of_gt (fact.out _) } },
  { intros c i, apply double_complex.col_ι_isometry, }
end
```

### child `weak_normed_snake_dual`: [`src/normed_snake_dual.lean` lines 300-331](https://github.com/leanprover-community/lean-liquid/blob/ee4795874a99ea5f9d85bd0b364425f07b932377/src/normed_snake_dual.lean#L300-L331) ([local copy](code/src/normed_snake_dual.lean))

```lean
lemma weak_normed_snake_dual (k k' K K' r₁ r₂ : ℝ≥0)
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  {a : ℕ} {c₀ : ℝ≥0}
  (hN : N.is_weak_bounded_exact k K (a + 1) c₀)
  (hP : P.is_weak_bounded_exact k' K' (a + 1) c₀)
  (hN_adm : N.admissible)
  (hgnrm : ∀ c i (x : N c i), ∥g x∥ ≤ r₁ * ∥x∥)
  (Hg : ∀ (c : ℝ≥0) [fact (c₀ ≤ c)] (i : ℕ) (hi : i ≤ a + 1 + 1) (y : P c i),
    ∃ (x : N c i), g x = y ∧ ∥x∥ ≤ r₂ * ∥y∥)
  (hg : ∀ c i, (f.apply : M c i ⟶ N c i).range = g.apply.ker)
  (hf : ∀ c i, @isometry (M c i) (N c i) _ _ f.apply) :
  M.is_weak_bounded_exact (k * k') (K + r₁ * r₂ * K * K') a c₀ :=
begin
  introsI c hc i hi,
  apply exists_norm_sub_le_mul_add (admissible_of_isometry hN_adm hf),
  intros m ε hε,

  have hε₁ : 0 < ε / 2 * (1 + K' * r₁ * r₂)⁻¹ := mul_pos (half_pos hε)
    (inv_pos.2 $ add_pos_of_pos_of_nonneg zero_lt_one ((K' * r₁ * r₂).coe_nonneg)),
  obtain ⟨_, _, rfl, rfl, n₁, hn₁⟩ :=
    hN _ ⟨hc.out.trans $ le_mul_of_one_le_left' hk'.out⟩ _ (trans hi a.le_succ) (f m) _ hε₁,
  have Hi' : i - 1 ≤ a + 1 := trans i.pred_le (trans hi a.le_succ),
  obtain ⟨_, _, rfl, rfl, p₂, hp₂⟩ := hP _ hc _ Hi' (g n₁)
    (if (r₂ : ℝ) = 0 then 1 else (ε / 2) * r₂⁻¹) _,
  { simp_rw [nnreal.coe_eq_zero r₂] at hp₂,
    apply exist_norm_sub_le_mul_norm_add hε.le hN_adm hgnrm Hg hg hf hc hi hn₁ Hi' p₂,
    convert hp₂, },
  { by_cases H : r₂ = 0,
    { simp only [H, zero_lt_one, if_true, eq_self_iff_true, nnreal.coe_eq_zero] },
    { simp only [H, nnreal.coe_eq_zero, if_false],
      exact mul_pos (half_pos hε) (inv_pos.2 (nnreal.coe_pos.2 (zero_lt_iff.2 H))) } }
end
```

### child `col_complex_rescaled.is_weak_bounded_exact`: [`src/thm95/col_exact.lean` lines 710-718](https://github.com/leanprover-community/lean-liquid/blob/ee4795874a99ea5f9d85bd0b364425f07b932377/src/thm95/col_exact.lean#L710-L718) ([local copy](code/src/thm95/col_exact.lean))

```lean
lemma col_complex_rescaled.is_weak_bounded_exact
  (d : ℝ≥0) [pseudo_normed_group.splittable ((Λ →+ M)^n) N d]
  (k : ℝ≥0) [fact (1 ≤ k)] (m : ℕ) (c₀ : ℝ≥0) (hdkc₀N : d ≤ (k - 1) * c₀ / N) :
  (col_complex_rescaled r' V Λ M N n).is_weak_bounded_exact k (m+1) m c₀ :=
begin
  have := scale_factorial.is_weak_bounded_exact
    (col_complex.is_weak_bounded_exact r' V Λ M N n d k m c₀ hdkc₀N),
  rwa [one_mul] at this,
end
```

### child `col_exact'_aux1`: [`src/thm95/col_exact.lean` lines 1229-1238](https://github.com/leanprover-community/lean-liquid/blob/ee4795874a99ea5f9d85bd0b364425f07b932377/src/thm95/col_exact.lean#L1229-L1238) ([local copy](code/src/thm95/col_exact.lean))

```lean
lemma col_exact'_aux1 [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  ∀ x, ∥(((col_complex_rescaled.T_inv_sub_Tinv' r r' V Λ M N (BD.X n) (κ n)).app c).f i) x∥ ≤
    (1 + r⁻¹) * ∥x∥ :=
begin
  intro x,
  cases i;
  { apply normed_add_group_hom.le_of_op_norm_le,
    refine @SemiNormedGroup.norm_rescale_map_le _ _ _ _ _ (1 + r⁻¹) _,
    exact CLCFP.norm_T_inv_sub_Tinv_le _ _ _ _ _ _ _ }
end
```

### child `col_exact'_aux2`: [`src/thm95/col_exact.lean` lines 1242-1255](https://github.com/leanprover-community/lean-liquid/blob/ee4795874a99ea5f9d85bd0b364425f07b932377/src/thm95/col_exact.lean#L1242-L1255) ([local copy](code/src/thm95/col_exact.lean))

```lean
lemma col_exact'_aux2 [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  ∀ y, ∃ x,
    (((col_complex_rescaled.T_inv_sub_Tinv' r r' V Λ M N (BD.X n) (κ n)).app c).f i) x = y ∧
    ∥x∥ ≤ ↑(r / (1 - r) + 1) * ∥y∥ :=
begin
  haveI : fact (r < 1) := ⟨@lt_trans _ _ r r' 1 (fact.out _) (fact.out _)⟩,
  cases i;
  { refine SemiNormedGroup.rescale_exists_norm_le _ _ _ _,
    intro y,
    obtain ⟨x, h1, h2⟩ := CLCFP.T_inv_sub_Tinv_exists_preimage r r' y 1 zero_lt_one,
    refine ⟨x, h1, _⟩,
    rwa [nnreal.coe_add, nnreal.coe_div, nnreal.coe_sub],
    exact fact.out _ }
end
```

### child `col_ι_range`: [`src/thm95/col_exact.lean` lines 1136-1145](https://github.com/leanprover-community/lean-liquid/blob/ee4795874a99ea5f9d85bd0b364425f07b932377/src/thm95/col_exact.lean#L1136-L1145) ([local copy](code/src/thm95/col_exact.lean))

```lean
lemma col_ι_range :
  (((double_complex.col_ι BD κ r r' V Λ M N n).app c).f i).range =
  (((col_complex_rescaled.T_inv_sub_Tinv' r r' V Λ M N (BD.X n) (κ n)).app c).f i).ker :=
begin
  cases i;
  { refine SemiNormedGroup.rescale_exact _ _ _ _,
    rw CLCTinv.ι_range',
    ext1 x,
    refl, },
end
```

### child `col_ι_isometry`: [`src/thm95/col_exact.lean` lines 1147-1154](https://github.com/leanprover-community/lean-liquid/blob/ee4795874a99ea5f9d85bd0b364425f07b932377/src/thm95/col_exact.lean#L1147-L1154) ([local copy](code/src/thm95/col_exact.lean))

```lean
lemma col_ι_isometry :
  isometry (((double_complex.col_ι BD κ r r' V Λ M N n).app c).f i) :=
begin
  cases i;
  { refine SemiNormedGroup.rescale_map_isometry _ _,
    apply add_monoid_hom_class.isometry_of_norm,
    intro, refl },
end
```

### child `admissible_of_isometry`: [`src/system_of_complexes/basic.lean` lines 199-212](https://github.com/leanprover-community/lean-liquid/blob/ee4795874a99ea5f9d85bd0b364425f07b932377/src/system_of_complexes/basic.lean#L199-L212) ([local copy](code/src/system_of_complexes/basic.lean))

```lean
lemma admissible_of_isometry {f : M ⟶ M'} (hadm : M'.admissible)
  (hiso : ∀ c i, @isometry (M c i) (M' c i) _ _ f.apply) :
  M.admissible :=
begin
  refine ⟨λ c i j h x, _, λ c' c i h x, _⟩,
  { rw [← (add_monoid_hom_class.isometry_iff_norm _).1 (hiso c i) _,
      ← (add_monoid_hom_class.isometry_iff_norm _).1 (hiso c j) _, ← system_of_complexes.hom_apply f,
      ← d_apply],
    exact hadm.d_norm_noninc _ _ _ _ _ },
  { rw [← (add_monoid_hom_class.isometry_iff_norm _).1 (hiso c i) _,
      ← (add_monoid_hom_class.isometry_iff_norm _).1 (hiso c' i) _, ← system_of_complexes.hom_apply f,
      ← system_of_complexes.hom_apply f, ← res_apply],
    exact hadm.res_norm_noninc _ _ _ _ _  }
end
```

### child `of_le`: [`src/system_of_complexes/basic.lean` lines 253-267](https://github.com/leanprover-community/lean-liquid/blob/ee4795874a99ea5f9d85bd0b364425f07b932377/src/system_of_complexes/basic.lean#L253-L267) ([local copy](code/src/system_of_complexes/basic.lean))

```lean
lemma of_le (hC : C.is_weak_bounded_exact k K m c₀) (hC_adm : C.admissible)
  (hk : fact (k ≤ k')) (hK : fact (K ≤ K')) (hm : m' ≤ m) (hc₀ : fact (c₀ ≤ c₀')) :
  C.is_weak_bounded_exact k' K' m' c₀' :=
begin
  intros c hc i hi x ε ε_pos,
  haveI : fact (k ≤ k') := hk,
  obtain ⟨i', j, hi', hj, y, hy⟩ := hC c ⟨hc₀.out.trans hc.out⟩ i (hi.trans hm) (res x) ε ε_pos,
  use [i', j, hi', hj, y],
  simp only [res_res] at hy,
  refine le_trans hy _,
  rw d_res,
  apply add_le_add_right,
  exact mul_le_mul hK.out (hC_adm.res_norm_noninc _ _ _ _ (C.d _ _ x))
    (norm_nonneg _) ((zero_le K).trans hK.out)
end
```

How the parts fit. The glue is one backward application of the key invariant:
`have key := weak_normed_snake_dual …` then `apply (key …).of_le …`, which
turns `col_exact'` into one goal per hypothesis of the snake lemma plus the
two extra hypotheses of `of_le`. The lemma graph (in text):

```
col_exact'  (the glue, 46 lines)
├── weak_normed_snake_dual                     ← the key invariant
│     with M = col', f = col_ι, g = T_T (T_inv_sub_Tinv'),
│          r₁ = 1 + r⁻¹,  r₂ = r/(1-r)+1,  a = (m+1)+1
│     ├── hN   (N weakly exact) = H.scale_index_right          (H = col_complex_rescaled.is_weak_bounded_exact)
│     ├── hP   (P weakly exact) = H.scale_index_left.scale_index_right
│     ├── hN_adm (N admissible) = (col_complex_rescaled.admissible).scale_index_right
│     ├── hgnrm (g norm ≤ r₁)     ← col_exact'_aux1
│     ├── Hg    (g surjective, bound r₂) ← col_exact'_aux2
│     ├── hg    (range f = ker g) ← col_ι_range
│     └── hf    (f isometry)      ← col_ι_isometry
└── is_weak_bounded_exact.of_le   (weaken k·k' → k', K + r₁r₂KK' → K')
      ├── hC_adm (col' admissible) ← admissible_of_isometry (using the isometry h_isom)
      └── hK (K + r₁r₂KK' ≤ K')    ← the calc chain + hK'
```

After `apply (key …).of_le _ ⟨hk'⟩ _ le_rfl ⟨le_rfl⟩` there are six goals,
each closed by one child or a short calc:

1. `∥g x∥ ≤ (1 + r⁻¹) · ∥x∥` — closed by `col_exact'_aux1` (the two cases
   `i = 0` and `i = i+1` reduce to `CLCFP.norm_T_inv_sub_Tinv_le`).
2. surjectivity of `g` with bound `r/(1-r)+1` — closed by `col_exact'_aux2`
   (via `SemiNormedGroup.rescale_exists_norm_le` and
   `CLCFP.T_inv_sub_Tinv_exists_preimage`).
3. `range f = ker g` — closed by `col_ι_range` (via
   `SemiNormedGroup.rescale_exact` and `CLCTinv.ι_range'`).
4. admissibility of `col'` — closed by `admissible_of_isometry` from the
   admissibility of `col_complex_rescaled` and the isometry `h_isom`.
5. the constant bound `(K + r₁r₂KK') ≤ K'` — closed by a `calc` proving
   `(1 + r⁻¹)·(r/(1-r)+1) = (r+1)/(r·(1-r))`, matching `hK'`.
6. `f` is an isometry — closed by `col_ι_isometry` (via
   `SemiNormedGroup.rescale_map_isometry`).

The inputs `H`, `H1`, `H2`, `adm`, `adm2` are themselves produced by
framework lemmas that the glue also invokes directly but which are *not* in
the child list (they are plumbing, not the argument): `col_complex_rescaled.admissible`
([`col_exact.lean:1208`](https://github.com/leanprover-community/lean-liquid/blob/ee4795874a99ea5f9d85bd0b364425f07b932377/src/thm95/col_exact.lean#L1208-L1223))
makes `adm`; `admissible.scale_index_left` / `admissible.scale_index_right` and
`is_weak_bounded_exact.scale_index_left` / `is_weak_bounded_exact.scale_index_right`
([`rescale.lean:124-177`](https://github.com/leanprover-community/lean-liquid/blob/ee4795874a99ea5f9d85bd0b364425f07b932377/src/system_of_complexes/rescale.lean#L124-L177))
shift the index and preserve exactness/admissibility under the scaling
`ScaleIndexLeft` / `ScaleIndexRight`.

The child names above are the declaration identifiers. Their fully qualified
names are `double_complex.col_ι_range` and `double_complex.col_ι_isometry`
(both declared inside `namespace double_complex`),
`system_of_complexes.admissible_of_isometry`, and
`system_of_complexes.is_weak_bounded_exact.of_le`; `weak_normed_snake_dual` is
top-level in `normed_snake_dual.lean`.

Below `weak_normed_snake_dual` the snake lemma itself is decomposed into
smaller partial inequalities (its file docstring says why): the chain
`weak_normed_snake_dual → exist_norm_sub_le_mul_norm_add →
norm_sub_le_mul_norm_add → norm_sub_le_split` is four project lemmas deep —
this is the `depth: 4` recorded in the shape.

## Why it is good

1. `col_exact'` is declared at lines 1257-1302 of `src/thm95/col_exact.lean`
   (check: `declared(col_exact', src/thm95/col_exact.lean, 1257-1302)`).
2. The parent cites the key invariant `weak_normed_snake_dual` at line 1272
   (check: `cites(parent, weak_normed_snake_dual)`).
3. The whole file `src/thm95/col_exact.lean` is sorry-free: the only
   `admit` tokens are in a commented-out lemma (lines 631, 637)
   (check: `no_sorry(src/thm95/col_exact.lean, 1-1318)`).
4. The decomposition has 8 direct project lemmas (child sites of 32, 9, 10,
   14, 10, 8, 14 and 15 lines), a 46-line glue, and depth 4:
   `col_exact' → weak_normed_snake_dual → exist_norm_sub_le_mul_norm_add →
   norm_sub_le_mul_norm_add → norm_sub_le_split` (measurement, counted from
   the sites and the citation chain).
5. The authors state why the snake lemma's own proof is split into partial
   inequalities: "we broke these proofs into smaller partial inequalities, for
   three reasons. First, it streamlines the formalization. Second, it helps
   Lean processing the statements, reducing processing times. Third, it
   allows us to us a large part of the argument for both
   `weak_normed_snake_dual` and `normed_snake_dual`."
   (author-statement, `normed_snake_dual.lean:33-36`).

In my opinion the detail worth copying is that the key invariant is *already
proved* and the glue is purely forward assembly: every hypothesis of the
snake lemma is discharged by a named lemma with its own two-case proof, and
the only free computation left in the glue is the constant-weakening `calc`
— so the parent reads as a table of "which lemma closes which obligation".

## When to use it, and when not

Use it when the goal is an instance of a reusable exactness or extension
principle (snake lemma, five lemma, a long-exact-sequence step) that is
already proved as a single statement, and the real work is supplying its
hypotheses: each hypothesis is then a separate, independently provable
statement (an isometry, a norm bound, a surjectivity-with-bound, a
range-equals-kernel equality), and a monotonicity lemma (`of_le`) afterwards
adjusts the principle's constants to the target ones.

Avoid it when the key statement is not yet proved and its proof is itself the
bulk of the argument — the glue would then hide a whole development behind
one `have`, and the "children" would carry the difficulty rather than
discharging routine hypotheses. Also avoid it when the hypotheses do not
separate cleanly: if the isometry, surjectivity and exactness conditions have
to be proved together in one lemma rather than as named two-case lemmas, the
backward application no longer decomposes the goal.

## Consequences

The move obliges the writer to discharge every hypothesis of the key
invariant as a named lemma: the norm bound (`col_exact'_aux1`,
`r₁ = 1 + r⁻¹`) and the surjectivity-with-bound (`col_exact'_aux2`,
`r₂ = r/(1-r)+1`) of `T_inv_sub_Tinv`; the `range = ker` exactness
(`col_ι_range`) and the isometry (`col_ι_isometry`) of the connecting
morphism `col_ι`; the exactness of the two neighbouring complexes
(`col_complex_rescaled.is_weak_bounded_exact`, rescaled by
`scale_index_left`/`scale_index_right`); and admissibility
(`admissible_of_isometry`, from `col_complex_rescaled.admissible`). A final
constant weakening (`is_weak_bounded_exact.of_le`) is an obligation too, and
it needs an arithmetic identity `(1 + r⁻¹)·(r/(1-r)+1) = (r+1)/(r·(1-r))`
plus the bound `hK'`.

Failure modes: the key lemma's constants (`k·k'`, `K + r₁·r₂·K·K'`) are not
the target constants, so forgetting the `of_le` weakening leaves the goal
unclosed; mis-ordering the hypotheses (supplying `hN` where `hP` is wanted)
breaks the `apply`; and if the admissibility input to `of_le` is missing, the
proof must reconstruct it via `admissible_of_isometry` from an isometry
(`h_isom`), which the glue leaves as a hole to be filled by unification.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml runs 'lean --json --make src' (builds src/thm95/col_exact.lean and src/normed_snake_dual.lean); commit ee4795874a99ea5f9d85bd0b364425f07b932377 is on master, the default branch | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: weak_normed_snake_dual@src/thm95/col_exact.lean:1272, col_complex_rescaled.is_weak_bounded_exact@src/thm95/col_exact.lean:1263, col_exact'_aux1@src/thm95/col_exact.lean:1279, col_exact'_aux2@src/thm95/col_exact.lean:1280, col_ι_range@src/thm95/col_exact.lean:1281, col_ι_isometry@src/thm95/col_exact.lean:1301, admissible_of_isometry@src/thm95/col_exact.lean:1282, of_le@src/thm95/col_exact.lean:1277; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 4 file(s) byte-identical at ee4795874a99ea5f9d85bd0b364425f07b932377 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(col_exact', src/thm95/col_exact.lean, 1257-1302) -> declared: col_exact' is declared at src/thm95/col_exact.lean:1257 | check_claims.py |
| 2 | verified | cites(parent, weak_normed_snake_dual) -> cites: weak_normed_snake_dual occurs at src/thm95/col_exact.lean:1272 | check_claims.py |
| 3 | verified | no_sorry(src/thm95/col_exact.lean, 1-1318) -> no_sorry: none of sorry, admit, axiom in src/thm95/col_exact.lean:1-1318 | check_claims.py |
| 4 | verified | citation chain checked in code: col_exact.lean:1272 'have key := weak_normed_snake_dual'; normed_snake_dual.lean:325 'apply exist_norm_sub_le_mul_norm_add' (inside weak_normed_snake_dual 300-331); normed_snake_dual.lean:259 'refine norm_sub_le_mul_norm_add' (inside exist_norm_sub_le_mul_norm_add, declared 223); normed_snake_dual.lean:160 'norm_sub_le_split hfnorm hm₁' (inside norm_sub_le_mul_norm_add, declared 143). 8 child sites with line counts 32,9,10,14,10,8,14,15; parent 1257-1302 = 46 lines. | verifier |
| 5 | verified | quote at src/normed_snake_dual.lean:33-36 matches verbatim: 'we broke these proofs into smaller partial inequalities, for three reasons. First, it streamlines the formalization. Second, it helps Lean processing the statements, reducing processing times. Third, it allows us to us a large part of the argument for both weak_normed_snake_dual and normed_snake_dual.' | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Decomposition matches code: parent col_exact' (1257-1302) reduces to weak_normed_snake_dual with its 7 hypotheses discharged by named lemmas plus of_le for constant weakening; the 6 post-apply goals (hgnrm/Hg/hg/admissibility/K-bound/h_isom) close via col_exact'_aux1(1279), col_exact'_aux2(1280), col_ι_range(1281), admissible_of_isometry(1282), the calc chain(1283-1300), col_ι_isometry(1301), no sorry in range. All 8 child statements match code verbatim and each closed_by matches its proof. Shape numbers correct: glue_lines 46 (1302-1257+1), child_lines [32,9,10,14,10,8,14,15] all match their sites, direct_lemmas 8, depth 4 chain verified (col_exact'->weak_normed_snake_dual@1272->exist_norm_sub_le_mul_norm_add@325->norm_sub_le_mul_norm_add@259->norm_sub_le_split@160). Minor: README glue-cites table records col_complex_rescaled.is_weak_bounded_exact@1263 but the citation is actually at 1268 (1263 is the conclusion); substance unaffected. col_complex_rescaled.admissible and scale_index_* are cited in the glue but excluded from children as documented plumbing. | reviewer-correctness |
| generality | accept | Generality holds. The move is stated beyond the example: 'When to use it' names snake lemma, five lemma and long-exact-sequence steps as the general class (a reusable exactness/extension principle already proved as one statement, the work being to supply its hypotheses), and applicability.goal_shape/use_when restate that abstractly. 'When not to use' is honest and specific: two conditions (key statement not yet proved, so the glue hides a whole proof behind one have; and hypotheses not separating cleanly into named two-case lemmas). Consequences are specific and grounded in the code: discharge every hypothesis as a named lemma, the of_le constant-weakening (needs the arithmetic identity (1+r^-1)(r/(1-r)+1)=(r+1)/(r(1-r)) plus hK'), and failure modes (constants k*k' vs k', K+r1r2KK' vs K' unclosed without of_le; mis-ordering hN/hP breaks apply; missing admissibility input leaves h_isom as a unification hole). The bounded-prover leaf story is present: 'Why it is good' states each hypothesis is discharged by a named lemma with its own two-case proof, the glue is purely forward assembly reading as a table of which lemma closes which obligation, child sites are 8-32 lines, and claim 5's author-statement notes smaller statements reduce Lean processing time. No standing objection. | reviewer-generality |
| provenance-licence | accept | check_provenance passes: 4 files byte-identical at ee4795874a99ea5f9d85bd0b364425f07b932377. Commit consistent across entry.json, source note (pinned 2026-11-12) and README (short form ee4795874a99). All permalinks use the full commit hash and point to correct paths; cited line ranges verified against the local copies (parent col_exact' at col_exact.lean:1257, weak_normed_snake_dual at normed_snake_dual.lean:300, aux1/aux2/col_iota_range/col_iota_isometry/admissible_of_isometry/of_le all start at their cited lines). Licence recorded as LicenseRef-unknown everywhere (entry.json, README, source note) and is honest: list_files.py shows no LICENSE/COPYING at the repo root, so 'no licence file found at the root' is accurate. Author-statement quote at normed_snake_dual.lean:33-36 matches verbatim. Minor non-blocking note: source note boilerplate says 'the licence text below governs' though no licence text follows; substantive record is accurate and traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover-community/lean-liquid at commit `ee4795874a99ea5f9d85bd0b364425f07b932377`, under `LicenseRef-unknown`; see the [source note](../../sources/lean-liquid/SOURCE.md) for the licence text and attribution.
