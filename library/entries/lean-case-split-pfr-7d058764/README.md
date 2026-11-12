# Case split on #H <= #A closes the polynomial Freiman-Ruzsa conjecture

| | |
|---|---|
| Kind | instance |
| Move | case-split |
| Language | lean |
| Status | accepted |
| Source | [pfr](../../sources/pfr/SOURCE.md) at `1ef23c3c5a83` |
| Licence | `Apache-2.0` |

## Intent

The headline theorem of the project, the polynomial Freiman-Ruzsa conjecture,
is reduced first to the finite case by `wlog`, then to a subgroup `H` produced
by the auxiliary lemma `PFR_conjecture_aux`, and finally split on whether
`|H| ≤ |A|`. The `#H ≤ #A` branch reuses `H` as-is and closes with `|c| ≤ K^12`;
the other branch shrinks `H` to a subgroup `H'` and covers `A` by cosets of
`H'`, closing with `|c| < 2·K^12`.

## The decomposition

### parent `PFR_conjecture`: [`PFR/Main.lean` lines 261-337](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/Main.lean#L261-L337) ([local copy](code/PFR/Main.lean))

```lean
theorem PFR_conjecture {G : Type*} [AddCommGroup G] [Module (ZMod 2) G]
    {A : Set G} {K : ℝ} (hA₀ : A.Nonempty) (Afin : A.Finite)
    (hA : (A + A).ncard ≤ K * A.ncard) :
    ∃ (H : Submodule (ZMod 2) G) (c : Set G), c.Finite ∧ (H : Set G).Finite ∧
      Nat.card c < 2 * K ^ 12 ∧ (H : Set G).ncard ≤ A.ncard ∧ A ⊆ c + H := by
  wlog hG : Finite G generalizing G with H
  · let G' := Submodule.span (ZMod 2) A
    let G'fin : Fintype G' := (Afin.submoduleSpan _).fintype
    let ι : G'→ₗ[ZMod 2] G := G'.subtype
    have ι_inj : Injective ι := G'.toAddSubgroup.subtype_injective
    let A' : Set G' := ι ⁻¹' A
    have A_rg : A ⊆ range ι := by simp [G', ι]
    have cardA' : Nat.card A' = A.ncard := Nat.card_preimage_of_injective ι_inj A_rg
    have hA' : Nat.card (A' + A') ≤ K * Nat.card A' := by
      rwa [cardA', ← preimage_add _ ι_inj A_rg A_rg,
           Nat.card_preimage_of_injective ι_inj (add_subset_range _ A_rg A_rg)]
    obtain ⟨H', c', -, -, hc', hH', hH'₂⟩ :=
      H (hA₀.preimage' A_rg) (toFinite _) hA' inferInstance
    refine ⟨H'.map ι , ι '' c', toFinite _, toFinite (ι '' H'), ?_, ?_, fun x hx ↦ ?_⟩
    · rwa [Nat.card_image_of_injective ι_inj]
    · simpa [Set.ncard_image_of_injective _ ι_inj, ← cardA']
    · erw [← image_add]
      exact ⟨⟨x, Submodule.subset_span hx⟩, hH'₂ hx, rfl⟩
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < A.ncard ∧ (0 : ℝ) < (A + A).ncard ∧ 0 < K :=
    PFR_conjecture_pos_aux' A.toFinite hA₀ hA
  -- consider the subgroup `H` given by Lemma `PFR_conjecture_aux`.
  obtain ⟨H, c, hc, IHA, IAH, A_subs_cH⟩ : ∃ (H : Submodule (ZMod 2) G) (c : Set G),
    Nat.card c ≤ K ^ (13/2) * A.ncard ^ (1/2) * (H : Set G).ncard ^ (-1/2)
      ∧ (H : Set G).ncard ≤ K ^ 11 * A.ncard ∧ A.ncard ≤ K ^ 11 * (H : Set G).ncard
      ∧ A ⊆ c + H :=
    PFR_conjecture_aux hA₀ hA
  have H_pos : (0 : ℝ) < (H : Set G).ncard := by
    have : 0 < (H : Set G).ncard := Nat.card_pos; positivity
  rcases le_or_gt ((H : Set G).ncard) A.ncard with h|h
  -- If `#H ≤ #A`, then `H` satisfies the conclusion of the theorem
  · refine ⟨H, c, toFinite _, toFinite _, ?_, h, A_subs_cH⟩
    calc
    Nat.card c ≤ K ^ (13/2 : ℝ) * A.ncard ^ (1/2 : ℝ) * (H : Set G).ncard ^ (-1/2 : ℝ) := hc
    _ ≤ K ^ (13/2 : ℝ) * (K ^ 11 * (H : Set G).ncard) ^ (1/2) * (H : Set G).ncard ^ (-1/2 : ℝ) := by
      gcongr
    _ = K ^ 12 := by rpow_ring; norm_num
    _ < 2 * K ^ 12 := by linarith [show 0 < K ^ 12 by positivity]
  -- otherwise, we decompose `H` into cosets of one of its subgroups `H'`, chosen so that
  -- `#A / 2 < #H' ≤ #A`. This `H'` satisfies the desired conclusion.
  · obtain ⟨H', IH'A, IAH', H'H⟩ : ∃ H' : Submodule (ZMod 2) G, Nat.card H' ≤ A.ncard
          ∧ A.ncard < 2 * Nat.card H' ∧ H' ≤ H := by
      have A_pos' : 0 < A.ncard := mod_cast A_pos
      exact ZModModule.exists_submodule_subset_card_le Nat.prime_two H h.le A_pos'.ne'
    have : (A.ncard / 2 : ℝ) < Nat.card H' := by
      rw [div_lt_iff₀ zero_lt_two, mul_comm]; norm_cast
    have H'_pos : (0 : ℝ) < Nat.card H' := by
      have : 0 < Nat.card H' := Nat.card_pos; positivity
    obtain ⟨u, HH'u, hu⟩ :=
      H'.toAddSubgroup.exists_left_transversal_of_le (H := H.toAddSubgroup) H'H
    dsimp at HH'u
    refine ⟨H', c + u, toFinite _, toFinite _, ?_, IH'A, by rwa [add_assoc, HH'u]⟩
    calc
    (Nat.card (c + u) : ℝ)
      ≤ Nat.card c * Nat.card u := mod_cast natCard_add_le
    _ ≤ (K ^ (13/2 : ℝ) * A.ncard ^ (1 / 2 : ℝ) * ((H : Set G).ncard ^ (-1 / 2 : ℝ)))
          * ((H : Set G).ncard / Nat.card H') := by
        gcongr
        apply le_of_eq
        rw [eq_div_iff H'_pos.ne']
        norm_cast
    _ < (K ^ (13/2) * A.ncard ^ (1 / 2) * ((H : Set G).ncard ^ (-1 / 2)))
          * ((H : Set G).ncard / (A.ncard / 2)) := by
        gcongr
    _ = 2 * K ^ (13/2) * A.ncard ^ (-1/2) * (H : Set G).ncard ^ (1/2) := by
        field_simp
        rpow_ring
        norm_num
    _ ≤ 2 * K ^ (13/2) * A.ncard ^ (-1/2) * (K ^ 11 * A.ncard) ^ (1/2) := by
        gcongr
    _ = 2 * K ^ 12 := by
        rpow_ring
        norm_num
```

### child `PFR_conjecture_aux`: [`PFR/Main.lean` lines 149-254](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/Main.lean#L149-L254) ([local copy](code/PFR/Main.lean))

```lean
/-- Auxiliary statement towards the polynomial Freiman-Ruzsa (PFR) conjecture: if `A` is a subset of
an elementary abelian 2-group of doubling constant at most $K$, then there exists a subgroup `H`
such that `A` can be covered by at most `K^(13/2) |A|^(1/2) / |H|^(1/2)` cosets of `H`, and `H` has
the same cardinality as `A` up to a multiplicative factor `K^11`. -/
lemma PFR_conjecture_aux (hA₀ : A.Nonempty) (hA : (A + A).ncard ≤ K * A.ncard) :
    ∃ (H : Submodule (ZMod 2) G) (c : Set G),
    Nat.card c ≤ K ^ (13/2 : ℝ) * A.ncard ^ (1/2 : ℝ) * (H : Set G).ncard ^ (-1/2 : ℝ) ∧
      (H : Set G).ncard ≤ K ^ 11 * A.ncard ∧ A.ncard ≤ K ^ 11 * (H : Set G).ncard ∧ A ⊆ c + H := by
  cases nonempty_fintype G
  classical
  have A_fin : Finite A := by infer_instance
  let : MeasurableSpace G := ⊤
  rw [← Set.sub_eq_add] at hA
  have : MeasurableSingletonClass G := ⟨fun _ ↦ trivial⟩
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < A.ncard ∧ (0 : ℝ) < (A - A).ncard ∧ 0 < K :=
    PFR_conjecture_pos_aux A.toFinite hA₀ hA
  let A' := A.toFinite.toFinset
  have hA₀' : Finset.Nonempty A' := by simpa [Finset.Nonempty, Set.Nonempty, A'] using hA₀
  have hAA' : A' = A := Finite.coe_toFinset (toFinite A)
  rcases exists_isUniform_measureSpace A' hA₀' with ⟨Ω₀, mΩ₀, UA, hP₀, UAmeas, UAunif, -, -⟩
  rw [hAA'] at UAunif
  have : d[UA # UA] ≤ log K := rdist_le_of_isUniform_of_card_sub_le hA₀ hA UAunif UAmeas
  rw [Set.sub_eq_add] at hA
  let p : refPackage Ω₀ Ω₀ G := ⟨UA, UA, UAmeas, UAmeas, 1/9, (by norm_num), (by norm_num)⟩
  -- entropic PFR gives a subgroup `H` which is close to `A` for the Rusza distance
  obtain ⟨H, Ω₁, mΩ₁, UH, hP₁, UHmeas, UHunif, hUH, -, -⟩ := entropic_PFR_conjecture p (by norm_num)
  have H_fin : (H : Set G).Finite := (H : Set G).toFinite
  rcases independent_copies_two UAmeas UHmeas
    with ⟨Ω, mΩ, VA, VH, hP, VAmeas, VHmeas, Vindep, idVA, idVH⟩
  have VAunif : IsUniform A VA := UAunif.of_identDistrib idVA.symm .of_discrete
  have VA'unif := VAunif
  rw [← hAA'] at VA'unif
  have VHunif : IsUniform H VH := UHunif.of_identDistrib idVH.symm .of_discrete
  let H' := (H : Set G).toFinite.toFinset
  have hHH' : H' = (H : Set G) := (toFinite (H : Set G)).coe_toFinset
  have VH'unif := VHunif
  rw [← hHH'] at VH'unif
  have : d[VA # VH] ≤ 11/2 * log K := by rw [idVA.rdist_congr idVH]; linarith
  have H_pos : (0 : ℝ) < (H : Set G).ncard := by
    have : 0 < (H : Set G).ncard := Nat.card_pos
    positivity
  have VA_ent : H[VA] = log A.ncard := VAunif.entropy_eq' A_fin VAmeas
  have VH_ent : H[VH] = log (H : Set G).ncard := VHunif.entropy_eq' H_fin VHmeas
  have Icard : |log A.ncard - log (H : Set G).ncard| ≤ 11 * log K := by
    rw [← VA_ent, ← VH_ent]
    apply (diff_ent_le_rdist VAmeas VHmeas).trans
    linarith
  have IAH : A.ncard ≤ K ^ 11 * (H : Set G).ncard := by
    have : log A.ncard ≤ log K * 11 + log (H : Set G).ncard := by
      linarith [(le_abs_self _).trans Icard]
    simpa [exp_log, A_pos, H_pos, exp_add, ← rpow_def_of_pos K_pos] using exp_monotone this
  have IHA : (H : Set G).ncard ≤ K ^ 11 * A.ncard := by
    have : log (H : Set G).ncard ≤ log K * 11 + log A.ncard := by
      linarith [(neg_le_abs _).trans Icard]
    simpa [exp_log, A_pos, H_pos, exp_add, ← rpow_def_of_pos K_pos] using exp_monotone this
  -- entropic PFR shows that the entropy of `VA - VH` is small
  have I : log K * (-11/2) + log A.ncard * (-1/2) + log (H : Set G).ncard * (-1/2)
      ≤ - H[VA - VH] := by
    rw [Vindep.rdist_eq VAmeas VHmeas] at this
    linarith
  -- therefore, there exists a point `x₀` which is attained by `VA - VH` with a large probability
  obtain ⟨x₀, h₀⟩ : ∃ x₀ : G, rexp (- H[VA - VH]) ≤ (ℙ : Measure Ω).real ((VA - VH) ⁻¹' {x₀}) :=
    prob_ge_exp_neg_entropy' _ ((VAmeas.sub VHmeas).comp measurable_id')
  -- massage the previous inequality to get that `A ∩ (H + {x₀})` is large
  have J : K ^ (-11/2 : ℝ) * A.ncard ^ (1/2) * (H : Set G).ncard ^ (1/2 : ℝ) ≤
      (A ∩ (H + {x₀}) : Set G).ncard := by
    rw [VA'unif.measureReal_preimage_sub VAmeas VH'unif VHmeas Vindep] at h₀
    have := (Real.exp_monotone I).trans h₀
    have hAA'_card : A'.card  = A.ncard := by simp [← hAA']
    have hHH'_card : H'.card = (H : Set G).ncard := by simp [← hHH']
    rw [hAA'_card, hHH'_card, le_div_iff₀ (by positivity)] at this
    convert! this using 1
    · rw [exp_add, exp_add, ← rpow_def_of_pos K_pos, ← rpow_def_of_pos A_pos,
        ← rpow_def_of_pos H_pos]
      rpow_ring
      norm_num
    · simp [← Set.ncard_coe_finset, hAA', hHH', -add_singleton]
  have Hne : (A ∩ (H + {x₀} : Set G)).Nonempty := by
    by_contra h'
    have : (0 : ℝ) < Nat.card (A ∩ (H + {x₀}) : Set G) := lt_of_lt_of_le (by positivity) J
    simp only [Nat.card_eq_fintype_card, card_of_isEmpty, CharP.cast_eq_zero, lt_self_iff_false,
      not_nonempty_iff_eq_empty.1 h'] at this
  /- use Rusza covering lemma to cover `A` by few translates of `A ∩ (H + {x₀}) - A ∩ (H + {x₀})`
  (which is contained in `H`). The number of translates is at most
  `#(A + (A ∩ (H + {x₀}))) / #(A ∩ (H + {x₀}))`, where the numerator is controlled as this is
  a subset of `A + A`, and the denominator is bounded below by the previous inequality`. -/
  have Z3 :
      ((A + A ∩ (↑H + {x₀})).ncard : ℝ) ≤ (K ^ (13/2 : ℝ) * A.ncard ^ (1/2 : ℝ) *
        (H : Set G).ncard ^ (-1/2 : ℝ)) * (A ∩ (↑H + {x₀})).ncard := by
    calc
      (Nat.card (A + A ∩ (↑H + {x₀})) : ℝ)
      _ ≤ (A + A).ncard := by
        gcongr; exact Nat.card_mono (toFinite _) <| add_subset_add_left inter_subset_left
      _ ≤ K * A.ncard := hA
      _ = (K ^ (13/2 : ℝ) * A.ncard ^ (1/2 : ℝ) * (H : Set G).ncard ^ (-1/2 : ℝ)) *
          (K ^ (-11/2 : ℝ) * A.ncard ^ (1/2 : ℝ) * (H : Set G).ncard ^ (1/2 : ℝ)) := by
        rpow_ring; norm_num
      _ ≤ (K ^ (13/2 : ℝ) * A.ncard ^ (1/2 : ℝ) * (H : Set G).ncard ^ (-1/2 : ℝ)) *
        (A ∩ (↑H + {x₀})).ncard := by gcongr
  obtain ⟨u, huA, hucard, hAu, -⟩ :=
    Set.ruzsa_covering_add (toFinite A) (toFinite (A ∩ ((H + {x₀} : Set G)))) Hne (by exact Z3)
  have A_subset_uH : A ⊆ u + H := by
    grw [hAu, inter_subset_right]
    rw [add_sub_add_comm, singleton_sub_singleton, sub_self]
    simp
  exact ⟨H, u, hucard, IHA, IAH, A_subset_uH⟩
```

### child `PFR_conjecture_pos_aux'`: [`PFR/Main.lean` lines 102-109](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/Main.lean#L102-L109) ([local copy](code/PFR/Main.lean))

```lean
lemma PFR_conjecture_pos_aux' {G : Type*} [AddCommGroup G] {A : Set G} (hA : A.Finite) {K : ℝ}
    (hA₀ : A.Nonempty) (hAK : (A + A).ncard ≤ K * A.ncard) :
    (0 : ℝ) < A.ncard ∧ (0 : ℝ) < (A + A).ncard ∧ 0 < K := by
  have card_AA_pos : (0 : ℝ) < (A + A).ncard := by simpa [Set.ncard_pos (hA.add hA)]
  have KA_pos : 0 < K ∧ (0 : ℝ) < A.ncard := by
    have I : ¬ (A.ncard : ℝ) < 0 := by simp
    simpa [Nat.cast_pos, I, and_false, or_false] using mul_pos_iff.1 (card_AA_pos.trans_le hAK)
  exact ⟨KA_pos.2, card_AA_pos, KA_pos.1⟩
```

How the parts fit. The proof of `PFR_conjecture` is the *glue*; its first
obligation is met by the two project children, and its second by the split.

- `PFR_conjecture_pos_aux'` supplies the positivity facts `0 < A.ncard`,
  `0 < (A + A).ncard`, `0 < K` (line 284-285) that the rest of the argument
  exponentiates. It is a leaf: it closes on its own by `Set.ncard_pos` and
  `mul_pos_iff`, no sibling needed.
- `PFR_conjecture_aux` supplies the subgroup `H` and the covering set `c`, with
  `Nat.card c ≤ K^(13/2) · A.ncard^(1/2) · (H).ncard^(-1/2)` and the two `K^11`
  comparisons (lines 287-291). It is self-contained: its own proof calls
  `entropic_PFR_conjecture` for `H`, then entropy/cardinality estimates and
  `Set.ruzsa_covering_add` for `c`.
- The split `rcases le_or_gt ((H : Set G).ncard) A.ncard with h|h` (line 294)
  makes two children from the comparison.
  - Branch `#H ≤ #A` reuses `H` and `c` directly (line 296) and closes the
    cardinality bound by a `calc` that ends in `K ^ 12 < 2 * K ^ 12` (lines
    297-302). This branch needs only the output of `PFR_conjecture_aux`.
  - Branch `#A < #H` cannot reuse `H`, so it shrinks it: the Mathlib lemma
    `ZModModule.exists_submodule_subset_card_le` gives `H' ≤ H` with
    `Nat.card H' ≤ A.ncard < 2 · Nat.card H'` (line 305-308); then the Mathlib
    lemma `AddSubgroup.exists_left_transversal_of_le` gives a transversal `u`
    with `u + H' = H` (lines 313-314); the cover `c + u` is bounded by a `calc`
    ending in `2 * K ^ 12` (lines 317-337). This branch needs the two Mathlib
    lemmas in addition to `PFR_conjecture_aux`.

Two of the four direct lemmas are library API from Mathlib rather than project
lemmas, so they are named here but not copied as child sites:

- `ZModModule.exists_submodule_subset_card_le` — `Mathlib/Algebra/Module/ZMod.lean`
  lines 132-134, at mathlib4 revision `8fe7ce4` (pinned in the pfr
  `lake-manifest.json`): `lemma exists_submodule_subset_card_le (hp : p.Prime)
  [Module (ZMod p) G] {H : Submodule (ZMod p) G} {k : ℕ} (hk : k ≤ Nat.card H)
  (hk₀ : k ≠ 0) : ∃ H' : Submodule (ZMod p) G, Nat.card H' ≤ k ∧ k < p * Nat.card H'
  ∧ H' ≤ H`.
- `AddSubgroup.exists_left_transversal_of_le` — `Mathlib/GroupTheory/Complement.lean`
  lines 292-294 (generated from `Subgroup.exists_left_transversal_of_le` by
  `@[to_additive]`), same revision: `∃ S : Set G, S + H' = H ∧ Nat.card S *
  Nat.card H' = Nat.card H`.

The lemma graph (who uses whom, one level down):

```
PFR_conjecture
├── PFR_conjecture_pos_aux'            (line 285, project leaf)
├── PFR_conjecture_aux                 (line 291, project lemma)
│     ├── PFR_conjecture_pos_aux       (line 164, project leaf)
│     ├── rdist_le_of_isUniform_of_card_sub_le  (line 170, project theorem)
│     │     └── PFR_conjecture_pos_aux (line 121)
│     └── entropic_PFR_conjecture      (imported from PFR.EntropyPFR)
├── ZModModule.exists_submodule_subset_card_le   (line 308, Mathlib)
└── AddSubgroup.exists_left_transversal_of_le    (line 314, Mathlib)
```

Why each project child is a good leaf: `PFR_conjecture_pos_aux'` is a short,
self-contained statement whose proof closes from `Set.ncard_pos` and
`mul_pos_iff` alone; `PFR_conjecture_aux` is a larger statement but its
interface is exactly what the glue needs — `hA₀, hA ⊢ ∃ H c, (bounds) ∧ A ⊆ c + H`
— so the main proof treats it as a black box and never reopens its 102-line
entropy argument.

## Why it is good

1. (check) The parent closes from its children and the split: `rcases le_or_gt
   ((H : Set G).ncard) A.ncard with h|h` (line 294), with the two branches
   ending in `K ^ 12 < 2 * K ^ 12` (lines 296-302) and `2 * K ^ 12` (lines
   317-337) respectively; the file builds in the project's CI. See
   [PFR/Main.lean#L294-L337](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/Main.lean#L294-L337).
2. (author-statement) The authors factored the subgroup construction out as a
   named lemma: "Auxiliary statement towards the polynomial Freiman-Ruzsa (PFR)
   conjecture" (lines 149-152), and the glue names it, "consider the subgroup
   `H` given by Lemma `PFR_conjecture_aux`" (line 286). See
   [PFR/Main.lean#L149-L156](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/Main.lean#L149-L156).
3. (measurement) The glue is 72 proof lines (266-337) and calls 4 named lemmas
   directly — `PFR_conjecture_pos_aux'` (285), `PFR_conjecture_aux` (291),
   `ZModModule.exists_submodule_subset_card_le` (308),
   `AddSubgroup.exists_left_transversal_of_le` (314). See
   [PFR/Main.lean#L266-L337](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/Main.lean#L266-L337).
4. (known-use) The identical move — `wlog` to finite `G`, the `le_or_gt #H #A`
   split, the auxiliary-lemma branch, then the submodule+transversal branch —
   closes the improved bound `PFR_conjecture_improv`. See
   [PFR/ImprovedPFR.lean#L948-L1008](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/ImprovedPFR.lean#L948-L1008).

In my opinion the detail worth copying is the *shape* of the split rather than
the arithmetic: a bound that is unconditional in one regime (`#H ≤ #A`) and
needs a shrink-and-recover construction in the other (`#A < #H`), with both
regimes closing by the same `calc` pattern and only the exponents changing.

## When to use it, and when not

Use it when a main theorem has already obtained a candidate object `H` (by an
auxiliary lemma) and the remaining proof divides cleanly by a total-order
dichotomy on a size — `|H| ≤ |A|` here — where one regime reuses `H` and the
other must shrink it. The comparison should be one that a library lemma already
makes exhaustive (`le_or_gt`), so the split costs no extra obligation. Avoid it
when the two regimes need genuinely different constructions (then each should be
its own lemma, not two `·` branches of one proof), when the dichotomy's
exhaustiveness has to be stated and proved by hand, or when the size comparison
is not the natural cut point of the argument.

## Consequences

The move creates two goals from `|H| ≤ |A|`; the exhaustiveness obligation is
discharged by Mathlib's `le_or_gt`, so no separate disjunction lemma appears in
the file. Each branch still has to close a `calc` chain set up by its
`refine ⟨H, c, …⟩` / `refine ⟨H', c+u, …⟩`; when the bound exponents change (the
improved theorem uses `K^11` and `K^10` instead of `K^12` and `K^11`), the
`rpow_ring; norm_num` step is the only part that moves. The second branch is not
self-contained: it depends on a submodule-shrinking lemma and a
coset-transversal lemma from Mathlib; without them the shrink step does not
close, and a prover that cannot reach library lemmas would leave this branch
open.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push.yml 'Build project' job uses leanprover/lean-action (lake build of the whole project; PFR/Main.lean is imported by PFR.lean line 30); pinned commit 1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a is the tip of default branch master (api.github.com/repos/teorth/pfr/branches/master) | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read Main.lean L294-337: rcases le_or_gt ((H:Set G).ncard) A.ncard at L294; #H<=#A branch calc ends 'K^12 < 2*K^12' (L296-302); #A<#H branch ZModModule.exists_submodule_subset_card_le at L308, AddSubgroup.exists_left_transversal_of_le via H'.toAddSubgroup at L314, calc ends '2*K^12' (L335-337). CI builds the file. | verifier |
| 2 | verified | Read Main.lean L149-152 doc comment 'Auxiliary statement towards the polynomial Freiman-Ruzsa (PFR) conjecture'; L286 comment '-- consider the subgroup H given by Lemma PFR_conjecture_aux.' | verifier |
| 3 | verified | Read Main.lean L266-337 (72 lines). Named-lemma calls: PFR_conjecture_pos_aux' L285, PFR_conjecture_aux L291, ZModModule.exists_submodule_subset_card_le L308, AddSubgroup.exists_left_transversal_of_le L314 (via H'.toAddSubgroup). | verifier |
| 4 | verified | Read ImprovedPFR.lean L948-1008: theorem PFR_conjecture_improv L953; wlog Finite G L958; PFR_conjecture_improv_aux L983; rcases le_or_gt #H #A L986; ZModModule.exists_submodule_subset_card_le L1000; AddSubgroup.exists_left_transversal_of_le L1006. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent/children statements match PFR/Main.lean (parent 261-265; aux 153-156; pos_aux' 102-104). Split rcases le_or_gt at L294; #H<=#A branch closes via PFR_conjecture_aux calc ending K^12<2*K^12 (L296-302); #A<#H branch shrinks H via ZModModule.exists_submodule_subset_card_le (L308) and AddSubgroup.exists_left_transversal_of_le (L314), calc ends 2*K^12 (L317-337). Children are exactly the lemmas the proof uses directly (pos_aux' L285, aux L291); two Mathlib lemmas are named but not treated as children, and direct_lemmas=4 reflects this. Shape numbers correct: glue_lines=72 (266-337), child_lines=[98,5] (aux proof 157-254, pos_aux' proof 105-109), depth=3 (PFR_conjecture->aux->rdist_le_of_isUniform_of_card_sub_le->PFR_conjecture_pos_aux). Minor wording only (closed_by says '102-line proof' vs 98 proof lines; 'covering set c' vs local u) - not correctness defects. | reviewer-correctness |
| generality | accept | Generality is handled honestly and specifically. (1) Applies beyond the example: applicability.use_when/avoid_when are stated over a 'total-order dichotomy on a size or measure' with 'reuse vs shrink' branches and 'same calc chain', not over the concrete #H/#A; the README opinion explicitly separates 'the shape of the split' from 'the arithmetic'; claim 4 (known-use, already verifier-confirmed) shows the same move (wlog finite, le_or_gt #H #A split, aux-lemma branch, submodule+transversal branch) closes PFR_conjecture_improv in ImprovedPFR.lean L948-1008. (2) When-not-to-use is concrete (genuinely different constructions -> separate lemmas; exhaustiveness not supplied by a library lemma -> state it as its own fact; comparison not the natural cut point). Consequences are honest and specific: exhaustiveness is free via Mathlib le_or_gt so no disjunction lemma appears, each branch still owes a calc chain, exponent changes move only the rpow_ring;norm_num step, and the #A<#H branch is not self-contained (depends on ZModModule.exists_submodule_subset_card_le and AddSubgroup.exists_left_transversal_of_le, so a prover that cannot reach library lemmas leaves it open). (3) It says what makes the leaves good for a bounded prover: PFR_conjecture_pos_aux' is self-contained (closes from Set.ncard_pos + mul_pos_iff alone), and PFR_conjecture_aux has an interface exactly matching the glue's needs (hA0, hA |- exists H c, bounds and A subset c+H) so the glue uses it as a black box and never reopens its entropy argument. | reviewer-generality |
| provenance-licence | accept | provenance pass (check_provenance.py: 1 file byte-identical at 1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a, recorded sha256 matches). Commit 1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a is consistent across entry.json, sources/pfr/source.json, sources/pfr/SOURCE.md and README. Permalinks point to teorth/pfr at that commit with path PFR/Main.lean and line ranges matching the local copy (parent 261-337 ends at file line 337; aux 149-254; pos_aux' 102-109; cited lines 285/286/291/294/308/314 all verified in the copied file). Licence Apache-2.0 consistent in entry.json, source note and upstream-LICENSE (Apache License 2.0). | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/teorth/pfr at commit `1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a`, under `Apache-2.0`; see the [source note](../../sources/pfr/SOURCE.md) for the licence text and attribution.
