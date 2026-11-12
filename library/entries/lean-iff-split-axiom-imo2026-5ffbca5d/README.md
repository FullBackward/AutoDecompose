# Iff split of the triangle-game main theorem: Mulan can guarantee θ iff θ = 180/n for some n ≥ 2

| | |
|---|---|
| Kind | instance |
| Move | iff-split |
| Language | lean |
| Status | draft |
| Source | [axiom-imo2026](../../sources/axiom-imo2026/SOURCE.md) at `c5a6a089d06d` |
| Licence | `MIT` |

## Intent

Assemble the triangle game's headline result — Mulan can force a winning
angle θ from every valid triangle in finitely many steps exactly when
`θ = 180 / n` for some integer `n ≥ 2` — by splitting the biconditional with
`constructor` and closing each direction with one named lemma already proved
above. The necessity direction derives `∃ z, 180 = z·θ` by contradiction with
`equilateral_counterexample` and converts `z` to a natural `n ≥ 2`; the
sufficiency direction rewrites `θ = 180/n` to `180 = n·θ` and hands off to
`all_win_of_divides`.

## The decomposition

### parent `main_theorem`: [`IMO2026/Q4/solution.lean` lines 469-518](https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q4/solution.lean#L469-L518) ([local copy](code/IMO2026/Q4/solution.lean))

```lean
theorem main_theorem (θ : ℝ) (hθ0 : 0 < θ) (hθ180 : θ < 180) :
    MulanCanGuarantee θ ↔ ∃ n : ℕ, 2 ≤ n ∧ θ = 180 / n := by
  constructor
  · -- Forward (necessity): MulanCanGuarantee θ → ∃ n ≥ 2, θ = 180/n.
    intro hguar
    -- Step A: `180` IS an integer multiple of `θ`.
    -- If not (i.e. `(*)` holds), `equilateral_counterexample` contradicts `hguar`.
    -- So obtain `z : ℤ` with `180 = (z:ℝ)*θ`.
    have hmult : ∃ z : ℤ, (180 : ℝ) = (z : ℝ) * θ := by
      -- by_contra: push_neg gives `∀ z, 180 ≠ (z:ℝ)*θ = (*)`;
      -- then `equilateral_counterexample θ hθ0 (*)` contradicts `hguar`.
      by_contra h; push_neg at h; exact equilateral_counterexample θ hθ0 h hguar
    obtain ⟨z, hz⟩ := hmult
    -- Step B: `z > 0` (since `180 = z*θ`, `θ>0` ⇒ `z*θ>0` ⇒ `z>0`), so `z = (n:ℕ)`
    -- with `n ≥ 1`; `n ≠ 1` since `θ < 180` (n=1 ⇒ θ=180); hence `n ≥ 2`.
    -- Then `θ = 180/n` from `180 = n*θ`, `n ≠ 0`.
    have hzpos : 0 < z := by
      have hzθ : 0 < (z : ℝ) * θ := by rw [← hz]; norm_num
      have hzr : 0 < (z : ℝ) := by
        by_contra hle
        push_neg at hle
        nlinarith [hzθ, hθ0, hle]
      exact_mod_cast hzr
    have hz2 : 2 ≤ z := by
      by_contra hlt
      push_neg at hlt
      interval_cases z
      · -- z = 1: 180 = θ, contradiction
        simp at hz; linarith
    have htoNat : (z.toNat : ℝ) = (z : ℝ) := by
      have := Int.toNat_of_nonneg (le_of_lt hzpos)
      exact_mod_cast this
    refine ⟨z.toNat, ?_, ?_⟩
    · -- 2 ≤ z.toNat
      omega
    · -- θ = 180 / z.toNat
      rw [htoNat]
      have hzne : (z : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hzpos)
      field_simp
      linarith [hz]
  · -- Reverse (sufficiency): (∃ n ≥ 2, θ = 180/n) → MulanCanGuarantee θ.
    rintro ⟨n, hn, hθ⟩
    -- From `θ = 180/n` and `n ≥ 2` (so `(n:ℝ) ≠ 0`), get `180 = (n:ℝ)*θ`.
    -- Then `all_win_of_divides θ hθ0 n hn hdvd` gives `MulanCanGuarantee θ`.
    have hdvd : (180 : ℝ) = (n : ℝ) * θ := by
      have hn0 : (n : ℝ) ≠ 0 := by
        have : n ≠ 0 := by omega
        exact_mod_cast this
      rw [hθ]; field_simp
    exact all_win_of_divides θ hθ0 n hn hdvd
```

### child `equilateral_counterexample`: [`IMO2026/Q4/solution.lean` lines 444-462](https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q4/solution.lean#L444-L462) ([local copy](code/IMO2026/Q4/solution.lean))

```lean
theorem equilateral_counterexample (θ : ℝ) (hθ0 : 0 < θ)
    (hstar : ∀ z : ℤ, (180 : ℝ) ≠ (z : ℝ) * θ) :
    ¬ MulanCanGuarantee θ := by
  intro hguar
  set e : Multiset ℝ := {60, 60, 60} with he
  have hetri : IsTriangle e := by
    refine ⟨?_, ?_, ?_⟩
    · rw [he]; exact card_triple _ _ _
    · intro y hy; rw [he, mem_triple] at hy; rcases hy with h | h | h <;> (rw [h]; norm_num)
    · rw [he, sum_triple]; norm_num
  have hesafe : Safe θ e := by
    intro a ha z heq
    rw [he, mem_triple] at ha
    have h60 : a = 60 := by rcases ha with h | h | h <;> exact h
    rw [h60] at heq
    -- 60 = z*θ ⇒ 180 = (3z)*θ
    apply hstar (3 * z)
    push_cast; linarith [heq]
  exact safe_not_win θ hθ0 hstar hetri hesafe (hguar e hetri)
```

### child `all_win_of_divides`: [`IMO2026/Q4/solution.lean` lines 251-360](https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q4/solution.lean#L251-L360) ([local copy](code/IMO2026/Q4/solution.lean))

```lean
theorem all_win_of_divides (θ : ℝ) (hθ0 : 0 < θ) (n : ℕ) (hn : 2 ≤ n)
    (hdvd : (180 : ℝ) = (n : ℝ) * θ) :
    ∀ s : Multiset ℝ, IsTriangle s → MulanWins θ s := by
  have hθne : θ ≠ 0 := ne_of_gt hθ0
  intro s hs
  obtain ⟨hcard, hpos, hsum⟩ := hs
  have hs' : IsTriangle s := ⟨hcard, hpos, hsum⟩
  obtain ⟨a, b, c, hs_eq⟩ := Multiset.card_eq_three.mp hcard
  have ha : 0 < a := hpos a (by rw [hs_eq, mem_triple]; tauto)
  have hb : 0 < b := hpos b (by rw [hs_eq, mem_triple]; tauto)
  have hc : 0 < c := hpos c (by rw [hs_eq, mem_triple]; tauto)
  have habc : a + b + c = 180 := by rw [hs_eq, sum_triple] at hsum; exact hsum
  -- Case A: some angle is an integer multiple of θ
  by_cases hcaseA : ∃ v ∈ s, ∃ z : ℤ, v = (z : ℝ) * θ
  · obtain ⟨v, hvmem, z, hveq⟩ := hcaseA
    have hvpos : 0 < v := hpos v hvmem
    have hzpos : 0 < z := by
      have : 0 < (z : ℝ) * θ := by rw [← hveq]; exact hvpos
      have hzr : 0 < (z : ℝ) := by
        by_contra hle; push_neg at hle; nlinarith [this, hθ0, hle]
      exact_mod_cast hzr
    have hk : (z.toNat : ℝ) * θ ∈ s := by
      have : (z.toNat : ℝ) = (z : ℝ) := by
        have := Int.toNat_of_nonneg (le_of_lt hzpos); exact_mod_cast this
      rw [this, ← hveq]; exact hvmem
    exact win_of_multiple θ hθ0 z.toNat (by omega) s hs' hk
  · -- Case B: no angle is a multiple of θ
    push_neg at hcaseA
    -- normalize
    set ra := a / θ with hra
    set rb := b / θ with hrb
    set rc := c / θ with hrc
    have hra_pos : 0 < ra := by rw [hra]; positivity
    have hrb_pos : 0 < rb := by rw [hrb]; positivity
    have hrc_pos : 0 < rc := by rw [hrc]; positivity
    -- sum = n
    have hn0 : (n : ℝ) ≠ 0 := by
      have : n ≠ 0 := by omega
      exact_mod_cast this
    have hsum_r : ra + rb + rc = (n : ℝ) := by
      rw [hra, hrb, hrc]
      field_simp
      -- (a + b + c) = n * θ  and a+b+c = 180 = n*θ
      rw [habc]; linarith [hdvd]
    -- none is an integer
    have hni : ∀ z : ℤ, ra ≠ (z : ℝ) ∧ rb ≠ (z : ℝ) ∧ rc ≠ (z : ℝ) := by
      intro z
      refine ⟨?_, ?_, ?_⟩
      · intro heq
        exact hcaseA a (by rw [hs_eq, mem_triple]; tauto) z (by rw [hra] at heq; field_simp at heq; linarith [heq])
      · intro heq
        exact hcaseA b (by rw [hs_eq, mem_triple]; tauto) z (by rw [hrb] at heq; field_simp at heq; linarith [heq])
      · intro heq
        exact hcaseA c (by rw [hs_eq, mem_triple]; tauto) z (by rw [hrc] at heq; field_simp at heq; linarith [heq])
    obtain ⟨α', β', γ', m, hperm, hm1, hmn, hγm, hmγα, hsabc⟩ :=
      interval_lemma ra rb rc n hn hra_pos hrb_pos hrc_pos hsum_r hni
    -- actual angles
    set α := α' * θ with hα
    set β := β' * θ with hβ
    set γ := γ' * θ with hγ
    -- s = {α, β, γ}
    have hs_eq2 : s = {α, β, γ} := by
      rw [hs_eq]
      -- {a,b,c} = map (·*θ) {ra,rb,rc}, and {α,β,γ} = map (·*θ) {α',β',γ'}
      have hmapL : ({a, b, c} : Multiset ℝ) = Multiset.map (· * θ) {ra, rb, rc} := by
        simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
        rw [hra, hrb, hrc]
        congr 1
        · field_simp
        congr 1
        · field_simp
        congr 1
        · field_simp
      have hmapR : ({α, β, γ} : Multiset ℝ) = Multiset.map (· * θ) {α', β', γ'} := by
        simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
        rw [hα, hβ, hγ]
      rw [hmapL, hmapR, hperm]
    -- sum α+β+γ = 180
    have hsumαβγ : α + β + γ = 180 := by
      rw [hα, hβ, hγ]
      have : (α' + β' + γ') * θ = (n : ℝ) * θ := by rw [hsabc]
      rw [hdvd]; nlinarith [this]
    -- cut parameter x = m*θ
    have hγx : γ < (m : ℝ) * θ := by rw [hγ]; nlinarith [hγm, hθ0]
    have hxβ : (m : ℝ) * θ < 180 - β := by
      -- m < γ'+α' ⇒ mθ < (γ'+α')θ = γ+α = 180-β
      rw [hβ]
      have h1 : (m : ℝ) * θ < (γ' + α') * θ := by nlinarith [hmγα, hθ0]
      have h2 : (γ' + α') * θ = 180 - β' * θ := by
        have : γ + α = 180 - β := by rw [hα, hβ, hγ] at *; linarith [hsumαβγ]
        rw [hγ, hα] at this; nlinarith [this]
      linarith [h1, h2]
    have hcut : IsCut s {β, (m : ℝ) * θ, 180 - β - (m : ℝ) * θ}
        {γ, 180 - (m : ℝ) * θ, (m : ℝ) * θ - γ} :=
      ⟨α, β, γ, (m : ℝ) * θ, hs_eq2, hγx, hxβ, rfl, rfl⟩
    apply MulanWins.move hcut
    · -- L wins: contains mθ = (m:ℝ)*θ, m ≥ 1
      obtain ⟨hLtri, _⟩ := cut_preserves hs' hcut
      apply win_of_multiple θ hθ0 m hm1 _ hLtri
      rw [mem_triple]; right; left; rfl
    · -- R wins: contains 180 - mθ = (n-m)θ, n-m ≥ 1
      obtain ⟨_, hRtri⟩ := cut_preserves hs' hcut
      apply win_of_multiple θ hθ0 (n - m) (by omega) _ hRtri
      rw [mem_triple]; right; left
      -- 180 - mθ = (n-m)*θ
      have hnm : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
        have : m ≤ n := by omega
        push_cast [Nat.cast_sub this]; ring
      rw [hnm]
      rw [hdvd]; ring
```

How the parts fit. The lemma graph (each arrow is an `exact`/`apply` of a
named project lemma; `→` reads "uses"):

```
main_theorem (constructor on ↔, two directions)
├─ necessity   ── equilateral_counterexample θ hθ0 h hguar            (line 480)
│   equilateral_counterexample (Lemma 8)
│   └─ safe_not_win θ hθ0 hstar hetri hesafe ...                      (line 462)
│       safe_not_win (Lemma 7)
│       ├─ cut_preserves hs hcut                                      (line 435)
│       └─ safe_child θ hθ0 hstar hs hsafe hcut                       (line 436)
│           safe_child (Lemma 6)  ── leaf (rcases/linarith)
└─ sufficiency ── all_win_of_divides θ hθ0 n hn hdvd                  (line 518)
    all_win_of_divides (Lemma 5)
    ├─ win_of_multiple θ hθ0 z.toNat ...                              (line 276)
    │   win_of_multiple (Lemma 3)
    │   ├─ triangle_with_apex hs hmem                                 (line 121)
    │   └─ cut_preserves hs' hcut                                     (line 144)
    ├─ interval_lemma ra rb rc n hn ...                               (line 306)
    │   interval_lemma (Lemma 4)  ── leaf (rcases/nlinarith)
    └─ cut_preserves hs' hcut                                         (lines 348, 352)
```

The split is the whole glue: `constructor` on the `↔` produces the two
directions, and each direction's only content is the derivation that turns
the theorem's hypotheses into exactly the hypotheses of one named lemma,
then a single `exact` of that lemma. The necessity direction reduces
`MulanCanGuarantee θ` to `∃ z, 180 = z·θ` by `by_contra` against
`equilateral_counterexample`, then converts `z` to `z.toNat` and proves
`2 ≤ z.toNat` (ruling out `z = 1` with `θ < 180`). The sufficiency direction
rewrites `θ = 180/n` into `hdvd : 180 = n·θ` and applies
`all_win_of_divides`.

Why each child is a good leaf:

- `equilateral_counterexample` (Lemma 8) is a self-contained negative
  statement: under `(*)` (no integer multiple of θ equals 180) the concrete
  triangle `{60, 60, 60}` is valid and safe, hence not winning. Its proof
  closes on the named sibling `safe_not_win`, so the leaf is the pair
  `safe_not_win` → `safe_child`, each of which closes by `rcases`/`linarith`
  on its own hypotheses.

- `all_win_of_divides` (Lemma 5) is the entire sufficiency engine: it
  universalises over all valid triangles and closes either by the induction
  lemma `win_of_multiple` (Case A) or by `interval_lemma` to place a cut
  point `m·θ` and then two applications of `win_of_multiple` (Case B). Its
  statement is self-contained — `0 < θ`, `2 ≤ n`, `180 = n·θ` are exactly the
  facts the sufficiency direction can supply — so the glue never unfolds it.

The remaining labelled lemmas of the file (`cut_preserves` Lemma 2,
`win_of_multiple` Lemma 3, `interval_lemma` Lemma 4, `safe_child` Lemma 6,
`safe_not_win` Lemma 7) sit below the two children, and the structural
helpers `mem_triple`, `sum_triple`, `card_triple`, `triangle_with_apex` sit
below those. The main theorem never names them directly; they are the proof
content *inside* the two children.

## Why it is good

1. The parent closes from exactly two named project lemmas —
   `equilateral_counterexample` (line 480) and `all_win_of_divides` (line
   518) — and the `constructor` on `↔` is the only glue between them (check;
   [lines 469-518](https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q4/solution.lean#L469-L518)).
2. The glue is 50 lines while the two children carry 19 + 110 = 129 lines, so
   almost all of the argument lives in the lemmas and the assembly stays thin
   (measurement;
   [lines 469-518, 444-462, 251-360](https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q4/solution.lean#L469-L518)).
3. The authors state the goal and the equivalence explicitly: "**Main
   theorem.** … if and only if `θ = 180 / n` for some integer `n ≥ 2`"
   (author-statement;
   [lines 466-468](https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q4/solution.lean#L466-L468)).
4. Below the main theorem the longest chain of project lemmas is 3 deep
   (`main_theorem` → `equilateral_counterexample` → `safe_not_win` →
   `safe_child`, and `main_theorem` → `all_win_of_divides` →
   `win_of_multiple` → `triangle_with_apex`), so each child sits close to a
   self-contained leaf (check;
   [lines 444-462, 422-440, 372-418, 251-360, 109-155](https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q4/solution.lean#L444-L462)).

In my opinion the detail worth copying is the *hand-off discipline*: each
direction does no mathematics of its own but reduces the theorem's hypotheses
to the exact shape of one lemma's hypotheses, so the two `exact` calls are
the entire glue and the two directions read as mirror images.

## When to use it, and when not

Use it when a theorem is a genuine biconditional whose two directions are
already proved as standalone lemmas stated over matching hypotheses — a
negative lemma (a counterexample or a "not winning" statement) for the
necessity side and a universal/constructive lemma for the sufficiency side —
so each direction collapses to one `exact`. It also fits when one side needs
a small number-theoretic conversion (here `z : ℤ` to `n : ℕ`, and excluding
`n = 1` with `θ < 180`) that is short enough to keep inline.

Avoid it when one direction needs a substantial argument that has not been
lifted into a lemma (then the glue stops being glue and the split buys
nothing); when the two lemmas are stated over different hypotheses, so the
hand-off needs real rewriting rather than a `field_simp`/`linarith` shuffle;
or when the "iff" is really a one-way implication and one direction is empty.

## Consequences

The `constructor` creates exactly two goals, one per direction, and each
direction is its own obligation. The necessity side must produce
`∃ n, 2 ≤ n ∧ θ = 180/n` from `MulanCanGuarantee θ`, which here means
deriving `∃ z, 180 = z·θ` (by contradiction with
`equilateral_counterexample`) and then excluding `n = 1` via `θ < 180`. The
sufficiency side must produce `MulanCanGuarantee θ` from `θ = 180/n`, which
here is one rewrite plus `all_win_of_divides`. Failure modes: dropping
`θ < 180` leaves `n = 1` (`θ = 180`) unexcluded and necessity fails; if the
two lemmas are not stated with matching hypotheses (`0 < θ`, `hstar` for the
counterexample, `2 ≤ n` and `hdvd` for sufficiency), the `exact` hand-offs
fail and the glue grows back.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/AxiomMath/IMO2026 at commit `c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2`, under `MIT`; see the [source note](../../sources/axiom-imo2026/SOURCE.md) for the licence text and attribution.
