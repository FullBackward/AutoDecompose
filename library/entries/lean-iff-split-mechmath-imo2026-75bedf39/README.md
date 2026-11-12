# Iff split for IMO 2026 Q4: MulanCanGuarantee θ iff θ = 180/n for some n ≥ 2

| | |
|---|---|
| Kind | instance |
| Move | iff-split |
| Language | lean |
| Status | draft |
| Source | [mechmath-imo2026](../../sources/mechmath-imo2026/SOURCE.md) at `47ff510110dd` |
| Licence | `LicenseRef-unknown` |

## Intent

Reduce the triangle game's headline biconditional — Mulan can force a winning
angle `θ` from every valid triangle exactly when `θ = 180 / n` for some integer
`n ≥ 2` — to two already-proved named lemmas per direction. A rewrite lemma,
`arithmetic_bridge`, first converts the intermediate predicate `Marked θ 180`
into the arithmetic `∃ n, 2 ≤ n ∧ θ = 180 / n` form; then `constructor` splits
the `↔` and each direction closes in one step (necessity by `safe_start` +
`safe_nonwin`, sufficiency by `universal_win`).

## The decomposition

### parent `main_theorem`: [`IMO2026/Q4/solution.lean` lines 383-398](https://github.com/MechMath/IMO2026/blob/47ff510110dd400c98aee2ead3be0f53f7b8ba04/IMO2026/Q4/solution.lean#L383-L398) ([local copy](code/IMO2026/Q4/solution.lean))

```lean
theorem main_theorem (θ : ℝ) (hθ0 : 0 < θ) (hθ180 : θ < 180) :
    MulanCanGuarantee θ ↔ ∃ n : ℕ, 2 ≤ n ∧ θ = 180 / n := by
  rw [← arithmetic_bridge hθ0 hθ180]
  constructor
  · intro hg
    by_contra hT
    have hsafe := safe_start hθ0 hθ180 hT
    have hwin := hg _ hsafe.1
    exact (safe_nonwin hθ0 hT hsafe) hwin
  · rintro ⟨m, hm, heq⟩
    have hmθ : θ < (m : ℝ) * θ := by rw [← heq]; exact hθ180
    have hm1 : (1 : ℝ) < (m : ℝ) := by
      have h : (1 : ℝ) * θ < (m : ℝ) * θ := by rw [one_mul]; exact hmθ
      exact lt_of_mul_lt_mul_right h (le_of_lt hθ0)
    have hm1n : 1 < m := by exact_mod_cast hm1
    exact universal_win hθ0 (by omega) heq
```

### child `arithmetic_bridge`: [`IMO2026/Q4/solution.lean` lines 359-381](https://github.com/MechMath/IMO2026/blob/47ff510110dd400c98aee2ead3be0f53f7b8ba04/IMO2026/Q4/solution.lean#L359-L381) ([local copy](code/IMO2026/Q4/solution.lean))

```lean
lemma arithmetic_bridge {θ : ℝ} (h0 : 0 < θ) (h180 : θ < 180) :
    Marked θ 180 ↔ ∃ n : ℕ, 2 ≤ n ∧ θ = 180 / (n : ℝ) := by
  constructor
  · rintro ⟨m, hm, heq⟩
    have hmθ : θ < (m : ℝ) * θ := by rw [← heq]; exact h180
    have hm1 : (1 : ℝ) < (m : ℝ) := by
      have h : (1 : ℝ) * θ < (m : ℝ) * θ := by rw [one_mul]; exact hmθ
      exact lt_of_mul_lt_mul_right h (le_of_lt h0)
    have hm1n : 1 < m := by exact_mod_cast hm1
    have hmpos : (0 : ℝ) < (m : ℝ) := by
      have : 0 < m := by omega
      exact_mod_cast this
    refine ⟨m, by omega, ?_⟩
    rw [eq_div_iff (ne_of_gt hmpos)]
    linarith [heq, mul_comm (m : ℝ) θ]
  · rintro ⟨n, hn, heq⟩
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    refine ⟨n, by omega, ?_⟩
    rw [heq]
    field_simp
```

### child `safe_start`: [`IMO2026/Q4/solution.lean` lines 184-200](https://github.com/MechMath/IMO2026/blob/47ff510110dd400c98aee2ead3be0f53f7b8ba04/IMO2026/Q4/solution.lean#L184-L200) ([local copy](code/IMO2026/Q4/solution.lean))

```lean
lemma safe_start {θ : ℝ} (h0 : 0 < θ) (h180 : θ < 180) (hT : ¬ Marked θ 180) :
    Safe θ ({θ / 2, θ / 2, 180 - θ} : Multiset ℝ) := by
  refine ⟨isTriangle_triple (by linarith) (by linarith) (by linarith) (by ring), ?_⟩
  intro y hy
  rw [mem_triple] at hy
  rcases hy with rfl | rfl | rfl
  · rintro ⟨m, hm, heq⟩
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith [heq, h0, hm1]
  · rintro ⟨m, hm, heq⟩
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith [heq, h0, hm1]
  · rintro ⟨m, hm, heq⟩
    refine hT ⟨m + 1, by omega, ?_⟩
    push_cast
    have h1 : ((m : ℝ) + 1) * θ = (m : ℝ) * θ + θ := by ring
    linarith [heq, h1]
```

### child `safe_nonwin`: [`IMO2026/Q4/solution.lean` lines 203-216](https://github.com/MechMath/IMO2026/blob/47ff510110dd400c98aee2ead3be0f53f7b8ba04/IMO2026/Q4/solution.lean#L203-L216) ([local copy](code/IMO2026/Q4/solution.lean))

```lean
lemma safe_nonwin {θ : ℝ} (hθ : 0 < θ) (hT : ¬ Marked θ 180)
    {s : Multiset ℝ} (hsafe : Safe θ s) : ¬ MulanWins θ s := by
  suffices h : ∀ t, MulanWins θ t → Safe θ t → False by
    exact fun hwin => h s hwin hsafe
  intro t hwin
  induction hwin with
  | @win t h =>
    intro hsafe'
    exact hsafe'.2 θ h ⟨1, le_refl 1, by push_cast; ring⟩
  | @move t L R hcut hL hR ihL ihR =>
    intro hsafe'
    rcases safe_child hθ hT hsafe' hcut with hsL | hsR
    · exact ihL hsL
    · exact ihR hsR
```

### child `universal_win`: [`IMO2026/Q4/solution.lean` lines 302-354](https://github.com/MechMath/IMO2026/blob/47ff510110dd400c98aee2ead3be0f53f7b8ba04/IMO2026/Q4/solution.lean#L302-L354) ([local copy](code/IMO2026/Q4/solution.lean))

```lean
lemma universal_win {θ : ℝ} (hθ : 0 < θ) {n : ℕ} (hn : 2 ≤ n)
    (hT : (180 : ℝ) = (n : ℝ) * θ) : MulanCanGuarantee θ := by
  have Pq : ∀ q : ℕ, 1 ≤ q → ∀ (s : Multiset ℝ) (a : ℝ),
      IsTriangle s → a ∈ s → 0 < a → a ≤ (q : ℝ) * θ → MulanWins θ s := by
    intro q hq
    induction q, hq using Nat.le_induction with
    | base =>
      intro s a hs ha ha0 hle
      simp only [Nat.cast_one, one_mul] at hle
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact small_angle_finish hθ hn hT hs ha0 hlt ha
      · exact MulanWins.win (by rw [HasAngle, ← heq]; exact ha)
    | succ q hq ih =>
      intro s a hs ha ha0 hle
      push_cast at hle
      have hexp : ((q : ℝ) + 1) * θ = (q : ℝ) * θ + θ := by ring
      rw [hexp] at hle
      by_cases hcase : a ≤ (q : ℝ) * θ
      · exact ih s a hs ha ha0 hcase
      · push_neg at hcase
        have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
        have hθq : θ ≤ (q : ℝ) * θ := by nlinarith [hθ, hq1]
        have hθa : θ < a := lt_of_le_of_lt hθq hcase
        obtain ⟨b, c, hseq, hb, hc, hsum⟩ := triangle_of_mem hs ha
        have hcut := peeling_cut hθ hb hc hsum hθa
        have hLwin : MulanWins θ ({b, 180 - b - θ, θ} : Multiset ℝ) :=
          MulanWins.win (by rw [HasAngle, mem_triple]; right; right; rfl)
        have haθ0 : 0 < a - θ := by linarith
        have hbθ0 : 0 < b + θ := by linarith
        have hRsum : c + (b + θ) + (a - θ) = 180 := by linarith
        have hRtri : IsTriangle ({c, b + θ, a - θ} : Multiset ℝ) :=
          isTriangle_triple hc hbθ0 haθ0 hRsum
        have haθmem : (a - θ) ∈ ({c, b + θ, a - θ} : Multiset ℝ) :=
          mem_triple.mpr (by right; right; rfl)
        have haθle : a - θ ≤ (q : ℝ) * θ := by linarith
        have hRwin : MulanWins θ ({c, b + θ, a - θ} : Multiset ℝ) :=
          ih _ (a - θ) hRtri haθmem haθ0 haθle
        rw [hseq]
        exact MulanWins.move hcut hLwin hRwin
  intro s hs
  have hcard : s.card = 3 := hs.1
  have hne : s ≠ 0 := by
    intro h; rw [h] at hcard; simp at hcard
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
  have ha0 : 0 < a := hs.2.1 a ha
  obtain ⟨N, hN⟩ := exists_nat_ge (a / θ)
  have haN : a ≤ (N : ℝ) * θ := (div_le_iff₀ hθ).mp hN
  set q := max N 1 with hqdef
  have hq1 : 1 ≤ q := le_max_right N 1
  have hNq : (N : ℝ) ≤ (q : ℝ) := by exact_mod_cast le_max_left N 1
  have haq : a ≤ (q : ℝ) * θ :=
    le_trans haN (mul_le_mul_of_nonneg_right hNq (le_of_lt hθ))
  exact Pq q hq1 s a hs ha ha0 haq
```

How the parts fit. `main_theorem` first rewrites the right-hand side with
`arithmetic_bridge hθ0 hθ180`, turning the goal into
`MulanCanGuarantee θ ↔ Marked θ 180`. Then `constructor` produces the two
inclusions:

```text
main_theorem (383-398)
├─ rw [← arithmetic_bridge hθ0 hθ180]     (385)  — ∃n,2≤n∧θ=180/n  ↔  Marked θ 180
├─ constructor                             (386)
│   ├─ MulanCanGuarantee θ → Marked θ 180  (necessity, 387-391)
│   │     by_contra hT : ¬ Marked θ 180
│   │     safe_start hθ0 hθ180 hT          (389)   safe triangle {θ/2,θ/2,180-θ}
│   │     safe_nonwin hθ0 hT hsafe         (391)   contradicts the win
│   └─ Marked θ 180 → MulanCanGuarantee θ  (sufficiency, 392-398)
│         rintro ⟨m, hm, heq⟩ → 1 < m → universal_win hθ0 (by omega) heq  (398)
```

Each direct lemma is a good leaf because its statement is self-contained and
its proof closes on its own or from named siblings already in the file:

- `arithmetic_bridge` (359-381) is a pure arithmetic equivalence with no project
  dependency: both directions close by `omega`/`ring`/`linarith`/`field_simp`.
  It isolates all the bookkeeping of `Marked` so the glue never unfolds it.
- `safe_start` (184-200) constructs the explicit safe triangle
  `{θ/2, θ/2, 180-θ}`; it needs only the toolkit leaf `isTriangle_triple` and
  `mem_triple`, then `nlinarith` for the two `θ/2` angles and `exact hT ⟨m+1,
  by omega, …⟩` for `180-θ`.
- `safe_nonwin` (203-216) states the invariant "no safe triangle is winning"
  and proves it by `suffices` + induction on `MulanWins`; its only named
  dependency is `safe_child` (line 214), which itself closes from
  `cut_witnesses`/`not_safe_triple`. This encapsulates the whole necessity
  obstruction behind one statement.
- `universal_win` (302-354) is the sufficiency engine: it proves
  `MulanCanGuarantee θ` by an inner strong induction `Pq` over the bound `q` on
  `a / θ`, peeling a cut at `θ` via `peeling_cut` and recursing. Its statement
  (`180 = n·θ`, `n ≥ 2`) is exactly the hypothesis the sufficiency direction
  hands it, so that direction is a one-liner.

Two lemmas used below these children are worth noting as the deeper layers of
the same tree: `safe_child` (130-181) — "if the parent is safe and `180` is
unmarked, at least one child of any cut is safe" — and `cut_witnesses` (86-109),
which normalises a cut into positive witnesses and both children's validity.

## Why it is good

1. `main_theorem` closes from exactly four named project lemmas —
   `arithmetic_bridge`, `safe_start`, `safe_nonwin`, `universal_win` — with
   `constructor` on `↔` as the only glue (lines 383-398); the file is read
   whole ([check](https://github.com/MechMath/IMO2026/blob/47ff510110dd400c98aee2ead3be0f53f7b8ba04/IMO2026/Q4/solution.lean#L383-L398)).
2. The parent's proof body is 14 lines (385-398), while the four children total
   107 lines, so the named lemmas carry the argument and the assembly stays a
   skeleton ([measurement](https://github.com/MechMath/IMO2026/blob/47ff510110dd400c98aee2ead3be0f53f7b8ba04/IMO2026/Q4/solution.lean#L383-L398)).
3. The repository README records that the file is `sorry`-free and `admit`-free
   and that `#print axioms TriangleGame.main_theorem` yields
   `[propext, Classical.choice, Quot.sound]` — no `sorryAx` and no custom axiom
   ([author-statement](https://github.com/MechMath/IMO2026/blob/47ff510110dd400c98aee2ead3be0f53f7b8ba04/README.md#L47-L62)).
4. Below `main_theorem` the longest chain of project lemmas is 5 deep
   (`main_theorem` → `safe_nonwin` → `safe_child` → `cut_witnesses` →
   `isTriangle_triple` → `mem_triple`), so the assembly is a genuine tree of
   named lemmas, not a flat list
   ([check](https://github.com/MechMath/IMO2026/blob/47ff510110dd400c98aee2ead3be0f53f7b8ba04/IMO2026/Q4/solution.lean#L203-L216)).
5. The same theorem is split the same way in the independent AxiomMath/IMO2026
   formalization, already harvested as `lean-iff-split-axiom-imo2026-5ffbca5d`
   ([known-use](../lean-iff-split-axiom-imo2026-5ffbca5d/README.md)).

In my opinion the detail worth copying is `arithmetic_bridge`: the proof does
the arithmetic once, as a named equivalence, so that the main theorem's split
happens on the clean game predicate `Marked θ 180` rather than on the
`∃ n, 2 ≤ n ∧ θ = 180 / n` formula, and the glue stays two one-liners.

## When to use it, and when not

Use it when the two directions of a biconditional are already proved as named
lemmas whose hypotheses match the theorem's exactly, so each side closes by a
single `rw`/`exact`, and when an intermediate predicate can be bridged to the
arithmetic statement by one rewrite lemma so the split happens on the simpler
side. The shape to look for is a headline `↔` whose `by` block is mostly
`rw [← bridge]`, `constructor`, and one `exact` per direction.

Avoid it when one direction needs a bespoke argument too large to name (the glue
then grows and the "two one-liners" shape is lost); when the two lemmas are
stated over different hypotheses so the hand-off needs extra rewriting; or when
there is no clean bridge lemma, so the `rw` at the top does not fire and the
`constructor` splits a still-complex formula. Also do not force it when the
"iff" is really a one-way implication with a trivial other direction.

## Consequences

`constructor` on `↔` creates exactly two goals. The necessity direction
(`MulanCanGuarantee θ → Marked θ 180`) is proved by contradiction: assume
`hT : ¬ Marked θ 180`, build a safe triangle with `safe_start`, obtain a win from
`hg`, and refute it with `safe_nonwin`. The sufficiency direction
(`Marked θ 180 → MulanCanGuarantee θ`) unpacks the mark as `⟨m, hm, heq⟩`,
re-derives `1 < m` from `θ < 180` (lines 393-397, duplicating part of
`arithmetic_bridge`'s forward direction) to satisfy `universal_win`'s `2 ≤ n`,
and applies `universal_win`.

Failure modes: dropping `θ < 180` leaves `n = 1` (θ = 180) unexcluded and both
`arithmetic_bridge` and the glue's `1 < m` argument fail; if `arithmetic_bridge`
is stated over different hypotheses the `rw [← …]` at line 385 does not fire; and
the `1 < m` re-derivation in the glue (lines 393-397) is a small duplication that
must stay in step with `arithmetic_bridge`'s forward direction.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/MechMath/IMO2026 at commit `47ff510110dd400c98aee2ead3be0f53f7b8ba04`, under `LicenseRef-unknown`; see the [source note](../../sources/mechmath-imo2026/SOURCE.md) for the licence text and attribution.
