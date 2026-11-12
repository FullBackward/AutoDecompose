# Step-preservation of the invariant pair (s1^2 <= k*s2, s2 <= 2k) for IMO 2025 P5

| | |
|---|---|
| Kind | instance |
| Move | key-invariant |
| Language | lean |
| Status | draft |
| Source | [seed-prover](../../sources/seed-prover/SOURCE.md) at `38c59cebaf96` |
| Licence | `Apache-2.0` |

## Intent

The proof of IMO 2025 P5 in the case `l > √2 / 2` is carried by a single named
invariant: the pair `s1 ^ 2 ≤ k * s2` and `s2 ≤ 2 * k`, held together with
`¬ WinA k s1 s2`. `round15_lemma1` shows the step `k → k + 1` preserves all
three, producing a `b_next` that advances the state and re-establishes the
bounds; that one lemma is then the entire successor case of the induction, so
the invariant (not the game predicate) is what drives the contradiction.

## The decomposition

### parent `round15_lemma1`: [`SeedProver/imo2025/IMO2025/P5.lean` lines 170-245](https://github.com/ByteDance-Seed/Seed-Prover/blob/38c59cebaf969ac259196eb091757518d5b54c67/SeedProver/imo2025/IMO2025/P5.lean#L170-L245) ([local copy](code/SeedProver/imo2025/IMO2025/P5.lean))

```lean
lemma round15_lemma1 (l : ℝ) (hl0 : l > 0) (WinA : ℕ → ℝ → ℝ → Prop)
  (winA_iff : ∀ (n : ℕ) (sum1 sum2 : ℝ), WinA n sum1 sum2 ↔
    ∃ a : ℝ, a ≥ 0 ∧ sum1 + a ≤ (2 * n + 1) * l ∧
      ∀ b : ℝ, b ≥ 0 → sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 →
        WinA (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2))
  (hl : l > √2 / 2):
  ∀ (k : ℕ) (s1 s2 : ℝ),
    (¬ WinA k s1 s2) →
    (0 ≤ s1) →
    (0 ≤ s2) →
    (s1 ^ 2 ≤ (k : ℝ) * s2) →
    (s2 ≤ 2 * (k : ℝ)) →
    ∃ (b_next : ℝ),
      b_next ≥ 0 ∧
      (¬ WinA (k + 1) (s1 + b_next) (s2 + b_next ^ 2)) ∧
      (s2 + b_next ^ 2 ≤ 2 * ((k : ℝ) + 1)) ∧
      ((s1 + b_next) ^ 2 ≤ ((k : ℝ) + 1) * (s2 + b_next ^ 2)) := by
  intro k s1 s2 h1 h2 h_s2_nonneg h3 h4
  have h5 := (round8_LoseA_iff l WinA winA_iff k s1 s2).mp h1
  have h6 := h5 0 (by linarith)
  have h7 : s1 ^ 2 ≤ 2 * (k : ℝ) ^ 2 := by
    have h71 : s1 ^ 2 ≤ (k : ℝ) * s2 := h3
    have h72 : s2 ≤ 2 * (k : ℝ) := h4
    have h73 : (k : ℝ) * s2 ≤ (k : ℝ) * (2 * (k : ℝ)) := by
      have h731 : 0 ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
      nlinarith
    have h74 : (k : ℝ) * (2 * (k : ℝ)) = 2 * (k : ℝ) ^ 2 := by ring
    nlinarith
  have h8 : s1 ≤ Real.sqrt 2 * (k : ℝ) := by
    have h81 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have h82 : 0 ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
    have h83 : s1 ^ 2 ≤ 2 * (k : ℝ) ^ 2 := h7
    have h84 : s1 ≤ Real.sqrt 2 * (k : ℝ) := by
      nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, sq_nonneg s1, sq_nonneg ((k : ℝ)), mul_nonneg h81 h82]
    linarith
  have h9 : (2 * (k : ℝ) + 1) * l ≥ Real.sqrt 2 * (k : ℝ) := by
    have h91 : l > Real.sqrt 2 / 2 := hl
    have h92 : 0 < l := by linarith
    have h93 : 0 ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
    have h94 : 2 * l - Real.sqrt 2 > 0 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h10 : s1 ≤ (2 * (k : ℝ) + 1) * l := by linarith
  have h11 : ∃ (b : ℝ), b ≥ 0 ∧ s2 + b ^ 2 ≤ 2 * (k : ℝ) + 2 ∧ ¬ WinA (k + 1) (s1 + b) (s2 + b ^ 2) := by
    have h61 : s1 > (2 * (k : ℝ) + 1) * l ∨ (∃ (b : ℝ), b ≥ 0 ∧ s2 + 0 ^ 2 + b ^ 2 ≤ 2 * (k : ℝ) + 2 ∧ ¬ WinA (k + 1) (s1 + 0 + b) (s2 + 0 ^ 2 + b ^ 2)) := by simpa using h6
    have h62 : ¬ (s1 > (2 * (k : ℝ) + 1) * l) := by linarith
    have h63 : ∃ (b : ℝ), b ≥ 0 ∧ s2 + 0 ^ 2 + b ^ 2 ≤ 2 * (k : ℝ) + 2 ∧ ¬ WinA (k + 1) (s1 + 0 + b) (s2 + 0 ^ 2 + b ^ 2) := by tauto
    rcases h63 with ⟨b, hb1, hb2, hb3⟩
    refine ⟨b, hb1, ?_, ?_⟩
    · ring_nf at hb2 ⊢ <;> linarith
    · simpa using hb3
  rcases h11 with ⟨b, hb1, hb2, hb3⟩
  have h12 : (k : ℝ) * b ^ 2 - 2 * s1 * b + s2 ≥ 0 := by
    by_cases h121 : (k : ℝ) = 0
    · -- Case 1: (k : ℝ) = 0
      have h1211 : s1 = 0 := by
        have h1212 : s1 ^ 2 ≤ (k : ℝ) * s2 := h3
        rw [h121] at h1212
        have h1213 : s1 ^ 2 ≤ 0 := by nlinarith
        have h1214 : s1 ^ 2 ≥ 0 := by positivity
        have h1215 : s1 ^ 2 = 0 := by linarith
        have h1216 : s1 = 0 := by nlinarith
        exact h1216
      rw [h121, h1211]
      <;> nlinarith
    · -- Case 2: (k : ℝ) ≠ 0
      have h122 : (k : ℝ) > 0 := by
        have h1221 : (k : ℝ) ≥ 0 := by exact_mod_cast Nat.zero_le k
        by_contra h1222
        have h1223 : (k : ℝ) ≤ 0 := by linarith
        have h1224 : (k : ℝ) = 0 := by linarith
        contradiction
      nlinarith [sq_nonneg (b * (k : ℝ) - s1), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2, sq_nonneg (s1), sq_nonneg ((k : ℝ)), sq_nonneg (b), h3, mul_nonneg h122.le h_s2_nonneg]
  have h13 : (s1 + b) ^ 2 ≤ ((k : ℝ) + 1) * (s2 + b ^ 2) := by
    nlinarith
  refine ⟨b, hb1, hb3, by linarith, h13⟩
```

### context `round15_h_main`: [`SeedProver/imo2025/IMO2025/P5.lean` lines 248-287](https://github.com/ByteDance-Seed/Seed-Prover/blob/38c59cebaf969ac259196eb091757518d5b54c67/SeedProver/imo2025/IMO2025/P5.lean#L248-L287) ([local copy](code/SeedProver/imo2025/IMO2025/P5.lean))

```lean
lemma round15_h_main (l : ℝ) (hl0 : l > 0) (WinA : ℕ → ℝ → ℝ → Prop)
  (winA_iff : ∀ (n : ℕ) (sum1 sum2 : ℝ), WinA n sum1 sum2 ↔
    ∃ a : ℝ, a ≥ 0 ∧ sum1 + a ≤ (2 * n + 1) * l ∧
      ∀ b : ℝ, b ≥ 0 → sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 →
        WinA (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2))
  (hl : l > √2 / 2)
  (h : ¬ WinA 0 0 0)
  (lemma1 : ∀ (k : ℕ) (s1 s2 : ℝ),
    (¬ WinA k s1 s2) →
    (0 ≤ s1) →
    (0 ≤ s2) →
    (s1 ^ 2 ≤ (k : ℝ) * s2) →
    (s2 ≤ 2 * (k : ℝ)) →
    ∃ (b_next : ℝ),
      b_next ≥ 0 ∧
      (¬ WinA (k + 1) (s1 + b_next) (s2 + b_next ^ 2)) ∧
      (s2 + b_next ^ 2 ≤ 2 * ((k : ℝ) + 1)) ∧
      ((s1 + b_next) ^ 2 ≤ ((k : ℝ) + 1) * (s2 + b_next ^ 2))):
  ∀ k : ℕ, ∃ s1 s2 : ℝ, (0 ≤ s1) ∧ (0 ≤ s2) ∧ (s1 ^ 2 ≤ (k : ℝ) * s2) ∧ (s2 ≤ 2 * (k : ℝ)) ∧ (¬ WinA k s1 s2) := by
  intro k
  induction k with
  | zero =>
    refine ⟨0, 0, by norm_num, by norm_num, by norm_num, by norm_num, h⟩
  | succ k ih =>
    rcases ih with ⟨s1, s2, h1, h2, h3, h4, h5⟩
    have h6 := lemma1 k s1 s2 h5 h1 h2 h3 h4
    rcases h6 with ⟨b_next, h_b_next1, h_b_next2, h_b_next3, h_b_next4⟩
    refine ⟨s1 + b_next, s2 + b_next ^ 2, ?_, ?_, ?_, ?_, ?_⟩
    · -- 0 ≤ s1 + b_next
      nlinarith
    · -- 0 ≤ s2 + b_next ^ 2
      nlinarith [sq_nonneg b_next]
    · -- (s1 + b_next) ^ 2 ≤ ((k + 1 : ℕ) : ℝ) * (s2 + b_next ^ 2)
      simp [Nat.cast_add, Nat.cast_one] at *
      <;> linarith
    · -- s2 + b_next ^ 2 ≤ 2 * ((k + 1 : ℕ) : ℝ)
      simp [Nat.cast_add, Nat.cast_one] at *
      <;> linarith
    · -- ¬ WinA (k + 1) (s1 + b_next) (s2 + b_next ^ 2)
      exact h_b_next2
```

How the parts fit. The invariant is stated twice in the lemma's own type: as
the hypotheses `s1 ^ 2 ≤ (k:ℝ) * s2` and `s2 ≤ 2 * (k:ℝ)` (together with
`¬ WinA k s1 s2`), and as the last two conjuncts of the `∃ b_next` conclusion.
The proof of `round15_lemma1` unfolds `¬ WinA k s1 s2` with the iff
`round8_LoseA_iff` (lines 9-56 of the same file) to get a disjunction, then
instantiates it at `a = 0` (`h6`, line 189). From the invariant it derives
`s1 ≤ (2k+1)·l` (`h7`-`h10`, lines 190-212): `h3` and `h4` give `s1^2 ≤ 2k^2`
(`h7`), hence `s1 ≤ √2·k` (`h8`), and `hl` gives `(2k+1)·l ≥ √2·k` (`h9`). That
rules out the first disjunct and leaves `h11`, the existence of the witness `b`
with `b ≥ 0`, `s2 + b^2 ≤ 2k+2` and `¬ WinA (k+1) (s1+b) (s2+b^2)`. The two
bounds are then re-established for `k+1`: `h12` (the algebraic step
`k·b^2 − 2·s1·b + s2 ≥ 0`) is closed by a case split on `(k:ℝ) = 0` — when
`k = 0` the invariant `h3` forces `s1 = 0`, otherwise `nlinarith` uses `h3` —
and `h13` (`(s1+b)^2 ≤ (k+1)·(s2+b^2)`) follows by `nlinarith` from `h12`.
Line 245 repacks the four conjuncts with `refine ⟨b, hb1, hb3, by linarith, h13⟩`.

The context excerpt shows where the invariant is going: `round15_h_main` proves
`∀ k, ∃ s1 s2, (0 ≤ s1) ∧ (0 ≤ s2) ∧ (s1^2 ≤ k·s2) ∧ (s2 ≤ 2k) ∧ ¬ WinA k s1 s2`
by induction on `k`. The base case is `h : ¬ WinA 0 0 0`; the successor case
takes the induction hypothesis as `h1 … h5`, applies `lemma1` (i.e.
`round15_lemma1`) with them (`have h6 := lemma1 k s1 s2 h5 h1 h2 h3 h4`,
line 273), and repacks the returned `b_next` into the state at `k+1`, restoring
the invariant and `¬ WinA` (lines 275-287).

## Why it is good

1. The parent `round15_lemma1` closes from three intermediate goals and no
   further named lemma: the witness `b` from `round8_LoseA_iff` (`h11`, lines
   213-220), the algebraic step `k*b^2 - 2*s1*b + s2 ≥ 0` by a case split on
   `(k:ℝ) = 0` (`h12`, lines 222-242), and the step-preservation
   `(s1+b)^2 ≤ (k+1)*(s2+b^2)` by `nlinarith` (`h13`, lines 243-244), repacked
   at line 245 (`check`, lines 213-245).
2. The invariant pair is written out as an inductive hypothesis in three
   declarations — `round15_lemma1` (lines 180-181), `round15_h_main`'s `lemma1`
   parameter (259-260) and the inlined `lemma1` in `imo2025_p5_algebra_A`
   (303-304) — and as a conclusion in three places (185-186, 266, 311)
   (`measurement`, grep for the two conjuncts; see the claim for the line
   list).
3. `round15_h_main`'s successor case applies the step-preservation lemma and
   repacks its output: `have h6 := lemma1 k s1 s2 h5 h1 h2 h3 h4` (line 273),
   then `refine ⟨s1 + b_next, s2 + b_next ^ 2, ...⟩` (lines 275-287) restores
   the two invariant conjuncts and `¬ WinA` at `k+1` (`known-use`, lines
   271-287).
4. The invariant is what drives the final contradiction: in
   `imo2025_p5_algebra_A`, `h_main N` (line 315) yields `h3 : s1^2 ≤ N*s2` and
   `h4 : s2 ≤ 2*N`, which feed `round8_quadratic_growth_contradiction` (line
   329, needing `h6 : s1 ≤ √2·N` derived from `h3`,`h4` at lines 317-328) to
   force `s2 + ((2N+1)l - s1)^2 > 2N+2`, which `round8_LoseA_iff` then
   contradicts (lines 339-350) (`check`, lines 313-350).

In my opinion the detail worth copying is that the invariant is *named and its
step is a standalone lemma*, not an inline `have`: the induction
(`round15_h_main`) and the final theorem both use the invariant only through
`lemma1`'s signature, so the strengthened induction hypothesis and its
step-preservation proof are one reusable unit.

## When to use it, and when not

Use a key invariant when the proof is an induction (or a fixpoint/reachability
argument) whose inductive hypothesis alone is too weak to take the step, so the
real content is a strengthened hypothesis — a potential or invariant pair
tying two quantities (here `s1² ≤ k·s2` and `s2 ≤ 2k`) — together with a
step lemma that re-establishes it at `k+1`. It applies when the step needs to
*produce* a witness (here `b_next`) that both advances the index and keeps the
bounds, and the strengthened hypothesis is strong enough to rule out the
undesired branch of a disjunction (here `s1 > (2k+1)·l` via `h10`).

Avoid it when a plain induction already goes through (the invariant would be
vacuous), when the invariant cannot be stated as a self-contained
`∀ k, P k → P (k+1)` lemma because its proof needs state from outside the
hypotheses, or when the step-preservation proof itself is the hard part and the
invariant does not actually simplify it.

## Consequences

The move's obligation is to *re-establish* the invariant after the step, not
merely assume it: `round15_lemma1` must produce `b_next` and prove both bounds
at `k+1` (via `h12`→`h13` and the `s2` bound) plus `¬ WinA` (via `h11`). The
strengthened hypothesis carries two further obligations: its base case must be
discharged (`round15_h_main`'s zero case uses `h : ¬ WinA 0 0 0`), and the
witness only exists because the WinA iff (`round8_LoseA_iff`) is instantiated
at `a = 0` and its first disjunct refuted — so a weaker invariant (e.g. `s2 ≤
2k` alone) would not derive `h10 : s1 ≤ (2k+1)·l` and no witness would follow.
Known failure mode: the algebraic step `h12` needs a genuine case split at
`k = 0` (where `h3` degenerates and forces `s1 = 0`), so the invariant must be
stated so that its boundary case is decidable rather than assumed.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | not-run | No CI workflow in the source: list_files.py seed-prover at commit 38c59cebaf969ac259196eb091757518d5b54c67 lists 579 files with no .github/workflows/ directory and no .yml/.yaml CI config, so no workflow builds SeedProver/imo2025/IMO2025/P5.lean. | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 38c59cebaf969ac259196eb091757518d5b54c67 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read copied P5.lean L170-L245. round15_lemma1 body references only round8_LoseA_iff (L188); h11 (L213-220) obtains witness b from round8_LoseA_iff via h5/h6 instantiated at a=0; h12 (L222-242) by_cases on (k:R)=0; h13 (L243-244) nlinarith; L245 refine <b, hb1, hb3, by linarith, h13>. Matches claim. | verifier |
| 2 | verified | grep on copied P5.lean: "s1 ^ 2 <= (k : R) * s2" -> 7 lines (180, 191, 226, 259, 266, 303, 311); "s2 <= 2 * (k : R)" -> 6 lines (181, 192, 260, 266, 304, 311). Both counts and line lists match the claim. | verifier |
| 3 | verified | Read copied P5.lean L271-L287: L273 have h6 := lemma1 k s1 s2 h5 h1 h2 h3 h4; L275 refine <s1 + b_next, s2 + b_next ^ 2, ...> then L276-287 restores 0<=s1+b_next, 0<=s2+b_next^2, both invariant conjuncts, and not-WinA (k+1). Matches claim. | verifier |
| 4 | verified | Read copied P5.lean L313-L350: h14 = round8_quadratic_growth_contradiction (L313); h15 := h_main N (L315) -> h3 : s1^2<=N*s2, h4 : s2<=2N (L316); h6 : s1 <= Real.sqrt 2 * N derived from h3,h4 (L317-328); h7 := hN s1 s2 h1 h6 h2 h4 (L329); round8_LoseA_iff .mp h5 (L339) rcases both branches end in linarith (L344, L350) contradicting h7. Matches claim. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent round15_lemma1 (code L170-245) matches entry parent.statement verbatim. Children h11/h12/h13 (L213/L222/L243) match their recorded statements. h11 closes via round8_LoseA_iff.mp at a=0 (h6), refuting the s1>(2k+1)l disjunct with h10 then tauto, rcases and ring_nf/simpa; h12 closes by by_cases (k:ℝ)=0 forcing s1=0 from h3 then nlinarith, else nlinarith with sq_nonneg(b*k-s1); h13 closes by nlinarith from h12. L245 refine <b,hb1,hb3,by linarith,h13> supplies all four conjuncts in order, so the parent closes. round15_h_main (L248-287) matches the context excerpt and applies lemma1 at L273 with args h5 h1 h2 h3 h4 in signature order, repacking the five subgoals; imo2025_p5_algebra_A (L292-350) closes via h_main N (L315) -> h3/h4 -> h6 (L317-328) -> round8_quadratic_growth_contradiction (L329) -> round8_LoseA_iff contradiction (L339-350). Claim line references (h11 213-220, h12 222-242, h13 243-244, refine 245) all accurate; grep counts in claim 2 (7 and 6 matches) verified against the copied file. | reviewer-correctness |
| generality | accept | Move is stated beyond the example: the 'When to use' abstracts to any induction/fixpoint/reachability whose plain IH is too weak, carried by a named invariant (potential / invariant pair) plus a self-contained forall k, P k -> P (k+1) step lemma that re-establishes it, with witness-production and disjunction-ruling as extra conditions rather than the whole move. 'When not to use' gives three specific, honest avoid conditions (plain induction suffices -> invariant vacuous; invariant not expressible as a self-contained step lemma because it needs outside state; invariant does not simplify the hard part). Consequences are specific and honest and match the copied code: obligation to re-establish not assume, base case discharge via h : not WinA 0 0 0, witness b_next exists only via the full invariant (a weaker s2<=2k invariant would not derive h10 so no witness), and a concrete failure mode (h12's algebraic step needs a real case split at k=0). | reviewer-generality |
| provenance-licence | accept | check_provenance.py passes (1 file byte-identical at 38c59cebaf969ac259196eb091757518d5b54c67). Copied file sha256 875e09cd...e7966 and 39490 bytes match entry.json files[0]. Commit is identical across entry.json, sources/seed-prover/SOURCE.md and source.json. Licence Apache-2.0 consistent across entry.json, SOURCE.md, source.json, and sources/seed-prover/upstream-LICENSE is the Apache 2.0 text. All permalinks use the pinned commit and the path SeedProver/imo2025/IMO2025/P5.lean, matching files[0].path and both site paths. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/ByteDance-Seed/Seed-Prover at commit `38c59cebaf969ac259196eb091757518d5b54c67`, under `Apache-2.0`; see the [source note](../../sources/seed-prover/SOURCE.md) for the licence text and attribution.
