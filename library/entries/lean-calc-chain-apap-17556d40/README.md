# calc-chain: lemma28 counting bound from a Markov bound and three norm lemmas

| | |
|---|---|
| Kind | instance |
| Move | calc-chain |
| Language | lean |
| Status | accepted |
| Source | [apap](../../sources/apap/SOURCE.md) at `fb5cb9c4f594` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T15:16:14Z |

## Intent

A statement about every k-tuple `a ∈ A ^^ k` — the counting bound
`(#A ^ k) / 2 ≤ #(l k m ε f A)`, where `l k m ε f A` collects the tuples whose
Lp-norm `‖∑ f (x - a i) - (k • (mu A ∗ᵈ f)) x‖_[2 * m]` is small — is reduced
first to a Markov-type bound (`lemma28_markov`) and then to a chain of three
inequalities, one named lemma per link: `lemma28_part_one` (a per-point
Marcinkiewicz-Zygmund bound on the k-fold sum), `lemma28_part_two` (a
translate-norm bound) and `lemma28_end` (the closing arithmetic). The glue
(lines 284-318) does nothing but sequence these four lemmas, discharging each
one's side conditions in turn.

## The decomposition

### parent `lemma28`: [`APAP/Physics/AlmostPeriodicity.lean` lines 284-318](https://github.com/YaelDillies/apap/blob/fb5cb9c4f594cbeeb160c715618d13640984c521/APAP/Physics/AlmostPeriodicity.lean#L284-L318) ([local copy](code/APAP/Physics/AlmostPeriodicity.lean))

```lean
public lemma lemma28 (hε : 0 < ε) (hm : 1 ≤ m) (hk : (64 : ℝ) * m / ε ^ 2 ≤ k) :
    (#A ^ k : ℝ) / 2 ≤ #(l k m ε f A) := by
  have : 0 < k := by
    rw [← @Nat.cast_pos ℝ]
    refine hk.trans_lt' ?_
    refine div_pos (mul_pos (by norm_num1) ?_) (pow_pos hε _)
    rw [Nat.cast_pos, ← Nat.succ_le_iff]
    exact hm
  rcases A.eq_empty_or_nonempty with (rfl | hA)
  · simp [zero_pow this.ne']
  refine lemma28_markov hε hm ?_
  have hm' : 2 * m ≠ 0 := by linarith
  have hmeq : ((2 * m : ℕ) : ℝ≥0∞) = 2 * m := by rw [Nat.cast_mul, Nat.cast_two]
  rw [← hmeq, mul_pow]
  simp only [dLpNorm_pow_eq_sum_norm hm']
  rw [sum_comm]
  have : ∀ x : G, ∑ a ∈ A ^^ k,
      ‖∑ i, f (x - a i) - (k • (mu A ∗ᵈ f)) x‖ ^ (2 * m) ≤
    (8 * m) ^ m * k ^ (m - 1) *
      ∑ a ∈ A ^^ k, ∑ i, ‖f (x - a i) - (mu A ∗ᵈ f) x‖ ^ (2 * m) :=
    lemma28_part_one hm
  refine (sum_le_sum fun x _ ↦ this x).trans ?_
  rw [← mul_sum]
  simp only [@sum_comm _ _ G]
  have (a : Fin k → G) (i : Fin k) :
      ∑ x, ‖f (x - a i) - (mu A ∗ᵈ f) x‖ ^ (2 * m) = ‖τ (a i) f - mu A ∗ᵈ f‖_[2 * m] ^ (2 * m) := by
    rw [← hmeq, dLpNorm_pow_eq_sum_norm hm']
    simp only [Pi.sub_apply, translate_apply]
  simp only [this]
  have :
    (8 * m) ^ m * k ^ (m - 1) * ∑ a ∈ A ^^ k, ∑ i, ‖τ (a i) f - mu A ∗ᵈ f‖_[2 * m] ^ (2 * m) ≤
      (8 * m) ^ m * k ^ (m - 1) * ∑ a ∈ A ^^ k, ∑ i, (2 * ‖f‖_[2 * m]) ^ (2 * m) :=
    lemma28_part_two hm hA
  refine le_trans (mod_cast this) ?_
  simpa [mul_assoc] using lemma28_end hε hm hk
```

### child `lemma28_markov`: [`APAP/Physics/AlmostPeriodicity.lean` lines 246-258](https://github.com/YaelDillies/apap/blob/fb5cb9c4f594cbeeb160c715618d13640984c521/APAP/Physics/AlmostPeriodicity.lean#L246-L258) ([local copy](code/APAP/Physics/AlmostPeriodicity.lean))

```lean
lemma lemma28_markov (hε : 0 < ε) (hm : 1 ≤ m)
    (h : ∑ a ∈ A ^^ k,
        (‖fun x : G ↦ ∑ i : Fin k, f (x - a i) - (k • (mu A ∗ᵈ f)) x‖_[2 * m] ^ (2 * m) : ℝ) ≤
      1 / 2 * (k * ε * ‖f‖_[2 * m]) ^ (2 * m) * #A ^ k) :
    (#A ^ k : ℝ) / 2 ≤ #(l k m ε f A) := by
  rw [← Nat.cast_pow, ← Fintype.card_piFinset_const] at h
  have := my_other_markov (by positivity) (by norm_num) (fun _ _ ↦ by positivity) h
  norm_num1 at this
  rw [Fintype.card_piFinset_const, mul_comm, mul_one_div, Nat.cast_pow] at this
  refine this.trans_eq ?_
  rw [l]
  congr with a : 3
  refine pow_le_pow_iff_left₀ ?_ ?_ ?_ <;> positivity
```

### child `lemma28_part_one`: [`APAP/Physics/AlmostPeriodicity.lean` lines 139-155](https://github.com/YaelDillies/apap/blob/fb5cb9c4f594cbeeb160c715618d13640984c521/APAP/Physics/AlmostPeriodicity.lean#L139-L155) ([local copy](code/APAP/Physics/AlmostPeriodicity.lean))

```lean
lemma lemma28_part_one (hm : 1 ≤ m) (x : G) :
    ∑ a ∈ A ^^ k, ‖∑ i, f (x - a i) - (k • (mu A ∗ᵈ f)) x‖ ^ (2 * m) ≤
      (8 * m) ^ m * k ^ (m - 1) *
        ∑ a ∈ A ^^ k, ∑ i, ‖f (x - a i) - (mu A ∗ᵈ f) x‖ ^ (2 * m) := by
  let f' : G → ℂ := fun a ↦ f (x - a) - (mu A ∗ᵈ f) x
  calc
    _ = ∑ a ∈ A ^^ k, ‖∑ i, f' (a i)‖ ^ (2 * m) := by
      congr with a : 1
      simp only [sum_sub_distrib, Pi.smul_apply, sum_const, card_fin, f']
    _ ≤ (4 * m) ^ m * k ^ (m - 1) * ∑ a ∈ A ^^ k, ∑ i, ‖f' (a i)‖ ^ (2 * m) :=
      marcinkiewicz_zygmund_piFinset (by lia) f' ?_
    _ ≤ _ := by gcongr; norm_num
  rw [sum_sub_distrib]
  simp only [sum_const]
  rw [← Pi.smul_apply (card A), ← smul_ddconv, card_smul_mu, ddconv_eq_sum_sub']
  simp only [boole_mul, Set.indicator_apply, mem_coe]
  rw [← sum_filter, filter_mem_eq_inter, univ_inter, sub_self]
```

### child `lemma28_part_two`: [`APAP/Physics/AlmostPeriodicity.lean` lines 263-280](https://github.com/YaelDillies/apap/blob/fb5cb9c4f594cbeeb160c715618d13640984c521/APAP/Physics/AlmostPeriodicity.lean#L263-L280) ([local copy](code/APAP/Physics/AlmostPeriodicity.lean))

```lean
lemma lemma28_part_two (hm : 1 ≤ m) (hA : A.Nonempty) :
    (8 * m) ^ m * k ^ (m - 1) * ∑ a ∈ A ^^ k, ∑ i, ‖τ (a i) f - mu A ∗ᵈ f‖_[2 * m] ^ (2 * m) ≤
      (8 * m) ^ m * k ^ (m - 1) * ∑ _a ∈ A ^^ k, ∑ _i : Fin k, (2 * ‖f‖_[2 * m]) ^ (2 * m) := by
  -- lots of the equalities about m can be automated but it's *way* slower
  have hmeq : ((2 * m : ℕ) : ℝ≥0∞) = 2 * m := by rw [Nat.cast_mul, Nat.cast_two]
  have hm' : 1 < 2 * m := (Nat.mul_le_mul_left 2 hm).trans_lt' <| by norm_num1
  have hm'' : (1 : ℝ≥0∞) ≤ 2 * m := by rw [← hmeq, Nat.one_le_cast]; exact hm'.le
  gcongr
  refine (dLpNorm_sub_le hm'').trans ?_
  rw [dLpNorm_translate, two_mul ‖f‖_[2 * m], add_le_add_iff_left]
  have hmeq' : ((2 * m : ℝ≥0) : ℝ≥0∞) = 2 * m := by
    rw [ENNReal.coe_mul, ENNReal.coe_two, ENNReal.coe_natCast]
  have : (1 : ℝ≥0) < 2 * m := by
    rw [← Nat.cast_two, ← Nat.cast_mul, Nat.one_lt_cast]
    exact hm'
  rw [← hmeq', ddconv_comm]
  refine (dLpNorm_ddconv_le this.le _ _).trans ?_
  rw [dL1Norm_mu hA, mul_one]
```

### child `lemma28_end`: [`APAP/Physics/AlmostPeriodicity.lean` lines 110-131](https://github.com/YaelDillies/apap/blob/fb5cb9c4f594cbeeb160c715618d13640984c521/APAP/Physics/AlmostPeriodicity.lean#L110-L131) ([local copy](code/APAP/Physics/AlmostPeriodicity.lean))

```lean
lemma lemma28_end (hε : 0 < ε) (hm : 1 ≤ m) (hk : 64 * m / ε ^ 2 ≤ k) :
    (8 * m) ^ m * k ^ (m - 1) * #A ^ k * k * (2 * ‖f‖_[2 * m] : ℝ) ^ (2 * m) ≤
      1 / 2 * ((k * ε) ^ (2 * m) * ∑ i : G, ‖f i‖ ^ (2 * m)) * #A ^ k := by
  have hmeq : ((2 * m : ℕ) : ℝ≥0∞) = 2 * m := by rw [Nat.cast_mul, Nat.cast_two]
  have hm' : 2 * m ≠ 0 := by
    refine mul_ne_zero two_pos.ne' ?_
    rw [← pos_iff_ne_zero, ← Nat.succ_le_iff]
    exact hm
  rw [mul_pow (2 : ℝ), ← hmeq, ← dLpNorm_pow_eq_sum_norm hm' f, ← mul_assoc, ← mul_assoc,
    mul_right_comm _ (#A ^ k : ℝ), mul_right_comm _ (#A ^ k : ℝ),
    mul_right_comm _ (#A ^ k : ℝ)]
  rw [div_le_iff₀' (by positivity)] at hk
  gcongr ?_ * _ * _
  calc
    (8 * m : ℝ) ^ m * k ^ (m - 1) * k * 2 ^ (2 * m)
      = (8 * m) ^ m * 2 ^ (2 * m) * (k ^ (m - 1) * k) := by ring
    _ = (64 * m * k / 2) ^ m := by rw [pow_sub_one_mul (by omega), pow_mul, ← mul_pow]; ring
    _ ≤ (ε ^ 2 * k * k / 2) ^ m := by gcongr
    -- FIXME: `ring` regression. See https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/ring.20regression.20in.20v4.2E19.2E0-rc2/with/511226890
    _ = (k * ε) ^ (2 * m) / 2 ^ m := by ring_nf; simp_rw [one_div]
    _ ≤ (k * ε) ^ (2 * m) / 2 ^ 1 := by gcongr; norm_num
    _ = 1 / 2 * (k * ε) ^ (2 * m) := by ring
```

How the parts fit. The parent `lemma28` first derives `0 < k` from `hk` and
splits on `A` empty or not (line 292). In the nonempty case it applies
`lemma28_markov`, leaving the hypothesis that a norm-sum is at most the half
bound. It then proves that hypothesis as a chain of inequalities, one named
lemma per link:

```
lemma28
├── lemma28_markov             — turns the counting claim into a norm bound
│     └── my_other_markov      — the file's own Markov bound it applies (line 252)
│           └── my_markov      — the strict version (line 83)
└── the norm bound, chained:
    ∑_{a∈A^^k} ‖∑_i f(x-a i) - (k•(mu A ∗ᵈ f))x‖^(2m)
      ≤ (8m)^m k^(m-1) ∑_a ∑_i ‖f(x-a i) - (mu A ∗ᵈ f)x‖^(2m)      [lemma28_part_one]
      = (8m)^m k^(m-1) ∑_a ∑_i ‖τ(a i) f - mu A ∗ᵈ f‖_[2m]^(2m)    [rewrite, lines 308-312]
      ≤ (8m)^m k^(m-1) ∑_a ∑_i (2‖f‖_[2m])^(2m)                     [lemma28_part_two]
      ≤ 1/2 · (kε)^(2m) · ∑_i ‖f i‖^(2m) · #A^k                     [lemma28_end]
```

Each child is a good leaf: its statement is self-contained and its proof closes
from library facts or from named siblings.

- `lemma28_markov` closes by applying `my_other_markov` (lines 80-91), which
  applies `my_markov` (lines 68-78); the chain of project lemmas below `lemma28`
  is therefore `lemma28_markov → my_other_markov → my_markov`, depth 3.
- `lemma28_part_one` closes from the imported
  `marcinkiewicz_zygmund_piFinset` (`AddCombi.Concentration.MarcinkiewiczZygmund`,
  imported at line 8) plus rewriting.
- `lemma28_part_two` closes from the Lp-norm facts `dLpNorm_sub_le`,
  `dLpNorm_translate`, `dLpNorm_ddconv_le` and `dL1Norm_mu`.
- `lemma28_end` closes as a pure `calc` of arithmetic (`ring`, `ring_nf`,
  `gcongr`, `norm_num`, `omega`).

## Why it is good

1. The parent `lemma28` cites its child `lemma28_markov` (line 294) — the first
   link of the chain is a real named lemma, not an inlined proof (check).
2. The glue (the parent site) is 35 lines long (lines 284-318); aside from the
   `0 < k` derivation and the `A` empty case it sequences the four lemmas
   (check).
3. The theorem-scale shape: 4 direct lemmas, glue 35 lines, child sites of 13,
   17, 18 and 22 lines (70 total), and a longest project-lemma chain below
   `lemma28` of depth 3 (measurement; counted from the copied file).
4. The authors mark `lemma28` as a blueprint node: the line before it reads
   `-- Public because it is in the blueprint` (line 283) (author-statement).
5. The same assembly is reused by the headline theorem `almost_periodicity`,
   which combines `lemma28` (line 412), `big_shifts` (line 416), `T_bound`
   (line 419) and `just_the_triangle_inequality` (line 423) (known-use).

In my opinion the detail worth copying is that each step of the norm chain is a
separately-stated lemma whose hypotheses are exactly what that step needs, so
the glue is pure sequencing: nothing is proved inline except the two rewrites
that connect one lemma's conclusion to the next lemma's hypothesis.

## When to use it, and when not

Use it when a theorem is a counting / large-deviation bound that can be
reduced to (i) a Markov-type bound turning the counting claim into a norm
bound, then (ii) a chain of inequalities each expressible as its own
self-contained named lemma — a pointwise concentration bound, a translate-norm
bound, an arithmetic end. Use it when each lemma's hypotheses are exactly what
the previous step delivers, so the glue is pure sequencing.

Avoid it when the steps do not compose into a single chain (different measure
spaces, mismatched norms), when a side condition one lemma needs (`A` nonempty,
`ε > 0`, `k` large) is not delivered by the preceding step, or when the
arithmetic end is entangled with the analytic steps and cannot be stated as a
separate `calc`.

## Consequences

The glue must discharge each child's side conditions in order: `lemma28`
derives `0 < k` from `hk` (lines 286-291) before the split, closes the `A`
empty case directly (line 293), passes `hA : A.Nonempty` to `lemma28_part_two`
(line 316) and `hε`/`hm`/`hk` to `lemma28_end` (line 318). `lemma28_markov`
needs its half-bound hypothesis, which the glue proves as the norm chain. A
failure mode is a child whose hypothesis is only delivered by a later step,
which breaks the linear chain; the empty case must be handled before the
nonempty-only lemmas apply, and the connecting rewrites (lines 308-312) must
match one lemma's conclusion to the next lemma's hypothesis exactly.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push.yml build job (leanprover/lean-action) builds the APAP project on push to master; AlmostPeriodicity.lean is part of it; commit fb5cb9c4f594cbeeb160c715618d13640984c521 on default branch | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: lemma28_markov@APAP/Physics/AlmostPeriodicity.lean:294, lemma28_part_one@APAP/Physics/AlmostPeriodicity.lean:304, lemma28_part_two@APAP/Physics/AlmostPeriodicity.lean:316, lemma28_end@APAP/Physics/AlmostPeriodicity.lean:318; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at fb5cb9c4f594cbeeb160c715618d13640984c521 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, lemma28_markov) -> cites: lemma28_markov occurs at APAP/Physics/AlmostPeriodicity.lean:294 | check_claims.py |
| 2 | verified | lines(parent, 35) -> lines: site parent has 35 lines | check_claims.py |
| 3 | verified | Counted from code/APAP/Physics/AlmostPeriodicity.lean: parent 284-318 = 35 lines; children 246-258=13, 139-155=17, 263-280=18, 110-131=22 (sum 70); 4 direct lemmas. Depth chain: lemma28 cites lemma28_markov at L294 (refine lemma28_markov hε hm ?_), lemma28_markov cites my_other_markov at L252 (have := my_other_markov ...), my_other_markov cites my_markov at L83 (· exact my_markov hc hg h) | verifier |
| 4 | verified | code/APAP/Physics/AlmostPeriodicity.lean L283: '-- Public because it is in the blueprint' (line above the lemma28 declaration at L284) | verifier |
| 5 | verified | code/APAP/Physics/AlmostPeriodicity.lean: lemma28 at L412, big_shifts at L416 (obtain ⟨a,ha,hL'⟩ := big_shifts ...), T_bound at L419 (exact T_bound hK₂ ...), just_the_triangle_inequality at L423 (have := just_the_triangle_inequality ha ht hk.bot_lt hm) | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Verified against code copy APAP/Physics/AlmostPeriodicity.lean. Parent lemma28 is 284-318 (35 lines) and cites exactly the four children: lemma28_markov@294, lemma28_part_one@304, lemma28_part_two@316, lemma28_end@318; no other named project lemma is cited in the glue. Child sites and shape numbers are exact: lemma28_markov 246-258 (13), lemma28_part_one 139-155 (17), lemma28_part_two 263-280 (18), lemma28_end 110-131 (22); direct_lemmas=4, glue_lines=35, child_lines=[13,17,18,22] all match. Closing methods match the code (my_other_markov/pow_le_pow_iff_left0; marcinkiewicz_zygmund_piFinset+gcongr/norm_num; dLpNorm_sub_le/translate/ddconv_le/dL1Norm_mu; ring/ring_nf/gcongr/norm_num/omega calc). Proof closes: empty case via simp@293, nonempty via lemma28_markov leaving a norm subgoal closed by the part_one->rewrite->part_two->end chain, ending simpa[mul_assoc] using lemma28_end@318; no sorry in any site. Depth chain lemma28->lemma28_markov->my_other_markov->my_markov is depth 3 (my_markov applied@83, declared@68). Statement texts in entry.json match the declarations verbatim. | reviewer-correctness |
| generality | accept | Move stated generally: 'one named lemma per inequality step, each with hypotheses exactly what the previous step delivers, glue as pure sequencing' (README 210-217), with the pointwise/translate-norm/arithmetic triple offered as an instance, not the rule. 'When not to use' is honest and specific: non-composing steps (mismatched norms), a side condition not delivered by the preceding step (hA, ε>0, k large — all real hypotheses of lemma28_part_two/lemma28_end), and an arithmetic end entangled with the analytic steps. Consequences are specific and grounded in the glue I read (lines 284-318): 0<k from hk before the split, A-empty case before nonempty-only lemmas, hA passed to part_two, hε/hm/hk to end, and the connecting rewrite (lines 308-312) matching one lemma's conclusion to the next's hypothesis. Good-leaf answer present (README 175-187): each child has a self-contained statement and closes from library facts (marcinkiewicz_zygmund_piFinset, dLpNorm_* lemmas) or named siblings (my_other_markov), with the arithmetic child a pure ring/gcongr calc — the bounded-prover-relevant property. | reviewer-generality |
| provenance-licence | accept | Provenance passes: check_provenance reports 1 file byte-identical at fb5cb9c4f594cbeeb160c715618d13640984c521; copied AlmostPeriodicity.lean sha256 8454cf5d... matches entry.json files[0].sha256 and 25380 bytes. Licence Apache-2.0 is consistent across entry.json source.licence, sources/apap/source.json, and SOURCE.md; upstream-LICENSE is the Apache License 2.0 text. Commit fb5cb9c4f594cbeeb160c715618d13640984c521 matches in all three places; every permalink pins that commit. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/YaelDillies/apap at commit `fb5cb9c4f594cbeeb160c715618d13640984c521`, under `Apache-2.0`; see the [source note](../../sources/apap/SOURCE.md) for the licence text and attribution.
