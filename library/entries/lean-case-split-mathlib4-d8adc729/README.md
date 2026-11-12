# Case split on the degree d < 3 vs 3 ≤ d in the Friendship Theorem

| | |
|---|---|
| Kind | instance |
| Move | case-split |
| Language | lean |
| Status | accepted |
| Source | [mathlib4](../../sources/mathlib4/SOURCE.md) at `e1545ebed975` |
| Licence | `Apache-2.0` |

## Intent

The Friendship Theorem (every finite friendship graph has a politician) is
proved by contradiction: assume no politician, obtain the regular degree `d`,
then split on `d < 3` vs `3 ≤ d`. The small-degree branch is closed by a
constructive lemma (`existsPolitician_of_degree_le_two`) and the large-degree
branch by a contradiction (`false_of_three_le_degree`), so the two halves are
entirely separate sub-arguments joined by a six-line glue.

## The decomposition

### parent `friendship_theorem`: [`Archive/Wiedijk100Theorems/FriendshipGraphs.lean` lines 330-335](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/FriendshipGraphs.lean#L330-L335) ([local copy](code/Archive/Wiedijk100Theorems/FriendshipGraphs.lean))

```lean
theorem friendship_theorem [Nonempty V] : ExistsPolitician G := by
  by_contra npG
  rcases hG.isRegularOf_not_existsPolitician npG with ⟨d, dreg⟩
  rcases lt_or_ge d 3 with dle2 | dge3
  · exact npG (hG.existsPolitician_of_degree_le_two dreg (Nat.lt_succ_iff.mp dle2))
  · exact hG.false_of_three_le_degree dreg dge3
```

### child `isRegularOf_not_existsPolitician`: [`Archive/Wiedijk100Theorems/FriendshipGraphs.lean` lines 149-175](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/FriendshipGraphs.lean#L149-L175) ([local copy](code/Archive/Wiedijk100Theorems/FriendshipGraphs.lean))

```lean
theorem isRegularOf_not_existsPolitician (hG' : ¬ExistsPolitician G) :
    ∃ d : ℕ, G.IsRegularOfDegree d := by
  have v := Classical.arbitrary V
  use G.degree v
  intro x
  by_cases hvx : G.Adj v x; swap; · exact (degree_eq_of_not_adj hG hvx).symm
  dsimp only [Theorems100.ExistsPolitician] at hG'
  push Not at hG'
  rcases hG' v with ⟨w, hvw', hvw⟩
  rcases hG' x with ⟨y, hxy', hxy⟩
  by_cases hxw : G.Adj x w
  swap; · rw [degree_eq_of_not_adj hG hvw]; exact degree_eq_of_not_adj hG hxw
  rw [degree_eq_of_not_adj hG hxy]
  by_cases hvy : G.Adj v y
  swap; · exact (degree_eq_of_not_adj hG hvy).symm
  rw [degree_eq_of_not_adj hG hvw]
  apply degree_eq_of_not_adj hG
  intro hcontra
  rcases Finset.card_eq_one.mp (hG hvw') with ⟨⟨a, ha⟩, h⟩
  have key : ∀ {x}, x ∈ G.commonNeighbors v w → x = a := by
    intro x hx
    have h' : ⟨x, hx⟩ ∈ (univ : Finset (G.commonNeighbors v w)) := mem_univ (Subtype.mk x hx)
    rw [h, mem_singleton] at h'
    injection h'
  apply hxy'
  rw [key ((mem_commonNeighbors G).mpr ⟨hvx, hxw.symm⟩),
    key ((mem_commonNeighbors G).mpr ⟨hvy, hcontra.symm⟩)]
```

### child `false_of_three_le_degree`: [`Archive/Wiedijk100Theorems/FriendshipGraphs.lean` lines 248-273](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/FriendshipGraphs.lean#L248-L273) ([local copy](code/Archive/Wiedijk100Theorems/FriendshipGraphs.lean))

```lean
theorem false_of_three_le_degree (hd : G.IsRegularOfDegree d) (h : 3 ≤ d) : False := by
  -- get a prime factor of d - 1
  let p : ℕ := (d - 1).minFac
  have p_dvd_d_pred := (ZMod.natCast_eq_zero_iff _ _).mpr (d - 1).minFac_dvd
  have dpos : 1 ≤ d := by lia
  have d_cast : ↑(d - 1) = (d : ℤ) - 1 := by norm_cast
  have : Fact p.Prime := ⟨Nat.minFac_prime (by lia)⟩
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have dmod : (d : ZMod p) = 1 := by
    rw [← Nat.succ_pred_eq_of_pos dpos, Nat.succ_eq_add_one, Nat.pred_eq_sub_one]
    simp only [add_eq_right, Nat.cast_add, Nat.cast_one]
    exact p_dvd_d_pred
  have Vmod := card_mod_p_of_regular hG dmod hd
  -- now we reduce to a trace calculation
  have := ZMod.trace_pow_card (G.adjMatrix (ZMod p))
  contrapose! this; clear this
  -- the trace is 0 mod p when computed one way
  rw [trace_adjMatrix, zero_pow this.out.ne_zero]
  -- but the trace is 1 mod p when computed the other way
  rw [adjMatrix_pow_mod_p_of_regular hG dmod hd hp2]
  dsimp only [Fintype.card] at Vmod
  simp only [Matrix.trace, Matrix.diag, mul_one, nsmul_eq_mul, sum_const,
    of_apply, Ne]
  rw [Vmod, ← Nat.cast_one (R := ZMod (Nat.minFac (d - 1))), ZMod.natCast_eq_zero_iff,
    Nat.dvd_one, Nat.minFac_eq_one_iff]
  lia
```

### child `existsPolitician_of_degree_le_two`: [`Archive/Wiedijk100Theorems/FriendshipGraphs.lean` lines 315-319](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/FriendshipGraphs.lean#L315-L319) ([local copy](code/Archive/Wiedijk100Theorems/FriendshipGraphs.lean))

```lean
theorem existsPolitician_of_degree_le_two (hd : G.IsRegularOfDegree d) (h : d ≤ 2) :
    ExistsPolitician G := by
  interval_cases d
  iterate 2 apply existsPolitician_of_degree_le_one hG hd; norm_num
  exact existsPolitician_of_degree_eq_two hG hd
```

How the parts fit. The parent proves by contradiction (`by_contra npG`), then
`isRegularOf_not_existsPolitician npG` turns "no politician" into a regular
degree `∃ d, G.IsRegularOfDegree d`, which `rcases` destructures to `d, dreg`.
The split itself is `rcases lt_or_ge d 3`, giving goals `d < 3` and `3 ≤ d`
(the exhaustiveness is the library lemma `lt_or_ge`). Each branch is closed by
one `exact` of a child lemma: `existsPolitician_of_degree_le_two dreg
(Nat.lt_succ_iff.mp dle2)` for the small degree (which still contradicts
`npG`), and `false_of_three_le_degree dreg dge3` for the large one (an outright
`False`).

The lemma graph (each arrow "uses", i.e. is proved by calling):

```
friendship_theorem
├─ isRegularOf_not_existsPolitician
│    └─ degree_eq_of_not_adj ── adjMatrix_pow_three_of_not_adj ── adjMatrix_sq_of_ne
├─ existsPolitician_of_degree_le_two
│    ├─ existsPolitician_of_degree_le_one ── card_of_regular ── adjMatrix_sq_of_regular ── adjMatrix_sq_of_ne
│    └─ existsPolitician_of_degree_eq_two ── neighborFinset_eq_of_degree_eq_two ── card_of_regular ── adjMatrix_sq_of_regular ── adjMatrix_sq_of_ne
└─ false_of_three_le_degree
     ├─ card_mod_p_of_regular ── card_of_regular ── adjMatrix_sq_of_regular ── adjMatrix_sq_of_ne
     └─ adjMatrix_pow_mod_p_of_regular ── adjMatrix_sq_mod_p_of_regular ── adjMatrix_sq_of_regular ── adjMatrix_sq_of_ne
```

Why each direct child is a good leaf:

- `isRegularOf_not_existsPolitician` has a self-contained statement
  (no-politician ⇒ regular) and closes on its own from the earlier sibling
  `degree_eq_of_not_adj`, without touching the main theorem.
- `existsPolitician_of_degree_le_two` closes by a nested case split
  (`interval_cases d`, i.e. d ∈ {0,1,2}) that reuses the two named siblings
  `existsPolitician_of_degree_le_one` and `existsPolitician_of_degree_eq_two`.
- `false_of_three_le_degree` closes by a trace-mod-`p` contradiction:
  `contrapose!` on `ZMod.trace_pow_card`, then `lia`, using the siblings
  `card_mod_p_of_regular` and `adjMatrix_pow_mod_p_of_regular`.

So the glue is a pure skeleton: one lemma supplies the degree, one splits, and
the two remaining lemmas each close a branch by themselves.

## Why it is good

1. The parent `friendship_theorem` closes from the three named child lemmas in
   six lines of glue (lines 330-335): `isRegularOf_not_existsPolitician`
   supplies the degree, `lt_or_ge d 3` splits, and each branch is closed by one
   `exact` applying a child lemma. *(check)*
2. The two goals produced by `rcases lt_or_ge d 3` are `d < 3` and `3 ≤ d`; the
   first closes with `exact npG (hG.existsPolitician_of_degree_le_two dreg
   (Nat.lt_succ_iff.mp dle2))` (line 334) and the second with `exact
   hG.false_of_three_le_degree dreg dge3` (line 335). *(check)*
3. The theorem's docstring states the plan the proof realises: "If the degree
   is at most 2, we observe by casework that it has a politician anyway. If the
   degree is at least 3, the graph cannot exist." (lines 328-329), matching the
   module outline "By casework, show that if d = 0, 1, 2, then G has a
   politician. If 3 ≤ d, let p be a prime factor of d - 1." (lines 29-30).
   *(author-statement)*
4. The longest chain of project lemmas below `friendship_theorem` is six deep:
   `friendship_theorem` → `existsPolitician_of_degree_le_two` →
   `existsPolitician_of_degree_eq_two` → `neighborFinset_eq_of_degree_eq_two` →
   `card_of_regular` → `adjMatrix_sq_of_regular` → `adjMatrix_sq_of_ne` (a
   leaf). *(measurement)*

In my opinion the detail worth copying is the shape of the glue: the split is
exhaustive for free (a library `lt_or_ge`), and each branch is a *named lemma*
rather than an inline tactic block, so the two very different sub-arguments
(linear-algebra over `ZMod p` on one side, small-graph combinatorics on the
other) stay out of the main proof.

## When to use it, and when not

Use it when the goal depends on a natural-number parameter `d` that you can
first extract from the hypotheses, and there is a genuine threshold: one side
closes by a constructive existence lemma, the other by deriving a
contradiction, so the branches are independent sub-arguments. The
exhaustiveness of the split should already be a library fact (`lt_or_ge`,
`le_or_lt`, `interval_cases`) so the glue stays short.

Avoid it when the threshold is not a real cut between a constructive and an
impossible case (one branch may be vacuous), when the branches share
substantial proof (a single lemma is then cleaner), or when the two sides need
`d` in different forms (here the small side needs `d ≤ 2`, not `d < 3`, which
costs a `Nat.lt_succ_iff.mp` rewrite).

## Consequences

The move creates two goals plus an exhaustiveness obligation, discharged here
by the library lemma `lt_or_ge d 3`. The witness `d` must be obtained before
the split (`isRegularOf_not_existsPolitician`), so the glue depends on that
lemma's signature; if it changed to return a different regular-degree witness,
the split would need to follow. The `d < 3` branch is re-encoded to `d ≤ 2` via
`Nat.lt_succ_iff.mp` before invoking its lemma — a coercion the author supplies
by hand; stating the threshold as `≤` on both sides would remove it. Failure
mode: if the two branches are not genuinely independent, one of the two branch
lemmas will drag the other's assumptions in and the clean skeleton collapses.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml (delegates to build_template.yml, whose 'build archive, counterexamples and wanted' step runs lake-build-with-retry.sh Archive and 'check that Archive built' runs lake build --no-build --wfail Archive); commit e1545ebed97594477bbd88b2fe948ffce56e5af2 on default branch master | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at e1545ebed97594477bbd88b2fe948ffce56e5af2 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Opened code/Archive/Wiedijk100Theorems/FriendshipGraphs.lean lines 330-335: six lines; L332 rcases hG.isRegularOf_not_existsPolitician npG supplies degree d, L333 rcases lt_or_ge d 3 splits, L334 and L335 each close one branch by a single exact applying a child lemma | verifier |
| 2 | verified | Opened code lines 333-335: L333 rcases lt_or_ge d 3 with dle2 | dge3 (goals d < 3 and 3 <= d); L334 exact npG (hG.existsPolitician_of_degree_le_two dreg (Nat.lt_succ_iff.mp dle2)); L335 exact hG.false_of_three_le_degree dreg dge3 | verifier |
| 3 | verified | Opened code lines 328-329 (docstring: 'If the degree is at most 2, we observe by casework that it has a politician anyway. If the degree is at least 3, the graph cannot exist.') and lines 29-30 (module outline: 'By casework, show that if d = 0, 1, 2, then G has a politician. If 3 <= d, let p be a prime factor of d - 1.'); both quoted sentences present verbatim | verifier |
| 4 | verified | Traced calls in code: friendship_theorem L330 -> existsPolitician_of_degree_le_two L315 (calls existsPolitician_of_degree_eq_two at L319) -> existsPolitician_of_degree_eq_two L306 (calls neighborFinset_eq_of_degree_eq_two at L310) -> neighborFinset_eq_of_degree_eq_two L289 (calls card_of_regular at L298) -> card_of_regular L185 (calls adjMatrix_sq_of_regular at L188) -> adjMatrix_sq_of_regular L127 (calls adjMatrix_sq_of_ne at L131) -> adjMatrix_sq_of_ne L82 leaf. 6 edges, all line numbers match; checked alternative branches (isRegularOf..., false_of_three_le_degree -> card_mod_p/adjMatrix_pow_mod_p) are shorter | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Verified against the copied code/Archive/Wiedijk100Theorems/FriendshipGraphs.lean. Parent friendship_theorem (L330-335) is 6 glue lines: by_contra npG, rcases hG.isRegularOf_not_existsPolitician npG, rcases lt_or_ge d 3, and one exact per branch (L334, L335); each branch closes. The three children are exactly the lemmas the glue calls: isRegularOf_not_existsPolitician (L149-175, 27 lines), false_of_three_le_degree (L248-273, 26 lines, closed by contrapose! on ZMod.trace_pow_card then trace_adjMatrix vs adjMatrix_pow_mod_p_of_regular, lia at L273), existsPolitician_of_degree_le_two (L315-319, 5 lines, interval_cases d; iterate 2 apply existsPolitician_of_degree_le_one; exact existsPolitician_of_degree_eq_two). Child statements and closed_by match the code verbatim. Shape numbers correct: direct_lemmas=3, glue_lines=6, child_lines=[27,26,5]. Depth=6 confirmed by following the longest chain friendship_theorem->existsPolitician_of_degree_le_two(L319)->existsPolitician_of_degree_eq_two(L310)->neighborFinset_eq_of_degree_eq_two(L298)->card_of_regular(L188)->adjMatrix_sq_of_regular(L131)->adjMatrix_sq_of_ne(L82 leaf); no longer chain exists. Claims 1-4 all match the code and line numbers. | reviewer-correctness |
| generality | accept | Move is stated to generalise: 'extract a natural-number parameter d from an assumption, then threshold-split it via a library fact (lt_or_ge d 3), closing each branch with one named lemma' (applicability.goal_shape/use_when). 'When not to use' and Consequences are honest and specific against the copied code: the d<3 to d<=2 re-encoding costs Nat.lt_succ_iff.mp (line 334); exhaustiveness is a free library fact lt_or_ge; d must be obtained before the split via isRegularOf_not_existsPolitician; failure mode when branches drag shared assumptions is named. 'Why each direct child is a good leaf' states the bounded-prover-relevant property: self-contained statement + independent closure (each closes by one named lemma or a deterministic interval_cases). Non-blocking notes: entry.json avoid_when's third item (exhaustiveness not a library fact) and README's third 'avoid' bullet (sides need d in different forms) differ, and known_uses points at the entry's own site (L315-L319) rather than an independent use. | reviewer-generality |
| provenance-licence | accept | check_provenance passes: 1 file byte-identical at pinned commit e1545ebed97594477bbd88b2fe948ffce56e5af2; copied file sha256 27ed2662... matches entry.json; all file/site permalinks use the same pinned commit; licence Apache-2.0 matches upstream LICENSE (Apache License 2.0, copied as sources/mathlib4/upstream-LICENSE) and source.json/SOURCE.md; site line ranges (149-175, 248-273, 315-319, 330-335, 28-32) verified against the local copy | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover-community/mathlib4 at commit `e1545ebed97594477bbd88b2fe948ffce56e5af2`, under `Apache-2.0`; see the [source note](../../sources/mathlib4/SOURCE.md) for the licence text and attribution.
