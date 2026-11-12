# API lemma expressing s(N) as N/d₁ + N/d₂ + N/d₃ (IMO 2025 P4)

| | |
|---|---|
| Kind | instance |
| Move | interface-lemma |
| Language | lean |
| Status | accepted |
| Source | [harmonic-imo2025](../../sources/harmonic-imo2025/SOURCE.md) at `72b62405a176` |
| Licence | `LicenseRef-unknown` |

## Intent

Establish an interface for `s N` — the sum of the three largest proper
divisors, defined by indexing into the descending sort of
`N.properDivisors` — by rewriting it as `N / d₁ + N / d₂ + N / d₃`, where
`d₁ < d₂ < d₃` are the three smallest divisors of `N` greater than 1. Later
lemmas reason about `s` through this arithmetic form instead of unfolding
the sort.

## The decomposition

### parent `lem_s_N_smallest_divisors`: [`HarmonicLean/IMO2025P4_solve2.lean` lines 74-110](https://github.com/harmonic-ai/IMO2025/blob/72b62405a176a7eaeadb335a7fa6ee80b6667161/HarmonicLean/IMO2025P4_solve2.lean#L74-L110) ([local copy](code/HarmonicLean/IMO2025P4_solve2.lean))

```lean
lemma lem_s_N_smallest_divisors (N : ℕ) (h_card : 3 ≤ N.properDivisors.card) :
  let d₁ := ((N.divisors.erase 1).sort (· ≤ ·))[0]!
  let d₂ := ((N.divisors.erase 1).sort (· ≤ ·))[1]!
  let d₃ := ((N.divisors.erase 1).sort (· ≤ ·))[2]!
  s N = N / d₁ + N / d₂ + N / d₃ := by
    -- The three largest proper divisors of $N$ are $N/d_1$, $N/d_2$, and $N/d_3$, where $d_1$, $d_2$, and $d_3$ are the three smallest divisors of $N$ greater than 1.
    have h_largest : (N.properDivisors.sort (· ≥ ·))[0]! = N / ((N.divisors.erase 1).sort (· ≤ ·))[0]! ∧
                     (N.properDivisors.sort (· ≥ ·))[1]! = N / ((N.divisors.erase 1).sort (· ≤ ·))[1]! ∧
                     (N.properDivisors.sort (· ≥ ·))[2]! = N / ((N.divisors.erase 1).sort (· ≤ ·))[2]! := by
                       have h_largest : (N.properDivisors.sort (· ≥ ·)) = List.map (fun d => N / d) ((N.divisors.erase 1).sort (· ≤ ·)) := by
                         have h_largest : List.Sorted (· ≥ ·) (List.map (fun d => N / d) ((N.divisors.erase 1).sort (· ≤ ·))) ∧ List.Nodup (List.map (fun d => N / d) ((N.divisors.erase 1).sort (· ≤ ·))) := by
                           aesop;
                           · -- Since the original list of divisors is sorted in ascending order, applying N/d to each element will reverse the order, resulting in a list sorted in descending order.
                             have h_sorted : ∀ {l : List ℕ}, (∀ d ∈ l, d ∣ N) → List.Sorted (· ≤ ·) l → List.Sorted (· ≥ ·) (List.map (fun d => N / d) l) := by
                               intros l hl_div hl_sorted; induction hl_sorted <;> aesop;
                               exact Nat.div_le_div_left ( a_1 _ a_4 ) ( Nat.pos_of_dvd_of_pos left ( Nat.pos_of_ne_zero ( by aesop_cat ) ) );
                             exact h_sorted ( fun d hd => Nat.dvd_of_mem_divisors <| Finset.mem_of_mem_erase <| Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 hd ) <| Finset.sort_sorted _ _;
                           · rw [ List.nodup_map_iff_inj_on ];
                             · aesop;
                               exact?;
                             · exact Finset.sort_nodup _ _;
                         -- To prove the equality of the two lists, we can show that they are permutations of each other and that they are both sorted in the required order.
                         have h_perm : List.Perm (List.map (fun d => N / d) ((N.divisors.erase 1).sort (· ≤ ·))) (Finset.sort (· ≥ ·) N.properDivisors) := by
                           -- Since every proper divisor of $N$ can be written as $N/d$ for some divisor $d$ of $N$, the list of $N/d$ for each $d$ in the sorted list of divisors (excluding 1) is exactly the list of proper divisors.
                           have h_perm : List.toFinset (List.map (fun d => N / d) ((N.divisors.erase 1).sort (· ≤ ·))) = N.properDivisors := by
                             ext; aesop;
                             · -- Since $w \mid N$, we have $N / w \mid N$ by definition of division.
                               apply Nat.div_dvd_of_dvd left_2;
                             · exact Nat.div_lt_self ( Nat.pos_of_ne_zero right_2 ) ( lt_of_le_of_ne ( Nat.pos_of_dvd_of_pos left_2 ( Nat.pos_of_ne_zero right_2 ) ) ( Ne.symm left_1 ) );
                             · exact ⟨ N / a, ⟨ by nlinarith [ Nat.div_mul_cancel left_1 ], Nat.div_dvd_of_dvd left_1, by linarith ⟩, by rw [ Nat.div_div_self ] <;> aesop ⟩;
                           rw [ List.perm_iff_count ];
                           intro a; replace h_perm := Finset.ext_iff.mp h_perm a; aesop;
                           by_cases ha : a ∈ List.map ( fun d => N / d ) ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( N.divisors.erase 1 ) ) <;> aesop;
                           rw [ List.count_eq_zero_of_not_mem, List.count_eq_zero_of_not_mem ] <;> aesop;
                         rw [ List.eq_of_perm_of_sorted h_perm h_largest.1 ( Finset.sort_sorted _ _ ) ];
                       rcases n : Finset.sort ( · ≤ · ) ( Nat.divisors N |> Finset.erase <| 1 ) with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | n ⟩ ⟩ ⟩ <;> aesop;
    unfold s; aesop;
```

### context `def_s`: [`HarmonicLean/IMO2025P4_solve2.lean` lines 43-48](https://github.com/harmonic-ai/IMO2025/blob/72b62405a176a7eaeadb335a7fa6ee80b6667161/HarmonicLean/IMO2025P4_solve2.lean#L43-L48) ([local copy](code/HarmonicLean/IMO2025P4_solve2.lean))

```lean
def s (N : ℕ) : ℕ :=
  if h : 3 ≤ N.properDivisors.card then
    ((N.properDivisors.sort (· ≥ ·))[0]! +
     (N.properDivisors.sort (· ≥ ·))[1]! +
     (N.properDivisors.sort (· ≥ ·))[2]!)
  else 0
```

### context `lem_s_N_formula`: [`HarmonicLean/IMO2025P4_solve2.lean` lines 163-193](https://github.com/harmonic-ai/IMO2025/blob/72b62405a176a7eaeadb335a7fa6ee80b6667161/HarmonicLean/IMO2025P4_solve2.lean#L163-L193) ([local copy](code/HarmonicLean/IMO2025P4_solve2.lean))

```lean
lemma lem_s_N_formula (N : ℕ) (h_card : 3 ≤ N.properDivisors.card) :
  let d₁ := ((N.divisors.erase 1).sort (· ≤ ·))[0]!
  let d₂ := ((N.divisors.erase 1).sort (· ≤ ·))[1]!
  let d₃ := ((N.divisors.erase 1).sort (· ≤ ·))[2]!
  (s N : ℚ) = (N : ℚ) * (1 / (d₁ : ℚ) + 1 / (d₂ : ℚ) + 1 / (d₃ : ℚ)) := by
    -- Apply the lemma lem_s_N_smallest_divisors to express s(N) in terms of the reciprocals of the smallest divisors.
    have h_s_N : s N = N / ((N.divisors.erase 1).sort (· ≤ ·))[0]! + N / ((N.divisors.erase 1).sort (· ≤ ·))[1]! + N / ((N.divisors.erase 1).sort (· ≤ ·))[2]! := by
      -- Apply the lemma lem_s_N_smallest_divisors to conclude the proof.
      apply lem_s_N_smallest_divisors;
      assumption;
    rcases n : ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( N.divisors.erase 1 ) ) with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | n ⟩ ⟩ ⟩ <;> aesop;
    · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n a; aesop;
    · rw [ Nat.cast_div ( Nat.dvd_of_mem_divisors <| Finset.mem_of_mem_erase <| Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 <| by rw [ n ] ; simp ( config := { decide := Bool.true } ) ), Nat.cast_div ( Nat.dvd_of_mem_divisors <| Finset.mem_of_mem_erase <| Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 <| by rw [ n ] ; simp ( config := { decide := Bool.true } ) ) ];
      · ring;
      · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n b; aesop;
      · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 0; aesop;
    · have hn : a ∣ N ∧ b ∣ N ∧ c ∣ N := by
        replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; aesop;
        · specialize n a; aesop;
        · grind;
        · specialize n c; aesop;
      rw [ Nat.cast_div ( by tauto ), Nat.cast_div ( by tauto ), Nat.cast_div ( by tauto ) ] <;> ring <;> aesop;
    · -- By definition of $d₁$, $d₂$, and $d₃$, we know that $d₁$, $d₂$, and $d₃$ are the three smallest divisors of $N$ greater than 1.
      have h_divisors : d₁ ∣ N ∧ d₂ ∣ N ∧ d₃ ∣ N := by
        replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; aesop;
        · specialize n a; aesop;
        · -- By definition of $n$, we know that $b$ divides $N$.
          specialize n b; aesop;
        · specialize n c; aesop;
      rw [ Nat.cast_div, Nat.cast_div, Nat.cast_div ] <;> aesop;
      ring
```

How the parts fit. `lem_s_N_smallest_divisors` wraps the definition `s`
(lines 43-48) so that clients never unfold the sort. Its proof splits into
one key invariant and a final closure.

The key invariant `h_largest` (lines 80-109) says the three largest entries
of the descending sort of `N.properDivisors` equal `N / d₁`, `N / d₂`,
`N / d₃` — i.e. the map `d ↦ N / d` sends the three *smallest* divisors
greater than 1 to the three *largest* proper divisors. It is proved in three
steps: (a) `List.Sorted` and `List.Nodup` of the mapped list (lines 84-94),
using a small induction that `N / d` reverses the order `≤` into `≥`
(line 87); (b) `List.Perm` of the mapped list and the descending sort, by
showing their `toFinset` coincide (lines 96-107); (c)
`List.eq_of_perm_of_sorted` to get the list equality (line 108), then
`rcases` on the sorted divisor list to read off the three index equalities
(line 109).

The remaining goal is then just `unfold s; aesop` (line 110): unfolding `s`
turns it into the sum of the three entries that `h_largest` has already
identified, and `aesop` assembles the three equalities into the target
`N / d₁ + N / d₂ + N / d₃`.

The context excerpt `lem_s_N_formula` (lines 163-193) shows the interface at
work: at line 171 it applies `lem_s_N_smallest_divisors` (with the same
`h_card`) to lift the natural-number formula to the rational reciprocal
formula `(N : ℚ) * (1/d₁ + 1/d₂ + 1/d₃)`, again without unfolding `s`.

## Why it is good

1. The parent closes from two children: `h_largest` (lines 80-109) proves the
   three largest proper divisors are `N/d₁, N/d₂, N/d₃`, then
   `unfold s; aesop` (line 110) discharges the goal (`check`, lines 74-110).
2. The interface is reused at seven sites without re-unfolding the sort:
   directly at lines 171 and 590, and via `lem_s_N_formula` at lines 300, 331,
   368, 551, 627 (`measurement`, grep of the copied file).
3. The authors state the purpose in the doc comment above the lemma: "If
   1 < d₁ < d₂ < d₃ < … are the positive divisors of N greater than 1 in
   increasing order, then the three largest proper divisors of N are N/d₁,
   N/d₂, and N/d₃." (`author-statement`, lines 71-73).
4. The same pattern recurs one level up: `lem_s_N_formula` (lines 163-193) is
   a second API lemma that rewrites `s N` as the rational reciprocal formula
   and consumes `lem_s_N_smallest_divisors` at line 171 (`known-use`,
   lines 163-193).

In my opinion the interesting detail is that the abstraction is *bidirectional*:
the descending sort of proper divisors and the ascending sort of divisors
greater than 1 are the same list up to the reciprocal map `d ↦ N / d`, and
the interface lemma pins down exactly that correspondence once, so the seven
client sites only ever manipulate `N / dᵢ`.

## When to use it, and when not

Use it when a definition is a sort- or indexing-based computation that many
later lemmas would otherwise each unfold, and there is a cleaner equivalent
form over a companion list that the actual arguments use. The interface lemma
should carry the definition's side condition (`3 ≤ N.properDivisors.card`
here) explicitly so clients know what they must provide.

Avoid it when the definition is used once, when the sort-based form itself is
what the proof needs (for example, to reason directly about the ordering of
the proper divisors), or when the side condition is awkward for clients to
discharge and the abstraction would force every use to re-prove it.

## Consequences

The move creates an obligation for every client: to apply the interface lemma
it must discharge `h_card : 3 ≤ N.properDivisors.card` (cheap here, since the
client lemmas already assume it). It changes the representation of `s N` from
a sort-based term to an arithmetic sum, so a client that needs the
descending-sort form itself must unfold `s` or use a different lemma. It also
adds a dependency on the companion list `N.divisors.erase 1` sorted ascending.
The proof of the interface is the bulk of the work (the `h_largest`
sub-argument, lines 80-109), so the move pays off only when the interface is
reused; a single-use abstraction would be net-negative.

Survey F §10 has no rule that names the interface-lemma move (its candidate
rules cover splitting, induction, witnesses, calculational chains, memoising
and repair, but not "state an API lemma at an abstraction boundary"), so this
entry maps to no rule rather than forcing a fit.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/lean_action_ci.yml (leanprover/lean-action@v1 runs lake build on the whole HarmonicLean package, which includes HarmonicLean/IMO2025P4_solve2.lean); pinned commit 72b62405a176a7eaeadb335a7fa6ee80b6667161 is HEAD of default branch main | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 72b62405a176a7eaeadb335a7fa6ee80b6667161 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Copied file lines 80-109 contain 'have h_largest : ...' establishing the three largest proper divisors equal N/d1,N/d2,N/d3 (with the List.eq_of_perm_of_sorted and rcases n : Finset.sort proof at 84-109), and line 110 is 'unfold s; aesop;' closing the goal. Matches the claim. | verifier |
| 2 | verified | Grep of copied file: lem_s_N_smallest_divisors used in proof code at 171 (apply) and 590 (convert ... using 1); lem_s_N_formula used at 300, 331, 368, 551, 627 (all rw/have, no unfold of s). That is 2 direct + 5 via formula = 7 reuse sites, matching the claim. | verifier |
| 3 | verified | Copied file lines 71-73 doc comment reads: "If 1 < d_1 < d_2 < d_3 < ... are the positive divisors of N greater than 1 in increasing order, then the three largest proper divisors of N are N/d_1, N/d_2, and N/d_3." Matches the quoted author statement. | verifier |
| 4 | verified | Copied file lines 163-193: lem_s_N_formula states (s N : ℚ) = (N : ℚ) * (1/(d₁:ℚ) + 1/(d₂:ℚ) + 1/(d₃:ℚ)), and line 171 'apply lem_s_N_smallest_divisors' consumes the interface lemma rather than unfolding s. Matches. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Correctness holds. Provenance passes (1 file byte-identical at 72b62405a176). Copied code lines 74-110 show lem_s_N_smallest_divisors decomposes exactly as the entry states: child h_largest (have at lines 80-82, proved 83-109 via Sorted/Nodup induction 84-94, Perm via toFinset 96-107, List.eq_of_perm_of_sorted 108, then rcases n : Finset.sort <;> aesop 109) establishes the three largest proper divisors equal N/d1,N/d2,N/d3; the main goal is then closed by 'unfold s; aesop' at line 110, which unfolds s to the guarded sum and rewrites via h_largest (d1,d2,d3 are let-bound to the sorted entries, so N/d_i is definitionally equal). This matches children[] statements and closing methods and closes the parent. Reuse sites verified by grep: lem_s_N_smallest_divisors at 171 (apply) and 590 (convert ... using 1); lem_s_N_formula at 300,331,368,551,627 = 2 direct + 5 via formula = 7. Parent line count 74-110 = 37 matches metrics. Move interface-lemma is a fair fit: an API lemma at the abstraction boundary of def s letting clients stop unfolding the sort. | reviewer-correctness |
| generality | accept | Generality holds. The move is stated beyond the example: README 'When to use it' generalises to 'a definition that is a sort- or indexing-based computation that many later lemmas would otherwise each unfold, with a cleaner equivalent form over a companion list that the actual arguments use', and to carrying the definition's side condition explicitly. 'When not to use' is honest and specific: used once; the sort-based form itself is what the proof needs; or the side condition is awkward for clients to discharge. Consequences are honest and specific: every client must discharge h_card (admitted cheap here), representation changes from sort-term to arithmetic sum, a dependency on N.divisors.erase 1 is added, and the move pays off only on reuse (single-use is net-negative). | reviewer-generality |
| provenance-licence | accept | Provenance already passes (1 file byte-identical at 72b62405a176; recorded by check_provenance.py). Commit is consistent everywhere: entry.json, source.json, SOURCE.md and every permalink all use 72b62405a176a7eaeadb335a7fa6ee80b6667161. Licence 'LicenseRef-unknown' is consistent across entry.json, source.json, SOURCE.md and README, and is accurate: the root listing at the pinned commit has no LICENSE/LICENCE/COPYING file, and README.md (190 B) and lakefile.toml declare no licence. All permalinks use the same commit + path HarmonicLean/IMO2025P4_solve2.lean, and their line anchors match the copied file (def_s 43-48, doc comment 71-73, parent 74-110, lem_s_N_formula 163-193, reuse sites 171/590/300/331/368/551/627). files[0].bytes=74500 matches the file listing and local copy. Source note (SOURCE.md) correctly records repo, pinned commit, 'no licence file found at the root' and attribution, and the copied file is byte-identical to upstream. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/harmonic-ai/IMO2025 at commit `72b62405a176a7eaeadb335a7fa6ee80b6667161`, under `LicenseRef-unknown`; see the [source note](../../sources/harmonic-imo2025/SOURCE.md) for the licence text and attribution.
