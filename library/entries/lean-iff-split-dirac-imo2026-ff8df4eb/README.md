# Iff-split for IMO 2026 Q4: MulanCanGuarantee θ iff θ = 180/n

| | |
|---|---|
| Kind | instance |
| Move | iff-split |
| Language | lean |
| Status | draft |
| Source | [dirac-imo2026](../../sources/dirac-imo2026/SOURCE.md) at `372592370162` |
| Licence | `MIT` |

## Intent

The headline iff of IMO 2026 Q4, `MulanCanGuarantee θ ↔ ∃ n : ℕ, 2 ≤ n ∧ θ = 180 / n`,
is proved by splitting it into its two directions with `constructor`, and each
direction is discharged by one project lemma stated and proved independently
above it: the forward direction (⇒) by `exists_div_of_canGuarantee`, the
backward direction (⇐) by `mulanCanGuarantee_of_div`.

## The decomposition

### parent `main_theorem`: [`IMO2026/Q4/solution.lean` lines 376-384](https://github.com/Boundless-Intuition/IMO2026/blob/37259237016275044e3905e8d537efd0eead74d2/IMO2026/Q4/solution.lean#L376-L384) ([local copy](code/IMO2026/Q4/solution.lean))

```lean
/-- **Main theorem.** For `0 < θ < 180`, Mulan can guarantee her victory in finitely
many steps, no matter how Shan-Yu plays, if and only if `θ = 180 / n` for some
integer `n ≥ 2`. -/
theorem main_theorem (θ : ℝ) (hθ0 : 0 < θ) (hθ180 : θ < 180) :
    MulanCanGuarantee θ ↔ ∃ n : ℕ, 2 ≤ n ∧ θ = 180 / n := by
  constructor
  · exact exists_div_of_canGuarantee hθ0 hθ180
  · rintro ⟨n, hn, hθ⟩
    exact mulanCanGuarantee_of_div hn hθ
```

### child `exists_div_of_canGuarantee`: [`IMO2026/Q4/solution.lean` lines 363-370](https://github.com/Boundless-Intuition/IMO2026/blob/37259237016275044e3905e8d537efd0eead74d2/IMO2026/Q4/solution.lean#L363-L370) ([local copy](code/IMO2026/Q4/solution.lean))

```lean
lemma exists_div_of_canGuarantee {θ : ℝ} (hθ0 : 0 < θ) (hθ180 : θ < 180)
    (h : MulanCanGuarantee θ) : ∃ n : ℕ, 2 ≤ n ∧ θ = 180 / n := by
  rw [div_iff_intMul hθ0 hθ180]
  by_contra hc
  push_neg at hc
  have htri : IsTriangle ({60, 60, 60} : Multiset ℝ) := by
    refine isTriangle_triple ?_ ?_ ?_ ?_ <;> norm_num
  exact not_good_of_mulanWins hc (h _ htri) (good_equilateral hc)
```

### child `mulanCanGuarantee_of_div`: [`IMO2026/Q4/solution.lean` lines 271-279](https://github.com/Boundless-Intuition/IMO2026/blob/37259237016275044e3905e8d537efd0eead74d2/IMO2026/Q4/solution.lean#L271-L279) ([local copy](code/IMO2026/Q4/solution.lean))

```lean
lemma mulanCanGuarantee_of_div {n : ℕ} (hn : 2 ≤ n) {θ : ℝ} (hθdef : θ = 180 / n) :
    MulanCanGuarantee θ := by
  intro s hs
  by_cases h : θ ∈ s
  · exact MulanWins.win h
  · obtain ⟨L, R, hcut, hL, hR, ⟨i, hi⟩, ⟨j, hj⟩⟩ := exists_opening_cut hn hθdef hs h
    exact MulanWins.move hcut
      (mulanWins_of_succ_mul (theta_pos hn hθdef) i L hL hi)
      (mulanWins_of_succ_mul (theta_pos hn hθdef) j R hR hj)
```

### context `MulanWins_MulanCanGuarantee`: [`IMO2026/Q4/solution.lean` lines 36-44](https://github.com/Boundless-Intuition/IMO2026/blob/37259237016275044e3905e8d537efd0eead74d2/IMO2026/Q4/solution.lean#L36-L44) ([local copy](code/IMO2026/Q4/solution.lean))

```lean
inductive MulanWins (θ : ℝ) : Multiset ℝ → Prop
  | win {s : Multiset ℝ} (h : HasAngle θ s) : MulanWins θ s
  | move {s L R : Multiset ℝ} (hcut : IsCut s L R)
      (hL : MulanWins θ L) (hR : MulanWins θ R) : MulanWins θ s

/-- Mulan can guarantee victory for the value `θ`: from every valid starting
triangle she wins in finitely many steps regardless of Shan-Yu's play. -/
def MulanCanGuarantee (θ : ℝ) : Prop :=
  ∀ s : Multiset ℝ, IsTriangle s → MulanWins θ s
```

How the parts fit. `main_theorem` is split by `constructor` into the two
directions of the `↔`. The first bullet (⇒, guarantee implies existence) is a
single `exact exists_div_of_canGuarantee hθ0 hθ180`; the second bullet (⇐,
existence implies guarantee) unpacks the witness with `rintro ⟨n, hn, hθ⟩` and
is a single `exact mulanCanGuarantee_of_div hn hθ`. So the parent's proof is
exactly the two lemmas plus the bookkeeping of unpacking the existential
witness — no tactic work happens in the parent itself.

The lemma graph (which project lemma uses which, below `main_theorem`):

```text
main_theorem
├── exists_div_of_canGuarantee            (⇒)
│     ├── div_iff_intMul                  (rewrites the goal to an integer-multiple form)
│     ├── not_good_of_mulanWins           (a MulanWins triangle is never Good)
│     │     └── good_of_cut               (one child of every cut is Good)
│     │           ├── isTriangle_triple → card_triple, mem_triple, sum_triple
│     │           └── mem_triple, sum_triple
│     └── good_equilateral                ({60,60,60} is Good)
│           └── isTriangle_triple → card_triple, mem_triple, sum_triple
└── mulanCanGuarantee_of_div              (⇐)
      ├── exists_opening_cut              (the opening cut whose children carry (k+1)·θ)
      │     ├── exists_repr_apex → exists_repr → mem_triple, sum_triple
      │     └── isTriangle_triple → card_triple, mem_triple, sum_triple
      └── mulanWins_of_succ_mul           (a triangle containing (k+1)·θ is a win)
            ├── exists_repr_apex → exists_repr
            └── isTriangle_triple → card_triple, mem_triple, sum_triple
```

Each direction is a good leaf because its statement is self-contained and its
proof closes on its own from named siblings, never from the other direction:

- `exists_div_of_canGuarantee` (lines 363-370) is closed by `not_good_of_mulanWins`
  and `good_equilateral`: rewriting the goal to `∃ k : ℤ, 180 = k * θ` via
  `div_iff_intMul`, then deriving a contradiction — the equilateral triangle
  `{60,60,60}` is both `Good` (no angle an integer multiple of θ) and, by the
  hypothesis `h`, a `MulanWins` triangle, which `not_good_of_mulanWins` forbids.
- `mulanCanGuarantee_of_div` (lines 271-279) is closed by `exists_opening_cut`
  and `mulanWins_of_succ_mul`: for any triangle `s`, either `θ ∈ s` (already a
  win) or the opening cut produces two children each containing an integer
  multiple of θ, and each such child is a win by `mulanWins_of_succ_mul`.

## Why it is good

1. The parent's entire proof is `constructor` plus one `exact` per direction
   (lines 381-384): the iff carries no proof burden of its own, only the split
   and the routing of each side to its lemma.
2. Measured: 4 lines of glue calling 2 direct lemmas; the two children's proofs
   are 6 and 7 lines; the longest chain of project lemmas below the main theorem
   is 5 (`main_theorem → exists_div_of_canGuarantee → not_good_of_mulanWins →
   good_of_cut → isTriangle_triple → card_triple`).
3. The authors mark the theorem with the comment "**Main theorem.** For
   `0 < θ < 180`, Mulan can guarantee her victory ... if and only if
   `θ = 180 / n`" (lines 376-378), and the formal statement matches it.
4. Each direction is a self-contained lemma that closes without mentioning the
   other direction: the forward direction by contradiction from the good
   equilateral triangle (lines 363-370), the backward direction by the
   constructive opening cut (lines 271-279).

This instance supports survey F §10 rule 7 (bidirectional splits): each
direction of the iff is a child, and the glue is exactly the split, with the
forward lemma receiving only the hypotheses it needs (`hθ0`, `hθ180`) and the
backward lemma only `hn`, `hθdef`.

In my opinion the detail worth copying is the assignment of hypotheses: the
split is also a *surgery* — the forward direction genuinely needs `0 < θ` and
`θ < 180` (to use `div_iff_intMul`), while the backward direction only needs
`2 ≤ n` and `θ = 180/n`, so splitting the iff lets each direction take exactly
the assumptions that make it true.

## When to use it, and when not

Use it when an iff (or an order antisymmetry, or a set equality) has two
directions with genuinely different arguments, each already stated as its own
lemma, so the glue is `constructor` plus one `exact` per side. Avoid it when the
two directions share most of their proof — fold them into one lemma, or use
`le_antisymm`/`ext` directly — or when a direction is not yet a lemma, in which
case `constructor` just exposes an open goal and the split itself does no work.

## Consequences

The split creates exactly two obligations, one per direction, both already
discharged by named lemmas: (⇒) a guarantee forces `θ = 180/n`, and (⇐)
`θ = 180/n` allows a guarantee. It also lets each direction take exactly the
hypotheses it needs (see above). Failure mode: `constructor` on an iff whose
sides are not lemmas merely produces two open goals, so this move is worth
recording only when the children already read on their own; otherwise the real
content is elsewhere and the split is just bookkeeping.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | not-run | no CI workflow at the pinned commit 37259237016275044e3905e8d537efd0eead74d2 (repository tree has no .github/workflows; list_files.py shows no .github directory) and no local Lean toolchain (protocol section 6), so the build was not run | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| glue-cites-children | pass | cited: exists_div_of_canGuarantee@IMO2026/Q4/solution.lean:382, mulanCanGuarantee_of_div@IMO2026/Q4/solution.lean:384; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 37259237016275044e3905e8d537efd0eead74d2 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | read code/IMO2026/Q4/solution.lean L381-384: constructor (L381) splits the iff; bullet 1 is a single exact of exists_div_of_canGuarantee (L382); bullet 2 is rintro ⟨n, hn, hθ⟩ then a single exact of mulanCanGuarantee_of_div (L383-384). Each bullet applies exactly one named project lemma via exact; the only extra tactic is the witness-unpacking rintro, so no substantive tactic work happens in the parent proof | verifier |
| 2 | refuted | glue counts correct: L381-384 = 4 lines calling exactly exists_div_of_canGuarantee and mulanCanGuarantee_of_div (2 direct lemmas); child proofs = 6 lines (L365-370) and 7 lines (L273-279). But longest chain is not 4: isTriangle_triple (L68-73) is not a leaf — it uses card_triple (L70), mem_triple (L72), sum_triple (L73), so main_theorem → exists_div_of_canGuarantee → not_good_of_mulanWins → good_of_cut → isTriangle_triple → card_triple has 5 project lemmas below main_theorem (depth 5), not 4 | verifier |
| 3 | verified | read code L376-378: doc comment labels it Main theorem and states the informal biconditional (0 < θ < 180, Mulan can guarantee victory iff θ = 180/n for some integer n ≥ 2), matching the formal statement L379-380 component-wise (0<θ<180 ↔ hθ0 hθ180; guarantee ↔ MulanCanGuarantee θ; iff ↔ iff; θ=180/n for n≥2 ↔ ∃ n, 2≤n ∧ θ=180/n) | verifier |
| 4 | verified | read L363-370: exists_div_of_canGuarantee closes by exact not_good_of_mulanWins hc (h _ htri) (good_equilateral hc) at L370, using not_good_of_mulanWins and good_equilateral, not the other direction. read L271-279: mulanCanGuarantee_of_div closes by obtain ... := exists_opening_cut (L276) and exact MulanWins.move ... mulanWins_of_succ_mul ... (L277-279), not the other direction. Both children close on their own from named siblings without referencing the opposite direction | verifier |
| 5 | verified | read code/IMO2026/Q4/solution.lean. Glue: L381-384 = 4 lines (constructor, exact exists_div_of_canGuarantee, rintro, exact mulanCanGuarantee_of_div) calling exactly the 2 direct lemmas exists_div_of_canGuarantee and mulanCanGuarantee_of_div. Child proof bodies: exists_div_of_canGuarantee L365-370 = 6 lines; mulanCanGuarantee_of_div L273-279 = 7 lines. Longest chain (depth 5) confirmed: main_theorem L382 -> exists_div_of_canGuarantee -> not_good_of_mulanWins (L370) -> good_of_cut (L352 rcases) -> isTriangle_triple (L307-310) -> card_triple (L70 refine) = 5 project lemmas below main_theorem. Other branch reaches depth 5 too (mulanCanGuarantee_of_div -> exists_opening_cut -> exists_repr_apex -> exists_repr -> mem_triple) and mulanWins_of_succ_mul branch depth 4, so no chain exceeds 5. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Read code/IMO2026/Q4/solution.lean directly. Parent main_theorem (L379-384) is exactly constructor then one exact per direction: exact exists_div_of_canGuarantee hθ0 hθ180 (L382) and rintro ⟨n,hn,hθ⟩ / exact mulanCanGuarantee_of_div hn hθ (L383-384); the rintro witness-unpacking is acknowledged in the intent and README, so the decomposition matches. Children are exactly the two lemmas the parent proof uses. Child closed_by matches code: exists_div_of_canGuarantee (L365-370) terminates in exact not_good_of_mulanWins hc (h _ htri) (good_equilateral hc); mulanCanGuarantee_of_div (L273-279) terminates in exact MulanWins.move hcut (mulanWins_of_succ_mul ...) (mulanWins_of_succ_mul ...) from exists_opening_cut. Shape numbers verified against the shape definition in fields.md: direct_lemmas=2, glue_lines=4 (L381-384), child_lines=[6,7] (L365-370 and L273-279), depth=5. Longest chain independently traced: main_theorem -> exists_div_of_canGuarantee -> not_good_of_mulanWins -> good_of_cut -> isTriangle_triple -> card_triple = 5 lemmas below main_theorem; backward branch mulanCanGuarantee_of_div -> exists_opening_cut -> exists_repr_apex -> exists_repr -> mem_triple also reaches 5, none exceeds 5, so depth=5 is correct (the earlier refuted depth-4 claim was fixed). Build is not-run for want of a toolchain, but the code is syntactically consistent and every named closing method exists and is applied as claimed. | reviewer-correctness |
| generality | accept | Move stated beyond the example: applicability.goal_shape generalises to any iff whose two directions are already separate forward/backward lemmas, and notes the same shape for order antisymmetry and set equality; use_when/avoid_when give general criteria. When-not-to-use is honest and specific (shared proofs -> fold into one lemma or use le_antisymm/ext; a direction not yet a lemma -> constructor just exposes an open goal). Consequences are honest: exactly two obligations, each named with its argument, a true hypothesis-surgery observation (forward needs h0/h180 for div_iff_intMul, backward only hn/hdef), and the failure mode stated. Good-leaf question answered in substance: README says each direction is a good leaf because its statement is self-contained and it closes on its own from named siblings never from the other direction, with measured 6/7-line proofs and depth-5 chain; the exact phrase 'bounded prover' is not used, but the properties a bounded prover needs (self-contained statement, short independent proof, shallow lemma chain) are all recorded. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are consistent and traceable. check_provenance.py passes: code/IMO2026/Q4/solution.lean is byte-identical at commit 37259237016275044e3905e8d537efd0eead74d2 and its recorded sha256 matches. Commit is identical across entry.json source.commit, source.json, SOURCE.md (pinned 2026-11-12T10:23:52Z) and README (372592370162 = first 12 chars). Licence MIT is consistent in entry.json, source.json, SOURCE.md and README; upstream-LICENSE is the MIT text (Copyright 2026 Boundless Intuition) and is byte-identical to the fetched upstream LICENSE at the pinned commit. All 4 site permalinks and the file permalink use the pinned commit and correct path IMO2026/Q4/solution.lean with line anchors matching the README excerpts. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/Boundless-Intuition/IMO2026 at commit `37259237016275044e3905e8d537efd0eead74d2`, under `MIT`; see the [source note](../../sources/dirac-imo2026/SOURCE.md) for the licence text and attribution.
