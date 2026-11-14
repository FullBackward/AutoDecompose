# Key invariant: the pair of longest increasing/decreasing sequence lengths for Erdős–Szekeres

| | |
|---|---|
| Kind | instance |
| Move | key-invariant |
| Language | lean |
| Status | accepted |
| Source | [mathlib4](../../sources/mathlib4/SOURCE.md) at `e1545ebed975` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T09:09:07Z |

## Intent

Prove the Erdős–Szekeres theorem — more than `r * s` distinct values force an increasing
sequence longer than `r` or a decreasing sequence longer than `s` — by labelling each
index `i` with the pair of longest increasing and decreasing sequence lengths ending at
`i`, proving that labelling injective, and pigeonholing more than `r * s` elements into
the `r × s` box of possible labels.

## The decomposition

### parent `erdos_szekeres`: [`Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean` lines 142-166](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean#L142-L166) ([local copy](code/Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean))

```lean
theorem erdos_szekeres {r s : ℕ} {f : α → β} (hn : r * s < Fintype.card α) (hf : Injective f) :
    (∃ t : Finset α, r < #t ∧ StrictMonoOn f t) ∨
      ∃ t : Finset α, s < #t ∧ StrictAntiOn f t := by
  classical
  -- It suffices to prove that there is some `i` where one of the max lengths is bigger than
  -- `r` or `s`, as this corresponds to a monotone sequence of the required length.
  rsuffices ⟨i, hi⟩ : ∃ i, r < maxIncSequencesTo f i ∨ s < maxDecSequencesTo f i
  · refine Or.imp ?_ ?_ hi
    on_goal 1 =>
      have : maxIncSequencesTo f i ∈ image card _ := maxIncSequencesTo_mem
    on_goal 2 =>
      have : maxDecSequencesTo f i ∈ image card _ := maxDecSequencesTo_mem
    all_goals
      intro hi
      obtain ⟨t, ht₁, ht₂⟩ := mem_image.1 this
      refine ⟨t, by rwa [ht₂], ?_⟩
      rw [mem_filter] at ht₁
      exact ht₁.2.2
  -- If such an `i` does not exist, then our pairs of labels lie in a small set, which is a
  -- contradiction since the pairs are unique.
  by_contra! q
  have : Set.MapsTo (paired f) (univ : Finset α) (Icc 1 r ×ˢ Icc 1 s : Finset _) := by
    simp [paired, one_le_maxIncSequencesTo, one_le_maxDecSequencesTo, Set.MapsTo, *]
  refine hn.not_ge ?_
  simpa using card_le_card_of_injOn (paired f) this (paired_injective hf).injOn
```

### child `maxIncSequencesTo_mem`: [`Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean` lines 71-72](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean#L71-L72) ([local copy](code/Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean))

```lean
private lemma maxIncSequencesTo_mem : maxIncSequencesTo f i ∈ incSequencesTo f i :=
  max'_mem _ incSequencesTo_nonempty
```

### child `maxDecSequencesTo_mem`: [`Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean` lines 73-74](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean#L73-L74) ([local copy](code/Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean))

```lean
private lemma maxDecSequencesTo_mem : maxDecSequencesTo f i ∈ decSequencesTo f i :=
  max'_mem _ decSequencesTo_nonempty
```

### child `paired_injective`: [`Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean` lines 125-130](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean#L125-L130) ([local copy](code/Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean))

```lean
private lemma paired_injective (hf : Injective f) : Injective (paired f) := by
  apply Injective.of_lt_imp_ne
  intro i j hij q
  cases lt_or_gt_of_ne (hf.ne hij.ne)
  case inl h => exact (maxIncSequencesTo_lt hij h).ne congr($q.1)
  case inr h => exact (maxDecSequencesTo_gt hij h).ne congr($q.2)
```

### child `one_le_maxIncSequencesTo`: [`Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean` lines 66-67](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean#L66-L67) ([local copy](code/Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean))

```lean
private lemma one_le_maxIncSequencesTo : 1 ≤ maxIncSequencesTo f i :=
  le_max' _ _ one_mem_incSequencesTo
```

### child `one_le_maxDecSequencesTo`: [`Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean` lines 68-69](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean#L68-L69) ([local copy](code/Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean))

```lean
private lemma one_le_maxDecSequencesTo : 1 ≤ maxDecSequencesTo f i :=
  le_max' _ _ one_mem_decSequencesTo
```

### context `maxIncSequencesTo_lt`: [`Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean` lines 84-108](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean#L84-L108) ([local copy](code/Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean))

```lean
private lemma maxIncSequencesTo_lt {i j : α} (hij : i < j) (hfij : f i < f j) :
    maxIncSequencesTo f i < maxIncSequencesTo f j := by
  rw [Nat.lt_iff_add_one_le]
  refine le_max' _ _ ?_
  have : maxIncSequencesTo f i ∈ incSequencesTo f i := max'_mem _ incSequencesTo_nonempty
  simp only [incSequencesTo, mem_image, mem_filter, mem_univ, true_and, and_assoc] at this
  obtain ⟨t, hti, ht₁, ht₂⟩ := this
  simp only [incSequencesTo, mem_image, mem_filter, mem_univ, true_and, and_assoc]
  have : ∀ x ∈ t, x < j := by
    intro x hx
    exact (hti.2 hx).trans_lt hij
  refine ⟨insert j t, ?_, ?_, ?_⟩
  next =>
    convert hti.insert j
    next => simp
    next => rw [max_eq_left hij.le]
  next =>
    simp only [coe_insert]
    rw [strictMonoOn_insert_iff_of_forall_le]
    · refine ⟨?_, ht₁⟩
      intro x hx hxj
      exact (ht₁.monotoneOn hx hti.1 (hti.2 hx)).trans_lt hfij
    · exact fun x hx ↦ (this x hx).le
  have : j ∉ t := fun hj ↦ lt_irrefl _ (this _ hj)
  simp [this, ht₂]
```

### context `maxDecSequencesTo_gt`: [`Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean` lines 110-112](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean#L110-L112) ([local copy](code/Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean))

```lean
private lemma maxDecSequencesTo_gt {i j : α} (hij : i < j) (hfij : f j < f i) :
    maxDecSequencesTo f i < maxDecSequencesTo f j :=
  maxIncSequencesTo_lt (β := βᵒᵈ) hij hfij
```

### context `paired`: [`Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean` lines 118-119](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean#L118-L119) ([local copy](code/Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean))

```lean
private noncomputable def paired (f : α → β) (i : α) : ℕ × ℕ :=
  (maxIncSequencesTo f i, maxDecSequencesTo f i)
```

How the parts fit. The invariant is `paired f i = (maxIncSequencesTo f i,
maxDecSequencesTo f i)` (context site `paired`): each index is labelled by the pair of
maximum increasing and decreasing sequence lengths ending there. The main theorem
`erdos_szekeres` (parent) is assembled from five named lemmas, all stated above it in the
same file, in two branches of glue:

- *From a big label to a long sequence* (lines 148-159). `rsuffices` replaces the goal
  by `∃ i, r < maxIncSequencesTo f i ∨ s < maxDecSequencesTo f i`. Each disjunct is then
  turned back into a real monotone sequence by `maxIncSequencesTo_mem` /
  `maxDecSequencesTo_mem`, which say the maximum length is attained, so `r < max` yields a
  sequence of length longer than `r`.
- *Pigeonhole* (lines 162-166). Assuming no such `i` (`by_contra!`), every pair
  `paired f i` lies in the box `Icc 1 r ×ˢ Icc 1 s`: the `1 ≤` lower bounds come from
  `one_le_maxIncSequencesTo` / `one_le_maxDecSequencesTo`, and `paired_injective` makes
  `paired f` injective, so `card_le_card_of_injOn` gives `Fintype.card α ≤ r * s`,
  contradicting `hn : r * s < Fintype.card α`.

Lemma graph (who uses whom):

    erdos_szekeres
     ├─ maxIncSequencesTo_mem     (closed by `max'_mem _ incSequencesTo_nonempty`)
     ├─ maxDecSequencesTo_mem     (closed by `max'_mem _ decSequencesTo_nonempty`)
     ├─ one_le_maxIncSequencesTo  (closed by `le_max' _ _ one_mem_incSequencesTo`)
     ├─ one_le_maxDecSequencesTo  (closed by `le_max' _ _ one_mem_decSequencesTo`)
     └─ paired_injective
         ├─ maxIncSequencesTo_lt  (context site, lines 84-108)
         └─ maxDecSequencesTo_gt  (context site, lines 110-112)
             └─ maxIncSequencesTo_lt  (order duality, `βᵒᵈ`)

Why each lemma is a good leaf:

- `maxIncSequencesTo_mem` / `maxDecSequencesTo_mem` are one-liners
  (`max'_mem _ ..._nonempty`) whose proof closes as soon as the matching
  `incSequencesTo_nonempty` / `decSequencesTo_nonempty` (the singleton `{i}`) is given.
- `one_le_maxIncSequencesTo` / `one_le_maxDecSequencesTo` are one-liners
  (`le_max' _ _ one_mem_...`) closing on the same singleton facts.
- `paired_injective` is the key leaf: its proof closes on two named siblings
  (`maxIncSequencesTo_lt`, `maxDecSequencesTo_gt`) through a two-way case split on
  `i < j ∨ j < i`, and each sibling is itself proved (`maxDecSequencesTo_gt` by order
  duality from `maxIncSequencesTo_lt`). The longest chain below the theorem is therefore
  `erdos_szekeres → paired_injective → maxDecSequencesTo_gt → maxIncSequencesTo_lt`, a
  depth of 3.

## Why it is good

1. `erdos_szekeres` is declared at lines 142-166 of the file (*check*; permalink
   [#L142-L166](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean#L142-L166)).
2. The parent site cites `paired_injective` (*check*; the term appears at line 166 of the
   same permalink).
3. Lines 1-168 of the file contain no `sorry`, `admit`, or `axiom` (*check*; the whole
   [file](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean)).
4. The decomposition has 5 direct lemmas (child sites of 2, 2, 6, 2 and 2 lines), a
   25-line glue, and depth 3: the theorem cites `paired_injective`, which cites
   `maxDecSequencesTo_gt`, which cites `maxIncSequencesTo_lt` (*measurement*; counted from
   the site line ranges above).
5. The authors state the invariant and the pigeonhole plan in the theorem's docstring:
   "We label each value in the sequence with two numbers specifying the longest increasing
   subsequence ending there, and the longest decreasing subsequence ending there. We then
   show the pair of labels must be unique. Now if there is no increasing sequence longer
   than `r` and no decreasing sequence longer than `s`, then there are at most `r * s`
   possible labels, which is a contradiction if there are more than `r * s` elements."
   (*author-statement*; lines 135-140).

In my opinion the detail worth copying is the *shape* of the invariant, not its subject:
a pair `(L_inc i, L_dec i)` of two extremal quantities, one per direction, that is
injective precisely because one coordinate or the other must grow when the sequence is
injective. The pigeonhole box `Icc 1 r ×ˢ Icc 1 s` then falls out of the two `one_le_`
bounds without any extra work.

## When to use it, and when not

Use it for a pigeonhole argument over a finite type: the conclusion "some element of the
structure is large" is rephrased as "some element has a large label", the labelling is
made injective by a short case split, and the set of possible labels is a finite product
whose size is a product. Here the extremal quantities are the maximum lengths of
monotone sequences *ending at* an index, so the label `paired f i` is well-defined and
attained at every `i`.

Avoid it when the invariant cannot be made injective (each label component needs its own
comparison lemma, and here `maxDecSequencesTo_gt` only works because the decreasing side
is the increasing side on the order dual `βᵒᵈ`); when the label set is not a clean finite
product, so the cardinality bound is not `r * s`; or when the extremal object is a
supremum that need not be attained, since the whole argument leans on the attainment
lemmas `maxIncSequencesTo_mem` / `maxDecSequencesTo_mem` (the `max'` of a nonempty finite
set).

## Consequences

The move creates three obligations, one per supporting fact: prove the invariant is
attained at every index (`maxIncSequencesTo_mem` / `maxDecSequencesTo_mem`, from the
nonemptiness of the singleton sequence); prove the invariant is injective, a two-way case
split on `i < j ∨ j < i` backed by the comparison lemmas `maxIncSequencesTo_lt` and
`maxDecSequencesTo_gt`; and bound the label set below by 1
(`one_le_maxIncSequencesTo` / `one_le_maxDecSequencesTo`) so it is exactly the product box
`Icc 1 r ×ˢ Icc 1 s`.

Failure mode: the injectivity rests on order duality — `maxDecSequencesTo_gt` is
`maxIncSequencesTo_lt` at `βᵒᵈ` — so the invariant only works when the increasing and
decreasing halves are stated with the same "ends at `i`" notion. If the extremal object
were a supremum that need not be attained, the `one_mem_` / `max'_mem` lemmas would not
exist and the argument would need a different completion.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | mathlib4 CI: .github/workflows/build.yml runs on push to master (the default branch) and delegates to .github/workflows/build_template.yml, whose 'build' job runs 'lake-build-with-retry.sh Archive Counterexamples Wanted' and then 'lake build --no-build --wfail Archive'; the entry's file Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean is part of the Archive library, so CI builds it at commit e1545ebed97594477bbd88b2fe948ffce56e5af2 (merged to master, default branch) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: maxIncSequencesTo_mem@Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean:151, maxDecSequencesTo_mem@Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean:153, paired_injective@Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean:166, one_le_maxIncSequencesTo@Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean:164, one_le_maxDecSequencesTo@Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean:164; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at e1545ebed97594477bbd88b2fe948ffce56e5af2 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(erdos_szekeres, Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean, 142-166) -> declared: erdos_szekeres is declared at Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean:142 | check_claims.py |
| 2 | verified | cites(parent, paired_injective) -> cites: paired_injective occurs at Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean:166 | check_claims.py |
| 3 | verified | no_sorry(Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean, 1-168) -> no_sorry: none of sorry, admit, axiom in Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean:1-168 | check_claims.py |
| 4 | verified | Read the copied file Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean. 5 child lemmas at the stated line ranges: one_le_maxIncSequencesTo 66-67 (2), one_le_maxDecSequencesTo 68-69 (2), maxIncSequencesTo_mem 71-72 (2), maxDecSequencesTo_mem 73-74 (2), paired_injective 125-130 (6) = 2,2,6,2,2. Parent erdos_szekeres 142-166 = 25 lines. Depth chain: erdos_szekeres cites paired_injective at 166; paired_injective cites maxIncSequencesTo_lt (129) and maxDecSequencesTo_gt (130); maxDecSequencesTo_gt (110-112) cites maxIncSequencesTo_lt at 112 -> depth 3. | verifier |
| 5 | verified | Read the copied file's docstring above erdos_szekeres (lines 132-141). The quoted text matches verbatim (ignoring Lean backtick markup around r/s/r*s): 'We label each value in the sequence with two numbers specifying the longest increasing subsequence ending there, and the longest decreasing subsequence ending there. We then show the pair of labels must be unique. Now if there is no increasing sequence longer than r and no decreasing sequence longer than s, then there are at most r * s possible labels, which is a contradiction if there are more than r * s elements.' at lines 136-140; the locator L135-L140 opens one line early at 'Proof idea:'. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent erdos_szekeres (142-166, 25 lines) cites exactly the five children: maxIncSequencesTo_mem@151, maxDecSequencesTo_mem@153, one_le_maxIncSequencesTo@164, one_le_maxDecSequencesTo@164, paired_injective@166, and no other project lemma, so the children are exactly the lemmas the proof uses. Each child's statement and closed_by match the code (max'_mem/le_max' one-liners; paired_injective's case split on lt_or_gt_of_ne). Proof closes at 166 via card_le_card_of_injOn; no sorry/admit/axiom. Shape numbers right: glue_lines 25, child_lines [2,2,6,2,2] = 71-72,73-74,125-130,66-67,68-69, direct_lemmas 5, depth 3 = erdos_szekeres->paired_injective->maxDecSequencesTo_gt->maxIncSequencesTo_lt. | reviewer-correctness |
| generality | accept | Move stated generally: applicability/use_when and 'When to use it' reframe it as pigeonhole over a finite type with an injective pair-of-labels, and the opinion para isolates the reusable shape (two extremal quantities, one per direction, injective because a coordinate must grow). 'When not to use'/'avoid_when' is honest and specific: injectivity needs a comparison lemma per coordinate (cheap here only via order duality beta^op), label set must be a clean finite product, and the extremal object must be attained (max'_mem/one_mem), each a real failure mode of this argument. Consequences names three concrete obligations + the duality failure mode. Good-leaves question answered: _mem and one_le_ leaves are one-liners closing on singleton facts; paired_injective closes on two named siblings through a case split, giving depth 3. Minor non-blocking note: known_uses is empty, so the generality is asserted not evidenced by an independent use. | reviewer-generality |
| provenance-licence | accept | Provenance consistent and traceable: commit e1545ebed97594477bbd88b2fe948ffce56e5af2 matches across entry.json source, README, SOURCE.md and source.json; licence Apache-2.0 matches everywhere and upstream-LICENSE is Apache 2.0; copied file sha256 069584aa... and byte count 7464 match entry.json files[0]; check_provenance reports the file byte-identical at the pinned commit; permalinks use the pinned commit and correct Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean path. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover-community/mathlib4 at commit `e1545ebed97594477bbd88b2fe948ffce56e5af2`, under `Apache-2.0`; see the [source note](../../sources/mathlib4/SOURCE.md) for the licence text and attribution.
