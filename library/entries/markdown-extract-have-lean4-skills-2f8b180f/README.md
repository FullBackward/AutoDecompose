# Extract-have: lift the two inline haves of big_result into helper1 and helper2

| | |
|---|---|
| Kind | instance |
| Move | extract-have |
| Language | markdown |
| Status | draft |
| Source | [lean4-skills](../../sources/lean4-skills/SOURCE.md) at `3f913c66251b` |
| Licence | `MIT` |
| Licence recorded | 2026-11-12T15:19:46Z |

## Intent

A monolithic proof of `big_result` whose body holds two inline `have` blocks
(30 and 40 lines of tactics) plus a 30-line remainder is refactored into two
named lemmas, `helper1` and `helper2`, each owning one intermediate goal. The
main proof then reduces to a one-line application per lemma plus the
remainder, so each intermediate step is stated once, testable on its own, and
reusable.

## The decomposition

### parent `big_result`: [`plugins/lean4/skills/lean4/references/proof-refactoring.md` lines 208-212](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/proof-refactoring.md#L208-L212) ([local copy](code/plugins/lean4/skills/lean4/references/proof-refactoring.md))

```lean
theorem big_result : Conclusion := by
  intro x hx
  have h1 := helper1 x hx
  have h2 := helper2 x h1
  [30 lines - much clearer now]
```

### child `helper1`: [`plugins/lean4/skills/lean4/references/proof-refactoring.md` lines 202-203](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/proof-refactoring.md#L202-L203) ([local copy](code/plugins/lean4/skills/lean4/references/proof-refactoring.md))

```lean
lemma helper1 (x : α) (hx : Property x) : IntermediateGoal1 := by
  [30 lines - extracted from h1]
```

### child `helper2`: [`plugins/lean4/skills/lean4/references/proof-refactoring.md` lines 205-206](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/proof-refactoring.md#L205-L206) ([local copy](code/plugins/lean4/skills/lean4/references/proof-refactoring.md))

```lean
lemma helper2 (x : α) (h1 : IntermediateGoal1) : IntermediateGoal2 := by
  [40 lines - extracted from h2]
```

### context `before-monolithic`: [`plugins/lean4/skills/lean4/references/proof-refactoring.md` lines 192-199](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/proof-refactoring.md#L192-L199) ([local copy](code/plugins/lean4/skills/lean4/references/proof-refactoring.md))

```lean
-- BEFORE: Monolithic proof
theorem big_result : Conclusion := by
  intro x hx
  have h1 : IntermediateGoal1 := by
    [30 lines of tactics...]
  have h2 : IntermediateGoal2 := by
    [40 lines of tactics...]
  [30 more lines...]
```

How the parts fit. `helper2` depends on `helper1`: its second parameter
`h1 : IntermediateGoal1` is exactly `helper1`'s conclusion, so the two leaves
form a two-link chain

```
big_result ── have h1 := helper1 x hx ──▶ helper1 : Property x → IntermediateGoal1
    └──────── have h2 := helper2 x h1 ──▶ helper2 : IntermediateGoal1 → IntermediateGoal2
```

`big_result` applies `helper1` first (binding `h1`), then `helper2`
(consuming `h1`), then the 30-line remainder. The BEFORE block shows the same
two goals as inline `have`s (`have h1 : IntermediateGoal1`,
`have h2 : IntermediateGoal2`), so the two one-line applications in the AFTER
proof are exactly the glue: nothing else in the parent refers to how either
goal is proved.

Why each leaf is good. `helper1` is a self-contained statement —
`(x : α) → Property x → IntermediateGoal1` — that closes on its own from the
extracted 30-line block and takes only the hypotheses it uses (`x`, `hx`).
`helper2` is self-contained given its named sibling:
`(x : α) → IntermediateGoal1 → IntermediateGoal2`, closing from the extracted
40-line block with `helper1`'s conclusion as its only extra input. Because
`helper2` states its dependence on `helper1` as an explicit parameter rather
than re-proving it, the two leaves are independently provable and the parent's
glue is just composition.

## Why it is good

1. The AFTER proof of `big_result` cites exactly two lemmas, `helper1` and
   `helper2`, one application each (`have h1 := helper1 x hx`,
   `have h2 := helper2 x h1`), and these correspond one-to-one to the two
   inline goals of the BEFORE block (check, lines 192-212).
2. The main proof drops from the 8-line BEFORE block, embedding 70 lines of
   elided tactic blocks, to 5 lines of glue; the two extracted bodies move out
   into the lemmas (measurement, lines 192-199 versus 208-212).
3. The file states the trigger for this exact move in its own words: refactor
   on "Large preliminary calculations (50+ line `have` statements)" (line 59),
   and Step 3 is its illustration.
4. The same move recurs in the file's "Real Refactoring Example": the inline
   `have hk_bound : ... := by ...` is extracted to `private lemma
   strictMono_all_lt_succ_last` and the main proof "now just calls helper"
   (known-use, lines 309-330).

In my opinion the detail worth copying is that `helper2` takes the previous
lemma's conclusion as an explicit parameter, which records the dependency in
the type instead of leaving it implicit in the surrounding proof.

## When to use it, and when not

Use it when the proof body is dominated by intermediate goals stated as inline
`have`s whose tactic blocks are long (the file's trigger is a 50+ line `have`
statement, line 59) and whose statements are clean and self-contained with
local dependencies only. The extracted helper should take exactly the
hypotheses it uses, so each leaf is provable and testable on its own. Avoid it
when the `have` is short and linear, when the helper would need 10+ parameters
or its context is too tangled to separate cleanly (the file's "Bad
breakpoints", lines 182-187), or when the intermediate result depends on later
bindings so it cannot be stated before the parent. Do not extract
definitionally sensitive fragments: the file's Pattern 3.4 warns that
measure-theory manipulations with `let` bindings should stay inline.

## Consequences

Each extracted `have` becomes a top-level lemma whose statement must be exactly
the type the parent's `have` expects, with every hypothesis the body uses:
`helper1` must conclude in `IntermediateGoal1` given `hx : Property x`, and
`helper2` must take `h1 : IntermediateGoal1` — the previous lemma's conclusion
— or the glue `have h2 := helper2 x h1` will not elaborate. The file's Step 4
(lines 215-232) turns this into a check: the goal at the old `have` line must
match the helper's conclusion. A dropped or mismatched hypothesis breaks
sufficiency silently. Sequential dependence is the other cost: `helper2`
depends on `helper1`, so the two leaves are not parallelisable as stated (to
parallelise, `helper2` would re-prove `IntermediateGoal1` or take it as an
assumption).

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | not-run | The copied file is a Markdown skill reference (plugins/lean4/skills/lean4/references/proof-refactoring.md), not a Lean source module, so no CI workflow compiles it; its code blocks are illustrative pseudocode with placeholders like '[30 lines of tactics...]'. No Lean toolchain is installed on the harvest machine (protocol section 6), and a markdown file has no Lean build target. | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 3f913c66251b8712bb58e6ce83a453fa96e3f94f | check_provenance.py | 2026-11-12 |
| sorry-scan | not-run | no Lean, Rocq or Isabelle file among the copied files | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Opened the copied file. AFTER block (lines 208-212) cites exactly two lemmas, one application each: 'have h1 := helper1 x hx' (210) and 'have h2 := helper2 x h1' (211). BEFORE block (lines 192-199) has exactly the two inline goals 'have h1 : IntermediateGoal1 := by' (195) and 'have h2 : IntermediateGoal2 := by' (197), matching one-to-one. | verifier |
| 2 | verified | Counted on the copied file: BEFORE lines 192-199 are 8 lines and embed '[30 lines of tactics...]' (196) plus '[40 lines of tactics...]' (198), totalling 70 elided lines. AFTER lines 208-212 are 5 lines. helper1 carries '[30 lines - extracted from h1]' (203) and helper2 '[40 lines - extracted from h2]' (206), so the 30- and 40-line bodies are moved out. | verifier |
| 3 | verified | Line 59 of the copied file reads, verbatim, 'Large preliminary calculations (50+ line `have` statements)' under the '**Refactor when:**' list (line 53). The site (lines 208-212) sits under the '### Step 3: Extract Helper Lemma' heading (line 189), so it is Step 3's illustration. Note the Step 3 example uses 30/40-line haves rather than 50+, so the 'of that rule' link is loose, but the quoted author-statement is exact. | verifier |
| 4 | verified | Opened the copied file. '## Real Refactoring Example' (line 295). Inline 'have hk_bound : ∀ i : Fin (m' + 1), k i < n := by' (310) with body 311-316; extracted to 'private lemma strictMono_all_lt_succ_last' (321-327). Line 330 reads '**Result:** Main proof now just calls helper, much clearer.' All cited lines match. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Correctness verified against the copied file code/plugins/lean4/skills/lean4/references/proof-refactoring.md. Parent statement and site lines match: theorem big_result : Conclusion at L208-212 (5 lines). Child statements verbatim: helper1 L202-203 (x:alpha)(hx:Property x):IntermediateGoal1; helper2 L205-206 (x:alpha)(h1:IntermediateGoal1):IntermediateGoal2. Closing methods match the elided blocks '[30 lines - extracted from h1]' and '[40 lines - extracted from h2]'. Children are exactly the lemmas the main proof uses: AFTER proof (L210-211) cites only helper1 and helper2, one application each (have h1 := helper1 x hx; have h2 := helper2 x h1), one-to-one with the BEFORE inline haves (L195-198). Glue is type-consistent so it closes: helper1's conclusion IntermediateGoal1 is passed as helper2's h1 parameter, then the 30-line remainder reaches Conclusion. Shape numbers: direct_lemmas=2 (correct), glue_lines=5 (L208-212, correct), child_lines=[2,2] (each child 2 lines, correct), scale=theorem (correct, >=2 named child lemmas). depth=2 is justified by the entry's stated sequential dependency (helper2 consumes helper1's conclusion as a parameter, a two-link chain, non-parallelisable), which the consequences field documents consistently. Claims 1-4 all check out against the cited lines (L59 trigger quote verbatim; L309-330 known-use extraction to strictMono_all_lt_succ_last; 'now just calls helper' L330). | reviewer-correctness |
| generality | accept | Move stated generally: applicability.goal_shape gives the rule (lift 'have h : T := by <block>' to a lemma concluding T whose parameters are exactly the hypotheses the block uses; parent becomes 'have h := helper <args>'), and use_when/avoid_when generalize the trigger and boundaries. When-not-to-use and consequences are honest and specific, each locator confirmed in the copied proof-refactoring.md (trigger line 59, Bad breakpoints 182-187, Pattern 3.4 let-binding caution 644-648, Step 4 goal-match check 215-232); consequences name the silent sufficiency break and non-parallelizable sequential leaves. Why-each-leaf-is-good states the bounded-prover-relevant qualities: self-contained, takes only the hypotheses it uses, dependency recorded as an explicit parameter, independently provable, glue is composition. | reviewer-generality |
| provenance-licence | accept | Commit 3f913c66251b8712bb58e6ce83a453fa96e3f94f is consistent across entry.json, source.json, SOURCE.md and every permalink; check_provenance passes (copied file byte-identical at that commit, 28691 bytes matches bytes field). Licence MIT is consistent across entry.json, source.json, SOURCE.md and the upstream-LICENSE text (MIT License, copyright Lean 4 Theorem Proving Skill Contributors). Source note records repo URL, commit, licence files and attribution. All line anchors (59, 182-187, 192-199, 202-203, 205-206, 208-212, 215-232) match the copied file's content. Traceable end to end. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/cameronfreer/lean4-skills at commit `3f913c66251b8712bb58e6ce83a453fa96e3f94f`, under `MIT`; see the [source note](../../sources/lean4-skills/SOURCE.md) for the licence text and attribution.
