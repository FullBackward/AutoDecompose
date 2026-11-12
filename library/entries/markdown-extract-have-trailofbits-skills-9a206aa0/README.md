# The extraction ladder

| | |
|---|---|
| Kind | skill |
| Move | extract-have |
| Language | markdown |
| Status | accepted |
| Source | [trailofbits-skills](../../sources/trailofbits-skills/SOURCE.md) at `e4dd0bb5b155` |
| Licence | `CC-BY-SA-4.0` |

## Intent

A graded rule for deciding when a proof fragment graduates from an inline
argument into a local `have` and then a standalone lemma: search by shape
first (rung 0), name a repeated sub-argument as a local `have` (rung 1),
promote an independently interesting or hypothesis-shedding statement to a
standalone lemma (rung 2), and split a proof that reads "long and unwieldy"
(rung 3).

## The decomposition

### skill-text `the-extraction-ladder`: [`plugins/writing-lean-proofs/skills/writing-lean-proofs/SKILL.md` lines 158-193](https://github.com/trailofbits/skills/blob/e4dd0bb5b15535f7c5a0834187dffba6ac37e4ff/plugins/writing-lean-proofs/skills/writing-lean-proofs/SKILL.md#L158-L193) ([local copy](code/plugins/writing-lean-proofs/skills/writing-lean-proofs/SKILL.md))

````markdown
## The extraction ladder

When does proof structure graduate into separate lemmas?

0. **Before extracting, state the fragment's type and search by shape.** Put
   the proposed statement in a scratch `example`, run `exact?` and `apply?`
   on the bare goal, then try a type-pattern and source search. If an existing
   theorem fits, use it. Do not report an API gap without recording the
   searches that failed.

1. **A sub-argument repeats within one proof** → name it as a local `have`.

   ```lean
   theorem min_comm (a b : ℝ) : min a b = min b a := by
     have h : ∀ x y : ℝ, min x y ≤ min y x := by
       intro x y
       apply le_min
       · show min x y ≤ y
         exact min_le_right x y
       · show min x y ≤ x
         exact min_le_left x y
     apply le_antisymm
     · show min a b ≤ min b a
       exact h a b
     · show min b a ≤ min a b
       exact h b a
   ```

2. **The statement is independently interesting, or extraction sheds
   hypotheses the sub-argument does not need** → standalone lemma. Dropping
   unneeded hypotheses is the stronger trigger: the extracted lemma becomes
   more general than the proof it came from.
3. **The proof reads as "long and unwieldy"** → split it. This is Mathlib's
   review criterion, and it is deliberately qualitative — there is no line
   threshold. Resolve doubt by attempting the extraction: if a fragment has
   a clean statement, it wanted to be a lemma.
````

How the parts fit. The ladder is an ordered decision: rung 0 (search by shape)
comes first, so a fragment is extracted only after `exact?`/`apply?` and a
type/source search have failed to find an existing theorem. Rung 1 names a
sub-argument that repeats within one proof as a local `have`; its worked
example is `min_comm`, where the quantified `have h : ∀ x y : ℝ, min x y ≤ min y x`
is used twice — `apply le_antisymm` splits the equality into two ≤-goals,
`min a b ≤ min b a` (closed by `exact h a b`) and `min b a ≤ min a b` (closed
by `exact h b a`). Rung 2 graduates the fragment to a standalone lemma when the
statement is independently interesting or, more strongly, when extraction
* sheds hypotheses the sub-argument does not need*. Rung 3 is the catch-all for
a proof that reads "long and unwieldy", decided not by a line count but by
attempting the extraction: a fragment with a clean statement wanted to be a
lemma.

## Why it is good

1. The worked example closes both directions from one extracted fragment: the
   local `have h` is instantiated twice and closes the two `le_antisymm` goals
   with `exact h a b` and `exact h b a` (lines 179-183).
2. The four rungs are ordered so extraction is always preceded by a search
   (rung 0, line 162), then graduates from local `have` (rung 1, line 168) to
   standalone lemma (rung 2, line 186) to split (rung 3, line 190).
3. The trigger for a standalone lemma is dropping hypotheses, stated by the
   authors: "extraction sheds hypotheses the sub-argument does not need" and
   "Dropping unneeded hypotheses is the stronger trigger: the extracted lemma
   becomes more general than the proof it came from" (lines 186-189).
4. Rung 3 is explicitly qualitative, not a line threshold: "it is deliberately
   qualitative — there is no line threshold" (lines 190-192).
5. The same "drop hypotheses → general" trigger recurs in the skill's
   Rationalizations to reject table: "This helper is too specific to be a
   lemma" is answered by "If it has a clean statement, extract it — dropping
   the hypotheses it doesn't need usually reveals it was general all along"
   (line 230).

In my opinion the most reusable detail is rung 2's trigger — "sheds
hypotheses" — because it turns an aesthetic call ("is this worth a lemma?")
into a testable one: count the hypotheses the fragment actually uses.

## When to use it, and when not

Use it when a sub-argument is needed more than once in one proof (rung 1), a
fragment is independently interesting or its extraction drops hypotheses
(rung 2), or a proof reads "long and unwieldy" (rung 3). Always search by
shape first (rung 0) before extracting. Avoid it when an existing theorem
already fits the fragment's shape (rung 0), when the fragment is used once
with no independent meaning, when extraction would drop no hypotheses and
generalise nothing, or when the project defers to a non-Mathlib house style
(the skill's "When NOT to Use" says check the project's CONTRIBUTING first).

## Consequences

Lifting to a local `have` (rung 1) keeps the fragment local but requires the
caller to instantiate the quantified form at each use site (`h a b`,
`h b a`). Lifting to a standalone lemma (rung 2) requires stating the fragment
with exactly the hypotheses it needs and dropping the rest: under-generalising
keeps proof-specific constants and limits reuse, while over-generalising adds
hypotheses the caller must discharge. Rung 0 is the fidelity gate — extracting
before searching duplicates an existing theorem, and the skill forbids
reporting an API gap without recording the failed searches. Rung 3's criterion
is deliberately qualitative and so cannot be turned into a line threshold; the
test is whether the fragment has a clean statement. The `min_comm` example
stops at rung 1 (a local `have`), so it does not exercise rung 2's
standalone-lemma obligations.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | Source CI .github/workflows/validate.yml runs on push/PR to default branch main. Its 'Validate SKILL.md frontmatter' step walks every plugins/**/SKILL.md, which includes this file (plugins/writing-lean-proofs/skills/writing-lean-proofs/SKILL.md), and 'Check Claude loadability' runs .github/scripts/check_claude_loadability.py. Commit e4dd0bb5b15535f7c5a0834187dffba6ac37e4ff is head of default branch main (GitHub API: default_branch=main; branches-where-head returns main). Note: the file is Markdown, so CI validates frontmatter/loadability rather than compiling Lean. | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at e4dd0bb5b15535f7c5a0834187dffba6ac37e4ff | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read the copied code file plugins/writing-lean-proofs/skills/writing-lean-proofs/SKILL.md lines 170-184: line 172 declares 'have h : forall x y : R, min x y <= min y x'; line 179 'apply le_antisymm' creates two goals; line 181 'exact h a b' and line 183 'exact h b a' close them. h is instantiated exactly twice, no other use of h. Matches the claim. | verifier |
| 2 | verified | Read copied file lines 158-193: rung 0 'Before extracting... search by shape' at line 162; rung 1 'A sub-argument repeats... local have' at line 168; rung 2 'independently interesting... standalone lemma' at line 186; rung 3 'long and unwieldy... split it' at line 190. The four rungs appear in ascending order 0-3 at exactly those line numbers. | verifier |
| 3 | verified | Read copied file lines 186-189: 'extraction sheds hypotheses the sub-argument does not need' (186-187) and 'Dropping unneeded hypotheses is the stronger trigger: the extracted lemma becomes more general than the proof it came from.' (187-189). Both quoted phrases present verbatim. | verifier |
| 4 | verified | Read copied file lines 190-192: 'This is Mathlib's review criterion, and it is deliberately qualitative — there is no line threshold.' spans lines 190-191, followed by 'Resolve doubt by attempting the extraction...'. The quoted sentence is present verbatim, stating rung 3 is qualitative with no line threshold. | verifier |
| 5 | verified | Read copied file line 230 in the Rationalizations-to-reject table: excuse 'This helper is too specific to be a lemma' paired with reality 'If it has a clean statement, extract it — dropping the hypotheses it doesn't need usually reveals it was general all along.' Both quoted phrases present verbatim. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Read the copied SKILL.md: lines 158-193 contain the extraction ladder with rungs 0-3 (search-by-shape L162, local-have L168, standalone-lemma L186, split-long-proof L190), matching the four children verbatim; the min_comm worked example (L171-183) instantiates have h twice via exact h a b / exact h b a and closes both le_antisymm goals, so the decomposition is what the entry says and closes. | reviewer-correctness |
| generality | accept | Move is stated as a four-rung ladder (search by shape, local have, standalone lemma, split) independent of the single min_comm worked example; applicability.goal_shape/use_when/avoid_when restate the rungs as general conditions. 'When not to use' maps each avoid-condition to a rung (existing theorem fits=rung 0; used once with no independent meaning=rung 2 negation; no hypotheses dropped; non-Mathlib house style, matching the skill's 'When NOT to Use' CONTRIBUTING caveat). Consequences are specific and honest, including the caveat that min_comm stops at rung 1 and never exercises rung 2, and an explicit under-/over-generalisation treatment. | reviewer-generality |
| provenance-licence | accept | check_provenance passes (1 file byte-identical at e4dd0bb5b15535f7c5a0834187dffba6ac37e4ff). Commit e4dd0bb5b15535f7c5a0834187dffba6ac37e4ff recorded identically in entry.json, README.md, SOURCE.md, source.json; all permalinks in files[] and sites[] use that commit and the correct path. Licence CC-BY-SA-4.0 recorded identically in all four places and matches upstream-LICENSE (Attribution-ShareAlike 4.0 International). Source note points to LICENSE and copies it as upstream-LICENSE. Everything consistent and traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/trailofbits/skills at commit `e4dd0bb5b15535f7c5a0834187dffba6ac37e4ff`, under `CC-BY-SA-4.0`; see the [source note](../../sources/trailofbits-skills/SOURCE.md) for the licence text and attribution.
