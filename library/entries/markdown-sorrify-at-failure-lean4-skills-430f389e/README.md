# Sorrify-at-failure: five common sorry types and their responses

| | |
|---|---|
| Kind | skill |
| Move | sorrify-at-failure |
| Language | markdown |
| Status | draft |
| Source | [lean4-skills](../../sources/lean4-skills/SOURCE.md) at `3f913c66251b` |
| Licence | `MIT` |

## Intent

Classify why a `sorry` resists filling into five ordered types so the filler
picks the right response: search, a tactic, or a `have` for the cheap cases,
and for the structural case (Type 4) replace the too-large goal with
sub-sorries and work them one at a time, escalating to a separate helper
lemma (Type 5) when the hole is in fact a missing statement.

## The decomposition

### skill-text `sorry-filling-common-sorry-types`: [`plugins/lean4/skills/lean4/references/sorry-filling.md` lines 88-103](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/sorry-filling.md#L88-L103) ([local copy](code/plugins/lean4/skills/lean4/references/sorry-filling.md))

```markdown
## Common Sorry Types

### Type 1: "Forgot to search mathlib" (most common)
**Solution:** Search thoroughly, apply existing lemma

### Type 2: "Just needs right tactic" (common)
**Solution:** Try `rfl`, `simp`, `ring`, or domain automation

### Type 3: "Missing intermediate step" (less common)
**Solution:** Add `have` with connecting lemma

### Type 4: "Complex structural proof" (rare)
**Solution:** Break into sub-sorries with clear strategy

### Type 5: "Actually needs new lemma" (very rare)
**Solution:** Extract as helper lemma, prove separately
```

### context `when-to-escalate`: [`plugins/lean4/skills/lean4/references/sorry-filling.md` lines 242-253](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/sorry-filling.md#L242-L253) ([local copy](code/plugins/lean4/skills/lean4/references/sorry-filling.md))

```markdown
## When to Escalate

**Give up and escalate if:**
- All 3 candidates fail with same error
- Goal requires domain knowledge you don't have
- Needs multi-file refactoring
- Missing foundational lemmas
- Time spent > 15 minutes on single sorry

**Escalation options:**
- Break into smaller sub-sorries
- Extract as helper lemma
```

How the parts fit. The skill-text site is a decision ladder ordered by
frequency: Types 1-3 are the cheap responses (search mathlib, apply the right
tactic, add a connecting `have`), and only the two rare structural cases touch
the `sorrify-at-failure` move. Type 4 is the move itself — a goal too large to
fill in one step is replaced by sub-sorries, each worked one at a time. Type 5
is the escalation when the hole is not a hole at all but a missing statement:
extract it as a helper lemma and prove it separately. The context site
("When to Escalate") is where the same two responses reappear as the first two
escalation options. A further branch sits just below it in the same file
(lines 257-261, visible in the local copy): if the statement may be false, run
preflight falsification and salvage (`T_counterexample`, `T_salvaged`) rather
than keep sorrifying.

## Why it is good

1. The section classifies why a sorry resists filling into exactly five types,
   each heading stating a frequency in order: "most common" (Type 1) through
   "very rare" (Type 5) (lines 88-103) (`check`).
2. Type 4's response is the move verbatim — "Break into sub-sorries with clear
   strategy" (lines 99-100): replace the too-large goal with holes and work
   them one at a time (`check`).
3. For the very rare case the authors name a missing statement and prescribe
   "Extract as helper lemma, prove separately" (lines 102-103)
   (`author-statement`).
4. The same two structural responses recur as the first two escalation options
   in "When to Escalate": "Break into smaller sub-sorries" and "Extract as
   helper lemma" (lines 251-253) (`author-statement`).

In my opinion the value is the triage, not the tactics: the classification
makes sorrifying a *conditional* move — it is the response only for the rare
structural case, never a substitute for searching or for stating the missing
lemma.

## When to use it, and when not

Use it when a hole has resisted 2-3 direct candidates and you must decide
between searching, a tactic, a `have`, a sub-sorry split, or a helper lemma.
Use the sub-sorry split (Type 4) only when the proof is structurally complex
but does not need a new fact. Do not use it when the hole is only a missed
search (search first), a routine goal (try the tactic), or a missing statement
(extract a lemma rather than sorrify); the section orders these so the
structural split is last-resort and itself marked "rare".

## Consequences

Sorrifying a structural goal (Type 4) creates several smaller holes, each still
needing a filler and its own verification gate (`lake env lean`); it shrinks
each obligation but not the total. Extracting a helper lemma (Type 5) introduces
a new top-level statement that must be stated faithfully (its hypotheses and
universals) and proved, with the original hole becoming an application of it.
Both are marked "rare"/"very rare", so over-applying them where a search or a
tactic would close the goal is the failure mode.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | not-run | markdown skill reference file (sorry-filling.md); not a compiled Lean module, so no CI build compiles it | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 3f913c66251b8712bb58e6ce83a453fa96e3f94f | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read copied file code/plugins/lean4/skills/lean4/references/sorry-filling.md lines 88-103: five '### Type N' headings with frequencies most common / common / less common / rare / very rare in order | verifier |
| 2 | verified | Read copied file lines 99-100: '### Type 4: "Complex structural proof" (rare)' then '**Solution:** Break into sub-sorries with clear strategy' verbatim | verifier |
| 3 | verified | Read copied file lines 102-103: '### Type 5: "Actually needs new lemma" (very rare)' and '**Solution:** Extract as helper lemma, prove separately' verbatim | verifier |
| 4 | verified | Read copied file lines 251-253: '**Escalation options:**' followed by '- Break into smaller sub-sorries' and '- Extract as helper lemma' as the first two options | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Skill entry (no parent/children, so 'closes' is n/a). Copied file code/plugins/lean4/skills/lean4/references/sorry-filling.md matches the README excerpts and all four claims: lines 88-103 enumerate exactly five types with frequencies most common/common/less common/rare/very rare (claim 1); line 100 'Break into sub-sorries with clear strategy' is the Type 4 response verbatim (claim 2); line 102-103 'Actually needs new lemma (very rare)' + 'Extract as helper lemma, prove separately' (claim 3); lines 252-253 are the first two escalation options (claim 4). The README's context excerpt (242-253) and the false-statement branch note (257-261) also match. check_provenance.py passes byte-identical at 3f913c66251b. | reviewer-correctness |
| generality | object | Move is stated generically (replace too-large goal with sub-sorries, work one at a time; escalate to helper lemma) and consequences are honest/specific ('shrinks each obligation but not the total'; helper lemma must be stated faithfully). But 'when not to use'/avoid_when is incomplete on the one case where the move cannot work: the source's own 'When to Escalate' (lines 257-261) prescribes 'If statement may be false: run preflight falsification ... create T_salvaged' rather than keep sorrifying, and the entry's README lines 68-71 acknowledges this branch, yet neither the README 'when not' prose nor entry.json avoid_when carries it. Fix: add to 'when not to use' and avoid_when a clause like 'or when the statement may be false -- falsify and salvage (T_counterexample/T_salvaged) instead of keep sorrifying (lines 257-261)'. | reviewer-generality |
| provenance-licence | accept | Commit 3f913c66251b8712bb58e6ce83a453fa96e3f94f is consistent across entry.json, sources/lean4-skills/SOURCE.md and source.json. Licence is MIT everywhere (entry.json, source.json, SOURCE.md) and sources/lean4-skills/upstream-LICENSE holds the MIT text (c) 2025 Lean 4 Theorem Proving Skill Contributors. check_provenance.py passes: 1 file byte-identical at the pinned commit and the recorded sha256 matches; local copy is 11663 bytes as recorded. All permalinks use the same commit and the file path plugins/lean4/skills/lean4/references/sorry-filling.md, with line anchors 88-103 and 242-253 matching the copied content. Source note records repo URL, commit, licence and attribution. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/cameronfreer/lean4-skills at commit `3f913c66251b8712bb58e6ce83a453fa96e3f94f`, under `MIT`; see the [source note](../../sources/lean4-skills/SOURCE.md) for the licence text and attribution.
