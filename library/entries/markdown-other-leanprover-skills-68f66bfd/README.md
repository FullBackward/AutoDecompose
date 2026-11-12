# Lemma-splitting: one hard equality into two helper lemmas joined by rw

| | |
|---|---|
| Kind | skill |
| Move | other |
| Language | markdown |
| Status | draft |
| Source | [leanprover-skills](../../sources/leanprover-skills/SOURCE.md) at `7d3da0282e7b` |
| Licence | `Apache-2.0` |

## Intent

Replace one hard equality `A = C` with two simpler equalities `A = B` and
`B = C` by introducing an intermediate term `B`, then close the parent with a
single rewrite chain `rw [lemma1, lemma2]`. The parent is fully proved, and the
difficulty is relocated into two smaller, independent holes.

## The decomposition

### skill-text `across-theorems-lemma-splitting`: [`skills/lean-proof/SKILL.md` lines 29-44](https://github.com/leanprover/skills/blob/7d3da0282e7b724b07620e45cf212f2e05e19334/skills/lean-proof/SKILL.md#L29-L44) ([local copy](code/skills/lean-proof/SKILL.md))

````markdown
### Across Theorems

Go directly to the target theorem. Don't fill in `sorry`s in helper lemmas first — Lean treats `sorry` as an axiom, so dependent theorems still work.

Move sorries earlier in the file by replacing a `sorry` proof with references to simpler lemmas:

```lean
-- Before:
theorem main_theorem : A = C := by sorry

-- After:
theorem lemma1 : A = B := by sorry
theorem lemma2 : B = C := by sorry
theorem main_theorem : A = C := by
  rw [lemma1, lemma2]
```
````

This is the "Across Theorems" subsection of the `lean-proof` skill. It gives a
two-state recipe. *Before*: one theorem, `main_theorem : A = C`, closed by a
single `sorry` (line 37). *After*: the same theorem is closed by
`rw [lemma1, lemma2]` (lines 42-43), and two new helper lemmas carry the
`sorry`s — `lemma1 : A = B` (line 40) and `lemma2 : B = C` (line 41).

The parts fit as a two-link equality chain. The intermediate `B` is introduced
only as the right-hand side of `lemma1` and the left-hand side of `lemma2`.
`rw [lemma1, lemma2]` rewrites the goal `A = C` to `B = C` using `lemma1`, then
to `C = C` using `lemma2`, which closes by reflexivity. So the parent contains
no `sorry`; each remaining hole is a single equality between adjacent terms,
deliberately simpler than the original `A = C`.

The sentence above the example (line 31) explains why the sorries are moved
*toward the helpers* rather than the reverse: "Lean treats `sorry` as an axiom,
so dependent theorems still work." The skill's policy is to work on the target
theorem first, leaving the helper lemmas as placeholders while the harder,
higher-value goal is settled.

## Why it is good

1. The After block closes `main_theorem : A = C` with the single tactic
   `rw [lemma1, lemma2]` (line 43), and the parent's two lines (42-43) contain
   no `sorry`; the only two `sorry`s in the After block are the helper lemmas
   `lemma1` (line 40) and `lemma2` (line 41) (`check`, lines 36-44).
2. The skill states the move and its reason in its own words: "Move sorries
   earlier in the file by replacing a `sorry` proof with references to simpler
   lemmas" (line 33), motivated by "Go directly to the target theorem. Don't
   fill in `sorry`s in helper lemmas first" (line 31) (`author-statement`,
   lines 29-33).
3. Counting `sorry` in the example: the Before state has one `sorry` on the
   whole goal (line 37); the After state has two (lines 40-41), each on an
   equality between adjacent terms, and the parent (lines 42-43) has none
   (`measurement`, lines 36-44).

In my opinion the detail worth copying is that the intermediate `B` is never
named in the parent: it exists only as the shared side of the two lemmas, so
the rewrite chain is the entire proof and the two holes are manifestly
independent.

## When to use it, and when not

Use it when the goal is an equality `A = C` (or another relation `rw` can
chain) and there is a natural intermediate `B` — a definitional unfolding, a
canonical or normal form, the midpoint of a calculation — such that `A = B` and
`B = C` are each easier than `A = C`. Also use it when you want to work
top-down: prove the target's structure first and leave the helpers as `sorry`.
Avoid it when no such `B` exists (the two halves would be as hard as the
whole), when the two helper lemmas are not independent (one needs the other, so
the chain gives no real split), or when the goal is not an equality/transitive
relation that `rw` composes.

## Consequences

The move creates two new top-level lemmas (`lemma1`, `lemma2`) that must
eventually be proved or left as `sorry`. The parent's proof now depends on the
intermediate `B` and on the rewrite chain composing: `rw [lemma1]` rewrites
`A` to `B`, then `rw [lemma2]` rewrites `B` to `C`. It closes nothing by
itself — it relocates one hole into two, and is only a win if each new hole is
genuinely simpler. Failure mode: if `B` is not equal to `A` and `C` via the
stated lemmas, `rw [lemma1, lemma2]` fails at the first link that does not
apply.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | not-run | The entry's only file is a Markdown skill file (skills/lean-proof/SKILL.md), not compiled Lean code; no CI workflow builds it. | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 7d3da0282e7b724b07620e45cf212f2e05e19334 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read copied file code/skills/lean-proof/SKILL.md: line 43 is '  rw [lemma1, lemma2]'; lines 42-43 ('theorem main_theorem : A = C := by' / 'rw [lemma1, lemma2]') contain no sorry; the only sorries in the After block are line 40 'theorem lemma1 : A = B := by sorry' and line 41 'theorem lemma2 : B = C := by sorry'. | verifier |
| 2 | verified | Read copied file SKILL.md: line 33 says Move sorries earlier in the file by replacing a sorry proof with references to simpler lemmas, and line 31 says Go directly to the target theorem. Do not fill in sorries in helper lemmas first; Lean treats sorry as an axiom, so dependent theorems still work. Both quotes match verbatim. | verifier |
| 3 | verified | Read copied file lines 36-44: Before parent (line 37) 'theorem main_theorem : A = C := by sorry' has one sorry; After block has two sorries at lines 40-41 (lemma1, lemma2); After parent lines 42-43 have none. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Copied code skills/lean-proof/SKILL.md lines 29-44 matches the entry. Decomposition: parent main_theorem : A = C (line 37 before, 42-43 after) is split into children lemma1 : A = B (line 40) and lemma2 : B = C (line 41), joined by rw [lemma1, lemma2] (line 43); this closes the parent (rw rewrites A->B then B->C, closing by reflexivity). Children closed_by 'sorry' matches lines 40-41 verbatim; parent field null is correct for a skill. All line refs (31, 33, 37, 40, 41, 42-43) exact. Entry is honest that the two helper holes remain sorry, so the move relocates rather than eliminates the hole. | reviewer-correctness |
| generality | accept | Move stated abstractly (A, B, C with a natural intermediate B, or any relation rw chains), so it applies beyond the one skill file; applicability.use_when/avoid_when and the README give three specific honest 'when not to use' conditions (no natural B; helpers not independent; goal not a transitive relation rw composes). Consequences are honest and specific: the move creates two new top-level lemmas that must be proved or left as sorry, relocates one hole into two and is only a win if each hole is genuinely simpler, with a concrete failure mode (rw fails at the first inapplicable link). | reviewer-generality |
| provenance-licence | accept | Provenance check passes (1 file byte-identical at 7d3da0282e7b724b07620e45cf212f2e05e19334). Permalinks in entry.json (files[] and sites[]) use the same pinned commit and path skills/lean-proof/SKILL.md as the copied file; site line range 29-44 matches the copied excerpt. source.licence=Apache-2.0, README Licence=Apache-2.0, SOURCE.md licence=Apache-2.0, and upstream-LICENSE is Apache License Version 2.0 (LICENSE file). Commit is consistent across source.json, entry.json, README and SOURCE.md. Source note records repo, pinned commit, licence, licence file and attribution. Everything traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover/skills at commit `7d3da0282e7b724b07620e45cf212f2e05e19334`, under `Apache-2.0`; see the [source note](../../sources/leanprover-skills/SOURCE.md) for the licence text and attribution.
