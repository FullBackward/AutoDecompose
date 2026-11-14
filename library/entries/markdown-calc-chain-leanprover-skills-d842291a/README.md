# Across Theorems: main_theorem via lemma1, lemma2

| | |
|---|---|
| Kind | instance |
| Move | calc-chain |
| Language | markdown |
| Status | draft |
| Source | [leanprover-skills](../../sources/leanprover-skills/SOURCE.md) at `7d3da0282e7b` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-12T15:23:08Z |

## Intent

Replace a single theorem `main_theorem : A = C` held by a `sorry` with two named
helper lemmas `lemma1 : A = B` and `lemma2 : B = C`, and a parent whose entire
proof is the two-step rewrite chain `rw [lemma1, lemma2]`. Each remaining hole is
a smaller equality than the original, and the parent closes the moment both
helpers are filled.

## The decomposition

### parent `main_theorem`: [`skills/lean-proof/SKILL.md` lines 42-43](https://github.com/leanprover/skills/blob/7d3da0282e7b724b07620e45cf212f2e05e19334/skills/lean-proof/SKILL.md#L42-L43) ([local copy](code/skills/lean-proof/SKILL.md))

```markdown
theorem main_theorem : A = C := by
  rw [lemma1, lemma2]
```

### child `lemma1`: [`skills/lean-proof/SKILL.md` lines 40-40](https://github.com/leanprover/skills/blob/7d3da0282e7b724b07620e45cf212f2e05e19334/skills/lean-proof/SKILL.md#L40-L40) ([local copy](code/skills/lean-proof/SKILL.md))

```markdown
theorem lemma1 : A = B := by sorry
```

### child `lemma2`: [`skills/lean-proof/SKILL.md` lines 41-41](https://github.com/leanprover/skills/blob/7d3da0282e7b724b07620e45cf212f2e05e19334/skills/lean-proof/SKILL.md#L41-L41) ([local copy](code/skills/lean-proof/SKILL.md))

```markdown
theorem lemma2 : B = C := by sorry
```

### context `before_main_theorem`: [`skills/lean-proof/SKILL.md` lines 37-37](https://github.com/leanprover/skills/blob/7d3da0282e7b724b07620e45cf212f2e05e19334/skills/lean-proof/SKILL.md#L37-L37) ([local copy](code/skills/lean-proof/SKILL.md))

```markdown
theorem main_theorem : A = C := by sorry
```

### skill-text `across_theorems_rule`: [`skills/lean-proof/SKILL.md` lines 29-33](https://github.com/leanprover/skills/blob/7d3da0282e7b724b07620e45cf212f2e05e19334/skills/lean-proof/SKILL.md#L29-L33) ([local copy](code/skills/lean-proof/SKILL.md))

```markdown
### Across Theorems

Go directly to the target theorem. Don't fill in `sorry`s in helper lemmas first — Lean treats `sorry` as an axiom, so dependent theorems still work.

Move sorries earlier in the file by replacing a `sorry` proof with references to simpler lemmas:
```

Lemma graph (text): `main_theorem` (the glue) uses `lemma1` then `lemma2` and
nothing else; `lemma1` and `lemma2` are siblings and neither uses the other, so
the depth below `main_theorem` is 1.

The `before_main_theorem` context shows the undecomposed form: one theorem
`main_theorem : A = C := by sorry`. The `after` form is the decomposition. The
parent's proof is exactly `rw [lemma1, lemma2]`: `rw [lemma1]` rewrites `A` to
`B`, then `rw [lemma2]` rewrites `B` to `C`, closing `A = C`. `lemma1` is a good
leaf because its statement `A = B` is self-contained (no hypotheses, no local
context) and closes on its own once filled; likewise `lemma2 : B = C`. Neither
child is closed in the example — both are `by sorry` — because the skill's point
is the shape of the split, not a finished proof. The skill-text makes the rule
explicit: move sorries into smaller helper lemmas and leave the parent as a
rewrite skeleton.

## Why it is good

1. The parent `main_theorem`'s whole proof is one line, `rw [lemma1, lemma2]`,
   closing `A = C` from exactly the two children (lines 42-43).
2. The shape is `direct_lemmas = 2`, `depth = 1`, `glue_lines = 1`,
   `child_lines = [1, 1]`: one line of glue and one line per helper
   (lines 40-43).
3. The skill states the rule in its own words — "Move sorries earlier in the
   file by replacing a `sorry` proof with references to simpler lemmas"
   (line 33) — and permits `by sorry` for placeholders (line 14).
4. Both children are themselves holes (`by sorry`, lines 40-41): a teaching
   skeleton, not a closed instance.

In my opinion the detail worth copying is that the parent is reduced to a bare
rewrite skeleton, so the parent is trivial the moment the leaves are filled —
the decomposition *is* the lemma graph AutoDecompose must produce.

## When to use it, and when not

Use it when a target equality is stuck (a single `sorry`) and an intermediate
value `B` splits it into two smaller, self-contained equalities, each a named
lemma so `rw` can rewrite by name. Avoid it when the intermediate `B` does not
genuinely simplify either side (the children are then no smaller than the
parent), when the helpers need hypotheses or local context that a bare `rw`
cannot supply, or when the equality is already a single rewrite step.

## Consequences

The helper statements must typecheck even while `sorry` (Lean treats `sorry` as
an axiom, so the file shows no error but also no proof). The two lemmas must
share the same intermediate `B` and the right orientation: `rw [lemma1, lemma2]`
rewrites `A` to `B` then `B` to `C`, so `lemma1 : B = A` or a mismatched middle
value breaks the chain. The move leaves the proof incomplete by design — the
skill forbids declaring done while any `sorry` remains (line 93) — so the real
work is deferred to filling `lemma1` and `lemma2`.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | not-run | Entry code is skills/lean-proof/SKILL.md, a Markdown skill file, not Lean source, so no build applies; the embedded example deliberately uses 'by sorry' and is a teaching skeleton, not a compiling proof. No toolchain installed. | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 7d3da0282e7b724b07620e45cf212f2e05e19334 | check_provenance.py | 2026-11-12 |
| sorry-scan | not-run | no Lean, Rocq or Isabelle file among the copied files | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Opened code/skills/lean-proof/SKILL.md at pinned commit: L42 'theorem main_theorem : A = C := by', L43 '  rw [lemma1, lemma2]'. The parent's entire proof is exactly rw [lemma1, lemma2], closing A = C from the two named children. | verifier |
| 2 | verified | Opened code/skills/lean-proof/SKILL.md L40-L43: L40 'theorem lemma1 : A = B := by sorry' (one line), L41 'theorem lemma2 : B = C := by sorry' (one line), L42-L43 main_theorem with one-line glue 'rw [lemma1, lemma2]'. Two direct lemmas, neither references the other (depth 1), one line each. | verifier |
| 3 | verified | Opened code/skills/lean-proof/SKILL.md: line 33 reads 'Move sorries earlier in the file by replacing a sorry proof with references to simpler lemmas:' and line 14 reads 'by sorry is acceptable: For placeholders you're not actively working on.' Both quotes match verbatim. | verifier |
| 4 | verified | Opened code/skills/lean-proof/SKILL.md L40-L41: 'theorem lemma1 : A = B := by sorry' and 'theorem lemma2 : B = C := by sorry'. Both children end in 'by sorry', so neither leaf is proved; the instance is a teaching skeleton. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Opened code/skills/lean-proof/SKILL.md at pinned commit. Parent L42-43 is 'theorem main_theorem : A = C := by' / '  rw [lemma1, lemma2]'; child lemma1 L40 'theorem lemma1 : A = B := by sorry'; child lemma2 L41 'theorem lemma2 : B = C := by sorry'. The parent proof references exactly lemma1 then lemma2 and nothing else, and rw [lemma1, lemma2] rewrites A->B then B->C, closing A = C by rfl once both leaves are filled, so children and closing method match the code. Shape numbers are right: direct_lemmas=2, depth=1 (neither leaf uses the other), glue_lines=1 (the single rw line), child_lines=[1,1]. Children are unproved (by sorry), which the entry states honestly as a teaching skeleton. | reviewer-correctness |
| generality | accept | Move is stated generically: goal_shape covers 'an equality A = C (or any rewrite-friendly relation) that factors through an intermediate B', not just the A=B=C skeleton, and also_known_as gives the general names. avoid_when lists three specific, honest failure modes (B does not reduce either side; helpers need hypotheses/local context a bare rw cannot supply; already a single rw step), and consequences are specific and correct (matching intermediate B and orientation, typecheck-while-sorry, incomplete by design per line 93). It says what makes the lemmas good leaves for a bounded prover: self-contained statements with no hypotheses/local context, smaller than the parent, independent siblings (depth 1), each closing on its own, so the parent closes the moment both are filled. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note all consistent and traceable. Commit 7d3da0282e7b724b07620e45cf212f2e05e19334 is identical across entry.json, sources/leanprover-skills/source.json, SOURCE.md, and every permalink; blob URLs use the correct path skills/lean-proof/SKILL.md with correct #L anchors (verified L29,33,37,40,41,42-43 against the copied file). Licence Apache-2.0 agrees in entry.json, source.json, SOURCE.md, and the copied upstream-LICENSE (Apache License 2.0). Copied code byte-identical: sha256 362c42dd... matches the entry's recorded sha256, and check_provenance.py passes. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover/skills at commit `7d3da0282e7b724b07620e45cf212f2e05e19334`, under `Apache-2.0`; see the [source note](../../sources/leanprover-skills/SOURCE.md) for the licence text and attribution.
