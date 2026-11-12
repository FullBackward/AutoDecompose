# Lifting an embedded have into a private lemma (strict-monotone bound)

| | |
|---|---|
| Kind | instance |
| Move | extract-have |
| Language | markdown |
| Status | draft |
| Source | [lean4-skills](../../sources/lean4-skills/SOURCE.md) at `3f913c66251b` |
| Licence | `MIT` |

## Intent

Take the `have hk_bound` embedded in a long proof, promote its surrounding
context (`m'`, `k`, `hk_mono`) into explicit parameters, and generalise the
specific bound `k i ≤ k ⟨m', Nat.lt_succ_self m'⟩` to `k i ≤ k last`, so the
main proof closes its strict bound `k i < n` by `omega` from a top-level
`private lemma` instead of an inline calculation. The embedded code is Lean,
shown inside this markdown source file.

## The decomposition

### parent `hk_bound`: [`plugins/lean4/skills/lean4/references/proof-refactoring.md` lines 309-317](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/proof-refactoring.md#L309-L317) ([local copy](code/plugins/lean4/skills/lean4/references/proof-refactoring.md))

````markdown
```lean
have hk_bound : ∀ i : Fin (m' + 1), k i < n := by
  intro i
  simp only [n]
  have : k i ≤ k ⟨m', Nat.lt_succ_self m'⟩ := by
    apply StrictMono.monotone hk_mono
    exact Fin.le_last i
  omega
```
````

### child `strictMono_all_lt_succ_last`: [`plugins/lean4/skills/lean4/references/proof-refactoring.md` lines 320-328](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/proof-refactoring.md#L320-L328) ([local copy](code/plugins/lean4/skills/lean4/references/proof-refactoring.md))

````markdown
```lean
/-- Strictly monotone functions satisfy k(i) ≤ k(last) for all i -/
private lemma strictMono_all_lt_succ_last {m : ℕ} (k : Fin m → ℕ)
    (hk : StrictMono k) (i : Fin m) (last : Fin m)
    (h_last : ∀ j, j ≤ last) :
    k i ≤ k last := by
  apply StrictMono.monotone hk
  exact h_last i
```
````

How the parts fit. The parent is the `have` as it lived inside the main proof:
an outer obligation `hk_bound : ∀ i : Fin (m' + 1), k i < n`, discharged by
`intro i`, `simp only [n]`, an inner `have : k i ≤ k ⟨m', Nat.lt_succ_self
m'⟩`, then `omega`. The child is the same mathematical content lifted to a
top-level `private lemma`, with the proof body copied and the context promoted
to parameters. The one real change is generalisation: the specific last index
`⟨m', Nat.lt_succ_self m'⟩` becomes `last : Fin m`, and the fact `Fin.le_last i`
that supplied `i ≤ last` becomes the explicit hypothesis `h_last : ∀ j, j ≤
last`. The outer `hk_bound` is then closed by `omega` from the helper, so the
parent's strict bound and the child's non-strict bound are two statements of
the same monotonicity fact, the child being the reusable one. Both versions
close: the parent by `omega` (line 316), the child by `apply StrictMono.monotone
hk; exact h_last i` (lines 326-327).

## Why it is good

1. The embedded `have` closes by `omega` (line 316) after an inner
   `have : k i ≤ k ⟨m', Nat.lt_succ_self m'⟩` closed by `apply
   StrictMono.monotone hk_mono; exact Fin.le_last i` (lines 313-315), with
   `simp only [n]` discharging the `n` of the outer goal. `check`,
   [lines 310-316](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/proof-refactoring.md#L310-L316).
2. The extracted `private lemma` closes by the same two-step argument `apply
   StrictMono.monotone hk; exact h_last i` (lines 326-327), with the specific
   last index and its witness generalised to `last : Fin m` and
   `h_last : ∀ j, j ≤ last`. `check`,
   [lines 321-327](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/proof-refactoring.md#L321-L327).
3. The authors state the lemma's meaning in its docstring — "Strictly
   monotone functions satisfy k(i) ≤ k(last) for all i" (line 321) — and the
   point of the extraction — "Result: Main proof now just calls helper, much
   clearer." (line 330). `author-statement`,
   [line 321](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/proof-refactoring.md#L321),
   [line 330](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/proof-refactoring.md#L330).
4. The same file states the recipe this example follows — "Copy have proof to
   new lemma; Identify required parameters; Replace original with `have h :=
   helper args`" (lines 264-266) — and the generalisation step is its own rule,
   "Generic is better (Pattern 2.1): Remove proof-specific constraints" (line
   39). `author-statement`,
   [lines 264-266](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/proof-refactoring.md#L264-L266),
   [line 39](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/proof-refactoring.md#L39).

In my opinion the detail worth copying is the generalisation, not the mere
copying of the proof body: the helper stays useful precisely because the
proof-specific `⟨m', Nat.lt_succ_self m'⟩` and `Fin.le_last i` were replaced by
a parameter `last` and a hypothesis `h_last` the caller controls.

## When to use it, and when not

Use it when an embedded fact has independent mathematical content and can be
re-stated with the surrounding context as explicit parameters; when the fact is
reusable elsewhere, or when lifting it makes the main proof shorter and clearer
(the file's own triggers: a large preliminary calculation, or a bound whose only
proof-specific part is the choice of a last index). Avoid it when the fact would
need a long parameter list (the file warns against 10+ / 15+ parameters), when
the statement depends on definitional `let` bindings that will not line up after
extraction (Pattern 2.3), when the `have` is short and linear with no
independent meaning, or when the extraction would obscure the main flow rather
than clarify it.

## Consequences

The extracted lemma must carry the whole context as parameters: `m'` in
`Fin (m' + 1)` is re-typed as the implicit `{m : ℕ}`, `k` and `hk_mono` become
`k` and `hk : StrictMono k`, and the specific last index
`⟨m', Nat.lt_succ_self m'⟩` is generalised to `last : Fin m` with the explicit
hypothesis `h_last : ∀ j, j ≤ last` (previously supplied for free by
`Fin.le_last i`). The outer `have hk_bound` is then closed by `omega` from the
helper, so the caller must still supply the `last`/`h_last` pair and finish the
strict bound. A helper left too specific (still naming `n` and `m'`) would not
be reusable; one made too general gains a hypothesis the caller must discharge.
The file's Pattern 5.1 requires recompiling after each such extraction, since a
parameter mismatch or a dropped hypothesis is caught only by the compiler.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | not-run | Source file is Markdown documentation (plugins/lean4/skills/lean4/references/proof-refactoring.md), not Lean source; no toolchain or CI workflow builds it. Checked .github/workflows/lint.yml (ruff/mypy/shellcheck/lint_docs, no md build) and lean-integration.yml (runs Lean integration/reference-snippet scripts, no md compilation). | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 3f913c66251b8712bb58e6ce83a453fa96e3f94f | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Copied code lines 310-316: have hk_bound closes with omega (line 316); inner have (line 313) closed by apply StrictMono.monotone hk_mono (314) / exact Fin.le_last i (315); simp only [n] at line 312. | verifier |
| 2 | verified | Copied code lines 321-327: private lemma strictMono_all_lt_succ_last closes with apply StrictMono.monotone hk / exact h_last i (326-327); params last : Fin m (323) and h_last : ∀ j, j ≤ last (324) replace the specific index and Fin.le_last witness. | verifier |
| 3 | verified | Copied code: line 321 docstring reads 'Strictly monotone functions satisfy k(i) ≤ k(last) for all i'; line 330 reads 'Result: Main proof now just calls helper, much clearer.' | verifier |
| 4 | verified | Copied code: lines 264-266 'Copy have proof to new lemma / Identify required parameters / Replace original with have h := helper args'; line 39 'Generic is better (Pattern 2.1): Remove proof-specific constraints'. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Opened the copied code file at code/plugins/lean4/skills/lean4/references/proof-refactoring.md. Parent site lines 309-317 hold the fence-to-fence before block: have hk_bound (310) with intro i (311), simp only [n] (312), inner have k i <= k <m', Nat.lt_succ_self m'> (313) closed by apply StrictMono.monotone hk_mono (314) / exact Fin.le_last i (315), then omega (316). Child site lines 320-328 hold the fence-to-fence extracted lemma: docstring (321), private lemma strictMono_all_lt_succ_last (322) with params {m} k hk i last h_last, body apply StrictMono.monotone hk (326) / exact h_last i (327). The generalisation is faithful: Fin.le_last i -> explicit h_last : forall j, j <= last, and the specific last index becomes parameter last. Both close: parent by omega, child by exact h_last i (h_last i : i <= last, then monotone gives k i <= k last). Line 330 is Result: Main proof now just calls helper; recipe at 264-266; Generic is better at 39. Decomposition matches the entry, child and closing method match the code, and it closes. | reviewer-correctness |
| generality | accept | Move is stated generally: applicability.use_when/avoid_when and README 'When to use/not' restate extract-have as lifting any embedded have with independent content into a parameterised lemma, citing the file's own recipe (lines 264-266) and Pattern 2.1 'Generic is better' (line 39). 'When not to use' items are honest and specific, each grounded in the copied source: 10+/15+ parameter warning (lines 184, 556, 853), definitional let bindings (Pattern 2.3, lines 569-581), short/linear have (lines 63-64), extraction obscuring flow (line 99). Consequences accurately describe promoting m'/k/hk_mono to parameters and the last/h_last obligation, and the too-specific vs too-general trade-off is honest. Minor nits only: entry.json avoid_when parenthetical '(Pattern 2.3, measure theory)' conflates 2.3 (let bindings) with 3.4 (measure theory), and use_when cites 'large preliminary calculation' though this 7-line have is not large; neither undermines the move's generality. | reviewer-generality |
| provenance-licence | accept | Provenance check passes (1 file byte-identical at 3f913c66251b8712bb58e6ce83a453fa96e3f94f). Commit is consistent across entry.json, source.json and SOURCE.md. Licence is 'MIT' in entry.json/source.json/SOURCE.md and the copied upstream-LICENSE is MIT License text (copyright 2025 Lean 4 Theorem Proving Skill Contributors). Permalinks all use the same full commit and correct path; site line ranges (309-317 parent, 320-328 child) and all claim line anchors (310-316, 321-327, 321+330, 264-266+39) match the copied proof-refactoring.md exactly. Source note links LICENSE at the pinned commit and gives attribution. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/cameronfreer/lean4-skills at commit `3f913c66251b8712bb58e6ce83a453fa96e3f94f`, under `MIT`; see the [source note](../../sources/lean4-skills/SOURCE.md) for the licence text and attribution.
