# The /lean4:refactor workflow: strategy-level proof simplification behind a per-batch diagnostic gate

| | |
|---|---|
| Kind | skill |
| Move | workflow |
| Language | markdown |
| Status | draft |
| Source | [lean4-skills](../../sources/lean4-skills/SOURCE.md) at `3f913c66251b` |
| Licence | `MIT` |

## Intent

Prescribe a seven-step process for strategy-level proof simplification — audit
for long proofs and thin definition APIs, search mathlib, plan with measured
impact, approve per batch, apply each edit behind a diagnostic gate that
reverts on any new diagnostic or sorry increase, verify through `lake lean` /
`lake build`, then report — while never changing theorem statements or
introducing axioms, and with a fixed helper-scope rule (local `have` for single
use, `private theorem` for reuse within a file).

## The decomposition

### skill-text `actions`: [`plugins/lean4/commands/refactor.md` lines 58-75](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/commands/refactor.md#L58-L75) ([local copy](code/plugins/lean4/commands/refactor.md))

````markdown
## Actions

1. **Audit** — Read target proofs, identify repeated patterns, long proofs (>30 lines), hand-rolled arguments, case splits replaceable by `congr`/`EqOn`/`EventuallyEq`, thin definition APIs
2. **Search** — For each opportunity, search mathlib via [LSP-first protocol](../skills/lean4/references/cycle-engine.md#lsp-first-protocol). `--search=quick`: up to 2 LSP queries per opportunity. `--search=full`: up to 5 queries with module exploration.
3. **Plan** — Present findings with estimated impact:
   ```markdown
   ## Refactor Plan — File.lean
   ### Strategy Improvements
   1. [proof] (line N): [current] → Use [mathlib lemma] (saves ~N lines)
   ### Helper Extraction
   1. [pattern] — Nx (lines ...) → Extract `helper_name`
   ### Estimated Impact
   - Lines before: N → after: ~N | Helpers: N | New mathlib lemmas: N
   ```
4. **Approval** — Ask before each batch (`--dry-run` stops here). A batch groups opportunities within a single proof or closely related proofs. Prompt: `Apply batch N (M changes)? [yes / skip / stop]` — yes applies, skip moves to next batch, stop ends the session.
5. **Apply** — Edit files, verify with `lean_diagnostic_messages` after each batch; revert batch on any new diagnostic or sorry increase
6. **Verify** — `lake lean <file>` file gate (run from project root; it builds the file's imports first, so a cross-file batch cannot false-fail against a stale `.olean` — see [File Gate Scope](../skills/lean4/references/cycle-engine.md#file-gate-scope)); `lake build` project gate if multi-file. If final gate fails, revert all batches applied in this session.
7. **Report** — Summarize changes applied, helpers extracted, line count delta
````

### skill-text `helper-scope`: [`plugins/lean4/commands/refactor.md` lines 79-79](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/commands/refactor.md#L79-L79) ([local copy](code/plugins/lean4/commands/refactor.md))

```markdown
**Helper scope defaults:** Single use inside one proof → local (`have` / local helper). Reused within one file → `private theorem`. Public/non-private → only with explicit user approval or clear existing API reason.
```

How the parts fit. The seven actions form a pipeline in which each step's
output is the next step's input. *Audit* (read-only) scans the target for
repeated patterns, long proofs, hand-rolled arguments, and thin definition
APIs; *Search* runs a bounded number of LSP queries against mathlib per
opportunity (2 quick, 5 full); *Plan* turns the findings into an `Estimated
Impact` block that states the line-count reduction *before* any edit; *Approval*
stops the run unless the user answers `yes` per batch; *Apply* makes the edits
and closes each batch with a diagnostic gate — revert on any new
`lean_diagnostic_messages` error or any sorry increase; *Verify* closes the
session with a `lake lean <file>` (or `lake build`) gate, reverting all batches
if it fails; *Report* states the line-count delta. The helper-extraction
sub-step, which appears in Audit as "repeated patterns" and in Plan as "Helper
Extraction", is closed by the `helper-scope` rule: a helper is lifted to a
standalone `private theorem` only when it is reused within the file, stays a
local `have` when used once, and goes public only with approval.

## Why it is good

1. The `## Actions` section specifies seven ordered steps, and the Apply step
   (5) makes each batch self-checking: after editing, verify with
   `lean_diagnostic_messages` and "revert batch on any new diagnostic or sorry
   increase" (lines 58-75). Evidence kind: check.
2. Verification is two-tier — `lake lean <file>` builds the file's imports
   first (so a cross-file batch cannot false-fail against a stale `.olean`),
   `lake build` is the project gate for multi-file changes, and a final-gate
   failure reverts the whole session (line 74). Evidence kind: check.
3. The command names its own invariant in prose: "Mutating command: Edits
   files with user approval. Does not change theorem statements, introduce
   axioms, or create commits." (line 11). Evidence kind: author-statement.
4. The helper-scope defaults fix the extraction decision by reuse count:
   single use → local `have`, reuse within one file → `private theorem`,
   public/non-private → only with explicit approval (line 79). Evidence kind:
   check.

In my opinion the detail worth copying is the *per-batch* diagnostic gate plus
the *session-level* `lake lean` gate: a strategy change is never trusted on
the strength of "it looks simpler"; it must keep compiling with no new
diagnostics and no new sorries, or it is reverted, and a stale-`.olean`
false-fail is excluded by building imports first.

## When to use it, and when not

Use it when the proofs already compile (no sorries, no build errors) and the
change is statement-preserving simplification: a mathlib lemma or a
`congr`/`EqOn`/`EventuallyEq` rewrite is likely to replace hand-rolled
reasoning, a long proof (>30 lines) has a shorter argument, or a helper is
reused within a file and should be lifted to a `private theorem`. Avoid it when
the target has sorries or build errors (the command refuses), when the change
would alter a theorem statement or needs axiom/assumption hygiene (those are
reported, or sent to the axiom-eliminator, not applied here), or when the
cleanup is purely local tactic-level — that is `/lean4:golf`, which escalates
to this command only for multi-file or strategy-level changes (line 13).

## Consequences

Every edit must pass two gates before it stands: a per-batch
`lean_diagnostic_messages` check with no new diagnostic and no sorry increase,
and a final `lake lean` (single file) or `lake build` (multi-file) gate; a
failure reverts the batch, and a final-gate failure reverts the whole session.
Helper extraction carries a scoping obligation: single use stays a local
`have`, reuse within a file becomes a `private theorem`, and public visibility
needs explicit approval. The command never changes theorem statements,
introduces axioms, or creates commits, so statement-level changes are out of
scope and are reported rather than applied. A batch that reduces line count but
breaks a proof is caught only by the sorry/diagnostic gate, not by the
line-count delta.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | not-run | plugins/lean4/commands/refactor.md is a markdown skill file (kind skill, language markdown), not Lean/Rocq source; no prover toolchain compiles it and no CI builds a markdown command file | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 3f913c66251b8712bb58e6ce83a453fa96e3f94f | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Checked the byte-identical local copy code/plugins/lean4/commands/refactor.md (provenance pass) and the raw view at the pinned commit: line 58 is '## Actions', lines 60-75 are seven numbered steps Audit/Search/Plan/Approval/Apply/Verify/Report, and step 5 (line 73) reads 'Edit files, verify with lean_diagnostic_messages after each batch; revert batch on any new diagnostic or sorry increase' | verifier |
| 2 | verified | Line 74 reads '6. **Verify** — lake lean <file> file gate (run from project root; it builds the file's imports first, so a cross-file batch cannot false-fail against a stale .olean ...); lake build project gate if multi-file. If final gate fails, revert all batches applied in this session.' Matches all three parts | verifier |
| 3 | verified | Line 11 reads '**Mutating command:** Edits files with user approval. Does not change theorem statements, introduce axioms, or create commits.' Quote matches | verifier |
| 4 | verified | Line 79 reads '**Helper scope defaults:** Single use inside one proof -> local (have / local helper). Reused within one file -> private theorem. Public/non-private -> only with explicit user approval or clear existing API reason.' Matches all three tiers | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Provenance passes (1 file byte-identical at 3f913c6). All four claims verified against copied refactor.md: seven ordered steps at lines 60-75 with Apply (step 5, line 73) requiring lean_diagnostic_messages and revert on new diagnostic/sorry; two-tier verify at line 74 (lake lean builds imports first, lake build if multi-file, final-gate failure reverts session); mutating-command invariant at line 11; helper-scope defaults at line 79. All seven children (audit..report) statements and closed_by match lines 60-75; workflow closes via the per-batch diagnostic gate and the session-level lake lean/lake build gate. | reviewer-correctness |
| generality | accept | The move is stated as a transferable process, not just 'run /lean4:refactor on Lean files': the README 'How the parts fit' abstracts the seven steps into a pipeline (each step's output feeds the next), and 'Why it is good' names the copyable core (per-batch diagnostic gate + session-level build gate that builds imports first, never trusting 'it looks simpler'), labelled as opinion as the protocol requires. 'When not to use' is honest and specific and matches the source: refuses on sorries/build errors (refactor.md lines 49-56), statement/axiom changes are reported or routed to the axiom-eliminator rather than applied (lines 11,13), and purely local tactic-level cleanup is /lean4:golf's job (lines 9,13). Consequences are honest and specific, including self-articulated failure modes: stale-.olean false-fail excluded by building imports first, and a line-count-reducing edit that breaks a proof is caught only by the diagnostic/sorry gate, not the line-count delta. No objection. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are all consistent and traceable. check_provenance.py passes: 1 file byte-identical at 3f913c66251b8712bb58e6ce83a453fa96e3f94f (sha256 13e6753636a819cd0da1371b0283ffa0b9ad1afe417d37d213db7c3a2e31b32d, 5397 bytes match the local copy). The commit hash appears identically in entry.json source.commit, files[0].permalink, all site/claim/known_use permalinks, and sources/lean4-skills/source.json+SOURCE.md. Line anchors are correct against the byte-identical local copy: L58='## Actions', L60-L75 hold the seven steps, L73=Apply, L74=Verify, L11=mutating-command invariant, L79=helper-scope. Licence 'MIT' is recorded consistently in entry.json, README, source.json, and SOURCE.md, and matches upstream-LICENSE (MIT text copied from the pinned commit's LICENSE). Source note SOURCE.md exists with attribution and licence-text link. Minor out-of-lens note: known_uses points to a self-reference (same file L13) rather than an independent use. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/cameronfreer/lean4-skills at commit `3f913c66251b8712bb58e6ce83a453fa96e3f94f`, under `MIT`; see the [source note](../../sources/lean4-skills/SOURCE.md) for the licence text and attribution.
