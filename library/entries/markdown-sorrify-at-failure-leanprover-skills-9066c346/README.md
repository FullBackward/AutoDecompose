# Sorrify the easy branches and work the hardest case first

| | |
|---|---|
| Kind | skill |
| Move | sorrify-at-failure |
| Language | markdown |
| Status | draft |
| Source | [leanprover-skills](../../sources/leanprover-skills/SOURCE.md) at `7d3da0282e7b` |
| Licence | `Apache-2.0` |

## Intent

Order a multi-case proof so that the recognisably hardest branch is attempted
first while the easy branches are stubbed with `sorry`, so that if the hard
case cannot be proved, the effort already spent on the easy cases is not
wasted.

## The decomposition

### skill-text `work-hardest-case-first`: [`skills/lean-proof/SKILL.md` lines 46-48](https://github.com/leanprover/skills/blob/7d3da0282e7b724b07620e45cf212f2e05e19334/skills/lean-proof/SKILL.md#L46-L48) ([local copy](code/skills/lean-proof/SKILL.md))

```markdown
### Within a Proof

When a proof has multiple cases, `sorry` the easy cases and work on the hardest one first. If the hard case fails, effort on easy cases is wasted.
```

### skeleton `match-with-sorries`: [`skills/lean-proof/SKILL.md` lines 50-55](https://github.com/leanprover/skills/blob/7d3da0282e7b724b07620e45cf212f2e05e19334/skills/lean-proof/SKILL.md#L50-L55) ([local copy](code/skills/lean-proof/SKILL.md))

````markdown
```lean
match n with
| 0 => sorry -- fill in later
| 1 => sorry -- fill in later
| n + 2 => -- WORK ON THIS FIRST
```
````

How the parts fit. The skill-text (lines 46-48) states the rule and its
reason: in a multi-case proof, put `sorry` on the easy cases and work the
hardest case first, because if the hard case fails the effort on the easy
cases is wasted. The skeleton (lines 50-55) shows the rule concretely as a
`match n with` with three branches: the two base cases `0` and `1` carry
`sorry` (deferred, with the comment `-- fill in later`), and the recursive
case `n + 2` carries no `sorry`, only the comment `-- WORK ON THIS FIRST`
marking it as the branch to attempt now. Nothing is closed here — the move
schedules the branches, it does not prove any of them; the deferred `sorry`s
and the open hard case are what remains to be filled after the ordering
decision.

## Why it is good

1. The example makes the ordering visible in code: exactly the two base cases
   carry `sorry` (`| 0 => sorry -- fill in later`, line 52; `| 1 => sorry --
   fill in later`, line 53) while the recursive case `| n + 2 => -- WORK ON
   THIS FIRST` (line 54) carries no `sorry`, only the comment (`check`).
2. The skill states the rule and its reason in its own words: "`sorry` the
   easy cases and work on the hardest one first. If the hard case fails,
   effort on easy cases is wasted." (line 48) (`author-statement`).
3. Two of the three branches are sorrified and one is left open; the two
   sorrified branches are the base cases `0` and `1`, and the single open
   branch is the recursive case `n + 2` (`measurement`, a `sorry` count over
   lines 50-55).
4. The file's own Verification rule bounds the move: "Never declare a proof
   complete while `sorry` placeholders or error diagnostics remain." (line 93)
   (`author-statement`).

In my opinion the transferable part is the *reasoning*, not the `sorry`
placement: the ordering is a fail-fast heuristic, front-loading the branch
most likely to kill the proof so that infeasibility is discovered before the
cheap work is done. That reasoning is not itself one of the survey F §10
rules — §10 rule 2 covers sorrifying a failing block mechanically, while this
rule sorrifies the *easy* branches pre-emptively and adds an ordering
principle §10 does not yet state.

## When to use it, and when not

Use it when one branch is clearly harder than the rest (typically a
recursive/structural case such as `n + 2` set against base cases `0`, `1`)
and you want to discover as early as possible whether the whole proof is
feasible. Do not use it when the branches are about equally hard, or all
easy — the ordering then saves nothing; when the "hard" branch is not in fact
the risk, e.g. the easy branches carry the only subtle content; or when you
already know the proof works and simply need every branch filled, since the
file's Verification rule forbids leaving any `sorry` in a completed proof.

## Consequences

Leaves `sorry` holes on the easy branches that must be filled later; Lean
accepts `sorry` as an axiom, so the theorem type-checks while those branches
are open. The `match` must still be exhaustive over `n` (the base cases `0`,
`1` plus the recursive case `n + 2` cover all naturals). The move is a
scheduling heuristic, not a reduction: it makes no branch smaller, it only
front-loads the one most likely to kill the proof. The failure mode is
misjudging which branch is hard — that defers the risky work instead of
surfacing it — and leaving the deferred `sorry`s in, which the file's own
Verification rule (line 93) forbids.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | not-run | Entry's only copied file is skills/lean-proof/SKILL.md, a markdown skill file. The source leanprover/skills is not a Lean project (no lakefile.lean/lean-toolchain; its .claude/CLAUDE.md states 'There is nothing to build'). CI (.github/workflows/check-validation.yml -> scripts/check-validation) only checks that test results exist and are judged satisfactory/current; it does not compile or build the markdown file. | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 7d3da0282e7b724b07620e45cf212f2e05e19334 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read copied file code/skills/lean-proof/SKILL.md: line 52 '| 0 => sorry -- fill in later', line 53 '| 1 => sorry -- fill in later', line 54 '| n + 2 => -- WORK ON THIS FIRST' (no sorry). Exactly matches the claim. | verifier |
| 2 | verified | Copied file line 48 reads verbatim: 'When a proof has multiple cases, sorry the easy cases and work on the hardest one first. If the hard case fails, effort on easy cases is wasted.' Matches the quoted author-statement. | verifier |
| 3 | verified | Counted sorry tokens over lines 50-55 of the copied file: exactly 2 (line 52 '| 0 => sorry', line 53 '| 1 => sorry') across 3 branches; third branch '| n + 2' (line 54) has none. Base cases 0 and 1 sorrified, recursive n+2 open. Matches. | verifier |
| 4 | verified | Copied file line 93 reads verbatim: 'Never declare a proof complete while sorry placeholders or error diagnostics remain.' Matches the quoted author-statement. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Local copy matches: rule text at line 48, example match lines 50-55 with | 0 => sorry (52), | 1 => sorry (53), | n + 2 => -- WORK ON THIS FIRST (54, no sorry), Verification rule line 93. Children and closing methods (two base cases closed by deferred sorry, recursive case left open) match the code. Entry honestly states nothing closes (scheduling heuristic, deferred sorries must be filled); claims 1-4 all verified against the copied file. | reviewer-correctness |
| generality | accept | Move stated beyond the example: intent and applicability.goal_shape lift it from the specific match n with 0/1/n+2 to 'a match or case split with several branches, exactly one recognisably the hard case', and also_known_as names the transferable principle (hardest-case-first, risk-first ordering, fail-fast). avoid_when is honest and specific (equally-hard/all-easy branches save nothing; the 'hard' branch may not be the real risk; already-known-proof still must not leave sorry), and consequences are honest (sorries remain as axioms to be filled, match still exhaustive, scheduling heuristic not a reduction, failure mode is misjudging which branch is hard). | reviewer-generality |
| provenance-licence | accept | check_provenance passes (SKILL.md byte-identical at 7d3da0282e7b724b07620e45cf212f2e05e19334); local sha256 362c42dd... matches entry.json; permalinks (files + sites L46-L48, L50-L55) use the pinned commit and match the copied lines; licence Apache-2.0 recorded consistently in entry.json, README, SOURCE.md, source.json and confirmed by upstream LICENSE at the commit; source note consistent. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover/skills at commit `7d3da0282e7b724b07620e45cf212f2e05e19334`, under `Apache-2.0`; see the [source note](../../sources/leanprover-skills/SOURCE.md) for the licence text and attribution.
