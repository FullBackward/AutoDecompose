# Blueprint-node split of a stalled lemma into three dependency-chained sub-lemmas

| | |
|---|---|
| Kind | instance |
| Move | blueprint-node |
| Language | markdown |
| Status | draft |
| Source | [numina-lean-agent](../../sources/numina-lean-agent/SOURCE.md) at `1c9af8a52e71` |
| Licence | `MIT` |
| Licence recorded | 2026-11-14T22:40:52Z |

## Intent

Replace one stalled lemma (`lem:complex`, partial 45/50) by three named
blueprint nodes written for it, chained `step1 → step2 → step3 → lem:complex`
by their `uses` fields, each with a reset attempt budget, so work is scheduled
from the leaf and the parent's glue is the single `uses` edge to the last
child.

## The decomposition

### parent `lem:complex`: [`prompts/docs/prompts/coordinator.md` lines 355-357](https://github.com/project-numina/numina-lean-agent/blob/1c9af8a52e715f22fede766425ba3d3b95526132/prompts/docs/prompts/coordinator.md#L355-L357) ([local copy](code/prompts/docs/prompts/coordinator.md))

```markdown
# lemma lem:complex
- uses: [[lem:complex_step3]]
- status: ❌ todo (0/50)  # reset
```

### child `lem:complex_step1`: [`prompts/docs/prompts/coordinator.md` lines 344-345](https://github.com/project-numina/numina-lean-agent/blob/1c9af8a52e715f22fede766425ba3d3b95526132/prompts/docs/prompts/coordinator.md#L344-L345) ([local copy](code/prompts/docs/prompts/coordinator.md))

```markdown
# lemma lem:complex_step1
- status: ❌ todo (0/20)
```

### child `lem:complex_step2`: [`prompts/docs/prompts/coordinator.md` lines 347-349](https://github.com/project-numina/numina-lean-agent/blob/1c9af8a52e715f22fede766425ba3d3b95526132/prompts/docs/prompts/coordinator.md#L347-L349) ([local copy](code/prompts/docs/prompts/coordinator.md))

```markdown
# lemma lem:complex_step2
- uses: [[lem:complex_step1]]
- status: ❌ todo (0/20)
```

### child `lem:complex_step3`: [`prompts/docs/prompts/coordinator.md` lines 351-353](https://github.com/project-numina/numina-lean-agent/blob/1c9af8a52e715f22fede766425ba3d3b95526132/prompts/docs/prompts/coordinator.md#L351-L353) ([local copy](code/prompts/docs/prompts/coordinator.md))

```markdown
# lemma lem:complex_step3
- uses: [[lem:complex_step2]]
- status: ❌ todo (0/20)
```

### context `lem:complex-before`: [`prompts/docs/prompts/coordinator.md` lines 338-339](https://github.com/project-numina/numina-lean-agent/blob/1c9af8a52e715f22fede766425ba3d3b95526132/prompts/docs/prompts/coordinator.md#L338-L339) ([local copy](code/prompts/docs/prompts/coordinator.md))

```markdown
# lemma lem:complex
- status: 🔄 partial (45/50)
```

### context `your-action`: [`prompts/docs/prompts/coordinator.md` lines 360-365](https://github.com/project-numina/numina-lean-agent/blob/1c9af8a52e715f22fede766425ba3d3b95526132/prompts/docs/prompts/coordinator.md#L360-L365) ([local copy](code/prompts/docs/prompts/coordinator.md))

```markdown
**Your action**:
1. Refresh blueprint understanding
2. Select [lem:complex_step1] (no dependencies)
3. Spawn sketch + proof agents for step1
4. When step1 done, move to step2, then step3
5. Finally prove original [lem:complex] using step3
```

**How the parts fit.** Before the split, the blueprint has one stalled node,
`# lemma lem:complex` with `status: 🔄 partial (45/50)` (the `lem:complex-before`
excerpt). The Blueprint Agent replaces it with a published dependency graph of
four nodes, stated before they are proved:

```
lem:complex ──uses──▶ lem:complex_step3 ──uses──▶ lem:complex_step2 ──uses──▶ lem:complex_step1
```

The parent's glue is exactly one line: `- uses: [[lem:complex_step3]]`. Each
intermediate node carries its own `uses` edge (`step2` names `step1`,
`step3` names `step2`) and its own attempt budget, reset to `0/20`; the parent
is reset to `0/50`. The "Your action" list derives the work order from the
graph: because `step1` has no dependencies it is selected first, then `step2`,
then `step3`, and only then is the original `lem:complex` re-proved *from*
`step3`.

Why each child is a good leaf, structurally: `lem:complex_step1` is a leaf
because its node has no `uses` field, so its proof must close from nothing but
its own statement (and it is the one node that can start immediately).
`lem:complex_step2` closes from the named sibling `lem:complex_step1`, and
`lem:complex_step3` from the named sibling `lem:complex_step2`; the parent then
closes from `lem:complex_step3`. The statements are schematic — the protocol
does not spell out what each step asserts — so "closes on its own / from named
siblings" here means the *dependency structure* the coordinator will honour,
not a recorded proof.

## Why it is good

1. The parent site cites `lem:complex_step3` (lines 355-357). (*check*,
   `cites(parent, lem:complex_step3)`.)
2. The `lem:complex_step2` site cites `lem:complex_step1` (lines 347-349).
   (*check*, `cites(lem:complex_step2, lem:complex_step1)`.)
3. The `lem:complex_step3` site cites `lem:complex_step2` (lines 351-353).
   (*check*, `cites(lem:complex_step3, lem:complex_step2)`.)
4. The split is a depth-3 chain of three named nodes below the parent:
   `lem:complex_step1` has no `uses` field (a leaf), `lem:complex_step2` uses
   `lem:complex_step1` (line 348), `lem:complex_step3` uses `lem:complex_step2`
   (line 352), and the parent uses `lem:complex_step3` (line 356).
   (*measurement*, read of the four `uses` fields, lines 344-357.)
5. The coordinator states its own rule for deriving the order from the graph:
   "2. Select [lem:complex_step1] (no dependencies)" and "5. Finally prove
   original [lem:complex] using step3" (lines 362 and 365).
   (*author-statement*.)

In my opinion the detail worth copying is the reset of the budget *together
with* the split: a stalled node at 45/50 is not retried, it is replaced by
three nodes each starting at 0/20 (and the parent reset to 0/50), so the
coordinator never wastes the rest of a near-exhausted budget on a lemma it has
just decided is too large.

## When to use it, and when not

Use it when a blueprint node's proof is partial or its attempts are exhausted
and the proof has three or more distinct steps — the coordinator's "Complex"
path (lines 134-138) is exactly this trigger, and the Blueprint Agent then
splits the lemma into a `uses` chain. Use it when the steps are genuinely
ordered, so the chain records a real dependency and lets the coordinator
schedule leaves-first.

Avoid it when the lemma is small enough for a single Proof Agent (the "Simple"
path, lines 124-127); when the steps are independent of one another, in which
case they should be siblings under the parent rather than a chain; or when the
split would deepen the dependency graph past the project's depth cap, since a
long chain serialises work that could be parallel.

## Consequences

The split creates three new nodes, each still `todo` with a fresh 0/20 budget,
so every child's proof remains to be done and the parent's correctness now
rests entirely on the chain holding. Obligations: every `uses` edge must stay
consistent — a node is eligible only when all its dependencies are done (the
selection rule at line 106) — and the parent's `uses` field must name exactly
the last child. Failure modes: a child that is not self-contained cannot later
close from its own statement; a broken `uses` edge schedules a node before its
dependency is proved; and because the parent is re-proved only from `step3`, a
wrong step propagates to the theorem undetected.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| sorry-scan | not-run | no Lean, Rocq or Isabelle file among the copied files | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, lem:complex_step3) -> cites: lem:complex_step3 occurs at prompts/docs/prompts/coordinator.md:356 | check_claims.py |
| 2 | verified | cites(lem:complex_step2, lem:complex_step1) -> cites: lem:complex_step1 occurs at prompts/docs/prompts/coordinator.md:348 | check_claims.py |
| 3 | verified | cites(lem:complex_step3, lem:complex_step2) -> cites: lem:complex_step2 occurs at prompts/docs/prompts/coordinator.md:352 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/project-numina/numina-lean-agent at commit `1c9af8a52e715f22fede766425ba3d3b95526132`, under `MIT`; see the [source note](../../sources/numina-lean-agent/SOURCE.md) for the licence text and attribution.
