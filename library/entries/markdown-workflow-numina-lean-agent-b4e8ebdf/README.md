# Worked split of an alternating-property lemma into three dependency-chained sub-lemmas

| | |
|---|---|
| Kind | instance |
| Move | workflow |
| Language | markdown |
| Status | draft |
| Source | [numina-lean-agent](../../sources/numina-lean-agent/SOURCE.md) at `1c9af8a52e71` |
| Licence | `LicenseRef-unknown` |

## Intent

Record the blueprint-agent workflow's worked example: one lemma whose proof is
empty is replaced by three named sub-lemmas, one per proof step returned by
Gemini, chained by `uses`. The parent's six-line proof then only cites the
chain, and each child's body is an informal Gemini proof left to be
formalised.

## The decomposition

### parent `lem:alternating_property`: [`prompts/docs/prompts/blueprint_agent.md` lines 551-568](https://github.com/project-numina/numina-lean-agent/blob/1c9af8a52e715f22fede766425ba3d3b95526132/prompts/docs/prompts/blueprint_agent.md#L551-L568) ([local copy](code/prompts/docs/prompts/blueprint_agent.md))

```markdown
# lemma lem:alternating_property

## meta
- **label**: [lem:alternating_property]
- **uses**: [[lem:alternating_property_maximal]]
- **file**: `PutnamLean/Example.lean:89`
- **status**: todo
- **attempts**: 0 / 50

## statement
If s is alternating, then f(n, s) is maximal.

## proof
Follows from [lem:alternating_property_maximal]:
Step 1 shows pattern must be respected.
Step 2 counts permutations.
Step 3 proves alternating is maximal.
QED.
```

### child `lem:alternating_property_respects_pattern`: [`prompts/docs/prompts/blueprint_agent.md` lines 500-513](https://github.com/project-numina/numina-lean-agent/blob/1c9af8a52e715f22fede766425ba3d3b95526132/prompts/docs/prompts/blueprint_agent.md#L500-L513) ([local copy](code/prompts/docs/prompts/blueprint_agent.md))

```markdown
# lemma lem:alternating_property_respects_pattern

## meta
- **label**: [lem:alternating_property_respects_pattern]
- **uses**: [[def:alternating]]
- **file**: `PutnamLean/Example.lean` (to be created)
- **status**: todo
- **attempts**: 0 / 20

## statement
Valid permutations must respect alternating pattern.

## proof
[Detailed reasoning from Gemini]
```

### child `lem:alternating_property_count`: [`prompts/docs/prompts/blueprint_agent.md` lines 517-530](https://github.com/project-numina/numina-lean-agent/blob/1c9af8a52e715f22fede766425ba3d3b95526132/prompts/docs/prompts/blueprint_agent.md#L517-L530) ([local copy](code/prompts/docs/prompts/blueprint_agent.md))

```markdown
# lemma lem:alternating_property_count

## meta
- **label**: [lem:alternating_property_count]
- **uses**: [[lem:alternating_property_respects_pattern], [def:f]]
- **file**: `PutnamLean/Example.lean` (to be created)
- **status**: todo
- **attempts**: 0 / 20

## statement
Count of valid permutations for alternating vs non-alternating.

## proof
[Detailed reasoning from Gemini]
```

### child `lem:alternating_property_maximal`: [`prompts/docs/prompts/blueprint_agent.md` lines 534-547](https://github.com/project-numina/numina-lean-agent/blob/1c9af8a52e715f22fede766425ba3d3b95526132/prompts/docs/prompts/blueprint_agent.md#L534-L547) ([local copy](code/prompts/docs/prompts/blueprint_agent.md))

```markdown
# lemma lem:alternating_property_maximal

## meta
- **label**: [lem:alternating_property_maximal]
- **uses**: [[lem:alternating_property_count]]
- **file**: `PutnamLean/Example.lean` (to be created)
- **status**: todo
- **attempts**: 0 / 20

## statement
Alternating has strictly more valid permutations.

## proof
[Detailed reasoning from Gemini]
```

### context `lem:alternating_property-before`: [`prompts/docs/prompts/blueprint_agent.md` lines 468-483](https://github.com/project-numina/numina-lean-agent/blob/1c9af8a52e715f22fede766425ba3d3b95526132/prompts/docs/prompts/blueprint_agent.md#L468-L483) ([local copy](code/prompts/docs/prompts/blueprint_agent.md))

````markdown
```markdown
# lemma lem:alternating_property

## meta
- **label**: [lem:alternating_property]
- **uses**: [[def:alternating], [def:f]]
- **file**: `PutnamLean/Example.lean:89`
- **status**: partial
- **attempts**: 48 / 50

## statement
If s is alternating, then f(n, s) is maximal.

## proof
[Empty]
```
````

### context `gemini-three-steps`: [`prompts/docs/prompts/blueprint_agent.md` lines 488-493](https://github.com/project-numina/numina-lean-agent/blob/1c9af8a52e715f22fede766425ba3d3b95526132/prompts/docs/prompts/blueprint_agent.md#L488-L493) ([local copy](code/prompts/docs/prompts/blueprint_agent.md))

````markdown
Gemini Response (summarized):
```
Step 1: Show any permutation satisfying the condition must respect alternating pattern
Step 2: Count permutations for alternating vs non-alternating
Step 3: Prove alternating has strictly more valid permutations
```
````

How the parts fit. The parent `lem:alternating_property` (lines 551-568) is
the main lemma; its `## proof` (lines 563-568) is the glue, six lines that
cite `lem:alternating_property_maximal` and restate the three steps rather
than re-prove them. The three children form one linear chain, read off their
`uses` fields:

- `lem:alternating_property` uses `lem:alternating_property_maximal` (line 555)
- `lem:alternating_property_maximal` uses `lem:alternating_property_count` (line 538)
- `lem:alternating_property_count` uses `lem:alternating_property_respects_pattern` (line 521)
- `lem:alternating_property_respects_pattern` uses only `def:alternating` (line 504)

Each child is a good leaf: `respects_pattern` closes on its own (its `uses`
lists only the definition `def:alternating`), `count` closes from its own
reasoning plus the named sibling `respects_pattern`, and `maximal` closes from
its own reasoning plus `count`. Each child's body is a single placeholder
`[Detailed reasoning from Gemini]`, so the example is an informal blueprint
sketch: the sub-lemmas are stated and dependency-ordered before any
formalisation. The `lem:alternating_property-before` context shows the same
lemma before the split — proof `[Empty]`, status `partial`, attempts `48/50` —
and the `gemini-three-steps` context is the Gemini reply whose three steps
become the three sub-lemmas (matching `3 distinct steps → SPLIT`, line 496).

## Why it is good

1. The parent is closed by a six-line glue (lines 563-568): the `## proof`
   header, `Follows from [lem:alternating_property_maximal]:`, one line per
   step, and `QED.` — it cites the chain rather than re-proving (`check`,
   [permalink](https://github.com/project-numina/numina-lean-agent/blob/1c9af8a52e715f22fede766425ba3d3b95526132/prompts/docs/prompts/blueprint_agent.md#L563-L568)).
2. The split is a depth-3 chain of three sub-lemmas: `respects_pattern` uses
   only `def:alternating` (line 504), `count` uses `respects_pattern` (line
   521), `maximal` uses `count` (line 538), and the parent uses `maximal` (line
   555) — so `direct_lemmas = 3` and `depth = 3` (`measurement`, the four
   `uses` fields, [lines 504, 521, 538, 555](https://github.com/project-numina/numina-lean-agent/blob/1c9af8a52e715f22fede766425ba3d3b95526132/prompts/docs/prompts/blueprint_agent.md#L504)).
3. The workflow states its split rule in its own words: "3 distinct steps →
   SPLIT" (line 496) and "Split complex lemmas when proof has 3+ steps" (line
   583) (`author-statement`,
   [line 496](https://github.com/project-numina/numina-lean-agent/blob/1c9af8a52e715f22fede766425ba3d3b95526132/prompts/docs/prompts/blueprint_agent.md#L496),
   [line 583](https://github.com/project-numina/numina-lean-agent/blob/1c9af8a52e715f22fede766425ba3d3b95526132/prompts/docs/prompts/blueprint_agent.md#L583)).
4. The file contains no `sorry`, `admit`, `Admitted` or `oops` token; the three
   child proof bodies are the placeholder `[Detailed reasoning from Gemini]`
   (`check`, grep over the whole 15933-byte copied file returned no match).

In my opinion the detail worth copying is the pairing of "one lemma per proof
step" with a dependency-ordered `uses` chain: the parent's proof is allowed to
shrink to a citation *because* the topology is recorded separately, so the
decomposition is the graph, not the text.

## When to use it, and when not

Use it when a blueprint node's proof is empty or partial, the LLM returns a
step-by-step informal proof with several distinct steps, and the proof agent
has already exhausted its attempts — the workflow turns the steps into named,
dependency-ordered sub-lemmas so each can be proved (or further split)
independently. Avoid it when the proof has fewer than three steps (the
workflow says to refine instead of split), when the steps are not ordered into
a chain that `uses` can express, or when the lemma is already small enough for
the proof agent to close directly.

## Consequences

The split creates three new blueprint nodes whose Lean files are marked "(to
be created)", so each child's informal Gemini proof still has to be formalised,
and the parent's proof reduces to a citation whose correctness rests entirely
on the chain holding. Obligations: every `uses` edge must stay consistent (the
checklist requires "Updated all `uses` fields correctly", line 454, and
"Reordered blueprint by topology (if needed)", line 456), and each child must
close from its own reasoning plus its named siblings. Failure modes: a step
that is not self-contained becomes a child whose placeholder proof cannot
later close; a broken `uses` edge leaves a lemma importing a sibling that is
not yet proved; and a wrong sub-lemma propagates to the theorem undetected
because the parent only cites it.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/project-numina/numina-lean-agent at commit `1c9af8a52e715f22fede766425ba3d3b95526132`, under `LicenseRef-unknown`; see the [source note](../../sources/numina-lean-agent/SOURCE.md) for the licence text and attribution.
