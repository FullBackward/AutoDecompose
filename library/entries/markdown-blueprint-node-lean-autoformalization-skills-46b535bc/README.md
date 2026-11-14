# Model a proof faithfully as a dependency graph of step nodes (blueprint node)

| | |
|---|---|
| Kind | skill |
| Move | blueprint-node |
| Language | markdown |
| Status | draft |
| Source | [lean-autoformalization-skills](../../sources/lean-autoformalization-skills/SOURCE.md) at `1837b95b3d5a` |
| Licence | `CC-BY-4.0` |

## Intent

Turn a root theorem's proof into a source-level dependency graph: the root is
author-frozen before its proof, the proof is modelled as a conjunction of
substantive step nodes consumed through a `DEPS` edge set, and the glue is the
edges — one direct-use locator per edge — so a later Lean orchestrator gets a
checked skeleton with one bounded, independently failing obligation per step.
This is the "stated before proved" shape of the `blueprint-node` move, applied
as a *procedure* rather than a single instance: it prescribes how every proof
in the corpus is split, not how one particular proof was.

## The decomposition

### parent `model-the-proof-faithfully`: [`skills/build-proof-dependency-graph/SKILL.md` lines 184-234](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/1837b95b3d5a9fd8d311367603902ad7fe261adf/skills/build-proof-dependency-graph/SKILL.md#L184-L234) ([local copy](code/skills/build-proof-dependency-graph/SKILL.md))

```markdown
## Phase 4: model the proof faithfully

Use only direct dependency edges. Do not add a prerequisite merely because it
appears earlier in the paper. An edge can still be direct even when another
path makes it transitively redundant: retain it when the target's own proof
explicitly invokes or logically consumes that prerequisite.

Create a step node when omitting the step would hide a plausible Lean lemma or
an independently failing obligation. Typical examples are a nontrivial
estimate, construction, case split, parameter or witness choice, theorem
application, quantifier closure, carrier change, or reused intermediate claim.
Do not create nodes for routine algebra or purely syntactic rewrites unless
they change hypotheses, constants, carriers, or quantifier strength.

If the source asserts or needs a substantive bridge without actually proving
it, keep that bridge as a `step` or `application` node and mark `NOTE` with a
clear `SOURCE_GAP:` explanation. Its `STATEMENT_SOURCE` may point to the target
statement and its `PROOF_SOURCE` to the prose where the bridge is invoked.
`TOPOLOGY_STATUS` judges whether this modeling is accurate, not whether the
source proves the mathematics, so an independently confirmed gap can be
`REVIEWED`. Do not silently fill an omitted bridge merely because a reviewer
can reconstruct a proof; apply the substantive-step threshold to what the
source actually supplies. Never invent a proof-status-like topology value.

Interpret `DEPS` conjunctively. If the source offers alternative derivations,
create one `KIND: route` node for each derivation and list them in `ROUTES` on
the target. One available route will later suffice. Never put alternatives in
one comma-separated `DEPS` list. `ROUTE_FOR` is exclusively the ownership field
for these route nodes; do not use it as a parent pointer for ordinary proof
steps or displays.

Represent standing assumptions and external results as explicit leaf nodes.
Do not hide them in notes or magic dependency tokens. Only IDs frozen in the
header may use `KIND: assumption`; the linter rejects undeclared assumption
nodes.

Do not turn every bound variable or theorem-local premise into a node. Keep a
premise inside its statement unless it is a genuine standing assumption or a
substantive obligation established elsewhere. A named local hypothesis package
may map to the enclosing theorem node in the coverage manifest; naming alone
does not make it a globally `ASSUMED` leaf. A conditional lemma may therefore
be a node without separate nodes for all of its premises. At each later
application, create direct dependencies for the source steps that discharge
those premises, splitting out a substantive application node when necessary.

Keep source-statement fields and proof topology separate. `DEPS` names results the
source proof consumes; it never enlarges `SOURCE_HYPOTHESES`. If result `B` is
used to prove `A`, represent `B` as a dependency of `A`, not as an allowed
hypothesis of `A`. A genuinely conditional source lemma records its displayed
premises in `SOURCE_HYPOTHESES`; a helper with additional premises is not the
same source node. Never use an edge to launder proof content into a statement.
```

### The five step-node kinds (children), [`lines 191-196`](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/1837b95b3d5a9fd8d311367603902ad7fe261adf/skills/build-proof-dependency-graph/SKILL.md#L191-L196) ([local copy](code/skills/build-proof-dependency-graph/SKILL.md))

The five child sites all point to the same threshold paragraph, because the
skill names all five step-node kinds in one sentence (lines 192-194):

```markdown
Create a step node when omitting the step would hide a plausible Lean lemma or
an independently failing obligation. Typical examples are a nontrivial
estimate, construction, case split, parameter or witness choice, theorem
application, quantifier closure, carrier change, or reused intermediate claim.
Do not create nodes for routine algebra or purely syntactic rewrites unless
they change hypotheses, constants, carriers, or quantifier strength.
```

### How the parts fit

The parent is the **root theorem**, an author-frozen anchor whose statement is
final before any proof exists (the skill's Phase 0, SKILL.md lines 63-107:
"Freeze each approved keystone proposition or theorem with the exact body `by
sorry` … do not wait for its proof"). The **glue** is the edge set: `DEPS`
naming the results the proof consumes, each with one `EDGE:` record carrying a
direct-use locator (line 186: "Use only direct dependency edges"; line 208:
"Interpret `DEPS` conjunctively"). The **children** are the substantive step
nodes, the five kinds enumerated at lines 191-196:

```
root theorem (frozen before proof; Phase 0)
   └── its proof, modelled as the glue = DEPS edge set (lines 186-189, 208-213)
         ├── step node: nontrivial estimate or construction     (191-196)
         ├── step node: case split or witness choice            (191-196)
         ├── step node: theorem application                     (191-196)
         ├── step node: quantifier closure or carrier change    (191-196)
         └── step node: reused intermediate claim               (191-196)
   (plus explicit leaf nodes for standing assumptions and external results, 215-218)
```

There is no edge *between* step nodes in this site — each is a direct leaf of
the root — so the shape's depth is 1. Each child is a good leaf because it is
a self-contained obligation whose proof closes on its own or from a named
external result: the skill requires a step node precisely "when omitting the
step would hide a plausible Lean lemma or an independently failing
obligation" (lines 191-192), and it forbids nodes for "routine algebra or
purely syntactic rewrites" (lines 195-196), so no leaf is trivial. The skill
itself is source-extraction only: it records each node and "mak[es] no claim
that an anchor's proof has been completed" (lines 10-11); the later Lean
orchestrator proves each leaf. The complementary negative rule — no child is a
copied hypothesis — is lines 229-234: `DEPS` "never enlarges
`SOURCE_HYPOTHESES`", so a proof step never leaks into the root's statement.

The node schema that `DEPS`, `EDGE`, `KIND` and the other fields refer to is in
the copied [`assets/DEPGRAPH.template.md`](code/skills/build-proof-dependency-graph/assets/DEPGRAPH.template.md)
("The dependency direction is `NODE -> prerequisite`. `DEPS` is conjunctive.").

## Why it is good

1. **check** — The parent site names `DEPS` (the conjunctive edge set that is
   the glue). Form `cites(model-the-proof-faithfully, DEPS)`;
   [SKILL.md#L184-L234](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/1837b95b3d5a9fd8d311367603902ad7fe261adf/skills/build-proof-dependency-graph/SKILL.md#L184-L234).

2. **check** — `DEPS` occurs 4 times in the SKILL.md file. Form
   `count(DEPS, 4, skills/build-proof-dependency-graph/SKILL.md)`; counted by
   `check_claims.py` over the copied file.

3. **measurement** — The theorem-scale shape is `direct_lemmas = 5` (the five
   step-node kinds), `depth = 1` (every step node is a direct leaf of the
   root), `glue_lines = 51` (the parent site, lines 184-234), and
   `child_lines = [6, 6, 6, 6, 6]` (each child is the threshold paragraph,
   lines 191-196).

4. **author-statement** — The skill states the step-node threshold in its own
   words: "Create a step node when omitting the step would hide a plausible
   Lean lemma or an independently failing obligation", and excludes routine
   steps: "Do not create nodes for routine algebra or purely syntactic rewrites
   unless they change hypotheses, constants, carriers, or quantifier strength".
   [SKILL.md#L191-L196](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/1837b95b3d5a9fd8d311367603902ad7fe261adf/skills/build-proof-dependency-graph/SKILL.md#L191-L196).

5. **author-statement** — The skill keeps proof topology out of the statement:
   "Keep source-statement fields and proof topology separate. `DEPS` names
   results the source proof consumes; it never enlarges
   `SOURCE_HYPOTHESES`", and "Never use an edge to launder proof content into a
   statement".
   [SKILL.md#L229-L234](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/1837b95b3d5a9fd8d311367603902ad7fe261adf/skills/build-proof-dependency-graph/SKILL.md#L229-L234).

## When to use it, and when not

**Goal shape.** A proof of a root theorem (an author-frozen, one-declaration
anchor) that must be turned into a machine-checked dependency graph for a later
Lean orchestrator, where the proof is line-addressable source (LaTeX or
Markdown) and each substantive step can become one node.

**Use when** you must trace a proof's dependencies at source level without
deciding whether any theorem is proved; the root is already frozen as an exact
Lean declaration (Phase 0, SKILL.md lines 63-107); and you want a bounded
number of lemma-sized step nodes per proof, each an independently failing
obligation, plus explicit leaf nodes for standing assumptions and external
results.

**Avoid when** you are inspecting implementation Lean code or deciding whether
a theorem is proved (the skill forbids this, SKILL.md lines 16-21); the step is
routine algebra or a purely syntactic rewrite that changes no hypothesis,
constant, carrier or quantifier strength (lines 195-196); or there is no
author-frozen root anchor to root the graph.

## Consequences

The move creates obligations: every substantive step must become a node with a
stable ID and statement/proof locators; every `DEPS` or `ROUTES` entry needs one
`EDGE` record with a direct-use locator (the glue); standing assumptions and
external results must be explicit leaf nodes (lines 215-218). The failure modes
the skill names are: adding a prerequisite merely because it appears earlier in
the paper (lines 186-187); putting alternatives in one comma-separated `DEPS`
list instead of separate `ROUTE` nodes (lines 208-211); turning a theorem-local
premise into a node (lines 220-221); and laundering proof content into a
statement — `DEPS` must never enlarge `SOURCE_HYPOTHESES` (lines 229-234).

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
| 1 | verified | cites(model-the-proof-faithfully, DEPS) -> cites: DEPS occurs at skills/build-proof-dependency-graph/SKILL.md:208 | check_claims.py |
| 2 | verified | count(DEPS, 4, skills/build-proof-dependency-graph/SKILL.md) -> count: DEPS occurs 4 times in 1 file(s) matching skills/build-proof-dependency-graph/SKILL.md | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/scottnarmstrong/LeanAutoformalizationSkills at commit `1837b95b3d5a9fd8d311367603902ad7fe261adf`, under `CC-BY-4.0`; see the [source note](../../sources/lean-autoformalization-skills/SOURCE.md) for the licence text and attribution.
