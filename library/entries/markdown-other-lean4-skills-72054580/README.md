# Keep named intermediates for the combining lemma

| | |
|---|---|
| Kind | instance |
| Move | other |
| Language | markdown |
| Status | draft |
| Source | [lean4-skills](../../sources/lean4-skills/SOURCE.md) at `3f913c66251b` |
| Licence | `MIT` |

## Intent

A proof whose goal closes by one application of a combining lemma `combine`
over two intermediate facts is golfed *without* inlining the intermediates
into the application. The two facts stay as named `have`s (`h1 : A`,
`h2 : B`) and the goal closes by `exact combine h1 h2`, so the decomposition
into two leaf facts plus the combining application stays visible instead of
collapsing into one opaque `exact combine (...)`.

## The decomposition

### parent `combining-goal`: [`plugins/lean4/skills/lean4/references/proof-golfing.md` lines 251-253](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/proof-golfing.md#L251-L253) ([local copy](code/plugins/lean4/skills/lean4/references/proof-golfing.md))

```markdown
have h1 : A := ...
have h2 : B := ...
exact combine h1 h2
```

### child `h1`: [`plugins/lean4/skills/lean4/references/proof-golfing.md` lines 251-251](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/proof-golfing.md#L251-L251) ([local copy](code/plugins/lean4/skills/lean4/references/proof-golfing.md))

```markdown
have h1 : A := ...
```

### child `h2`: [`plugins/lean4/skills/lean4/references/proof-golfing.md` lines 252-252](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/proof-golfing.md#L252-L252) ([local copy](code/plugins/lean4/skills/lean4/references/proof-golfing.md))

```markdown
have h2 : B := ...
```

### child `combine`: [`plugins/lean4/skills/lean4/references/proof-golfing.md` lines 253-253](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/proof-golfing.md#L253-L253) ([local copy](code/plugins/lean4/skills/lean4/references/proof-golfing.md))

```markdown
exact combine h1 h2
```

### context `bad-inline`: [`plugins/lean4/skills/lean4/references/proof-golfing.md` lines 247-248](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/proof-golfing.md#L247-L248) ([local copy](code/plugins/lean4/skills/lean4/references/proof-golfing.md))

```markdown
-- ❌ Bad - unreadable
exact combine (obscure nested lambdas spanning 100+ chars)
```

### context `name-earlier-fact`: [`plugins/lean4/skills/lean4/references/proof-golfing.md` lines 256-266](https://github.com/cameronfreer/lean4-skills/blob/3f913c66251b8712bb58e6ce83a453fa96e3f94f/plugins/lean4/skills/lean4/references/proof-golfing.md#L256-L266) ([local copy](code/plugins/lean4/skills/lean4/references/proof-golfing.md))

````markdown
### Don't Remove Helpful Names

```lean
-- ❌ Bad
have : ... := by ...  -- 10 lines
have : ... := by ...  -- uses first anonymous have

-- ✅ Good
have h_key_property : ... := by ...
have h_conclusion : ... := by ...  -- uses h_key_property
```
````

This is the `### Don't Over-Inline` subsection (line 242) of the file's
*Anti-Patterns* section. The subsection pairs a Bad example — `exact combine
(obscure nested lambdas spanning 100+ chars)`, which folds both intermediates
into one unreadable application — with the Good example above, which keeps
them as named `have`s. The companion subsection, `### Don't Remove Helpful
Names` (lines 256-266), states the same value from the other direction: a
later step can only use an earlier fact if that fact was named first.

How the parts fit. The parent `combining-goal` (an unnamed enclosing goal,
shown only by its proof body) names two independent leaves and then closes:

```
combining-goal ── exact combine h1 h2 ──▶ combine : A → B → goal
    ├── have h1 : A := ...   (leaf, independent of h2 and combine)
    └── have h2 : B := ...   (leaf, independent of h1 and combine)
```

Neither leaf depends on the other; the only dependency is the combining
lemma `combine`, which consumes both `h1` and `h2` and returns the goal. The
glue is exactly three lines: two `have` bindings and one `exact`.

Why each leaf is good. `h1` is a self-contained statement — `A` — whose proof
(the `...` placeholder) closes on its own, using nothing from `h2` or
`combine`. `h2` is the same shape, a self-contained `B`. `combine` is a
pre-existing lemma of type `A → B → goal`, stated outside the excerpt; it is
a leaf here because it is *applied*, not proved — the point of the rule is
that the application `exact combine h1 h2` stays visible rather than
absorbing the two leaves into a single term.

## Why it is good

1. The parent's proof cites the combining lemma `combine`: the closing line
   is `exact combine h1 h2` (line 253) (`check`, form `cites(parent,
   combine)`).
2. The parent site `combining-goal` — the whole proof — is 3 lines long: two
   named `have`s and the closing application (lines 251-253) (`check`, form
   `lines(parent, 3)`).
3. The file states the rule in its own words — "If inlining creates
   unreadable proof, keep intermediate steps" (line 244) — and the Good
   example that follows it is exactly the parent's three lines
   (`author-statement`, lines 244 and 250-253).
4. The theorem-scale shape is measured as 3 direct lemmas (`h1`, `h2`,
   `combine`) with no chain of project lemmas below the main theorem
   (depth 1): direct_lemmas=3, depth=1, glue_lines=3, child_lines=[1,1,1]
   (`measurement`, counted on the copied file, lines 251-253).

Against survey F §10 this is the inverse-direction rule to §10.4
(*extract a `have` into a standalone lemma only with a fidelity check*):
rule 4 lifts a `have` up into a top-level lemma, while this rule keeps the
`have` as a named inline intermediate and forbids flattening it into one
opaque application. The two pull in opposite directions on the same object;
both agree that the intermediate's *name* must be preserved.

In my opinion the detail worth copying is that the intermediates are named
`have`s rather than top-level lemmas: the combining lemma's arguments are
manifestly available as `h1` and `h2`, so a reader (or a bounded prover) can
fill each leaf independently without touching the glue.

## When to use it, and when not

Use it when the intermediate facts are meaningful on their own and worth
naming for re-reading, when the combined application would be long or nested
(the Bad example is "obscure nested lambdas spanning 100+ chars", line 248),
or when a later step must refer back to an earlier fact (the companion
"Don't Remove Helpful Names" rule). Avoid it when the intermediate is short
and used exactly once — the file's Tier 3 prescribes inlining a single-use
`have` whose term is under 40 characters — when the name adds no meaning, or
when the goal is trivial enough that the named intermediates are noise. This
rule is a guard against over-golfing, not a reason to stop golfing: it lives
in the file's *Anti-Patterns* section precisely because inlining is the
default elsewhere.

## Consequences

Keeping the intermediates named preserves the dependency structure — which
fact feeds which argument of `combine` — at the cost of two extra `have`
lines versus the inlined one-liner. The companion obligation is that a later
step can use an earlier fact only if that fact was named first: an anonymous
`have : ...` cannot be cited (the "Don't Remove Helpful Names" Bad example
shows a second anonymous `have` silently depending on the first, lines
259-261). Failure modes: naming an intermediate that is never used again
leaves a dead binding that the golfer's Tier 3 would inline; inlining a fact
that a later step needs breaks the proof.

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
| 1 | verified | cites(parent, combine) -> cites: combine occurs at plugins/lean4/skills/lean4/references/proof-golfing.md:253 | check_claims.py |
| 2 | verified | lines(parent, 3) -> lines: site parent has 3 lines | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/cameronfreer/lean4-skills at commit `3f913c66251b8712bb58e6ce83a453fa96e3f94f`, under `MIT`; see the [source note](../../sources/lean4-skills/SOURCE.md) for the licence text and attribution.
