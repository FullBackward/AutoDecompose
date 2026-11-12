# The isabelle skill workflow: sorry-first skeleton, then incremental proof

| | |
|---|---|
| Kind | skill |
| Move | workflow |
| Language | markdown |
| Status | draft |
| Source | [isabelle-pide-ai](../../sources/isabelle-pide-ai/SOURCE.md) at `80ec85239c8a` |
| Licence | `LGPL-3.0` |

## Intent

Prescribe a workflow for developing an Isabelle theory top-down: plan the
order of definitions and key lemmas informally, state each lemma as a `sorry`
stub and check that the stubs suffice for the main results before proving any
of them, reserve further `sorry` holes for genuinely stuck subproofs, and
check incrementally so errors and non-termination stay local.

## The decomposition

### skill-text `workflow`: [`.agents/skills/isabelle/SKILL.md` lines 15-19](https://github.com/kappelmann/isabelle-pide-ai/blob/80ec85239c8a76d992a6f06d586cdc370934d751/.agents/skills/isabelle/SKILL.md#L15-L19) ([local copy](code/.agents/skills/isabelle/SKILL.md))

```markdown
- Understand the mathematics informally first. Plan the structure, order of definitions and theorems, and key lemmas.
- Work top-down: state definitions and lemmas with sorry and check that they suffice for the main results before proving them. Likewise within proofs: sorry larger subproofs first.
- Don't sorry steps you can prove right away and only sorry statements you are convinced are true.
- When stuck, isolate problems with sorry.
- Work incrementally: don't add too much before checking, so errors and non-termination stay easy to locate.
```

How the parts fit. The five rules form an ordered loop, not a single tactic.
*understand-plan* (line 15) produces the order of definitions, theorems, and
key lemmas; *sorry-skeleton* (line 16) states those as `sorry` stubs top-down
and — the key step — checks that the stubs *suffice* for the main results
before any of them is proved; the same line applies the move inside a proof by
sorry-ing larger subproofs first. *sorry-only-believed* (line 17) constrains
that move, proving right away whatever is provable and reserving `sorry` for
statements the author is convinced are true. *isolate-stuck* (line 18) is the
recovery step: when a proof does not close, a `sorry` reduces it to the stuck
subgoal, which then becomes its own target. *incremental-check* (line 19)
closes the loop by requiring frequent checking so errors and non-termination
stay easy to locate. Each rule's output is the next rule's input, and the two
`sorry` rules (16, 18) are both bounded by the same constraint (17).

This is a theorem-scale *workflow*, not a theorem-scale *instance*: the
passage names the decomposition order itself (plan, stub, check sufficiency,
then prove) rather than any concrete lemma, so there is no parent theorem and
no named child lemma to point at — the "children" above are the workflow's
steps, following the convention of the other `workflow` skill entries.

## Why it is good

1. The five rules are ordered plan → sorry-skeleton/sufficiency →
   don't-sorry-provables → isolate-with-sorry → incremental, and line 16
   states the sufficiency-first rule verbatim: "state definitions and lemmas
   with sorry and check that they suffice for the main results before proving
   them" (lines 15-19). Evidence kind: check.
2. The skill's Principles rank Correctness first and Faithfulness second
   ("1. Correctness: no errors or inconsistencies." / "2. Faithfulness:
   definitions and statements capture the intended meaning."), and the
   workflow's "only sorry statements you are convinced are true" (line 17) is
   the workflow-level expression of that priority. Evidence kind:
   author-statement.
3. The word "sorry" occurs 5 times across the five workflow lines (twice in
   line 16, twice in line 17, once in line 18) and no other proof method or
   tactic is named in the excerpt, so `sorry` is the only decomposition
   mechanism the workflow invokes. Evidence kind: measurement.

In my opinion the detail worth copying is the ordering *sufficiency before
truth*: the skeleton of stubs is checked against the main result before any
lemma is proved, so a wrong decomposition is caught when it is cheapest to
fix. The "only sorry what you believe true" guard is the other half — it
stops `sorry` from silently becoming a dumping ground for statements that
later turn out false.

## When to use it, and when not

Use it when the main result depends on several not-yet-proved lemmas whose
statements you can plan and believe true, and you want to fix the
decomposition (which lemmas, in which order) before spending effort on any
proof. Avoid it when you do not yet know the key lemmas — the workflow itself
says to search the libraries first (line 20); when a statement may be false,
because `sorry` checks sufficiency but not truth (quickcheck/nitpick do); or
when the task is a single stuck step in an otherwise complete proof, where
only the isolate-with-sorry rule (line 18) applies and the rest of the
workflow is overhead.

## Consequences

The workflow leaves the theory full of `sorry` stubs, which creates two
obligations. Sufficiency: the stubs must imply the main results, checked
before any lemma is proved (line 16). Discharge: every `sorry` must eventually
be replaced by a proof, and the "don't sorry steps you can prove right away /
only sorry statements you are convinced are true" rule (line 17) keeps the
sorry count honest rather than a dumping ground. Failure modes: `sorry` checks
sufficiency but not truth, so a false-but-plausible lemma slips through until
it is actually proved (nothing in the excerpt runs quickcheck/nitpick); and
skipping the incremental rule can hide a non-terminating proof until far too
much has been added.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/kappelmann/isabelle-pide-ai at commit `80ec85239c8a76d992a6f06d586cdc370934d751`, under `LGPL-3.0`; see the [source note](../../sources/isabelle-pide-ai/SOURCE.md) for the licence text and attribution.
