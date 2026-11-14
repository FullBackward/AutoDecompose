# Definition-first interface: prove and tag a definition's intro/elim/dest/simp rules, then apply them instead of unfolding

| | |
|---|---|
| Kind | skill |
| Move | interface-lemma |
| Language | markdown |
| Status | draft |
| Source | [isabelle-pide-ai](../../sources/isabelle-pide-ai/SOURCE.md) at `80ec85239c8a` |
| Licence | `LGPL-3.0-only` |

## Intent

Prescribe a definition-first interface discipline for writing Isabelle
theories: prove each new definition's basic properties as intro, elim, dest
and simp rules (its interface) and then close later goals by applying those
lemmas instead of unfolding the definition, so proofs stay at the level of
named rules rather than expanded terms. The paired honesty rule bounds this:
do not weaken statements without a clear reason, and generalise only when the
generalisation instantiates back to the wanted result.

## The decomposition

### skill-text `interface-lemma`: [`.agents/skills/isabelle/SKILL.md` lines 23-25](https://github.com/kappelmann/isabelle-pide-ai/blob/80ec85239c8a76d992a6f06d586cdc370934d751/.agents/skills/isabelle/SKILL.md#L23-L25) ([local copy](code/.agents/skills/isabelle/SKILL.md))

```markdown
## Definitions and statements
- Prove basic properties of definitions first (e.g. intro, elim, dest, simp rules) and use them instead of unfolding definitions.
- Don't weaken statements unless clearly justified. Generalisations are fine if they instantiate to the desired result.
```

How the parts fit. The two bullets are one move plus its guard, not a theorem
with named lemmas — this is a *skill* (a rule for stating and closing goals),
so its parts are the steps of the discipline rather than child lemmas. This is
the same situation as the sibling `workflow` entry in this file, which is a
skill rather than a theorem-scale instance for the same reason: the passage
names rule families ("intro, elim, dest, simp"), not concrete lemma names.

- `prove-interface-rules` (line 24, first clause) is the production half of the
  move: for each new definition, prove its basic properties as intro, elim,
  dest and simp rules. Those four families are the definition's *interface* —
  the facts later proofs are allowed to know about it.
- `use-interface-not-unfold` (line 24, second clause) is the consumption half:
  later proofs close goals by applying those interface lemmas instead of
  unfolding the definition. This is what "lets clients stop unfolding" means in
  the move's definition: the definition's expansion becomes a private detail
  behind the interface.
- `no-weakening` (line 25, first clause) keeps the interface honest on the
  input side: a statement may be weakened only with a clear justification, so
  the interface does not quietly promise less than the definition means.
- `generalise-to-instantiate` (line 25, second clause) keeps it honest on the
  output side: a generalisation is admitted only if it instantiates back to the
  wanted result, so the interface does not over-claim.

The two honesty clauses are what make it safe to stop unfolding at all: if each
intro/elim/dest/simp rule is a true, unweakened basic property, then a proof
that applies them rather than unfolding is sound, and the reader can audit the
interface once instead of at every unfolding site.

## Why it is good

1. The skill-text site `interface-lemma` is 3 lines long (lines 23-25 of the
   copied file). Evidence kind: check, form `lines(interface-lemma, 3)`.
2. The word `simp` occurs 6 times in the copied file
   `.agents/skills/isabelle/SKILL.md`. Evidence kind: check, form
   `count(simp, 6, .agents/skills/isabelle/SKILL.md)`.
3. The skill's "Theorem tagging" section restates the discipline as an
   instruction — "Tag fundamental theorems of new definitions, unless they are
   rarely used; then pass the rules explicitly" (line 44) — and line 43 names
   the same families "simp, intro, elim, dest" to be tagged. Evidence kind:
   author-statement.
4. Counting whole-word occurrences in the copied file, "intro" appears 4 times,
   "elim" 3 times, "dest" 3 times and "simp" 6 times, and the three families
   "intro", "elim", "dest" co-occur at exactly lines 24, 38 and 43 — the
   definition-interface rule, the find_theorems guide and the tagging rule — so
   the skill reuses one rule-family vocabulary for stating, finding and tagging
   interface rules. Evidence kind: measurement.

Survey F §10's 18 rules are decomposition *procedures* (split, induction,
sorry, salvage, …); the interface-lemma discipline is lemma *organisation*
at an abstraction boundary, so it is not one of them and the entry records
`relation: none`. Its closest neighbour is rule 14 ("nearly trivial leaves
closed by try0/sledgehammer"), which the tagged simp/intro/elim/dest rules
serve — but the move here is "prove and tag the interface", not "decide when a
leaf is done".

In my opinion the detail worth copying is the pairing of the production rule
with its honesty guard in the same breath: line 24 says "prove the interface
and use it", and line 25 immediately says what the interface must not do
(weaken, or generalise beyond instantiation). A discipline that only said
"prove intro/elim/dest/simp rules" without the guard would license a lemma
whose simp rule silently loops or whose statement was weakened to something
false-but-convenient.

## When to use it, and when not

Use it when you have just defined a constant and several later lemmas will
reason about it: the basic facts are worth proving once and tagging, so that
`simp`/`intro`/`elim`/`dest` and the hammers (`try0`, `sledgehammer`) can find
and apply them, rather than each proof unfolding by hand. Use it especially at
an abstraction boundary — a locale, a type class, a datatype, an API constant —
whose clients should not see the definition's expansion.

Avoid it when the definition is used once or twice and a one-off unfold is
clearer than a named interface; when the basic fact is already in the library
(the skill itself says to search the libraries before defining, line 20); or
when the "basic" fact does not actually fit the intro/elim/dest/simp families —
forcing it in can produce a looping simp rule, which the skill warns of
separately at line 43.

## Consequences

The discipline creates two obligations. Interface completeness: every basic
property a client needs must be captured as an intro/elim/dest/simp rule, and a
missing rule forces the next proof to unfold by hand or fail. Honesty of the
interface: because later proofs trust the rules, a weakened or over-generalised
rule propagates silently, which is why line 25 pairs the guard with the move.
Failure modes: an over-aggressive simp rule loops (warned at line 43); tagging a
rule `simp` that is not a good normal form makes later `simp` calls
non-terminating or non-confluent; and proving the interface first is wasted work
if the definition later changes, since the whole interface must then be
re-proved.

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
| 1 | verified | lines(interface-lemma, 3) -> lines: site interface-lemma has 3 lines | check_claims.py |
| 2 | verified | count(simp, 6, .agents/skills/isabelle/SKILL.md) -> count: simp occurs 6 times in 1 file(s) matching .agents/skills/isabelle/SKILL.md | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/kappelmann/isabelle-pide-ai at commit `80ec85239c8a76d992a6f06d586cdc370934d751`, under `LGPL-3.0-only`; see the [source note](../../sources/isabelle-pide-ai/SOURCE.md) for the licence text and attribution.
