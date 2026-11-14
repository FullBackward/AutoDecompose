# Do Not Turn Proof Sections Into Assumptions

| | |
|---|---|
| Kind | skill |
| Move | workflow |
| Language | markdown |
| Status | draft |
| Source | [lean-autoformalization-skills](../../sources/lean-autoformalization-skills/SOURCE.md) at `1837b95b3d5a` |
| Licence | `CC-BY-4.0` |
| Licence recorded | 2026-11-12T15:31:19Z |

## Intent

When formalizing a paper theorem `A -> B` whose proof runs through named analytic
sections, the rule says to state each section (Step 1, Step 2) as its own
theorem, proved from the approved concrete inputs, and to have the final
theorem prove `B` by composing them. It forbids the alternative: adding a
section's conclusion as a hypothesis to the public theorem, which leaves only a
"conditional scaffold" — a strictly weaker claim than the implication the user
asked for.

## The decomposition

### skill-text `the-rule`: [`skills/lean-proof-patterns/references/math-to-lean.md` lines 40-42](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/1837b95b3d5a9fd8d311367603902ad7fe261adf/skills/lean-proof-patterns/references/math-to-lean.md#L40-L42) ([local copy](code/skills/lean-proof-patterns/references/math-to-lean.md))

> Use `suffices` and helper lemmas for local proof decomposition only.  When
> formalizing a paper theorem, do not replace a major analytic section by adding
> that section's conclusion as a hypothesis to the public theorem.

### parent `final`: [`skills/lean-proof-patterns/references/math-to-lean.md` line 56](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/1837b95b3d5a9fd8d311367603902ad7fe261adf/skills/lean-proof-patterns/references/math-to-lean.md#L56-L56) ([local copy](code/skills/lean-proof-patterns/references/math-to-lean.md))

The file quotes the public theorem in the form the rule *criticises* — a
conditional scaffold with the two sections as hypotheses:

```lean
theorem final (hA : A) (hStep1 : Step1) (hStep2 : Step2) : B
```

The correct form the rule demands is `final : A -> B` (no `hStep1`, `hStep2`),
with `Step1` and `Step2` proved as separate theorems.

### the glue: [`skills/lean-proof-patterns/references/math-to-lean.md` line 47](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/1837b95b3d5a9fd8d311367603902ad7fe261adf/skills/lean-proof-patterns/references/math-to-lean.md#L47-L47) ([local copy](code/skills/lean-proof-patterns/references/math-to-lean.md))

```text
A -> Step 1 -> Step 2 -> B
```

### children `Step1` and `Step2`: [`skills/lean-proof-patterns/references/math-to-lean.md` line 47](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/1837b95b3d5a9fd8d311367603902ad7fe261adf/skills/lean-proof-patterns/references/math-to-lean.md#L47-L47) ([local copy](code/skills/lean-proof-patterns/references/math-to-lean.md))

The two named lemmas are the stages of that single glue line: `Step1` is the
step `A -> Step 1` and `Step2` is the step `Step 1 -> Step 2`. Both are
schematic — this reference names them but gives neither a statement nor a proof
body, because it is a skill, not a development.

### context `must-prove-steps`: [`skills/lean-proof-patterns/references/math-to-lean.md` lines 50-51](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/1837b95b3d5a9fd8d311367603902ad7fe261adf/skills/lean-proof-patterns/references/math-to-lean.md#L50-L51) ([local copy](code/skills/lean-proof-patterns/references/math-to-lean.md))

> then the Lean development must contain theorems proving `Step 1` and `Step 2`
> from the approved concrete inputs before the final theorem proves `B`.

### context `failure-conditions`: [`skills/lean-proof-patterns/references/math-to-lean.md` lines 59-62](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/1837b95b3d5a9fd8d311367603902ad7fe261adf/skills/lean-proof-patterns/references/math-to-lean.md#L59-L62) ([local copy](code/skills/lean-proof-patterns/references/math-to-lean.md))

> is not a formalization of `A -> B`; it is only a conditional scaffold.  Treat
> auditor phrases such as "certified under the abstract interface" or
> "conditional certification" as failures when the user asked for the implication
> itself.

How the parts fit. The glue is the three-stage path
`A -> Step 1 -> Step 2 -> B`; the parent `final : A -> B` is proved by
composing two named lemmas:

```
final : A -> B
  ├── uses Step2 : Step 1 -> Step 2     (Step 2 is the paper's second section)
  └── uses Step1 : A -> Step 1          (Step 1 is the paper's first section)
          └─ Step2's only input is Step1's conclusion
```

`Step1` is a good leaf because it is a self-contained statement — `A -> Step 1`
— whose proof closes on its own from the approved concrete inputs, with no
sibling. `Step2` is a good leaf given its named sibling: `Step 1 -> Step 2`
takes `Step1`'s conclusion as its explicit input, so it closes from `Step1`
rather than re-proving it. The anti-pattern the rule rejects is the theorem that
turns these two leaves into hypotheses: `final (hA : A) (hStep1 : Step1)
(hStep2 : Step2) : B`, which proves a weaker claim than `A -> B` and does not
discharge either section.

## Why it is good

1. The only theorem statement in the excerpt is the conditional scaffold
   `theorem final (hA : A) (hStep1 : Step1) (hStep2 : Step2) : B` (line 56),
   with `Step1` and `Step2` as added hypotheses, and the next sentence declares
   it "not a formalization of `A -> B`; it is only a conditional scaffold"
   (lines 59-60) (check).
2. The positive obligation is stated in the file's own words: "the Lean
   development must contain theorems proving `Step 1` and `Step 2` from the
   approved concrete inputs before the final theorem proves `B`" (lines 50-51)
   (author-statement).
3. The theorem-scale shape is `direct_lemmas = 2` (Step1, Step2), `depth = 2`
   (Step2 depends on Step1), `glue_lines = 1` (the single path line), and
   `child_lines = [1, 1]` — each child is shown only by that one path line,
   with no proof body in the reference (measurement, lines 44-57).
4. The rule names the failure symptom as auditor language: "certified under the
   abstract interface" and "conditional certification" are failures "when the
   user asked for the implication itself" (lines 60-62) (author-statement).

In my opinion the detail worth copying is the test at the end: the way to detect
the mistake is not to read the proof but to compare the *type* of the public
theorem against the paper's claim — any extra hypothesis is a proof section that
was assumed instead of proved.

## When to use it, and when not

Use it when you are stating the public theorem of a formalization whose paper
proof runs through identifiable sections (Step 1, Step 2) that can each be
stated as their own theorem from the approved concrete inputs. It is a statement
hygiene rule, so it applies at the boundary of the theorem, not inside a single
proof. Avoid it when a section's conclusion genuinely *is* an extra hypothesis
of the paper's result rather than a step to prove; when you are building a
provisional scaffold for development on purpose and will discharge the sections
later; or when the decomposition is local to one proof, where the rule itself
says to use `suffices` and helper lemmas instead.

## Consequences

Promoting a proof section to a hypothesis silently weakens the public theorem:
`final (hA : A) (hStep1 : Step1) (hStep2 : Step2) : B` proves a strictly weaker
claim than `A -> B`, and no downstream client can detect the gap without
comparing the type to the paper's statement. The correct structure creates
obligations instead: Step 1 must be proved from the approved concrete inputs,
Step 2 from Step 1's conclusion, and `final` must compose them. The sequential
dependence means Step 2 is not provable until Step 1 is, so the two leaves are
not parallelisable as stated. The failure modes the file names are the auditor
phrases "certified under the abstract interface" and "conditional
certification" — signs that sections were assumed rather than proved.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | not-run | the copied file is a Markdown skill reference (skills/lean-proof-patterns/references/math-to-lean.md), not a Lean source file; no CI compiles a Markdown phrasebook, so there is no build to record | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 1837b95b3d5a9fd8d311367603902ad7fe261adf | check_provenance.py | 2026-11-12 |
| sorry-scan | not-run | no Lean, Rocq or Isabelle file among the copied files | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | read the copied file: line 56 is exactly "theorem final (hA : A) (hStep1 : Step1) (hStep2 : Step2) : B" with the two added hypotheses, and line 59 reads "is not a formalization of A -> B; it is only a conditional scaffold." | verifier |
| 2 | verified | read the copied file lines 50-51: "then the Lean development must contain theorems proving Step 1 and Step 2 from the approved concrete inputs before the final theorem proves B." | verifier |
| 3 | verified | counted on the copied file: the glue path 'A -> Step 1 -> Step 2 -> B' is the single line 47; the parent theorem is line 56; the mandate naming Step 1 and Step 2 is lines 50-51, giving direct_lemmas=2, depth=2, glue_lines=1, child_lines=[1,1] with no child proof bodies shown. | verifier |
| 4 | verified | read the copied file lines 60-62: 'Treat auditor phrases such as "certified under the abstract interface" or "conditional certification" as failures when the user asked for the implication itself.' | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | object | Decomposition, children and closing methods match the copied file: the glue 'A -> Step 1 -> Step 2 -> B' (line 47), the mandate to prove Step 1 and Step 2 before final proves B (lines 50-51), and the anti-pattern theorem on line 56 are all quoted verbatim. direct_lemmas=2 and depth=2 are right. But shape.child_lines=[1,1] is not right: the field is 'proof lines of each child shown', and neither child has a statement or proof body in the source (they are schematic, only named in prose); the single glue/path line 47 is not a proof line of either child. This contradicts the entry's own metrics.child_bodies_shown=0. Fix: set child_lines to [0,0] (and reconcile metrics), or annotate the shape to say the children are not shown. Secondary: glue_lines is counted as the glue path line 47, but the field defines it as 'lines of the main proof' (here the parent theorem line 56); the number is coincidentally also 1. | reviewer-correctness |
| generality | accept | Move is stated abstractly (named analytic sections, schematic Step1/Step2 with no proof body), so it applies beyond the one A -> Step1 -> Step2 -> B example. 'When not to use' gives three honest, specific cases grounded in the source: (a) section is genuinely a paper hypothesis, not a step (source's 'when the user asked for the implication itself' implies the converse); (b) deliberate provisional scaffold discharged later; (c) local decomposition, where source line 40 itself says use suffices/helper lemmas. Consequences are honest and specific: hypothesis promotion yields a strictly weaker type undetectable by downstream clients without comparing to the paper, and the sequential Step1->Step2 dependence means the leaves are not parallelisable. It states what makes the leaves good for a bounded prover (README lines 78-85): Step1 is self-contained (A -> Step 1 closes from approved inputs, no sibling) and Step2 has a single explicit input (Step 1 -> Step 2 closes from Step1's conclusion rather than re-proving it). No overclaim beyond the source's implication scope. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are all consistent and traceable. check_provenance.py passes: the single copied file (6469 bytes, sha256 4b65d248...) is byte-identical at commit 1837b95b3d5a9fd8d311367603902ad7fe261adf. entry.json, README.md, sources/lean-autoformalization-skills/source.json and SOURCE.md all record the same commit. Licence CC-BY-4.0 is recorded identically in entry.json, README, source.json and SOURCE.md, and the copied upstream-LICENSE is the genuine CC-BY-4.0 text. SOURCE.md lists LICENSE copied as upstream-LICENSE and gives repo URL/commit/pinned date. The entry README's Source-and-licence section notes the derivative attribution to cameronfreer/lean4-skills, which the copied file's header (lines 3-7) also retains, so CC-BY attribution is preserved. All site permalinks use the pinned commit with line anchors that match the copied file. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/scottnarmstrong/LeanAutoformalizationSkills at commit `1837b95b3d5a9fd8d311367603902ad7fe261adf`, under `CC-BY-4.0`; see the [source note](../../sources/lean-autoformalization-skills/SOURCE.md) for the licence text and attribution. The file is adapted from cameronfreer/lean4-skills `lean-phrasebook.md` (line 3-4 of the copied file).
