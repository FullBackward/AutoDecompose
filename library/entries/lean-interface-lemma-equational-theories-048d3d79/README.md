# Interface lemma models_def' re-expresses entailment over all universes for Birkhoff completeness

| | |
|---|---|
| Kind | instance |
| Move | interface-lemma |
| Language | lean |
| Status | accepted |
| Source | [equational-theories](../../sources/equational-theories/SOURCE.md) at `8b87204d5b20` |
| Licence | `Apache-2.0` |

## Intent

`Completeness'` is Birkhoff's completeness theorem, and its proof is two lines
of glue with no case analysis or induction. The hypothesis `h : Γ ⊧ E` is
re-expressed through the interface lemma `models_def'` into a statement about
the free magma with laws, instantiated at `FreeMagmaWithLaws β Γ` using
`isModel` (that this magma satisfies `Γ`), and converted into a derivation
with `isDerives`. The interface lemma `models_def'` is the abstraction
boundary: it reformulates the bundled `models` relation, which quantifies only
over `Type` (universe 0), as a universal statement over `Type*` (all
universes), so the client stops unfolding `models` and stops reasoning about
universes.

## The decomposition

### parent `Completeness'`: [`equational_theories/Completeness.lean` lines 156-158](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/Completeness.lean#L156-L158) ([local copy](code/equational_theories/Completeness.lean))

```lean
/-- Birkhoff's completeness theorem -/
theorem Completeness' {α β} {Γ : Ctx α} {E : MagmaLaw β} (h : Γ ⊧ E) : Nonempty (Γ ⊢' E) :=
  FreeMagmaWithLaws.isDerives (models_def'.1 h _ (FreeMagmaWithLaws.isModel β Γ))
```

### child `models_def'`: [`equational_theories/Completeness.lean` lines 147-154](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/Completeness.lean#L147-L154) ([local copy](code/equational_theories/Completeness.lean))

```lean
theorem models_def' {α β} {Γ : Ctx α} {E : MagmaLaw β} :
    Γ ⊧ E ↔ ∀ (G : Type*) [Magma G], G ⊧ Γ → G ⊧ E := by
  constructor <;> intro H G _ h
  · classical
    rw [← models_toNat] at H
    have ⟨h'⟩ := FreeMagmaWithLaws.isDerives (FreeMagmaWithLaws.models_iff_u.1 H)
    exact satisfies_toNat.1 (Soundness'_u h' h)
  · exact (satisfies_equiv uliftMagmaEquiv).2 (H _ ((satisfiesSet_equiv uliftMagmaEquiv).1 h))
```

### child `FreeMagmaWithLaws.isDerives`: [`equational_theories/Completeness.lean` lines 100-109](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/Completeness.lean#L100-L109) ([local copy](code/equational_theories/Completeness.lean))

```lean
theorem FreeMagmaWithLaws.isDerives {α β} {Γ : Ctx α} {E : MagmaLaw β} :
    FreeMagmaWithLaws β Γ ⊧ E → Nonempty (Γ ⊢' E) := by
  simp [satisfies, satisfiesPhi]
  intro eq; have h := eq (LfEmbed Γ)
  simp only [LfEmbed] at h
  repeat rw [FreeMagmaWithLaws.evalInMagmaIsQuot] at h
  have h' := Quotient.exact h
  simp [SetoidOfLaws.iff] at h'
  repeat rw [evalInMagma_leaf] at h'
  exact h'
```

### child `FreeMagmaWithLaws.isModel`: [`equational_theories/Completeness.lean` lines 123-129](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/Completeness.lean#L123-L129) ([local copy](code/equational_theories/Completeness.lean))

```lean
theorem FreeMagmaWithLaws.isModel {α} (β) (Γ : Ctx α) : FreeMagmaWithLaws β Γ ⊧ Γ := by
  intro E mem φ
  simp only [satisfiesPhi]
  have ⟨σ, eq_sig⟩ := (PhiAsSubst _ φ)
  rw [eq_sig]
  repeat rw [FreeMagmaWithLaws.evalInMagmaIsQuot]
  exact Quotient.sound ⟨derive'.SubstAx mem _⟩
```

### context `models`: [`equational_theories/MagmaLaw.lean` lines 96-98](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/MagmaLaw.lean#L96-L98) ([local copy](code/equational_theories/MagmaLaw.lean))

```lean
/-- `models Γ E`, or `Γ ⊧ E`, means that every magma `G` satisfying `Γ` also satisfies `E`. -/
def models {α β} (Γ : Ctx α) (E : MagmaLaw β) : Prop :=
  ∀ (G : Type) [Magma G], satisfiesSet G Γ → satisfies G E
```

### How the parts fit

The glue (the parent's one-line proof, line 158) is a single application
composed right-to-left:

```
Completeness'   h : Γ ⊧ E        ⊢  Nonempty (Γ ⊢' E)          (parent, the main theorem)
  = FreeMagmaWithLaws.isDerives (models_def'.1 h _ (FreeMagmaWithLaws.isModel β Γ))
      └── FreeMagmaWithLaws.isModel β Γ      : FreeMagmaWithLaws β Γ ⊧ Γ     (child)
      └── models_def'.1 h _ (isModel …)      : FreeMagmaWithLaws β Γ ⊧ E     (child, applied)
      └── FreeMagmaWithLaws.isDerives (…)    : Nonempty (Γ ⊢' E)             (child)
```

Reading the proof from the inside out: `FreeMagmaWithLaws.isModel β Γ` says the
free magma with laws is a model of the laws `Γ`; `models_def'.1 h _ (…)`
applies the forward direction of the interface lemma to `h : Γ ⊧ E`, giving
`FreeMagmaWithLaws β Γ ⊧ E`; `FreeMagmaWithLaws.isDerives (…)` turns that
satisfaction into the derivation `Nonempty (Γ ⊢' E)`. So the three direct
children are exactly the three lemmas cited on line 158.

The lemma graph (which lemma uses which):

```
Completeness' (156-158)
├── models_def' (147-154) ── the interface lemma (the iff that reformulates Γ ⊧ E)
│     ├── FreeMagmaWithLaws.isDerives (100-109)     ── satisfaction in the free magma ⇒ derivable
│     │     └── FreeMagmaWithLaws.evalInMagmaIsQuot (84-94)
│     ├── FreeMagmaWithLaws.models_iff_u (131-135)   ── universal form ⇔ free magma
│     │     ├── FreeMagmaWithLaws.isModel (123-129)   ── the free magma with laws satisfies Γ (line 133)
│     │     └── FreeMagmaWithLaws.isDerives (100-109) ── satisfaction in the free magma ⇒ derivable (line 134)
│     ├── Soundness'_u (11-30)                        ── derivability ⇒ satisfaction
│     └── models_toNat / satisfies_toNat / satisfies_equiv / satisfiesSet_equiv (MagmaLaw.lean)
├── FreeMagmaWithLaws.isDerives (100-109)
└── FreeMagmaWithLaws.isModel (123-129) ── the free magma with laws satisfies Γ
      └── PhiAsSubst (118-121)
            └── PhiAsSubst_aux (112-116) ── Classical.axiomOfChoice (the one use of choice)
```

Why each child is a good leaf:

- **`models_def'`** is the interface lemma, a self-contained statement
  (`Γ ⊧ E ↔ ∀ (G : Type*) [Magma G], G ⊧ Γ → G ⊧ E`) whose proof closes from
  named siblings (`FreeMagmaWithLaws.isDerives`, `FreeMagmaWithLaws.models_iff_u`,
  `Soundness'_u`) and four MagmaLaw rewrites (`models_toNat`, `satisfies_toNat`,
  `satisfies_equiv`, `satisfiesSet_equiv`). It is the only child that touches the
  `models` definition and the universe question; after it, the client never
  unfolds `models`.
- **`FreeMagmaWithLaws.isDerives`** is the converse of soundness for the free
  magma: a single `→` statement whose proof instantiates the satisfaction at
  `LfEmbed Γ` and unwinds the quotient (`Quotient.exact`, `SetoidOfLaws.iff`,
  `evalInMagma_leaf`), closing on the project lemma `evalInMagmaIsQuot`.
- **`FreeMagmaWithLaws.isModel`** is the "the constructed magma works" fact: for
  every `E ∈ Γ` it builds the substitution via `PhiAsSubst`, rewrites by
  `evalInMagmaIsQuot`, and closes with `Quotient.sound ⟨derive'.SubstAx mem _⟩`.

The result is the free-magma-with-laws proof of Birkhoff completeness: the
model is the quotient of the free magma by the laws, and every semantic
entailment is witnessed by a derivation.

## Why it is good

1. Lines 100-158 of `equational_theories/Completeness.lean` contain no
   closing-by-sorry token; the range (the parent and its three children) was
   machine-checked with `check_claims.py` (`no_sorry`).
2. The glue cites its children: `models_def'` occurs in the parent site (line
   158), and the same line also cites `FreeMagmaWithLaws.isDerives` and
   `FreeMagmaWithLaws.isModel` (the `glue-cites-children` check records all
   three).
3. The shape is small: the glue is 3 lines, the children 8, 10 and 7 lines,
   and the longest checked chain of project lemmas below the parent is
   `Completeness' → models_def' → FreeMagmaWithLaws.models_iff_u →
   FreeMagmaWithLaws.isModel → PhiAsSubst → PhiAsSubst_aux`, depth 5 (measured
   from the copied file, lines 84-158).
4. The authors name the result in its docstring (`/-- Birkhoff's completeness
   theorem -/`, line 156) and flag the proof's one non-constructive step with
   a comment (`-- Sadly, we falter here and use choice. Somewhat confident
   it's not needed.`, line 111), so the boundary of the interface lemma is
   exactly where the authors say the real content is.

In my opinion the detail worth copying is the division of labour: `models_def'`
is the only child that unfolds `models` and handles the universe lift from
`Type` to `Type*`; `isModel` and `isDerives` are reusable facts about the free
magma with laws that a bounded prover can prove independently, and the parent
is then a single line of composition.

Note on the rule survey: the interface-lemma move is not one of survey F §10's
18 numbered rules (the closest is rule 17, "memoise canonical statements
across branches"); this entry is evidence that the move is worth naming on its
own.

## When to use it, and when not

Use it when a semantic or bundled definition is universe-restricted or
otherwise not in a form the client can instantiate, and the client wants one
canonical re-expression — an API lemma — so it stops unfolding the bundled
definition. The goal shape is a semantic entailment `Γ ⊧ E` (an unbundled
`def models` over `Type`) that must be discharged by constructing a model in a
larger universe, with the target an existence of a derivation.

Avoid it when the entailment can be discharged directly at a model already in
`Type` (then no universe lift is needed and unfolding locally suffices), when
the re-expression is not yet the stable form clients consume (so it would be
rewritten again downstream), or when the two directions of the equivalence
need materially different arguments, in which case the iff hides real work
rather than removing it.

## Consequences

The move creates three obligations, one per direct child: the interface
equivalence `models_def'` (an iff, so two directions — the forward one still
needs the completeness core, the backward one is a soundness fact); `isModel`,
that the constructed magma satisfies the laws; and `isDerives`, that
satisfaction in the constructed magma yields a derivation. The proof relies on
the axiom of choice: `isModel` reaches `PhiAsSubst_aux`, whose proof uses
`Classical.axiomOfChoice` (the authors flag it at line 111). It pins the
reformulation: after `models_def'`, a client that wants entailment over `Type`
only must still go through the `Type*` form. The sibling theorem
`Completeness` (160-162) is the immediate specialisation to `derive`, so any
change to the `models` definition must keep `models_def'` in sync.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/blueprint-paper.yml, job build_project (step 'Build project') runs '~/.elan/bin/lake build equational_theories' on push to main with paths including '**/*.lean'; Completeness.lean is inside the equational_theories package; default branch is main; commit 8b87204d5b201e1cf6c69b8dcabb0558109bee00 | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: models_def'@equational_theories/Completeness.lean:158, FreeMagmaWithLaws.isDerives@equational_theories/Completeness.lean:158, FreeMagmaWithLaws.isModel@equational_theories/Completeness.lean:158; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 5 file(s) byte-identical at 8b87204d5b201e1cf6c69b8dcabb0558109bee00 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | no_sorry(equational_theories/Completeness.lean, 100-158) -> no_sorry: none of sorry, admit, axiom in equational_theories/Completeness.lean:100-158 | check_claims.py |
| 2 | verified | cites(equational_theories/Completeness.lean:156-158, models_def') -> cites: models_def' occurs at equational_theories/Completeness.lean:158 | check_claims.py |
| 3 | verified | read code/equational_theories/Completeness.lean 84-158: Completeness' 156-158 (3 lines); models_def' 147-154 (8); isDerives 100-109 (10); isModel 123-129 (7); glue line 158 'FreeMagmaWithLaws.isDerives (models_def'.1 h _ (FreeMagmaWithLaws.isModel β Γ))' cites all three; chain Completeness'->models_def'(152 uses isDerives)->isDerives(105 uses evalInMagmaIsQuot)->evalInMagmaIsQuot 84-94, depth 3 | verifier |
| 4 | verified | read code/equational_theories/Completeness.lean: line 156 '/-- Birkhoff's completeness theorem -/'; line 111 '-- Sadly, we falter here and use choice. Somewhat confident it's not needed.' | verifier |
| 5 | verified | read code/equational_theories/Completeness.lean 96-162: Completeness' = 156-158 (3 lines); models_def' = 147-154 (8); FreeMagmaWithLaws.isDerives = 100-109 (10); FreeMagmaWithLaws.isModel = 123-129 (7); glue line 158 'FreeMagmaWithLaws.isDerives (models_def'.1 h _ (FreeMagmaWithLaws.isModel β Γ))' cites all three children directly; chain Completeness'(158 -> models_def'.1) -> models_def'(152 -> models_iff_u.1) -> models_iff_u(133 -> isModel) -> isModel(126 -> PhiAsSubst) -> PhiAsSubst(120 -> PhiAsSubst_aux) -> PhiAsSubst_aux, 5 edges = depth 5 | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Prior depth objection fully addressed. Verified against copied code Completeness.lean 84-162 and MagmaLaw.lean 96-98: glue line 158 cites exactly the three children models_def', FreeMagmaWithLaws.isDerives, FreeMagmaWithLaws.isModel and nothing else; their statements in entry.json/README match the code verbatim; the glue type-checks/closes (isModel: FreeMagmaWithLaws beta Gamma |= Gamma; models_def'.1 h _ (..): FreeMagmaWithLaws beta Gamma |= E; isDerives (..): Nonempty (Gamma |-' E)). Shape numbers now right: direct_lemmas 3, glue_lines 3 (156-158), child_lines [8,10,7] (147-154, 100-109, 123-129), depth 5 = longest chain Completeness'->models_def'(152)->models_iff_u(131-135)->isModel(133)->PhiAsSubst(126)->PhiAsSubst_aux(120); I confirmed each citation; alternative chain via models_iff_u->isDerives->evalInMagmaIsQuot is depth 4, and Soundness'_u (11-30) is a leaf (induction over the derivation, no named project lemmas) so no longer chain exists. README lemma graph now has models_iff_u->isModel and models_iff_u->isDerives edges; Why-it-is-good point 3 says depth 5; claim 5 records the corrected chain. | reviewer-correctness |
| generality | accept | Move generalises past the example: applicability/use_when/avoid_when restate it in terms of any bundled or universe-restricted definition needing one canonical re-expression (API lemma) so clients stop unfolding, not just models. avoid_when is specific and honest (no lift needed when a Type model works; skip if the reformulation is not the stable client form; skip if the iff's two directions hide real work). Consequences are honest: the iff is two-directional with the forward still needing the completeness core, the proof depends on Classical.axiomOfChoice (flagged at line 111), the reformulation is pinned, and sibling Completeness (160-162) is the specialisation. 'Why each child is a good leaf' plus point 4 name the bounded-prover properties: self-contained single-direction statements that close on named siblings/project lemmas, one concern each (universe lift vs quotient unwind vs substitution), reusable, leaving a one-line parent. Verified against copied code 84-162 and MagmaLaw.lean 96-98. | reviewer-generality |
| provenance-licence | accept | Commit 8b87204d5b201e1cf6c69b8dcabb0558109bee00 is consistent across entry.json source/files/sites, every permalink, and sources/equational-theories/SOURCE.md; check_provenance.py reports 5 files byte-identical at that commit; recorded sha256/byte counts match the local code copies (Completeness 9008B, MagmaLaw 14231B, Magma 1436B, Homomorphisms 11972B, FreeMagma 10073B); licence Apache-2.0 in entry.json matches SOURCE.md ('Apache-2.0 (detected)') and upstream-LICENSE (Apache License 2.0); all cited line ranges (Completeness.lean 100-109, 123-129, 147-154, 156-158; MagmaLaw.lean 96-98) exist and match the README excerpts; SOURCE.md records the pin timestamp and attribution. Everything traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/teorth/equational_theories at commit `8b87204d5b201e1cf6c69b8dcabb0558109bee00`, under `Apache-2.0`; see the [source note](../../sources/equational-theories/SOURCE.md) for the licence text and attribution.
