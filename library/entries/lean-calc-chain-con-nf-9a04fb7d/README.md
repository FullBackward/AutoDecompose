# Calc chain bounding beta-support orbits by the coding-function hypothesis (ConNF.card_supportOrbit_lt)

| | |
|---|---|
| Kind | instance |
| Move | calc-chain |
| Language | lean |
| Status | accepted |
| Source | [con-nf](../../sources/con-nf/SOURCE.md) at `edbce7eb9835` |
| Licence | `Apache-2.0 OR MIT` |

## Intent

The cardinal bound `#(SupportOrbit β) < #μ` — the number of β-support orbits is
strictly below the strong limit `μ`, given the inductive hypothesis that every
lower-type `CodingFunction δ` also stays below `μ` — is proved as a single
transitive chain of three lemmas already stated in the same file. The parent's
whole proof is the one line
`card_supportOrbit_lt'.trans_lt (card_weakSpec_of_card_spec (card_spec_of_card_codingFunction h))`:
inject support orbits into weak specifications, bound weak specifications by
specifications, and bound specifications from the coding-function hypothesis.

## The decomposition

### parent `card_supportOrbit_lt`: [`ConNF/Counting/CountSupportOrbit.lean` lines 197-199](https://github.com/leanprover-community/con-nf/blob/edbce7eb98351870f553cfab6ccb7cab327e4259/ConNF/Counting/CountSupportOrbit.lean#L197-L199) ([local copy](code/ConNF/Counting/CountSupportOrbit.lean))

```lean
theorem card_supportOrbit_lt (h : ∀ δ < β, [LeLevel δ] → #(CodingFunction δ) < #μ) :
    #(SupportOrbit β) < #μ :=
  card_supportOrbit_lt'.trans_lt (card_weakSpec_of_card_spec (card_spec_of_card_codingFunction h))
```

### child `card_supportOrbit_lt'`: [`ConNF/Counting/CountSupportOrbit.lean` lines 184-195](https://github.com/leanprover-community/con-nf/blob/edbce7eb98351870f553cfab6ccb7cab327e4259/ConNF/Counting/CountSupportOrbit.lean#L184-L195) ([local copy](code/ConNF/Counting/CountSupportOrbit.lean))

```lean
theorem card_supportOrbit_lt' : #(SupportOrbit β) ≤ #(WeakSpec β) := by
  have := WeakSpec.exists (β := β)
  choose σ hσ using this
  apply mk_le_of_injective (f := λ o ↦ σ o.out)
  intro o₁ o₂ ho
  dsimp only at ho
  have h₁ := hσ o₁.out
  have h₂ := hσ o₂.out
  rw [ho] at h₁
  obtain ⟨ρ, hρ⟩ := WeakSpec.exists_conv _ h₁ h₂
  have := congr_arg Support.orbit hρ
  rwa [Support.smul_orbit, SupportOrbit.out_orbit, SupportOrbit.out_orbit] at this
```

### child `card_weakSpec_of_card_spec`: [`ConNF/Counting/CountSupportOrbit.lean` lines 105-118](https://github.com/leanprover-community/con-nf/blob/edbce7eb98351870f553cfab6ccb7cab327e4259/ConNF/Counting/CountSupportOrbit.lean#L105-L118) ([local copy](code/ConNF/Counting/CountSupportOrbit.lean))

```lean
theorem card_weakSpec_of_card_spec (h : #(Spec β) < #μ) : #(WeakSpec β) < #μ := by
  rw [Cardinal.eq.mpr ⟨weakSpecEquiv⟩]
  simp only [mk_prod, Cardinal.lift_id]
  apply mul_lt_of_lt μ_isStrongLimit.aleph0_le (card_tree_lt κ_lt_μ)
  apply mul_lt_of_lt μ_isStrongLimit.aleph0_le (card_tree_lt κ_lt_μ)
  apply mul_lt_of_lt μ_isStrongLimit.aleph0_le
  · apply card_tree_lt
    rw [mk_set]
    exact μ_isStrongLimit.2 κ_lt_μ
  apply mul_lt_of_lt μ_isStrongLimit.aleph0_le
  · apply card_tree_lt
    rw [mk_set]
    exact μ_isStrongLimit.2 κ_lt_μ
  exact h
```

### child `card_spec_of_card_codingFunction`: [`ConNF/Counting/CountSupportOrbit.lean` lines 155-182](https://github.com/leanprover-community/con-nf/blob/edbce7eb98351870f553cfab6ccb7cab327e4259/ConNF/Counting/CountSupportOrbit.lean#L155-L182) ([local copy](code/ConNF/Counting/CountSupportOrbit.lean))

```lean
theorem card_spec_of_card_codingFunction
    (h : ∀ δ < β, [LeLevel δ] → #(CodingFunction δ) < #μ) : #(Spec β) < #μ := by
  rw [Cardinal.eq.mpr ⟨specEquiv⟩, mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  apply mul_lt_of_lt μ_isStrongLimit.aleph0_le
  · apply card_tree_lt
    apply card_enumeration_lt
    rw [Cardinal.eq.mpr ⟨atomCondEquiv⟩, mk_prod, mk_set, Cardinal.lift_id]
    exact mul_lt_of_lt μ_isStrongLimit.aleph0_le
      (μ_isStrongLimit.2 κ_lt_μ) (μ_isStrongLimit.2 κ_lt_μ)
  · apply card_tree_lt
    apply card_enumeration_lt
    rw [Cardinal.eq.mpr ⟨nearLitterCondEquiv⟩, mk_sum, Cardinal.lift_id, mk_sigma, Cardinal.lift_id]
    apply add_lt_of_lt μ_isStrongLimit.aleph0_le
    · rw [Cardinal.eq.mpr ⟨flexCondEquiv⟩, mk_set]
      exact μ_isStrongLimit.2 κ_lt_μ
    · refine (sum_lt_prod _ (λ _ ↦ #μ) ?_).trans_le ?_
      · intro P
        rw [Cardinal.eq.mpr ⟨inflexCondEquiv P.δ⟩]
        simp only [mk_prod, Cardinal.lift_id]
        apply mul_lt_of_lt μ_isStrongLimit.aleph0_le (h P.δ (P.hδ.trans_le P.A.le))
        apply mul_lt_of_lt μ_isStrongLimit.aleph0_le <;>
        · apply card_tree_lt
          change #(Set (κ × κ)) < #μ
          rw [mk_set, mk_prod, Cardinal.lift_id, mul_mk_eq_max, max_self]
          exact μ_isStrongLimit.2 κ_lt_μ
      · rw [prod_const, Cardinal.lift_id, Cardinal.lift_id]
        apply mk_pow_le_of_mk_lt_ord_cof μ_isStrongLimit
        exact card_inflexiblePath_lt β
```

How the parts fit. The parent `card_supportOrbit_lt` is pure glue: its proof
is the single transitive composition
`card_supportOrbit_lt'.trans_lt (card_weakSpec_of_card_spec (card_spec_of_card_codingFunction h))`,
which reads as a three-link chain
`#(SupportOrbit β) ≤ #(WeakSpec β) < #μ` with the middle bound supplied from
`#(Spec β) < #μ`, itself supplied from the hypothesis `h`. The lemma graph:

```text
card_supportOrbit_lt (CountSupportOrbit 197-199)          — glue: one trans_lt chain
├── card_supportOrbit_lt' (184-195)   #(SupportOrbit β) ≤ #(WeakSpec β)
│     ├── WeakSpec.exists (48)        choose σ hσ, the orbit ↦ weak-spec injection
│     └── WeakSpec.exists_conv (51)   the two orbits are equal
│           └── Support.exists_conv (ConNF/Strong/SpecSame.lean 209)
├── card_weakSpec_of_card_spec (105-118)   #(WeakSpec β) < #μ given #(Spec β) < #μ
│     └── weakSpecEquiv (98) → a product of four trees + Spec, each factor via card_tree_lt
└── card_spec_of_card_codingFunction (155-182)   #(Spec β) < #μ given the coding-function hypothesis
      └── specEquiv (120), atomCondEquiv/nearLitterCondEquiv/flexCondEquiv/inflexCondEquiv (127-153)
            → two enumeration trees, each via card_tree_lt / card_enumeration_lt; the inflexible
              half closes from h and card_inflexiblePath_lt β
```

The nesting of the glue is exactly the dependency order. `card_spec_of_card_codingFunction h`
is applied first and yields `#(Spec β) < #μ`; `card_weakSpec_of_card_spec` turns that
into `#(WeakSpec β) < #μ`; `card_supportOrbit_lt'` supplies the `≤` link, and
`.trans_lt` composes `≤` with `<` to obtain the strict bound.

Each child is a good leaf. `card_supportOrbit_lt'` is self-contained: it closes
by `apply mk_le_of_injective` on the function `λ o ↦ σ o.out` chosen by
`WeakSpec.exists`, and its injectivity obligation closes by
`WeakSpec.exists_conv` followed by a rewrite of the smul orbit — no cardinal
arithmetic at all. `card_weakSpec_of_card_spec` closes from the definitional
`weakSpecEquiv` (a `WeakSpec` is a product of four trees plus a `Spec`) and the
generic `card_tree_lt` bound on each tree factor, with the `Spec` factor handed
to it as its hypothesis `h`. `card_spec_of_card_codingFunction` is the deepest
leaf: it unfolds `Spec` into two enumeration trees via `specEquiv`, bounds each
with `card_tree_lt`/`card_enumeration_lt`, and only the inflexible half of the
near-litter conditions needs the coding-function hypothesis `h` (plus
`card_inflexiblePath_lt β`).

The three formal children correspond one-to-one to the blueprint's proof of
node `prop:card_supportOrbit`: its proof cites `prop:exists_weakSpec` and
`prop:exists_allowable_of_weakSpec` (both folded into `card_supportOrbit_lt'`)
and `prop:card_weakSpec` (the formal `card_weakSpec_of_card_spec`), which in turn
uses `prop:card_spec` (the formal `card_spec_of_card_codingFunction`).

## Why it is good

1. *(check)* No `sorry`, `admit`, `Admitted` or `axiom` occurs in
   [CountSupportOrbit.lean 1-201](https://github.com/leanprover-community/con-nf/blob/edbce7eb98351870f553cfab6ccb7cab327e4259/ConNF/Counting/CountSupportOrbit.lean) —
   every declaration in the decomposition closes.
2. *(check)* `card_supportOrbit_lt` is declared at
   [CountSupportOrbit.lean 197-199](https://github.com/leanprover-community/con-nf/blob/edbce7eb98351870f553cfab6ccb7cab327e4259/ConNF/Counting/CountSupportOrbit.lean#L197-L199).
3. *(check)* `card_supportOrbit_lt'` occurs in the parent site
   [CountSupportOrbit.lean 197-199](https://github.com/leanprover-community/con-nf/blob/edbce7eb98351870f553cfab6ccb7cab327e4259/ConNF/Counting/CountSupportOrbit.lean#L197-L199).
4. *(measurement)* The shape is minimal: the glue is 3 lines, the three children
   are 12, 14 and 28 lines, and the longest chain of project lemmas below the
   main theorem is 3 deep (`card_supportOrbit_lt → card_supportOrbit_lt' →
   WeakSpec.exists_conv → Support.exists_conv`). Counted by reading
   [CountSupportOrbit.lean](https://github.com/leanprover-community/con-nf/blob/edbce7eb98351870f553cfab6ccb7cab327e4259/ConNF/Counting/CountSupportOrbit.lean)
   (parent 197-199, children 184-195 / 105-118 / 155-182, `WeakSpec.exists_conv`
   51) and [SpecSame.lean 209](https://github.com/leanprover-community/con-nf/blob/edbce7eb98351870f553cfab6ccb7cab327e4259/ConNF/Strong/SpecSame.lean#L209).
5. *(author-statement)* The blueprint labels the theorem `prop:card_supportOrbit`
   and its proof reads "Define a function from the type of β-support orbits into
   the type of weak β-specifications by mapping a representative to a weak
   specification that specifies it; one will always exist by
   prop:exists_weakSpec. This is an injection: ..." and cites
   `prop:exists_weakSpec`, `prop:exists_allowable_of_weakSpec` and
   `prop:card_weakSpec` — exactly the three formal lemmas
   ([counting.tex 605-616](https://github.com/leanprover-community/con-nf/blob/edbce7eb98351870f553cfab6ccb7cab327e4259/blueprint/src/chapters/counting.tex#L605-L616)).

This entry supports survey F §10 rule 9 ("Calculational chains, one child per
link"): each link of the inequality chain is a single named lemma, and the
transitivity is checked by the chain itself (`trans_lt`).

In my opinion the detail worth copying is the *nesting as dependency order*:
`card_weakSpec_of_card_spec (card_spec_of_card_codingFunction h)` is the inner
`<` link feeding the outer `≤` link, so the proof reads as one nested term whose
order of application is exactly the order of the mathematical reduction.

## When to use it, and when not

Use it when a strict cardinal bound `#X < #μ` is assembled from inequalities
that are each already stated as a named lemma with a matching type — here an
injection `X ↪ Y`, a product bound on `Y` given a bound on one factor, and that
factor bounded from an inductive hypothesis — so the parent's proof is a single
`trans_lt` (or `calc`) composition. The chain here is a `≤` followed by a `<`,
which `trans_lt` composes into a strict bound; this is the natural shape for
"embed into an intermediate, then strictly bound the intermediate".

Avoid it when the intermediate bounds are not yet stated as lemmas (the parent
would have to prove them inline and the skeleton becomes one big proof); when
the chain needs a `≥` or `>` step that `trans_lt`/`calc` cannot compose
directly; or when the child lemmas carry side conditions the glue cannot
discharge by applying the next lemma down the chain (here the only side
condition is the theorem's own hypothesis `h`, threaded down unchanged).

## Consequences

The move creates one obligation per child hypothesis, each discharged by the
next lemma down the chain: `card_supportOrbit_lt'` needs no cardinal hypothesis;
`card_weakSpec_of_card_spec` needs `#(Spec β) < #μ`, discharged by
`card_spec_of_card_codingFunction`; `card_spec_of_card_codingFunction` needs the
coding-function hypothesis `h`, which is the theorem's own hypothesis and is
threaded through unchanged. Known failure mode: the chain is `≤` then `<`, so
`trans_lt` is the correct combinator; if a link were weakened to `≥`, or if a
`≤` link had to feed a lemma that demands a strict `<`, the composition would
fail and the strictness argument would have to be lifted into a separate child.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push_main.yml runs '~/.elan/bin/lake -Kenv=dev build ConNF' on push to main; ConNF/Counting/CountSupportOrbit.lean is part of the ConNF library target (checked imports via mk_all --lib ConNF --check); pinned commit edbce7eb98351870f553cfab6ccb7cab327e4259 is on main (API branches-where-head = [main]) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: card_supportOrbit_lt'@ConNF/Counting/CountSupportOrbit.lean:199, card_weakSpec_of_card_spec@ConNF/Counting/CountSupportOrbit.lean:199, card_spec_of_card_codingFunction@ConNF/Counting/CountSupportOrbit.lean:199; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at edbce7eb98351870f553cfab6ccb7cab327e4259 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | no_sorry(ConNF/Counting/CountSupportOrbit.lean, 1-201) -> no_sorry: none of sorry, admit, axiom in ConNF/Counting/CountSupportOrbit.lean:1-201 | check_claims.py |
| 2 | verified | declared(card_supportOrbit_lt, ConNF/Counting/CountSupportOrbit.lean, 197-199) -> declared: card_supportOrbit_lt is declared at ConNF/Counting/CountSupportOrbit.lean:197 | check_claims.py |
| 3 | verified | cites(card_supportOrbit_lt, card_supportOrbit_lt') -> cites: card_supportOrbit_lt' occurs at ConNF/Counting/CountSupportOrbit.lean:199 | check_claims.py |
| 4 | verified | read code/ConNF/Counting/CountSupportOrbit.lean: parent card_supportOrbit_lt at 197-199 = 3 lines (statement 2 + trans_lt glue 1); card_supportOrbit_lt' 184-195 = 12 lines; card_weakSpec_of_card_spec 105-118 = 14 lines; card_spec_of_card_codingFunction 155-182 = 28 lines; WeakSpec.exists_conv at line 51, its proof calls Support.exists_conv at line 56; code/ConNF/Strong/SpecSame.lean Support.exists_conv at line 209. Chain card_supportOrbit_lt -> card_supportOrbit_lt' (199 trans_lt) -> WeakSpec.exists_conv (193) -> Support.exists_conv (56) is 3 edges deep. All line ranges and counts match | verifier |
| 5 | verified | fetched blueprint/src/chapters/counting.tex at edbce7eb: node \label{prop:card_supportOrbit} with \uses{prop:exists_weakSpec,prop:exists_allowable_of_weakSpec,prop:card_weakSpec}; proof text 'Define a function from the type of β-support orbits into the type of weak β-specifications... one will always exist by prop:exists_weakSpec'; injectivity by prop:exists_allowable_of_weakSpec; bound by prop:card_weakSpec. Formal card_supportOrbit_lt' uses WeakSpec.exists (185) and WeakSpec.exists_conv (193), matching the blueprint | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent site (CountSupportOrbit.lean 197-199) is pure glue: a single card_supportOrbit_lt'.trans_lt (card_weakSpec_of_card_spec (card_spec_of_card_codingFunction h)), citing exactly the three children and no others. All three child statements and closing methods match the copied code: card_supportOrbit_lt' (184-195, mk_le_of_injective on sigma chosen via WeakSpec.exists, injectivity via WeakSpec.exists_conv then rwa smul_orbit/out_orbit); card_weakSpec_of_card_spec (105-118, weakSpecEquiv to four trees + Spec, four mul_lt_of_lt, trees via card_tree_lt, Spec by exact h); card_spec_of_card_codingFunction (155-182, specEquiv to two enumeration trees, flex/inflex split with h and card_inflexiblePath_lt). Proofs are complete (no sorry/admit/axiom in the ranges; sorry-scan pass recorded). Shape numbers are right: direct_lemmas=3 (exactly the three cited lemmas), glue_lines=3 (197-199), child_lines=[12,14,28] = 184-195, 105-118, 155-182, and depth=3 is the real chain card_supportOrbit_lt -> card_supportOrbit_lt' -> WeakSpec.exists_conv -> Support.exists_conv (SpecSame.lean 209, in namespace Support at lines 30-242). | reviewer-correctness |
| generality | accept | Move is stated generally: use_when/avoid_when turn the specific cardinal bound into the portable principle 'each link of the inequality chain is a named lemma with a matching type, parent is a single trans_lt (or calc) composition', and rule mapping cites survey F rule 9 (one child per link). When-not-to-use and consequences are honest and specific: I confirmed against the copied code that the glue is the single trans_lt composition, that h threads unchanged through card_spec_of_card_codingFunction, and that the Spec factor of card_weakSpec_of_card_spec closes by exact h (lines 105-118, 155-182, 197-199). The 'Each child is a good leaf' paragraph (README 128-139) says what makes them good leaves: self-contained closure by a named injection lemma with no cardinal arithmetic, definitional equivalence + generic card_tree_lt bound, one hypothesis threaded from the parent — i.e. small, closing from already-available lemmas, which is the bounded-prover property, though it does not use the phrase 'bounded prover'. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are all consistent and traceable. Commit edbce7eb98351870f553cfab6ccb7cab327e4259 matches across entry.json source.commit, sources/con-nf/source.json, SOURCE.md, and every permalink in README.md and entry.json (all blob URLs use the same 40-char hash; source note browse URL uses tree/ at the same hash). Licence 'Apache-2.0 AND MIT' matches entry.json, source.json, SOURCE.md and README.md; both upstream-LICENSE_APACHE (Apache 2.0) and upstream-LICENSE_MIT (MIT) are present under sources/con-nf. The two copied files are byte-identical to the pinned commit (sha256 d97967... for CountSupportOrbit.lean and 615753... for SpecSame.lean match entry.json files[], and check_provenance.py recorded pass '2 file(s) byte-identical at edbce7eb'). All cited line ranges in the README (parent 197-199, children 184-195/105-118/155-182, WeakSpec.exists 48, WeakSpec.exists_conv 51, weakSpecEquiv 98, specEquiv 120, SpecSame.lean Support.exists_conv 209 in namespace Support at 30) read back verbatim from the copied code. No stray files under the entry code dir (only the two declared paths). | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover-community/con-nf at commit `edbce7eb98351870f553cfab6ccb7cab327e4259`, under `Apache-2.0 OR MIT`; see the [source note](../../sources/con-nf/SOURCE.md) for the licence text and attribution. The copied files are outside `Old/`, so they are offered under either licence, at the user's choice.
