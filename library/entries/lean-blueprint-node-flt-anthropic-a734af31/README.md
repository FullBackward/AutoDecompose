# Blueprint node closing the Frey package: Wiles_Frey and solution

| | |
|---|---|
| Kind | instance |
| Move | blueprint-node |
| Language | lean |
| Status | draft |
| Source | [flt-anthropic](../../sources/flt-anthropic/SOURCE.md) at `6e837e753555` |
| Licence | `Apache-2.0` |

## Intent

Close the Frey package: from a Frey package `P` derive `False` by composing four
chapter theorems — `Mazur_Frey` (irreducibility), `frey_isModular` (modularity),
`level_lowering_to_two` (a nonzero weight-2 cusp form on Γ₀(2)) and
`S2_Gamma0_2_eq_zero` (no such form exists) — with no proof of its own beyond the
applications.

## The decomposition

### parent `solution`: [`P2M/Sol/S_FreyPackage_no_frey_package.lean` lines 139-147](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_no_frey_package.lean#L139-L147) ([local copy](code/P2M/Sol/S_FreyPackage_no_frey_package.lean))

```lean
theorem Wiles_Frey (P : FreyPackage) :
    ¬ GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p := fun hirr =>
  let ⟨f, hf⟩ := level_lowering_to_two P (frey_isModular P) hirr
  hf (ModularForm.S2_Gamma0_2_eq_zero f)

end FreyPackage

theorem solution (P : FreyPackage) : False :=
  FreyPackage.Wiles_Frey P (FreyPackage.Mazur_Frey P)
```

### child `FreyPackage.Mazur_Frey`: [`Theorems/Thm_FreyPackage_Mazur_Frey.lean` lines 70-70](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_FreyPackage_Mazur_Frey.lean#L70-L70) ([local copy](code/Theorems/Thm_FreyPackage_Mazur_Frey.lean))

```lean
theorem FreyPackage.Mazur_Frey (P : FreyPackage) : GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_Mazur_Frey.solution
```

### child `FreyPackage.frey_isModular`: [`Theorems/Thm_FreyPackage_frey_isModular.lean` lines 131-131](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_FreyPackage_frey_isModular.lean#L131-L131) ([local copy](code/Theorems/Thm_FreyPackage_frey_isModular.lean))

```lean
theorem FreyPackage.frey_isModular (P : FreyPackage) : P.freyCurve.IsModular := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_frey_isModular.solution
```

### child `FreyPackage.level_lowering_to_two`: [`Theorems/Thm_FreyPackage_level_lowering_to_two.lean` lines 131-131](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_FreyPackage_level_lowering_to_two.lean#L131-L131) ([local copy](code/Theorems/Thm_FreyPackage_level_lowering_to_two.lean))

```lean
theorem FreyPackage.level_lowering_to_two (P : FreyPackage) (hmod : P.freyCurve.IsModular) (hirr : GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p) : ∃ f : CuspForm (CongruenceSubgroup.Gamma0 2) 2, f ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_level_lowering_to_two.solution
```

### child `ModularForm.S2_Gamma0_2_eq_zero`: [`Theorems/Thm_ModularForm_S2_Gamma0_2_eq_zero.lean` lines 13-13](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_ModularForm_S2_Gamma0_2_eq_zero.lean#L13-L13) ([local copy](code/Theorems/Thm_ModularForm_S2_Gamma0_2_eq_zero.lean))

```lean
theorem ModularForm.S2_Gamma0_2_eq_zero (f : CuspForm (CongruenceSubgroup.Gamma0 2) 2) : f = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_S2_Gamma0_2_eq_zero.solution
```

How the parts fit. The node is the two declarations at the end of
`P2M/Sol/S_FreyPackage_no_frey_package.lean`: an auxiliary `Wiles_Frey` (lines
139-142) and the headline `solution` (lines 146-147). The dependency graph the
glue draws is:

```
solution (P : FreyPackage) : False
└── Wiles_Frey P (FreyPackage.Mazur_Frey P)          -- line 147
    ├── FreyPackage.Mazur_Frey P : GaloisRepIsIrreducible … P.freyCurve P.p
    │        -- irreducibility, feeds Wiles_Frey's hypothesis `hirr`
    └── (Wiles_Frey's body, lines 140-142)
        fun hirr =>
        let ⟨f, hf⟩ := level_lowering_to_two P (frey_isModular P) hirr
        hf (ModularForm.S2_Gamma0_2_eq_zero f)
```

Reading `Wiles_Frey`'s body: the hypothesis `hirr` is exactly the conclusion of
`Mazur_Frey`. It is combined with `frey_isModular P` (modularity) and fed to
`level_lowering_to_two`, which returns a witness `⟨f, hf⟩` with `hf : f ≠ 0`
for a weight-2 cusp form `f` on `Gamma0 2`. `ModularForm.S2_Gamma0_2_eq_zero f`
gives `f = 0`, so `hf` (which is `f ≠ 0`) applied to it is the contradiction.
`solution` then applies `Wiles_Frey` to `Mazur_Frey` and obtains `False`.

Each child is a good leaf because it is a self-contained statement whose proof,
in the copied file, closes on its own: every child is a one-line declaration
whose body is `by p2m_exact_reverting @_root_.P2MW.S_*.solution`, a delegation
to a Prove2Me solution in the sibling `P2M/Sol/S_*` file. None of the four
children needs any other child to typecheck; the only place they meet is the
glue, where their exact types line up: `Mazur_Frey`'s conclusion is
`Wiles_Frey`'s hypothesis, `frey_isModular` and `hirr` are exactly
`level_lowering_to_two`'s two premises, and `level_lowering_to_two`'s witness is
exactly what `S2_Gamma0_2_eq_zero` consumes.

The `p2m_export`/`p2m_open` lines immediately above (lines 134-137) are the
Prove2Me machinery that names the dependency: `p2m_export "FreyPackage"
"Mazur_Frey freyCurve p a frey_isModular level_lowering_to_two"` lists the
chapter theorems this node depends on, and `p2m_open` brings their names into
scope, which is what makes the one-line applications in the glue possible.

## Why it is good

1. The parent site is 9 lines long (`check`, the `lines(parent, 9)` form; see
   the permalink at lines 139-147).
2. The name `level_lowering_to_two` occurs in the parent site — the glue cites
   the level-lowering chapter theorem directly at line 141 (`check`,
   `cites(parent, level_lowering_to_two)`).
3. The parent site contains none of the Lean closing tokens `sorry`, `admit` or
   `axiom` (`check`, `no_sorry(...)` over lines 139-147).
4. The node is a 4-way composition: 4 direct chapter lemmas, glue 9 lines, and
   each of the four child sites a single line (declaration with its proof on the
   same line) (`measurement`; counts and line numbers in the claim's evidence).
5. The same node shape — a `Theorems/Thm_*.lean` declaration whose proof is
   `by p2m_exact_reverting @_root_.P2MW.S_*.solution` — is reused across the
   project, for example `Thm_fermatLastTheoremFive.lean` line 5 (`known-use`).

In my opinion the detail worth copying is not the mathematical content (which is
all in the four chapter theorems) but the *shape*: the closing node contains no
argument at all, only the applications that the published dependency graph
prescribes, so its correctness reduces to the four children's types matching.

## When to use it, and when not

Use it when the project already publishes the dependency graph — a blueprint
`\uses{}` or a Prove2Me `p2m_export` list — and the node you are formalising is a
closing node whose proof is a short composition of named chapter theorems with no
argument of its own in between. This is the cheap end of the theorem scale: once
the chapter theorems are proved, the closing node is nine lines of applications
and there is nothing left to prove.

Avoid it when the glue has real work to do between the lemmas (an actual
deduction, a choice, a case analysis), when the needed lemmas are not yet stated
as named declarations, or when the combination is not read off a published graph
but has to be discovered. The decomposition is only as good as the four
children's exact types: if `level_lowering_to_two`'s conclusion changed (a
different subgroup or weight), the closing node would fail to typecheck, and a
prover that merely re-runs this glue without re-deriving the chapter theorems has
not done the mathematics.

## Consequences

The move creates four obligations, each discharged by a separate chapter theorem
in its own file, and none by the glue itself. Correctness lives entirely in the
exact types of the four chapter theorems meeting in the glue; a mismatch in any
one (irreducibility conclusion vs. `Wiles_Frey` hypothesis, modularity and
irreducibility vs. `level_lowering_to_two`'s premises, the cusp-form witness vs.
`S2_Gamma0_2_eq_zero`'s argument) breaks the node at typecheck time. The glue
also depends on the `p2m_open`/`p2m_export` names resolving to the imported
theorems and on `let ⟨f, hf⟩ := …` matching the existential `level_lowering_to_two`
produces. The deeper solutions the four children delegate to (`P2M/Sol/S_*`)
are not copied here; a reader who wants the actual proofs follows the four
`p2m_exact_reverting` targets.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: FreyPackage.Mazur_Frey@P2M/Sol/S_FreyPackage_no_frey_package.lean:147, FreyPackage.frey_isModular@P2M/Sol/S_FreyPackage_no_frey_package.lean:141, FreyPackage.level_lowering_to_two@P2M/Sol/S_FreyPackage_no_frey_package.lean:141, ModularForm.S2_Gamma0_2_eq_zero@P2M/Sol/S_FreyPackage_no_frey_package.lean:142; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(parent, 9) -> lines: site parent has 9 lines | check_claims.py |
| 2 | verified | cites(parent, level_lowering_to_two) -> cites: level_lowering_to_two occurs at P2M/Sol/S_FreyPackage_no_frey_package.lean:141 | check_claims.py |
| 3 | verified | no_sorry(P2M/Sol/S_FreyPackage_no_frey_package.lean, 139-147) -> no_sorry: none of sorry, admit, axiom in P2M/Sol/S_FreyPackage_no_frey_package.lean:139-147 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/anthropics/fermats-last-theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, under `Apache-2.0`; see the [source note](../../sources/flt-anthropic/SOURCE.md) for the licence text and attribution.
