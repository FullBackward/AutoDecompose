# Fermat's last theorem for p ≥ 5 from a counterexample via the Frey package

| | |
|---|---|
| Kind | instance |
| Move | other |
| Language | lean |
| Status | draft |
| Source | [flt-anthropic](../../sources/flt-anthropic/SOURCE.md) at `6e837e753555` |
| Licence | `Apache-2.0` |

## Intent

Prove Fermat's Last Theorem for primes `p ≥ 5` by contradiction, split into two
project theorems that meet only at an intermediate object: a counterexample
`a^p + b^p = c^p` is turned into a **Frey package** (construction), and a Frey
package is impossible (refutation). The main proof is a five-line glue that
`obtain`s the package and immediately destroys it.

## The decomposition

### parent `solution`: [`P2M/Sol/S_FreyPackage_fermatLastTheoremFor_of_five_le.lean` lines 131-135](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_fermatLastTheoremFor_of_five_le.lean#L131-L135) ([local copy](code/P2M/Sol/S_FreyPackage_fermatLastTheoremFor_of_five_le.lean))

```lean
theorem solution (p : ℕ) (pp : p.Prime) (hp5 : 5 ≤ p) : FermatLastTheoremFor p := by
  rw [fermatLastTheoremFor_iff_int]
  intro a b c ha hb hc heq
  obtain ⟨P⟩ := FreyPackage.of_counterexample a b c ha hb hc p pp hp5 heq
  exact P.no_frey_package
```

This is the whole theorem. Note that the name at this site is the generic
`solution`: the public, citable statement is the one-theorem-per-file object
`FreyPackage.fermatLastTheoremFor_of_five_le`
([`Theorems/Thm_FreyPackage_fermatLastTheoremFor_of_five_le.lean`](code/Theorems/Thm_FreyPackage_fermatLastTheoremFor_of_five_le.lean)),
which delegates to this `solution` through the project's `p2m_exact_reverting`
tactic. The glue is the `solution` theorem's `by` block.

### child `FreyPackage.of_counterexample`: [`Theorems/Thm_FreyPackage_of_counterexample.lean` lines 6-6](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_FreyPackage_of_counterexample.lean#L6-L6) ([local copy](code/Theorems/Thm_FreyPackage_of_counterexample.lean))

```lean
theorem FreyPackage.of_counterexample (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (p : ℕ) (pp : p.Prime) (hp5 : 5 ≤ p) (H : a ^ p + b ^ p = c ^ p) : Nonempty FreyPackage := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_of_counterexample.solution
```

### child `FreyPackage.no_frey_package`: [`Theorems/Thm_FreyPackage_no_frey_package.lean` lines 129-129](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_FreyPackage_no_frey_package.lean#L129-L129) ([local copy](code/Theorems/Thm_FreyPackage_no_frey_package.lean))

```lean
theorem FreyPackage.no_frey_package (P : FreyPackage) : False := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_no_frey_package.solution
```

### context `of_counterexample_solution`: [`P2M/Sol/S_FreyPackage_of_counterexample.lean` lines 70-73](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_of_counterexample.lean#L70-L73) ([local copy](code/P2M/Sol/S_FreyPackage_of_counterexample.lean))

```lean
theorem solution (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (p : ℕ) (pp : p.Prime) (hp5 : 5 ≤ p) (H : a ^ p + b ^ p = c ^ p) :
    Nonempty FreyPackage :=
  FreyPackage.of_counterexample a b c ha hb hc p pp hp5 H
```

### context `Wiles_Frey_solution`: [`P2M/Sol/S_FreyPackage_no_frey_package.lean` lines 139-147](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_no_frey_package.lean#L139-L147) ([local copy](code/P2M/Sol/S_FreyPackage_no_frey_package.lean))

```lean
theorem Wiles_Frey (P : FreyPackage) :
    ¬ GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p := fun hirr =>
  let ⟨f, hf⟩ := level_lowering_to_two P (frey_isModular P) hirr
  hf (ModularForm.S2_Gamma0_2_eq_zero f)

end FreyPackage

theorem solution (P : FreyPackage) : False :=
  FreyPackage.Wiles_Frey P (FreyPackage.Mazur_Frey P)
```

### How the parts fit

The glue combines the two children in a construct-then-refute pattern:

```
solution (FermatLastTheoremFor p, p ≥ 5)          — parent, 5-line glue
  rw [fermatLastTheoremFor_iff_int]               — restate over ℤ, so the counterexample is an equality
  intro a b c ha hb hc heq                        — assume a counterexample a^p + b^p = c^p
  obtain ⟨P⟩ := FreyPackage.of_counterexample …   — child 1: build the witness (a FreyPackage)
  exact P.no_frey_package                         — child 2: refute the witness → False
```

The two children meet *only* at the `FreyPackage` type — neither mentions the
other, and neither mentions the parent's conclusion. That is the point of the
decomposition: each half can be developed, and even proved, independently.

Each child is a **good leaf** for a different reason:

- `FreyPackage.of_counterexample` is the *construction*. Its conclusion
  `Nonempty FreyPackage` is exactly what the glue needs, and its proof is a
  self-contained normalisation chore (make the triple coprime, make `b` even,
  force `a ≡ 3 mod 4`, then assemble the structure field by field) — the 55-line
  body in `P2M/Sol/S_FreyPackage_of_counterexample.lean` lines 12-66. It closes
  without any deep number theory, so it is a leaf a bounded prover can be given
  whole.
- `FreyPackage.no_frey_package` is the *refutation*. Its conclusion `False`
  hides the entire hard direction: `solution` composes
  `FreyPackage.Wiles_Frey P (FreyPackage.Mazur_Frey P)` — modularity of the Frey
  curve plus level lowering (Wiles), applied against Mazur's theorem — and the
  glue never has to see any of it. It is a leaf because the argument is
  self-contained behind the single interface `FreyPackage → False`.

The mechanism that makes this layering work is the project's
`p2m_exact_reverting` tactic ([`P2M/Util.lean`](code/P2M/Util.lean) lines 4-16):
it reverts every hypothesis variable, elaborates the given term against the
target type, and errors if any metavariable is left unassigned. Each
one-theorem-per-file statement object in `Theorems/` therefore *is* a
declaration whose proof is exactly the delegation to its `P2M/Sol/S_*.lean`
solution module, and whose `import` lines are its citation set.

## Why it is good

1. **The parent glue is 5 lines long.** (`check`, [`#L131-L135`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_fermatLastTheoremFor_of_five_le.lean#L131-L135)). The whole headline theorem is two citations plus a reformulation and an `intro`.
2. **The glue cites the construction child** `FreyPackage.of_counterexample` at [`#L134`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_fermatLastTheoremFor_of_five_le.lean#L134) (`check`).
3. **The glue cites the refutation child** `FreyPackage.no_frey_package` at [`#L135`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_fermatLastTheoremFor_of_five_le.lean#L135) (`check`).
4. **Each child is a declared theorem in its own file** — the `statement-object` layout, one theorem per file with its `import`s as its citation graph ([`Thm_FreyPackage_no_frey_package.lean#L129`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_FreyPackage_no_frey_package.lean#L129); `check`). This is what lets the two halves be assigned to separate provers.
5. **The shape is `{direct_lemmas: 2, depth: 3, glue_lines: 5, child_lines: [1, 1]}`** (`measurement`): two lemmas in five lines of glue, each child a one-line delegation, and the deepest chain I traced is three project lemmas below the main theorem (`solution → no_frey_package → S_FreyPackage_no_frey_package.solution → FreyPackage.Wiles_Frey`).

*Opinion (not a claim):* the beauty of this move is that the hardest part of
the whole project — Wiles's modularity argument — is compressed into a single
leaf with the trivial-looking statement `FreyPackage → False`. The glue, and
everyone reading it, never has to know how hard that leaf is.

### Survey F rule mapping

The move is `other` because none of the standard moves names it: it is a
**construct-then-refute** split, the FLT proof's signature (Frey's curve + the
Serre–Ribet level-lowering + Wiles's modularity theorem). It *supports* survey F
§10 rule 8 (witnesses as templates) mechanically: the glue's
`obtain ⟨P⟩ := FreyPackage.of_counterexample …` turns the existential fact
`Nonempty FreyPackage` into the named context `P`, and both children are
parameterised over that named witness rather than containing an unfixed one.

## When to use it, and when not

Use it when the proof is a contradiction that needs a **substantial mediating
object** — one whose construction and whose impossibility are each deep enough
to deserve a named theorem, and which lets the two halves be built independently
(here, by different bodies of work: the curve construction versus modularity +
level lowering). It is the right shape when you want the hard argument isolated
behind a one-line interface the main proof can ignore.

Do not use it when the intermediate object adds no information — i.e. the two
lemmas could meet directly on the hypotheses — or when only one of the two
halves is non-trivial (then it is a `suffices-or-strengthen`, not a two-lemma
glue). It also fails when the object's fields cannot be pinned down as a stable
structure both sides agree on, since the two lemmas are coupled precisely
through those fields.

## Consequences

The move creates two obligations that meet *only* at the intermediate type: the
constructor must produce the object from the counterexample's hypotheses, and
the refuter must consume the object to reach `False`. Because the coupling is
through the object's fields (the curve, the prime, the modularity invariants),
extending or weakening the structure forces both sides to be revisited. The two
known failure modes are the object being **too weak to refute** (you must add
invariants to its structure) or **too strong to construct** (it needs hypotheses
the counterexample cannot supply).

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: FreyPackage.of_counterexample@P2M/Sol/S_FreyPackage_fermatLastTheoremFor_of_five_le.lean:134, FreyPackage.no_frey_package@P2M/Sol/S_FreyPackage_fermatLastTheoremFor_of_five_le.lean:135; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(solution, 5) -> lines: site solution has 5 lines | check_claims.py |
| 2 | verified | cites(solution, FreyPackage.of_counterexample) -> cites: FreyPackage.of_counterexample occurs at P2M/Sol/S_FreyPackage_fermatLastTheoremFor_of_five_le.lean:134 | check_claims.py |
| 3 | verified | cites(solution, FreyPackage.no_frey_package) -> cites: FreyPackage.no_frey_package occurs at P2M/Sol/S_FreyPackage_fermatLastTheoremFor_of_five_le.lean:135 | check_claims.py |
| 4 | verified | declared(FreyPackage.no_frey_package, Theorems/Thm_FreyPackage_no_frey_package.lean, 129-129) -> declared: FreyPackage.no_frey_package is declared at Theorems/Thm_FreyPackage_no_frey_package.lean:129 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/anthropics/fermats-last-theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, under `Apache-2.0`; see the [source note](../../sources/flt-anthropic/SOURCE.md) for the licence text and attribution.
