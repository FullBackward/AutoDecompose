# Induction on n for exactness of the inflation-restriction complex

| | |
|---|---|
| Kind | instance |
| Move | induction |
| Language | lean |
| Status | verified |
| Source | [classfieldtheory](../../sources/classfieldtheory/SOURCE.md) at `1e7f5dbe3835` |
| Licence | `Apache-2.0` |

## Intent

Prove that the inflation-restriction complex `inflationRestriction surj n M` is
exact in every cohomological degree `n`. The theorem is proved by
`induction n generalizing M`: the `zero` case is transported across the
isomorphism `isoHInfRes` to Mathlib's `H1InfRes_exact`, and the `succ` case is
transported across the dimension-shifting isomorphism `IsoNext`, itself
assembled from `δUpResIso`.

## The decomposition

### parent `inflation_restriction_exact`: [`ClassFieldTheory/Cohomology/Functors/InflationRestriction.lean` lines 143-163](https://github.com/kbuzzard/ClassFieldTheory/blob/1e7f5dbe38358bd37a0643bb0db2dd3a436e6cb7/ClassFieldTheory/Cohomology/Functors/InflationRestriction.lean#L143-L163) ([local copy](code/ClassFieldTheory/Cohomology/Functors/InflationRestriction.lean))

```lean
theorem inflation_restriction_exact (n : ℕ) {M : Rep R G}
    (hM : ∀ i : ℕ, i < n → IsZero (groupCohomology (M ↓ φ.ker.subtype) (i + 1))) :
    (inflationRestriction surj n M).Exact := by
  /-
  The proof is by induction on `n`. The `H¹` case (i.e. `n = 0`) is in Mathlib.
  For the inductive step, use the fact that the following diagram commutes by
  `infl_δ_naturality` and `rest_δ_naturality`.

  ` Hⁿ⁺¹(G⧸S,M^S)     ⟶    Hⁿ⁺¹(G,M)     ⟶    Hⁿ⁺¹(S,M)   `
  `       |                   |                   |       `
  ` Hⁿ(G⧸S,(up M)^S)  ⟶    Hⁿ(G,(up M))  ⟶    Hⁿ(S,up M)  `

  The vertical maps are the dimension-shifting isomorphisms.
  -/
  induction n generalizing M with
  | zero => exact ShortComplex.exact_of_iso (isoHInfRes surj 0 M).symm (H1InfRes_exact M φ.ker)
  | succ n ih =>
    specialize @ih (up.obj M) <| fun i hi ↦ by
      refine IsZero.of_iso ?_ (Rep.dimensionShift.δUpResIso _ φ.ker.subtype_injective _)
      exact hM (i + 1) (by omega)
    exact ShortComplex.exact_of_iso (IsoNext surj n M (hM 0 (by omega))) ih
```

### child `IsoNext`: [`ClassFieldTheory/Cohomology/Functors/InflationRestriction.lean` lines 89-101](https://github.com/kbuzzard/ClassFieldTheory/blob/1e7f5dbe38358bd37a0643bb0db2dd3a436e6cb7/ClassFieldTheory/Cohomology/Functors/InflationRestriction.lean#L89-L101) ([local copy](code/ClassFieldTheory/Cohomology/Functors/InflationRestriction.lean))

```lean
def IsoNext (n) (M : Rep R G) (hM : IsZero (H1 (M ↓ φ.ker.subtype))) :
    inflationRestriction surj n (up.obj M) ≅ inflationRestriction surj (n + 1) M :=
  ShortComplex.isoMk
    (@asIso _ _ _ _
      (δ (quotientToInvariantsFunctor'_shortExact_ofShortExact surj (shortExact_upSES M) hM)
        (n + 1) (n + 1 + 1) rfl)
      (isIso_δ_ofhM surj n M hM))
    (asIso (δ (shortExact_upSES M) (n + 1) (n + 1 + 1) rfl))
    (δUpResIso M φ.ker.subtype_injective (n + 1))
    (infl_δ_naturality surj (shortExact_upSES M)
      (quotientToInvariantsFunctor'_shortExact_ofShortExact surj (shortExact_upSES M) hM)
      (n + 1) (n + 1 + 1) rfl)
    (rest_δ_naturality (shortExact_upSES M) φ.ker.subtype (n + 1) (n + 1 + 1) rfl)
```

### child `isoHInfRes`: [`ClassFieldTheory/Cohomology/Functors/InflationRestriction.lean` lines 105-119](https://github.com/kbuzzard/ClassFieldTheory/blob/1e7f5dbe38358bd37a0643bb0db2dd3a436e6cb7/ClassFieldTheory/Cohomology/Functors/InflationRestriction.lean#L105-L119) ([local copy](code/ClassFieldTheory/Cohomology/Functors/InflationRestriction.lean))

```lean
def isoHInfRes (n : ℕ) (M : Rep R G) :
    inflationRestriction surj n M ≅ HInfRes M φ.ker (n + 1) :=
  ShortComplex.isoMk (resEquiv_inv (n + 1) Q (M.quotientToInvariants φ.ker)
    (QuotientGroup.quotientKerEquivOfSurjective φ surj)) (Iso.refl _) (Iso.refl _)
    (by
      rw [Iso.refl_hom, Category.comp_id, HInfRes_f, inflationRestriction_f, resEquiv_inv_hom,
        ← map_comp, infl_app]
      refine map_congr ?_ ?_ _
      · ext x
        simp [← MulEquiv.eq_symm_apply]
      · ext x
        simp [res_quotientToInvariantsFunctor'_ι, quotientToInvariantsFunctor'_obj_ρ])
    (by
      rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id, HInfRes_g,
        inflationRestriction_g, rest_app])
```

### child `δUpResIso`: [`ClassFieldTheory/Cohomology/Functors/UpDown.lean` lines 148-151](https://github.com/kbuzzard/ClassFieldTheory/blob/1e7f5dbe38358bd37a0643bb0db2dd3a436e6cb7/ClassFieldTheory/Cohomology/Functors/UpDown.lean#L148-L151) ([local copy](code/ClassFieldTheory/Cohomology/Functors/UpDown.lean))

```lean
def δUpResIso {S : Type u} [Group S] {φ : S →* G} (inj : Function.Injective φ) (n : ℕ) [NeZero n] :
    groupCohomology (up.obj M ↓ φ) n ≅ groupCohomology (M ↓ φ) (n + 1) := by
  have := isIso_δ_up_res M inj n
  apply asIso (δ ((shortExact_res φ).2 <| shortExact_upSES M) n (n + 1) rfl)
```

`inflation_restriction_exact` is the headline theorem of the file (exactness
of the inflation-restriction complex) and is proved by induction on the
cohomological degree `n`, generalising the representation `M`. Its two branches
close as follows.

- **`zero` branch** (`n = 0`): `exact ShortComplex.exact_of_iso (isoHInfRes
  surj 0 M).symm (H1InfRes_exact M φ.ker)`. The child `isoHInfRes` identifies
  `inflationRestriction surj 0 M` with Mathlib's `HInfRes M φ.ker 1`;
  `ShortComplex.exact_of_iso` (Mathlib) transports exactness across it; the
  base case `H1InfRes_exact` (Mathlib, not a project lemma) supplies exactness
  of `HInfRes`.
- **`succ` branch** (`n + 1`): the induction hypothesis `ih` is specialised at
  the shifted representation `up.obj M`, its own hypothesis `hM (i + 1)`
  discharged by `IsZero.of_iso` plus the child `δUpResIso` (one `omega` per
  index); then `exact ShortComplex.exact_of_iso (IsoNext surj n M (hM 0 (by
  omega))) ih` transports exactness along the child `IsoNext`, the isomorphism
  `inflationRestriction surj n (up.obj M) ≅ inflationRestriction surj (n + 1)
  M`.

Lemma graph (which project lemma uses which):

```
inflation_restriction_exact
 ├─ IsoNext ── δUpResIso ── isIso_δ_up_res      (UpDown.lean 143-146)
 │            └ isIso_δ_ofhM                    (InflationRestriction.lean 81-87)
 ├─ isoHInfRes
 └─ δUpResIso ─ isIso_δ_up_res                  (UpDown.lean 143-146)
```

`IsoNext` also cites Mathlib's `infl_δ_naturality` and `rest_δ_naturality` for
its two commutation fields; the longest checked chain of project lemmas below
the main theorem is `inflation_restriction_exact → IsoNext → δUpResIso →
isIso_δ_up_res` (depth 3).

Why each child is a good leaf:

- **`isoHInfRes`** is a self-contained statement
  (`inflationRestriction surj n M ≅ HInfRes M φ.ker (n + 1)`) whose proof
  closes on its own by `ShortComplex.isoMk` with two rewrite-chain commutation
  proofs; it packages the entire base case as a reduction to a known Mathlib
  fact.
- **`IsoNext`** is the step isomorphism; it closes by pure assembly —
  `ShortComplex.isoMk` of already-proved isos (`asIso (δ …)`, `δUpResIso`)
  plus the naturality lemmas `infl_δ_naturality` and `rest_δ_naturality` — so
  its proof is a term, not an argument.
- **`δUpResIso`** is the dimension shift
  `groupCohomology (up.obj M ↓ φ) n ≅ groupCohomology (M ↓ φ) (n + 1)` on the
  restricted representation; it closes in two lines by `have :=
  isIso_δ_up_res M inj n; apply asIso (δ …)`.

## Why it is good

1. The parent's proof cites `IsoNext` (claim 1, `check`, decided by
   `check_claims.py` against the copied file via `cites(parent, IsoNext)`).
2. No closing-by-sorry token occurs in the parent or its in-file children
   (claim 2, `check`, `no_sorry(ClassFieldTheory/Cohomology/Functors/InflationRestriction.lean, 89-163)`).
3. The parent site is 21 lines long — this is the `glue_lines` of the
   theorem-scale shape (claim 3, `check`, `lines(parent, 21)`).
4. The authors state the induction plan in the theorem's doc comment: "The
   proof is by induction on `n`. The `H¹` case (i.e. `n = 0`) is in Mathlib.
   For the inductive step, use the fact that the following diagram commutes by
   `infl_δ_naturality` and `rest_δ_naturality`. … The vertical maps are the
   dimension-shifting isomorphisms." (claim 4, `author-statement`, lines 146-156).
5. The sibling `inflation_restriction_mono` (lines 121-141) is proved by the
   same induction skeleton — `isoHInfRes` for `zero`, `IsoNext`/`δUpResIso`
   for `succ` — so the move is reused in-file for a different conclusion
   (`Mono` instead of `Exact`) (claim 5, `known-use`).

In my opinion the detail worth copying is how the *base case is delegated*:
the `zero` branch is not an argument but a reduction `isoHInfRes` to a lemma
that already exists elsewhere (`H1InfRes_exact`), and every `succ` step is
isomorphism transport, so the induction itself carries no cohomological
content — the content lives entirely in the two isomorphisms `IsoNext` and
`δUpResIso`.

## When to use it, and when not

Use it when the goal is a property of a complex indexed by a cohomological
degree `n` whose base case is already a named lemma, and whose step can be
phrased as transport of that property along an isomorphism (`IsoNext`) built
from dimension-shifting isos (`δUpResIso`); generalise the representation so
the induction hypothesis applies at the shifted object `up.obj M`.

Avoid it when the base case is not already available and would have to be
proved inside the `zero` branch, when the step needs a genuinely new argument
rather than isomorphism transport, or when the generalised hypothesis at
`up.obj M` cannot be discharged from the original hypothesis by a single
dimension shift.

## Consequences

Induction creates a `zero` base case and a `succ` step with an induction
hypothesis. The step obliges proving the hypothesis `hM` at the shifted
representation `up.obj M` (discharged here by `IsZero.of_iso` plus
`δUpResIso`, one `omega` per index), and the `generalizing M` means the IH
must be stated strongly enough to apply at `up.obj M`. Failure mode: if the
base case is not already a named lemma, the `zero` branch is where the real
content would go; if the step cannot be phrased as isomorphism transport
(`ShortComplex.exact_of_iso`), the shared skeleton breaks.

## Verification

<!-- verification:start -->
Status: **verified**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push.yml (Build Lean project) triggers on push to main and builds via lean-action; pinned commit 1e7f5dbe38358bd37a0643bb0db2dd3a436e6cb7 is a merge PR (#204) on the default branch main | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: IsoNext@ClassFieldTheory/Cohomology/Functors/InflationRestriction.lean:163, isoHInfRes@ClassFieldTheory/Cohomology/Functors/InflationRestriction.lean:158, δUpResIso@ClassFieldTheory/Cohomology/Functors/InflationRestriction.lean:161; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at 1e7f5dbe38358bd37a0643bb0db2dd3a436e6cb7 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, IsoNext) -> cites: IsoNext occurs at ClassFieldTheory/Cohomology/Functors/InflationRestriction.lean:163 | check_claims.py |
| 2 | verified | no_sorry(ClassFieldTheory/Cohomology/Functors/InflationRestriction.lean, 89-163) -> no_sorry: none of sorry, admit, axiom in ClassFieldTheory/Cohomology/Functors/InflationRestriction.lean:89-163 | check_claims.py |
| 3 | verified | lines(parent, 21) -> lines: site parent has 21 lines | check_claims.py |
| 4 | verified | doc comment lines 146-156 of InflationRestriction.lean reads 'The proof is by induction on n. The H1 case (i.e. n = 0) is in Mathlib. For the inductive step, use the fact that the following diagram commutes by infl_δ_naturality and rest_δ_naturality. ... The vertical maps are the dimension-shifting isomorphisms.' | verifier |
| 5 | verified | inflation_restriction_mono (lines 121-141): zero case 'exact ShortComplex.mono_f_of_iso (isoHInfRes surj 0 M).symm' (line 135), succ case uses Rep.dimensionShift.δUpResIso (line 140) and 'exact ShortComplex.mono_f_of_iso (IsoNext surj n M ...) ih' (line 141) | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | object | Decomposition, children, closing methods, closing, and direct_lemmas/glue_lines/child_lines all check out: parent inflation_restriction_exact is at InflationRestriction.lean 143-163 (21 lines), induction n generalizing M; zero branch uses isoHInfRes (105-119, 15 lines), succ branch uses IsoNext (89-101, 13 lines) and deltaUpResIso (UpDown.lean 148-151, 4 lines); all three children are exactly the project lemmas the parent cites, statements and closed_by match the code verbatim, both branches close with exact and there is no sorry. One shape number is wrong: shape.depth=3 understates the longest chain of project lemmas below the theorem. isIso_delta_up_res (UpDown.lean 143-146), which ends the entry's claimed longest chain, itself delegates to project lemmas isIso_delta_of_isZero and isZero_of_injective (lines 145-146), and the child IsoNext also uses isIso_delta_ofhM (InflationRestriction.lean 81-87) which uses coind1'_quotientToInvariants_trivialCohomology and isZero_of_trivialCohomology (lines 84,87); these are project lemmas (not Mathlib), so the true longest chain is at least inflation_restriction_exact -> IsoNext -> deltaUpResIso -> isIso_delta_up_res -> isZero_of_injective, depth >= 4. Fix: trace the chains to their project-lemma leaves and set shape.depth (and README's 'depth 3' text) to the true value (>= 4). | reviewer-correctness |
| generality | accept | Move stated beyond the example: goal_shape abstracts to 'P n on a complex indexed by degree n with a named base case and a step expressible as transport along an isomorphism', with also_known_as linking to Lean generalizing / Isabelle arbitrary, and a verified known-use (sibling inflation_restriction_mono, lines 121-141, confirmed in code to reuse the identical skeleton). When-not-to-use and consequences are honest and specific: avoid_when flags the three real failure modes (base case not already a named lemma, step needing a new argument rather than iso transport, generalised hypothesis at up.obj M not dischargeable by one dimension shift), and consequences states the obligations (proving hM at up.obj M via IsZero.of_iso + δUpResIso; generalizing M forces a strong enough IH). It does say what makes these good bounded-prover leaves: each child is a self-contained statement with a term-level (not tactic) proof delegating to already-proved lemmas (isoHInfRes packages the base case as a reduction to Mathlib's H1InfRes_exact; IsoNext is pure ShortComplex.isoMk assembly of asIso terms + naturality lemmas; δUpResIso closes in two lines via isIso_δ_up_res). | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are consistent and traceable. All four site permalinks point at pinned commit 1e7f5dbe38358bd37a0643bb0db2dd3a436e6cb7 with line ranges that match the copied files verbatim (parent 143-163, IsoNext 89-101, isoHInfRes 105-119 in InflationRestriction.lean; dUpResIso 148-151 in UpDown.lean). check_provenance.py reports both files byte-identical at that commit. Licence recorded as Apache-2.0 in entry.json, README and source.json/SOURCE.md; sources/classfieldtheory/upstream-LICENSE is the Apache-2.0 text. Byte counts in entry.json (7589, 16556) match the copied files. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/kbuzzard/ClassFieldTheory at commit `1e7f5dbe38358bd37a0643bb0db2dd3a436e6cb7`, under `Apache-2.0`; see the [source note](../../sources/classfieldtheory/SOURCE.md) for the licence text and attribution.
