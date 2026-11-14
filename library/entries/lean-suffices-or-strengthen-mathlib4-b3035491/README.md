# Suffices to the generalized equation for Fermat's Last Theorem n = 3

| | |
|---|---|
| Kind | instance |
| Move | suffices-or-strengthen |
| Language | lean |
| Status | accepted |
| Source | [mathlib4](../../sources/mathlib4/SOURCE.md) at `e1545ebed975` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T10:54:07Z |

## Intent

Reduce Fermat's Last Theorem for exponent 3 to the generalized equation
`FermatLastTheoremForThreeGen` over the cyclotomic integers — a stronger
statement in which the unit `u` is free — and close that generalized statement
by infinite descent on the multiplicity of `λ = ζ₃ − 1` in `c`. The move is the
first step: the main theorem applies the reduction lemma
`FermatLastTheoremForThree_of_FermatLastTheoremThreeGen` as a backward rule
(`Q → P`), then proves `Q` by descent.

## The decomposition

### parent `fermatLastTheoremThree`: [`Mathlib/NumberTheory/FLT/Three.lean` lines 751-771](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Mathlib/NumberTheory/FLT/Three.lean#L751-L771) ([local copy](code/Mathlib/NumberTheory/FLT/Three.lean))

```lean
public theorem fermatLastTheoremThree : FermatLastTheoremFor 3 := by
  let K := CyclotomicField 3 ℚ
  let hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have : NumberField K := IsCyclotomicExtension.numberField {3} ℚ _
  apply FermatLastTheoremForThree_of_FermatLastTheoremThreeGen hζ
  intro a b c u hc ha hb hcdvd coprime H
  let S' : FermatLastTheoremForThreeGen.Solution' hζ :=
  { a := a
    b := b
    c := c
    u := u
    ha := ha
    hb := hb
    hc := hc
    coprime := coprime
    hcdvd := hcdvd
    H := H }
  obtain ⟨S, -⟩ := FermatLastTheoremForThreeGen.exists_Solution_of_Solution' S'
  obtain ⟨Smin, hSmin⟩ := S.exists_minimal
  obtain ⟨Sfin, hSfin⟩ := Smin.exists_Solution_multiplicity_lt
  linarith [hSmin Sfin]
```

### child `FermatLastTheoremForThree_of_FermatLastTheoremThreeGen`: [`Mathlib/NumberTheory/FLT/Three.lean` lines 166-178](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Mathlib/NumberTheory/FLT/Three.lean#L166-L178) ([local copy](code/Mathlib/NumberTheory/FLT/Three.lean))

```lean
lemma FermatLastTheoremForThree_of_FermatLastTheoremThreeGen
    [NumberField K] [IsCyclotomicExtension {3} ℚ K] :
    FermatLastTheoremForThreeGen hζ → FermatLastTheoremFor 3 := by
  intro H
  refine fermatLastTheoremThree_of_three_dvd_only_c (fun a b c hc ha hb ⟨x, hx⟩ hcoprime h ↦ ?_)
  refine H a b c 1 (by simp [hc]) (fun hdvd ↦ ha ?_) (fun hdvd ↦ hb ?_) ?_ ?_ ?_
  · rwa [← Ideal.norm_dvd_iff (hζ.prime_norm_toInteger_sub_one_of_prime_ne_two' (by decide)),
      hζ.norm_toInteger_sub_one_of_prime_ne_two' (by decide)] at hdvd
  · rwa [← Ideal.norm_dvd_iff (hζ.prime_norm_toInteger_sub_one_of_prime_ne_two' (by decide)),
      hζ.norm_toInteger_sub_one_of_prime_ne_two' (by decide)] at hdvd
  · exact dvd_trans hζ.toInteger_sub_one_dvd_prime' ⟨x, by simp [hx]⟩
  · exact IsCoprime.intCast hcoprime
  · simpa using mod_cast h
```

### child `exists_Solution_of_Solution'`: [`Mathlib/NumberTheory/FLT/Three.lean` lines 360-373](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Mathlib/NumberTheory/FLT/Three.lean#L360-L373) ([local copy](code/Mathlib/NumberTheory/FLT/Three.lean))

```lean
lemma exists_Solution_of_Solution' : ∃ (S₁ : Solution hζ), S₁.multiplicity = S'.multiplicity := by
  obtain ⟨a, b, H, coprime, ha, hb, hab⟩ := ex_cube_add_cube_eq_and_isCoprime_and_not_dvd_and_dvd S'
  exact ⟨
  { a := a
    b := b
    c := S'.c
    u := S'.u
    ha := ha
    hb := hb
    hc := S'.hc
    coprime := coprime
    hcdvd := S'.hcdvd
    H := H
    hab := hab }, rfl⟩
```

### child `Solution.exists_minimal`: [`Mathlib/NumberTheory/FLT/Three.lean` lines 233-237](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Mathlib/NumberTheory/FLT/Three.lean#L233-L237) ([local copy](code/Mathlib/NumberTheory/FLT/Three.lean))

```lean
lemma Solution.exists_minimal : ∃ (S₁ : Solution hζ), S₁.isMinimal := by
  classical
  let T := {n | ∃ (S' : Solution hζ), S'.multiplicity = n}
  rcases Nat.find_spec (⟨S.multiplicity, ⟨S, rfl⟩⟩ : T.Nonempty) with ⟨S₁, hS₁⟩
  exact ⟨S₁, fun S'' ↦ hS₁ ▸ Nat.find_min' _ ⟨S'', rfl⟩⟩
```

### child `exists_Solution_multiplicity_lt`: [`Mathlib/NumberTheory/FLT/Three.lean` lines 735-738](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Mathlib/NumberTheory/FLT/Three.lean#L735-L738) ([local copy](code/Mathlib/NumberTheory/FLT/Three.lean))

```lean
theorem exists_Solution_multiplicity_lt :
    ∃ S₁ : Solution hζ, S₁.multiplicity < S.multiplicity := by
  obtain ⟨S', hS'⟩ := exists_Solution_of_Solution' (Solution'_descent S)
  exact ⟨S', hS' ▸ Solution'_descent_multiplicity_lt S⟩
```

### context `FermatLastTheoremForThreeGen`: [`Mathlib/NumberTheory/FLT/Three.lean` lines 158-163](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Mathlib/NumberTheory/FLT/Three.lean#L158-L163) ([local copy](code/Mathlib/NumberTheory/FLT/Three.lean))

```lean
/-- `FermatLastTheoremForThreeGen` is the statement that `a ^ 3 + b ^ 3 = u * c ^ 3` has no
nontrivial solutions in `𝓞 K` for all `u : (𝓞 K)ˣ` such that `¬ λ ∣ a`, `¬ λ ∣ b` and `λ ∣ c`.
The reason to consider `FermatLastTheoremForThreeGen` is to make a descent argument working. -/
def FermatLastTheoremForThreeGen : Prop :=
  ∀ a b c : 𝓞 K, ∀ u : (𝓞 K)ˣ, c ≠ 0 → ¬ λ ∣ a → ¬ λ ∣ b → λ ∣ c → IsCoprime a b →
    a ^ 3 + b ^ 3 ≠ u * c ^ 3
```

### context `Solution'`: [`Mathlib/NumberTheory/FLT/Three.lean` lines 185-195](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Mathlib/NumberTheory/FLT/Three.lean#L185-L195) ([local copy](code/Mathlib/NumberTheory/FLT/Three.lean))

```lean
structure Solution' where
  a : 𝓞 K
  b : 𝓞 K
  c : 𝓞 K
  u : (𝓞 K)ˣ
  ha : ¬ λ ∣ a
  hb : ¬ λ ∣ b
  hc : c ≠ 0
  coprime : IsCoprime a b
  hcdvd : λ ∣ c
  H : a ^ 3 + b ^ 3 = u * c ^ 3
```

### context `Solution`: [`Mathlib/NumberTheory/FLT/Three.lean` lines 201-203](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Mathlib/NumberTheory/FLT/Three.lean#L201-L203) ([local copy](code/Mathlib/NumberTheory/FLT/Three.lean))

```lean
/-- `Solution` is the same as `Solution'` with the additional assumption that `λ ^ 2 ∣ a + b`. -/
structure Solution extends Solution' hζ where
  hab : λ ^ 2 ∣ a + b
```

### context `Solution.multiplicity_isMinimal`: [`Mathlib/NumberTheory/FLT/Three.lean` lines 224-228](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Mathlib/NumberTheory/FLT/Three.lean#L224-L228) ([local copy](code/Mathlib/NumberTheory/FLT/Three.lean))

```lean
noncomputable def Solution.multiplicity := S.toSolution'.multiplicity

/-- We say that `S : Solution` is minimal if for all `S₁ : Solution`, the multiplicity of `λ` in
`S.c` is less or equal than the multiplicity in `S₁.c`. -/
def Solution.isMinimal : Prop := ∀ (S₁ : Solution hζ), S.multiplicity ≤ S₁.multiplicity
```

The lemma graph, read down the parent's 21 lines (751–771):

```
fermatLastTheoremThree (751-771)                                  the main theorem; the glue
├─ apply FermatLastTheoremForThree_of_FermatLastTheoremThreeGen hζ  (755)       reduce: it suffices to prove Q
├─ let S' : FermatLastTheoremForThreeGen.Solution' hζ := { … }      (757-767)   re-package the tuple
├─ obtain ⟨S, -⟩ := … exists_Solution_of_Solution' S'               (768)       Solution' ↦ Solution
├─ obtain ⟨Smin, hSmin⟩ := S.exists_minimal                         (769)       take a minimal Solution
├─ obtain ⟨Sfin, hSfin⟩ := Smin.exists_Solution_multiplicity_lt     (770)       descend to a smaller one
└─ linarith [hSmin Sfin]                                            (771)       contradict minimality
```

Each child is a self-contained named lemma whose proof closes on its own or
from named siblings:

- `FermatLastTheoremForThree_of_FermatLastTheoremThreeGen` (166–178) is the
  reduction: it states `Q → P` and is proved by `intro H; refine
  fermatLastTheoremThree_of_three_dvd_only_c …` then `refine H a b c 1 …`; its
  six subgoals close by `rwa`, `exact dvd_trans`, `exact IsCoprime.intCast` and
  `simpa using mod_cast`. A good leaf: the statement is exactly the "it is
  enough" step, and its proof only names earlier lemmas of the same file.
- `exists_Solution_of_Solution'` (360–373) turns a `Solution'` into a
  `Solution` with the same multiplicity; it closes from one sibling,
  `ex_cube_add_cube_eq_and_isCoprime_and_not_dvd_and_dvd`, then
  `exact ⟨{ … }, rfl⟩`.
- `Solution.exists_minimal` (233–237) gives a `Solution` of least multiplicity;
  it closes by `classical` well-ordering via `Nat.find_spec` and
  `Nat.find_min'`.
- `exists_Solution_multiplicity_lt` (735–738) is the descent step: it reuses
  `exists_Solution_of_Solution'` on `Solution'_descent S` and the sibling
  `Solution'_descent_multiplicity_lt`, giving a strictly smaller multiplicity.

The glue then closes by `linarith [hSmin Sfin]`: `hSmin` says `Smin` is
minimal, `hSfin` says `Sfin` has strictly smaller multiplicity, so `linarith`
derives the contradiction.

Below the children, the descent is a 7-lemma chain of project lemmas (the
`depth` recorded in `shape`): `exists_Solution_multiplicity_lt →
exists_Solution_of_Solution' → ex_cube_add_cube_eq_and_isCoprime_and_not_dvd_and_dvd →
lambda_sq_dvd_or_dvd_or_dvd → lambda_sq_dvd_c → lambda_pow_four_dvd_c_cube →
a_cube_b_cube_congr_one_or_neg_one`, which bottoms out at the imported
`lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd` (from
`Mathlib.NumberTheory.NumberField.Cyclotomic.Three`).

In my opinion the detail worth copying is that the strengthening and the
descent are kept apart: the reduction lemma hides the strengthening behind an
`apply`, and the descent is a self-contained `exists_Solution_multiplicity_lt`
the glue can call, so the 21-line glue reads as one `apply`, one structure
literal, three `obtain`s and a `linarith`.

## Why it is good

1. The parent is a real declaration, not a hole: a declaration named
   `fermatLastTheoremThree` starts at line 751 of
   `Mathlib/NumberTheory/FLT/Three.lean` (check, `declared`).
2. The decomposition is not closed by cheating: lines 166–771 (the parent and
   all four children) contain no `sorry`, `admit` or `axiom` (check,
   `no_sorry`).
3. The glue drives the descent from the descent child:
   `exists_Solution_multiplicity_lt` occurs in the parent site at line 770
   (check, `cites`).
4. The argument is a genuine tower, not a flat list: the longest chain of
   project lemmas below the main theorem has length 7 (measurement — the chain
   is listed with each link's line).
5. The authors state the move explicitly as "it is enough": the reduction
   lemma's doc comment and the module comment both say it (author-statement).

## When to use it, and when not

Use it when a goal `P` is proved more naturally as a stronger statement `Q`
(more variables, a free parameter, a generalized domain), and a lemma `Q → P`
exists or is cheap: the reduction is then a single `apply`/`suffices`. Avoid it
when `Q` is not actually true, when `Q` is no easier than `P`, or when the
backward step `Q → P` is the hard part — here the transfer of a `ℤ` solution
into `𝓞 K` needs the ideal-norm argument `Ideal.norm_dvd_iff` (lines 172–178),
and if that transfer were not already in the library the reduction would not be
"elementary". Also avoid strengthening so far that the descent's well-founded
measure (here the multiplicity of `λ` in `c`) stops existing.

## Consequences

Replacing `FermatLastTheoremFor 3` by `FermatLastTheoremForThreeGen hζ`
creates two obligations. First, the backward step must be faithful: `Q → P`
here passes through the ideal-norm transfer `Ideal.norm_dvd_iff` to move a `ℤ`
solution into `𝓞 K` (lines 172–178). Second, `Q` must be strong enough to carry
the descent — which is exactly why the unit `u` is left free, since the descent
cannot control `u` (module comment, lines 42–46). The descent adds its own
obligations: a well-founded measure (the multiplicity of `λ` in `c`), a
minimality lemma, and a step that constructs a strictly smaller `Solution`; if
any of these is missing, the `linarith [hSmin Sfin]` close (line 771) has
nothing to work with.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml (continuous integration; 'build mathlib' step runs lake-build-with-retry.sh Mathlib, building the whole Mathlib target which imports Mathlib/NumberTheory/FLT/Three.lean); commit e1545ebed97594477bbd88b2fe948ffce56e5af2 on default branch master | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: FermatLastTheoremForThree_of_FermatLastTheoremThreeGen@Mathlib/NumberTheory/FLT/Three.lean:755, exists_Solution_of_Solution'@Mathlib/NumberTheory/FLT/Three.lean:768, Solution.exists_minimal@Mathlib/NumberTheory/FLT/Three.lean:769, exists_Solution_multiplicity_lt@Mathlib/NumberTheory/FLT/Three.lean:770; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at e1545ebed97594477bbd88b2fe948ffce56e5af2 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(fermatLastTheoremThree, Mathlib/NumberTheory/FLT/Three.lean, 748-772) -> declared: fermatLastTheoremThree is declared at Mathlib/NumberTheory/FLT/Three.lean:751 | check_claims.py |
| 2 | verified | no_sorry(Mathlib/NumberTheory/FLT/Three.lean, 166-771) -> no_sorry: none of sorry, admit, axiom in Mathlib/NumberTheory/FLT/Three.lean:166-771 | check_claims.py |
| 3 | verified | cites(parent, exists_Solution_multiplicity_lt) -> cites: exists_Solution_multiplicity_lt occurs at Mathlib/NumberTheory/FLT/Three.lean:770 | check_claims.py |
| 4 | verified | chain of 7 calls confirmed in copied Three.lean: L737 exists_Solution_multiplicity_lt -> exists_Solution_of_Solution'; L361 -> ex_cube_add_cube_eq_and_isCoprime_and_not_dvd_and_dvd; L344 -> lambda_sq_dvd_or_dvd_or_dvd; L331 -> lambda_sq_dvd_c; L281 -> lambda_pow_four_dvd_c_cube; L269 -> a_cube_b_cube_congr_one_or_neg_one; L244 -> lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd (imported, public-import Mathlib.NumberTheory.NumberField.Cyclotomic.Three at L9, not declared in file) | verifier |
| 5 | verified | L165 doc comment: "To prove FermatLastTheoremFor 3, it is enough to prove FermatLastTheoremForThreeGen"; L39 module comment: "In particular it is enough to prove that no Solution exists" | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent fermatLastTheoremThree is at 751-771 (grep: 'public theorem' =751, linarith =771); glue cites exactly the 4 children at 755/768/769/770; each child's statement and closing method match code (166-178 reduce Q->P; 360-373 via ex_cube_add_cube_eq...; 233-237 via Nat.find; 735-738 via Solution'_descent); closes by linarith [hSmin Sfin], no sorry in 166-771. Shape numbers correct: glue_lines=21 (751-771), child_lines=[13,14,5,4] matching the four site ranges, direct_lemmas=4, depth=7 chain verified line-by-line (737->361->344->331->281->269->244). | reviewer-correctness |
| generality | accept | Move generalizes: applicability + When-to-use abstract FLT-n=3 to 'prove P by applying backward rule Q->P then proving stronger Q (free parameter u, wider domain)'. When-not-to-use and consequences are honest and specific, and I confirmed the cited code: module comment (42-46) says 'we cannot control the unit u... reason why we need the generalized equation'; doc comment (165) says 'it is enough to prove FermatLastTheoremForThreeGen'; the avoid_when caveat correctly points to the non-trivial ideal-norm transfer Ideal.norm_dvd_iff (172-178). Leaf quality is stated: children are 'self-contained named lemma[s] whose proof closes on its own or from named siblings', the reduction lemma is explicitly 'a good leaf' (statement is exactly the step; proof only names earlier lemmas), and the opinion paragraph notes strengthening/descent are kept apart so the 21-line glue is one apply + three obtains + linarith. This is the bounded-prover leaf property (small self-contained statement, short proof naming only siblings) though 'bounded prover' is not named verbatim. | reviewer-generality |
| provenance-licence | accept | Provenance check passes: 1 file byte-identical at e1545ebed97594477bbd88b2fe948ffce56e5af2. Commit, URL, licence (Apache-2.0) consistent across entry.json source/files/sites, README, sources/mathlib4/source.json and SOURCE.md; upstream-LICENSE is Apache 2.0. Copied Three.lean sha256 01db065f... matches files[0].sha256 and bytes 38263; permalinks well-formed (commit, path, line ranges match the sites; parent 751-771 excerpt matches copied file). | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover-community/mathlib4 at commit `e1545ebed97594477bbd88b2fe948ffce56e5af2`, under `Apache-2.0`; see the [source note](../../sources/mathlib4/SOURCE.md) for the licence text and attribution.
