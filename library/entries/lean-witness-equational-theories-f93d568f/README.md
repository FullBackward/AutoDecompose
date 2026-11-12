# Finite 8-entry magma-table witness that 854 implies neither 413 nor 1045

| | |
|---|---|
| Kind | instance |
| Move | witness |
| Language | lean |
| Status | accepted |
| Source | [equational-theories](../../sources/equational-theories/SOURCE.md) at `8b87204d5b20` |
| Licence | `Apache-2.0` |

## Intent

The existential goal `∃ (G : Type) (_ : Magma G), Facts G [854] [413, 1045]`
(there is a magma satisfying equation 854 but neither 413 nor 1045) is reduced
to a single finite 8-entry table. The table is named as the witness `e`; the
law and the cancellation property are taken from the greedy-extension accessors
`Extension.eq854` / `Extension.aux`, and the two refutations close by
evaluating the table with `fromList_eval` and one `cases` each.

## The decomposition

### parent `not_413_1045`: [`equational_theories/ManuallyProved/Equation854.lean` lines 506-527](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/ManuallyProved/Equation854.lean#L506-L527) ([local copy](code/equational_theories/ManuallyProved/Equation854.lean))

```lean
@[equational_result]
theorem not_413_1045 : ∃ (G : Type) (_ : Magma G), Facts G [854] [413, 1045] := by
  have ⟨e, he⟩ : ∃ e : Extension, e.1 = fromList
    [((0,0),2), ((0,1),0), ((0,2),0), ((1,2),3), ((2,0),2), ((2,1),2), ((2,3),2), ((3,2),3)] :=
    ⟨⟨_, fromList_ok⟩, rfl⟩
  refine ⟨GreedyMagma e, inferInstance, e.eq854, fun h => ?_, fun h => ?_⟩
  · have h21 := fromList_eval he 2 1 2
    have h123 := fromList_eval he 1 2 3
    have := h 1 2
    rw [show ((2 : GreedyMagma e) ◇ (1 : GreedyMagma e)) = 2 from h21,
        show ((1 : GreedyMagma e) ◇ (2 : GreedyMagma e)) = 3 from h123] at this
    cases e.aux this.symm
  · have h010 := fromList_eval he 0 1 0
    have h002 := fromList_eval he 0 0 2
    have h21 := fromList_eval he 2 1 2
    have h123 := fromList_eval he 1 2 3
    have := h 1 0
    rw [show ((0 : GreedyMagma e) ◇ (1 : GreedyMagma e)) = 0 from h010,
        show ((0 : GreedyMagma e) ◇ (0 : GreedyMagma e)) = 2 from h002,
        show ((2 : GreedyMagma e) ◇ (1 : GreedyMagma e)) = 2 from h21,
        show ((1 : GreedyMagma e) ◇ (2 : GreedyMagma e)) = 3 from h123] at this
    cases this
```

### child `fromList_ok`: [`equational_theories/ManuallyProved/Equation854.lean` lines 466-494](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/ManuallyProved/Equation854.lean#L466-L494) ([local copy](code/equational_theories/ManuallyProved/Equation854.lean))

```lean
theorem fromList_ok {S : List ((Nat × Nat) × Nat)}
    (sorted : S.IsChain (fun a b => lexLt a.1 b.1) := by decide)
    (eq854 : ∀ a ∈ S, ∀ b ∈ S, a.1.2 = b.1.2 →
      ∀ c ∈ S, c.1 = (b.2, a.2) → ((a.1.1, c.2), a.1.1) ∈ S := by decide)
    (eq8 : ∀ a ∈ S, a.1.1 = a.1.2 → ((a.1.1, a.2), a.1.1) ∈ S := by decide)
    (eq101 : ∀ a ∈ S, ∀ b ∈ S, a.2 = b.1.1 → a.1.1 = b.1.2 → ((a.1.1, b.2), a.1.1) ∈ S := by decide)
    (eq46155 : ∀ a ∈ S, ∀ b ∈ S, a.1.1 = b.1.1 → a.2 = b.1.2 → ((a.2, b.2), a.2) ∈ S := by decide)
    (eq378 : ∀ a ∈ S, ((a.2, a.1.2), a.2) ∈ S := by decide)
    (no_idem : ∀ a ∈ S, a.1.1 = a.2 → a.1.2 ≠ a.2 := by decide)
    (aux : ∀ a ∈ S, a.1.1 ≠ a.1.2 → ((a.1.1, a.2), a.1.1) ∉ S := by decide)
    (uniq_fac : ∀ a ∈ S, a.2 ≠ a.1.1 → ∀ b ∈ S, a.2 = b.2 → a.2 = b.1.1 ∨ a.1 = b.1 := by decide)
    (mono : ∀ a ∈ S, a.2 = a.1.1 ∨ a.1.1 < a.2 ∧ a.1.2 < a.2 := by decide) :
    (fromList S).OK where
  finite := List.finite_toSet S
  func h1 _ h2 := Decidable.by_contra fun h => by
    have hpw : List.Pairwise (fun a b : (ℕ × ℕ) × ℕ => a.1 ≠ b.1) S :=
      (List.isChain_iff_pairwise.1 sorted).imp (fun hab heq => by
        rcases hab with hab | ⟨_, hab⟩ <;> simp_all)
    have hsym : Symmetric (fun a b : (ℕ × ℕ) × ℕ => a.1 ≠ b.1) := fun _ _ => Ne.symm
    exact hpw.forall hsym h1 h2 (by rintro ⟨⟩; exact h rfl) rfl
  eq854 h1 h2 h3 := eq854 _ h1 _ h2 rfl _ h3 rfl
  eq8 h1 := eq8 _ h1 rfl
  eq101 h1 h2 := eq101 _ h1 _ h2 rfl rfl
  eq46155 h1 h2 := eq46155 _ h1 _ h2 rfl rfl
  eq378 h1 := eq378 _ h1
  no_idem h1 := no_idem _ h1 rfl rfl
  aux h1 h2 := Decidable.by_contra (aux _ h1 · h2)
  uniq_fac h1 h2 := Decidable.or_iff_not_imp_left.2 fun h => uniq_fac _ h1 h _ h2 rfl
  mono h1 := mono _ h1
```

### child `fromList_eval`: [`equational_theories/ManuallyProved/Equation854.lean` lines 496-499](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/ManuallyProved/Equation854.lean#L496-L499) ([local copy](code/equational_theories/ManuallyProved/Equation854.lean))

```lean
theorem fromList_eval {e : Extension} {S : List ((Nat × Nat) × Nat)} (hS : e.1 = fromList S)
    (a b c : Nat) (h : ((a, b), c) ∈ S := by decide) :
    haveI : Magma Nat := instMagma e; a ◇ b = c :=
  (Extension.base e (hS ▸ h)).symm
```

### child `Extension.eq854`: [`equational_theories/ManuallyProved/Equation854.lean` lines 442-443](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/ManuallyProved/Equation854.lean#L442-L443) ([local copy](code/equational_theories/ManuallyProved/Equation854.lean))

```lean
theorem Extension.eq854 : Equation854 (GreedyMagma e₀) :=
  (exists_extension e₀).choose_spec.1
```

### child `Extension.aux`: [`equational_theories/ManuallyProved/Equation854.lean` lines 445-446](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/ManuallyProved/Equation854.lean#L445-L446) ([local copy](code/equational_theories/ManuallyProved/Equation854.lean))

```lean
theorem Extension.aux : ∀ {x y : GreedyMagma e₀}, x ◇ (x ◇ y) = x → x = y :=
  (exists_extension e₀).choose_spec.2.1
```

### context `Extension.base`: [`equational_theories/ManuallyProved/Equation854.lean` lines 448-449](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/ManuallyProved/Equation854.lean#L448-L449) ([local copy](code/equational_theories/ManuallyProved/Equation854.lean))

```lean
theorem Extension.base : ∀ {x y z : GreedyMagma e₀}, z ∈ e₀.1 x y → z = x ◇ y :=
  (exists_extension e₀).choose_spec.2.2
```

### context `exists_extension`: [`equational_theories/ManuallyProved/Equation854.lean` lines 403-433](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/ManuallyProved/Equation854.lean#L403-L433) ([local copy](code/equational_theories/ManuallyProved/Equation854.lean))

```lean
theorem exists_extension :
    ∃ op : ℕ → ℕ → ℕ,
    (∀ x y z, x = op x (op (op y z) (op x z))) ∧
    (∀ {x y}, op x (op x y) = x → x = y) ∧
    (∀ {x y z}, z ∈ e₀.1 x y → z = op x y) := by
  classical
  have ⟨c, hc, h1, h2, h3⟩ := exists_greedy_chain (a := e₀)
    (task := fun x : _ × _ => {e | (e.1 x.1 x.2).Nonempty}) fun ⟨E, ok⟩ ⟨a, b⟩ => by
      if h : (E a b).Nonempty then exact ⟨_, le_rfl, h⟩ else
      let E1 : Extension1 := { E, ok, a, b, not_def := fun h' => h ⟨_, h'⟩ }
      exact ⟨⟨E1.next, E1.next_ok⟩, fun _ _ _ => (.base ·), _, .new⟩
  simp only [Subtype.exists, Prod.forall] at h3
  classical
  choose f hf1 hf2 op hop using h3
  refine ⟨op, fun x y z => ?_, fun {x y} h => ?_, fun {x y z} H => ?_⟩
  · let S : Finset _ := {(x,z), (y,z), (op y z, op x z), (x, op (op y z) (op x z))}
    have ⟨⟨e, he⟩, le⟩ := hc.directed.finset_le (hι := ⟨⟨_, h1⟩⟩)
      (S.image fun (a, b) => ⟨⟨f a b, hf1 a b⟩, hf2 a b⟩)
    replace le a (ha : a ∈ S) := Finset.forall_mem_image.1 le ha _ _ (hop a.1 a.2)
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, S] at le
    obtain ⟨xz, yz, yzxz, xyzxz⟩ := le
    exact e.2.func (e.2.eq854 xz yz yzxz) xyzxz
  · let S : Finset _ := {(x,y), (x, op x y)}
    have ⟨⟨e, he⟩, le⟩ := hc.directed.finset_le (hι := ⟨⟨_, h1⟩⟩)
      (S.image fun (a, b) => ⟨⟨f a b, hf1 a b⟩, hf2 a b⟩)
    replace le a (ha : a ∈ S) := Finset.forall_mem_image.1 le ha _ _ (hop a.1 a.2)
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, S] at le
    obtain ⟨xy, xxy⟩ := le
    rw [h] at xxy
    exact e.2.aux xy xxy
  · exact (hf1 ..).func (h2 _ (hf2 x y) _ _ H) (hop ..)
```

### context `GreedyMagma`: [`equational_theories/ManuallyProved/Equation854.lean` lines 435-440](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/ManuallyProved/Equation854.lean#L435-L440) ([local copy](code/equational_theories/ManuallyProved/Equation854.lean))

```lean
def GreedyMagma (_ : Extension) := ℕ

instance (n) : OfNat (GreedyMagma e₀) n := inferInstanceAs (OfNat Nat n)

noncomputable instance instMagma : Magma (GreedyMagma e₀) where
  op := (exists_extension e₀).choose
```

### context `fromList`: [`equational_theories/ManuallyProved/Equation854.lean` lines 451-451](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/ManuallyProved/Equation854.lean#L451-L451) ([local copy](code/equational_theories/ManuallyProved/Equation854.lean))

```lean
def fromList (S : List ((Nat × Nat) × Nat)) : PreExtension := fun a b => {c | ((a, b), c) ∈ S}
```

### context `PreExtension_OK`: [`equational_theories/ManuallyProved/Equation854.lean` lines 120-137](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/ManuallyProved/Equation854.lean#L120-L137) ([local copy](code/equational_theories/ManuallyProved/Equation854.lean))

```lean
variable (G) in
abbrev PreExtension := ℕ → ℕ → Set ℕ

structure PreExtension.OK (E : PreExtension) : Prop where
  finite : Set.Finite {x : (ℕ × ℕ) × ℕ | x.2 ∈ E x.1.1 x.1.2}
  func {x y} : Set.Subsingleton (E x y)
  eq854 {x y z xz yz yzxz} : xz ∈ E x z → yz ∈ E y z → yzxz ∈ E yz xz → x ∈ E x yzxz
  eq8 {x xx} : xx ∈ E x x → x ∈ E x xx
  eq101 {x y xy xyx} : xy ∈ E x y → xyx ∈ E xy x → x ∈ E x xyx
  eq46155 {x y xy xxy} : xy ∈ E x y → xxy ∈ E x xy → xy ∈ E xy xxy
  eq378 {x y xy} : xy ∈ E x y → xy ∈ E xy y
  no_idem {x} : x ∉ E x x
  aux {x y xy} : xy ∈ E x y → x ∈ E x xy → x = y
  uniq_fac {x y x' y' xy} : xy ∈ E x y → xy ∈ E x' y' → xy = x ∨ xy = x' ∨ (x, y) = (x', y')
  mono {x y xy} : xy ∈ E x y → xy = x ∨ x < xy ∧ y < xy

variable (G) in
abbrev Extension := {E : PreExtension // E.OK}
```

How the parts fit. The parent `not_413_1045` is an ∃-goal, and the glue is a
witness proof in three steps.

1. **Name the witness** (`have ⟨e, he⟩ … := ⟨⟨_, fromList_ok⟩, rfl⟩`, lines
   508-510). The witness is an `Extension e` whose underlying partial magma
   `e.1` equals `fromList` of the literal 8-entry table. The first component
   `fromList_ok` proves `(fromList S).OK` — that the table is a valid partial
   854 magma (finite, functional, and satisfying the ten `PreExtension.OK`
   side conditions) — and closes entirely by `decide` on the literal list.
2. **Supply the carrier, instance and law** (`refine ⟨GreedyMagma e,
   inferInstance, e.eq854, fun h => ?_, fun h => ?_⟩`, line 511). The carrier
   is `GreedyMagma e` (definitionally `ℕ`), its magma instance is
   `instMagma` whose `op` is `(exists_extension e₀).choose`, and the law is
   the accessor `e.eq854`, which closes by projecting
   `(exists_extension e₀).choose_spec.1`. This leaves two refutation goals.
3. **Close the two refutations.** Each is a negation; the glue assumes
   `h : Equation… G`, instantiates it at a concrete element, rewrites with
   `fromList_eval` table lookups, and hits a contradiction. For 413 it ends
   `cases e.aux this.symm` (line 517) — the cancellation accessor `Extension.aux`
   (`x ◇ (x ◇ y) = x → x = y`) turns the forced equality into `1 = 2`-style
   absurdity. For 1045 it ends `cases this` (line 527) — the four `fromList_eval`
   rewrites already produce a false numeral equality.

The lemma graph (each arrow is "is used by"):

```
not_413_1045 (parent)
 ├─ fromList_ok           ─ proves the 8-entry table is a valid PreExtension.OK
 ├─ Extension.eq854       ─ proves Equation854 (GreedyMagma e)
 ├─ Extension.aux         ─ cancellation x ◇ (x ◇ y) = x → x = y
 └─ fromList_eval         ─ table lookup a ◇ b = c
       └─ Extension.base  ─ z ∈ e.1 x y → z = x ◇ y
             └─ exists_extension ─ (all four accessors project (exists_extension e₀).choose_spec)
                   └─ exists_greedy_chain ─ (equational_theories/Mathlib/Order/Greedy.lean)
```

Why each child is a good leaf:

- `fromList_ok` is self-contained: its statement is `(fromList S).OK` for any
  list `S` whose ten properties are `decide`-able, and its proof closes field
  by field, each from its matching `by decide` hypothesis (lines 478-494).
- `fromList_eval` is self-contained: it turns a table membership
  `((a,b),c) ∈ S` into an evaluation `a ◇ b = c`, closing on the sibling
  accessor `Extension.base` (line 499).
- `Extension.eq854` and `Extension.aux` are self-contained statements that
  close by projecting out of `exists_extension`'s `choose_spec` — the law and
  the cancellation property are packaged as accessors so the witness proof
  never re-derives them.

## Why it is good

1. *(check)* The parent closes from its four direct children: the witness is
   justified by `⟨⟨_, fromList_ok⟩, rfl⟩` (line 510), the law by `e.eq854`
   (511), six `fromList_eval` lookups (512, 513, 518, 519, 520, 521), and the
   two refutations end `cases e.aux this.symm` (517) and `cases this` (527)
   — [Equation854.lean L506-L527](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/ManuallyProved/Equation854.lean#L506-L527).
2. *(measurement)* The proof is 21 lines and combines exactly 4 named lemmas
   from the same file; the longest project-lemma chain below it, traced by
   hand, is `fromList_eval → Extension.base → exists_extension →
   exists_greedy_chain` (depth 4) — glue at
   [L507-L527](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/ManuallyProved/Equation854.lean#L507-L527),
   chain bottom at [Greedy.lean L8-L43](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/Mathlib/Order/Greedy.lean#L8-L43).
3. *(author-statement)* The blueprint states the same plan: corollaries
   `854-413` (line 238) and `854-1045` (line 248) both name
   `Refutation_854.not_413_1045`, and the sketch says "Create a partial magma
   by imposing the laws … We then extend it to a global magma using extend-854"
   (lines 241-245), matching the `fromList` + `exists_extension` structure —
   [854.tex L231-L254](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/blueprint/src/chapter/854.tex#L231-L254).
4. *(known-use)* The same witness-table move is reused in `Equation73.lean`,
   which declares its own `fromList` (line 37), `fromList_ok` (248),
   `fromList_eval` (260) and uses them identically at 273, 280-281 —
   [Equation73.lean L37-L281](https://github.com/teorth/equational_theories/blob/8b87204d5b201e1cf6c69b8dcabb0558109bee00/equational_theories/ManuallyProved/Equation73.lean#L37-L281).

In my opinion the detail worth copying is the *split of labour*: the witness is
a bare literal table, its validity is an automated `decide` leaf, and the law
and cancellation are accessors over a separately-proved extension theorem, so
the witness proof itself is nearly flat.

## When to use it, and when not

Use it for an existential over a magma (or any algebraic structure) whose
refutations are determined by a small finite table with decidable side
conditions, and where the law and the auxiliary properties already exist as an
extension theorem exposed through accessors — then the witness proof is
`fromList_ok` + accessor projections + `fromList_eval` lookups.

Avoid it when the witness needs infinitely many entries or a side condition
that `decide` cannot discharge (then `fromList_ok` fails), when the law must be
re-derived inside the proof instead of imported as an accessor, or when the
refutation does not reduce to a table evaluation plus a single `cases`.

## Consequences

The witness `e` must be proved a valid `Extension`: `⟨⟨_, fromList_ok⟩, rfl⟩`
requires `(fromList S).OK`, i.e. all ten side conditions (sorted, eq854, eq8,
eq101, eq46155, eq378, no_idem, aux, uniq_fac, mono) of the 8-entry table to be
discharged by `decide` — the burden is shifted onto the decidability of the
literal list. The law (854) and the cancellation property are not re-derived
for the witness: they are taken from `exists_extension` via `.choose_spec`, so
the proof inherits a dependency on the greedy-extension theorem (which itself
rests on `exists_greedy_chain` and the ~170-line `next_ok` extension of
`PreExtension.OK`, lines 229-397). Failure modes: if `decide` cannot discharge one table side
condition, `fromList_ok` fails; if a queried triple is absent from `S`,
`fromList_eval`'s `by decide` membership fails; each refutation must reduce to
a single falsehood (`e.aux` contradiction for 413, a numeral contradiction for
1045).

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/blueprint-paper.yml, job build_project, step 'Build project': run: ~/.elan/bin/lake build equational_theories, triggered on push to main (default branch, paths include '**/*.lean'); this compiles equational_theories/ManuallyProved/Equation854.lean; pinned commit 8b87204d5b201e1cf6c69b8dcabb0558109bee00 is HEAD of main | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 3 file(s) byte-identical at 8b87204d5b201e1cf6c69b8dcabb0558109bee00 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read copied Equation854.lean L506-527: line 510 is '⟨⟨_, fromList_ok⟩, rfl⟩'; line 511 'refine ⟨GreedyMagma e, inferInstance, e.eq854, fun h => ?_, fun h => ?_⟩' supplies the law via e.eq854; six fromList_eval calls at 512, 513, 518, 519, 520, 521; refutations end 'cases e.aux this.symm' (517) and 'cases this' (527), closing the by-block | verifier |
| 2 | verified | Glue spans L507-527 (21 lines). 4 named lemmas cited: fromList_ok (510), fromList_eval (512/513/518-521), Extension.eq854 via e.eq854 (511), Extension.aux via e.aux (517), all in Equation854.lean. Chain: fromList_eval uses Extension.base (499) -> Extension.base = (exists_extension e0).choose_spec.2.2 (448-449) -> exists_extension uses exists_greedy_chain (409) -> exists_greedy_chain Greedy.lean L8-43; depth 4 | verifier |
| 3 | verified | Read copied blueprint/src/chapter/854.tex L231-254: corollary 854-413 at L238 and 854-1045 at L248 both carry \lean{Refutation_854.not_413_1045}; proof sketch L241-245 reads 'Create a partial magma by imposing the laws ... We then extend it to a global magma using \Cref{extend-854}', matching fromList + exists_extension (extend-854 is Refutation_854.Greedy.exists_extension, L231) | verifier |
| 4 | verified | Fetched Equation73.lean at 8b87204d5b201e1cf6c69b8dcabb0558109bee00: fromList at L37 (abbrev), fromList_ok at L248, fromList_eval at L260; used the same way at L273 '⟨⟨_, fromList_ok⟩, rfl⟩' and L280-281 'rw [fromList_eval he 1 x₁, fromList_eval he (x₁^(-1)) x₃, fromList_eval he (x₃ * x₁) x₄]' | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent statement verbatim matches code (Equation854.lean L507). The 4 children are exactly the named lemmas the glue cites: fromList_ok (L510), Extension.eq854 (L511 e.eq854), fromList_eval (6 calls L512,513,518,519,520,521), Extension.aux (L517 e.aux); no other named lemma is used. Closing methods match: fromList_ok field-by-field (finite:=List.finite_toSet L479; func via isChain_iff_pairwise L480-485; rest direct L486-494); fromList_eval via Extension.base (L499); eq854/aux via choose_spec (L443/L446). Glue closes both refutations with cases e.aux this.symm (L517) and cases this (L527), no sorry/admit. Shape numbers all correct: direct_lemmas=4; depth=4 chain fromList_eval->Extension.base->exists_extension->exists_greedy_chain verified (L499, L449, L409, Greedy.lean L8-L43); glue_lines=21 (507-527); child_lines=[29,4,2,2] match site ranges 466-494, 496-499, 442-443, 445-446. Minor non-blocking note: closed_by says '10 PreExtension.OK fields' but OK has 11 fields (finite,func + 9 law fields); only 9 are discharged from matching by-decide hypotheses. Does not affect the decomposition or shape. | reviewer-correctness |
| generality | accept | Move stated beyond the single example: applicability.goal_shape generalises to any existential over a magma whose witness is a finite literal table, and use_when/avoid_when are stated in general terms (small finite table with decidable side conditions, accessor-packaged law). When-not-to-use is specific and honest (infinite/undecidable table, law not already an accessor, refutation not a table eval plus single cases). Consequences are honest and specific, acknowledging the shifted burden onto decide-decidability and the inherited dependency on exists_extension/exists_greedy_chain/~170-line next_ok, plus concrete failure modes. Why-each-child-is-a-good-leaf names what makes leaves bounded-prover-friendly (self-contained, closes field-by-field by decide, closes by projecting choose_spec). Known-use (Equation73.lean) corroborates reuse within the project. | reviewer-generality |
| provenance-licence | accept | Provenance is fully traceable and consistent. check_provenance.py passes: 3 files byte-identical at pinned commit 8b87204d5b201e1cf6c69b8dcabb0558109bee00. Commit matches across entry.json source.commit, source.json, SOURCE.md, and every file/site permalink. Licence Apache-2.0 is consistent in entry.json, SOURCE.md (Licence detected), and source.json, and upstream-LICENSE is the genuine Apache-2.0 text. Copied files exist with matching byte sizes (Equation854.lean 22923, Greedy.lean 2426, 854.tex 32686). Site permalinks' line ranges (parent 506-527; children 466-494, 496-499, 442-443, 445-446; contexts) were checked against the local copy and match the excerpted code exactly. SOURCE.md links the repo, pinned commit, browse-at-commit URL, and licence file (LICENSE copied as upstream-LICENSE). | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/teorth/equational_theories at commit `8b87204d5b201e1cf6c69b8dcabb0558109bee00`, under `Apache-2.0`; see the [source note](../../sources/equational-theories/SOURCE.md) for the licence text and attribution.
