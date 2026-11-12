# Strong induction on s+t for the Erdos-Szekeres binomial bound C(s+t, s)

| | |
|---|---|
| Kind | instance |
| Move | induction |
| Language | lean |
| Status | accepted |
| Source | [formal-conjectures](../../sources/formal-conjectures/SOURCE.md) at `a425ca3eb797` |
| Licence | `Apache-2.0` |

## Intent

Prove the off-diagonal Ramsey binomial bound `HasRamseyProperty (Nat.choose (s+t) s) s t`
for all `s, t` by strong induction on the shared measure `n = s + t`, so that the induction
step is exactly the pigeonhole recurrence lemma `HasRamseyProperty.step` and each base case
is `HasRamseyProperty.mono` applied to a zero base case. This is the induction chapter that
the file's headline result `Combinatorics.hypergraphRamsey_two_le_four_pow` (lines 290-308)
is assembled from.

## The decomposition

### parent `hasRamseyProperty_choose`: [`FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean` lines 237-278](https://github.com/google-deepmind/formal-conjectures/blob/a425ca3eb797fe927cb88c950565fdcbbbbada70/FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean#L237-L278) ([local copy](code/FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean))

```lean
lemma hasRamseyProperty_choose : ∀ (s t : ℕ),
    HasRamseyProperty (Nat.choose (s + t) s) s t := by
  -- Induction on `s + t` via `Nat.strong_induction_on`.
  suffices h : ∀ (n : ℕ), ∀ (s t : ℕ), s + t = n → HasRamseyProperty (Nat.choose n s) s t by
    intro s t
    exact h (s + t) s t rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s t hst
    match s, t, hst with
    | 0, t, hst =>
      -- C(n, 0) = 1; we want HasRamseyProperty 1 0 t, which follows from the s = 0 base.
      show HasRamseyProperty (Nat.choose n 0) 0 t
      rw [Nat.choose_zero_right]
      exact HasRamseyProperty.mono (Nat.zero_le _) (hasRamseyProperty_zero_left 0 t)
    | s+1, 0, hst =>
      -- C(n, s+1) with t = 0. Use the t = 0 base case.
      show HasRamseyProperty (Nat.choose n (s+1)) (s+1) 0
      exact HasRamseyProperty.mono (Nat.zero_le _) (hasRamseyProperty_zero_right 0 (s+1))
    | s+1, t+1, hst =>
      -- Pascal: C(n, s+1) = C(n-1, s) + C(n-1, s+1), where n = s+1+t+1 = s+t+2.
      -- i.e. n - 1 = s + (t+1) = (s+1) + t.
      have hn_pred : n - 1 + 1 = n := by omega
      have hs_ih : HasRamseyProperty (Nat.choose (n - 1) s) s (t + 1) := by
        apply ih (n - 1) (by omega) s (t + 1)
        omega
      have ht_ih : HasRamseyProperty (Nat.choose (n - 1) (s + 1)) (s + 1) t := by
        apply ih (n - 1) (by omega) (s + 1) t
        omega
      have hNs_pos : 1 ≤ Nat.choose (n - 1) s := by
        have : s ≤ n - 1 := by omega
        exact Nat.choose_pos this
      have hrec : HasRamseyProperty (Nat.choose (n - 1) s + Nat.choose (n - 1) (s + 1))
          (s + 1) (t + 1) := HasRamseyProperty.step hs_ih ht_ih hNs_pos
      -- Pascal's identity: C(n, s+1) = C(n-1, s) + C(n-1, s+1) when n ≥ 1.
      have hpascal : Nat.choose n (s + 1) = Nat.choose (n - 1) s + Nat.choose (n - 1) (s + 1) := by
        conv_lhs => rw [← hn_pred]
        rw [Nat.choose_succ_succ]
      show HasRamseyProperty (Nat.choose n (s + 1)) (s + 1) (t + 1)
      rw [hpascal]
      exact hrec
```

### child `HasRamseyProperty.mono`: [`FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean` lines 67-70](https://github.com/google-deepmind/formal-conjectures/blob/a425ca3eb797fe927cb88c950565fdcbbbbada70/FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean#L67-L70) ([local copy](code/FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean))

```lean
lemma HasRamseyProperty.mono {N N' s t : ℕ} (hNN' : N ≤ N') (h : HasRamseyProperty N s t) :
    HasRamseyProperty N' s t := by
  intro m c V hV
  exact h c V (hNN'.trans hV)
```

### child `hasRamseyProperty_zero_left`: [`FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean` lines 73-79](https://github.com/google-deepmind/formal-conjectures/blob/a425ca3eb797fe927cb88c950565fdcbbbbada70/FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean#L73-L79) ([local copy](code/FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean))

```lean
lemma hasRamseyProperty_zero_left (N t : ℕ) : HasRamseyProperty N 0 t := by
  intro m c V _hV
  refine Or.inl ⟨∅, Finset.empty_subset _, by simp, ?_⟩
  intro e he _
  -- e ⊆ ∅, so e = ∅, but e.card = 2.
  have he_empty : e = ∅ := Finset.subset_empty.mp he
  simp [he_empty] at *
```

### child `hasRamseyProperty_zero_right`: [`FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean` lines 82-87](https://github.com/google-deepmind/formal-conjectures/blob/a425ca3eb797fe927cb88c950565fdcbbbbada70/FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean#L82-L87) ([local copy](code/FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean))

```lean
lemma hasRamseyProperty_zero_right (N s : ℕ) : HasRamseyProperty N s 0 := by
  intro m c V _hV
  refine Or.inr ⟨∅, Finset.empty_subset _, by simp, ?_⟩
  intro e he _
  have he_empty : e = ∅ := Finset.subset_empty.mp he
  simp [he_empty] at *
```

### child `HasRamseyProperty.step`: [`FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean` lines 180-233](https://github.com/google-deepmind/formal-conjectures/blob/a425ca3eb797fe927cb88c950565fdcbbbbada70/FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean#L180-L233) ([local copy](code/FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean))

```lean
lemma HasRamseyProperty.step {Ns Nt s t : ℕ}
    (hs : HasRamseyProperty Ns s (t + 1))
    (ht : HasRamseyProperty Nt (s + 1) t) (hNs : 1 ≤ Ns) :
    HasRamseyProperty (Ns + Nt) (s + 1) (t + 1) := by
  classical
  intro m c V hV
  -- V is nonempty since V.card ≥ Ns + Nt ≥ 1.
  have hVpos : 0 < V.card := by
    have : 1 ≤ V.card := Nat.le_trans hNs (Nat.le_trans (Nat.le_add_right _ _) hV)
    exact this
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hVpos
  -- Split V.erase v by colour of pair {v, u}.
  set R := (V.erase v).filter (fun u => c {v, u} = false) with hR_def
  set B := (V.erase v).filter (fun u => c {v, u} = true) with hB_def
  have hsplit : R.card + B.card = V.card - 1 :=
    card_false_true_split c V hv
  have hRsubV : R ⊆ V := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have hBsubV : B ⊆ V := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have hvnR : v ∉ R := fun h => Finset.notMem_erase _ _ (Finset.mem_of_mem_filter _ h)
  have hvnB : v ∉ B := fun h => Finset.notMem_erase _ _ (Finset.mem_of_mem_filter _ h)
  -- Pigeonhole: either R.card ≥ Ns or B.card ≥ Nt.
  obtain hRcard | hRcard := le_or_gt Ns R.card
  · -- Case 1: apply `hs` on R to get false K_s (extend by v) or true K_{t+1}.
    rcases hs c R hRcard with ⟨S, hSsub, hScard, hSmono⟩ | ⟨S, hSsub, hScard, hSmono⟩
    · -- false K_s on R ⊆ V; extend by v (false-adjacent to all of R) to false K_{s+1}.
      have hvS : v ∉ S := fun h => hvnR (hSsub h)
      refine Or.inl ⟨insert v S, ?_, ?_, ?_⟩
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu'
        · exact hv
        · exact hRsubV (hSsub hu')
      · rw [Finset.card_insert_of_notMem hvS, hScard]
      · apply mono_insert hSmono
        intro u hu
        have hu' : u ∈ R := hSsub hu
        exact (Finset.mem_filter.mp hu').2
    · -- true K_{t+1} on R ⊆ V.
      exact Or.inr ⟨S, hSsub.trans hRsubV, hScard, hSmono⟩
  · -- Case 2: R.card < Ns, so B.card ≥ Nt. Apply `ht` on B symmetrically.
    rcases ht c B (by lia) with ⟨S, hSsub, hScard, hSmono⟩ | ⟨S, hSsub, hScard, hSmono⟩
    · -- false K_{s+1} on B ⊆ V.
      exact Or.inl ⟨S, hSsub.trans hBsubV, hScard, hSmono⟩
    · -- true K_t on B; extend by v (true-adjacent to all of B) to true K_{t+1}.
      have hvS : v ∉ S := fun h => hvnB (hSsub h)
      refine Or.inr ⟨insert v S, ?_, ?_, ?_⟩
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu'
        · exact hv
        · exact hBsubV (hSsub hu')
      · rw [Finset.card_insert_of_notMem hvS, hScard]
      · apply mono_insert hSmono
        intro u hu
        have hu' : u ∈ B := hSsub hu
        exact (Finset.mem_filter.mp hu').2
```

### context `HasRamseyProperty`: [`FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean` lines 61-64](https://github.com/google-deepmind/formal-conjectures/blob/a425ca3eb797fe927cb88c950565fdcbbbbada70/FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean#L61-L64) ([local copy](code/FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean))

```lean
def HasRamseyProperty (N s t : ℕ) : Prop :=
  ∀ {m : ℕ} (c : Finset (Fin m) → Bool) (V : Finset (Fin m)), N ≤ V.card →
    (∃ S ⊆ V, S.card = s ∧ ∀ e ⊆ S, e.card = 2 → c e = false) ∨
    (∃ S ⊆ V, S.card = t ∧ ∀ e ⊆ S, e.card = 2 → c e = true)
```

How the parts fit. The parent first *strengthens* the statement with a `suffices`: instead of
proving `HasRamseyProperty (Nat.choose (s+t) s) s t` directly, it proves the more convenient
`∀ n s t, s + t = n → HasRamseyProperty (Nat.choose n s) s t` and then instantiates it at
`n = s + t` (lines 240-242). This generalisation is what lets the induction hypothesis apply at
both `(s, t+1)` and `(s+1, t)`, each with the smaller measure `n - 1`. Strong induction then runs
on `n` (`Nat.strong_induction_on`, line 244), and the `match s, t` gives three branches:

```
hasRamseyProperty_choose (strong induction on n = s+t)
├── HasRamseyProperty.mono          — used in BOTH base cases to weaken C(n,·) ≥ 1
├── hasRamseyProperty_zero_left     — base case s = 0  (line 252)
├── hasRamseyProperty_zero_right    — base case t = 0  (line 256)
└── HasRamseyProperty.step          — induction step s+1, t+1  (line 271)
    ├── card_false_true_split       — the colour split of V.erase v (line 195)
    └── mono_insert                 — extend the clique by v (lines 212, 230)
```

The glue itself does almost nothing beyond naming these lemmas: the two base-case branches each
`rw [Nat.choose_zero_right]` then `exact HasRamseyProperty.mono (Nat.zero_le _) (hasRamseyProperty_zero_*)`,
and the step branch applies the two induction hypotheses to build `hs_ih` and `ht_ih`, combines them
with `HasRamseyProperty.step`, and closes with Pascal's identity `Nat.choose_succ_succ` (lines 273-278).

Why each child is a good leaf:

- `HasRamseyProperty.mono` (67-70) is a one-line statement that transports the property from a
  smaller `N` to a larger `N'` by transitivity of `≤`; its proof is just `hNN'.trans hV`. It is a
  self-contained interface lemma, not specific to Ramsey: it holds for any predicate with the same
  "`N ≤ V.card`" guard.
- `hasRamseyProperty_zero_left` / `hasRamseyProperty_zero_right` (73-79 / 82-87) each close by
  exhibiting the empty set and discharging the 2-subset condition vacuously (`e ⊆ ∅` forces `e = ∅`);
  they are independent of `N`, which is why the glue only needs them at the value `1`.
- `HasRamseyProperty.step` (180-233) is the genuinely hard leaf: it owns the pigeonhole split of
  `V.erase v` into false- and true-neighbours, and closes with two further project lemmas
  `card_false_true_split` (117-137) and the private `mono_insert` (142-169). It does not reference
  `choose`, so it is reusable for any recurrence `HasRamseyProperty (Ns+Nt) (s+1) (t+1)`.

The depth-2 lemmas `card_false_true_split` and `mono_insert` are not children of the glue (the glue
never names them) but are what the step child depends on; this is the chain
`hasRamseyProperty_choose → HasRamseyProperty.step → {card_false_true_split, mono_insert}` that
gives `shape.depth = 2`.

## Why it is good

1. *(check)* The file compiles at the pinned commit: `.github/workflows/build-and-docs.yml`'s
   `build` job runs `lake --wfail build FormalConjecturesForMathlib FormalConjecturesUtil`, which
   builds `FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean`
   ([workflow lines 208-212](https://github.com/google-deepmind/formal-conjectures/blob/a425ca3eb797fe927cb88c950565fdcbbbbada70/.github/workflows/build-and-docs.yml#L208-L212)).
2. *(check)* The parent closes by strong induction (`Nat.strong_induction_on`, line 244) in three
   `match` branches, each an `exact` built from the four named children:
   `HasRamseyProperty.mono` + `hasRamseyProperty_zero_left` (line 252),
   `HasRamseyProperty.mono` + `hasRamseyProperty_zero_right` (line 256), and
   `HasRamseyProperty.step` applied to the two induction hypotheses (line 271); the other lemmas it
   uses are `Nat.zero_le` (the monotonicity bound in both base branches, lines 252 and 256),
   `Nat.choose_zero_right` (line 251), `Nat.choose_pos` (line 269) and `Nat.choose_succ_succ`
   (line 275, Pascal's identity)
   ([lines 237-278](https://github.com/google-deepmind/formal-conjectures/blob/a425ca3eb797fe927cb88c950565fdcbbbbada70/FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean#L237-L278)).
3. *(measurement)* The decomposition is theorem scale with 4 direct lemmas and depth 2: the glue is
   42 lines (237-278), shorter than its step child (54 lines, 180-233), and the step child itself
   rests on `card_false_true_split` (117-137) and `mono_insert` (142-169).
4. *(author-statement)* The authors state the plan as induction on `s + t` in the module docstring:
   "Induction on `s + t` then gives `R(s, t) ≤ C(s+t, s)`; for `s = t = k` this is
   `R(k, k) ≤ C(2k, k) ≤ 4 ^ k`"
   ([lines 27-31](https://github.com/google-deepmind/formal-conjectures/blob/a425ca3eb797fe927cb88c950565fdcbbbbada70/FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean#L27-L31)).
5. *(known-use)* `hasRamseyProperty_choose` is the chapter the file's headline
   `Combinatorics.hypergraphRamsey_two_le_four_pow` is assembled from: that theorem instantiates it
   at `s = t = k` to get the `C(2k, k)` member of the `hypergraphRamsey` defining set
   ([lines 290-308](https://github.com/google-deepmind/formal-conjectures/blob/a425ca3eb797fe927cb88c950565fdcbbbbada70/FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean#L290-L308)).

In my opinion the detail worth copying is the `suffices` generalisation paired with the strong
induction: it turns a two-index statement into one indexed by the measure `n = s + t`, so that a
single induction variable suffices and the IH fires at both `(s, t+1)` and `(s+1, t)`.

## When to use it, and when not

Use it when the target's truth depends on two indices only through their shared sum (or another
single measure), the recurrence lowers that measure by 1, and the recurrence step and the base cases
can be stated as separate named lemmas. The generalisation step (`suffices` over `n = s + t`) is
what makes the induction variable and the generalised set explicit; it is the Lean counterpart of
Isabelle's `arbitrary:` generalisation for `induction`.

Avoid it when the recurrence does not lower one shared measure (then you need a more complex
well-founded order, e.g. a lexicographic one), when the strengthened statement indexed by `n` is not
obviously implied by the target, or when the base cases cannot be obtained by a single
monotonicity/weakening lemma from one zero base case — if each base case needs its own argument, the
"one lemma per branch" shape here breaks down and the glue would carry real proof content.

## Consequences

The move creates two obligations: (a) the strengthened statement must imply the target — discharged
here by instantiating the strengthened theorem at `n = s + t`; (b) the induction must be
well-founded, which `Nat.strong_induction_on` provides on `n`. Each `match` branch must line its goal
up with one child's exact statement, so the glue carries the two rewrites `Nat.choose_zero_right`
and `Nat.choose_succ_succ` (Pascal) to reshape the binomial coefficient into the child's form; a
child stated with a different `choose` argument would not apply without that reshaping.

Failure modes: if the measure is not a plain sum the generalisation is less mechanical; if a base
case cannot be reached by monotonicity from a zero base case, more base-case lemmas are needed; and
if the step's pigeonhole split has to be told which side is "large" (`le_or_gt` here), the glue
relies on arithmetic (`by lia` in `HasRamseyProperty.step` line 219) that the induction hypothesis
does not supply.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build-and-docs.yml build job (steps 208-212) runs lake --wfail build FormalConjecturesForMathlib FormalConjecturesUtil on push to main (default branch), which builds the library containing Combinatorics/Ramsey/Diagonal.lean; pinned commit a425ca3eb797fe927cb88c950565fdcbbbbada70 registered at ref=HEAD (default branch) | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at a425ca3eb797fe927cb88c950565fdcbbbbada70 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | workflow .github/workflows/build-and-docs.yml at a425ca3: build job step Build ForMathlib utilities and test (lines 208-212) runs lake --wfail build FormalConjecturesForMathlib FormalConjecturesUtil; library FormalConjecturesForMathlib contains module FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean | verifier |
| 2 | refuted | read copied Diagonal.lean lines 237-278: branches invoke mono + zero_left (252), mono + zero_right (256), step (271); but both base branches also apply Nat.zero_le (lines 252, 256), a lemma the claim omits from its only-other-lemmas list (choose_zero_right, choose_pos, choose_succ_succ); the induction also uses Nat.strong_induction_on (244) | verifier |
| 3 | verified | counted copied file lines: 237-278 = 42 (glue), 180-233 = 54 (step), mono 67-70 = 4, zero_left 73-79 = 7, zero_right 82-87 = 6; depth-2 lemmas card_false_true_split 117-137 and mono_insert 142-169; glue calls step (271); step calls card_false_true_split (195) and mono_insert (212, 230); 4 direct children, depth 2, glue 42 is shorter than step 54 | verifier |
| 4 | verified | read module docstring lines 27-31: the sentence Induction on s + t then gives R(s,t) <= C(s+t,s); for s = t = k this is R(k,k) <= C(2k,k) <= 4^k appears verbatim | verifier |
| 5 | verified | read lines 290-308: hypergraphRamsey_two_le_four_pow (290) sets hprop := Diagonal.hasRamseyProperty_choose k k (293-294), builds hmem showing Nat.choose (k+k) k is in the defining set (295-304), then closes with Nat.sInf_le hmem (305) and Nat.centralBinom_le_four_pow (308) | verifier |
| 6 | verified | read copied file Diagonal.lean (byte-identical at a425ca3e): line 244 'induction n using Nat.strong_induction_on with'; match at 247 with three branches 248/253/257; branch 0,t (252) exact HasRamseyProperty.mono (Nat.zero_le _) (hasRamseyProperty_zero_left 0 t); branch s+1,0 (256) exact HasRamseyProperty.mono (Nat.zero_le _) (hasRamseyProperty_zero_right 0 (s+1)); branch s+1,t+1 builds hs_ih (261-263) and ht_ih (264-266) via ih then hrec := HasRamseyProperty.step hs_ih ht_ih hNs_pos (271); other lemmas Nat.choose_zero_right (251), Nat.zero_le (252,256), Nat.choose_pos (269), Nat.choose_succ_succ (275); all match the claim | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent hasRamseyProperty_choose (237-278) matches the copied code verbatim; the four children (HasRamseyProperty.mono 67-70, hasRamseyProperty_zero_left 73-79, hasRamseyProperty_zero_right 82-87, HasRamseyProperty.step 180-233) are exactly the named project lemmas the glue applies directly (lines 252, 256, 271), each child's statement and closed_by text match the code, and the glue's only other lemmas are mathlib facts (Nat.zero_le, Nat.choose_zero_right, Nat.choose_pos, Nat.choose_succ_succ). The proof closes: no sorry/admit/axiom in the file, and the suffices-generalise + Nat.strong_induction_on + three match branches assemble correctly. Shape numbers are right: direct_lemmas=4, depth=2 (hasRamseyProperty_choose -> HasRamseyProperty.step -> {card_false_true_split 117-137, mono_insert 142-169}), glue_lines=42 (237-278), child_lines=[4,7,6,54] matching mono/zero_left/zero_right/step. Provenance check passes (file byte-identical at a425ca3eb797). | reviewer-correctness |
| generality | accept | Generality lens passes. (1) The move is stated beyond the example: 'When to use' abstracts to any two-index statement whose truth depends only on a shared measure (s+t 'or another single measure'), with a recurrence lowering that measure by 1 and base/step lemmas pre-stated; the suffices-over-n generalisation is explicitly named the Lean counterpart of Isabelle's arbitrary:. (2) 'When not to use' is honest and specific: recurrence not lowering one shared measure (needs lexicographic order), strengthened statement not obviously implied by target, and base cases not reachable by a single monotonicity/weakening lemma — each a concrete, falsifiable condition, and Consequences correctly lists the two obligations (strengthened statement implies target via instantiation at n=s+t; well-foundedness from Nat.strong_induction_on) plus the real failure mode that the pigeonhole split leans on le_or_gt/by lia not supplied by the IH. (3) 'Why each child is a good leaf' names the bounded-prover properties: mono is a one-line transitivity transport holding for any predicate with the N ≤ V.card guard; the zero lemmas discharge vacuously and are independent of N; step is the self-contained hard leaf that does not reference choose and is reusable for any (Ns+Nt)(s+1)(t+1) recurrence. No standing objection. | reviewer-generality |
| provenance-licence | accept | Provenance/licence lens passes. Permalinks: every files[] and sites[] permalink and every claim URL pins the full commit a425ca3eb797fe927cb88c950565fdcbbbbada70 with the correct repo google-deepmind/formal-conjectures and path FormalConjecturesForMathlib/Combinatorics/Ramsey/Diagonal.lean; site line ranges match the copied file verbatim (mono 67-70, zero_left 73-79, zero_right 82-87, HasRamseyProperty 61-64, step 180-233, parent 237-278; claim-4 docstring 27-31 and claim-5 290-308 also match). Commit: entry.json source.commit == source.json commit == SOURCE.md pinned commit (a425ca3e..., pinned 2026-11-12T10:23:42Z); check_provenance re-ran pass ('1 file(s) byte-identical at a425ca3eb797fe927cb88c950565fdcbbbbada70'), proving the commit and path resolve upstream and the local copy (14955 bytes, recorded sha256) is unmodified. Licence: entry.json 'Apache-2.0' == source.json licence == SOURCE.md 'Apache-2.0'; the copied file header declares Apache License 2.0 and sources/formal-conjectures/upstream-LICENSE begins with the Apache 2.0 text; SOURCE.md lists the LICENSE permalink and attribution. Source note is consistent with the copied files. Everything traceable; no objection. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/google-deepmind/formal-conjectures at commit `a425ca3eb797fe927cb88c950565fdcbbbbada70`, under `Apache-2.0`; see the [source note](../../sources/formal-conjectures/SOURCE.md) for the licence text and attribution.
