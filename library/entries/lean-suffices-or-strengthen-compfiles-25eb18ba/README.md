# Strengthen to 'only the last lamp on' then convert to all-on: IMO 1993 P6(b)

| | |
|---|---|
| Kind | instance |
| Move | suffices-or-strengthen |
| Language | lean |
| Status | accepted |
| Source | [compfiles](../../sources/compfiles/SOURCE.md) at `1745e6ced3e6` |
| Licence | `Apache-2.0` |

## Intent

A statement about all `n` lamps being on after `n^2 - 1` steps is reduced to two
lemmas: `last_lamp_only_of_two_pow` proves the stronger intermediate state (after
`n*(n-1)` steps only the last lamp is on, when `n = 2^k`), and
`all_on_of_last_only` converts that state into "all lamps on" by sweeping one
lamp at a time around the circle. The glue is eight lines: one side condition
(`1 < n`) and one `exact`.

## The decomposition

### parent `imo1993_p6_b`: [`Compfiles/Imo1993P6.lean` lines 1233-1240](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Imo1993P6.lean#L1233-L1240) ([local copy](code/Compfiles/Imo1993P6.lean))

```lean
problem imo1993_p6_b (n k : ℕ) [NeZero n] (hn : n = 2 ^ k) (hk : 0 < k) :
    ∀ i : Fin n, lampsAfter n (n ^ 2 - 1) i = true := by
  have hn2 : 1 < n := by
    have h2 : (2 : ℕ) ≤ 2 ^ k :=
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    lia
  exact all_on_of_last_only hn2 (last_lamp_only_of_two_pow n k hk hn)
```

### child `all_on_of_last_only`: [`Compfiles/Imo1993P6.lean` lines 143-225](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Imo1993P6.lean#L143-L225) ([local copy](code/Compfiles/Imo1993P6.lean))

```lean
lemma all_on_of_last_only {n : ℕ} [NeZero n] (hn : 1 < n)
    (h : ∀ i : Fin n, lampsAfter n (n * (n - 1)) i = decide (i.val = n - 1)) :
    ∀ i : Fin n, lampsAfter n (n ^ 2 - 1) i = true := by
  have hT0 : ((n * (n - 1) : ℕ) : Fin n) = 0 := by
    ext
    rw [Fin.coe_natCast_eq_mod, Nat.mul_mod_right]
    simp
  have h' : ∀ i : Fin n, (step^[n * (n - 1)] (initial n)).1 i = decide (i.val = n - 1) :=
    h
  -- After `n * (n - 1) + j` steps (for `j ≤ n - 1`), exactly the lamps with index
  -- `< j` and the lamp `n - 1` are on.
  have key : ∀ j : ℕ, j ≤ n - 1 → ∀ i : Fin n,
      (step^[n * (n - 1) + j] (initial n)).1 i = decide (i.val < j ∨ i.val = n - 1) := by
    intro j
    induction j with
    | zero =>
      intro _ i
      rw [Nat.add_zero]
      simp only [Nat.not_lt_zero, false_or]
      exact h' i
    | succ j ih =>
      intro hj
      have hj1 : j < n := by lia
      have ih' := ih (by lia : j ≤ n - 1)
      have hpos : (step^[n * (n - 1) + j] (initial n)).2 = (j : Fin n) := by
        rw [pos_after, Nat.cast_add, hT0, zero_add]
      have hstep : step^[n * (n - 1) + (j + 1)] (initial n) =
          step (step^[n * (n - 1) + j] (initial n)) := by
        rw [← add_assoc, Function.iterate_succ_apply']
      intro i
      show (step^[n * (n - 1) + (j + 1)] (initial n)).1 i =
        decide (i.val < j + 1 ∨ i.val = n - 1)
      rw [hstep, step_lamps]
      by_cases hi : i = (step^[n * (n - 1) + j] (initial n)).2
      · -- Lamp `j` is toggled: its predecessor is on, so it switches from off to on.
        subst hi
        rw [Function.update_self, hpos, bool_toggle]
        have hm : ((j : Fin n) - 1).val < j ∨ ((j : Fin n) - 1).val = n - 1 := by
          by_cases hj0 : j = 0
          · subst hj0
            right
            rcases n with _ | m
            · lia
            · rw [Fin.natCast_zero, zero_sub, Fin.coe_neg_one]
              exact (Nat.add_sub_cancel m 1).symm
          · left
            have h1 : (j : Fin n) ≠ 0 := by
              rw [← Fin.val_ne_zero_iff, Fin.val_natCast, Nat.mod_eq_of_lt hj1]
              exact hj0
            rw [Fin.val_sub_one_of_ne_zero h1, Fin.val_natCast, Nat.mod_eq_of_lt hj1]
            lia
        have hpred : (step^[n * (n - 1) + j] (initial n)).1 ((j : Fin n) - 1) = true := by
          rw [ih', decide_eq_true_eq]
          exact hm
        have hcur : (step^[n * (n - 1) + j] (initial n)).1 (j : Fin n) = false := by
          rw [ih', Fin.val_natCast, Nat.mod_eq_of_lt hj1, decide_eq_false_iff_not]
          push Not
          exact ⟨le_refl j, by lia⟩
        rw [hpred, hcur, Fin.val_natCast, Nat.mod_eq_of_lt hj1, Bool.true_xor,
          Bool.not_false]
        symm
        rw [decide_eq_true_eq]
        lia
      · -- All other lamps keep their state; the threshold condition is unchanged
        -- since `i.val ≠ j`.
        rw [Function.update_of_ne hi, ih']
        have hvi : i.val ≠ j := by
          intro hv
          apply hi
          rw [hpos, Fin.ext_iff, Fin.val_natCast, Nat.mod_eq_of_lt hj1, hv]
        rw [Bool.decide_congr (by lia :
          (i.val < j ∨ i.val = n - 1) ↔ (i.val < j + 1 ∨ i.val = n - 1))]
  intro i
  have hfin : n * (n - 1) + (n - 1) = n ^ 2 - 1 := by
    have h1 : n * (n - 1) = n * n - n := by rw [Nat.mul_sub_left_distrib, mul_one]
    have h2 : n ≤ n * n := Nat.le_mul_of_pos_right n (by lia)
    rw [h1, pow_two]
    lia
  rw [← hfin]
  show (step^[n * (n - 1) + (n - 1)] (initial n)).1 i = true
  rw [key (n - 1) le_rfl i, decide_eq_true_eq]
  have := i.isLt
  lia
```

### child `last_lamp_only_of_two_pow`: [`Compfiles/Imo1993P6.lean` lines 1002-1023](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Imo1993P6.lean#L1002-L1023) ([local copy](code/Compfiles/Imo1993P6.lean))

```lean
theorem last_lamp_only_of_two_pow (n k : ℕ) [NeZero n] (hk : 0 < k) (hn : n = 2 ^ k) :
    ∀ i : Fin n, lampsAfter n (n * (n - 1)) i = decide (i.val = n - 1) := by
  subst hn
  intro i
  have hA := (core k hk (2 ^ k) rfl).1
  show (step^[2 ^ k * (2 ^ k - 1)] (initial (2 ^ k))).1 i = decide (i.val = 2 ^ k - 1)
  have hgl : (step^[2 ^ k * (2 ^ k - 1)] (initial (2 ^ k))).1 i
      = z2b ((zstep^[2 ^ k * (2 ^ k - 1)] (zinit (2 ^ k))).1 i) :=
    congrFun (congrArg Prod.fst (glue _)) i
  rw [hgl, Function.iterate_mul, aux, hA]
  show z2b (eFn (2 ^ k) i) = decide (i.val = 2 ^ k - 1)
  unfold eFn
  by_cases hi : i = lasti (2 ^ k)
  · rw [ite_eq_left hi, z2b_one]
    rw [Fin.ext_iff, lasti_val] at hi
    simp [hi]
  · rw [ite_eq_right hi, z2b_zero]
    have hne : i.val ≠ 2 ^ k - 1 := by
      intro hc
      apply hi
      exact Fin.ext hc
    simp [hne]
```

How the parts fit. The glue `imo1993_p6_b` (lines 1233-1240) does two things: it
establishes the side condition `hn2 : 1 < n` (from `n = 2 ^ k` and `0 < k`), then
closes the goal with a single `exact all_on_of_last_only hn2
(last_lamp_only_of_two_pow n k hk hn)`. The argument is a strengthen-then-convert:

```
imo1993_p6_b (1233-1240)               all lamps on after n^2 - 1 steps
├── all_on_of_last_only (143-225)      final phase: "only the last lamp on" → "all on"
└── last_lamp_only_of_two_pow (1002-1023)  core: "only the last lamp on" after n*(n-1) steps
    └── core (983) → stepLemma (791) → catL (658)   (depth 4, the ZMod 2 induction)
```

`last_lamp_only_of_two_pow` proves the hypothesis `h` that `all_on_of_last_only`
needs: its conclusion `∀ i, lampsAfter n (n*(n-1)) i = decide (i.val = n-1)` is
exactly `h` once `n = 2^k` is substituted. Each child is a good leaf — a
self-contained statement whose proof closes from named siblings of the same file:

- `last_lamp_only_of_two_pow` closes from the named project lemmas `core`, `glue`
  and `aux` (the ZMod 2 model and its Bool correspondence), finished by `simp` on
  a case split at `i = lasti (2^k)`.
- `all_on_of_last_only` closes from the named project lemmas `pos_after`,
  `step_lamps` and `bool_toggle`, via an internal `have key` induction over the
  position `j`, finished by `key (n-1) le_rfl i` and `lia`.

## Why it is good

1. `last_lamp_only_of_two_pow` occurs in the parent site (check, line 1240).
2. `all_on_of_last_only` occurs in the parent site (check, line 1240).
3. No `sorry`/`admit`/`axiom` occurs in the parent site (check, lines 1233-1240).
4. The glue is 8 lines (1233-1240); the two children it joins are 83 lines
   (`all_on_of_last_only`, 143-225) and 22 lines (`last_lamp_only_of_two_pow`,
   1002-1023), matching the theorem-scale shape `direct_lemmas=2`,
   `glue_lines=8`, `child_lines=[83,22]` (measurement).
5. The authors state the two-half structure in a comment at lines 365-368: the
   cores of (b) and (c) are proved by "induction on `k` via a `ZMod 2` model of
   the process (toggling is adding the predecessor)", with
   "`all_on_of_last_only` and `all_on_of_lamp1_only` for the final phases"
   (author-statement).

In my opinion the detail worth copying is the *agreement* between the two
children: the strengthened core's conclusion is, word for word, the final-phase
lemma's hypothesis, so the glue is a bare `exact` with only a numeric side
condition to discharge.

## When to use it, and when not

Use it when the final state ("all on") is the result of a uniform sweep from a
simpler distinguished state ("only the last lamp on"), and that distinguished
state is exactly what a stronger induction produces for free — here the ZMod 2
model makes the "only the last lamp on" state a clean fixed target for induction
on `k`. The two halves must agree on the intermediate state, so the glue stays a
bare `exact`. Avoid it when the intermediate state is not actually stronger or
more convenient; when the conversion sweep is not uniform in `n` (here
`all_on_of_last_only` carries its own induction over the position, which only
works because the sweep advances one lamp per step); or when the strengthened
core would need the very theorem being proved.

## Consequences

The move splits the goal into a strengthened core (after `n*(n-1)` steps exactly
"only the last lamp is on") and a final phase (a deterministic sweep turning that
state into "all on"). Each half carries its own induction: the core by induction
on `k` over a ZMod 2 model, the final phase by induction on the position `j`.
The halves must agree on the intermediate state — `last_lamp_only_of_two_pow`'s
conclusion is exactly `all_on_of_last_only`'s hypothesis `h` — and the glue also
discharges the side condition `hn2 : 1 < n` that `all_on_of_last_only` needs.
Failure modes: if the strengthened state does not match the conversion lemma's
hypothesis exactly (same step count, same "only lamp L_{n-1}" predicate), the
glue needs an extra rewrite; if the conversion is not uniform in `n` it cannot
be a standalone lemma.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push-main.yaml runs 'lake build' on pushes to default branch main; commit 1745e6ced3e671bd74417548494b034eb2c87da8 is HEAD of main (compare status identical) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: all_on_of_last_only@Compfiles/Imo1993P6.lean:1240, last_lamp_only_of_two_pow@Compfiles/Imo1993P6.lean:1240; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 1745e6ced3e671bd74417548494b034eb2c87da8 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, last_lamp_only_of_two_pow) -> cites: last_lamp_only_of_two_pow occurs at Compfiles/Imo1993P6.lean:1240 | check_claims.py |
| 2 | verified | cites(parent, all_on_of_last_only) -> cites: all_on_of_last_only occurs at Compfiles/Imo1993P6.lean:1240 | check_claims.py |
| 3 | verified | no_sorry(Compfiles/Imo1993P6.lean, 1233-1240) -> no_sorry: none of sorry, admit, axiom in Compfiles/Imo1993P6.lean:1233-1240 | check_claims.py |
| 4 | verified | Read code/Compfiles/Imo1993P6.lean: parent site 1233-1240 = 8 lines (1240-1233+1); all_on_of_last_only 143-225 = 83 lines; last_lamp_only_of_two_pow 1002-1023 = 22 lines; matches shape direct_lemmas=2, glue_lines=8, child_lines=[83,22] | verifier |
| 5 | verified | Read lines 365-368 of code/Compfiles/Imo1993P6.lean: comment states 'The cores of parts (b) and (c) are proved at the end of this section (last_lamp_only_of_two_pow and lamp1_only_of_two_pow_add_one): induction on k via a ZMod 2 model of the process (toggling is adding the predecessor); see all_on_of_last_only and all_on_of_lamp1_only for the final phases.' The claim's quoted fragments match verbatim | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent (1233-1240, 8 lines) closes by 'exact all_on_of_last_only hn2 (last_lamp_only_of_two_pow n k hk hn)'; both children cited and are exactly the two lemmas the parent uses. Child statements match code verbatim: all_on_of_last_only (143-145) closes via internal 'key (n-1) le_rfl i' then lia; last_lamp_only_of_two_pow (1002-1023) closes via core/glue/aux then simp on by_cases hi: i = lasti (2^k). Type unification closes: all_on_of_last_only's h equals last_lamp_only_of_two_pow's conclusion, hn2 discharges 1 < n. Shape numbers correct: glue_lines=8 (1240-1233+1), child_lines=[83,22] (225-143+1, 1023-1002+1), direct_lemmas=2. Depth-4 chain verified: core@983, stepLemma@791 (uses catL@658), core used by last_lamp_only_of_two_pow@1006. Author-statement comment at 365-368 matches claim 5. | reviewer-correctness |
| generality | accept | Move is stated beyond the example: applicability.goal_shape abstracts to 'P(i) after a fixed number of steps via a distinguished intermediate state then a deterministic sweep', and use_when/avoid_when name the mechanism (uniform sweep + intermediate state produced for free by a stronger induction). avoid_when is honest and specific, tied to the code: (1) intermediate state not actually stronger/more convenient, (2) conversion sweep not uniform in n — all_on_of_last_only's per-position induction only works because the sweep advances one lamp per step, (3) strengthened core would need the theorem being proved. consequences state concrete failure modes (mismatched intermediate state forces an extra rewrite in the glue; non-uniform conversion can't be a standalone lemma). Good leaves are described: 'a self-contained statement whose proof closes from named siblings of the same file', substantiated per child (last_lamp_only_of_two_pow closes from core/glue/aux; all_on_of_last_only from pos_after/step_lamps/bool_toggle). Minor gap: the phrase 'bounded prover' is not used — the leaf criterion (self-contained, closes from named siblings) is the bounded-prover-relevant property but the connection is left implicit, not blocking. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note all consistent and traceable. check_provenance.py reports pass (1 file byte-identical at 1745e6ced3e671bd74417548494b034eb2c87da8). Commit SHA matches across entry.json source.commit, README.md, sources/compfiles/SOURCE.md and source.json. Licence Apache-2.0 recorded in entry.json/README/SOURCE.md/source.json, and sources/compfiles/upstream-LICENSE is the Apache 2.0 text. All permalinks point at the pinned commit's Compfiles/Imo1993P6.lean, and the cited line ranges (1233-1240, 143-225, 1002-1023, 365-368) match the copied file verbatim. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/dwrensha/compfiles at commit `1745e6ced3e671bd74417548494b034eb2c87da8`, under `Apache-2.0`; see the [source note](../../sources/compfiles/SOURCE.md) for the licence text and attribution.
