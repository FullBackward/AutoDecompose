# Induction on the fuel extra for the closed form of truncated probGeometric

| | |
|---|---|
| Kind | instance |
| Move | induction |
| Language | lean |
| Status | verified |
| Source | [sampcert](../../sources/sampcert/SOURCE.md) at `a2c53bb5ff79` |
| Licence | `Apache-2.0` |

## Intent

Prove a closed form for every terminating run of the truncated `probGeometric`
loop — the probability mass of a run that samples `true` after `n` attempts —
by induction on the surplus fuel `extra`. The value at `extra + (n + 1)`
unrollings is already known at the minimal fuel by one lemma, and a second
lemma says one more step of fuel does not change it, so the parent only
carries the fuel arithmetic.

## The decomposition

### parent `geometric_characterization`: [`SampCert/Samplers/Geometric/Properties.lean` lines 272-290](https://github.com/leanprover/sampcert/blob/a2c53bb5ff790e729e252958060699b7eff898b9/SampCert/Samplers/Geometric/Properties.lean#L272-L290) ([local copy](code/SampCert/Samplers/Geometric/Properties.lean))

```lean
theorem geometric_characterization (n extra : ℕ) (h : ¬ n = 0) :
  probWhileCut geoLoopCond (geoLoopBody trial) (extra + (n + 1)) (true,0) (false,n) = (trial true)^(n-1) * (trial false) := by
  revert n
  induction extra
  · simp
    intro n h
    apply geometric_progress' trial _ h
  · rename_i extra IH
    intro n h
    have IH' := IH n h
    clear IH
    have A : extra + (n + 1) = (extra + n) + 1 := by exact rfl
    rw [A] at IH'
    rw [← geometric_preservation'] at IH'
    · have B : succ extra + (n + 1) = extra + n + 2 := by exact succ_add_eq_add_succ extra (n + 1)
      rw [B]
      trivial
    · trivial
    · exact Nat.le_add_left n extra
```

### child `geometric_progress'`: [`SampCert/Samplers/Geometric/Properties.lean` lines 186-194](https://github.com/leanprover/sampcert/blob/a2c53bb5ff790e729e252958060699b7eff898b9/SampCert/Samplers/Geometric/Properties.lean#L186-L194) ([local copy](code/SampCert/Samplers/Geometric/Properties.lean))

```lean
theorem geometric_progress' (n : ℕ) (h : ¬ n = 0) :
  probWhileCut geoLoopCond (geoLoopBody trial) (n + 1) (true, 0) (false, n) = (trial true)^(n-1) * (trial false) := by
  have prog := geometric_progress trial (n - 1) 0
  simp at prog
  have A : n - 1 + 1 = n := by exact succ_pred h
  rw [A] at prog
  have B : n - 1 + 2 = n + 1 := by exact succ_inj.mpr A
  rw [B] at prog
  trivial
```

### child `geometric_preservation'`: [`SampCert/Samplers/Geometric/Properties.lean` lines 235-267](https://github.com/leanprover/sampcert/blob/a2c53bb5ff790e729e252958060699b7eff898b9/SampCert/Samplers/Geometric/Properties.lean#L235-L267) ([local copy](code/SampCert/Samplers/Geometric/Properties.lean))

```lean
theorem geometric_preservation' (n m : ℕ) (h1 : ¬ m = 0) (h2 : n ≥ m) :
  probWhileCut geoLoopCond (geoLoopBody trial) (n + 2) (true,0) (false,m)
  =
  probWhileCut geoLoopCond (geoLoopBody trial) (n + 1) (true,0) (false,m) := by
  have prog := geometric_preservation trial (n - 1) (m - 1) 0
  have P : ¬ n = 0 := by
      by_contra h
      subst h
      simp at h2
      subst h2
      contradiction
  have A : 1 + (n - 1) + 2 = n + 2 := by
    conv =>
      left
      left
      rw [add_comm]
    rw [Nat.add_right_cancel_iff]
    exact succ_pred P
  rw [A] at prog
  have B : 0 + (m - 1) + 1 = m := by
    rw [add_assoc]
    rw [Nat.zero_add]
    exact succ_pred h1
  rw [B] at prog
  have C : n - 1 + 2 = n + 1 := by
    have C' : 2 = 1 + 1 := by rfl
    rw [C']
    rw [← add_assoc]
    rw [Nat.add_right_cancel_iff]
    exact succ_pred P
  rw [C] at prog
  apply prog
  exact Nat.sub_le_sub_right h2 1
```

How the parts fit. The parent is a single induction on `extra`, with `n`
generalised first (`revert n`), so the induction hypothesis is over every
`n`. The glue combines exactly two named lemmas:

```
geometric_characterization (parent, 272-290)
  ├─ base case ── geometric_progress'   (child, 186-194)
  │                └─ uses geometric_progress    (162-181)
  └─ step case ── geometric_preservation' (child, 235-267)
                   └─ uses geometric_preservation (199-230)
```

- The **base case** is `geometric_progress'`: at `extra = 0` the goal is
  `probWhileCut ... (n + 1) (true,0) (false,n) = (trial true)^(n-1) * (trial false)`,
  exactly the statement of `geometric_progress'`, applied by
  `apply geometric_progress' trial _ h`. Its proof closes by specialising
  `geometric_progress` to `(n - 1, 0)`, rewriting the fuel arithmetic with
  `succ_pred h` and `succ_inj.mpr A`, and `trivial`.
- The **step case** is `geometric_preservation'`: the induction hypothesis
  `IH'` is at fuel `extra + n + 1`, and the goal at `succ extra + (n + 1)`.
  After `rw [A]` re-associates the fuel, `rw [← geometric_preservation']`
  rewrites the goal backwards through the preservation lemma, leaving three
  goals: two arithmetic identities closed by `trivial` and the side condition
  `extra ≥ n` (the lemma's `n ≥ m` with `m := n`) closed by
  `Nat.le_add_left n extra`. The preservation lemma's own proof closes by
  specialising `geometric_preservation` to `(n - 1, m - 1, 0)`, proving
  `¬ n = 0` from `n ≥ m` and `¬ m = 0`, rewriting the fuel arithmetic, then
  `apply prog; exact Nat.sub_le_sub_right h2 1`.

Each child is a good leaf because its statement is self-contained — a closed
form at one fuel bound, and a "one more step of fuel does nothing" equation —
and its proof closes on its own from one unprimed sibling (`geometric_progress`
or `geometric_preservation`), so neither child exposes the induction to the
parent.

## Why it is good

1. The declaration `geometric_characterization` sits at lines 272-290 of the
   copied file (check, permalink above).
2. The parent's proof cites `geometric_progress'` (line 278) — the base case —
   and `geometric_preservation'` (line 285) — the step case — and nothing
   else is the glue's content (check, permalink).
3. `geometric_preservation'` occurs in the parent site (check, permalink).
4. The shape is 2 direct lemmas, a checked chain of depth 2, a 19-line glue
   and child proofs of 9 and 33 lines (measurement; see the `shape` field and
   the site ranges).
5. `geometric_characterization` is reused at line 312 to prove the limit
   theorem `geometric_pwc_sup` (known-use, permalink).

In my opinion the detail worth copying is the pairing: the induction variable
is the *surplus* fuel `extra`, not the loop's own fuel, and the two named
lemmas let the parent be pure fuel arithmetic. The real work lives one level
down, in `geometric_progress` and `geometric_preservation`, whose proofs do
their own inductions.

## When to use it, and when not

Use it when a value computed by unrolling a loop `fuel` times is known at one
fuel bound by a base lemma, and a preservation lemma says one more step of
fuel leaves the value unchanged; then an induction on the surplus fuel carries
the base to every larger fuel. Generalise the other arguments first (`revert
n`) so the induction hypothesis covers every starting state. Avoid it when the
base value or the preservation step is not already a named lemma — here each
child closes only by specialising an unprimed sibling, so lifting those to
named lemmas is the actual decomposition — or when the value genuinely depends
on the surplus fuel, in which case no such induction can close.

## Consequences

The induction creates a base case that must equal the value at the minimal
fuel (discharged by `geometric_progress'`) and a step case that rewrites the
induction hypothesis backwards through `geometric_preservation'`, leaving the
side conditions `¬ m = 0` and `n ≥ m` to the parent, discharged here by
`trivial` and `Nat.le_add_left`. Because the preservation lemma is applied
backwards (`rw [← geometric_preservation']`), the parent's arithmetic
`B : succ extra + (n + 1) = extra + n + 2` must exactly match the lemma's
left-hand fuel `n + 2`; a differently shaped fuel term makes the rewrite fail
to fire. The unprimed siblings `geometric_progress` and `geometric_preservation`
are each proved by their own induction, so the cost of the move is two levels
of lemmas rather than one.

## Verification

<!-- verification:start -->
Status: **verified**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/lean_build.yml (Verify): leanprover/lean-action@v1 with -R -Kwerror builds the whole Lean project on pushes to main; pinned commit a2c53bb5ff790e729e252958060699b7eff898b9 is on main | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: geometric_progress'@SampCert/Samplers/Geometric/Properties.lean:278, geometric_preservation'@SampCert/Samplers/Geometric/Properties.lean:285; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at a2c53bb5ff790e729e252958060699b7eff898b9 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(geometric_characterization, SampCert/Samplers/Geometric/Properties.lean, 272-290) -> declared: geometric_characterization is declared at SampCert/Samplers/Geometric/Properties.lean:272 | check_claims.py |
| 2 | verified | cites(geometric_characterization, geometric_progress') -> cites: geometric_progress' occurs at SampCert/Samplers/Geometric/Properties.lean:278 | check_claims.py |
| 3 | verified | cites(geometric_characterization, geometric_preservation') -> cites: geometric_preservation' occurs at SampCert/Samplers/Geometric/Properties.lean:285 | check_claims.py |
| 4 | verified | Checked copied code: parent site Properties.lean 272-290 is 19 lines (290-272+1); child sites 186-194 is 9 lines and 235-267 is 33 lines; geometric_progress' (188) cites geometric_progress (declared 162-181), geometric_preservation' (240) cites geometric_preservation (199-230), so depth 2; entry lists exactly 2 children (geometric_progress', geometric_preservation') | verifier |
| 5 | verified | Checked copied code: line 312 is the rewrite 'rw [geometric_characterization trial _ _ h]', inside the proof of theorem geometric_pwc_sup (starts line 295), reusing geometric_characterization | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | object | Correctness review. The decomposition is as described and closes: parent geometric_characterization (272-290) is an induction on extra after 'revert n'; the glue cites exactly the two children, geometric_progress' (base, line 278) and geometric_preservation' (step, line 285), and the step closes with trivial / trivial / exact Nat.le_add_left n extra (no sorry). Child statements match code verbatim; shape numbers are right (direct_lemmas=2, glue_lines 272-290 = 19, child_lines 186-194 = 9 and 235-267 = 33). Objection: the README step-case bullet says the parent discharges the side condition 'extra >= n', but the code discharges 'n >= m' instantiated with n := extra + n, m := n (the fuel (extra + n) + 1 matches the lemma's n' + 1), i.e. 'extra + n >= n', closed by Nat.le_add_left n extra. Fix: change 'extra >= n' to 'extra + n >= n' (lemma n := extra + n, m := n), and describe the three goals as one fuel identity (succ extra + (n+1) = extra + n + 2 via succ_add_eq_add_succ), one not-n=0 via trivial, and one extra + n >= n via Nat.le_add_left n extra. | reviewer-correctness |
| generality | accept | Move is stated generically, not just as this probGeometric case: applicability gives a goal_shape/use_when in terms of 'a value computed by unrolling a loop fuel times' plus a base lemma and a preservation lemma, and also_known_as names fuel induction / induction on a surplus counter / generalising the loop counter before induction (revert n; induction extra). 'When not to use' is honest and specific: it admits the real work is one level down in the unprimed siblings, and that the induction cannot close when the value depends on the surplus fuel. Consequences are honest and specific, including the concrete failure mode that rw [<- geometric_preservation'] needs the parent's fuel term to match the lemma's n+2 shape exactly. README explicitly states what makes the children good leaves for a bounded prover: self-contained statements (a closed form at one fuel bound; a one-more-fuel-step-does-nothing equation), each closing on its own from a single sibling without exposing the induction to the parent. Code excerpts at the cited ranges (272-290, 186-194, 235-267) match the descriptions. | reviewer-generality |
| provenance-licence | accept | commit a2c53bb5ff790e729e252958060699b7eff898b9 is identical across entry.json, source.json and SOURCE.md; all permalinks use that commit; licence Apache-2.0 recorded in entry.json, source.json and SOURCE.md and matches upstream-LICENSE (Apache-2.0 text); check_provenance passes (Code.lean 920B and Properties.lean 13085B byte-identical at the commit); cited line ranges 272-290, 186-194, 235-267 and 312 verified against the local copy and match the README excerpts and entry statements. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover/sampcert at commit `a2c53bb5ff790e729e252958060699b7eff898b9`, under `Apache-2.0`; see the [source note](../../sources/sampcert/SOURCE.md) for the licence text and attribution.
