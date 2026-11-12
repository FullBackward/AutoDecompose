# Suffices to the bracketed conditioning for the conditional mutual information step of sum_of_rdist_eq

| | |
|---|---|
| Kind | instance |
| Move | suffices-or-strengthen |
| Language | lean |
| Status | accepted |
| Source | [pfr](../../sources/pfr/SOURCE.md) at `1ef23c3c5a83` |
| Licence | `Apache-2.0` |

## Intent

The conditional mutual information step of the fibring identity is proved by
restating it with the conditioning rewritten from the expanded
`Y 0 - Y 1 - Y 2 + Y 3` to the bracketed difference `Y 0 - Y 1 - (Y 2 - Y 3)`.
The bracketed form exposes a single difference `(Y 0 - Y 1) - (Y 2 - Y 3)` so
that the injective-map lemma `condMutualInfo_of_inj_map` matches, and the
residual difference between the two conditioning forms is closed by
`convert this using 2; abel`.

## The decomposition

### parent `sum_of_rdist_eq_step_condMutualInfo`: [`PFR/Fibring.lean` lines 120-123](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/Fibring.lean#L120-L123) ([local copy](code/PFR/Fibring.lean))

```lean
lemma sum_of_rdist_eq_step_condMutualInfo {Y : Fin 4 → Ω → G}
    (h_meas : ∀ i, Measurable (Y i)) :
    I[⟨Y 0 - Y 1, Y 2 - Y 3⟩:⟨Y 0 - Y 2, Y 1 - Y 3⟩|Y 0 - Y 1 - (Y 2 - Y 3);μ] =
    I[Y 0 - Y 1 : Y 1 - Y 3|Y 0 - Y 1 - Y 2 + Y 3;μ] := by
```

### skeleton `sum_of_rdist_eq_step_condMutualInfo.suffices`: [`PFR/Fibring.lean` lines 124-125](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/Fibring.lean#L124-L125) ([local copy](code/PFR/Fibring.lean))

```lean
  suffices I[⟨Y 0 - Y 1, Y 2 - Y 3⟩:⟨Y 0 - Y 2, Y 1 - Y 3⟩|Y 0 - Y 1 - (Y 2 - Y 3);μ] =
    I[Y 0 - Y 1 : Y 1 - Y 3|Y 0 - Y 1 - (Y 2 - Y 3) ; μ] by convert this using 2; abel
```

### child `close_suffices`: [`PFR/Fibring.lean` lines 126-145](https://github.com/teorth/pfr/blob/1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a/PFR/Fibring.lean#L126-L145) ([local copy](code/PFR/Fibring.lean))

```lean
  symm
  have hm (f : G → G → G × G) {a b i j k l : Fin 4} :
    Measurable (uncurry f ∘ ⟨Y i - Y j - (Y k - Y l), Y a - Y b⟩) := by fun_prop
  have hmf : Measurable fun ω ↦ ((Y 0 - Y 1) ω, (Y 0 - Y 1) ω - (Y 0 - Y 1 - (Y 2 - Y 3)) ω) :=
    hm (fun z x ↦ (x, x - z))
  have hmg : Measurable fun ω ↦ ((Y 1 - Y 3) ω + (Y 0 - Y 1 - (Y 2 - Y 3)) ω, (Y 1 - Y 3) ω) :=
    hm (fun z x ↦ (x + z, x))
  have hmij {i j : Fin 4} : Measurable (Y i - Y j) := (h_meas _).sub (h_meas _)
  have hm0123 {i j k l : Fin 4} : Measurable (Y i - Y j - (Y k - Y l)) :=
    ((h_meas _).sub (h_meas _)).sub ((h_meas _).sub (h_meas _))
  rw [← condMutualInfo_of_inj_map hmij hmij hm0123 (fun z x ↦ (x, x - z)),
    condMutualInfo_comm hmf hmij,
    ← condMutualInfo_of_inj_map hmij hmf hm0123 (fun z x ↦ (x + z, x)),
    condMutualInfo_comm hmg hmf]
  · congr! 3 with ω
    · simp
    · rw [sub_sub, add_sub_left_comm, ← sub_sub]
      simp
  · exact fun _ _ _ h ↦ (Prod.ext_iff.1 h).2
  exact fun _ _ _ h ↦ (Prod.ext_iff.1 h).1
```

How the parts fit. The parent `sum_of_rdist_eq_step_condMutualInfo` proves
that `I[⟨Y 0 - Y 1, Y 2 - Y 3⟩ : ⟨Y 0 - Y 2, Y 1 - Y 3⟩ | Z]` equals
`I[Y 0 - Y 1 : Y 1 - Y 3 | Z]`, where the goal writes `Z` as
`Y 0 - Y 1 - Y 2 + Y 3`. The `suffices` (skeleton, lines 124-125) replaces the
goal with the *same* equality but with `Z` written as `Y 0 - Y 1 - (Y 2 - Y 3)`;
its `by` block closes the original goal from the restated one with
`convert this using 2; abel`. The child (lines 126-145) closes the restated
goal: `symm` reverses it, then a `rw` chain of `condMutualInfo_of_inj_map` and
`condMutualInfo_comm` (lines 136-139) rewrites `Y 0 - Y 1` into the pair
`⟨Y 0 - Y 1, Y 2 - Y 3⟩` via the injective map `(x, x - z)` and `Y 1 - Y 3`
into `⟨Y 0 - Y 2, Y 1 - Y 3⟩` via `(x + z, x)`. Those maps only simplify to
the desired pairs because the conditioning is the single difference
`z = Y 0 - Y 1 - (Y 2 - Y 3)`, so that `x - z = Y 2 - Y 3` and
`x + z = Y 0 - Y 2`. The pointwise equalities the maps introduce close by
`simp` (and `rw [sub_sub, add_sub_left_comm, ← sub_sub]`) inside
`congr! 3 with ω` (lines 140-143), and the two injectivity side goals close by
`(Prod.ext_iff.1 h).2` and `(Prod.ext_iff.1 h).1` (lines 144-145).

The definitions `condMutualInfo_of_inj_map` and `condMutualInfo_comm` that the
rewrites use are in [`code/PFR/ForMathlib/Entropy/Basic.lean`](code/PFR/ForMathlib/Entropy/Basic.lean)
(lines 931 and 962). `condMutualInfo_of_inj_map` states that
`I[f(Z, X) : Y | Z] = I[X : Y | Z]` whenever `f` is injective in its second
argument for each fixed first argument, which is exactly the device the whole
proof leans on.

## Why it is good

1. The restated goal closes by `symm` (line 126), a four-lemma `rw` chain of
   `condMutualInfo_of_inj_map` and `condMutualInfo_comm` (lines 136-139),
   `congr! 3 with ω` (lines 140-143), and the two injectivity side goals
   (lines 144-145). The file is built by the project's CI
   (`.github/workflows/push.yml` runs `leanprover/lean-action@v1.2.0`, i.e.
   `lake build`, on push to master and pull request). (*check*)
2. The difference between the bracketed `- (Y 2 - Y 3)` and the original
   `- Y 2 + Y 3` is discharged in one line by `convert this using 2; abel`
   (line 125). (*check*)
3. The `suffices` isolates a one-line discharge (line 125) from a 20-line proof
   of the restated goal (lines 126-145). (*measurement*)
4. The same "restate the goal into an equivalent arithmetic form and discharge
   the residual with a ring/linarith tactic" move appears elsewhere in the
   repository: `PFR/Endgame.lean` line 389 is
   `suffices sum4 = sum1 + p.η * (sum2 + sum3) by linarith`. (*known-use*)

In my opinion the detail worth copying is *why* the `suffices` is needed here
rather than a plain `rw`: `condMutualInfo_of_inj_map` matches on a single
difference, and `congr!` plus `simp` can close the residuals only when the
conditioning is already in that bracketed form. Writing it as `- Y 2 + Y 3`
would leave a residual that `simp` cannot discharge (it would need `abel`), so
the author pushes that single algebraic identity into the `suffices`' `by`
block and keeps the main proof `simp`-clean.

## When to use it, and when not

Use it when a rewrite you need is syntactic (a `rw`/definitional match) and
does not fire on the goal's stated form, but the form it needs differs from
the goal only by a ring/abel identity: restate the whole goal via `suffices`
with the subterm in the form the rewrite matches, prove the restated goal,
and close the residual with `convert … using 2; abel`.

Avoid it when the restated form is not actually reachable by the intended
rewrites (the `suffices` goal still has to close), when the residual is not a
ring identity that `convert`/`abel` can discharge, or when the original form
already matches the rewrite — then the `suffices` is redundant and a plain
`rw`/`have` does the job. The sibling lemma
`sum_of_rdist_eq_step_condRuzsaDist` in the same file (lines 93-117) faces the
same obligation — rewrite the statement so `condRuzsaDist_of_inj_map` applies —
and does it with `have h' … : ⟨Y i, Y j⟩ = ⟨Y i, Y i - (Y i - Y j)⟩ := by simp
only [sub_sub_cancel]` followed by `rw [h' 0 2, h' 1 3]` (lines 113-115),
because there the conditioning `Y i - Y j` already matches after a single
`simp`-lemma rewrite and no `suffices` is needed.

## Consequences

The move creates two obligations: the restated `suffices` goal, which must be
reachable by the rewrites that motivated the restatement, and the residual —
that the restated form implies the original — here a ring identity discharged
by `convert this using 2; abel`. A `suffices` whose restated form is not
actually matched by the intended lemma fails only when the restated goal is
attacked; the residual can silently become a stuck ring goal if the two forms
are not genuinely equal. The injectivity rewrites also leave side goals (that
each map is injective per fixed conditioning), closed here by
`(Prod.ext_iff.1 h).2` and `(Prod.ext_iff.1 h).1`.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push.yml at 1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a: 'Build project' job runs leanprover/lean-action@f807b338d95de7813c5c50d018f1c23c9b93b4ec (v1.2.0), i.e. lake build of the whole project incl. PFR/Fibring.lean, on push to master and pull_request; pinned commit is the default-branch (master) tip (source registered with ref HEAD) | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 2 file(s) byte-identical at 1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Checked local copy code/PFR/Fibring.lean (provenance-pass, byte-identical at 1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a): L126 symm; L136-139 rw [<-condMutualInfo_of_inj_map ..., condMutualInfo_comm hmf hmij, <-condMutualInfo_of_inj_map ..., condMutualInfo_comm hmg hmf] (4 lemmas); L140-143 congr! 3 with omega, subgoals simp and rw [sub_sub, add_sub_left_comm, <-sub_sub]; simp; L144-145 exact fun _ _ _ h => (Prod.ext_iff.1 h).2 / .1. CI evidence: .github/workflows/push.yml build job runs leanprover/lean-action@v1.2.0 (lake build) on push to master + pull_request | verifier |
| 2 | verified | Checked local copy code/PFR/Fibring.lean L124-125: L125 is 'I[Y 0 - Y 1 : Y 1 - Y 3|Y 0 - Y 1 - (Y 2 - Y 3) ; mu] by convert this using 2; abel'; the suffices (L124-125) restates the goal with conditioning 'Y 0 - Y 1 - (Y 2 - Y 3)' vs parent L123 'Y 0 - Y 1 - Y 2 + Y 3', residual closed by convert this using 2; abel | verifier |
| 3 | verified | Counted line spans in local copy code/PFR/Fibring.lean: discharge tactic on L125 (1 line, 'by convert this using 2; abel'); restated-goal proof spans L126 (symm) through L145 (last exact ... .1) = 20 lines (145-126+1). Matches metrics.discharge_lines=1, suffices_proof_lines=20 | verifier |
| 4 | verified | Fetched PFR/Endgame.lean at 1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a (raw view): L389 is 'suffices sum4 = sum1 + p.eta * (sum2 + sum3) by linarith' inside 'have h4 : sum4 <= ...' (L388), discharging the residual with linarith after restating into the equivalent arithmetic form | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Correctness verified against the copied code (PFR/Fibring.lean, provenance pass: 2 files byte-identical at 1ef23c3c5a83). Parent statement (L120-123), skeleton suffices (L124-125), and child close_suffices (L126-145) are transcribed exactly. The two children match: child 1 (suffices goal, bracketed conditioning) closes by symm (L126), the four-lemma rw chain of condMutualInfo_of_inj_map/condMutualInfo_comm (L136-139), congr! 3 with omega (L140-143), and the two injectivity side goals (L144-145); child 2 (residual original goal) closes by 'convert this using 2; abel' (L125). The maps are described correctly: Y0-Y1 -> <Y0-Y1,Y2-Y3> via (x,x-z) and Y1-Y3 -> <Y0-Y2,Y1-Y3> via (x+z,x) with z = Y0-Y1-(Y2-Y3), matching hmf/hmg (L129-132). The suffices restates only the right-hand conditioning from Y0-Y1-Y2+Y3 to Y0-Y1-(Y2-Y3), exactly as the intent states. Real compiling PFR code, so the proof closes. | reviewer-correctness |
| generality | accept | Move is stated at the tactic level ('suffices to a syntactic-match form, discharge the residual with convert/abel'), so it generalizes past this example: goal_shape names the general shape (syntactic injective-map rewrite only matching a single difference/sum), and claim 4's known-use (PFR/Endgame.lean L389 'suffices sum4 = sum1 + p.eta*(sum2+sum3) by linarith', confirmed in cache) shows the same move with linarith not abel. 'When not to use' is honest and specific: three concrete failure conditions, including the redundant-suffices case contrasted with sibling sum_of_rdist_eq_step_condRuzsaDist (lines 113-115) which uses a plain have/rw. Consequences name the two obligations and two concrete failure modes (restated goal unreachable; residual silently becoming a stuck ring goal), plus the injectivity side goals. No overclaim: the why-it's-needed insight is labelled opinion. | reviewer-generality |
| provenance-licence | accept | check_provenance passes (2 files byte-identical at pinned commit 1ef23c3c5a83); commit 1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a consistent across entry.json, source.json, SOURCE.md and every permalink; licence Apache-2.0 consistent across entry.json, README, source.json, SOURCE.md and the copied upstream-LICENSE (Apache 2.0 text); file/line permalinks match the copied Fibring.lean (parent L120-123, skeleton L124-125, child L126-145 verified line-for-line); source note present and correct. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/teorth/pfr at commit `1ef23c3c5a83db690fe3b3b5c2e8299fae17b81a`, under `Apache-2.0`; see the [source note](../../sources/pfr/SOURCE.md) for the licence text and attribution.
