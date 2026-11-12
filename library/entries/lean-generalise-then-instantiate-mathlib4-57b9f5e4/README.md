# Generalise IMO 1977 Q6 to f : ℕ → ℕ, then instantiate to ℕ+ via a garbage extension at 0

| | |
|---|---|
| Kind | instance |
| Move | generalise-then-instantiate |
| Language | lean |
| Status | accepted |
| Source | [mathlib4](../../sources/mathlib4/SOURCE.md) at `e1545ebed975` |
| Licence | `Apache-2.0` |

## Intent

Reduce IMO 1977 Q6 for `f : ℕ+ → ℕ+` to the same statement over `ℕ`, which is
easier because `ℕ` has `0` (a place to put a garbage value) and an induction
principle. The ℕ+ version is then recovered by extending the given function to
a total `ℕ → ℕ` function and instantiating, so the difficult proof is written
once, over the ambient type, and never repeated for the subtype.

## The decomposition

### parent `imo1977_q6_nat`: [`Archive/Imo/Imo1977Q6.lean` lines 23-35](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Imo/Imo1977Q6.lean#L23-L35) ([local copy](code/Archive/Imo/Imo1977Q6.lean))

```lean
public theorem imo1977_q6_nat (f : ℕ → ℕ) (h : ∀ n, f (f n) < f (n + 1)) : ∀ n, f n = n := by
  have h' (k n : ℕ) (hk : k ≤ n) : k ≤ f n := by
    induction k generalizing n with
    | zero => exact Nat.zero_le _
    | succ k h_ind =>
      apply Nat.succ_le_of_lt
      calc
        k ≤ f (f (n - 1)) := h_ind _ (h_ind (n - 1) (le_tsub_of_add_le_right hk))
        _ < f n := tsub_add_cancel_of_le (le_trans (Nat.succ_le_succ (Nat.zero_le _)) hk) ▸ h _
  have hf : ∀ n, n ≤ f n := fun n => h' n n rfl.le
  have hf_mono : StrictMono f := strictMono_nat_of_lt_succ fun _ => lt_of_le_of_lt (hf _) (h _)
  intro
  exact Nat.eq_of_le_of_lt_succ (hf _) (hf_mono.lt_iff_lt.mp (h _))
```

### child `imo1977_q6`: [`Archive/Imo/Imo1977Q6.lean` lines 41-48](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Imo/Imo1977Q6.lean#L41-L48) ([local copy](code/Archive/Imo/Imo1977Q6.lean))

```lean
public theorem imo1977_q6 (f : ℕ+ → ℕ+) (h : ∀ n, f (f n) < f (n + 1)) : ∀ n, f n = n := by
  intro n
  have := by
    refine imo1977_q6_nat (fun m => if 0 < m then f m.toPNat' else 0) ?_ n
    intro x; cases x
    · simp
    · simpa using! h _
  simpa
```

### context `module_comment`: [`Archive/Imo/Imo1977Q6.lean` lines 10-18](https://github.com/leanprover-community/mathlib4/blob/e1545ebed97594477bbd88b2fe948ffce56e5af2/Archive/Imo/Imo1977Q6.lean#L10-L18) ([local copy](code/Archive/Imo/Imo1977Q6.lean))

```lean
/-!
# IMO 1977 Q6

Suppose `f : ℕ+ → ℕ+` satisfies `f(f(n)) < f(n + 1)` for all `n`.
Prove that `f(n) = n` for all `n`.

We first prove the problem statement for `f : ℕ → ℕ`
then we use it to prove the statement for positive naturals.
-/
```

How the parts fit. The parent `imo1977_q6_nat` states the problem over
`f : ℕ → ℕ` (the ambient type, which has `0`). Its proof (lines 24-35) never
mentions ℕ+:

1. The key invariant `h' : k ≤ n → k ≤ f n` (lines 24-31) is proved by
   `induction k generalizing n`; the successor step is a `calc` chain
   `k ≤ f (f (n - 1)) < f n` that uses the hypothesis `h` at `n - 1`.
2. `hf : n ≤ f n` instantiates `h'` with `k = n` (line 32).
3. `hf_mono : StrictMono f` follows from `hf` and `h` (line 33).
4. `Nat.eq_of_le_of_lt_succ` closes `f n = n` (line 35).

The child `imo1977_q6` restores the ℕ+ statement. It extends the given
`f : ℕ+ → ℕ+` to a total function `f' : ℕ → ℕ := fun m => if 0 < m then f m.toPNat' else 0`:
at `m = 0` the garbage value `0`, and at positive `m` the value `f m.toPNat'`
(`Nat.toPNat'` sends `n + 1` to itself; see [`Mathlib/Data/PNat/Defs.lean`](code/Mathlib/Data/PNat/Defs.lean)).
Then `refine imo1977_q6_nat f' ?_ n` instantiates the parent; the one remaining
obligation, `∀ x, f' (f' x) < f' (x + 1)`, is discharged by `cases x` —
`· simp` closes the `0` case, `· simpa using! h _` the positive case — and a
final `simpa` coerces `f' n = n` in ℕ back to `f n = n` in ℕ+.

So the generalisation buys the whole argument for the price of an extension:
the child is 8 lines, none of which re-derive the induction.

## Why it is good

1. *(author-statement)* The authors state the plan in the module comment:
   "We first prove the problem statement for `f : ℕ → ℕ` then we use it to prove
   the statement for positive naturals." (lines 16-17).
2. *(check)* The child `imo1977_q6` is closed by instantiating the parent at the
   extension `fun m => if 0 < m then f m.toPNat' else 0` (line 44), discharging
   the new hypothesis by `intro x; cases x` into `· simp` and `· simpa using! h _`,
   and finishing with `simpa` (lines 41-48).
3. *(check)* The file builds as part of mathlib4's CI:
   `.github/workflows/build.yml` runs on push to `master` and delegates to
   `build_template.yml`, which builds the Archive library
   (`lake-build-with-retry.sh Archive Counterexamples Wanted`, line 252) and
   fails the job if Archive did not build (lines 410-414).
4. *(measurement)* The instantiation adds no new mathematics: the child's body
   is 7 lines (42-48) that only extend `f`, apply the parent, `cases`, and
   `simpa`; the parent's 8-line induction/`calc` (24-31) is never repeated.

In my opinion the reusable detail is the pair of obligations the move exposes —
a total, decidable extension and a `cases` on the added element — because those
are exactly what any later instantiation must supply, and both are cheap here.

## When to use it, and when not

Use it when the statement is over a subtype (here `ℕ+`, but also a finite set or
a `Subtype`) whose ambient type has an extra, harmless element and a recursion
principle the subtype lacks, and when the ambient-type proof does not actually
need that extra element (here the induction uses `n - 1`, and the extension's `0`
only shows up in the `simp` case). The general theorem's hypothesis must
transfer by a case on the added element, and the conclusion must coerce back (in
Lean, `simpa`). Avoid it when the object cannot be extended totally (no
decidable default), when the hypothesis cannot be discharged for the extension
without re-proving the argument, or when the ambient-type statement is not
actually easier than the subtype one. Survey F §8 lists "generalise /
strengthen" as a free move with no measured ablation and gives it no numbered
rule in §10, so this entry documents a clean instance but supports none of the
18 candidate rules (`rule` is `none`).

## Consequences

Three obligations beyond the general statement: (1) extend the given object to
the ambient type with a total default (`else 0` at `m = 0`); (2) prove the
general theorem's hypothesis for the extension, a case split on the added
element (`cases x`, `simp` at 0, `simpa using! h _` otherwise); (3) coerce the
ambient-type conclusion back to the subtype (`simpa`). Failure modes: the
garbage value can leak into the proof if the general statement's conclusion is
not literally `f n = n` (then `simpa` may not close); the extension must be
decidable (`if 0 < m` needs `Decidable`); and the ambient type must genuinely
be easier — if the proof needs the missing element, the generalisation is not
the simplification it looks like.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml (on: push, lines 3-14) invokes .github/workflows/build_template.yml (line 35 uses), whose step 'build archive, counterexamples and wanted' runs '../tools-branch/scripts/lake-build-with-retry.sh Archive Counterexamples Wanted' (line 252) and step 'Check if building Archive or Counterexamples failed' (lines 410-419) exits 1 if Archive did not build, so Archive/Imo/Imo1977Q6.lean is built. Pinned commit e1545ebed97594477bbd88b2fe948ffce56e5af2 confirmed on master (default branch) via GitHub compare API: status ahead, ahead_by 1, behind_by 0. | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 2 file(s) byte-identical at e1545ebed97594477bbd88b2fe948ffce56e5af2 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Copied file Archive/Imo/Imo1977Q6.lean lines 16-17 read: 'We first prove the problem statement for f over Nat, then we use it to prove the statement for positive naturals.' Matches the quoted module comment verbatim (backtick f : N -> N backtick). | verifier |
| 2 | verified | Copied code Archive/Imo/Imo1977Q6.lean lines 41-48: line 41 'public theorem imo1977_q6 (f : ℕ+ → ℕ+) (h : ...) : ∀ n, f n = n := by', line 44 'refine imo1977_q6_nat (fun m => if 0 < m then f m.toPNat' else 0) ?_ n' instantiates the parent at the extension, line 45 'intro x; cases x', line 46 '· simp' (x=0), line 47 '· simpa using! h _' (positive), line 48 'simpa' closes the goal — all as claimed. | verifier |
| 3 | verified | Fetched .github/workflows/build_template.yml and build.yml at e1545ebed97594477bbd88b2fe948ffce56e5af2 via fetch_file.py. build_template.yml line 252 runs '../tools-branch/scripts/lake-build-with-retry.sh Archive Counterexamples Wanted'; lines 410-419 are the step 'Check if building Archive or Counterexamples failed' which prints an error and exits 1 if steps.archive.outcome == 'failure'. build.yml lines 3-4 'on: push:' (branches-ignore excludes only bors/experiment branches, not master) and line 35 'uses: ./.github/workflows/build_template.yml'. | verifier |
| 4 | verified | Copied code Archive/Imo/Imo1977Q6.lean: child body is lines 42-48 = 7 lines (intro n; have := by; refine ... at line 44; intro x; cases x; · simp; · simpa using! h _; simpa), none re-deriving the induction; parent induction/calc block is lines 24-31 = 8 lines (have h' ... := by / induction k generalizing n with / | zero / | succ ... calc), and this block appears nowhere in the child (lines 41-48). Line counts match the claim. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Copied code Archive/Imo/Imo1977Q6.lean matches the entry: parent imo1977_q6_nat (L23-35) states the problem over Nat->Nat; child imo1977_q6 (L41-48) states it over PNat->PNat and instantiates the parent at the garbage extension 'fun m => if 0 < m then f m.toPNat' else 0' (L44), discharges the transferred hypothesis by 'intro x; cases x' into 'simp' (x=0) and 'simpa using! h _' (positive), then closes with 'simpa' (L48). The decomposition, children, and closing methods all match the code, and it closes (build CI-recorded: build_template.yml builds Archive). | reviewer-correctness |
| generality | accept | Move generalises beyond the example: goal_shape names the shape (subtype/restricted domain whose ambient type has a harmless extra element plus a recursion principle), and the README extends it to finite sets and Subtype. When-not-to-use and consequences are honest and specific and match the copied code: three obligations (total decidable extension 'if 0<m then f m.toPNat else 0', cases on the added element, final simpa) and failure modes (garbage leaks if the conclusion is not literally f n = n; Decidable required; ambient type must genuinely be easier). | reviewer-generality |
| provenance-licence | accept | check_provenance passes (2 files byte-identical at e1545ebed97594477bbd88b2fe948ffce56e5af2). Commit e1545ebed97594477bbd88b2fe948ffce56e5af2 is consistent across entry.json, README, sources/mathlib4/SOURCE.md and source.json; all permalinks pin that immutable commit and their line ranges match the copied file (parent 23-35, child 41-48, module comment 10-18 verified against code/Archive/Imo/Imo1977Q6.lean). Licence Apache-2.0 recorded in entry.json/README/source.json, matches the file copyright headers ('Released under Apache 2.0 license') and the upstream-LICENSE text; source note and its attribution are consistent with the copied files. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover-community/mathlib4 at commit `e1545ebed97594477bbd88b2fe948ffce56e5af2`, under `Apache-2.0`; see the [source note](../../sources/mathlib4/SOURCE.md) for the licence text and attribution.
