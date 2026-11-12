# Key invariant: each of x, y, z is 1 for USA 1973 P4

| | |
|---|---|
| Kind | instance |
| Move | key-invariant |
| Language | lean |
| Status | accepted |
| Source | [compfiles](../../sources/compfiles/SOURCE.md) at `1745e6ced3e6` |
| Licence | `Apache-2.0` |

## Intent

Prove the forward direction of USA 1973 P4 — that `x + y + z = 3 ∧
x ^ 2 + y ^ 2 + z ^ 2 = 3 ∧ x ^ 3 + y ^ 3 + z ^ 3 = 3` forces
`(x, y, z) = (1, 1, 1)` — by deriving the two remaining elementary symmetric
sums and then packaging the conclusion "each of x, y, z is 1" as one
invariant, proved once and instantiated three times.

## The decomposition

### parent `usa1973_p4`: [`Compfiles/Usa1973P4.lean` lines 29-49](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Usa1973P4.lean#L29-L49) ([local copy](code/Compfiles/Usa1973P4.lean))

```lean
problem usa1973_p4 (x y z : ℂ) :
    x + y + z = 3 ∧
    x ^ 2 + y ^ 2 + z ^ 2 = 3 ∧
    x ^ 3 + y ^ 3 + z ^ 3 = 3 ↔ ⟨x,y,z⟩ ∈ solution_set := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have e2 : x*y + y*z + z*x = 3 := by
      linear_combination (1/2 : ℂ) * ((x+y+z+3) * h1 - h2)
    have e3 : x*y*z = 1 := by
      linear_combination (1/3 : ℂ) * (h3 - (x^2+y^2+z^2 - (x*y+y*z+z*x)) * h1 - 3 * h2 + 3 * e2)
    have key : ∀ t, t = x ∨ t = y ∨ t = z → t = 1 := by
      rintro t ht
      have : (t - 1)^3 = 0 := by
        rcases ht with rfl | rfl | rfl
        · linear_combination t^2 * h1 - t * e2 + e3
        · linear_combination t^2 * h1 - t * e2 + e3
        · linear_combination t^2 * h1 - t * e2 + e3
      exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)
    simp [solution_set, key x (by simp), key y (by simp), key z (by simp)]
  rintro _
  grind
```

### context `e2_e3`: [`Compfiles/Usa1973P4.lean` lines 34-38](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Usa1973P4.lean#L34-L38) ([local copy](code/Compfiles/Usa1973P4.lean))

```lean
  · rintro ⟨h1, h2, h3⟩
    have e2 : x*y + y*z + z*x = 3 := by
      linear_combination (1/2 : ℂ) * ((x+y+z+3) * h1 - h2)
    have e3 : x*y*z = 1 := by
      linear_combination (1/3 : ℂ) * (h3 - (x^2+y^2+z^2 - (x*y+y*z+z*x)) * h1 - 3 * h2 + 3 * e2)
```

### child `key`: [`Compfiles/Usa1973P4.lean` lines 39-46](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Usa1973P4.lean#L39-L46) ([local copy](code/Compfiles/Usa1973P4.lean))

```lean
    have key : ∀ t, t = x ∨ t = y ∨ t = z → t = 1 := by
      rintro t ht
      have : (t - 1)^3 = 0 := by
        rcases ht with rfl | rfl | rfl
        · linear_combination t^2 * h1 - t * e2 + e3
        · linear_combination t^2 * h1 - t * e2 + e3
        · linear_combination t^2 * h1 - t * e2 + e3
      exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)
```

### skeleton `application`: [`Compfiles/Usa1973P4.lean` lines 47-47](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Usa1973P4.lean#L47-L47) ([local copy](code/Compfiles/Usa1973P4.lean))

```lean
    simp [solution_set, key x (by simp), key y (by simp), key z (by simp)]
```

How the parts fit. The parent is an `↔`; the key-invariant lives only in the
forward direction (`· rintro ⟨h1, h2, h3⟩`, line 34), while the backward
direction closes trivially by `grind` (lines 48-49). The forward direction
decomposes into three `have` obligations, then one application:

1. **`e2`** (`x*y + y*z + z*x = 3`) and **`e3`** (`x*y*z = 1`) fix the two
   remaining elementary symmetric sums from the three power sums `h1`, `h2`,
   `h3`. Each closes by a single `linear_combination` (lines 35-38). Together
   with `h1 : x + y + z = 3` they pin down the cubic whose roots are x, y, z:
   `T^3 - (x+y+z)T^2 + (xy+yz+zx)T - xyz = T^3 - 3T^2 + 3T - 1 = (T-1)^3`.

2. **`key`** (the invariant, lines 39-46) is the single auxiliary statement
   that carries the idea. Instead of proving `x = 1`, `y = 1`, `z = 1`
   separately, it states once that *any* `t` equal to one of the three equals
   1. Its proof: take `ht : t = x ∨ t = y ∨ t = z` and show `(t - 1)^3 = 0` by
   a three-way `rcases ht with rfl | rfl | rfl` (line 42). In each case `t` is
   one of the roots, so `t^2 * h1 - t * e2 + e3` is the linear combination
   `t^2·(x+y+z) - t·(xy+yz+zx) + xyz`, which by the three facts equals
   `t^3` on one side and `3t^2 - 3t + 1` on the other — i.e. it proves
   `t^3 - 3t^2 + 3t - 1 = 0`, which is `(t-1)^3 = 0`. The identical
   `linear_combination t^2 * h1 - t * e2 + e3` (lines 43-45) closes each
   case. Then
   `sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)` (line 46) turns
   `(t - 1)^3 = 0` into `t = 1` (over `ℂ`, `pow_eq_zero_iff` for exponent 3).

3. **application** (line 47) instantiates the invariant at each variable in a
   single `simp`: `key x (by simp)`, `key y (by simp)`, `key z (by simp)`
   give `x = 1`, `y = 1`, `z = 1`, which `simp` reduces to
   `⟨x, y, z⟩ ∈ solution_set`.

The invariant is the point of the entry: the three symmetric conclusions are
stated once, proved once by a uniform case split, and reused three times.

## Why it is good

1. The invariant `key` is proved by a three-way `rcases ht with rfl | rfl |
   rfl` and each case closes with the *same* tactic
   `linear_combination t^2 * h1 - t * e2 + e3` (lines 42-45) — a `check`, from
   the permalink.
2. The forward direction then closes with one `simp` that instantiates the
   invariant at x, y and z (line 47), with no further case analysis — a
   `check`, from the permalink.
3. `key` is instantiated exactly three times in the closing step, once per
   variable (counted on line 47) — a `measurement`.
4. The problem is stated symmetrically in x, y, z — "Find all complex numbers
   x, y, z which satisfy x + y + z = x² + y² + z² = x³ + y³ + z³ = 3."
   (lines 21-22) — which is what lets the three identical conclusions become
   one `∀ t` invariant — an `author-statement`.

In my opinion the detail worth copying is the *shape* of the invariant: it is
stated over a free `t` with the disjunction `t = x ∨ t = y ∨ t = z`, rather
than as a conjunction `x = 1 ∧ y = 1 ∧ z = 1`. That shape is what makes the
proof a single uniform case split and the use a single `simp`.

## When to use it, and when not

Use it when several variables must each satisfy the same conclusion and the
hypotheses treat them interchangeably (symmetric sums, cyclic constraints),
so that the per-variable conclusions can be packaged as
`∀ t, t = x ∨ t = y ∨ t = z → P t`. State the invariant over a free `t`, prove
it once, then instantiate at each variable in one closing step.

Avoid it when the variables are not interchangeable (each has its own
hypothesis), when the invariant's cases need different arguments (the shared
`linear_combination`/tactic would not be uniform), or when the closing step is
not uniform across variables. Also avoid it when the intermediate facts that
feed the invariant (here `e2`, `e3`) are themselves the hard part; then those
lemmas are the real content and belong before the invariant.

## Consequences

The move obliges the proof to first derive the other two elementary symmetric
sums (`e2 = x*y + y*z + z*x`, `e3 = x*y*z`) from the given power sums, and the
invariant's own proof needs a case split over the disjunction
`t = x ∨ t = y ∨ t = z`. The invariant must be stated over a free `t`, and the
per-case `linear_combination` must be one identical expression; if one
variable enters the symmetric relations in a different form, the shared tactic
breaks and the invariant has to be split again.

Against the harvest's survey F §10 rule 11 ("hypothesis consequences go to a
bounded, pruned pool; drop any candidate not cited"), this entry *supports* the rule:
`key` is exactly a hypothesis consequence (derived from `h1`, `h2`, `h3` via
`e2`, `e3`) that earns its keep by being cited three times in the closing
step, and it is kept precisely where an uncited consequence would be pruned.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push-main.yaml runs 'lake build' on push to main (default branch); main HEAD = 1745e6ced3e671bd74417548494b034eb2c87da8 = pinned commit, so CI builds Compfiles/Usa1973P4.lean (a module under Compfiles/, imported by the lake build) | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 1745e6ced3e671bd74417548494b034eb2c87da8 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Copied file Compfiles/Usa1973P4.lean (byte-identical to pinned commit): line 42 is 'rcases ht with rfl | rfl | rfl'; lines 43-45 are each '· linear_combination t^2 * h1 - t * e2 + e3' (identical). | verifier |
| 2 | verified | Copied file line 47: 'simp [solution_set, key x (by simp), key y (by simp), key z (by simp)]' - a single simp instantiating key at x, y, z; no further rcases/case analysis follows in the forward branch. | verifier |
| 3 | verified | Copied file line 47 contains exactly three subterms key x, key y, key z (once each); count = 3. | verifier |
| 4 | verified | Copied file lines 21-22 read verbatim: 'Find all complex numbers x, y, z which satisfy' / '  x + y + z = x² + y² + z² = x³ + y³ + z³ = 3.' The problem statement is symmetric in x, y, z. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Copied code Compfiles/Usa1973P4.lean matches every element of the entry: parent usa1973_p4 is the iff at lines 29-49; children e2 (x*y+y*z+z*x=3, closed by linear_combination (1/2)*( (x+y+z+3)*h1 - h2), line 36), e3 (x*y*z=1, line 38), and key (forall t, t=x | t=y | t=z -> t=1, lines 39-46) match the statements and closing tactics verbatim. key's proof does the three-way rcases rfl|rfl|rfl (line 42) and each case closes with the identical linear_combination t^2*h1 - t*e2 + e3, which in each case reduces the LHS to t^3 and the RHS to 3t^2-3t+1, i.e. (t-1)^3=0; sub_eq_zero.mp (pow_eq_zero_iff ..) then yields t=1. The skeleton (line 47) closes the forward direction with one simp instantiating key at x, y, z (three times). So the decomposition is what the entry says, children and closing methods match the code, and the proof closes. | reviewer-correctness |
| generality | accept | Move stated beyond the example: applicability.use_when and README 'When to use it' generalize from t = 1 to P t and to any tuple of interchangeable variables (package as forall t, t = x \/ t = y \/ t = z -> P t, prove once, instantiate per variable), naming the general precondition that hypotheses treat variables interchangeably (symmetric sums, cyclic constraints). 'When not to use' is specific and honest: three concrete failure modes (variables not interchangeable / each with its own hypothesis; invariant cases needing different arguments so the shared tactic is non-uniform; closing step not uniform) plus the caveat that e2/e3-style intermediate facts are themselves the real content. Consequences are specific and honest: name the free-t requirement and the failure mode that a variable entering the symmetric relations in a different form breaks the shared tactic. No overreach: the writer's own judgement about the shape is labelled as opinion, kept out of claims. | reviewer-generality |
| provenance-licence | accept | check_provenance.py passes (file byte-identical at pinned commit 1745e6ced3e671bd74417548494b034eb2c87da8). Commit hash is consistent across source.json, sources/compfiles/SOURCE.md, entry.json files+site permalinks and all claim permalinks. Licence Apache-2.0 is consistent across source.json, SOURCE.md, entry.json and the copied file header ('Released under Apache 2.0 license as described in the file LICENSE'); upstream-LICENSE contains the Apache 2.0 text. Permalink line ranges (parent 29-49, context 34-38, child 39-46, skeleton 47, claims 42-45/47/21-22) match the copied code/Compfiles/Usa1973P4.lean line-for-line. Source note links to the LICENSE file and records verbatim-copy attribution. Everything traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/dwrensha/compfiles at commit `1745e6ced3e671bd74417548494b034eb2c87da8`, under `Apache-2.0`; see the [source note](../../sources/compfiles/SOURCE.md) for the licence text and attribution.
