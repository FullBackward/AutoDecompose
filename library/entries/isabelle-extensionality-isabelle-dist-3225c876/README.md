# Extensionality via gauss_eq_iff closes the three idom_modulo axioms for the Gaussian integers

| | |
|---|---|
| Kind | instance |
| Move | extensionality |
| Language | isabelle |
| Status | draft |
| Source | [isabelle-dist](../../sources/isabelle-dist/SOURCE.md) at `34ca456d44ca` |
| Licence | `BSD-3-Clause` |

## Intent

Prove that the Gaussian integers form an `idom_modulo` by discharging its three
axioms, each an equality of `gauss` values. The glue reduces every such
equality to integer arithmetic on the `Re` and `Im` components through the
extensionality lemma `gauss_eq_iff`, and turns the non-zero divisor into a
positive norm through `gauss_eq_0`.

## The decomposition

### parent `instance gauss :: idom_modulo`: [`src/HOL/Examples/Gauss_Numbers.thy` lines 323-341](https://github.com/isabelle-prover/mirror-isabelle/blob/34ca456d44ca14641450b5d52f51b38688d4d1b5/src/HOL/Examples/Gauss_Numbers.thy#L323-L341) ([local copy](code/src/HOL/Examples/Gauss_Numbers.thy))

```isabelle
instance proof
  fix x y :: gauss
  show \<open>x div 0 = 0\<close>
    by (simp add: gauss_eq_iff)
  show \<open>x * y div y = x\<close> if \<open>y \<noteq> 0\<close>
  proof -
    define Y where \<open>Y = (Re y)\<^sup>2 + (Im y)\<^sup>2\<close>
    moreover have \<open>Y > 0\<close>
      using that by (simp add: gauss_eq_0 less_le Y_def)
    have *: \<open>Im y * (Im y * Re x) + Re x * (Re y * Re y) = Re x * Y\<close>
      \<open>Im x * (Im y * Im y) + Im x * (Re y * Re y) = Im x * Y\<close>
      \<open>(Im y)\<^sup>2 + (Re y)\<^sup>2 = Y\<close>
      by (simp_all add: power2_eq_square algebra_simps Y_def)
    from \<open>Y > 0\<close> show ?thesis
      by (simp add: gauss_eq_iff algebra_simps) (simp add: * nonzero_mult_cdiv_cancel_right)
  qed
  show \<open>x div y * y + x mod y = x\<close>
    by (simp add: gauss_eq_iff)
qed
```

### child `gauss_eq_iff`: [`src/HOL/Examples/Gauss_Numbers.thy` lines 16-18](https://github.com/isabelle-prover/mirror-isabelle/blob/34ca456d44ca14641450b5d52f51b38688d4d1b5/src/HOL/Examples/Gauss_Numbers.thy#L16-L18) ([local copy](code/src/HOL/Examples/Gauss_Numbers.thy))

```isabelle
lemma gauss_eq_iff:
  \<open>x = y \<longleftrightarrow> Re x = Re y \<and> Im x = Im y\<close>
  by (auto intro: gauss_eqI)
```

### child `gauss_eq_0`: [`src/HOL/Examples/Gauss_Numbers.thy` lines 89-91](https://github.com/isabelle-prover/mirror-isabelle/blob/34ca456d44ca14641450b5d52f51b38688d4d1b5/src/HOL/Examples/Gauss_Numbers.thy#L89-L91) ([local copy](code/src/HOL/Examples/Gauss_Numbers.thy))

```isabelle
lemma gauss_eq_0:
  \<open>z = 0 \<longleftrightarrow> (Re z)\<^sup>2 + (Im z)\<^sup>2 = 0\<close>
  by (simp add: gauss_eq_iff sum_power2_eq_zero_iff)
```

### context `gauss-codatatype`: [`src/HOL/Examples/Gauss_Numbers.thy` lines 10-10](https://github.com/isabelle-prover/mirror-isabelle/blob/34ca456d44ca14641450b5d52f51b38688d4d1b5/src/HOL/Examples/Gauss_Numbers.thy#L10-L10) ([local copy](code/src/HOL/Examples/Gauss_Numbers.thy))

```isabelle
codatatype gauss = Gauss (Re: int) (Im: int)
```

### context `gauss_eqI`: [`src/HOL/Examples/Gauss_Numbers.thy` lines 12-14](https://github.com/isabelle-prover/mirror-isabelle/blob/34ca456d44ca14641450b5d52f51b38688d4d1b5/src/HOL/Examples/Gauss_Numbers.thy#L12-L14) ([local copy](code/src/HOL/Examples/Gauss_Numbers.thy))

```isabelle
lemma gauss_eqI [intro?]:
  \<open>x = y\<close> if \<open>Re x = Re y\<close> \<open>Im x = Im y\<close>
  by (rule gauss.expand) (use that in simp)
```

### context `divide-modulo-defs`: [`src/HOL/Examples/Gauss_Numbers.thy` lines 309-321](https://github.com/isabelle-prover/mirror-isabelle/blob/34ca456d44ca14641450b5d52f51b38688d4d1b5/src/HOL/Examples/Gauss_Numbers.thy#L309-L321) ([local copy](code/src/HOL/Examples/Gauss_Numbers.thy))

```isabelle
primcorec divide_gauss :: \<open>gauss \<Rightarrow> gauss \<Rightarrow> gauss\<close>
  where
    \<open>Re (x div y) = (Re x * Re y + Im x * Im y) cdiv ((Re y)\<^sup>2 + (Im y)\<^sup>2)\<close>
  | \<open>Im (x div y) = (Im x * Re y - Re x * Im y) cdiv ((Re y)\<^sup>2 + (Im y)\<^sup>2)\<close>

primcorec modulo_gauss :: \<open>gauss \<Rightarrow> gauss \<Rightarrow> gauss\<close>
  where
    \<open>Re (x mod y) = Re x -
      ((Re x * Re y + Im x * Im y) cdiv ((Re y)\<^sup>2 + (Im y)\<^sup>2) * Re y -
       (Im x * Re y - Re x * Im y) cdiv ((Re y)\<^sup>2 + (Im y)\<^sup>2) * Im y)\<close>
  | \<open>Im (x mod y) = Im x -
      ((Re x * Re y + Im x * Im y) cdiv ((Re y)\<^sup>2 + (Im y)\<^sup>2) * Im y +
       (Im x * Re y - Re x * Im y) cdiv ((Re y)\<^sup>2 + (Im y)\<^sup>2) * Re y)\<close>
```

How the parts fit. The lemma graph is a two-branch tree whose two leaves sit
directly under the parent, with one leaf (`gauss_eq_0`) resting on the other
(`gauss_eq_iff`):

```
instance gauss :: idom_modulo   (parent, 323-341)
 ├─ gauss_eq_iff  (child, 16-18)  — x = y  ⟷  Re x = Re y ∧ Im x = Im y
 └─ gauss_eq_0    (child, 89-91)  — z = 0  ⟷  (Re z)² + (Im z)² = 0
        └─ (gauss_eq_0 cites gauss_eq_iff)
```

`gauss` is a `codatatype` with two `int` selectors `Re` and `Im` (context
`gauss-codatatype`), so a `gauss` value is nothing but its two components. The
extensionality lemma `gauss_eq_iff` makes that explicit: an equality of `gauss`
values reduces to two integer equations. The parent is the `instance proof`
for `idom_modulo`, whose three `show` statements are exactly the three class
axioms (in HOL: `semiring_modulo`'s `div_mult_mod_eq`, `divide_trivial`'s
`div_by_0`, and `algebraic_semidom`'s `nonzero_mult_div_cancel_right`):

- `x div 0 = 0` (line 325) closes by `by (simp add: gauss_eq_iff)`: extensionality
  turns it into `Re (x div 0) = 0` and `Im (x div 0) = 0`, and the `divide_gauss`
  definition (context `divide-modulo-defs`) expands each to `… cdiv 0`, which
  `cdiv_0_eq` (`k cdiv 0 = 0`) closes.
- `x * y div y = x` if `y ≠ 0` (line 327) is the only non-trivial obligation.
  It defines the norm `Y = (Re y)² + (Im y)²`, derives `Y > 0` from `y ≠ 0`
  using `gauss_eq_0` (`using that by (simp add: gauss_eq_0 less_le Y_def)`),
  collects three algebra identities in the fact `*` (lines 332-335), then
  closes with `by (simp add: gauss_eq_iff algebra_simps) (simp add: *
  nonzero_mult_cdiv_cancel_right)`: extensionality reduces it to its components,
  `algebra_simps` plus `*` rewrite each to `(…) cdiv Y * Y`, and
  `nonzero_mult_cdiv_cancel_right` (`k * l cdiv l = k` if `l ≠ 0`) finishes
  using `Y > 0`.
- `x div y * y + x mod y = x` (line 339) closes by `by (simp add: gauss_eq_iff)`:
  extensionality reduces it to its components, and the `modulo_gauss` definition
  is literally `Re x`/`Im x` minus the matching div-times-y components, so the
  sum `div·y + mod` telescopes back to `x` on each component by `algebra_simps`.

Each child is a good leaf. `gauss_eq_iff` is a self-contained statement (value
equality iff component equality) whose proof `by (auto intro: gauss_eqI)`
closes from the sibling `gauss_eqI` — the extensionality intro rule `x = y` if
`Re x = Re y` and `Im x = Im y` (context `gauss_eqI`), which itself closes by
the codatatype rule `gauss.expand` — plus the automatic forward direction.
`gauss_eq_0` is self-contained and closes by `by (simp add: gauss_eq_iff
sum_power2_eq_zero_iff)`: from the sibling `gauss_eq_iff` and the library lemma
`sum_power2_eq_zero_iff`. Neither child names a further project lemma beyond
this one step, so the only non-trivial chain below the main theorem is
`instance → gauss_eq_0 → gauss_eq_iff → gauss_eqI` (depth 3).

In my opinion the detail worth copying is that extensionality is stated *once*
as `gauss_eq_iff` and then reused everywhere, so each axiom of the algebraic
structure is proved by a one-line rewrite to its components rather than by any
arithmetic about the structure itself.

## Why it is good

1. **Check** — the parent site (the `instance proof`, lines 323-341) cites the
   child `gauss_eq_iff`; it does so in all three axioms (lines 326, 337, 340).
2. **Check** — the parent site cites the child `gauss_eq_0` (line 331), where it
   turns `y ≠ 0` into `Y > 0`.
3. **Check** — `gauss_eq_iff` occurs 35 times in the copied file, so the one
   extensionality lemma is the reusable leaf for the whole theory, not a lemma
   written for this instance alone.
4. **Measurement** — the theorem-scale shape is `direct_lemmas = 2`,
   `depth = 3`, `glue_lines = 19`, `child_lines = [3, 3]`: the glue cites
   `gauss_eq_iff` and `gauss_eq_0` directly; the longest project-lemma chain is
   `instance → gauss_eq_0 → gauss_eq_iff → gauss_eqI`; the parent site is 19
   lines and each child site 3 lines (declaration included).
5. **Check** — no `sorry` occurs anywhere in the copied file (nor any `oops`),
   so nothing in the dependency cone is closed by a hole.

## When to use it, and when not

Use it when you must prove the axioms of an algebraic structure (an
`instance`/`subclass` goal) over a carrier type whose values are freely
generated by a finite set of selectors — a `codatatype`, a product, or a
`record` — and whose operations are defined componentwise by `primcorec`/`fun`.
State the extensionality lemma once (`gauss_eq_iff`) as the bridge from value
equality to component equality, then each axiom becomes one equation per
component that `simp`/`algebra_simps` closes in the component type. It also
pays when the same extensionality lemma will be reused many times (here 35).

Avoid it when the carrier is not freely generated by its selectors — a quotient
or a type with an invariant (e.g. normalised fractions), where component
equality does not imply value equality and `gauss_eq_iff`'s backward direction
would be false. Avoid it when an operation's defining equations do not reduce
both sides to a common per-component form, so the extensionality step leaves a
residual goal; and when a side condition like `Y > 0` cannot be recovered from
the assumptions through a separate named lemma (here `gauss_eq_0`), since the
cancellation step (`nonzero_mult_cdiv_cancel_right`) needs it.

## Consequences

The move creates one obligation per component of the carrier for each equality
goal: `gauss_eq_iff` rewrites `a = b` to `Re a = Re b ∧ Im a = Im b`, so each
`idom_modulo` axiom splits into two integer equations that `simp` must close.
The whole reduction rests on `gauss.expand` making `Re`/`Im` jointly determine
the value; on a type without that property the backward direction of
`gauss_eq_iff` fails. The `x * y div y = x` axiom additionally obliges a positive
norm `Y = (Re y)² + (Im y)²` derived from `y ≠ 0` via `gauss_eq_0`, and the
three algebra identities of the fact `*`; and it relies on the `div`/`mod`
definitions routing the component division through `cdiv`, or the cancellation
lemma `nonzero_mult_cdiv_cancel_right` no longer applies. Known failure modes:
an equality whose two component sides do not reduce to a common form stalls the
`simp` call; and omitting the `Y > 0` side condition makes the
`nonzero_mult_cdiv_cancel_right` step inapplicable.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: gauss_eq_iff@src/HOL/Examples/Gauss_Numbers.thy:326, gauss_eq_0@src/HOL/Examples/Gauss_Numbers.thy:331; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, gauss_eq_iff) -> cites: gauss_eq_iff occurs at src/HOL/Examples/Gauss_Numbers.thy:326 | check_claims.py |
| 2 | verified | cites(parent, gauss_eq_0) -> cites: gauss_eq_0 occurs at src/HOL/Examples/Gauss_Numbers.thy:331 | check_claims.py |
| 3 | verified | count(gauss_eq_iff, 35, src/HOL/Examples/Gauss_Numbers.thy) -> count: gauss_eq_iff occurs 35 times in 1 file(s) matching src/HOL/Examples/Gauss_Numbers.thy | check_claims.py |
| 5 | verified | no_sorry(src/HOL/Examples/Gauss_Numbers.thy, 1-405) -> no_sorry: none of sorry in src/HOL/Examples/Gauss_Numbers.thy:1-405 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/isabelle-prover/mirror-isabelle at commit `34ca456d44ca14641450b5d52f51b38688d4d1b5`, under `BSD-3-Clause`; see the [source note](../../sources/isabelle-dist/SOURCE.md) for the licence text and attribution.
