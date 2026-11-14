# Suffices on the convenient I n-scaled integral for the Catalan integral formula

| | |
|---|---|
| Kind | instance |
| Move | suffices-or-strengthen |
| Language | isabelle |
| Status | draft |
| Source | [afp](../../sources/afp/SOURCE.md) at `07cd9ca548d1` |
| Licence | `BSD-3-Clause` |

## Intent

Prove the Catalan integral formula — the density `x powr (real n - 1/2) * sqrt (4 - x) / (2*pi)` has integral `real (catalan n)` over `{0..4}` — by not fighting the `catalan n` constant directly. The glue proves the more convenient statement in terms of the auxiliary integral `I n` (the same density without the `1/(2*pi)` normalization, integrated to `I n * inverse (2*pi)`), then rewrites `I n / (2*pi)` to `real (catalan n)` through the bridge lemma `catalan_eq_I`.

## The decomposition

### parent `catalan_integral_form`: [`thys/Catalan_Numbers/Catalan_Numbers.thy` lines 345-353](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/Catalan_Numbers/Catalan_Numbers.thy#L345-L353) ([local copy](code/thys/Catalan_Numbers/Catalan_Numbers.thy))

```isabelle
theorem catalan_integral_form:
  "((\<lambda>x. x powr (real n - 1 / 2) * sqrt (4 - x) / (2*pi)) 
       has_integral real (catalan n)) {0..4}"
proof -
  have "((\<lambda>x. x powr (real n - 1 / 2) * sqrt (4 - x) * inverse (2*pi)) has_integral 
           I n * inverse (2 * pi)) {0..4}" unfolding I_def
    by (intro has_integral_mult_left integrable_integral integrable_I)
  thus ?thesis by (simp add: catalan_eq_I field_simps)
qed
```

### child `integrable_I`: [`thys/Catalan_Numbers/Catalan_Numbers.thy` lines 269-278](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/Catalan_Numbers/Catalan_Numbers.thy#L269-L278) ([local copy](code/thys/Catalan_Numbers/Catalan_Numbers.thy))

```isabelle
private lemma integrable_I: 
  "(\<lambda>x. x powr (of_nat n - 1/2) * sqrt (4 - x)) integrable_on {0..4}"
proof (cases "n = 0")
  case True
  with has_integral_I0 show ?thesis by (simp add: has_integral_integrable)
next
  case False
  thus ?thesis by (intro integrable_continuous_real continuous_on_mult continuous_on_powr')
                  (auto intro!: continuous_intros)
qed
```

### child `catalan_eq_I`: [`thys/Catalan_Numbers/Catalan_Numbers.thy` lines 336-343](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/Catalan_Numbers/Catalan_Numbers.thy#L336-L343) ([local copy](code/thys/Catalan_Numbers/Catalan_Numbers.thy))

```isabelle
private lemma catalan_eq_I: "real (catalan n) = I n / (2 * pi)"
proof (induction n)
  case 0
  thus ?case using has_integral_I0 by (simp add: I_def integral_unique)
next
  case (Suc n)
  show ?case by (simp add: of_nat_catalan_Suc' Suc.IH I_Suc)
qed
```

How the parts fit. The parent `catalan_integral_form` is nine lines of glue that
names exactly two same-file project lemmas:

- **`integrable_I`** (lines 269-278) — the integrand `x powr (of_nat n - 1/2) * sqrt (4 - x)` is `integrable_on {0..4}`. This is the premise that the scaling rule `has_integral_mult_left` needs before it can move the constant `inverse (2*pi)` out of the integral.
- **`catalan_eq_I`** (lines 336-343) — `real (catalan n) = I n / (2 * pi)`. This is the bridge that turns the convenient `I n`-normalised result into the value of the Catalan number.

The glue runs in two steps. First the `have` (lines 349-351) states the convenient
scaled statement — `x powr (real n - 1/2) * sqrt (4 - x) * inverse (2*pi)` has
integral `I n * inverse (2*pi)` — and closes it by `unfolding I_def` then
`intro has_integral_mult_left integrable_integral integrable_I`, where
`integrable_I` supplies the integrability premise. Second, `thus ?thesis` (line
352) closes the original goal by `simp add: catalan_eq_I field_simps`, rewriting
`I n * inverse (2*pi)` through `catalan_eq_I` into `real (catalan n)`.

Lemma graph (each arrow = "is cited in the proof of"):

```
catalan_integral_form ──► integrable_I   (line 351)
      │                 └─► has_integral_I0  (case n = 0, line 273)
      └──► catalan_eq_I (line 352)
            ├─► has_integral_I0        (base case, line 339)
            └─► I_Suc                  (step case, line 342)
                  └─► integrable_I     (line 321)
```

Each child is a good leaf because it is a self-contained statement whose proof
closes on its own or from named siblings:

- `integrable_I` closes by `cases "n = 0"`: the `n = 0` case reuses the base
  integral `has_integral_I0` through `has_integral_integrable`, and the `n ≠ 0`
  case is continuity (`integrable_continuous_real` over `continuous_on_mult`
  and `continuous_on_powr'`). Its only job is the one integrability premise the
  convenient statement needs, so nothing else depends on it beyond `I_Suc`.
- `catalan_eq_I` closes by `induction n`: the base case uses `has_integral_I0`
  with `I_def integral_unique`, and the step case uses the recurrence
  `of_nat_catalan_Suc'` together with the induction hypothesis and `I_Suc`. It
  isolates the one place where the `I n` normalisation and the `catalan n` value
  are tied together, which is why the parent's final rewrite is a single `simp`.

## Why it is good

1. The parent proof cites both children: `integrable_I` at line 351 and
   `catalan_eq_I` at line 352, and no other project lemma (check, machine-checked).
2. The theorem `catalan_integral_form` is declared at lines 345-353 of the file
   (check, machine-checked).
3. The decomposition is minimal and shallow: 9 lines of glue, 2 direct lemmas,
   child proofs of 10 and 8 lines, and the longest checked same-file chain below
   the theorem is depth 4 (measurement).
4. The authors say the integral formula is a consequence of the recursive
   formula they just proved — "The recursive formula we have just proven allows
   us to derive an integral formula for the Catalan numbers" (lines 251-253)
   (author-statement).

In my opinion the detail worth copying is that the glue never names the target
constant in its proof body: it works entirely in the `I n` normalisation and
lets `catalan_eq_I` carry the single bridge back to `catalan n`, so the two
concerns (the integral exists and has a normalised value; that value is the
Catalan number) stay separate.

## When to use it, and when not

Use it when the goal's right-hand side involves a constant you also have an
auxiliary definition or equivalent form for (here the unnormalised integral
`I n`), so you can prove the statement in terms of that more convenient quantity
first and bridge back with one named identity. It fits in particular when the
target carries a normalising constant (`1/(2*pi)`) and the unnormalised version
is the natural thing to prove, because the scaling is a one-line rule
(`has_integral_mult_left`) once integrability is known.

Avoid it when the bridge identity is itself the hard part and is not already
proved — then the `suffices` only moves the difficulty, it does not reduce it.
Avoid it when the convenient statement is not genuinely easier than the
original, or when the goal can be closed by a single direct rule, where the
detour through the auxiliary quantity adds a lemma for no benefit.

## Consequences

The move creates two obligations from one: (a) the convenient restatement must
be proved, which here needs the integrability premise `integrable_I` and the
scaling rule `has_integral_mult_left`; and (b) the bridge identity
`catalan_eq_I` must hold, and it is the only place a reader sees why the result
is about the Catalan number at all. Failure modes: if the bridge constant were
wrong (a sign or normalisation error in `catalan_eq_I`), the final
`simp add: catalan_eq_I field_simps` would fail or rewrite to the wrong value;
and if `integrable_I` were stated for the wrong exponent, the
`intro ... integrable_I` step in the convenient statement would not apply.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: integrable_I@thys/Catalan_Numbers/Catalan_Numbers.thy:351, catalan_eq_I@thys/Catalan_Numbers/Catalan_Numbers.thy:352; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, integrable_I) -> cites: integrable_I occurs at thys/Catalan_Numbers/Catalan_Numbers.thy:351 | check_claims.py |
| 2 | verified | cites(parent, catalan_eq_I) -> cites: catalan_eq_I occurs at thys/Catalan_Numbers/Catalan_Numbers.thy:352 | check_claims.py |
| 3 | verified | declared(catalan_integral_form, thys/Catalan_Numbers/Catalan_Numbers.thy, 345-353) -> declared: catalan_integral_form is declared at thys/Catalan_Numbers/Catalan_Numbers.thy:345 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/isabelle-prover/mirror-afp-devel at commit `07cd9ca548d180f234c63f06bf5d1cb85c7fc5df`, under `BSD-3-Clause`; see the [source note](../../sources/afp/SOURCE.md) for the licence text and attribution.
