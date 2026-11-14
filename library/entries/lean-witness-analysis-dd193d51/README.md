# Witness LIM a for the least upper bound of a nonempty bounded set of reals (Theorem 5.5.9)

| | |
|---|---|
| Kind | instance |
| Move | witness |
| Language | lean |
| Status | draft |
| Source | [analysis](../../sources/analysis/SOURCE.md) at `a19a5bfadc61` |
| Licence | `Apache-2.0` |

## Intent

Theorem 5.5.9 — every nonempty set of reals bounded above has a least upper
bound — is proved by building a rational approximation `a n = m n / (n+1)` from
a rounding lemma, turning an adjacent-term bound into Cauchyness, and then
exhibiting `S := LIM a` as the witness whose upper-bound and minimality halves
are supplied by two pointwise-inequality limit lemmas.

## The decomposition

### parent `Real.LUB_exist`: [`Analysis/Section_5_5.lean` lines 166-189](https://github.com/teorth/analysis/blob/a19a5bfadc616467562995b75f46035232841943/Analysis/Section_5_5.lean#L166-L189) ([local copy](code/Analysis/Section_5_5.lean))

```lean
theorem Real.LUB_exist {E: Set Real} (hE: Set.Nonempty E) (hbound: BddAbove E): ∃ S, IsLUB E S := by
  -- This proof is written to follow the structure of the original text.
  set x₀ := hE.some
  have hx₀ : x₀ ∈ E := hE.some_mem
  set m : ℕ → ℤ := fun n ↦ (LUB_claim1 n hE hbound).exists.choose
  set a : ℕ → ℚ := fun n ↦ (m n:ℚ) / (n+1)
  set b : ℕ → ℚ := fun n ↦ 1 / (n+1)
  have claim1 (n: ℕ) := LUB_claim1 n hE hbound
  have hb : (b:Sequence).IsCauchy := .harmonic'
  have hm1 (n:ℕ) := (claim1 n).exists.choose_spec.1
  have hm2 (n:ℕ) : ¬((a - b) n: Real) ∈ upperBounds E := (claim1 n).exists.choose_spec.2
  have claim2 (N:ℕ) := LUB_claim2 N (by aesop) hm1 hm2
  have claim3 : (a:Sequence).IsCauchy := (LIM_of_Cauchy claim2).1
  set S := LIM a; use S
  have claim4 : S = LIM (a - b) := by
    have : LIM b = 0 := LIM.harmonic
    simp [←LIM_sub claim3 hb, S, this]
  rw [isLUB_def, upperBound_def]
  split_ands
  . intro x hx; apply LIM_of_ge claim3; intro n
    exact (upperBound_def E (a n)).mp (hm1 n) x hx
  intro y hy
  have claim5 (n:ℕ) : y ≥ (a-b) n := by contrapose! hm2; use n; apply upperBound_upper _ hy; order
  rw [claim4]; apply LIM_of_le _ claim5; solve_by_elim [Sequence.IsCauchy.sub]
```

### child `Real.LUB_claim1`: [`Analysis/Section_5_5.lean` lines 117-145](https://github.com/teorth/analysis/blob/a19a5bfadc616467562995b75f46035232841943/Analysis/Section_5_5.lean#L117-L145) ([local copy](code/Analysis/Section_5_5.lean))

```lean
lemma Real.LUB_claim1 (n : ℕ) {E: Set Real} (hE: Set.Nonempty E) (hbound: BddAbove E)
:  ∃! m:ℤ,
      (((m:ℚ) / (n+1):ℚ):Real) ∈ upperBounds E
      ∧ ¬ (((m:ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∈ upperBounds E := by
  set x₀ := Set.Nonempty.some hE
  observe hx₀ : x₀ ∈ E
  set ε := ((1/(n+1):ℚ):Real)
  have hpos : ε.IsPos := by simp [isPos_iff, ε]; positivity
  apply existsUnique_of_exists_of_unique
  . rw [bddAbove_def] at hbound; obtain ⟨ M, hbound ⟩ := hbound
    choose K _ hK using le_mul hpos M
    choose L' _ hL using le_mul hpos (-x₀)
    set L := -(L':ℤ)
    have claim1_1 : L * ε < x₀ := by simp [L]; linarith
    have claim1_2 : L * ε ∉ upperBounds E := by grind [upperBound_def]
    have claim1_3 : (K:Real) > (L:Real) := by
      contrapose! claim1_2
      replace claim1_2 := mul_le_mul_left claim1_2 hpos
      simp_rw [mul_comm] at claim1_2
      replace claim1_2 : M ≤ L * ε := by order
      grind [upperBound_upper]
    have claim1_4 : ∃ m:ℤ, L < m ∧ m ≤ K ∧ m*ε ∈ upperBounds E ∧ (m-1)*ε ∉ upperBounds E := by
      convert Real.upperBound_between (n := n) _ _ claim1_2
      . qify; rwa [←gt_iff_lt, gt_of_coe]
      simp [ε] at *; apply upperBound_upper _ hbound; order
    choose m _ _ hm hm' using claim1_4; use m
    have : (m/(n+1):ℚ) = m*ε := by simp [ε]; field_simp
    exact ⟨ by convert hm, by convert hm'; simp [this, sub_mul, ε] ⟩
  grind [upperBound_discrete_unique]
```

### child `Real.LUB_claim2`: [`Analysis/Section_5_5.lean` lines 147-163](https://github.com/teorth/analysis/blob/a19a5bfadc616467562995b75f46035232841943/Analysis/Section_5_5.lean#L147-L163) ([local copy](code/Analysis/Section_5_5.lean))

```lean
lemma Real.LUB_claim2 {E : Set Real} (N:ℕ) {a b: ℕ → ℚ}
  (hb : ∀ n, b n = 1 / (↑n + 1))
  (hm1 : ∀ (n : ℕ), ↑(a n) ∈ upperBounds E)
  (hm2 : ∀ (n : ℕ), ↑((a - b) n) ∉ upperBounds E)
: ∀ n ≥ N, ∀ n' ≥ N, |a n - a n'| ≤ 1 / (N+1) := by
    intro n hn n' hn'
    rw [abs_le]
    split_ands
    . specialize hm1 n; specialize hm2 n'
      have bound1 : ((a-b) n') < a n := by rw [lt_of_coe]; contrapose! hm2; grind [upperBound_upper]
      have bound3 : 1/((n':ℚ)+1) ≤ 1/(N+1) := by gcongr
      rw [←neg_le_neg_iff] at bound3; rw [Pi.sub_apply] at bound1; grind
    specialize hm1 n'; specialize hm2 n
    have bound1 : ((a-b) n) < a n' := by rw [lt_of_coe]; contrapose! hm2; grind [upperBound_upper]
    have bound2 : ((a-b) n) = a n - 1 / (n+1) := by simp [hb n]
    have bound3 : 1/((n+1):ℚ) ≤ 1/(N+1) := by gcongr
    linarith
```

### child `Real.LIM_of_Cauchy`: [`Analysis/Section_5_5.lean` lines 110-111](https://github.com/teorth/analysis/blob/a19a5bfadc616467562995b75f46035232841943/Analysis/Section_5_5.lean#L110-L111) ([local copy](code/Analysis/Section_5_5.lean))

```lean
theorem Real.LIM_of_Cauchy {q:ℕ → ℚ} (hq: ∀ M, ∀ n ≥ M, ∀ n' ≥ M, |q n - q n'| ≤ 1 / (M+1)) :
    (q:Sequence).IsCauchy ∧ ∀ M, |q M - LIM q| ≤ 1 / (M+1) := by sorry
```

### child `Real.LIM.harmonic`: [`Analysis/Section_5_3.lean` lines 467-467](https://github.com/teorth/analysis/blob/a19a5bfadc616467562995b75f46035232841943/Analysis/Section_5_3.lean#L467-L467) ([local copy](code/Analysis/Section_5_3.lean))

```lean
theorem Real.LIM.harmonic : LIM (fun n ↦ 1/((n:ℚ)+1)) = 0 := by sorry
```

### child `Real.LIM_of_ge`: [`Analysis/Section_5_4.lean` lines 349-350](https://github.com/teorth/analysis/blob/a19a5bfadc616467562995b75f46035232841943/Analysis/Section_5_4.lean#L349-L350) ([local copy](code/Analysis/Section_5_4.lean))

```lean
theorem Real.LIM_of_ge {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≥ x) :
    LIM a ≥ x := by sorry
```

### child `Real.LIM_of_le`: [`Analysis/Section_5_4.lean` lines 345-346](https://github.com/teorth/analysis/blob/a19a5bfadc616467562995b75f46035232841943/Analysis/Section_5_4.lean#L345-L346) ([local copy](code/Analysis/Section_5_4.lean))

```lean
theorem Real.LIM_of_le {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≤ x) :
    LIM a ≤ x := by sorry
```

How the parts fit. The glue builds the witness in four moves and then splits
the goal on the two halves of `IsLUB`:

```
Real.LUB_exist
├─ LUB_claim1 ──────── builds m (integer rounding at mesh 1/(n+1)) and a := m/(n+1)
├─ LUB_claim2 ──────── adjacent-term bound |a n − a n'| ≤ 1/(N+1)
├─ LIM_of_Cauchy ← LUB_claim2 ── claim3 : a is Cauchy, so LIM a exists
├─ LIM.harmonic (+ harmonic') ── LIM b = 0, so claim4 : S = LIM (a − b)
├─ LIM_of_ge ← claim3 ── S is an upper bound of E
└─ LIM_of_le ← claim3, claim4 ── S is minimal among upper bounds
```

The glue first names the witness: `set m := fun n ↦ (LUB_claim1 n hE
hbound).exists.choose`, then `set a := fun n ↦ (m n:ℚ)/(n+1)` (lines 170-171).
It obtains Cauchyness of `a` by feeding the adjacent-term bound from
`LUB_claim2` into `LIM_of_Cauchy` (line 178), which lets it `set S := LIM a; use
S` (line 179). To prove `S` is a least upper bound it rewrites with `isLUB_def`
and `upperBound_def` and splits into two conjuncts: the upper-bound half closes
by `LIM_of_ge` on the fact `hm1 : a n ∈ upperBounds E` (line 185), and the
minimality half closes by `LIM_of_le` on `claim5 : y ≥ (a−b) n` (line 189),
using `claim4` that `S = LIM (a − b)`.

Each child is a self-contained statement that closes on its own or from named
siblings:

- `LUB_claim1` and `LUB_claim2` close by their own proofs (no `sorry`); the
  former via `existsUnique_of_exists_of_unique` and the project lemmas
  `upperBound_between`, `upperBound_upper`, `upperBound_discrete_unique`, the
  latter via `abs_le`, `upperBound_upper` and `gcongr`/`linarith`.
- `LIM_of_Cauchy`, `LIM.harmonic`, `LIM_of_ge` and `LIM_of_le` are each a
  one-statement leaf whose proof is left as an exercise (`by sorry`) in this
  companion; the glue routes each of its obligations to exactly one such leaf.

Besides the six children the glue also cites a few supporting project lemmas,
listed here with permalinks rather than as children because they do definition
unfolding and Cauchy algebra, not the argument:
[`Sequence.IsCauchy.harmonic'`](https://github.com/teorth/analysis/blob/a19a5bfadc616467562995b75f46035232841943/Analysis/Section_5_3.lean#L461-L464)
(b is Cauchy, line 174),
[`Real.LIM_sub`](https://github.com/teorth/analysis/blob/a19a5bfadc616467562995b75f46035232841943/Analysis/Section_5_3.lean#L269-L270)
(S = LIM(a−b), line 182),
[`Sequence.IsCauchy.sub`](https://github.com/teorth/analysis/blob/a19a5bfadc616467562995b75f46035232841943/Analysis/Section_5_3.lean#L265-L266)
(line 189),
[`Real.upperBound_def`](https://github.com/teorth/analysis/blob/a19a5bfadc616467562995b75f46035232841943/Analysis/Section_5_5.lean#L29-L30)
(line 186) and
[`Real.upperBound_upper`](https://github.com/teorth/analysis/blob/a19a5bfadc616467562995b75f46035232841943/Analysis/Section_5_5.lean#L53-L54)
(line 188).

## Why it is good

1. `Real.LUB_exist` is declared in `Analysis/Section_5_5.lean`, lines 166-189
   (`check`; permalink above).
2. No `sorry`/`admit`/`axiom` closes the main theorem's proof — the 24-line glue
   is complete even though four of its leaves are stubbed
   (`check`; permalink above).
3. The glue cites the rounding lemma `Real.LUB_claim1` — the witness `a` is built
   from it (`check`; permalink above).
4. The witness move assembles the 24-line glue from six named lemmas totalling 53
   declaration lines (29 + 17 + 2 + 1 + 2 + 2), with the longest chain of project
   lemmas below the main theorem 2 deep (`LUB_exist → LUB_claim1 →
   upperBound_between`) (`measurement`; counts from the copied files, chain cited
   at lines 170/173 and 139).
5. The authors reindexed the harmonic-sequence lemma to serve this theorem
   specifically: "Same as `Sequence.IsCauchy.harmonic` but reindexing the
   sequence as a₀ = 1, a₁ = 1/2, ... This form is more convenient for the
   upcoming proof of Theorem 5.5.9" (`author-statement`; doc comment,
   Section_5_3.lean lines 457-459).

In my opinion the detail worth copying is the order of the glue: the witness
cannot be named until its Cauchyness is proved, so `claim3` necessarily precedes
`set S := LIM a`, and the two halves of `IsLUB` are each delegated to a single
pointwise-inequality limit lemma. That is exactly the skeleton-with-holes shape a
theorem-scale decomposition should produce: a complete glue over six named lemma
statements, some of which are left for a bounded prover.

## When to use it, and when not

Use it for an existence goal `∃ S, P S` whose witness is a limit or supremum
built from a sequence of approximations, when the witness term is nameable and
its two defining properties are already stated as named lemmas. The three
ingredients — a rounding/existence lemma, a Cauchy criterion, and pointwise-to-
limit inequality lemmas — are each self-contained and reusable.

Avoid it when the witness cannot be named before some side fact is proved (here
`claim3`, the Cauchyness of `a`, must precede `set S := LIM a`); when the
approximating sequence is not Cauchy, so the `LIM` term is not available; or when
the property to prove does not split cleanly into two halves each expressible as
a single pointwise-inequality limit lemma.

## Consequences

The `use S` commits to one witness and `rw [isLUB_def, upperBound_def]` +
`split_ands` creates the two conjuncts of `IsLUB` as obligations (upper bound,
minimality). Before the witness can be named, the approximating sequence `a` must
be shown Cauchy (`claim3`) and `b` must be Cauchy and tend to 0 (`harmonic'`,
`LIM.harmonic`). Four of the six leaves are stubbed with `sorry` in this source,
so the glue compiles but the theorem is only as strong as those exercise holes —
a failure mode to flag if the entry is reused as a proof, though harmless as a
decomposition. If `a` were not Cauchy the `LIM a` term would not exist to `use`;
if a half of `IsLUB` needed a different transfer than `LIM_of_ge`/`LIM_of_le`,
the pointwise-inequality step would not fit.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: Real.LUB_claim1@Analysis/Section_5_5.lean:170, Real.LUB_claim2@Analysis/Section_5_5.lean:177, Real.LIM_of_Cauchy@Analysis/Section_5_5.lean:178, Real.LIM.harmonic@Analysis/Section_5_5.lean:181, Real.LIM_of_ge@Analysis/Section_5_5.lean:185, Real.LIM_of_le@Analysis/Section_5_5.lean:189; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | fail | inside parent/child/skeleton sites: Analysis/Section_5_5.lean:111 (sorry), Analysis/Section_5_3.lean:467 (sorry), Analysis/Section_5_4.lean:346 (sorry), Analysis/Section_5_4.lean:350 (sorry); elsewhere in the copied files (not failed): Analysis/Section_5_5.lean:42 (sorry), Analysis/Section_5_5.lean:48 (sorry), Analysis/Section_5_5.lean:51 (sorry), Analysis/Section_5_5.lean:54 (sorry), Analysis/Section_5_5.lean:64 (sorry), Analysis/Section_5_5.lean:67 (sorry), Analysis/Section_5_5.lean:84 (sorry), Analysis/Section_5_5.lean:92 (sorry), Analysis/Section_5_5.lean:96 (sorry), Analysis/Section_5_5.lean:99 (sorry), Analysis/Section_5_5.lean:102 (sorry), Analysis/Section_5_5.lean:104 (sorry), ... (125 in all) | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(Real.LUB_exist, Analysis/Section_5_5.lean, 166-189) -> declared: Real.LUB_exist is declared at Analysis/Section_5_5.lean:166 | check_claims.py |
| 2 | verified | no_sorry(Analysis/Section_5_5.lean, 166-189) -> no_sorry: none of sorry, admit, axiom in Analysis/Section_5_5.lean:166-189 | check_claims.py |
| 3 | verified | cites(parent, Real.LUB_claim1) -> cites: Real.LUB_claim1 occurs at Analysis/Section_5_5.lean:170 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/teorth/analysis at commit `a19a5bfadc616467562995b75f46035232841943`, under `Apache-2.0`; see the [source note](../../sources/analysis/SOURCE.md) for the licence text and attribution.
