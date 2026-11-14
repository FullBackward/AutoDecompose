# Interface lemmas bridge logDeriv and MeromorphicOn.divisor for the rectangle argument principle

| | |
|---|---|
| Kind | instance |
| Move | interface-lemma |
| Language | lean |
| Status | accepted |
| Source | [pnt-and](../../sources/pnt-and/SOURCE.md) at `2c476fa6441c` |
| Licence | `Apache-2.0` |

## Intent

Reduce the rectangle argument principle — the contour integral of `logDeriv`
over a rectangle equals a finite sum of divisor orders — to a finite sum a
downstream theorem can already consume, by routing the proof through three
interface lemmas that relate `logDeriv` to `MeromorphicOn.divisor`. The glue
never unfolds either definition: it discharges the hypotheses of the rectangle
residue theorem with the bridge lemmas, then rewrites each residue as a divisor
order.

## The decomposition

### parent `rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt`: [`PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean` lines 278-341](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean#L278-L341) ([local copy](code/PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean))

```lean
theorem rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt
    {f : ℂ → ℂ} {z w : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (hf : MeromorphicOn f (Rectangle z w))
    (hlog : MeromorphicOn (logDeriv f) (Rectangle z w))
    (hfinite_order : ∀ p ∈ Rectangle z w, meromorphicOrderAt f p ≠ ⊤)
    (hno_boundary :
      Disjoint (RectangleBorder z w) (MeromorphicOn.divisor f (Rectangle z w)).support) :
    RectangleIntegral' (logDeriv f) z w =
      ∑ p ∈
        ((divisor_support_rectangle_finite f z w).toFinset),
          ((MeromorphicOn.divisor f (Rectangle z w)) p : ℂ) := by
  classical
  let R : Set ℂ := Rectangle z w
  let D := MeromorphicOn.divisor f R
  have hsupport : D.support.Finite := divisor_support_rectangle_finite f z w
  have hlog_simple : HasSimplePolesOn (logDeriv f) R :=
    logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top hf hlog hfinite_order
  have hlog_poles_eq :
      R ∩ {s | meromorphicOrderAt (logDeriv f) s < 0} = D.support := by
    simpa [R, D] using
      logDeriv_poles_eq_divisor_support (f := f) (R := R) hf hlog hfinite_order
  have hlog_no_boundary :
      Disjoint (RectangleBorder z w) {s | meromorphicOrderAt (logDeriv f) s < 0} := by
    rw [Set.disjoint_left]
    intro s hs_border hs_log_pole
    have hsR : s ∈ R := by
      exact rectangleBorder_subset_rectangle z w hs_border
    have hsD : s ∈ D.support := by
      rw [← hlog_poles_eq]
      exact ⟨hsR, hs_log_pole⟩
    exact Set.disjoint_left.mp (by simpa [R, D] using hno_boundary) hs_border hsD
  have hlog_poles_finite :
      (Rectangle z w ∩ {s | meromorphicOrderAt (logDeriv f) s < 0}).Finite := by
    simpa [R, D, hlog_poles_eq] using hsupport
  have hrect :=
    RectangleIntegral'_eq_sumResiduesIn zRe_le_wRe zIm_le_wIm hlog hlog_no_boundary
      hlog_poles_finite hlog_simple
  rw [hrect, hlog_poles_eq, sumResiduesIn_eq_finset_of_finite hsupport]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hpD : p ∈ D.support := by
    simpa [D] using (hsupport.mem_toFinset.mp hp)
  have hpR : p ∈ R := D.supportWithinDomain hpD
  have hpD_ne : D p ≠ 0 := by
    simpa [Function.mem_support] using hpD
  have horder_ne_zero_or_top :
      meromorphicOrderAt f p ≠ 0 ∧ meromorphicOrderAt f p ≠ ⊤ := by
    change (MeromorphicOn.divisor f R) p ≠ 0 at hpD_ne
    rw [MeromorphicOn.divisor_apply hf hpR] at hpD_ne
    constructor
    · intro hzero
      exact hpD_ne (by simp [hzero])
    · intro htop
      exact hpD_ne (by simp [htop])
  obtain ⟨n, hn⟩ :=
    WithTop.ne_top_iff_exists.mp horder_ne_zero_or_top.2
  have hres :
      residue (logDeriv f) p = (n : ℂ) :=
    logDeriv_residue_eq_meromorphicOrderAt (hf p hpR) hn.symm
  rw [hres]
  change (n : ℂ) = ((MeromorphicOn.divisor f R) p : ℂ)
  rw [MeromorphicOn.divisor_apply hf hpR, ← hn]
  simp
```

### child `logDeriv_residue_eq_meromorphicOrderAt`: [`PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean` lines 119-126](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean#L119-L126) ([local copy](code/PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean))

```lean
theorem logDeriv_residue_eq_meromorphicOrderAt
    {f : ℂ → ℂ} {p : ℂ} {n : ℤ}
    (hf : MeromorphicAt f p)
    (hord : meromorphicOrderAt f p = (n : WithTop ℤ)) :
    residue (logDeriv f) p = (n : ℂ) :=
  residue_eq_of_tendsto
    (tendsto_mul_self_of_sub_principal_isBigO_one
      (logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt hf hord))
```

### child `logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top`: [`PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean` lines 196-212](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean#L196-L212) ([local copy](code/PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean))

```lean
theorem logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top
    {f : ℂ → ℂ} {R : Set ℂ}
    (hf : MeromorphicOn f R) (hlog : MeromorphicOn (logDeriv f) R)
    (hfinite_order : ∀ p ∈ R, meromorphicOrderAt f p ≠ ⊤) :
    HasSimplePolesOn (logDeriv f) R := by
  intro p hpR
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (hfinite_order p hpR)
  by_cases hn0 : n = 0
  · have hord0 : meromorphicOrderAt f p = (0 : WithTop ℤ) := by
      simpa [hn0] using hn.symm
    have hnonneg :=
      logDeriv_meromorphicOrderAt_nonneg_of_order_zero (hf p hpR) (hlog p hpR) hord0
    exact le_trans (WithTop.coe_le_coe.2 (by norm_num : (-1 : ℤ) ≤ 0)) hnonneg
  · have hneg_one :=
      logDeriv_meromorphicOrderAt_eq_neg_one_of_order_ne_zero (hf p hpR) (hlog p hpR)
        hn.symm hn0
    rw [hneg_one]
```

### child `logDeriv_poles_eq_divisor_support`: [`PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean` lines 214-254](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean#L214-L254) ([local copy](code/PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean))

```lean
theorem logDeriv_poles_eq_divisor_support
    {f : ℂ → ℂ} {R : Set ℂ}
    (hf : MeromorphicOn f R) (hlog : MeromorphicOn (logDeriv f) R)
    (hfinite_order : ∀ p ∈ R, meromorphicOrderAt f p ≠ ⊤) :
    R ∩ {p | meromorphicOrderAt (logDeriv f) p < 0} =
      (MeromorphicOn.divisor f R).support := by
  classical
  let D := MeromorphicOn.divisor f R
  ext p
  constructor
  · intro hp
    rcases hp with ⟨hpR, hpneg⟩
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (hfinite_order p hpR)
    by_cases hn0 : n = 0
    · have hord0 : meromorphicOrderAt f p = (0 : WithTop ℤ) := by
        simpa [hn0] using hn.symm
      have hnonneg :=
        logDeriv_meromorphicOrderAt_nonneg_of_order_zero (hf p hpR) (hlog p hpR) hord0
      exact False.elim (not_lt_of_ge hnonneg hpneg)
    · have hpD_ne : D p ≠ 0 := by
        change (MeromorphicOn.divisor f R) p ≠ 0
        rw [MeromorphicOn.divisor_apply hf hpR, ← hn]
        simp [hn0]
      simp [D, Function.mem_support, hpD_ne]
  · intro hpD
    have hpR : p ∈ R := (MeromorphicOn.divisor f R).supportWithinDomain hpD
    have hpD_ne : D p ≠ 0 := by
      simpa [D, Function.mem_support] using hpD
    change (MeromorphicOn.divisor f R) p ≠ 0 at hpD_ne
    rw [MeromorphicOn.divisor_apply hf hpR] at hpD_ne
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (hfinite_order p hpR)
    have hn0 : n ≠ 0 := by
      intro hn0
      exact hpD_ne (by rw [← hn]; simp [hn0])
    have hneg_one :=
      logDeriv_meromorphicOrderAt_eq_neg_one_of_order_ne_zero (hf p hpR) (hlog p hpR)
        hn.symm hn0
    refine ⟨hpR, ?_⟩
    change meromorphicOrderAt (logDeriv f) p < 0
    rw [hneg_one]
    exact WithTop.coe_lt_coe.2 (by norm_num : (-1 : ℤ) < 0)
```

### child `divisor_support_rectangle_finite`: [`PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean` lines 266-276](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean#L266-L276) ([local copy](code/PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean))

```lean
lemma divisor_support_rectangle_finite (f : ℂ → ℂ) (z w : ℂ) :
    (MeromorphicOn.divisor f (Rectangle z w)).support.Finite := by
  let R : Set ℂ := Rectangle z w
  let D := MeromorphicOn.divisor f R
  have hR_compact : IsCompact R := by
    exact IsCompact.reProdIm isCompact_uIcc isCompact_uIcc
  have hfinite_inter :
      (R ∩ D.support).Finite :=
    MeromorphicOn.divisor_support_inter_compact_finite (f := f) (U := R) (K := R)
      hR_compact subset_rfl
  simpa [Set.inter_eq_right.mpr D.supportWithinDomain] using hfinite_inter
```

How the parts fit. The glue is a proof of the rectangle residue theorem
`RectangleIntegral'_eq_sumResiduesIn` (in `ResidueCalcOnRectangles.lean`, line
1193), whose conclusion `sumResiduesIn (logDeriv f) …` it must turn into the
divisor sum. Each obligation of that theorem is discharged by one child, so the
lemma graph is exactly the list of `have`s:

```
rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt   (glue, 278-341)
├── divisor_support_rectangle_finite                    (266-276)  finiteness of the sum
├── logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top (196-212)  "simple poles" hypothesis
├── logDeriv_poles_eq_divisor_support                   (214-254)  poles ↔ divisor support
└── logDeriv_residue_eq_meromorphicOrderAt              (119-126)  each residue = its order
```

In order the glue:

1. fixes the finite support `hsupport` from `divisor_support_rectangle_finite`,
2. shows the poles are simple (`hlog_simple`) from
   `logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top`,
3. rewrites the pole set to the divisor support (`hlog_poles_eq`) from
   `logDeriv_poles_eq_divisor_support`, which also lets it re-derive the
   border-disjointness `hlog_no_boundary` and the finiteness `hlog_poles_finite`,
4. applies `RectangleIntegral'_eq_sumResiduesIn` and then, inside a
   `Finset.sum_congr`, rewrites each residue to `(n : ℂ)` with
   `logDeriv_residue_eq_meromorphicOrderAt` before closing by `MeromorphicOn.divisor_apply`.

Each child is a good leaf — a self-contained statement whose proof closes on
its own or from named siblings:

- `divisor_support_rectangle_finite` closes in six lines from
  `MeromorphicOn.divisor_support_inter_compact_finite` and compactness of the
  rectangle (`IsCompact.reProdIm isCompact_uIcc isCompact_uIcc`); it needs
  nothing from the other children.
- `logDeriv_residue_eq_meromorphicOrderAt` closes in one `exact` from
  `residue_eq_of_tendsto` plus two private asymptotics lemmas
  (`tendsto_mul_self_of_sub_principal_isBigO_one`, line 21, and
  `logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt`, line 60).
- `logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top` splits on whether
  the order `n` is zero and closes each case by a private sibling
  (`logDeriv_meromorphicOrderAt_nonneg_of_order_zero`, line 175, or
  `logDeriv_meromorphicOrderAt_eq_neg_one_of_order_ne_zero`, line 186).
- `logDeriv_poles_eq_divisor_support` is the same case split done both
  directions of an `ext p`, reusing those two private siblings.

The glue also leans on three auxiliary facts that are *consumed* rather than
built: the rectangle residue theorem itself
`RectangleIntegral'_eq_sumResiduesIn` (`ResidueCalcOnRectangles.lean` line
1193), `rectangleBorder_subset_rectangle` (`Rectangle.lean` line 140), and the
private rewrite `sumResiduesIn_eq_finset_of_finite` (line 256 of the same
file). They are listed here for completeness but are not children of this
decomposition: they belong to the residue-calculus layer the interface lemmas
already bridge.

The longest chain of project lemmas below the main theorem (depth 4, recorded
in `shape`) runs through the two private siblings and their shared helper:

```
logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top   (196)
  → logDeriv_meromorphicOrderAt_eq_neg_one_of_order_ne_zero (186)
    → meromorphicOrderAt_eq_neg_one_of_sub_principal_isBigO_one (140)
      → meromorphicOrderAt_nonneg_of_isBigO_one           (128)
```

## Why it is good

1. The parent proof (lines 278-341) closes with no `sorry`, `admit` or `axiom`
   token — the glue is a complete proof, not a sketch (check;
   `no_sorry(PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean, 278-341)`).
2. The glue is 64 lines long (check; `lines(parent, 64)`).
3. The decomposition is theorem-scale with shape `direct_lemmas = 4`,
   `depth = 4`, `glue_lines = 64`, `child_lines = [8, 17, 41, 11]`, counted
   from the five sites in the copied file (measurement).
4. The parent is reused immediately: the next theorem
   `rectangle_argumentChange_eq_two_pi_sum_meromorphicOrderAt` (lines 343-368)
   proves the argument-change form by citing the parent at line 365 (known-use).
5. The authors state the file's purpose in the module docstring: "This file
   isolates the local logarithmic-derivative residue calculation and the
   rectangle-facing finite divisor sum used by the Kadiri contour lanes"
   (lines 8-13) (author-statement).

In my opinion the detail worth copying is that the three bridge lemmas are
*not* extracted from the glue — they sit above it as an interface, each with a
self-contained statement, so the client proof reads as a list of hypothesis
discharges and one final rewrite, with no unfolding of `logDeriv`,
`meromorphicOrderAt` or `divisor`. This move is not one of survey F §10's
rules: those catalogue decomposition *procedures*, while this is a
statement-design move (where to draw an abstraction boundary).

## When to use it, and when not

Use `interface-lemma` when two abstraction layers meet in one theorem and the
client would otherwise unfold one layer's definitions into the other — here
`logDeriv`/`residue` (Mathlib's calculus layer) and
`MeromorphicOn.divisor`/`meromorphicOrderAt` (the divisor layer). Write one
bridge lemma per direction of the crossing (residue↔order, poles↔support,
order→simple-poles) plus any finiteness fact the sum needs, so the client
becomes a sequence of `have`s citing them.

Avoid it when the boundary is crossed only once (a single inline `rw`
suffices); when the bridge lemmas are not self-contained — their statements
need hypotheses the client cannot discharge without unfolding; or when the
finiteness of the support needs a substantial separate argument that dominates
the proof, in which case the finiteness lemma, not the bridge, is the real
content.

## Consequences

The move creates three named bridge lemmas plus a finiteness lemma, each
carrying hypotheses the client must discharge: `MeromorphicAt`/`MeromorphicOn`
at every point and the finite-order condition `meromorphicOrderAt f p ≠ ⊤`.
The client therefore spends most of its length assembling those hypotheses
into the rectangle residue theorem's inputs (`hlog_simple`,
`hlog_no_boundary`, `hlog_poles_finite`) before a final `Finset.sum_congr`
rewrites each residue as a divisor order. Failure modes: a bridge lemma stated
too strongly (e.g. assuming all orders finite when the client only has that on
a subset) becomes un-appliable and forces either a weaker lemma or unfolding;
the border-disjointness obligation (`hno_boundary`) must be re-derived in the
divisor language via `hlog_poles_eq`, which fails if the poles/support
correspondence is not already an equality.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml; on push/PR to main (default branch), leanprover/lean-action runs 'lake build :blueprint', which builds PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: logDeriv_residue_eq_meromorphicOrderAt@PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean:337, logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top@PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean:295, logDeriv_poles_eq_divisor_support@PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean:299, divisor_support_rectangle_finite@PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean:288; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 4 file(s) byte-identical at 2c476fa6441c607096d93c8fc7ac0a227a655dae | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | no_sorry(PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean, 278-341) -> no_sorry: none of sorry, admit, axiom in PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean:278-341 | check_claims.py |
| 2 | verified | lines(parent, 64) -> lines: site parent has 64 lines | check_claims.py |
| 3 | verified | Measured line ranges in the copied file: child1 119-126=8, child2 196-212=17, child3 214-254=41, child4 266-276=11; glue 278-341=64. direct_lemmas=4 (four children). Depth chain verified in code: parent(278-341) cites logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top; that (196-212) cites logDeriv_meromorphicOrderAt_eq_neg_one_of_order_ne_zero; that (186-194) at line 193 cites meromorphicOrderAt_eq_neg_one_of_sub_principal_isBigO_one; that (140-154) at line 152 cites meromorphicOrderAt_nonneg_of_isBigO_one (128-138): 5 lemmas, 4 edges. | verifier |
| 4 | verified | Read lines 343-368: theorem rectangle_argumentChange_eq_two_pi_sum_meromorphicOrderAt starts at 343 and cites rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt at line 365 (rw [rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt zRe_le_wRe zIm_le_wIm hf hlog hfinite_order hno_boundary]). | verifier |
| 5 | verified | Read lines 8-13: module docstring (/-! ... -/) at lines 8-13 contains the quoted sentence across lines 11-12: 'This file isolates the local logarithmic-derivative residue calculation and the rectangle-facing finite divisor sum used by the Kadiri contour lanes.' | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Provenance passes (4 files byte-identical). Parent rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt is exactly lines 278-341; its four children and their cited ranges match the code verbatim: logDeriv_residue_eq_meromorphicOrderAt (119-126, closes by residue_eq_of_tendsto ...), logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top (196-212, by_cases n=0 on the two private siblings), logDeriv_poles_eq_divisor_support (214-254, ext p; constructor with the same case split), divisor_support_rectangle_finite (266-276, closes by MeromorphicOn.divisor_support_inter_compact_finite). Closing methods in entry.json match the code exactly. The parent cites all four children at lines 288/293, 295, 299, 337 (glue-cites-children pass) and closes with simp at 341, no sorry/admit/axiom anywhere in the file. The other lemmas the parent uses (RectangleIntegral'_eq_sumResiduesIn, rectangleBorder_subset_rectangle, sumResiduesIn_eq_finset_of_finite, divisor_apply) are pre-existing/helper facts, honestly listed as non-children. Shape numbers are exact: direct_lemmas=4, glue_lines=64 (278-341), child_lines=[8,17,41,11] (=119-126,196-212,214-254,266-276), and depth=4 matches the verified chain parent->logDeriv_hasSimplePolesOn->logDeriv_meromorphicOrderAt_eq_neg_one_of_order_ne_zero->meromorphicOrderAt_eq_neg_one_of_sub_principal_isBigO_one->meromorphicOrderAt_nonneg_of_isBigO_one (cites at 295,210,193,152). | reviewer-correctness |
| generality | accept | Move is stated generally (interface-lemma = bridge between two abstraction layers; one bridge lemma per crossing direction), not tied to the example. 'When not to use' gives three specific conditions (boundary crossed once; bridge lemmas not self-contained; finiteness argument dominates), and consequences are honest (work is relocated not removed: the client still spends 64 lines assembling hypotheses; failure modes 'bridge too strong' and 'hno_boundary re-derivation' are grounded in the copied glue). Good-leaf paragraph explicitly says what makes leaves suit a bounded prover: self-contained statements that close on their own or from named siblings, with per-child sizes, and it honestly discloses the private-helper depth-4 chain rather than pretending the leaves are trivial. | reviewer-generality |
| provenance-licence | accept | check_provenance.py passes: 4 copied files byte-identical at 2c476fa6441c607096d93c8fc7ac0a227a655dae. Commit, licence and permalinks are consistent across entry.json, sources/pnt-and/SOURCE.md and source.json (all pin 2c476fa..., all record Apache-2.0). Fetched upstream LICENSE at the pinned commit: Apache License 2.0, matching the recorded licence and the copied upstream-LICENSE. Line-range permalink anchors verified against the local copy: docstring at 8-13, parent theorem at 278, child at 119, next theorem at 343. Everything traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd at commit `2c476fa6441c607096d93c8fc7ac0a227a655dae`, under `Apache-2.0`; see the [source note](../../sources/pnt-and/SOURCE.md) for the licence text and attribution.
