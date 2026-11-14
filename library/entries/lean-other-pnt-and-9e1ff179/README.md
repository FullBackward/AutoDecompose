# Residue theorem on a rectangle with a simple pole, by splitting into holomorphic + principal part

| | |
|---|---|
| Kind | instance |
| Move | other |
| Language | lean |
| Status | accepted |
| Source | [pnt-and](../../sources/pnt-and/SOURCE.md) at `2c476fa6441c` |
| Licence | `Apache-2.0` |

## Intent

A statement about the integral of a function with one simple pole is reduced
to two already-proved facts: the integrand is rewritten on the rectangle's
border as a holomorphic part `g` plus the principal part `A/(s-p)`, the sum is
integrated term by term, the holomorphic part's integral vanishes and the
principal part's integral is the residue `A`.

## The decomposition

### parent `ResidueTheoremOnRectangleWithSimplePole`: [`PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean` lines 634-663](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L634-L663) ([local copy](code/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean))

```lean
lemma ResidueTheoremOnRectangleWithSimplePole {f g : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (gHolo : HolomorphicOn g (Rectangle z w))
    (principalPart : Set.EqOn (f - fun s ↦ A / (s - p)) g (Rectangle z w \ {p})) :
    RectangleIntegral' f z w = A := by
  have principalPart' : Set.EqOn f (g + (fun s ↦ A / (s - p))) (Rectangle z w \ {p}) :=
    fun s hs => by rw [Pi.add_apply, ← principalPart hs, Pi.sub_apply, sub_add_cancel]
  have : Set.EqOn f (g + (fun s ↦ A / (s - p))) (RectangleBorder z w) :=
    principalPart'.mono <| Set.subset_sdiff.mpr
      ⟨rectangleBorder_subset_rectangle z w,
        disjoint_singleton_right.mpr
          (not_mem_rectangleBorder_of_rectangle_mem_nhds pInRectInterior)⟩
  rw [RectangleIntegral'_congr this]
  have t1 : RectangleBorderIntegrable g z w :=
    gHolo.rectangleBorderIntegrable
  have t2 : HolomorphicOn (fun s ↦ A / (s - p)) (Rectangle z w \ {p}) := by
    apply DifferentiableOn.mono (t := {p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · exact fun x hx => by
          rw [sub_ne_zero]
          exact hx
    · rintro s ⟨_, hs⟩
      exact hs
  have t3 : RectangleBorderIntegrable (fun s ↦ A / (s - p)) z w :=
    HolomorphicOn.rectangleBorderIntegrable' t2 pInRectInterior
  rw [RectangleIntegral', RectangleBorderIntegrable.add t1 t3, smul_add]
  rw [gHolo.vanishesOnRectangle (by rfl), smul_zero, zero_add]
  exact ResidueTheoremInRectangle zRe_le_wRe zIm_le_wIm pInRectInterior
```

### child `RectangleIntegral'_congr`: [`PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean` lines 191-193](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L191-L193) ([local copy](code/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean))

```lean
theorem RectangleIntegral'_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral' f z w = RectangleIntegral' g z w := by
  rw [RectangleIntegral', RectangleIntegral_congr h]
```

### child `HolomorphicOn.rectangleBorderIntegrable`: [`PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean` lines 250-251](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L250-L251) ([local copy](code/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean))

```lean
theorem HolomorphicOn.rectangleBorderIntegrable (hf : HolomorphicOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w := hf.continuousOn.rectangleBorderIntegrable
```

### child `HolomorphicOn.rectangleBorderIntegrable'`: [`PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean` lines 245-248](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L245-L248) ([local copy](code/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean))

```lean
theorem HolomorphicOn.rectangleBorderIntegrable'
    (hf : HolomorphicOn f (Rectangle z w \ {p})) (hp : Rectangle z w ∈ nhds p) :
    RectangleBorderIntegrable f z w :=
  hf.continuousOn.rectangleBorderNoPIntegrable (not_mem_rectangleBorder_of_rectangle_mem_nhds hp)
```

### child `RectangleBorderIntegrable.add`: [`PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean` lines 214-223](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L214-L223) ([local copy](code/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean))

```lean
theorem RectangleBorderIntegrable.add {f g : ℂ → E}
    (hf : RectangleBorderIntegrable f z w) (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral (f + g) z w = RectangleIntegral f z w + RectangleIntegral g z w := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  have h₁ := intervalIntegral.integral_add hf.1 hg.1
  have h₂ := intervalIntegral.integral_add hf.2.1 hg.2.1
  have h₃ := intervalIntegral.integral_add hf.2.2.1 hg.2.2.1
  have h₄ := intervalIntegral.integral_add hf.2.2.2 hg.2.2.2
  rw [h₁, h₂, h₃, h₄]
  module
```

### child `HolomorphicOn.vanishesOnRectangle`: [`PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean` lines 174-179](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L174-L179) ([local copy](code/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean))

```lean
theorem HolomorphicOn.vanishesOnRectangle [CompleteSpace E]
    {U : Set ℂ} (f_holo : HolomorphicOn f U)
    (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn f z w
    (f_holo.mono hU)
```

### child `ResidueTheoremInRectangle`: [`PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean` lines 587-597](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L587-L597) ([local copy](code/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean))

```lean
theorem ResidueTheoremInRectangle
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) :
    RectangleIntegral' (fun s => c / (s - p)) z w = c := by
  simp only [rectangle_mem_nhds_iff, uIoo_of_le zRe_le_wRe, uIoo_of_le zIm_le_wIm,
    mem_reProdIm, mem_Ioo] at pInRectInterior
  rw [RectangleIntegral.translate', RectangleIntegral']
  have : 1 / (2 * ↑π * I) * (2 * I * ↑π * c) = c := by
    field_simp
  rwa [ResidueTheoremAtOrigin']
  all_goals simp [*]
```

How the parts fit. The glue first turns the hypothesis `principalPart : Set.EqOn
(f - fun s ↦ A / (s - p)) g (Rectangle z w \ {p})` into an agreement of `f` with
`g + fun s ↦ A / (s - p)` on the border (lines 639-645), then rewrites with
`RectangleIntegral'_congr` to replace the integrand `f` by the sum (line 646).
It then proves integrability of the two summands on the border — `t1` for `g`
via `HolomorphicOn.rectangleBorderIntegrable` (647-648), and `t3` for the
principal part via `HolomorphicOn.rectangleBorderIntegrable'` (659-660, using
`t2`, which shows the principal part is holomorphic off `p`) — and splits the
sum with `RectangleBorderIntegrable.add` (line 661). The holomorphic term is
killed by `HolomorphicOn.vanishesOnRectangle` (line 662) and the principal part
is evaluated by `ResidueTheoremInRectangle` (line 663). One lemma is applied per
summand; the proof is a short sequence of `rw`/`exact` applications, not a
`calc` or a case split.

Lemma graph (who calls whom, all in this file):

```
ResidueTheoremOnRectangleWithSimplePole
 ├─ RectangleIntegral'_congr ─────────────── RectangleIntegral_congr (sibling)
 ├─ HolomorphicOn.rectangleBorderIntegrable ─ hf.continuousOn.rectangleBorderIntegrable (sibling)
 ├─ HolomorphicOn.rectangleBorderIntegrable' ─ hf.continuousOn.rectangleBorderNoPIntegrable (sibling)
 ├─ RectangleBorderIntegrable.add ─────────── intervalIntegral.integral_add (Mathlib)
 ├─ HolomorphicOn.vanishesOnRectangle ─────── integral_boundary_rect_eq_zero_of_differentiableOn (Mathlib)
 └─ ResidueTheoremInRectangle ── ResidueTheoremAtOrigin' (sibling)
        └─ integral_const_div_re_add_self ── integral_const_div_self_add_im
               └─ integral_self_div_sq_add_sq ── continuous_self_div_sq_add_sq ── sq_add_sq_ne_zero
```

Each child is a good leaf because its statement is self-contained and its proof
closes on its own from a sibling or a Mathlib lemma, so the glue never opens a
definition: the two `HolomorphicOn` integrability lemmas and
`HolomorphicOn.vanishesOnRectangle` are one-liners, `RectangleBorderIntegrable.add`
is linearity by `intervalIntegral.integral_add`, and `ResidueTheoremInRectangle`
closes by `ResidueTheoremAtOrigin'`, which itself bottoms out in explicit
log/arctan integrals (`sq_add_sq_ne_zero`, line 494).

One divergence worth recording: the blueprint plan above the lemma (lines
623-632) says to "pull everything to a square about the origin using
`RectanglePullToNhdOfPole`", but the formal proof instead calls
`ResidueTheoremInRectangle`, which translates to the origin with
`RectangleIntegral.translate'` and calls `ResidueTheoremAtOrigin'`. The
"pull to a square" step is inlined into `ResidueTheoremInRectangle` rather than
done by `RectanglePullToNhdOfPole` (my reading; see lines 587-597).

## Why it is good

1. The parent site (the whole lemma with its proof) is 30 lines long — a
   headline theorem whose proof is a short sequence of named-lemma applications
   (`check`, [lines 634-663](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L634-L663)).
2. The glue closes by citing `ResidueTheoremInRectangle`
   (`check`, [line 663](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L663)).
3. The parent's proof contains no `sorry`
   (`check`, [lines 634-663](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L634-L663)).
4. The authors state the plan in the `@[blueprint]` attribute above the lemma:
   "Replace f with g + A/(s-p) in the integral. The integral of g vanishes by
   Lemma HolomorphicOn.vanishesOnRectangle. To evaluate the integral of
   1/(s-p), pull everything to a square about the origin using Lemma
   RectanglePullToNhdOfPole, and rescale by c; what remains is handled by Lemma
   ResidueTheoremAtOrigin." (`author-statement`,
   [lines 623-632](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/2c476fa6441c607096d93c8fc7ac0a227a655dae/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L623-L632)).
5. The glue cites 6 project lemmas directly, and the longest chain of project
   lemmas below the main theorem is 7 long (`measurement`, counted by reading
   the copied file; see `entry.json → shape`).

In my opinion the detail worth copying is the *one lemma per summand*
discipline: the parent never has to manipulate the integrand itself, because
linearity (`RectangleBorderIntegrable.add`) plus a congruence
(`RectangleIntegral'_congr`) hand the two summands to lemmas whose statements
are exactly "the holomorphic part vanishes" and "the principal part is the
residue".

## When to use it, and when not

Use it when the integrand's behaviour is stated as a holomorphic part plus a
simple-pole principal part `A/(s-p)` (the `Set.EqOn (f - fun s ↦ A / (s - p)) g`
hypothesis here), and each part already has its own integral lemma — a vanishing
lemma for the holomorphic part and a residue lemma for the principal part —
plus an integrability lemma per summand. The two per-part lemmas must be stated
for exactly the rectangle and orientation the congruence produces.

Avoid it when the pole has higher order (the principal part is not a single
`A/(s-p)`, so there is no single residue term to evaluate); when the pole lies
on the border (the principal part is then not border-integrable, so
`HolomorphicOn.rectangleBorderIntegrable'` cannot discharge the integrability);
or when the holomorphic-part and principal-part lemmas live for a different
rectangle or orientation, so the congruence and the two lemmas do not compose.

## Consequences

The move creates a congruence obligation (that `f` equals `g + A/(s-p)` on the
border, discharged here by `RectangleIntegral'_congr`), an integrability
obligation for each summand (`g` via `HolomorphicOn.rectangleBorderIntegrable`,
the principal part via `HolomorphicOn.rectangleBorderIntegrable'`), and a
linearity step (`RectangleBorderIntegrable.add`) before the two per-part lemmas
can be applied. If the pole is not simple or lies on the border, the principal
part is not border-integrable and the split fails. The divergence between the
blueprint's "pull to a square" plan and the formal proof (which inlines that
step into `ResidueTheoremInRectangle`) is the kind of gap a reviewer should
check: the plan names `RectanglePullToNhdOfPole` but the proof never cites it.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml runs leanprover/lean-action v1.6.0 with build-args ':blueprint' on push/PR to main; the ':blueprint' target compiles the PrimeNumberTheoremAnd library (the @[blueprint] annotations live in its .lean files, e.g. PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean), so the file is built; pinned commit 2c476fa6441c607096d93c8fc7ac0a227a655dae is on default branch main (compare API: 2c476fa...main behind_by=0) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: RectangleIntegral'_congr@PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean:646, HolomorphicOn.rectangleBorderIntegrable@PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean:648, HolomorphicOn.rectangleBorderIntegrable'@PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean:660, RectangleBorderIntegrable.add@PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean:661, HolomorphicOn.vanishesOnRectangle@PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean:662, ResidueTheoremInRectangle@PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean:663; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 2c476fa6441c607096d93c8fc7ac0a227a655dae | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(parent, 30) -> lines: site parent has 30 lines | check_claims.py |
| 2 | verified | cites(parent, ResidueTheoremInRectangle) -> cites: ResidueTheoremInRectangle occurs at PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean:663 | check_claims.py |
| 3 | verified | no_sorry(PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean, 634-663) -> no_sorry: none of sorry, admit, axiom in PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean:634-663 | check_claims.py |
| 4 | verified | Read lines 623-632 of code/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean: they contain (proof := /-- Replace f with g + A/(s-p) in the integral ... Lemma \ref{HolomorphicOn.vanishesOnRectangle} ... Lemma \ref{RectanglePullToNhdOfPole} ... Lemma \ref{ResidueTheoremAtOrigin}. -/) inside the @[blueprint ...] attribute directly above lemma ResidueTheoremOnRectangleWithSimplePole (line 634). Text matches the quoted plan (with math delimiters and \ref{} wrappers stripped). | verifier |
| 5 | verified | Read the copied file: glue (634-663) cites 6 lemmas at 646 (RectangleIntegral'_congr), 648 (HolomorphicOn.rectangleBorderIntegrable), 660 (HolomorphicOn.rectangleBorderIntegrable'), 661 (RectangleBorderIntegrable.add), 662 (HolomorphicOn.vanishesOnRectangle), 663 (ResidueTheoremInRectangle). Chain of 7 confirmed at the cited citation lines: ResidueTheoremInRectangle(663) -> ResidueTheoremAtOrigin'(596) -> integral_const_div_re_add_self(569) -> integral_const_div_self_add_im(563) -> integral_self_div_sq_add_sq(545) -> continuous_self_div_sq_add_sq(510) -> sq_add_sq_ne_zero(499); each edge is a real call (grep-verified). | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Verified against the copied code. Parent site 634-663 is 30 lines and its glue cites exactly the 6 children at the lines the glue-cites-children check records (646 RectangleIntegral'_congr, 648 HolomorphicOn.rectangleBorderIntegrable, 660 HolomorphicOn.rectangleBorderIntegrable', 661 RectangleBorderIntegrable.add, 662 HolomorphicOn.vanishesOnRectangle, 663 ResidueTheoremInRectangle), and closes with 'exact ResidueTheoremInRectangle' (no sorry). Each child's statement and closed_by match its declared text: RectangleIntegral'_congr (191-193, rw [RectangleIntegral', RectangleIntegral_congr h]), HolomorphicOn.rectangleBorderIntegrable (250-251, hf.continuousOn.rectangleBorderIntegrable), HolomorphicOn.rectangleBorderIntegrable' (245-248, ...rectangleBorderNoPIntegrable...), RectangleBorderIntegrable.add (214-223, four intervalIntegral.integral_add then module), HolomorphicOn.vanishesOnRectangle (174-179, integral_boundary_rect_eq_zero_of_differentiableOn), ResidueTheoremInRectangle (587-597, ResidueTheoremAtOrigin' at 596). Shape numbers verified: direct_lemmas=6, glue_lines=30, child_lines=[3,2,4,10,6,11] match the site ranges; depth=7 matches the chain ResidueTheoremInRectangle -> ResidueTheoremAtOrigin' -> integral_const_div_re_add_self -> integral_const_div_self_add_im -> integral_self_div_sq_add_sq -> continuous_self_div_sq_add_sq -> sq_add_sq_ne_zero (citations at 596/569/563/545/510/499). Blueprint plan text (623-632) matches claim 4. | reviewer-correctness |
| generality | accept | Move generalises beyond the example: 'one lemma per summand' / 'termwise integration of a sum' is named in also_known_as and stated in use_when as a transferable condition (integrand = sum of parts, each with its own integral + integrability lemma), and known_uses (lines 729, 1113-1140, checked in code) show the same discipline at the finite-sum-of-poles generalisation via ResidueTheoremInRectangle + RectangleBorderIntegrable.add. When-not-to-use is honest and specific (higher-order pole, pole on border defeating HolomorphicOn.rectangleBorderIntegrable' which needs p in interior, mismatched rectangle/orientation), and consequences name the concrete obligations (congruence, per-summand integrability, linearity) plus the plan/proof divergence, which I confirmed: blueprint lines 623-632 name RectanglePullToNhdOfPole but the proof 634-663 cites ResidueTheoremInRectangle instead. Good-leaves-for-a-bounded-prover is answered: children are self-contained, close from a sibling or Mathlib lemma, so the glue never opens a definition. | reviewer-generality |
| provenance-licence | accept | Commit 2c476fa6441c607096d93c8fc7ac0a227a655dae is consistent across entry.json, sources/pnt-and/SOURCE.md and source.json. check_provenance.py passes (1 file byte-identical at the pinned commit, sha256 and 65137 bytes match the copied code/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean). Licence Apache-2.0 is recorded in entry.json, SOURCE.md and source.json, and sources/pnt-and/upstream-LICENSE is the Apache 2.0 text. Every permalink uses the same pinned commit and path, and all cited line ranges (parent 634-663, children 191-193/250-251/245-248/214-223/174-179/587-597, author-statement 623-632, known-uses 729 and 1113-1140) were opened with sed and match the entry's quoted code verbatim. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd at commit `2c476fa6441c607096d93c8fc7ac0a227a655dae`, under `Apache-2.0`; see the [source note](../../sources/pnt-and/SOURCE.md) for the licence text and attribution.
