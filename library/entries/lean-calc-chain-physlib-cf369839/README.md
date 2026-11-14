# Data Processing Inequality for sandwiched Rényi divergence (α > 1) via Stinespring purification

| | |
|---|---|
| Kind | instance |
| Move | calc-chain |
| Language | lean |
| Status | accepted |
| Source | [physlib](../../sources/physlib/SOURCE.md) at `ca577bfd34ef` |
| Licence | `Apache-2.0` |

## Intent

Reduce the Data Processing Inequality `D̃_ α(Φ ρ‖Φ σ) ≤ D̃_ α(ρ‖σ)` for an
arbitrary CPTP map `Φ` to a six-link calculational chain: first dilate `Φ`
into ancilla preparation + unitary conjugation + partial trace (Stinespring),
then rewrite the target step by step with a named lemma per link — two
purification lemmas plus one lemma each for tensor-with-pure-ancilla,
monotonicity under partial trace, unitary invariance, and dropping the
ancilla.

## The decomposition

### parent `sandwichedRenyiEntropy_DPI_gt_one`: [`QuantumInfo/Entropy/DPI.lean` lines 1349-1378](https://github.com/leanprover-community/physlib/blob/ca577bfd34ef356be2595528da1ef13a4a405816/QuantumInfo/Entropy/DPI.lean#L1349-L1378) ([local copy](code/QuantumInfo/Entropy/DPI.lean))

```lean
theorem sandwichedRenyiEntropy_DPI_gt_one (hα : 1 < α) (ρ σ : MState d₁) (Φ : CPTPMap d₁ d₂) :
    D̃_ α(Φ ρ‖Φ σ) ≤ D̃_ α(ρ‖σ) := by
  have _ : Nonempty d₁ := ρ.nonempty
  have _ : Nonempty d₂ := (Φ ρ).nonempty
  have : Inhabited d₂ := Classical.inhabited_of_nonempty ‹_›
  let ψ₀ : Ket (d₂ × d₂) := Ket.basis default
  let τ := MState.pure ψ₀
  obtain ⟨U, hU⟩ := Φ.purify_IsUnitary
  -- USe the `zero_prep` / `prep` / `append` from `CPTPMap.purify_trace`
  let zero_prep : CPTPMap Unit (d₂ × d₂) := CPTPMap.replacement τ
  let prep := ((CPTPMap.id : CPTPMap d₁ d₁) ⊗ᶜᵖ zero_prep)
  let append : CPTPMap d₁ (d₁ × Unit) := CPTPMap.ofEquiv (Equiv.prodPUnit d₁).symm
  calc D̃_ α(Φ ρ‖Φ σ)
    _ = D̃_ α((Φ.purify ((prep ∘ₘ append) ρ)).traceLeft.traceLeft‖
            (Φ.purify ((prep ∘ₘ append) σ)).traceLeft.traceLeft) := by
        have h_trace (ξ) : Φ ξ = (Φ.purify ((prep ∘ₘ append) ξ)).traceLeft.traceLeft := by
          exact congr($Φ.purify_trace ξ)
        rw [h_trace ρ, h_trace σ]
    _ = D̃_ α(((ρ ⊗ᴹ τ).uConj U).traceLeft.traceLeft‖
             ((σ ⊗ᴹ τ).uConj U).traceLeft.traceLeft) := by
        have h_app (ξ) : Φ.purify ξ = ξ.uConj U := congr($hU ξ)
        rw [prep_append_eq_tensor_pure ρ, prep_append_eq_tensor_pure σ, h_app, h_app]
    _ ≤ D̃_ α(((ρ ⊗ᴹ τ).uConj U).traceLeft‖((σ ⊗ᴹ τ).uConj U).traceLeft) :=
        sandwichedRenyiEntropy_mono_traceLeft hα ..
    _ ≤ D̃_ α((ρ ⊗ᴹ τ).uConj U‖(σ ⊗ᴹ τ).uConj U) :=
        sandwichedRenyiEntropy_mono_traceLeft hα ..
    _ = D̃_ α(ρ ⊗ᴹ τ‖σ ⊗ᴹ τ) :=
        sandwichedRenyiEntropy_conj_unitary (by positivity) _ _ _
    _ = D̃_ α(ρ‖σ) :=
        sandwichedRenyiEntropy_tensor_pure (by positivity) ρ σ ψ₀
```

### child `purify_IsUnitary`: [`QuantumInfo/Channels/CPTP.lean` lines 753-754](https://github.com/leanprover-community/physlib/blob/ca577bfd34ef356be2595528da1ef13a4a405816/QuantumInfo/Channels/CPTP.lean#L753-L754) ([local copy](code/QuantumInfo/Channels/CPTP.lean))

```lean
lemma purify_IsUnitary (Λ : CPTPMap dIn dOut) : Λ.purify.IsUnitary :=
  exists_purify Λ |>.choose_spec.1
```

### child `purify_trace`: [`QuantumInfo/Channels/CPTP.lean` lines 763-769](https://github.com/leanprover-community/physlib/blob/ca577bfd34ef356be2595528da1ef13a4a405816/QuantumInfo/Channels/CPTP.lean#L763-L769) ([local copy](code/QuantumInfo/Channels/CPTP.lean))

```lean
theorem purify_trace (Λ : CPTPMap dIn dOut) : Λ = (
    let zero_prep : CPTPMap Unit (dOut × dOut) := replacement (MState.pure (Ket.basis default))
    let prep := (id ⊗ᶜᵖ zero_prep)
    let append : CPTPMap dIn (dIn × Unit) := CPTPMap.ofEquiv (Equiv.prodPUnit dIn).symm
    CPTPMap.traceLeft ∘ₘ CPTPMap.traceLeft ∘ₘ Λ.purify ∘ₘ prep ∘ₘ append
  ) :=
  exists_purify Λ |>.choose_spec.2
```

### child `prep_append_eq_tensor_pure`: [`QuantumInfo/Entropy/DPI.lean` lines 1327-1339](https://github.com/leanprover-community/physlib/blob/ca577bfd34ef356be2595528da1ef13a4a405816/QuantumInfo/Entropy/DPI.lean#L1327-L1339) ([local copy](code/QuantumInfo/Entropy/DPI.lean))

```lean
theorem prep_append_eq_tensor_pure [Inhabited d₂] (ρ : MState d₁) :
    let ψ₀ : Ket (d₂ × d₂) := Ket.basis default
    let τ := MState.pure ψ₀
    let zero_prep : CPTPMap Unit (d₂ × d₂) := CPTPMap.replacement τ
    let prep := (CPTPMap.id ⊗ᶜᵖ zero_prep)
    let append : CPTPMap d₁ (d₁ × Unit) := CPTPMap.ofEquiv (Equiv.prodPUnit d₁).symm
    (prep ∘ₘ append) ρ = ρ ⊗ᴹ τ := by
  apply MState.ext
  ext1
  funext ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  have h := CPTPMap.prep_append_map_entry ρ.m a₁ b₁ a₂ b₂
  simp only [MState.prod, kronecker]
  exact h
```

### child `sandwichedRenyiEntropy_mono_traceLeft`: [`QuantumInfo/Entropy/DPI.lean` lines 1314-1322](https://github.com/leanprover-community/physlib/blob/ca577bfd34ef356be2595528da1ef13a4a405816/QuantumInfo/Entropy/DPI.lean#L1314-L1322) ([local copy](code/QuantumInfo/Entropy/DPI.lean))

```lean
theorem sandwichedRenyiEntropy_mono_traceLeft [Nonempty dA]
    (hα : 1 < α) (ρ σ : MState (dA × dB)) :
    D̃_ α(ρ.traceLeft‖σ.traceLeft) ≤ D̃_ α(ρ‖σ) := by
  -- traceLeft = SWAP.traceRight, and SWAP preserves the SRD
  rw [← MState.traceRight_SWAP, ← MState.traceRight_SWAP]
  calc D̃_ α(ρ.SWAP.traceRight‖σ.SWAP.traceRight)
      ≤ D̃_ α(ρ.SWAP‖σ.SWAP) :=
        sandwichedRenyiEntropy_mono_traceRight' hα ρ.SWAP σ.SWAP
    _ = D̃_ α(ρ‖σ) := sandwichedRenyiEntropy_SWAP ρ σ
```

### child `sandwichedRenyiEntropy_conj_unitary`: [`QuantumInfo/Entropy/DPI.lean` lines 1231-1281](https://github.com/leanprover-community/physlib/blob/ca577bfd34ef356be2595528da1ef13a4a405816/QuantumInfo/Entropy/DPI.lean#L1231-L1281) ([local copy](code/QuantumInfo/Entropy/DPI.lean))

```lean
lemma sandwichedRenyiEntropy_conj_unitary (hα : 0 < α) (ρ σ : MState d)
    (U : Matrix.unitaryGroup d ℂ) :
    D̃_ α(ρ.uConj U‖σ.uConj U) = D̃_ α(ρ‖σ) := by
  -- Since unitary conjugation preserves the kernel, the condition σ.M.ker ≤ ρ.M.ker is
  -- equivalent to (σ.uConj U).M.ker ≤ (ρ.uConj U).M.ker.
  have h_kernel : σ.M.ker ≤ ρ.M.ker ↔ (σ.uConj U).M.ker ≤ (ρ.uConj U).M.ker := by
    have hk (A : HermitianMat d ℂ) : (A.conj U.val).ker = A.ker.map (U.val.toEuclideanLin) := by
      ext x
      simp [conj]
      constructor <;> intro hx
      all_goals generalize_proofs at *
      · use (U.val.conjTranspose.toEuclideanLin x)
        simp_all [ker, Matrix.toEuclideanLin]
        simp_all [lin, Matrix.toLpLin]
        have h_unitary : (U.val * U.val.conjTranspose) = 1 := by
          exact U.2.2
        generalize_proofs at *; (
        apply_fun (U.val.conjTranspose *ᵥ ·) at hx
        simp_all [Matrix.mul_assoc, Matrix.mulVec_mulVec]
        simp_all [← Matrix.mul_assoc, mul_eq_one_comm.mp h_unitary])
      · obtain ⟨y, hy, rfl⟩ := hx; simp_all [Matrix.toEuclideanLin, Matrix.mul_assoc]
        simp_all [ker, Matrix.toLpLin]
        simp_all [lin]
        simp_all [Matrix.toLpLin, Matrix.mulVec, funext_iff]
        simp_all [Matrix.mul_apply, dotProduct]
        -- Since U is unitary, we have ∑_{x_3} ⟨U_{x_3 x}, U_{x_3 x_1⟩ = δ_{x x_1}.
        have h_unitary : ∀ x x_1, ∑ x_3, (starRingEnd ℂ) (U.val x_3 x) * U.val x_3 x_1 =
            if x = x_1 then 1 else 0 := by
          intro x x_1
          have this := congr_fun (congr_fun U.2.1 x) x_1
          simp_all [Matrix.mul_apply, Matrix.one_apply]
        simp_all [mul_assoc, Finset.sum_mul]
        intro x; rw [Finset.sum_comm]; simp_all [← Finset.mul_sum]
    simp [hk, MState.uConj]
    constructor <;> intro h <;> simp_all [IsConcreteLE.le_iff]
    · exact fun x hx => ⟨x, h hx, rfl⟩
    · intro x hx
      obtain ⟨y, hy, hy'⟩ := h x hx
      obtain ⟨⟩ : y = x := by
        apply_fun (U.val⁻¹).mulVec at hy'
        simp_all [Matrix.mulVec_mulVec]
        exact PiLp.ext (congrFun hy')
      exact hy
  by_cases h : σ.M.ker ≤ ρ.M.ker <;> simp_all [SandwichedRelRentropy]
  split_ifs <;> simp_all [MState.uConj]
  · congr 1
    rw [inner_sub_right, inner_sub_right]
    grind only [log_conj_unitary, inner_conj_unitary]
  · ext1
    congr 3
    convert! congr_arg Real.log (sandwichedTraceFunctional_conj_unitary_MState U ρ σ) using 1
```

### child `sandwichedRenyiEntropy_tensor_pure`: [`QuantumInfo/Entropy/DPI.lean` lines 1287-1289](https://github.com/leanprover-community/physlib/blob/ca577bfd34ef356be2595528da1ef13a4a405816/QuantumInfo/Entropy/DPI.lean#L1287-L1289) ([local copy](code/QuantumInfo/Entropy/DPI.lean))

```lean
lemma sandwichedRenyiEntropy_tensor_pure (hα : 0 < α) (ρ σ : MState d₁) (ψ : Ket d₂) :
    D̃_ α(ρ ⊗ᴹ MState.pure ψ‖σ ⊗ᴹ MState.pure ψ) = D̃_ α(ρ‖σ) := by
  simp [hα]
```

## How the parts fit

The parent `sandwichedRenyiEntropy_DPI_gt_one` is a six-link `calc` chain
that walks `D̃_ α(Φ ρ‖Φ σ)` down to `D̃_ α(ρ‖σ)`. Before the chain, the proof
fixes the dilation: `obtain ⟨U, hU⟩ := Φ.purify_IsUnitary` gives a unitary `U`
with `Φ.purify ξ = ξ.uConj U`, and the `let`s name the Stinespring pieces
(`zero_prep`/`prep`/`append`) so they match the statement of `purify_trace`.
The links then proceed:

1. **dilate** (lines 1362-1366): `Φ ξ` is rewritten to
   `(Φ.purify ((prep ∘ₘ append) ξ)).traceLeft.traceLeft`, justified by
   `purify_trace` (the Stinespring identity `Λ = traceLeft ∘ₘ traceLeft ∘ₘ purify ∘ₘ prep ∘ₘ append`);
2. **tensor the ancilla** (lines 1367-1370): `(prep ∘ₘ append) ξ` becomes
   `ξ ⊗ᴹ τ` by `prep_append_eq_tensor_pure`, and `Φ.purify ξ` becomes
   `ξ.uConj U` by the `hU` obtained in the setup;
3. **drop the first trace** (lines 1371-1372): `sandwichedRenyiEntropy_mono_traceLeft`;
4. **drop the second trace** (lines 1373-1374): the same lemma again;
5. **undo the unitary** (lines 1375-1376): `sandwichedRenyiEntropy_conj_unitary`;
6. **undo the ancilla** (lines 1377-1378): `sandwichedRenyiEntropy_tensor_pure`,
   reaching `D̃_ α(ρ‖σ)`.

The lemma graph below the main theorem (arrow = "is closed by / uses"):

```
sandwichedRenyiEntropy_DPI_gt_one
├── purify_IsUnitary                   (CPTP.lean; = exists_purify .. .choose_spec.1)
├── purify_trace                       (CPTP.lean; = exists_purify .. .choose_spec.2)
├── prep_append_eq_tensor_pure         (DPI.lean;  → CPTPMap.prep_append_map_entry)
├── sandwichedRenyiEntropy_mono_traceLeft  (DPI.lean; → mono_traceRight' → mono_traceRight
│                                             → sandwichedTraceFunctional_mono_traceRight
│                                             → sandwichedTraceFunctional_jointly_convex)
├── sandwichedRenyiEntropy_conj_unitary    (DPI.lean;  → sandwichedTraceFunctional_conj_unitary_MState)
└── sandwichedRenyiEntropy_tensor_pure     (DPI.lean;  = simp [hα])
```

Why each child is a good leaf — a self-contained statement whose proof closes
on its own or from named siblings:

- `purify_IsUnitary` and `purify_trace` are one-line projections of the
  existence statement `exists_purify`, so the DPI proof consumes the
  Stinespring representation without ever unfolding it.
- `prep_append_eq_tensor_pure` is a self-contained matrix-level identity
  (prep∘append = tensor with a fixed pure state) closed by the sibling
  `CPTPMap.prep_append_map_entry` (which lives in the same copied file
  `QuantumInfo/Channels/CPTP.lean`).
- `sandwichedRenyiEntropy_mono_traceLeft` is the carrying lemma (used twice);
  it closes on the named sibling chain `mono_traceRight'` → `mono_traceRight`
  → `sandwichedTraceFunctional_mono_traceRight` plus SWAP invariance
  (`sandwichedRenyiEntropy_SWAP`).
- `sandwichedRenyiEntropy_conj_unitary` closes on the trace-functional
  version `sandwichedTraceFunctional_conj_unitary_MState` plus a
  kernel-equivalence argument and a `by_cases` on the kernel condition.
- `sandwichedRenyiEntropy_tensor_pure` is trivial at this point: `simp [hα]`.

## Why it is good

1. The parent `sandwichedRenyiEntropy_DPI_gt_one` is declared in
   `QuantumInfo/Entropy/DPI.lean` within lines 1349-1378. (check)
2. No `sorry`, `admit`, or `axiom` occurs in `QuantumInfo/Entropy/DPI.lean`
   lines 1349-1378. (check)
3. The parent site cites `purify_trace`. (check)
4. The authors state the reduction in the doc comment above the theorem: "The
   proof uses the Stinespring representation (see `CPTPMap.exists_purify`):
   every CPTP map can be written as ancilla preparation + unitary conjugation
   + partial trace. Since the sandwiched Rényi divergence is invariant under
   the first two operations (by additivity and relabel invariance) and
   monotone under partial trace (by `sandwichedRenyiEntropy_mono_traceRight`),
   the DPI follows." (author-statement)
5. Five project lemmas sit in a chain below the parent:
   `sandwichedRenyiEntropy_mono_traceLeft` (line 1314) is closed by
   `sandwichedRenyiEntropy_mono_traceRight'` (cited at line 1321), which uses
   `sandwichedRenyiEntropy_mono_traceRight` (line 1306), which uses
   `sandwichedTraceFunctional_mono_traceRight` (line 1222), which uses
   `sandwichedTraceFunctional_jointly_convex` (line 1110); all in
   `QuantumInfo/Entropy/DPI.lean`. (measurement)
6. The parent site is 30 lines long. (check)

In my opinion the detail worth copying is that the two hard invariance
lemmas (`sandwichedRenyiEntropy_conj_unitary`, the partial-trace monotonicity)
were proved once, as named leaves, so the headline DPI is a pure chain of six
citations and the reader sees the whole argument at a glance.

## When to use it, and when not

Use a `calc` chain whose links are named lemmas when the target is an
inequality or equality between two instances of an order-respecting quantity
(here `D̃_ α(Φ ρ‖Φ σ) ≤ D̃_ α(ρ‖σ)`), and when a representation theorem (here
Stinespring: ancilla preparation + unitary + partial trace) lets you walk the
target through an intermediate normal form, one invariance/monotonicity lemma
per link. Prefer it when the per-link lemmas already exist as leaves, so the
chain stays short and the skeleton is exactly the citations.

Avoid it when the steps are not already named lemmas — an inline `calc` with
long `by` blocks hides the skeleton this move is meant to expose — or when a
link needs the wrong monotonicity direction (`≥`), which a calculational chain
does not compose by default (survey F §10 rule 9).

## Consequences

Each link is an `=` or `≤` justified by one named lemma, so transitivity is
discharged by the chain itself and the only remaining obligations are the
hypotheses of each lemma (`hα : 1 < α`, `0 < α`, and the
`Nonempty`/`Inhabited` instances). Failure modes: a link in the wrong
direction (`≥`) does not compose; steps 3 and 4 reuse the same
`sandwichedRenyiEntropy_mono_traceLeft` with a `..` hole, so the two partial
traces must be dropped in exactly the right order; and the kernel condition of
the trace-functional monotonicity is hidden inside
`sandwichedRenyiEntropy_mono_traceLeft`, which dispatches it via `by_cases` in
`sandwichedRenyiEntropy_mono_traceRight'`.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/build.yml runs 'lake build -KCI --iofail' which builds Physlib (incl. QuantumInfo/Entropy/DPI.lean); pinned commit ca577bfd is on default branch master (compare master...ca577bfd = behind by 1, ahead 0) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: purify_IsUnitary@QuantumInfo/Entropy/DPI.lean:1356, purify_trace@QuantumInfo/Entropy/DPI.lean:1357, prep_append_eq_tensor_pure@QuantumInfo/Entropy/DPI.lean:1370, sandwichedRenyiEntropy_mono_traceLeft@QuantumInfo/Entropy/DPI.lean:1372, sandwichedRenyiEntropy_conj_unitary@QuantumInfo/Entropy/DPI.lean:1376, sandwichedRenyiEntropy_tensor_pure@QuantumInfo/Entropy/DPI.lean:1378; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at ca577bfd34ef356be2595528da1ef13a4a405816 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(sandwichedRenyiEntropy_DPI_gt_one, QuantumInfo/Entropy/DPI.lean, 1349-1378) -> declared: sandwichedRenyiEntropy_DPI_gt_one is declared at QuantumInfo/Entropy/DPI.lean:1349 | check_claims.py |
| 2 | verified | no_sorry(QuantumInfo/Entropy/DPI.lean, 1349-1378) -> no_sorry: none of sorry, admit, axiom in QuantumInfo/Entropy/DPI.lean:1349-1378 | check_claims.py |
| 3 | verified | cites(sandwichedRenyiEntropy_DPI_gt_one, purify_trace) -> cites: purify_trace occurs at QuantumInfo/Entropy/DPI.lean:1357 | check_claims.py |
| 4 | verified | Doc comment above the theorem (DPI.lean 1341-1348) reads verbatim as quoted: 'The proof uses the Stinespring representation (see CPTPMap.exists_purify): every CPTP map can be written as ancilla preparation + unitary conjugation + partial trace. Since the sandwiched Rényi divergence is invariant under the first two operations (by additivity and relabel invariance) and monotone under partial trace (by sandwichedRenyiEntropy_mono_traceRight), the DPI follows.' | verifier |
| 5 | verified | Chain verified in QuantumInfo/Entropy/DPI.lean: mono_traceLeft declared 1314, cites mono_traceRight' at 1321; mono_traceRight' (1302) cites mono_traceRight at 1306; mono_traceRight (1209) cites sandwichedTraceFunctional_mono_traceRight at 1222; sandwichedTraceFunctional_mono_traceRight (1083) cites sandwichedTraceFunctional_jointly_convex at 1110; jointly_convex declared 568. All in the same file. | verifier |
| 6 | verified | lines(sandwichedRenyiEntropy_DPI_gt_one, 30) -> lines: site sandwichedRenyiEntropy_DPI_gt_one has 30 lines | check_claims.py |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Verified against local copies. Parent sandwichedRenyiEntropy_DPI_gt_one (DPI.lean:1349-1378) is a six-link calc chain walking D̃_α(Φρ‖Φσ) to D̃_α(ρ‖σ) via = and ≤ only (no ≥), so it closes. The six children are exactly the six named lemmas the glue cites: purify_IsUnitary (obtain at 1356), purify_trace (1365), prep_append_eq_tensor_pure (1370), sandwichedRenyiEntropy_mono_traceLeft (1372 & 1374), sandwichedRenyiEntropy_conj_unitary (1376), sandwichedRenyiEntropy_tensor_pure (1378); no extra named lemma is cited. Each child statement and closed_by matches the code verbatim (purify_IsUnitary=choose_spec.1; purify_trace=choose_spec.2; prep_append_eq_tensor_pure via CPTPMap.prep_append_map_entry; mono_traceLeft via mono_traceRight'+SWAP; conj_unitary via sandwichedTraceFunctional_conj_unitary_MState+by_cases; tensor_pure=simp[hα]). Shape numbers correct: direct_lemmas=6, glue_lines=30 (1349-1378), child_lines=[2,7,13,9,51,3] matching each child site span, and depth=5 confirmed by the real chain mono_traceLeft(1314)->mono_traceRight'(1321)->mono_traceRight(1306/1209)->sandwichedTraceFunctional_mono_traceRight(1222/1083)->sandwichedTraceFunctional_jointly_convex(1110/568). | reviewer-correctness |
| generality | accept | Move stated generically: applicability.goal_shape/use_when and README 'When to use it' describe an order-respecting quantity plus a representation-theorem walk (ancilla+unitary+trace), not this DPI alone; the author doc comment (DPI.lean 1341-1348, claim 4) gives the same generic reduction. 'When not to use' and consequences are honest and specific, and I confirmed each in code: the >= direction caveat is a real calc-chain limitation; steps 3/4 both use sandwichedRenyiEntropy_mono_traceLeft hα .. (parent lines 1372/1374); the kernel condition is dispatched by by_cases hker in mono_traceRight' (line 1305); the leaves are one-line projections purify_IsUnitary/purify_trace = exists_purify .. |>.choose_spec.i (CPTP.lean 753/763) or simp [hα] (tensor_pure, DPI.lean 1287-1289). 'Why each child is a good leaf' answers the bounded-prover question: each leaf is a self-contained statement closing on its own or on named siblings, one per link, so a bounded prover gets one lemma-sized hole. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit and licence are consistent and traceable. check_provenance.py passes: both copied files (DPI.lean, CPTP.lean) byte-identical at ca577bfd34ef356be2595528da1ef13a4a405816. All entry permalinks use that same commit. entry.json source.commit, source.json commit, and SOURCE.md commit agree. Licence recorded as Apache-2.0 in entry, source.json, and SOURCE.md; the LICENSE at the pinned commit fetched via fetch_file.py is Apache 2.0 and sha256-matches sources/physlib/upstream-LICENSE. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/leanprover-community/physlib at commit `ca577bfd34ef356be2595528da1ef13a4a405816`, under `Apache-2.0`; see the [source note](../../sources/physlib/SOURCE.md) for the licence text and attribution.
