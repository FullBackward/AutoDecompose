# Abstract the hypothesis to a predicate, prove its API, then instantiate (IMO 2024 P2)

| | |
|---|---|
| Kind | instance |
| Move | generalise-then-instantiate |
| Language | lean |
| Status | accepted |
| Source | [compfiles](../../sources/compfiles/SOURCE.md) at `1745e6ced3e6` |
| Licence | `Apache-2.0` |

## Intent

The problem's hypothesis is an existential (`∃ g N : ℕ+, ∀ n, N ≤ n → Nat.gcd … = g`); the proof
hides it behind a predicate `Condition a b` and proves every fact about `(a, b)` as a lemma over
an *arbitrary* witness `h : Condition a b`. Only at the very end is the concrete witness built and
the generalised lemmas instantiated, so no proof ever unfolds `Condition`.

## The decomposition

### parent `imo2024_p2`: [`Compfiles/Imo2024P2.lean` lines 197-200](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Imo2024P2.lean#L197-L200) ([local copy](code/Compfiles/Imo2024P2.lean))

```lean
problem imo2024_p2 (a b : ℕ+) :
    (a, b) ∈ solutionSet ↔
    ∃ g N : ℕ+,
      ∀ n : ℕ, N ≤ n → Nat.gcd (a^n + b) (b^n + a) = g := by
```

### context `condition_def`: [`Compfiles/Imo2024P2.lean` lines 43-45](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Imo2024P2.lean#L43-L45) ([local copy](code/Compfiles/Imo2024P2.lean))

```lean
/-- The condition of the problem. -/
def Condition (a b : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ ∃ g N : ℕ, 0 < g ∧ 0 < N ∧ ∀ n : ℕ, N ≤ n → Nat.gcd (a ^ n + b) (b ^ n + a) = g
```

### child `condition_api`: [`Compfiles/Imo2024P2.lean` lines 55-94](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Imo2024P2.lean#L55-L94) ([local copy](code/Compfiles/Imo2024P2.lean))

```lean
namespace Condition

variable {a b : ℕ} (h : Condition a b)

section
include h

lemma a_pos : 0 < a := h.1

lemma b_pos : 0 < b := h.2.1

/-- The value of `g` in the problem (determined by `a` and `b`). -/
noncomputable def g : ℕ := h.2.2.choose

lemma g_spec : ∃ N : ℕ, 0 < h.g ∧ 0 < N ∧ ∀ n : ℕ, N ≤ n → Nat.gcd (a ^ n + b) (b ^ n + a) = h.g :=
  h.2.2.choose_spec

/-- The value of `N` in the problem (any sufficiently large value). -/
noncomputable def N : ℕ := h.g_spec.choose

lemma N_spec : 0 < h.g ∧ 0 < h.N ∧ ∀ n : ℕ, h.N ≤ n → Nat.gcd (a ^ n + b) (b ^ n + a) = h.g :=
  h.g_spec.choose_spec

lemma g_pos : 0 < h.g := h.N_spec.1

lemma N_pos : 0 < h.N := h.N_spec.2.1

lemma gcd_eq_g {n : ℕ} (hn : h.N ≤ n) : Nat.gcd (a ^ n + b) (b ^ n + a) = h.g := h.N_spec.2.2 n hn

protected lemma symm : Condition b a := by
  refine ⟨h.b_pos, h.a_pos, h.g, h.N, h.g_pos, h.N_pos, fun n hn ↦ ?_⟩
  rw [Nat.gcd_comm]
  exact h.gcd_eq_g hn

lemma dvd_g_of_le_N_of_dvd {n : ℕ} (hn : h.N ≤ n) {d : ℕ} (hab : d ∣ a ^ n + b)
    (hba : d ∣ b ^ n + a) : d ∣ h.g := by
  rw [← h.gcd_eq_g hn, Nat.dvd_gcd_iff]
  exact ⟨hab, hba⟩

end
```

### child `instantiation`: [`Compfiles/Imo2024P2.lean` lines 206-217](https://github.com/dwrensha/compfiles/blob/1745e6ced3e671bd74417548494b034eb2c87da8/Compfiles/Imo2024P2.lean#L206-L217) ([local copy](code/Compfiles/Imo2024P2.lean))

```lean
  · simp only [solutionSet, Set.mem_singleton_iff, Prod.mk.injEq]
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    have hc : Condition a b := by
      refine ⟨ha, hb, ?_⟩
      obtain ⟨g, N, HCm⟩ := h
      use g, N
      refine ⟨g.pos, N.pos, ?_⟩
      exact fun n a ↦ HCm n a
    constructor
    · exact PNat.coe_eq_one_iff.mp (hc.a_eq_one)
    · exact PNat.coe_eq_one_iff.mp (hc.b_eq_one)
```

How the parts fit. The parent `imo2024_p2` is a biconditional; its hard direction (`←`, lines
206-217) is the one the move decomposes. The move has two phases.

1. **Generalise** (`condition_api`, lines 55-94 and its continuation to line 191): instead of
   working with the concrete existential, the author opens `namespace Condition`, fixes an
   arbitrary `h : Condition a b` as a section variable, and proves an API of lemmas — `a_pos`,
   `b_pos`, `g`, `g_spec`, `N`, `N_spec`, `g_pos`, `N_pos`, `gcd_eq_g`, `symm`,
   `dvd_g_of_le_N_of_dvd` — each closed by projecting from `h` and rewriting. `g` and `N` are
   `noncomputable def`s via `choose`, so the API is the only way to talk about them; the definition
   of `Condition` (lines 44-45) is never unfolded. This API is the interface through which the
   later lemmas `a_eq_one` (line 179) and `b_eq_one` (line 189) are derived.

2. **Instantiate** (`instantiation`, lines 206-217): the concrete `hc : Condition a b` is assembled
   from the hypothesis with `refine ⟨ha, hb, ?_⟩` (the witness `g, N` supplied by `obtain`), and
   the two generalised lemmas `hc.a_eq_one` and `hc.b_eq_one` close the goal via
   `PNat.coe_eq_one_iff.mp`.

The net effect: the 137-line development of the `Condition` API (27 declarations, lines 55-191) is
written once over the abstract witness, and the concrete pair enters only in the 12-line
instantiation.

## Why it is good

1. [check] The parent `imo2024_p2` closes using only the two generalised lemmas `hc.a_eq_one` and
   `hc.b_eq_one`, applied after the concrete witness `hc : Condition a b` is built at lines
   209-214; `Condition` is never unfolded (lines 206-217; the file is built by `lake build` in
   `.github/workflows/push-main.yaml` on pushes to main).
2. [check] Every lemma of the API section (lines 55-94) is closed by projecting from the witness
   `h` and rewriting (`a_pos : 0 < a := h.1`, `b_pos : 0 < b := h.2.1`, `gcd_eq_g … := h.N_spec.2.2
   n hn`), and no `unfold Condition`, `rw [Condition]`, or `simp [Condition]` occurs anywhere in the
   file.
3. [author-statement] The author names the abstraction and its derived quantities, signalling an
   interface meant to be used rather than unfolded: `Condition` is documented as "The condition of
   the problem." (line 43) and `g` as "The value of `g` in the problem (determined by `a` and `b`)."
   (line 66).
4. [known-use] The generalised API is instantiated a second time inside the development itself:
   `symm : Condition b a` (lines 84-87) constructs a swapped witness, and the b-side results are
   obtained by instantiating the a-side ones — `b_eq_one := h.symm.a_eq_one` (line 189) and
   `ab_add_one_dvd_b_pow_large_n_add_a` via `convert h.symm.ab_add_one_dvd_a_pow_large_n_add_b`
   (lines 154-157).

In my opinion the detail worth copying is the *boundary*: the whole proof lives on the abstract
side of the `Condition` interface, and the single concrete instantiation at lines 209-214 is the
only place the existential is unpacked, so a change to how the hypothesis is used would be a change
to the API, not to the consumers.

## When to use it, and when not

Use it when the same hypothesis is needed by several lemmas with different conclusions, so that the
concrete witness would clutter each statement; the needed facts must be expressible as accessor
lemmas (here `h.1`, `h.2.1`, `h.2.2.choose_spec`) so the predicate is never unfolded again. Avoid
it when the witness must be chosen or transformed inside a proof in a way the accessors cannot
express, when the predicate is used only once (the indirection is not worth it), or when a proof
genuinely needs to unfold the definition.

Survey F: the "generalise / strengthen" move is recorded in §8 (sources AlphaProof variants, Numina
"strengthening assumptions", the PIDE skill "Generalizations are fine if they can actually be
instantiated") with evidence "none", and it was not promoted to a numbered rule in §10; this entry
is a worked, checkable instance of that move, so it maps to no §10 rule (`rule.relation = none`).

## Consequences

The move turns one existential hypothesis into a predicate plus a fixed set of accessor lemmas, so
every later fact about the hypothesis must go through those accessors rather than re-deriving from
the existential; adding a fact means first adding (and proving) another API lemma.
`noncomputable def g`/`N` via `choose` make the API only partially computational, so each property
needs `choose_spec`; that is fine here because nothing unfolds the predicate. The indirection
concentrates all dependence on the concrete witness in one place (lines 209-214): the parent's
sufficiency rests on `hc` satisfying exactly the same interface, and a client that later needs a
stronger witness must generalise the predicate again.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push-main.yaml runs 'lake build' on push to main (default branch); Compfiles/Imo2024P2.lean is imported by Compfiles.lean line 273, so lake build builds it | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 1745e6ced3e671bd74417548494b034eb2c87da8 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Opened copied code/Compfiles/Imo2024P2.lean lines 206-217: witness hc : Condition a b built at 209-214; parent closes via PNat.coe_eq_one_iff.mp (hc.a_eq_one) and (hc.b_eq_one) at 216-217; no unfold of Condition. File built by lake build in push-main.yaml | verifier |
| 2 | verified | Opened lines 55-94: a_pos:=h.1, b_pos:=h.2.1, g:=h.2.2.choose, g_spec:=choose_spec, N:=h.g_spec.choose, N_spec:=choose_spec, g_pos:=h.N_spec.1, N_pos:=h.N_spec.2.1, gcd_eq_g:=h.N_spec.2.2 n hn, symm via refine+rw Nat.gcd_comm, dvd_g_of_le_N_of_dvd via rw; grep for 'unfold Condition','rw [Condition]','simp [Condition]' over copied file returns no matches | verifier |
| 3 | verified | Opened lines 43 and 66: line 43 docstring "The condition of the problem." on def Condition; line 66 "The value of g in the problem (determined by a and b)." on noncomputable def g | verifier |
| 4 | verified | Opened lines 84-87 (protected lemma symm : Condition b a), line 189 (b_eq_one : b = 1 := h.symm.a_eq_one), lines 154-157 (ab_add_one_dvd_b_pow_large_n_add_a via convert h.symm.ab_add_one_dvd_a_pow_large_n_add_b using 1) | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Correctness verified. Parent imo2024_p2 (L197-200), Condition def (L43-45), API child (L55-94) and instantiation child (L206-217) all match the copied code verbatim. The hard (<-) direction builds hc : Condition a b via refine/ha/hb/use g,N (L209-214) and closes by constructor + PNat.coe_eq_one_iff.mp (hc.a_eq_one) and (hc.b_eq_one) (L216-217); forward direction closes via refine <2,1>. No sorry/admit/axiom in file. Grep for unfold Condition / rw [Condition] / simp [Condition] returns 0 matches, so Condition is never unfolded. CI .github/workflows/push-main.yaml runs lake build on push to main, so the file compiles. Children and closing methods match the code; the decomposition is the generalise-then-instantiate it claims. | reviewer-correctness |
| generality | accept | Move is stated generally: goal_shape generalises the hypothesis to 'an existential or other packaged condition used repeatedly by many lemmas', and use_when gives abstract preconditions (hypothesis needed by several lemmas, concrete witness would clutter, facts expressible as accessors so the predicate is never unfolded). 'When not to use' lists three specific, honest failure modes: witness must be chosen/transformed in a way accessors cannot express; single use makes the indirection not worth it; a proof that genuinely needs to unfold. Consequences are honest: every later fact must go through the accessors so a new fact needs a new API lemma; choose-based g/N are only partially computational so each property needs choose_spec; dependence on the concrete witness is concentrated at lines 209-214 and a client needing a stronger witness must re-generalise. Minor imprecision: avoid_when says avoid when the witness is 'chosen or transformed' while the example's own symm (lines 84-87) does transform the witness, but that transformation is itself an accessor lemma, so the 'in a way the accessors cannot express' qualifier already scopes it correctly. | reviewer-generality |
| provenance-licence | accept | check_provenance passes (1 file byte-identical at pinned commit 1745e6ced3e671bd74417548494b034eb2c87da8). Permalink line anchors (43-45, 55-94, 197-200, 206-217) match the copied file exactly. Licence Apache-2.0 is consistent across entry.json, sources/compfiles/SOURCE.md, source.json, upstream-LICENSE (Apache 2.0 text), and the file header (Released under Apache 2.0). Source note and commit agree with source.json pinned commit. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/dwrensha/compfiles at commit `1745e6ced3e671bd74417548494b034eb2c87da8`, under `Apache-2.0`; see the [source note](../../sources/compfiles/SOURCE.md) for the licence text and attribution.
