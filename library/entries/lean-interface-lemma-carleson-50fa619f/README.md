# Forest structure API lemmas: simp membership and field forwarders

| | |
|---|---|
| Kind | instance |
| Move | interface-lemma |
| Language | lean |
| Status | accepted |
| Source | [carleson](../../sources/carleson/SOURCE.md) at `d75f54374f7f` |
| Licence | `Apache-2.0` |

## Intent

Wrap the `Forest n` structure's raw projections and predicate fields in a
block of `@[simp]` membership lemmas and one-line forwarding lemmas, so that
every later client reads and reasons about a forest through the coercions
`u ∈ t` and `t u` without unfolding `Forest.mk` or the projections
`𝔘` / `𝔗`.

## The decomposition

### parent `Forest-API-lemmas`: [`Carleson/Forest.lean` lines 43-58](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/Forest.lean#L43-L58) ([local copy](code/Carleson/Forest.lean))

```lean
@[simp] lemma mem_mk (n 𝔘 𝔗 a b c d e f g h) (p : 𝔓 X) :
    p ∈ Forest.mk (n := n) 𝔘 𝔗 a b c d e f g h ↔ p ∈ 𝔘 := Iff.rfl

@[simp] lemma mem_𝔘 : u ∈ t.𝔘 ↔ u ∈ t := .rfl
@[simp] lemma mem_𝔗 : p ∈ t.𝔗 u ↔ p ∈ t u := .rfl

lemma nonempty (hu : u ∈ t) : (t u).Nonempty := t.nonempty' hu
lemma ordConnected (hu : u ∈ t) : OrdConnected (t u) := t.ordConnected' hu
lemma 𝓘_ne_𝓘 (hu : u ∈ t) (hp : p ∈ t u) : 𝓘 p ≠ 𝓘 u := t.𝓘_ne_𝓘' hu hp
lemma smul_four_le (hu : u ∈ t) (hp : p ∈ t u) : smul 4 p ≤ smul 1 u := t.smul_four_le' hu hp
lemma stackSize_le : stackSize t x ≤ 2 ^ n := t.stackSize_le'
lemma dens₁_𝔗_le (hu : u ∈ t) : dens₁ (t u) ≤ 2 ^ (4 * (a : ℝ) - n + 1) := t.dens₁_𝔗_le' hu
lemma lt_dist (hu : u ∈ t) (hu' : u' ∈ t) (huu' : u ≠ u') {p} (hp : p ∈ t u') (h : 𝓘 p ≤ 𝓘 u) :
    2 ^ (Z * (n + 1)) < dist_(p) (𝒬 p) (𝒬 u) := t.lt_dist' hu hu' huu' hp h
lemma ball_subset (hu : u ∈ t) (hp : p ∈ t u) : ball (𝔠 p) (8 * D ^ 𝔰 p) ⊆ 𝓘 u :=
  t.ball_subset' hu hp
```

### context `Forest`: [`Carleson/Forest.lean` lines 19-33](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/Forest.lean#L19-L33) ([local copy](code/Carleson/Forest.lean))

```lean
variable (X) in
/-- An `n`-forest -/
structure Forest (n : ℕ) where
  𝔘 : Set (𝔓 X)
  /-- The value of `𝔗 u` only matters when `u ∈ 𝔘`. -/
  𝔗 : 𝔓 X → Set (𝔓 X)
  nonempty' {u : _} (hu : u ∈ 𝔘) : (𝔗 u).Nonempty
  ordConnected' {u : _} (hu : u ∈ 𝔘) : OrdConnected (𝔗 u) -- (2.0.33)
  𝓘_ne_𝓘' {u : _} (hu : u ∈ 𝔘) {p} (hp : p ∈ 𝔗 u) : 𝓘 p ≠ 𝓘 u
  smul_four_le' {u : _} (hu : u ∈ 𝔘) {p} (hp : p ∈ 𝔗 u) : smul 4 p ≤ smul 1 u -- (2.0.32)
  stackSize_le' {x : _} : stackSize 𝔘 x ≤ 2 ^ n -- (2.0.34), we formulate this a bit differently.
  dens₁_𝔗_le' {u : _} (hu : u ∈ 𝔘) : dens₁ (𝔗 u) ≤ 2 ^ (4 * (a : ℝ) - n + 1) -- (2.0.35)
  lt_dist' {u u' : _} (hu : u ∈ 𝔘) (hu' : u' ∈ 𝔘) (huu' : u ≠ u') {p} (hp : p ∈ 𝔗 u')
    (h : 𝓘 p ≤ 𝓘 u) : 2 ^ (Z * (n + 1)) < dist_(p) (𝒬 p) (𝒬 u) -- (2.0.36)
  ball_subset' {u : _} (hu : u ∈ 𝔘) {p} (hp : p ∈ 𝔗 u) : ball (𝔠 p) (8 * D ^ 𝔰 p) ⊆ 𝓘 u -- (2.0.37)
```

### context `Forest-coercions`: [`Carleson/Forest.lean` lines 37-41](https://github.com/fpvandoorn/carleson/blob/d75f54374f7f930e70a86b443f20d0e0935c275e/Carleson/Forest.lean#L37-L41) ([local copy](code/Carleson/Forest.lean))

```lean
variable {n : ℕ} (t : Forest X n)

instance : CoeHead (Forest X n) (Set (𝔓 X)) := ⟨Forest.𝔘⟩
instance : Membership (𝔓 X) (Forest X n) := ⟨fun t x ↦ x ∈ (t : Set (𝔓 X))⟩
instance : CoeFun (Forest X n) (fun _ ↦ 𝔓 X → Set (𝔓 X)) := ⟨fun t x ↦ t.𝔗 x⟩
```

How the parts fit. The `Forest` structure (lines 19-33) bundles a set `𝔘`,
a map `𝔗`, and eight predicates, each stated over the raw projections with
hypotheses `hu : u ∈ 𝔘` and `hp : p ∈ 𝔗 u`. The three instances (lines
39-41) then declare the interface: `t : Set (𝔓 X)` is `t.𝔘`, `u ∈ t` is
`u ∈ t.𝔘`, and `t u` is `t.𝔗 u`.

The parent block (lines 43-58) provides the interface in two layers. First
the three `@[simp]` lemmas make the projection↔coercion correspondence rewrite
automatically: `mem_mk` unfolds membership of a constructed forest, and
`mem_𝔘` / `mem_𝔗` translate between the projection and coercion spellings,
all by `rfl`. Then eight forwarding lemmas restate each field so that a client
writes `hu : u ∈ t` and `hp : p ∈ t u` instead of `hu : u ∈ 𝔘` and
`hp : p ∈ 𝔗 u`; each is closed by a single application of the corresponding
field (`nonempty` by `t.nonempty' hu`, …, `ball_subset` by
`t.ball_subset' hu hp`). No lemma here has a proof longer than one forward:
the content is purely a change of hypothesis spelling at the abstraction
boundary, not new mathematics.

## Why it is good

1. Each of the eight forwarding lemmas (lines 49-58) is closed by a single
   application of the corresponding `Forest` field, and the three `@[simp]`
   lemmas (lines 43-47) close by `Iff.rfl` / `.rfl`; the file is built by the
   project's CI (`check`, lines 43-58, `.github/workflows/push.yml`).
2. The eight forwarding lemmas correspond one-to-one to the eight predicate
   fields of `Forest` (lines 25-33), each restating one field with
   `hu : u ∈ t` / `hp : p ∈ t u` in place of `hu : u ∈ 𝔘` / `hp : p ∈ 𝔗 u`
   (`measurement`, lines 25-33 vs 49-58).
3. The same interface pattern recurs for the `Row` structure in the same file
   (lines 86-101): `Row` extends `Forest`, re-declares `@[simp] mem_𝔘` /
   `mem_𝔗`, and forwards `pairwiseDisjoint'` to `pairwiseDisjoint`
   (`known-use`, lines 86-101).
4. The authors annotate the `𝔗` field: "The value of `𝔗 u` only matters when
   `u ∈ 𝔘`" (line 23) — the exact hypothesis the forwarding lemmas lift to
   `u ∈ t` (`author-statement`, line 23).
5. A client in the same file consumes the interface: `ball_subset_of_mem_𝓘`
   (lines 62-65) applies `t.ball_subset hu hp` at line 64 rather than
   unfolding the `ball_subset'` field (`known-use`, lines 62-65).

In my opinion the detail worth copying is that the whole interface costs zero
mathematics: each lemma is a bare forward to the same-named field, and the
`@[simp]` lemmas make the spelling switch invisible, so the structure's raw
fields and the client-facing API are kept consistent by construction.

## When to use it, and when not

Use it when a structure's fields are stated over its raw projections and many
later lemmas would otherwise each unfold the constructor or the projections.
Declare the coercion instances first (here `CoeHead`, `Membership`, `CoeFun`),
then give one `@[simp]` lemma per spelling difference and one forwarding lemma
per field, so the simplifier does the translation and clients never see the
projections.

Avoid it when the structure is used in only one place (the wrapper is then a
net cost), when a client genuinely needs the projection form itself (for
example to reason about `𝔘` as a set independent of the forest), or when the
coercion instances are not in scope, in which case the `@[simp]` lemmas do not
fire and the interface is only half present.

## Consequences

The interface adds 11 lemmas at near-zero proof cost (each a one-line forward),
but they must stay in sync if a field's statement changes. It re-binds the
hypotheses from the projection form (`u ∈ 𝔘`, `p ∈ 𝔗 u`) to the coercion form
(`u ∈ t`, `p ∈ t u`), so a client that still holds `u ∈ 𝔘` must first rewrite
via `mem_𝔘` before applying a forwarder. The `@[simp]` lemmas make the
projection/coercion translation automatic, but only once the
`CoeHead` / `Membership` / `CoeFun` instances are in scope; outside that scope
the forwarders still typecheck but the spelling does not normalise.

Survey F §10 has no rule that names the interface-lemma move (its candidate
rules cover splitting, induction, witnesses, calculational chains, memoising
and repair, but not "state an API lemma at an abstraction boundary"), so this
entry maps to no rule rather than forcing a fit.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/push.yml build_project job: lean-action build:true build-args 'Carleson Challenge Solution' on push to master; commit d75f54374f7f930e70a86b443f20d0e0935c275e is master HEAD (default branch, compare identical); lakefile.toml defaultTargets=['Carleson'] and lean_lib Carleson include Carleson/Forest.lean | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at d75f54374f7f930e70a86b443f20d0e0935c275e | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Read copied code/Carleson/Forest.lean (byte-identical to upstream at d75f543): lines 49-58 are 8 forwarders each closed by one field (nonempty=t.nonempty' hu ... ball_subset=t.ball_subset' hu hp); lines 43-47 three @[simp] lemmas closed by Iff.rfl/.rfl/.rfl. Fetched .github/workflows/push.yml: build_project uses lean-action build:true build-args 'Carleson Challenge Solution' on push to master, building Carleson/Forest.lean. | verifier |
| 2 | verified | Read code/Carleson/Forest.lean: lines 25-33 declare 8 predicate fields (nonempty'..ball_subset') with hu : u ∈ 𝔘 / hp : p ∈ 𝔗 u; lines 49-58 are 8 forwarders restating each with hu : u ∈ t / hp : p ∈ t u. One-to-one by name. | verifier |
| 3 | verified | Read code/Carleson/Forest.lean lines 86-101: structure Row extends Forest X n (line 86), namespace Row re-declares @[simp] mem_𝔘 / mem_𝔗 (lines 97-98) and forwards pairwiseDisjoint' to pairwiseDisjoint (lines 100-101). | verifier |
| 4 | verified | Read code/Carleson/Forest.lean line 23: doc comment "The value of (𝔗 u) only matters when (u ∈ 𝔘)." annotates the 𝔗 field (line 24), matching the hu : u ∈ t hypothesis lifted by the forwarders. | verifier |
| 5 | verified | Read code/Carleson/Forest.lean lines 62-65: ball_subset_of_mem_𝓘 applies the forwarding lemma t.ball_subset hu hp on line 64 (via ball_subset_ball.trans), not the raw ball_subset field. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Read code/Carleson/Forest.lean: all 11 children (mem_mk, mem_𝔘, mem_𝔗, nonempty, ordConnected, 𝓘_ne_𝓘, smul_four_le, stackSize_le, dens₁_𝔗_le, lt_dist, ball_subset) match lines 43-58 verbatim, and each closed_by matches the code's proof term exactly (Iff.rfl/.rfl for the 3 simp lemmas; t.<field>' args for the 8 forwarders). Each forwarder closes: u ∈ t and t u are definitionally t.𝔘 and t.𝔗 via the CoeHead/Membership/CoeFun instances (lines 39-41), so the field applications typecheck. The parent block and 8 field forwarders correspond one-to-one to the 8 predicate fields at lines 25-33. File is built by the project's CI (push.yml). | reviewer-correctness |
| generality | accept | Move stated structurally (bundled structure + raw projections + predicate fields; coercions make u∈t / t u natural; recipe: coercions → one @[simp] per spelling difference → one forwarder per field), not tied to Forest n. avoid_when gives three concrete conditions (single-use = net cost; client needs projection form; coercions out of scope). Consequences honest and specific (11 lemmas at near-zero cost but must stay in sync; hypothesis re-binding needs mem_𝔘 first; @[simp] layer needs instances in scope). Minor imprecision on the exact outside-scope failure mode is not a generality defect. | reviewer-generality |
| provenance-licence | accept | Commit d75f54374f7f930e70a86b443f20d0e0935c275e is consistent across entry.json, sources/carleson/SOURCE.md and source.json; check_provenance.py reports the copied Carleson/Forest.lean (4670 bytes, sha256 f5539c8e...) byte-identical at that commit. Licence Apache-2.0 recorded in entry, source note and source.json, and sources/carleson/upstream-LICENSE is the Apache 2.0 text. Every permalink pins repo/commit/path with line ranges that match the copied file (sites 43-58, 19-33, 37-41; claim lines 23, 25-33, 49-58, 62-65, 86-101 all correct). Source note records attribution and licence provenance. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/fpvandoorn/carleson at commit `d75f54374f7f930e70a86b443f20d0e0935c275e`, under `Apache-2.0`; see the [source note](../../sources/carleson/SOURCE.md) for the licence text and attribution.
