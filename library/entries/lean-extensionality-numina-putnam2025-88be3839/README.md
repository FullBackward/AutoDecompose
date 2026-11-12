# Function extensionality for σ_invol (Putnam 2025 A3), split at the first nonzero coordinate

| | |
|---|---|
| Kind | instance |
| Move | extensionality |
| Language | lean |
| Status | accepted |
| Source | [numina-putnam2025](../../sources/numina-putnam2025/SOURCE.md) at `60d33c8ba19a` |
| Licence | `MIT` |

## Intent

Prove that the strategy map `σ` is an involution, `σ (σ x) = x`, by function
extensionality: `ext i` reduces the function equality to a pointwise equality
at an arbitrary coordinate, `by_cases` on `i = firstNonzero x hx` splits it
into the coordinate `σ` touches and all others, and each branch closes by `σ`'s
two pointwise rewrite lemmas together with the involution of `swap12`.

## The decomposition

### parent `σ_invol`: [`NuminaPutnam2025/putnam_2025_a3.lean` lines 95-110](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a3.lean#L95-L110) ([local copy](code/NuminaPutnam2025/putnam_2025_a3.lean))

```lean
lemma σ_invol {n : ℕ} (x : Fin n → Fin 3) (hx : x ≠ fun _ => 0) :
    σ (σ x hx) (σ_ne_zero x hx) = x := by
  ext i
  have hk_σ : firstNonzero (σ x hx) (σ_ne_zero x hx) = firstNonzero x hx := firstNonzero_σ x hx
  by_cases hi : i = firstNonzero x hx
  · subst hi
    have eq1 : (σ (σ x hx) (σ_ne_zero x hx)) (firstNonzero x hx) =
               swap12 ((σ x hx) (firstNonzero x hx)) := by
      conv_lhs => rw [σ, if_pos hk_σ.symm]
    have eq2 : (σ x hx) (firstNonzero x hx) = swap12 (x (firstNonzero x hx)) :=
      σ_at_firstNonzero x hx
    rw [eq1, eq2, swap12_invol]
  · have eq1 : (σ (σ x hx) (σ_ne_zero x hx)) i = (σ x hx) i := by
      conv_lhs => rw [σ, if_neg (by rwa [hk_σ])]
    have eq2 : (σ x hx) i = x i := σ_away_firstNonzero x hx i hi
    rw [eq1, eq2]
```

### child `at_firstNonzero`: [`NuminaPutnam2025/putnam_2025_a3.lean` lines 100-106](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a3.lean#L100-L106) ([local copy](code/NuminaPutnam2025/putnam_2025_a3.lean))

```lean
  · subst hi
    have eq1 : (σ (σ x hx) (σ_ne_zero x hx)) (firstNonzero x hx) =
               swap12 ((σ x hx) (firstNonzero x hx)) := by
      conv_lhs => rw [σ, if_pos hk_σ.symm]
    have eq2 : (σ x hx) (firstNonzero x hx) = swap12 (x (firstNonzero x hx)) :=
      σ_at_firstNonzero x hx
    rw [eq1, eq2, swap12_invol]
```

### child `away_firstNonzero`: [`NuminaPutnam2025/putnam_2025_a3.lean` lines 107-110](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a3.lean#L107-L110) ([local copy](code/NuminaPutnam2025/putnam_2025_a3.lean))

```lean
  · have eq1 : (σ (σ x hx) (σ_ne_zero x hx)) i = (σ x hx) i := by
      conv_lhs => rw [σ, if_neg (by rwa [hk_σ])]
    have eq2 : (σ x hx) i = x i := σ_away_firstNonzero x hx i hi
    rw [eq1, eq2]
```

### context `σ`: [`NuminaPutnam2025/putnam_2025_a3.lean` lines 56-57](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a3.lean#L56-L57) ([local copy](code/NuminaPutnam2025/putnam_2025_a3.lean))

```lean
def σ {n : ℕ} (x : Fin n → Fin 3) (hx : x ≠ fun _ => 0) : Fin n → Fin 3 := fun i =>
  if i = firstNonzero x hx then swap12 (x i) else x i
```

### context `firstNonzero`: [`NuminaPutnam2025/putnam_2025_a3.lean` lines 37-41](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a3.lean#L37-L41) ([local copy](code/NuminaPutnam2025/putnam_2025_a3.lean))

```lean
def firstNonzero {n : ℕ} (x : Fin n → Fin 3) (hx : x ≠ fun _ => 0) : Fin n :=
  Fin.find (fun i => x i ≠ 0) (by
    by_contra h
    push_neg at h
    exact hx (funext h))
```

### context `swap12`: [`NuminaPutnam2025/putnam_2025_a3.lean` lines 27-28](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a3.lean#L27-L28) ([local copy](code/NuminaPutnam2025/putnam_2025_a3.lean))

```lean
def swap12 (v : Fin 3) : Fin 3 :=
  if v = 0 then 0 else if v = 1 then 2 else 1
```

### context `swap12_invol`: [`NuminaPutnam2025/putnam_2025_a3.lean` lines 33-34](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a3.lean#L33-L34) ([local copy](code/NuminaPutnam2025/putnam_2025_a3.lean))

```lean
lemma swap12_invol (v : Fin 3) : swap12 (swap12 v) = v := by
  fin_cases v <;> simp [swap12]
```

### context `σ_at_firstNonzero`: [`NuminaPutnam2025/putnam_2025_a3.lean` lines 70-72](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a3.lean#L70-L72) ([local copy](code/NuminaPutnam2025/putnam_2025_a3.lean))

```lean
lemma σ_at_firstNonzero {n : ℕ} (x : Fin n → Fin 3) (hx : x ≠ fun _ => 0) :
    (σ x hx) (firstNonzero x hx) = swap12 (x (firstNonzero x hx)) := by
  simp only [σ, ite_true]
```

### context `σ_away_firstNonzero`: [`NuminaPutnam2025/putnam_2025_a3.lean` lines 74-76](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a3.lean#L74-L76) ([local copy](code/NuminaPutnam2025/putnam_2025_a3.lean))

```lean
lemma σ_away_firstNonzero {n : ℕ} (x : Fin n → Fin 3) (hx : x ≠ fun _ => 0)
    (j : Fin n) (hj : j ≠ firstNonzero x hx) : (σ x hx) j = x j := by
  simp only [σ, hj, ite_false]
```

### context `firstNonzero_σ`: [`NuminaPutnam2025/putnam_2025_a3.lean` lines 78-93](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a3.lean#L78-L93) ([local copy](code/NuminaPutnam2025/putnam_2025_a3.lean))

```lean
lemma firstNonzero_σ {n : ℕ} (x : Fin n → Fin 3) (hx : x ≠ fun _ => 0) :
    firstNonzero (σ x hx) (σ_ne_zero x hx) = firstNonzero x hx := by
  let k := firstNonzero x hx
  have hσk : (σ x hx) k ≠ 0 := by
    rw [σ_at_firstNonzero]
    exact swap12_ne_zero (firstNonzero_spec x hx)
  have hσj : ∀ j < k, (σ x hx) j = 0 := by
    intro j hj
    rw [σ_away_firstNonzero x hx j (ne_of_lt hj)]
    exact firstNonzero_min x hx j hj
  unfold firstNonzero
  rw [Fin.find_eq_iff]
  constructor
  · exact hσk
  · intro j hj
    simp [hσj j hj]
```

`σ` is the matching function for Putnam 2025 A3: it maps a nonzero vector
`x : Fin n → Fin 3` to the same vector with its first nonzero coordinate
swapped by `swap12` (which exchanges `1 ↔ 2`). `σ_invol` states that applying
`σ` twice returns `x`.

The proof is a pointwise extensionality argument. `ext i` (line 97) turns the
equality of functions `σ (σ x hx) (σ_ne_zero x hx) = x` into the goal at an
arbitrary coordinate `i`. The next line records the invariance
`hk_σ : firstNonzero (σ x hx) (σ_ne_zero x hx) = firstNonzero x hx` from
`firstNonzero_σ` — this is what makes the outer and inner `σ` unfold at the
same coordinate. Then `by_cases hi : i = firstNonzero x hx` (line 99) produces
the two children:

- child `at_firstNonzero` (lines 100-106): when `i = firstNonzero x hx`, the
  outer `σ` unfolds via `conv_lhs => rw [σ, if_pos hk_σ.symm]` (eq1) and the
  inner `σ` via `σ_at_firstNonzero` (eq2); the goal becomes
  `swap12 (swap12 (x k)) = x k`, closed by `swap12_invol`.
- child `away_firstNonzero` (lines 107-110): when `i ≠ firstNonzero x hx`, the
  outer `σ` unfolds via `conv_lhs => rw [σ, if_neg (by rwa [hk_σ])]` (eq1) and
  the inner `σ` via `σ_away_firstNonzero` (eq2); the goal becomes `x i = x i`,
  closed by `rw [eq1, eq2]`.

The three helper lemmas `σ_at_firstNonzero`, `σ_away_firstNonzero` and
`firstNonzero_σ` are all stated and proved before `σ_invol`, each by a short
`simp`/`rw` argument; `σ_invol` merely wires them together. `σ_ne_zero` (the
second argument of `σ` in the statement) supplies the proof that `σ x hx` is
still nonzero, which `σ` needs as a precondition.

## Why it is good

1. *check* — The parent `σ_invol` is closed by its two children: `ext i` turns
   the function equality into a pointwise goal, `by_cases` yields the two
   branches, and each branch closes with a single `rw` (line 106
   `rw [eq1, eq2, swap12_invol]`; line 110 `rw [eq1, eq2]`), leaving no
   remaining goals ([lines 95-110](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a3.lean#L95-L110)).
2. *check* — The copied file contains no `sorry`, `axiom`, `admit` or
   `Admitted`, and the project's CI builds it: `.github/workflows/lean_action_ci.yml`
   runs `leanprover/lean-action@v1` on push/PR, and `NuminaPutnam2025.lean`
   imports `NuminaPutnam2025.putnam_2025_a3` ([workflow](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/.github/workflows/lean_action_ci.yml), [import](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025.lean#L3)).
3. *author-statement* — The authors name the fact the split relies on:
   "Key insight: σ only modifies the first nonzero position" (comment above
   `σ_inj`, [lines 118-120](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a3.lean#L118-L120)).
4. *known-use* — `σ_invol` is reused later in the same file to prove
   injectivity: `have h1 := σ_invol x hx` and `have h2 := σ_invol y hy`
   ([lines 127-128](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a3.lean#L127-L128)),
   and again `rw [key, σ_invol]` at [line 560](https://github.com/project-numina/Numina-Putnam2025/blob/60d33c8ba19af905bd731e938ebde1c5b8c76519/NuminaPutnam2025/putnam_2025_a3.lean#L560).
5. *measurement* — `σ_invol` is 16 lines total (95-110); the extensionality
   step `ext i` and the split `by_cases` are 2 lines (97, 99), and each branch
   is closed by one `rw` (106, 110); the two rewrite lemmas `σ_at_firstNonzero`
   and `σ_away_firstNonzero` are one-line proofs (72, 76).

In my opinion the detail worth copying is the one-line invariance `hk_σ` (from
`firstNonzero_σ`): it is the fact that lets a pointwise extensionality split
line up the outer and inner occurrences of `σ`, and it is stated as a separate
lemma before the proof that needs it.

## When to use it, and when not

Use extensionality when the goal is an equality between functions (or
finsets/sets) and the two sides differ pointwise in a way you can argue at an
arbitrary coordinate. It is especially clean when the function is defined by a
single `if` on "is this the special coordinate", because `by_cases` on that
test gives exactly two regions, each closed by the function's own definitional
rewrite. The special coordinate must be preserved by the map, so state that
preservation as its own lemma (here `firstNonzero_σ`) before the proof that
needs it. Avoid it when the functions are not definitionally equal pointwise
and each coordinate needs a different argument, when the "special coordinate"
is not invariant under the map (the case split will not typecheck), or when the
equality is between structured data rather than functions, where a plain `ext`
does not reduce the goal.

## Consequences

`ext i` turns one function-equality goal into a pointwise goal parameterised by
an arbitrary `i`, so every later step must work uniformly in `i` (or be
preceded by a split on `i`). The `by_cases` split creates two children plus an
obligation that the case test is decidable; here it is `i = firstNonzero x hx`,
decidable because `Fin n` has decidable equality. Each branch must unfold `σ`
itself (`conv_lhs => rw [σ, if_pos/if_neg]`), and that only works because
`hk_σ` makes the outer `σ`'s branch condition (`i = firstNonzero (σ x hx)`)
equivalent to the inner one; without `firstNonzero_σ` the two `σ` would unfold
at different coordinates and the branches would not close.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/lean_action_ci.yml (leanprover/lean-action@v1 on push/PR); commit 60d33c8ba19af905bd731e938ebde1c5b8c76519 is HEAD of default branch main; NuminaPutnam2025.lean imports NuminaPutnam2025.putnam_2025_a3 | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 1 file(s) byte-identical at 60d33c8ba19af905bd731e938ebde1c5b8c76519 | check_provenance.py | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | read copied code lines 95-110: ext i (97), by_cases hi (99), branch closes rw [eq1, eq2, swap12_invol] (106) and rw [eq1, eq2] (110), lemma ends at 110 with next lemma at 113 | verifier |
| 2 | verified | grep -nEi 'sorry|admit|\baxiom\b|Admitted' on copied file: no match; fetched .github/workflows/lean_action_ci.yml (leanprover/lean-action@v1 on push/PR); NuminaPutnam2025.lean line 3 imports putnam_2025_a3 | verifier |
| 3 | verified | read copied code lines 118-120: line 119 comment '-- Key insight: σ only modifies the first nonzero position' above σ_inj (121) | verifier |
| 4 | verified | read copied code: lines 127-128 'have h1 := σ_invol x hx'/'have h2 := σ_invol y hy'; line 560 'rw [key, σ_invol]' | verifier |
| 5 | verified | read copied code: σ_invol lines 95-110 (16 lines); ext i at 97, by_cases at 99; one-line proofs at 72 (σ_at_firstNonzero) and 76 (σ_away_firstNonzero); branches close at 106 and 110 | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Read copied code/NuminaPutnam2025/putnam_2025_a3.lean: parent sigma_invol at 95-110 matches entry.json statement; ext i (97), hk_sigma from firstNonzero_sigma (98), by_cases hi (99); child at_firstNonzero (100-106) closes with rw [eq1, eq2, swap12_invol] (106); child away_firstNonzero (107-110) closes with rw [eq1, eq2] (110); lemma ends at 110 with next lemma at 113, no sorry/axiom in file. Context lemmas (swap12 27-28, swap12_invol 33-34, firstNonzero 37-41, sigma 56-57, sigma_at_firstNonzero 70-72, sigma_away_firstNonzero 74-76, firstNonzero_sigma 78-93) all match their stated line ranges. Decomposition is as described and closes. | reviewer-correctness |
| generality | accept | Move is generalized beyond the example: applicability.goal_shape/use_when/avoid_when abstract to 'an equality of functions f = g where f is defined pointwise by an if i = p then … else …' over 'a single canonical point p', and the README use/avoid section states the clean case (single if -> two regions) without claiming it is the only case. 'When not to use' and consequences are honest and specific: three concrete failure modes (no pointwise uniformity; canonical point not invariant under the map; equality between structured data), plus the decidable-if obligation and the mechanism hk_σ aligning outer/inner σ unfoldings. Minor non-blocking nit: 'the case split will not typecheck' in use/avoid overstates the failure — by_cases always typechecks (decidable equality on Fin n); without firstNonzero_σ what fails is that the if_pos/if_neg rewrites do not fire and the branches do not close, which the entry's own Consequences section states correctly ('the branches would not close'). | reviewer-generality |
| provenance-licence | accept | check_provenance passes (1 file byte-identical at 60d33c8ba19af905bd731e938ebde1c5b8c76519); copied file is 27101 bytes with sha256 d7315cd9775c55a0297adf1ce384b1ea57fb7b9c22e4ad6860dfa402ad8dddff, matching entry.json. Commit 60d33c8ba19af905bd731e938ebde1c5b8c76519 is consistent across entry.json, sources/numina-putnam2025/source.json, SOURCE.md and the entry README. Licence MIT is recorded consistently in entry.json (source.licence), source.json, SOURCE.md and the entry README, and sources/numina-putnam2025/upstream-LICENSE carries the full MIT text (Copyright 2025 Numina). All site/context permalinks use the same repo (project-numina/Numina-Putnam2025), pinned commit and path, and the local lines 95-110 match the parent excerpt. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/project-numina/Numina-Putnam2025 at commit `60d33c8ba19af905bd731e938ebde1c5b8c76519`, under `MIT`; see the [source note](../../sources/numina-putnam2025/SOURCE.md) for the licence text and attribution.
