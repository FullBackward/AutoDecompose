# Eventual periodicity assembled from a stabilisation invariant and a modulus (IMO 2026 Q6)

| | |
|---|---|
| Kind | instance |
| Move | other |
| Language | lean |
| Status | draft |
| Source | [axiom-imo2026](../../sources/axiom-imo2026/SOURCE.md) at `c5a6a089d06d` |
| Licence | `MIT` |
| Licence recorded | 2026-11-14T09:32:31Z |

## Intent

Prove the eventual periodicity of any valid sequence by lifting the
number-theoretic heart — goodness stabilisation — into a threshold `N`, then
feeding that threshold and a prefix-product modulus `M = prefixMod a N` to a
"from stable" transformer lemma that manufactures the period `T` and shift `L`.
The 6-line glue does no arithmetic of its own: it only obtains the invariant
and instantiates the transformer.

## The decomposition

### parent `eventual_periodicity`: [`IMO2026/Q6/solution.lean` lines 752-757](https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q6/solution.lean#L752-L757) ([local copy](code/IMO2026/Q6/solution.lean))

```lean
theorem eventual_periodicity (a : ℕ → ℕ) (ha : IsValidSeq a) :
    ∃ N T L : ℕ, 0 < T ∧ 0 < L ∧ ∀ n, N ≤ n → a (n + T) = a n + L := by
  obtain ⟨N, hstab⟩ := good_stabilizes_core a ha
  obtain ⟨N', T, L, hT, hL, _hML, hper⟩ :=
    eventual_periodicity_from_stable a ha (prefixMod_pos ha N) hstab (prefixMod_absorbs N)
  exact ⟨N', T, L, hT, hL, hper⟩
```

### child `good_stabilizes_core`: [`IMO2026/Q6/solution.lean` lines 527-550](https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q6/solution.lean#L527-L550) ([local copy](code/IMO2026/Q6/solution.lean))

```lean
theorem good_stabilizes_core (a : ℕ → ℕ) (ha : IsValidSeq a) :
    ∃ N, ∀ n, N ≤ n → ∀ b, Good a n b ↔ Good a N b := by
  obtain ⟨N, hcov⟩ := ssupp_cover a
  refine ⟨N, ?_⟩
  intro n hn b
  constructor
  · -- (→) monotone: constraints of Good a N are a subset of those of Good a n.
    intro h i hi
    exact h i (le_trans hi hn)
  · -- (←) the content: Good a N b → Good a n b.
    intro h j hj
    -- get a matching prefix index i ≤ N with the same small support
    obtain ⟨i, hiN, hss⟩ := hcov j
    -- b good for prefix N shares a small prime with a i
    obtain ⟨p, hp, hple, hpb, hpai⟩ := good_small_witness ha h i hiN
    -- p ∈ ssupp a i = ssupp a j ⇒ p ∣ a j
    have hai0 : a i ≠ 0 := by have := ha.1 i; omega
    have haj0 : a j ≠ 0 := by have := ha.1 j; omega
    have hpi : p ∈ ssupp a i := (mem_ssupp hai0).mpr ⟨hple, hp, hpai⟩
    have hpj : p ∈ ssupp a j := hss ▸ hpi
    have hpaj : p ∣ a j := ((mem_ssupp haj0).mp hpj).2.2
    -- conclude 1 < gcd b (a j)
    have hajpos : 0 < a j := by have := ha.1 j; omega
    exact (one_lt_gcd_iff_exists_prime_dvd hajpos).mpr ⟨p, hp, hpb, hpaj⟩
```

### child `eventual_periodicity_from_stable`: [`IMO2026/Q6/solution.lean` lines 552-670](https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q6/solution.lean#L552-L670) ([local copy](code/IMO2026/Q6/solution.lean))

```lean
theorem eventual_periodicity_from_stable (a : ℕ → ℕ) (ha : IsValidSeq a)
    {N M : ℕ} (hMpos : 0 < M)
    (hstab : ∀ n, N ≤ n → ∀ b, Good a n b ↔ Good a N b)
    (hM : ∀ i ≤ N, ∀ p, Nat.Prime p → p ∣ a i → p ∣ M) :
    ∃ N' T L : ℕ, 0 < T ∧ 0 < L ∧ M ∣ L ∧
      ∀ n, N' ≤ n → a (n + T) = a n + L := by
  have hgreedy : ∀ n, N ≤ n →
      a n < a (n + 1) ∧ Good a N (a (n + 1)) ∧
        (∀ b, a n < b → b < a (n + 1) → ¬ Good a N b) := by
    intro n hn
    obtain ⟨hlt, hgood, hmin⟩ := ha.succ_least_good n
    refine ⟨hlt, (hstab n hn (a (n + 1))).mp hgood, ?_⟩
    intro b hb1 hb2 hgb
    exact hmin b hb1 hb2 ((hstab n hn b).mpr hgb)
  -- Pigeonhole on residues mod M over the M+1 indices in [N, N+M].
  have hmaps : Set.MapsTo (fun n => a n % M) ↑(Finset.Icc N (N + M)) ↑(Finset.range M) := by
    intro n _
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.mod_lt _ hMpos
  have hcard : (Finset.range M).card < (Finset.Icc N (N + M)).card := by
    rw [Finset.card_range, Nat.card_Icc]
    omega
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  simp only [Finset.mem_Icc] at hx hy
  -- Order the two indices: u < v.
  wlog hlt : x < y generalizing x y
  · exact this y x (Ne.symm hxy) hfxy.symm hy hx (by omega)
  set u := x with hu
  set v := y with hv
  have hNu : N ≤ u := hx.1
  have huv : u < v := hlt
  -- The period and translation length.
  refine ⟨u, v - u, a v - a u, by omega, ?_, ?_, ?_⟩
  · -- 0 < a v - a u  (strict monotonicity)
    have : a u < a v := ha.strictMono huv
    omega
  · -- M ∣ (a v - a u)  from equal residues
    have hle : a u ≤ a v := le_of_lt (ha.strictMono huv)
    have hmod : a u ≡ a v [MOD M] := hfxy
    exact (Nat.modEq_iff_dvd' hle).mp hmod
  · -- the periodicity: ∀ n ≥ u, a (n + (v-u)) = a n + (a v - a u)
    -- Abbreviations
    set T := v - u with hTdef
    set L := a v - a u with hLdef
    have hML : M ∣ L := by
      have hle : a u ≤ a v := le_of_lt (ha.strictMono huv)
      have hmod : a u ≡ a v [MOD M] := hfxy
      exact (Nat.modEq_iff_dvd' hle).mp hmod
    have hTpos : 0 < T := by omega
    -- Translation invariance of `Good a N` by +L.
    have hperN : ∀ b, Good a N (b + L) ↔ Good a N b :=
      Good_periodic_of_modulus ha hML hM
    -- Induction from u upward.  Claim Q n : a (n + T) = a n + L for n ≥ u.
    have hLval : a v = a u + L := by
      have hle : a u ≤ a v := le_of_lt (ha.strictMono huv)
      omega
    have key : ∀ d, a (u + d + T) = a (u + d) + L := by
      intro d
      induction d with
      | zero =>
        -- a (u + T) = a v = a u + L
        have hvu : u + T = v := by omega
        simpa [hvu] using hLval
      | succ e ih =>
        -- from Q(u+e) derive Q(u+e+1)
        set n := u + e with hn
        have hnN : N ≤ n := by omega
        -- greedy at n and at n+T (both ≥ N)
        obtain ⟨hlt1, hgood1, hmin1⟩ := hgreedy n hnN
        obtain ⟨hlt2, hgood2, hmin2⟩ := hgreedy (n + T) (by omega)
        -- ih : a (n + T) = a n + L
        have hnT : a (n + T) = a n + L := by simpa [hn] using ih
        -- a (n+1) + L is Good a N and > a n + L = a(n+T)
        have hgoodShift : Good a N (a (n + 1) + L) := (hperN (a (n + 1))).mpr hgood1
        have hgt : a (n + T) < a (n + 1) + L := by
          rw [hnT]; have := hlt1; omega
        -- No good strictly between a(n+T) and a(n+1)+L
        have hbetween : ∀ b, a (n + T) < b → b < a (n + 1) + L → ¬ Good a N b := by
          intro b hb1 hb2 hgb
          -- shift down by L: a n < b - L < a (n+1), Good a N (b-L)
          have hbL : L ≤ b := by rw [hnT] at hb1; omega
          have hbeq : b - L + L = b := by omega
          have hgbL : Good a N (b - L) := by
            have := (hperN (b - L)).mpr
            rw [hbeq] at this
            -- this : Good a N b → Good a N (b - L)? No: (hperN (b-L)).mp : Good a N ((b-L)+L) ↔..
            exact (hbeq ▸ (hperN (b - L))).mp hgb
          have hlb : a n < b - L := by rw [hnT] at hb1; omega
          have hub : b - L < a (n + 1) := by omega
          exact hmin1 (b - L) hlb hub hgbL
        -- a (n+T+1) is the least good above a(n+T); compare with a(n+1)+L
        -- n + 1 + T = n + T + 1
        have hidx : n + 1 + T = n + T + 1 := by ring
        -- greedy2 gives: a(n+T) < a(n+T+1), Good a N (a(n+T+1)), min
        -- Show a (n + T + 1) = a (n+1) + L by antisymmetry.
        have hle1 : a (n + T + 1) ≤ a (n + 1) + L := by
          by_contra hc
          push_neg at hc
          -- a(n+1)+L strictly between a(n+T) and a(n+T+1), and it's good ⇒ contra with hmin2
          exact hmin2 (a (n + 1) + L) hgt hc hgoodShift
        have hle2 : a (n + 1) + L ≤ a (n + T + 1) := by
          by_contra hc
          push_neg at hc
          -- a(n+T+1) strictly between a(n+T) and a(n+1)+L, good ⇒ contra hbetween
          exact hbetween (a (n + T + 1)) hlt2 hc hgood2
        have : a (n + T + 1) = a (n + 1) + L := le_antisymm hle1 hle2
        -- conclude Q(u+e+1)
        have : a (u + e + 1 + T) = a (u + e + 1) + L := by
          have h1 : u + e + 1 + T = n + T + 1 := by rw [hn]; ring
          have h2 : u + e + 1 = n + 1 := by rw [hn]
          rw [h1, h2]; exact this
        exact this
    -- Rewrite: for n ≥ u, n = u + (n - u)
    intro n hn
    have hd := key (n - u)
    have heq : u + (n - u) = n := by omega
    rw [heq] at hd
    exact hd
```

### child `prefixMod_pos`: [`IMO2026/Q6/solution.lean` lines 115-119](https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q6/solution.lean#L115-L119) ([local copy](code/IMO2026/Q6/solution.lean))

```lean
lemma prefixMod_pos {a : ℕ → ℕ} (ha : IsValidSeq a) (N : ℕ) : 0 < prefixMod a N := by
  unfold prefixMod
  apply Finset.prod_pos
  intro i _
  have := ha.1 i; omega
```

### child `prefixMod_absorbs`: [`IMO2026/Q6/solution.lean` lines 122-125](https://github.com/AxiomMath/IMO2026/blob/c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2/IMO2026/Q6/solution.lean#L122-L125) ([local copy](code/IMO2026/Q6/solution.lean))

```lean
lemma prefixMod_absorbs {a : ℕ → ℕ} (N : ℕ) :
    ∀ i ≤ N, ∀ p, Nat.Prime p → p ∣ a i → p ∣ prefixMod a N := by
  intro i hi p hp hpa
  exact prime_dvd_prefixMod hi hp hpa
```

How the parts fit. The parent `eventual_periodicity` is the main theorem and its
three-line body is the glue. It runs in two steps and a re-pack:

1. `obtain ⟨N, hstab⟩ := good_stabilizes_core a ha` — get the threshold `N` and
   the stabilisation fact `hstab : ∀ n, N ≤ n → ∀ b, Good a n b ↔ Good a N b`.
2. `obtain ⟨N', T, L, hT, hL, _hML, hper⟩ := eventual_periodicity_from_stable a ha
   (prefixMod_pos ha N) hstab (prefixMod_absorbs N)` — instantiate the
   transformer with the modulus positivity (`prefixMod_pos`), the stabilisation
   (`hstab`) and the modulus absorption (`prefixMod_absorbs`).
3. `exact ⟨N', T, L, hT, hL, hper⟩` — drop the unused `M ∣ L` hypothesis and
   return the witness.

The lemma graph (direct children in bold; the chain used for `shape.depth`
indented):

```
eventual_periodicity
├── good_stabilizes_core                     (the stabilisation invariant)
├── eventual_periodicity_from_stable         (the transformer: stable ⇒ periodic)
│     └── Good_periodic_of_modulus           (Good a N is invariant under +L)
│           └── gcd_constraint_periodic      (gcd constraint invariant under +L)
│                 └── one_lt_gcd_iff_exists_prime_dvd   (leaf: Mathlib only)
├── prefixMod_pos                            (the modulus is positive)
└── prefixMod_absorbs                        (the modulus absorbs prefix primes)
      └── prime_dvd_prefixMod                (leaf)
```

Why each direct child is a good leaf — a self-contained statement whose proof
closes on its own, or from named siblings earlier in the file:

- `good_stabilizes_core` (lines 527-550) states "there is a threshold past
  which goodness no longer changes", the number-theoretic heart. Its proof
  closes on its own: the (→) direction is the monotonicity of `Good`, the (←)
  direction combines `ssupp_cover`, `good_small_witness` and `mem_ssupp` and
  ends in `one_lt_gcd_iff_exists_prime_dvd`. The glue cites only its statement,
  never its proof.
- `eventual_periodicity_from_stable` (lines 552-670) is the transformer,
  parameterised by `hstab` rather than by a concrete sequence: from a modulus
  `M` with `M ∣ L`, stabilisation and absorption it produces the period. Its
  proof closes on its own — a pigeonhole on residues mod `M` then an induction
  whose step closes by `le_antisymm` of two greedy-minimality bounds, using
  `Good_periodic_of_modulus` for translation invariance. Being parameterised is
  what lets the glue be one line.
- `prefixMod_pos` (lines 115-119) supplies `0 < M`, closing by
  `Finset.prod_pos` and `omega`.
- `prefixMod_absorbs` (lines 122-125) supplies `M` absorbs every prime of the
  prefix, closing by `exact prime_dvd_prefixMod hi hp hpa`.

The chain I checked for `shape.depth` (4) is
`eventual_periodicity → eventual_periodicity_from_stable →
Good_periodic_of_modulus → gcd_constraint_periodic →
one_lt_gcd_iff_exists_prime_dvd`: each link is a citation in the file (lines
604, 135/137, 62), and `one_lt_gcd_iff_exists_prime_dvd` is a leaf that uses
only Mathlib. There is a second, at least as deep, branch through
`good_stabilizes_core → good_small_witness → term_has_small_subsupport →
large_prime_not_min_support → good_in_range_is_term`; I did not chase it to its
leaves, so I report the chain I verified.

## Why it is good

1. The parent site (the glue) is 6 lines long (lines 752-757) — `check`,
   form `lines(parent, 6)`.
2. No `sorry`/`admit`/`axiom` token appears in the parent site — `check`,
   form `no_sorry(IMO2026/Q6/solution.lean, 752-757)`.
3. The parent site cites `good_stabilizes_core` — `check`,
   form `cites(parent, good_stabilizes_core)`.
4. The proof assembles its conclusion from 4 named lemmas —
   `good_stabilizes_core`, `eventual_periodicity_from_stable`, `prefixMod_pos`,
   `prefixMod_absorbs` — with no arithmetic between them (the body is two
   `obtain` lines and a final `exact`; lines 752-757) — `measurement`.
5. The authors label the theorem "Eventual periodicity (number-theoretic core)"
   and restate its goal in the doc comment immediately above it (lines 749-751)
   — `author-statement`.

The same assembly is reused a few lines later by `main_theorem` (lines 762-771),
which re-cites `good_stabilizes_core` and `eventual_periodicity_from_stable` and
adds `pure_periodicity_from_stable` to drop the threshold. That is the
memoised-canonical-statement pattern: the invariant and the transformer are
computed once and reused across two theorems (survey F §10 rule 17).

In my opinion the detail worth copying is the *parameterised* transformer:
`eventual_periodicity_from_stable` is stated over an arbitrary `hstab`, so the
glue's only job is to supply the one concrete invariant the file proved, and the
arithmetic that used to sit in the parent lives entirely inside the children.

## When to use it, and when not

Use it when a goal of the shape `∃ N T L, 0 < T ∧ 0 < L ∧ ∀ n, N ≤ n →
a (n + T) = a n + L` (eventual periodicity, or any "from some point on the
behaviour is rigid" conclusion) factors cleanly into three pieces: a
stabilising/limiting invariant, a modulus that absorbs the finitely many
relevant objects, and a transformer that is parameterised by the invariant
rather than by a concrete instance. Each piece is then a self-contained lemma
and the glue is pure assembly.

Avoid it when the invariant does not actually stabilise (then the hard content
is inside the invariant, and the "from stable" step is vacuous); when the
transformer cannot be stated over an arbitrary invariant and must be re-proved
per instance; or when there is no finite modulus that absorbs the prefix primes
— the `prefixMod_absorbs` / `prefixMod_pos` pair only exists because the primes
below a threshold are finite.

## Consequences

The move splits one theorem into a stabilisation invariant, two modulus facts,
and a "from stable" transformer, leaving the glue with no arithmetic.
Obligations it creates: the invariant must genuinely stabilise
(`good_stabilizes_core` is the hard part); the modulus must absorb every prime
the prefix cares about (`prefixMod_absorbs`); and the transformer must be
parameterised by the invariant, not by a concrete instance. Failure modes: if
the stabilisation threshold and the modulus entangle, the transformer and the
invariant leak into each other; if the transformer needs a different invariant
than the one proved, the glue must redo the wiring instead of just instantiating.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | not-run | No CI workflow in the source repository at the pinned commit c5a6a089: the repo root has no .github directory (top-level contents are IMO2026/, LICENSE, README.md, lakefile.lean, lake-manifest.json, lean-toolchain, verify.py, formalization.yaml), so no GitHub Actions workflow builds IMO2026/Q6/solution.lean on the default branch main. | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: good_stabilizes_core@IMO2026/Q6/solution.lean:754, eventual_periodicity_from_stable@IMO2026/Q6/solution.lean:756, prefixMod_pos@IMO2026/Q6/solution.lean:756, prefixMod_absorbs@IMO2026/Q6/solution.lean:756; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(parent, 6) -> lines: site parent has 6 lines | check_claims.py |
| 2 | verified | no_sorry(IMO2026/Q6/solution.lean, 752-757) -> no_sorry: none of sorry, admit, axiom in IMO2026/Q6/solution.lean:752-757 | check_claims.py |
| 3 | verified | cites(parent, good_stabilizes_core) -> cites: good_stabilizes_core occurs at IMO2026/Q6/solution.lean:754 | check_claims.py |
| 4 | verified | Read code/IMO2026/Q6/solution.lean L752-756: the body is obtain <N,hstab> := good_stabilizes_core a ha; obtain <N',T,L,hT,hL,_hML,hper> := eventual_periodicity_from_stable a ha (prefixMod_pos ha N) hstab (prefixMod_absorbs N); exact <N',T,L,hT,hL,hper>. Two obtain lines and one exact, citing all four named lemmas, no arithmetic between them. | verifier |
| 5 | verified | Read code/IMO2026/Q6/solution.lean: doc comment (L748-750) immediately above the theorem (L751) is '/-- **Eventual periodicity (number-theoretic core).** There exist a threshold N and positive integers T, L such that the difference sequence is periodic beyond N: a (n + T) = a n + L for all n >= N. -/'. Note the label is on line 748, one line above the cited L749-L751 range. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent eventual_periodicity (752-757) is exactly the 3-line glue shown: obtain good_stabilizes_core, obtain eventual_periodicity_from_stable applied to (prefixMod_pos, hstab, prefixMod_absorbs), then exact; it cites exactly the 4 declared children and no others, and the final exact matches the parent statement, so it closes. Statements in entry.json match the code verbatim at 752-757, 527-550, 552-670, 115-119, 122-125. Closing methods match: good_stabilizes_core closes by constructor then one_lt_gcd_iff_exists_prime_dvd (550); eventual_periodicity_from_stable by Finset.exists_ne_map_eq_of_card_lt_of_maps_to pigeonhole then induction d closing by le_antisymm hle1 hle2; prefixMod_pos by unfold/apply Finset.prod_pos/omega; prefixMod_absorbs by exact prime_dvd_prefixMod. Shape numbers verified: direct_lemmas=4, glue_lines=6 (752-757), child_lines=[24,119,5,4] (527-550, 552-670, 115-119, 122-125), depth=4 via chain eventual_periodicity->eventual_periodicity_from_stable->Good_periodic_of_modulus(604)->gcd_constraint_periodic(135/137)->one_lt_gcd_iff_exists_prime_dvd(62), a Mathlib-only leaf; README honestly flags the un-chased second branch. No sorry/admit/axiom in any site. | reviewer-correctness |
| generality | accept | Move generalises beyond the example: use_when/avoid_when abstract to a three-piece assembly (stabilising invariant + finite modulus absorbing the finitely many relevant objects + transformer parameterised by the invariant), with goal shape generalised to 'from some point on the behaviour is rigid'; reuse is shown by main_theorem (lines 762-771) re-citing the same four lemmas. When-not-to-use is honest and specific (invariant fails to stabilise -> hard content stays inside it; transformer not parameterisable -> re-proved per instance; no finite modulus -> prefixMod pair unavailable). Consequences name real obligations and failure modes (threshold/modulus entanglement, invariant/transformer wiring mismatch). Leaf quality for a bounded prover is stated: self-contained statements closing on their own or from named siblings, glue cites statement only never proof, transformer parameterised by invariant. | reviewer-generality |
| provenance-licence | accept | check_provenance.py passes (1 file byte-identical at c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2). Commit is consistent across source.json, SOURCE.md, entry.json and every permalink (all c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2, pinned 2026-11-12T10:23:51Z). Licence MIT is recorded identically in entry.json, README.md, SOURCE.md, source.json and the copied upstream-LICENSE (MIT text, copyright Axiom Math). Copied code/ contains only IMO2026/Q6/solution.lean, matching entry.json files; sed confirms cited lines 749-757 (doc comment + eventual_periodicity) match the README excerpt. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/AxiomMath/IMO2026 at commit `c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2`, under `MIT`; see the [source note](../../sources/axiom-imo2026/SOURCE.md) for the licence text and attribution.
