# Three-stage lemma pipeline for IMO 2026 Q6 (purely periodic consecutive differences)

| | |
|---|---|
| Kind | instance |
| Move | other |
| Language | lean |
| Status | draft |
| Source | [dirac-imo2026](../../sources/dirac-imo2026/SOURCE.md) at `372592370162` |
| Licence | `MIT` |
| Licence recorded | 2026-11-14T09:37:47Z |

## Intent

Prove the headline theorem of IMO 2026 Q6 — that a valid sequence's
consecutive differences are purely periodic — by composing three independently
stated lemmas, each taking the previous one's conclusion as an explicit
hypothesis: prime supports stabilise, the admissible set becomes
shift-invariant, and shift invariance upgrades to pure periodicity. The glue is
a single nested application, one lemma per stage.

## The decomposition

### parent `main_theorem`: [`IMO2026/Q6/solution.lean` lines 700-705](https://github.com/Boundless-Intuition/IMO2026/blob/37259237016275044e3905e8d537efd0eead74d2/IMO2026/Q6/solution.lean#L700-L705) ([local copy](code/IMO2026/Q6/solution.lean))

```lean
/-- For any sequence satisfying Definition 1, there exist positive integers `T` and `L` such that
`a (n + T) = a n + L` for every `n`. Equivalently, the sequence of consecutive differences is
purely periodic. -/
theorem main_theorem (a : ℕ → ℕ) (ha : IsValidSeq a) :
    ∃ T L : ℕ, 0 < T ∧ 0 < L ∧ ∀ n, a (n + T) = a n + L := by
  exact main_of_period a ha (exists_period a ha (exists_stable a ha))
```

### child `exists_stable`: [`IMO2026/Q6/solution.lean` lines 599-610](https://github.com/Boundless-Intuition/IMO2026/blob/37259237016275044e3905e8d537efd0eead74d2/IMO2026/Q6/solution.lean#L599-L610) ([local copy](code/IMO2026/Q6/solution.lean))

```lean
theorem exists_stable (a : ℕ → ℕ) (ha : IsValidSeq a) :
    ∃ N, ∀ n, ∃ i ≤ N, (a i).primeFactors ⊆ (a n).primeFactors := by
  /- discharge the three hypotheses of `exists_stable_of` from the auxiliary lemmas -/
  have hkill : ∀ b, a 0 < b → ¬ Adm a b → ∃ i, a i < b ∧ Nat.gcd b (a i) = 1 :=
    fun b hb hn => killed_early a ha b hb hn
  have hminsub : ∀ n, ∃ S, IsMinMem a S ∧ S ⊆ PS a n := exists_minMem_subset a ha
  have hreal : ∀ X : Finset ℕ, X.Nonempty → (∀ p ∈ X, Nat.Prime p) → Trans a X →
      ∃ n, PS a n = X ∧ a n ≤ a 0 * ∏ p ∈ X, p :=
    fun X hne hp hT => trans_realized a ha X hne hp hT
  have hbound : ∀ S, IsMinMem a S → ∀ q ∈ S, q < (a 0) ^ 2 :=
    fun S hS q hq => prime_bound a ha hkill hminsub hreal S hS q hq
  exact exists_stable_of a ha hbound hreal hminsub
```

### child `exists_period`: [`IMO2026/Q6/solution.lean` lines 614-655](https://github.com/Boundless-Intuition/IMO2026/blob/37259237016275044e3905e8d537efd0eead74d2/IMO2026/Q6/solution.lean#L614-L655) ([local copy](code/IMO2026/Q6/solution.lean))

```lean
theorem exists_period (a : ℕ → ℕ) (ha : IsValidSeq a)
    (hstab : ∃ N, ∀ n, ∃ i ≤ N, (a i).primeFactors ⊆ (a n).primeFactors) :
    ∃ L, 0 < L ∧ ∀ b, (Adm a b ↔ Adm a (b + L)) := by
  obtain ⟨N, hN⟩ := hstab
  have hpos : ∀ i, 0 < a i := fun i => lt_trans Nat.one_pos (ha.1 i)
  have hne : ∀ i, a i ≠ 0 := fun i => (hpos i).ne'
  /- Bridge between `1 < Nat.gcd x y` and a common prime divisor. -/
  have key : ∀ x y : ℕ, y ≠ 0 → (1 < Nat.gcd x y ↔ ∃ p, Nat.Prime p ∧ p ∣ x ∧ p ∣ y) := by
    intro x y hy
    constructor
    · intro h
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := Nat.gcd x y) (by omega)
      exact ⟨p, hp, hpd.trans (Nat.gcd_dvd_left x y), hpd.trans (Nat.gcd_dvd_right x y)⟩
    · rintro ⟨p, hp, hpx, hpy⟩
      have hg : p ∣ Nat.gcd x y := Nat.dvd_gcd hpx hpy
      have hgne : Nat.gcd x y ≠ 0 := fun h => hy (Nat.eq_zero_of_gcd_eq_zero_right h)
      have h2 := hp.two_le
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hgne) hg
      omega
  refine ⟨∏ i ∈ Finset.range (N + 1), a i, ?_, ?_⟩
  · exact Finset.prod_pos fun i _ => hpos i
  /- (★): every `a i` with `i ≤ N` divides `L`. -/
  have hdvdL : ∀ i ≤ N, a i ∣ ∏ j ∈ Finset.range (N + 1), a j := by
    intro i hi
    exact Finset.dvd_prod_of_mem a (Finset.mem_range.mpr (by omega))
  intro b
  constructor
  · intro hb j
    obtain ⟨i, hiN, hsub⟩ := hN j
    obtain ⟨p, hp, hpb, hpai⟩ := (key b (a i) (hne i)).mp (hb i)
    have hmem : p ∈ (a i).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpai, hne i⟩
    have hpaj : p ∣ a j := (Nat.mem_primeFactors.mp (hsub hmem)).2.1
    have hpL : p ∣ ∏ j ∈ Finset.range (N + 1), a j := hpai.trans (hdvdL i hiN)
    exact (key _ (a j) (hne j)).mpr ⟨p, hp, dvd_add hpb hpL, hpaj⟩
  · intro hb j
    obtain ⟨i, hiN, hsub⟩ := hN j
    obtain ⟨p, hp, hpb, hpai⟩ := (key _ (a i) (hne i)).mp (hb i)
    have hmem : p ∈ (a i).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpai, hne i⟩
    have hpaj : p ∣ a j := (Nat.mem_primeFactors.mp (hsub hmem)).2.1
    have hpL : p ∣ ∏ j ∈ Finset.range (N + 1), a j := hpai.trans (hdvdL i hiN)
    have hpb' : p ∣ b := (Nat.dvd_add_iff_right hpL).mpr (by rwa [Nat.add_comm] at hpb)
    exact (key b (a j) (hne j)).mpr ⟨p, hp, hpb', hpaj⟩
```

### child `main_of_period`: [`IMO2026/Q6/solution.lean` lines 660-698](https://github.com/Boundless-Intuition/IMO2026/blob/37259237016275044e3905e8d537efd0eead74d2/IMO2026/Q6/solution.lean#L660-L698) ([local copy](code/IMO2026/Q6/solution.lean))

```lean
theorem main_of_period (a : ℕ → ℕ) (ha : IsValidSeq a)
    (hper : ∃ L, 0 < L ∧ ∀ b, (Adm a b ↔ Adm a (b + L))) :
    ∃ T L : ℕ, 0 < T ∧ 0 < L ∧ ∀ n, a (n + T) = a n + L := by
  obtain ⟨L, hL0, hshift⟩ := hper
  /- `a 0` is admissible, hence so is `a 0 + L`; it therefore occurs as some `a T`. -/
  have hadm0 : Adm a (a 0 + L) := (hshift (a 0)).mp (adm_seq a ha 0)
  obtain ⟨T, hT⟩ := adm_enum a ha (a 0 + L) hadm0 (by omega)
  have hT0 : 0 < T := by
    rcases Nat.eq_zero_or_pos T with h | h
    · subst h
      omega
    · exact h
  refine ⟨T, L, hT0, hL0, ?_⟩
  intro n
  induction n with
  | zero => simpa using hT
  | succ n ih =>
    have hidx : n + 1 + T = (n + T) + 1 := by omega
    rw [hidx]
    /- Upper bound: `a (n+1) + L` is admissible and exceeds `a (n+T)`. -/
    have h1 : Adm a (a (n + 1) + L) := (hshift (a (n + 1))).mp (adm_seq a ha (n + 1))
    have hlt1 : a (n + T) < a (n + 1) + L := by
      have := seq_lt_succ a ha n
      omega
    have hle : a ((n + T) + 1) ≤ a (n + 1) + L :=
      succ_le_of_adm a ha (n + T) (a (n + 1) + L) h1 hlt1
    /- Lower bound: shift `c := a ((n+T)+1)` back by `L`. -/
    set c := a ((n + T) + 1) with hc
    have hcgt : a (n + T) < c := seq_lt_succ a ha (n + T)
    have hcL : L ≤ c := by omega
    have hsub : (c - L) + L = c := Nat.sub_add_cancel hcL
    have hadmc : Adm a c := adm_seq a ha ((n + T) + 1)
    have hadmc' : Adm a (c - L) := by
      apply (hshift (c - L)).mpr
      rw [hsub]
      exact hadmc
    have hgt : a n < c - L := by omega
    have hge : a (n + 1) ≤ c - L := succ_le_of_adm a ha n (c - L) hadmc' hgt
    omega
```

How the parts fit. The glue is a single nested application; the lemma graph is
a chain of three stages, not a tree:

```
main_theorem (700-705)
  └─ exact main_of_period a ha (exists_period a ha (exists_stable a ha))
       ├─ main_of_period (660-698) : hper ⇒ pure periodicity
       │     hper := exists_period a ha hstab
       ├─ exists_period (614-655)  : hstab ⇒ shift-invariance of Adm
       │     hstab := exists_stable a ha
       └─ exists_stable (599-610)  : ∃ N, supports stabilise (no stage hypothesis)
```

Each stage states the *next-lower* stage's conclusion as an explicit
hypothesis, so the three lemmas are the three stages of a backward chain:

- `main_of_period` (lines 660-698) reduces the goal to a period `L`: it takes
  `hper : ∃ L, 0 < L ∧ ∀ b, Adm a b ↔ Adm a (b + L)` and proves the final
  `∃ T L, 0 < T ∧ 0 < L ∧ ∀ n, a (n + T) = a n + L`. Its proof is
  self-contained: `T` is defined as the index where the admissible value
  `a 0 + L` occurs (via `adm_enum`), and then induction on `n`, with
  `succ_le_of_adm` bounding `a ((n + T) + 1)` from above and below.
- `exists_period` (lines 614-655) supplies that period: it takes
  `hstab : ∃ N, ∀ n, ∃ i ≤ N, (a i).primeFactors ⊆ (a n).primeFactors` and
  proves shift-invariance of the admissible set. Its proof is self-contained:
  the witness is `L := ∏ i ∈ Finset.range (N + 1), a i`, and both directions of
  the `Adm` equivalence go through the `key` dictionary between
  `1 < Nat.gcd x y` and a common prime divisor.
- `exists_stable` (lines 599-610) supplies that stability: it has no stage
  hypothesis, and closes by `exact exists_stable_of a ha hbound hreal hminsub`
  after discharging the helper's three hypotheses from the project lemmas
  `killed_early`, `exists_minMem_subset`, `trans_realized` and `prime_bound`.

Why each is a good leaf. Each child is a self-contained statement whose proof
closes on its own or from named siblings:

- `exists_stable` is the bottom stage, closed from four named siblings in the
  same file (`killed_early`, `exists_minMem_subset`, `trans_realized`,
  `prime_bound`) routed through the local helper `exists_stable_of` (lines
  572-596). Its statement `∃ N, ∀ n, ∃ i ≤ N, …` needs no knowledge of `Adm`,
  `L`, or periodicity — it is purely about prime supports.
- `exists_period` is the middle stage and a genuine bridge: its statement
  mentions only `Adm` and translation, and its proof closes entirely on its own
  using only its hypothesis `hstab` and Mathlib facts about gcd and
  prime factors.
- `main_of_period` is the top stage and is stated exactly at the target's
  generality: its proof closes on its own via induction, using only its
  hypothesis `hper` and the earlier `adm_enum`, `adm_seq`, `seq_lt_succ` and
  `succ_le_of_adm`.

In my opinion the value of the move is the *contract* between stages: each
lemma's hypothesis is literally the previous lemma's conclusion, so the glue is
a single line of function application and every stage can be replayed or
strengthened independently without touching the others.

## Why it is good

1. The parent `main_theorem` cites `main_of_period` in its glue line
   (check, `cites(parent, main_of_period)`, line 705).
2. None of the four sites — the three stage lemmas and the main theorem, lines
   599-705 — closes a goal by `sorry`, `admit` or `axiom` (check,
   `no_sorry`, lines 599-705).
3. The decomposition is a pipeline of depth 3: `main_of_period` takes `hper`
   (the conclusion of `exists_period`) as a hypothesis, `exists_period` takes
   `hstab` (the conclusion of `exists_stable`) as a hypothesis, and
   `exists_stable` has no stage hypothesis (measurement: the glue at line 705,
   the `hper` hypothesis at line 661, the `hstab` hypothesis at line 615).
4. The authors label the three stages in comments — 'THE CRUX' above
   `exists_stable` (line 598), the stabilise-then-period remark above
   `exists_period` (lines 612-613), and 'Pure-periodicity lemma P' above
   `main_of_period` (line 657) — showing the three lemmas were written as a
   deliberate pipeline, not an accident of refactoring (author-statement).

## When to use it, and when not

Use it when the target property is the composition of a short sequence of
intermediate properties, each expressible as a self-contained named theorem
whose hypothesis is exactly the previous theorem's conclusion, and each stage
closes on its own (or from named siblings). This is the situation here:
stability ⇒ shift-invariance ⇒ pure periodicity, with the glue carrying no
argument of its own.

Avoid it when the intermediate properties are not natural standalone statements
(an inline `suffices` is cleaner), when a stage needs shared notation or
context that cannot be stated independently, or when the chain is long enough
that the nested `exact lemma3 (lemma2 (lemma1))` becomes hard to read and a
single structured proof would be clearer.

This entry's move is `other`, not `suffices-or-strengthen`, because the three
stages are three independent `theorem` declarations rather than `suffices`
inside one proof: each stage's hypothesis is stated explicitly in its signature,
and the glue is function application, not a sequence of `suffices` blocks.

## Consequences

Each stage becomes an independent, reusable theorem with an explicit hypothesis
that the next-lower stage must discharge; a missed or mis-typed discharge is
caught as a type error at the glue line. The glue carries no argument of its
own — all the mathematical content lives in the three lemmas, so the parent
proof is one line and the whole risk moves into the statements.

Failure mode: a stage stated a little too strong or too weak silently breaks
the chain, since the only contract between stages is the hypothesis (`hstab`,
`hper`); a subtle mismatch does not produce a counterexample, only a type error
at composition, which the author then has to trace across three signatures.

Scope note: `depth` here counts the stage pipeline only (`main_of_period →
exists_period → exists_stable`). The bottom stage `exists_stable` itself rests
on a deeper sub-decomposition — `exists_stable_of → prime_bound → descent →
cheap_killer → killed_early` — which would be its own entry.

This entry supports survey F §10 rule 8 ("Backward rule, `suffices`, and
witnesses as templates"): `proof (rule r)` makes `r`'s premises children. Here
the rule is generalised to a chain: `main_of_period`'s premise `hper` is the
child discharged by `exists_period`, whose premise `hstab` is the child
discharged by `exists_stable`.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | not-run | no CI workflow in the source repo (no .github/workflows directory; list_files dirac-imo2026 shows none); README documents only a manual 'lake build', so no CI builds IMO2026/Q6/solution.lean on the default branch | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: exists_stable@IMO2026/Q6/solution.lean:705, exists_period@IMO2026/Q6/solution.lean:705, main_of_period@IMO2026/Q6/solution.lean:705; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 37259237016275044e3905e8d537efd0eead74d2 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, main_of_period) -> cites: main_of_period occurs at IMO2026/Q6/solution.lean:705 | check_claims.py |
| 2 | verified | no_sorry(IMO2026/Q6/solution.lean, 599-705) -> no_sorry: none of sorry, admit, axiom in IMO2026/Q6/solution.lean:599-705 | check_claims.py |
| 3 | verified | glue line 705 'exact main_of_period a ha (exists_period a ha (exists_stable a ha))' composes all three; hper hypothesis at line 661 matches exists_period's conclusion (exists L, 0<L and Adm a b iff Adm a (b+L)); hstab hypothesis at line 615 matches exists_stable's conclusion (exists N, ...); exists_stable (lines 599-600) has only (a) and (ha), no stage hypothesis | verifier |
| 4 | verified | line 598 'THE CRUX: the family of prime supports has finitely many minimal elements' above exists_stable; lines 612-613 'If the family of prime-supports stabilises after index N, the admissible set is invariant under translation' above exists_period; line 657 'Pure-periodicity lemma P: shift invariance ... upgrades to pure periodicity' above main_of_period | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Verified all cited line ranges in code/IMO2026/Q6/solution.lean: main_theorem 700-705, exists_stable 599-610, exists_period 614-655, main_of_period 660-698; comments THE CRUX@598, remark@612-613, Pure-periodicity lemma P@657; exists_stable_of 572-596. Glue line 705 is 'exact main_of_period a ha (exists_period a ha (exists_stable a ha))' citing exactly the three children. Closing methods match: exists_stable closes via 'exact exists_stable_of a ha hbound hreal hminsub' after discharging hkill/hminsub/hreal/hbound from killed_early/exists_minMem_subset/trans_realized/prime_bound; exists_period and main_of_period are self-contained as stated. No sorry/admit/axiom in 599-705; glue-cites-children passes. Shape numbers correct: glue_lines 6 (700-705), child_lines [12,42,39] = 599-610/614-655/660-698, direct_lemmas 3, depth 3 (main_of_period->exists_period->exists_stable, hper@661, hstab@615). Children are exactly the lemmas the main proof uses. | reviewer-correctness |
| generality | accept | Move stated transferably: use_when/avoid_when generalise to 'target property is a short composition of intermediate properties, each a self-contained named theorem whose hypothesis is exactly the previous theorem's conclusion', and the entry explicitly distinguishes itself from suffices-or-strengthen (independent theorem declarations, glue is function application). 'When not to use' is specific and honest (not natural standalone statements; stage needs shared notation/context; chain too long to read). Consequences include a real failure mode (a too-strong/too-weak stage surfaces only as a type error at the glue, traced across three signatures), not just benefits. 'Why each is a good leaf' explains what makes them bounded-prover holes: self-contained statements, an explicit hypothesis contract, closing on own or from named siblings, and bottom stage needs no knowledge of Adm/L/periodicity. Author comments (THE CRUX at 598, Pure-periodicity lemma P at 657) confirm the deliberate pipeline, so the generality is grounded rather than invented. | reviewer-generality |
| provenance-licence | accept | Commit 37259237016275044e3905e8d537efd0eead74d2 is identical across entry.json, source.json and SOURCE.md, and every permalink uses it; check_provenance.py reports the copied solution.lean (32068 bytes) byte-identical at that commit. Licence MIT is recorded in entry.json/source.json/SOURCE.md and matches the copied upstream-LICENSE (MIT, Copyright Boundless Intuition). Copied file sha256 5111f905... matches entry.json files[].sha256 and bytes 32068 matches. Cited line ranges verified in the local copy: L598 THE CRUX, L599 exists_stable, L612-613 stabilise-then-period remark, L615 hstab, L657 Pure-periodicity lemma P, L661 hper, L700-705 main_theorem with glue 'exact main_of_period a ha (exists_period a ha (exists_stable a ha))' at L705. Permalinks, commit, licence and source note are consistent with the copied files; fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/Boundless-Intuition/IMO2026 at commit `37259237016275044e3905e8d537efd0eead74d2`, under `MIT`; see the [source note](../../sources/dirac-imo2026/SOURCE.md) for the licence text and attribution.
