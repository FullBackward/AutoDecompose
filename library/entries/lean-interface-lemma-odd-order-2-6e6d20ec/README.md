# theoremC_abstract: BG Appendix C Theorem C as a p/q-level interface lemma over the norm set

| | |
|---|---|
| Kind | instance |
| Move | interface-lemma |
| Language | lean |
| Status | accepted |
| Source | [odd-order-2](../../sources/odd-order-2/SOURCE.md) at `ba8ec35982ce` |
| Licence | `Apache-2.0` |
| Licence recorded | 2026-11-14T15:55:54Z |

## Intent

BG Appendix C Theorem C is restated as a `p, q`-level interface lemma,
`theoremC_abstract`, whose only inputs are oddness of `p` and `q` and the
norm-set relation `N(2a - 1) = 1` on `E`. This removes the Peterfalvi Section 16
configuration from the *statement*, so any Hypothesis-(B)-style input can reach
`p ≤ q` through the three step lemmas without unfolding the field-normalizer
data.

## The decomposition

### parent `theoremC_abstract`: [`OddOrder/BG/AppC_FinalContradiction.lean` lines 124-130](https://github.com/yawara/odd-order/blob/ba8ec35982ceecbd31ca987cbe0cee30477f4883/OddOrder/BG/AppC_FinalContradiction.lean#L124-L130) ([local copy](code/OddOrder/BG/AppC_FinalContradiction.lean))

```lean
theorem theoremC_abstract {p q : ℕ} [Fact p.Prime] (hp_odd : Odd p) (hq : q.Prime) (hq_odd : Odd q)
    (hrel : ∀ a : GaloisField p q, a ∈ NormSet.normSetE p q →
      NormSet.normN p q ((2 : GaloisField p q) * a - 1) = 1) :
    p ≤ q :=
  NormSet.lemmaC1 (p := p) (q := q) hq
    (NormSet.normSetE_eq_inv_of_forall_normN_two_mul_sub_one (p := p) (q := q) hq.pos hrel)
    (NormSet.lemmaC2 (p := p) (q := q) hp_odd hq hq_odd)
```

### child `lemmaC1`: [`OddOrder/BG/AppC_NormSet.lean` lines 535-604](https://github.com/yawara/odd-order/blob/ba8ec35982ceecbd31ca987cbe0cee30477f4883/OddOrder/BG/AppC_NormSet.lean#L535-L604) ([local copy](code/OddOrder/BG/AppC_NormSet.lean))

```lean
theorem lemmaC1 [Fact p.Prime] (hq : q.Prime)
    (hEinv : normSetE p q = (normSetE p q)⁻¹)
    (hcard : 2 ≤ (normSetE p q).ncard) :
    p ≤ q := by
  classical
  -- Start from `a ∈ E^#`.
  obtain ⟨a, ha, hane⟩ := exists_mem_normSetE_ne_one p q hcard
  have h1a : (1 : GaloisField p q) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hane)
  have : CharP (GaloisField p q) p := by
    rw [← Algebra.charP_iff (ZMod p) (GaloisField p q) p]; exact ZMod.charP p
  -- The norm polynomial `P(X) = ∏_{i<q} ((1-a)^{p^i} X + 1) - 1`.
  set P : (GaloisField p q)[X] :=
    (∏ i ∈ Finset.range q, (C ((1 - a) ^ (p ^ i)) * X + C 1)) - C 1 with hP_def
  have hcne : ∀ i, ((1 - a) ^ (p ^ i) : GaloisField p q) ≠ 0 := fun i => pow_ne_zero _ h1a
  have hfac_ne : ∀ i ∈ Finset.range q,
      (C ((1 - a) ^ (p ^ i)) * X + C 1 : (GaloisField p q)[X]) ≠ 0 := by
    intro i _ hz
    have hd1 := natDegree_linear (a := (1 - a) ^ (p ^ i)) (b := (1 : GaloisField p q)) (hcne i)
    rw [hz, natDegree_zero] at hd1
    exact one_ne_zero hd1.symm
  -- `P` has degree exactly `q`.
  have hdeg : P.natDegree = q := by
    rw [hP_def, natDegree_sub_C, natDegree_prod _ _ hfac_ne,
      Finset.sum_congr rfl (fun i _ => natDegree_linear (b := (1 : GaloisField p q)) (hcne i)),
      Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  -- Hence `P ≠ 0`.
  have hPne : P ≠ 0 := by
    intro hz
    have h0 := hdeg
    rw [hz, natDegree_zero] at h0
    have := hq.pos
    omega
  -- Every element of `𝔽_p` is a root of `P`.
  have heval : ∀ k : ℕ, P.eval ((k : ℕ) : GaloisField p q) = 0 := by
    intro k
    rw [hP_def, eval_sub, eval_C, eval_prod]
    have hprod : ∏ i ∈ Finset.range q,
        (C ((1 - a) ^ (p ^ i)) * X + C 1 : (GaloisField p q)[X]).eval ((k : ℕ) : GaloisField p q)
          = 1 := by
      have hstep : ∀ i ∈ Finset.range q,
          (C ((1 - a) ^ (p ^ i)) * X + C 1 : (GaloisField p q)[X]).eval
            ((k : ℕ) : GaloisField p q)
            = ((1 - a) * ((k : ℕ) : GaloisField p q) + 1) ^ (p ^ i) := by
        intro i _
        simp only [eval_add, eval_mul, eval_C, eval_X]
        rw [add_pow_char_pow, mul_pow, one_pow, natCast_pow_pPow]
      rw [Finset.prod_congr rfl hstep, ← normN]
      have hd : (1 - a) * ((k : ℕ) : GaloisField p q) + 1 = dSeq p q a k := by
        rw [dSeq]; ring
      rw [hd]
      exact normN_dSeq_eq_one p q hq.pos hEinv ha k
    rw [hprod]; ring
  -- `𝔽_p` is a `p`-element finset of roots, and `#roots ≤ deg P = q`.
  have hinj : Set.InjOn ((Nat.cast : ℕ → GaloisField p q))
      (↑(Finset.range p)) := by
    rw [Finset.coe_range]; exact CharP.natCast_injOn_Iio (GaloisField p q) p
  have hScard : ((Finset.range p).image ((Nat.cast : ℕ → GaloisField p q))).card = p := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hSsub : (Finset.range p).image ((Nat.cast : ℕ → GaloisField p q))
      ⊆ P.roots.toFinset := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨k, _, rfl⟩ := hx
    rw [Multiset.mem_toFinset, mem_roots']
    exact ⟨hPne, heval k⟩
  calc p = ((Finset.range p).image ((Nat.cast : ℕ → GaloisField p q))).card := hScard.symm
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hSsub
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' P
    _ = q := hdeg
```

### child `normSetE_eq_inv_of_forall_normN_two_mul_sub_one`: [`OddOrder/BG/AppC_NormSet.lean` lines 289-300](https://github.com/yawara/odd-order/blob/ba8ec35982ceecbd31ca987cbe0cee30477f4883/OddOrder/BG/AppC_NormSet.lean#L289-L300) ([local copy](code/OddOrder/BG/AppC_NormSet.lean))

```lean
theorem normSetE_eq_inv_of_forall_normN_two_mul_sub_one [Fact p.Prime] (hq : 0 < q)
    (hrel : ∀ a : GaloisField p q, a ∈ normSetE p q →
      normN p q ((2 : GaloisField p q) * a - 1) = 1) :
    normSetE p q = (normSetE p q)⁻¹ := by
  ext a
  constructor
  · intro ha
    rw [Set.mem_inv]
    exact inv_mem_normSetE_of_normN_two_mul_sub_one p q hq ha (hrel a ha)
  · intro ha
    rw [Set.mem_inv] at ha
    simpa using inv_mem_normSetE_of_normN_two_mul_sub_one p q hq ha (hrel a⁻¹ ha)
```

### child `lemmaC2`: [`OddOrder/BG/AppC_LemmaC2.lean` lines 41-49](https://github.com/yawara/odd-order/blob/ba8ec35982ceecbd31ca987cbe0cee30477f4883/OddOrder/BG/AppC_LemmaC2.lean#L41-L49) ([local copy](code/OddOrder/BG/AppC_LemmaC2.lean))

```lean
theorem lemmaC2 [Fact p.Prime] (hpodd : Odd p) (hq : q.Prime) (hqodd : Odd q) :
    2 ≤ (normSetE p q).ncard := by
  rcases eq_or_ne q 3 with rfl | hq3
  · exact normSetE_ncard_ge_two_of_eq_three p hpodd
  · have hfive : 5 ≤ q := by
      rcases hqodd with ⟨k, hk⟩
      have hq2 : 2 ≤ q := hq.two_le
      omega
    exact normSetE_ncard_ge_two_of_five_le p q hpodd hq hfive
```

How the parts fit. The glue is the three-line proof body of `theoremC_abstract`
(lines 128-130). `lemmaC1` is the conclusion step: it needs `hq : q.Prime`,
inverse-closure `E = E⁻¹`, and a size bound `|E| ≥ 2` and returns `p ≤ q`. The
glue builds the two missing hypotheses from the other two children:

- the inverse-closure argument `hEinv` comes from
  `normSetE_eq_inv_of_forall_normN_two_mul_sub_one`, fed `hq.pos` and the client's
  `hrel` (line 129) — this is the *interface*: it is exactly the boundary where
  the group-theoretic Hypothesis (B) contribution `hrel` enters and everything
  below stays purely `p, q`-algebraic;
- the size bound `hcard` comes from `lemmaC2`, fed only `hp_odd`, `hq`, `hq_odd`
  (line 130) — condition (A) is not an argument to any of the three.

The lemma graph (which lemma uses which):

```
theoremC_abstract  (p ≤ q)
├── lemmaC1        (E = E⁻¹ and |E| ≥ 2  →  p ≤ q)
│   ├── [hEinv] normSetE_eq_inv_of_forall_normN_two_mul_sub_one   (hrel  →  E = E⁻¹)
│   │   └── inv_mem_normSetE_of_normN_two_mul_sub_one             (a ∈ E with N(2a−1)=1  →  a⁻¹ ∈ E)
│   │       └── ne_zero_of_mem_normSetE  →  normN_zero
│   └── [hcard] lemmaC2                 (p, q odd  →  |E| ≥ 2)
```

Why each child is a good leaf:

- `lemmaC1` is self-contained over the norm set: its statement mentions only
  `E`, `|E|`, and `p ≤ q`, and its proof closes on its own — it builds a
  degree-`q` norm polynomial `P` whose roots include all of `𝔽_p`, then a
  `calc` chain `p = |image| ≤ |roots| ≤ P.natDegree = q` (lines 600-604). Its
  only project dependency inside the proof is the `dSeq` machinery
  (`normN_dSeq_eq_one`, line 585).
- `normSetE_eq_inv_of_forall_normN_two_mul_sub_one` is a bidirectional closure
  that reduces to one named sibling `inv_mem_normSetE_of_normN_two_mul_sub_one`
  in both directions (`ext a; constructor`, lines 293-300); it does not unfold
  `normSetE`.
- `lemmaC2` closes by a two-way case split `rcases eq_or_ne q 3` (lines 43-49):
  the `q = 3` branch is `normSetE_ncard_ge_two_of_eq_three`, the `q ≥ 5` branch
  `normSetE_ncard_ge_two_of_five_le`, each a named sibling proved in
  `AppC_NormSet.lean`.

## Why it is good

1. **check** — `lemmaC1` occurs in the parent site `theoremC_abstract`
   ([lines 124-130](https://github.com/yawara/odd-order/blob/ba8ec35982ceecbd31ca987cbe0cee30477f4883/OddOrder/BG/AppC_FinalContradiction.lean#L124-L130));
   the glue cites it for the conclusion.
2. **check** — the parent site (lines 124-130) contains no `sorry`, `admit` or
   `axiom`, so the composition closes without a hole.
3. **check** — `lemmaC2` is declared in
   [`OddOrder/BG/AppC_LemmaC2.lean` lines 41-49](https://github.com/yawara/odd-order/blob/ba8ec35982ceecbd31ca987cbe0cee30477f4883/OddOrder/BG/AppC_LemmaC2.lean#L41-L49).
4. **measurement** — the shape is 3 direct lemmas, glue 7 lines (124-130), child
   proofs 70 + 12 + 9 lines, depth 4 down the inverse-closure branch.
5. **author-statement** — the author's doc comment states the abstraction
   directly: "This is the book's Theorem C with the Peterfalvi Section 16
   configuration removed from the *statement*: no `S16.Hypothesis`, no
   `FieldNormalizerData`, no ambient `q < p`"
   ([lines 113-116](https://github.com/yawara/odd-order/blob/ba8ec35982ceecbd31ca987cbe0cee30477f4883/OddOrder/BG/AppC_FinalContradiction.lean#L113-L116)).

In my opinion the reusable insight is the *choice of the interface*: the glue
passes the client's `hrel` straight into a lemma whose statement is exactly
"`hrel` on `E` implies `E = E⁻¹`", so nothing below that point ever sees a group
or a Section 16 object. Condition (A), which the book's Theorem C states, is
deliberately left off this lemma (the author notes it does no work here); the
cost is deferred to the client that produces `hrel`.

## When to use it, and when not

Use it when the step lemmas are already stated over the abstraction variables
alone (here `p, q`), and a client can supply the boundary hypothesis (`hrel`)
without unfolding the concrete configuration that produced it. The move pays
when several clients hold the boundary hypothesis but not the configuration:
the same file reuses `theoremC_abstract` from the Section 16 instance
(`theoremC_of_hypothesisB`) and the Hypothesis-(B) abstract form
(`theoremC_of_hypothesisBAbstract`).

Avoid it when the step lemmas still mention the concrete configuration in their
statements, or when the boundary hypothesis is not what clients hold, so they
would have to unfold group data to build it. Also avoid thinning the statement
further than the step lemmas support: here condition (A) was removed only
because none of the three steps used it, and the comment records that fact
(lines 107-111).

## Consequences

The abstract lemma carries no condition (A) and no Section 16 data, so its
obligations are exactly three: the client must supply oddness of `p` and `q`
and the norm relation `hrel`. It defers condition (A)'s work to the client that
produces `hrel` (here `FieldNormalizerData.normSetGeneratorRelation_of_hypothesisB`,
line 143); if a client cannot produce `hrel` without unfolding the
configuration, the abstraction buys nothing. Both the inverse-closure and the
size bound must be supplied — neither is derived from the other here — so the
interface is only as thin as the three step lemmas allow. A failure mode is a
future client that assumes condition (A) is in scope: this lemma no longer
carries it, and the comment (lines 107-111) warns that (A) does real work only
downstream.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/lean_action_ci.yml; commit ba8ec35982ceecbd31ca987cbe0cee30477f4883 on default branch main (branches-where-head=main); lean-action runs lake build over OddOrder/** which includes OddOrder/BG/AppC_FinalContradiction.lean | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: lemmaC1@OddOrder/BG/AppC_FinalContradiction.lean:128, normSetE_eq_inv_of_forall_normN_two_mul_sub_one@OddOrder/BG/AppC_FinalContradiction.lean:129, lemmaC2@OddOrder/BG/AppC_FinalContradiction.lean:130; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 3 file(s) byte-identical at ba8ec35982ceecbd31ca987cbe0cee30477f4883 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, lemmaC1) -> cites: lemmaC1 occurs at OddOrder/BG/AppC_FinalContradiction.lean:128 | check_claims.py |
| 2 | verified | no_sorry(OddOrder/BG/AppC_FinalContradiction.lean, 124-130) -> no_sorry: none of sorry, admit, axiom in OddOrder/BG/AppC_FinalContradiction.lean:124-130 | check_claims.py |
| 3 | verified | declared(lemmaC2, OddOrder/BG/AppC_LemmaC2.lean, 41-49) -> declared: lemmaC2 is declared at OddOrder/BG/AppC_LemmaC2.lean:41 | check_claims.py |
| 4 | verified | Measured against code/: parent glue AppC_FinalContradiction.lean:124-130 is 7 lines citing lemmaC1(L128), normSetE_eq_inv_of_forall_normN_two_mul_sub_one(L129), lemmaC2(L130)=3 direct lemmas; child sites lemmaC1 AppC_NormSet.lean:535-604 (70 lines), normSetE_eq_inv 289-300 (12 lines), lemmaC2 AppC_LemmaC2.lean:41-49 (9 lines); depth chain verified: normSetE_eq_inv calls inv_mem_normSetE_of_normN_two_mul_sub_one (297,300), which calls ne_zero_of_mem_normSetE (279), which calls normN_zero (96) = 4 deep | verifier |
| 5 | verified | Doc comment /-- **BG Theorem C, p/q-abstract form.** in AppC_FinalContradiction.lean:113-114 reads verbatim 'This is the book's Theorem C with the Peterfalvi Section 16 configuration removed from the *statement*: no S16.Hypothesis, no FieldNormalizerData, no ambient q < p.' | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Decomposition matches: the parent theoremC_abstract (AppC_FinalContradiction.lean:124-130) proof body (128-130) calls exactly three named lemmas — NormSet.lemmaC1 (128), NormSet.normSetE_eq_inv_of_forall_normN_two_mul_sub_one (129), NormSet.lemmaC2 (130) — which are precisely the three children. Statements are verbatim from code. Closing methods match: lemmaC1 ends in the calc chain p = |image| ≤ |roots| ≤ P.natDegree = q (600-604); normSetE_eq_inv closes by ext a; constructor via inv_mem_normSetE_of_normN_two_mul_sub_one both directions (293-300); lemmaC2 by rcases eq_or_ne q 3 with the eq_three / five_le branches (43-49). Closes: no sorry/admit/axiom in parent or child sites (glue-cites-children and sorry-scan already pass; claims 1-3 verified by check_claims.py). Shape numbers correct: direct_lemmas 3, glue_lines 7 (site 124-130), child_lines [70,12,9] = 535-604, 289-300, 41-49, depth 4 = inverse-closure chain normSetE_eq_inv -> inv_mem_normSetE_of_normN_two_mul_sub_one (279) -> ne_zero_of_mem_normSetE (96) -> normN_zero, each edge verified in AppC_NormSet.lean. | reviewer-correctness |
| generality | accept | Generality holds. (1) The move is stated beyond the example: 'When to use' and applicability give general conditions (step lemmas over p,q alone; client supplies boundary hypothesis hrel without unfolding the configuration), and the reusable insight is named as the choice of interface, with the author's own doc comment (AppC_FinalContradiction.lean 118-122) confirming any configuration supplying hrel (e.g. SL(2,2^q)) feeds it directly. (2) 'When not to use' and consequences are honest and specific: condition (A) is dropped only because none of the three steps used it (comment 107-111); the interface is only as thin as the step lemmas allow (both inverse-closure and size bound must be supplied); work is deferred to the client that produces hrel (line 143); and a concrete failure mode (a future client assuming condition A is in scope) is named. (3) 'Why each child is a good leaf' states the leaf properties a bounded prover needs: self-contained statement over E/|E|/p<=q that closes on its own with a single calc chain and one project dependency (dSeq); a bidirectional closure reducing to one named sibling without unfolding normSetE; a two-way case split into named siblings. Minor non-blocking note: the 'When to use' sentence 'several clients hold the boundary hypothesis but not the configuration' slightly overstates — both cited clients hold the configuration, and theoremC_of_hypothesisBAbstract reaches theoremC_abstract only indirectly via theoremC_of_hypothesisB (metrics.reused_by=1 is the accurate count); this is a wording imprecision, not a dishonesty, and the surrounding text states the real generality correctly. | reviewer-generality |
| provenance-licence | accept | check_provenance passes (3 files byte-identical at ba8ec35982ceecbd31ca987cbe0cee30477f4883); commit hash identical across entry.json, README, source.json and SOURCE.md; licence Apache-2.0 matches upstream LICENSE (Apache-2.0) and is recorded consistently in entry.json/source.json/SOURCE.md; all permalinks use github.com/yawara/odd-order at the pinned commit with correct file paths and line ranges, and each cited range (parent 124-130, author comment 113-116, known_uses 139-145/158-162, lemmaC1 535-604, normSetE_eq_inv 289-300, lemmaC2 41-49, depth chain 275-285/92-97/86-89) was opened and matches the copied content; source note link resolves to library/sources/odd-order-2/SOURCE.md | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/yawara/odd-order at commit `ba8ec35982ceecbd31ca987cbe0cee30477f4883`, under `Apache-2.0`; see the [source note](../../sources/odd-order-2/SOURCE.md) for the licence text and attribution.
