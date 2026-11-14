# Key invariants mu (potential) and pinv (p-adic) close IMO 2026 Problem 1

| | |
|---|---|
| Kind | instance |
| Move | key-invariant |
| Language | lean |
| Status | draft |
| Source | [pramaana-imo2026](../../sources/pramaana-imo2026/SOURCE.md) at `788fddc53c46` |
| Licence | `MIT` |
| Licence recorded | 2026-11-14T09:36:49Z |

## Intent

IMO 2026 Problem 1 asks whether a move — replace two entries `m, n > 1` by
`gcd m n` and `lcm m n / gcd m n` — always ends, and what the final board
looks like. The answer is carried by two conserved quantities: a potential
`mu s = 2 * s.prod + bigCount s` that strictly decreases along every move
(giving termination and a well-founded induction), and a p-adic invariant
`pinv p s` (the gcd of the entries' p-adic valuations) that pins the single
surviving entry's prime factorization (giving confluence). The parent theorem
`answer_correctness` proves the answer is `true` and assembles these two
quantities into the four-part end-state characterisation.

## The decomposition

### parent `answer_correctness`: [`IMO2026/Q1/solution.lean` lines 248-338](https://github.com/pramaana-labs/imo2026-lean/blob/788fddc53c463d5d40d4680fb9bfd7b0f96f1063/IMO2026/Q1/solution.lean#L248-L338) ([local copy](code/IMO2026/Q1/solution.lean))

```lean
theorem answer_correctness
    (s₀ : Board)
    (h_card : Fact_card s₀)
    (h_all_gt1 : Fact_all_gt1 s₀)
    : answer = true ↔
        ( (¬ ∃ f : ℕ → Board, f 0 = s₀ ∧ ∀ k, Move (f k) (f (k + 1)))
          ∧ (∃ t, Relation.ReflTransGen Move s₀ t ∧ IsTerminal t)
          ∧ (∀ t, Relation.ReflTransGen Move s₀ t → IsTerminal t → bigCount t = 1)
          ∧ (∀ t₁ t₂, Relation.ReflTransGen Move s₀ t₁ → IsTerminal t₁ →
               Relation.ReflTransGen Move s₀ t₂ → IsTerminal t₂ →
               bigPart t₁ = bigPart t₂) ) := by
  have h_card' : Multiset.card s₀ = 2026 := h_card
  have h_gt1 : ∀ x ∈ s₀, 1 < x := h_all_gt1
  have hpos : Pos s₀ := fun x hx => lt_trans one_pos (h_gt1 x hx)
  have hb0 : bigCount s₀ = 2026 := by
    have h1 : Multiset.filter (fun x => 1 < x) s₀ = s₀ := Multiset.filter_eq_self.mpr h_gt1
    simp only [bigCount, h1]
    exact h_card'
  -- (a-count)
  have hbig1 : ∀ t, Relation.ReflTransGen Move s₀ t → IsTerminal t → bigCount t = 1 := by
    intro t hrt hT
    have hle : bigCount t ≤ 1 := isTerminal_iff.mp hT
    have hge : 1 ≤ bigCount t := by
      rcases Relation.ReflTransGen.cases_tail hrt with heq | ⟨u, hu, hmv⟩
      · rw [heq, hb0]; omega
      · exact one_le_bigCount_of_move hmv
    omega
  -- terminal boards are singletons with determined factorization
  have key : ∀ t, Relation.ReflTransGen Move s₀ t → IsTerminal t →
      ∃ M, bigPart t = {M} ∧ 1 < M ∧ ∀ p, M.factorization p = pinv p s₀ := by
    intro t hrt hT
    have hbc : Multiset.card (t.filter (fun x => 1 < x)) = 1 := hbig1 t hrt hT
    obtain ⟨M, hM⟩ := Multiset.card_eq_one.mp hbc
    have hMmem : M ∈ t.filter (fun x => 1 < x) := by
      rw [hM]; exact Multiset.mem_singleton_self M
    have hM1 : 1 < M := (Multiset.mem_filter.mp hMmem).2
    refine ⟨M, hM, hM1, ?_⟩
    intro p
    have hsplit : t.filter (fun x => 1 < x) + t.filter (fun x => ¬ 1 < x) = t :=
      Multiset.filter_add_not _ t
    have ht' : t = M ::ₘ t.filter (fun x => ¬ 1 < x) := by
      conv_lhs => rw [← hsplit, hM]
      rw [Multiset.singleton_add]
    have hz : ((t.filter (fun x => ¬ 1 < x)).map (fun x => x.factorization p)).gcd = 0 := by
      rw [Multiset.gcd_eq_zero_iff]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
      have hx1 : ¬ 1 < x := (Multiset.mem_filter.mp hx).2
      have hxt : x ∈ t := (Multiset.mem_filter.mp hx).1
      have hxpos : 0 < x := pos_rtg hpos hrt x hxt
      have : x = 1 := by omega
      rw [this]; simp
    have hit : pinv p t = M.factorization p := by
      unfold pinv
      rw [ht']
      simp only [Multiset.map_cons, Multiset.gcd_cons, gcd_coe]
      rw [hz, Nat.gcd_zero_right]
    rw [← hit]
    exact pinv_rtg hrt
  constructor
  · intro _
    refine ⟨?_, exists_terminal hpos, hbig1, ?_⟩
    · -- termination: no infinite play
      rintro ⟨f, hf0, hf⟩
      have hposk : ∀ k, Pos (f k) := by
        intro k
        induction k with
        | zero => rw [hf0]; exact hpos
        | succ k ih => exact pos_of_move ih (hf k)
      have hdec : ∀ k, mu (f k) + k ≤ mu (f 0) := by
        intro k
        induction k with
        | zero => omega
        | succ k ih =>
          have := mu_lt_of_move (hposk k) (hf k)
          omega
      have := hdec (mu (f 0) + 1)
      omega
    · -- uniqueness of the surviving big part
      intro t₁ t₂ hr1 hT1 hr2 hT2
      obtain ⟨M₁, hP1, hM11, hf1⟩ := key t₁ hr1 hT1
      obtain ⟨M₂, hP2, hM21, hf2⟩ := key t₂ hr2 hT2
      have hMM : M₁ = M₂ := by
        have hfeq : M₁.factorization = M₂.factorization :=
          Finsupp.ext fun p => by rw [hf1 p, hf2 p]
        have h10 : (M₁ : ℕ) ≠ 0 := by omega
        have h20 : (M₂ : ℕ) ≠ 0 := by omega
        exact Nat.factorization_inj h10 h20 hfeq
      rw [hP1, hP2, hMM]
  · intro _
    rfl
```

### child `isTerminal_iff`: [`IMO2026/Q1/solution.lean` lines 80-90](https://github.com/pramaana-labs/imo2026-lean/blob/788fddc53c463d5d40d4680fb9bfd7b0f96f1063/IMO2026/Q1/solution.lean#L80-L90) ([local copy](code/IMO2026/Q1/solution.lean))

```lean
lemma isTerminal_iff {s : Board} : IsTerminal s ↔ bigCount s ≤ 1 := by
  constructor
  · intro hT
    by_contra hc
    push Not at hc
    obtain ⟨t, ht⟩ := exists_move_of_two_le (s := s) (by omega)
    exact hT t ht
  · intro h t ht
    obtain ⟨m, n, r, hm, hn, hs, -⟩ := move_decomp ht
    rw [hs, bigCount_cons_big hm, bigCount_cons_big hn] at h
    omega
```

### child `pos_of_move`: [`IMO2026/Q1/solution.lean` lines 92-105](https://github.com/pramaana-labs/imo2026-lean/blob/788fddc53c463d5d40d4680fb9bfd7b0f96f1063/IMO2026/Q1/solution.lean#L92-L105) ([local copy](code/IMO2026/Q1/solution.lean))

```lean
lemma pos_of_move {s t : Board} (hp : Pos s) (h : Move s t) : Pos t := by
  obtain ⟨m, n, r, hm, hn, hs, ht⟩ := move_decomp h
  have hg : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n (by omega)
  have hl : 0 < Nat.lcm m n := Nat.lcm_pos (by omega) (by omega)
  have hgl : Nat.gcd m n ∣ Nat.lcm m n :=
    dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
  have hd : 0 < Nat.lcm m n / Nat.gcd m n := Nat.div_pos (Nat.le_of_dvd hl hgl) hg
  intro x hx
  rw [ht] at hx
  rcases Multiset.mem_cons.mp hx with rfl | hx
  · exact hg
  rcases Multiset.mem_cons.mp hx with rfl | hx
  · exact hd
  · exact hp x (by rw [hs]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hx))
```

### child `one_le_bigCount_of_move`: [`IMO2026/Q1/solution.lean` lines 107-118](https://github.com/pramaana-labs/imo2026-lean/blob/788fddc53c463d5d40d4680fb9bfd7b0f96f1063/IMO2026/Q1/solution.lean#L107-L118) ([local copy](code/IMO2026/Q1/solution.lean))

```lean
lemma one_le_bigCount_of_move {s t : Board} (h : Move s t) : 1 ≤ bigCount t := by
  obtain ⟨m, n, r, hm, hn, hs, ht⟩ := move_decomp h
  by_cases hgb : 1 < Nat.gcd m n
  · rw [ht, bigCount_cons_big hgb]; omega
  · have hg : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n (by omega)
    have hg1 : Nat.gcd m n = 1 := by omega
    have hl : 0 < Nat.lcm m n := Nat.lcm_pos (by omega) (by omega)
    have hd : 1 < Nat.lcm m n / Nat.gcd m n := by
      rw [hg1, Nat.div_one]
      exact lt_of_lt_of_le hm (Nat.le_of_dvd hl (Nat.dvd_lcm_left m n))
    rw [ht, bigCount_cons_small hgb, bigCount_cons_big hd]
    omega
```

### child `mu_lt_of_move`: [`IMO2026/Q1/solution.lean` lines 125-173](https://github.com/pramaana-labs/imo2026-lean/blob/788fddc53c463d5d40d4680fb9bfd7b0f96f1063/IMO2026/Q1/solution.lean#L125-L173) ([local copy](code/IMO2026/Q1/solution.lean))

```lean
lemma mu_lt_of_move {s t : Board} (hp : Pos s) (h : Move s t) : mu t < mu s := by
  obtain ⟨m, n, r, hm, hn, hs, ht⟩ := move_decomp h
  set g := Nat.gcd m n with hgdef
  set d := Nat.lcm m n / Nat.gcd m n with hddef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left n (by omega)
  have hl0 : 0 < Nat.lcm m n := Nat.lcm_pos (by omega) (by omega)
  have hgl : g ∣ Nat.lcm m n :=
    dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
  have hgd : g * d = Nat.lcm m n := Nat.mul_div_cancel' hgl
  have hglm : g * Nat.lcm m n = m * n := Nat.gcd_mul_lcm m n
  have hrpos : 0 < r.prod := by
    apply prod_pos_of_pos
    intro x hx
    exact hp x (by rw [hs]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hx))
  have hprods : s.prod = m * n * r.prod := by
    rw [hs, Multiset.prod_cons, Multiset.prod_cons, ← mul_assoc]
  have hprodt : t.prod = Nat.lcm m n * r.prod := by
    rw [ht, Multiset.prod_cons, Multiset.prod_cons, ← mul_assoc, hgd]
  have hbcs : bigCount s = bigCount r + 2 := by
    rw [hs, bigCount_cons_big hm, bigCount_cons_big hn]
  by_cases hg1 : g = 1
  · -- coprime case: product unchanged, bigCount drops by one
    have hlmn : Nat.lcm m n = m * n := by
      rw [hg1, one_mul] at hglm; exact hglm
    have hpp : t.prod = s.prod := by rw [hprodt, hprods, hlmn]
    have hd1 : 1 < d := by
      have : d = Nat.lcm m n := by rw [hddef, ← hgdef, hg1, Nat.div_one]
      rw [this, hlmn]
      calc 1 < m := hm
        _ ≤ m * n := Nat.le_mul_of_pos_right m (by omega)
    have hbct : bigCount t = bigCount r + 1 := by
      rw [ht, hg1, bigCount_cons_small (by omega), bigCount_cons_big hd1]
    unfold mu
    omega
  · -- gcd > 1: product strictly decreases
    have hl_lt : Nat.lcm m n < m * n := by
      have h2 : 2 ≤ g := by omega
      calc Nat.lcm m n < 2 * Nat.lcm m n := by omega
        _ ≤ g * Nat.lcm m n := Nat.mul_le_mul_right _ h2
        _ = m * n := hglm
    have hpt_lt : t.prod < s.prod := by
      rw [hprodt, hprods]
      exact (Nat.mul_lt_mul_right hrpos).mpr hl_lt
    have hbct_le : bigCount t ≤ bigCount r + 2 := by
      rw [ht]
      calc bigCount (g ::ₘ d ::ₘ r) ≤ bigCount (d ::ₘ r) + 1 := bigCount_cons_le _ _
        _ ≤ bigCount r + 2 := by have := bigCount_cons_le d r; omega
    unfold mu
    omega
```

### child `pos_rtg`: [`IMO2026/Q1/solution.lean` lines 210-213](https://github.com/pramaana-labs/imo2026-lean/blob/788fddc53c463d5d40d4680fb9bfd7b0f96f1063/IMO2026/Q1/solution.lean#L210-L213) ([local copy](code/IMO2026/Q1/solution.lean))

```lean
lemma pos_rtg {s t : Board} (hp : Pos s) (h : Relation.ReflTransGen Move s t) : Pos t := by
  induction h with
  | refl => exact hp
  | tail _ hmv ih => exact pos_of_move ih hmv
```

### child `pinv_rtg`: [`IMO2026/Q1/solution.lean` lines 215-219](https://github.com/pramaana-labs/imo2026-lean/blob/788fddc53c463d5d40d4680fb9bfd7b0f96f1063/IMO2026/Q1/solution.lean#L215-L219) ([local copy](code/IMO2026/Q1/solution.lean))

```lean
lemma pinv_rtg {p : ℕ} {s t : Board}
    (h : Relation.ReflTransGen Move s t) : pinv p t = pinv p s := by
  induction h with
  | refl => rfl
  | tail _ hmv ih => rw [pinv_move hmv, ih]
```

### child `exists_terminal`: [`IMO2026/Q1/solution.lean` lines 244-246](https://github.com/pramaana-labs/imo2026-lean/blob/788fddc53c463d5d40d4680fb9bfd7b0f96f1063/IMO2026/Q1/solution.lean#L244-L246) ([local copy](code/IMO2026/Q1/solution.lean))

```lean
lemma exists_terminal {s : Board} (hp : Pos s) :
    ∃ t, Relation.ReflTransGen Move s t ∧ IsTerminal t :=
  exists_terminal_aux (mu s) s le_rfl hp
```

How the parts fit. The glue is the proof of `answer_correctness` (lines
248-338), which after fixing `hpos : Pos s₀` and `hb0 : bigCount s₀ = 2026`
proves four sub-claims and then discharges the two directions of the `↔`.
Each sub-claim is closed from the seven child lemmas below.

```
answer_correctness (parent, 248-338)
├── isTerminal_iff         (80-90)     cited at 269  — terminal ⇔ bigCount ≤ 1
├── one_le_bigCount_of_move (107-118) cited at 273  — a move leaves bigCount ≥ 1
├── pos_rtg                (210-213)   cited at 297  — positivity along the closure
├── pinv_rtg               (215-219)   cited at 306  — pinv along the closure
├── exists_terminal        (244-246)   cited at 309  — a terminal board exists
├── pos_of_move            (92-105)    cited at 316  — positivity along one move
└── mu_lt_of_move          (125-173)   cited at 322  — the potential decreases
```

The two conserved quantities live one level deeper, in lemmas the children
use but the glue does not cite directly:

- `mu_lt_of_move` needs `move_decomp` (38-43), `prod_pos_of_pos` (120-121),
  `bigCount_cons_big`/`bigCount_cons_small` (45-51) and `bigCount_cons_le`
  (53-57).
- `exists_terminal` is `exists_terminal_aux` (221-242) instantiated at `mu s`;
  that well-founded induction cites `mu_lt_of_move` (240) and `pos_of_move`
  (241).
- `pinv_rtg` is induction over the closure using `pinv_move` (191-208), which
  in turn uses `move_decomp`, `gcd_coe` (177) and the custom `gcd_min_sub`
  (179-189).
- `pos_rtg` is induction over the closure using `pos_of_move`, which uses
  `move_decomp`.
- `isTerminal_iff` uses `exists_move_of_two_le` (59-78) forward and
  `move_decomp` + `bigCount_cons_big` backward.

Why each child is a good leaf — a self-contained statement whose proof closes
on its own or from a named sibling:

- `isTerminal_iff` is a clean `↔`, closed by `constructor` and `omega` in both
  directions, borrowing only `exists_move_of_two_le` and `move_decomp`.
- `pos_of_move` closes by `rcases` on the three entries of `t`; each entry is
  positive by `Nat.gcd_pos_of_pos_left`, `Nat.lcm_pos` + `Nat.div_pos`, or the
  hypothesis `hp`.
- `one_le_bigCount_of_move` closes by a `by_cases` on `1 < gcd m n`, then
  `bigCount_cons_big`/`bigCount_cons_small` and `omega`.
- `mu_lt_of_move` closes by a `by_cases` on `g = 1` (coprime vs not), then
  `unfold mu; omega` in each case; the two cases are the whole content of the
  descent.
- `pos_rtg` and `pinv_rtg` are one-line inductions over the reflexive-transitive
  closure: `refl` is `hp`/`rfl`, `tail` is `pos_of_move`/`pinv_move`.
- `exists_terminal` is a single application of `exists_terminal_aux (mu s) s
  le_rfl hp`, delegating the well-founded descent to the potential.

## Why it is good

1. The parent (glue) site is 91 lines, carrying the whole problem onto two
   conserved quantities; the site is [lines 248-338](https://github.com/pramaana-labs/imo2026-lean/blob/788fddc53c463d5d40d4680fb9bfd7b0f96f1063/IMO2026/Q1/solution.lean#L248-L338) (`check`).
2. The glue cites the invariant lift `pinv_rtg` (line 306), the lemma that
   transports `pinv` to any reachable board (`check`).
3. The glue cites the descent `mu_lt_of_move` (line 322), the lemma that makes
   termination and the well-founded induction go through (`check`).
4. No goal in the glue is closed by `sorry`, `admit`, or `axiom`: the 91 lines
   248-338 close without holes (`check`, [file](https://github.com/pramaana-labs/imo2026-lean/blob/788fddc53c463d5d40d4680fb9bfd7b0f96f1063/IMO2026/Q1/solution.lean#L248-L338)).
5. The skeleton is 7 direct lemmas on a 91-line glue with depth 4
   (`answer_correctness → exists_terminal → exists_terminal_aux →
   mu_lt_of_move → move_decomp`) (`measurement`, counted from the sites).
6. The authors label the two cases of the descent with comments — "coprime
   case: product unchanged, bigCount drops by one" and "gcd > 1: product
   strictly decreases" — showing the potential was chosen to make exactly this
   split work ([lines 146 and 159](https://github.com/pramaana-labs/imo2026-lean/blob/788fddc53c463d5d40d4680fb9bfd7b0f96f1063/IMO2026/Q1/solution.lean#L146-L159), `author-statement`).

In my opinion the detail worth copying is that the potential is *not* a pure
descent function: it is `2 * s.prod + bigCount s`, a linear combination of a
quantity that decreases when `gcd m n > 1` and a quantity that decreases when
`gcd m n = 1`. The two cases of `mu_lt_of_move` are exactly those two terms
taking over, so one scalar absorbs the entire argument.

## When to use it, and when not

Use a potential-plus-invariant pair when a rewriting or game process must be
shown both terminating and confluent, and the same two quantities do both
jobs: a potential that strictly decreases along every move (termination), and
an invariant that factors through every prime so that two normal forms with
equal invariant are equal (confluence). The potential is worth using when a
single quantity is monotone — here the trick is to mix a multiplicative term
(`s.prod`) and an additive term (`bigCount`) so that whichever move applies
forces one of them to drop.

Avoid it when the move can increase the product while decreasing the count
(the single potential would not be monotone and the two quantities would have
to be tracked separately), when the invariant is too weak to tell the normal
forms apart (confluence then needs its own argument), or when the end-state
fact is not a gcd/factorization fact already in the library (here `pinv`
leans on `Nat.factorization_gcd`, `Nat.factorization_lcm`,
`Nat.factorization_div`, and the hand-written `gcd_min_sub`).

## Consequences

Choosing the two invariants creates four obligations, each a child: prove the
potential strictly decreases along a move (`mu_lt_of_move`, a two-case split on
`gcd m n = 1`); prove the invariant is preserved along a move and along the
reflexive-transitive closure (`pinv_move`, `pinv_rtg`); prove positivity
propagates along a move (`pos_of_move`) so the potential stays defined and
non-negative; and lift the single-step facts to the closure (`pos_rtg`,
`pinv_rtg`) and to termination (`exists_terminal_aux`, a well-founded induction
on `mu`). The known failure mode is that `mu` mixes a multiplicative and an
additive quantity: if a move could raise `s.prod` while lowering `bigCount`, the
single scalar would no longer be monotone, and the two terms would have to be
tracked as separate arguments rather than folded into one potential.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: isTerminal_iff@IMO2026/Q1/solution.lean:269, pos_of_move@IMO2026/Q1/solution.lean:316, one_le_bigCount_of_move@IMO2026/Q1/solution.lean:273, mu_lt_of_move@IMO2026/Q1/solution.lean:322, pos_rtg@IMO2026/Q1/solution.lean:297, pinv_rtg@IMO2026/Q1/solution.lean:306, exists_terminal@IMO2026/Q1/solution.lean:309; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(answer_correctness, 91) -> lines: site answer_correctness has 91 lines | check_claims.py |
| 2 | verified | cites(answer_correctness, pinv_rtg) -> cites: pinv_rtg occurs at IMO2026/Q1/solution.lean:306 | check_claims.py |
| 3 | verified | cites(answer_correctness, mu_lt_of_move) -> cites: mu_lt_of_move occurs at IMO2026/Q1/solution.lean:322 | check_claims.py |
| 4 | verified | no_sorry(IMO2026/Q1/solution.lean, 248-338) -> no_sorry: none of sorry, admit, axiom in IMO2026/Q1/solution.lean:248-338 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/pramaana-labs/imo2026-lean at commit `788fddc53c463d5d40d4680fb9bfd7b0f96f1063`, under `MIT`; see the [source note](../../sources/pramaana-imo2026/SOURCE.md) for the licence text and attribution.
