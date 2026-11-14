# Inequality chain proving n < 7 for IMO 2019 Q4

| | |
|---|---|
| Kind | instance |
| Move | calc-chain |
| Language | isabelle |
| Status | draft |
| Source | [afp](../../sources/afp/SOURCE.md) at `07cd9ca548d1` |
| Licence | `BSD-3-Clause` |

## Intent

The parent `n_less_7` proves the bound `n < 7`, the step that collapses IMO
2019 Q4 from infinitely many candidate pairs `(k, n)` to a finite check over
`n ∈ {1..6}` (which the following lemma `n_k_in_set` finishes). It does so as
one `also … finally` inequality chain
`fact T ≤ fact k = rhs < 2^n² ≤ 8^T ≤ fact T`, whose three non-trivial links
are the named same-file lemmas `k_gt_T`, `rhs_less` and `fact_ge_power`.

## The decomposition

### parent `n_less_7`: [`thys/IMO2019/IMO2019_Q4.thy` lines 231-260](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/IMO2019/IMO2019_Q4.thy#L231-L260) ([local copy](code/thys/IMO2019/IMO2019_Q4.thy))

```isabelle
lemma n_less_7: "n < 7"
proof (rule ccontr)
  assume "\<not>n < 7"
  hence "n \<ge> 7" by simp
  have "T \<ge> (7 * 6) div 2"
    unfolding T_def using \<open>n \<ge> 7\<close> by (intro div_le_mono mult_mono) auto
  hence "T \<ge> 21" by simp

  from \<open>n \<ge> 7\<close> have "(n * 2) div 2 \<le> T"
    unfolding T_def by (intro div_le_mono) auto
  hence "T \<ge> n" by simp

  from \<open>T \<ge> 21\<close> have "sqrt (2 * pi * T) * (T / exp 1) ^ T \<le> fact T"
    using fact_bounds[of T] by simp
  have "fact T \<le> (fact k :: nat)"
    using k_gt_T by (intro fact_mono) (auto simp: T_def)
  also have "\<dots> = rhs" by fact
  also have "rhs < 2 ^ n\<^sup>2" by (rule rhs_less)
  also have "n\<^sup>2 = 2 * T + n"
    by (cases "even n") (auto simp: T_def algebra_simps power2_eq_square)
  also have "\<dots> \<le> 3 * T"
    using \<open>T \<ge> n\<close> by (simp add: T_def)
  also have "2 ^ (3 * T) = (8 ^ T :: nat)"
    by (simp add: power_mult)
  finally have "fact T < (8 ^ T :: nat)"
    by simp
  moreover have "fact T \<ge> (8 ^ T :: nat)"
    by (rule fact_ge_power[of _ 20]) (use \<open>T \<ge> 21\<close> in \<open>auto simp: fact_numeral\<close>)
  ultimately show False by simp
qed
```

### context `context`: [`thys/IMO2019/IMO2019_Q4.thy` lines 133-139](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/IMO2019/IMO2019_Q4.thy#L133-L139) ([local copy](code/thys/IMO2019/IMO2019_Q4.thy))

```isabelle
context
  fixes k n :: nat and rhs T :: nat
  defines "rhs \<equiv> (\<Prod>i<n. 2 ^ n - 2 ^ i)"
  defines "T \<equiv> (n * (n - 1)) div 2"
  assumes pos: "k > 0" "n > 0"
  assumes k_n: "fact k = rhs"
begin
```

### child `k_gt_T`: [`thys/IMO2019/IMO2019_Q4.thy` lines 180-191](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/IMO2019/IMO2019_Q4.thy#L180-L191) ([local copy](code/thys/IMO2019/IMO2019_Q4.thy))

```isabelle
lemma k_gt_T: "k > T"
proof -
  have "T = multiplicity 2 rhs"
    by simp
  also have "rhs = fact k"
    by (simp add: k_n)
  also have "multiplicity 2 (fact k :: nat) = legendre_aux k 2"
    by (simp add: multiplicity_prime_fact)
  also have "\<dots> < k"
    using legendre_aux_less[of 2 k] pos by simp
  finally show ?thesis .
qed
```

### child `rhs_less`: [`thys/IMO2019/IMO2019_Q4.thy` lines 206-224](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/IMO2019/IMO2019_Q4.thy#L206-L224) ([local copy](code/thys/IMO2019/IMO2019_Q4.thy))

```isabelle
lemma rhs_less: "rhs < 2 ^ n\<^sup>2"
proof -
  have "rhs = 2 ^ T * (\<Prod>i=1..n. 2 ^ i - 1)"
    by (simp add: rhs_altdef)
  also have "(\<Prod>i=1..n. 2 ^ i - 1 :: nat) < (\<Prod>i=1..n. 2 ^ i)"
    using pos by (intro prod_mono_strict[of 1]) auto
  also have "\<dots> = (\<Prod>i=0..<n. 2 * 2 ^ i)"
    by (intro prod.reindex_bij_witness[of _ Suc "\<lambda>i. i - 1"]) (auto simp flip: power_Suc)
  also have "\<dots> = 2 ^ n * 2 ^ (\<Sum>i=0..<n. i)"
    by (simp add: power_sum prod.distrib)
  also have "(\<Sum>i=0..<n. i) = T"
    unfolding T_def by (simp add: Sum_Ico_nat)
  also have "2 ^ T * (2 ^ n * 2 ^ T :: nat) = 2 ^ (2 * T + n)"
    by (simp flip: power_add power_Suc add: algebra_simps)
  also have "2 * T + n = n ^ 2"
    by (cases "even n") (auto simp: T_def algebra_simps power2_eq_square)
  finally show "rhs < 2 ^ n\<^sup>2"
    by simp
qed
```

### child `fact_ge_power`: [`thys/IMO2019/IMO2019_Q4.thy` lines 27-38](https://github.com/isabelle-prover/mirror-afp-devel/blob/07cd9ca548d180f234c63f06bf5d1cb85c7fc5df/thys/IMO2019/IMO2019_Q4.thy#L27-L38) ([local copy](code/thys/IMO2019/IMO2019_Q4.thy))

```isabelle
lemma fact_ge_power:
  fixes c :: nat
  assumes "fact n0 \<ge> c ^ n0" "c \<le> n0 + 1"
  assumes "n \<ge> n0"
  shows   "fact n \<ge> c ^ n"
  using assms(3,1,2)
proof (induction n rule: dec_induct)
  case (step n)
  have "c * c ^ n \<le> Suc n * fact n"
    using step by (intro mult_mono) auto
  thus ?case by simp
qed auto
```

How the parts fit. `n_less_7` is proved by contradiction: assuming `n ≥ 7`
(line 233), the glue first derives two small facts `T ≥ 21` (lines 235-237)
and `T ≥ n` (lines 239-241), then runs one `also … finally` chain
(lines 245-256) closed against the opposite bound with `moreover`/`ultimately`
(lines 257-259):

```
fact T ≤ fact k = rhs < 2^n² = 2^(2T+n) ≤ 2^(3T) = 8^T ≤ fact T
```

The three non-trivial links are the named children, each stated and proved
earlier in the same file:

- `k_gt_T` (lines 180-191) gives `fact T ≤ fact k`, via `T < k` and
  `fact_mono`. It is itself a small calc chain
  `T = multiplicity 2 rhs = legendre_aux k 2 < k` over the sibling lemmas
  `multiplicity_2_rhs`, `multiplicity_prime_fact`, `legendre_aux_less`.
- `rhs_less` (lines 206-224) gives `rhs < 2^n²`, a calc chain over
  `rhs_altdef`, `prod_mono_strict`, `power_sum`.
- `fact_ge_power` (lines 27-38) gives `fact T ≥ 8^T`, a self-contained
  induction on `T` from the base `fact 20 ≥ 8^20`; its step closes by
  `mult_mono`.

The only other fact the glue uses directly, `fact_bounds` (line 244), is an
imported library lemma (from `Stirling_Formula`), not a project lemma: it
supplies `sqrt (2πT) · (T/e)^T ≤ fact T`, which is needed only to make
`fact T ≥ 8^T` follow from `fact_ge_power`'s hypothesis `T ≥ 21`. The chain's
middle steps `n² = 2T + n ≤ 3T` and `2^(3T) = 8^T` (lines 249-254) are inline
arithmetic, part of the glue rather than named children.

Lemma graph (project lemmas only; `→` means "used by"):

```
n_less_7
├── k_gt_T ── multiplicity_2_rhs ── rhs_altdef
│         ├─ multiplicity_prime_fact ── prime_multiplicity_prime
│         └─ legendre_aux_less
├── rhs_less ── rhs_altdef
└── fact_ge_power          (leaf)
```

Each child is a good leaf because its statement is a single self-contained
inequality between named quantities and its proof closes either on its own
(`fact_ge_power`, an induction whose step is `mult_mono`) or from named
same-file siblings whose own proofs close on library facts (`k_gt_T`,
`rhs_less`). The longest project-lemma chain below `n_less_7` has depth 3
(`n_less_7 → k_gt_T → multiplicity_2_rhs → rhs_altdef`, and also
`n_less_7 → k_gt_T → multiplicity_prime_fact → prime_multiplicity_prime`).

## Why it is good

1. The parent closes from its three named children: `k_gt_T` supplies
   `fact T ≤ fact k` (lines 245-246), `rhs_less` supplies `rhs < 2^n²`
   (line 248), `fact_ge_power` supplies `fact T ≥ 8^T` (line 258), and the
   proof ends in `qed` (line 260); each child also ends in `qed` (lines 38,
   191, 224) (*check*).
2. `thys/IMO2019` contains no `sorry`, `admit` or `oops`: a grep over the
   three theories `IMO2019_Q1.thy`, `IMO2019_Q4.thy`, `IMO2019_Q5.thy` at the
   pinned commit returned no matches (*check*).
3. The glue proof spans 29 lines (232-260) and calls 3 named same-file lemmas
   directly; the longest project-lemma chain below it has depth 3
   (`n_less_7 → k_gt_T → multiplicity_2_rhs → rhs_altdef`); the child proofs
   are 11, 18 and 7 lines (*measurement*; see `shape` in entry.json).
4. The authors state the plan in the comment before the lemma: "It is clear
   that $2^{n^2} \le 8^T$ and that $8^T < T!$ if $T$ is sufficiently big … We
   can therefore conclude that $n$ must be less than 7" (lines 226-230)
   (*author-statement*).
5. The same `also … finally`-over-named-lemmas pattern recurs at the child
   level: `k_gt_T` (lines 181-191) chains `multiplicity_2_rhs`,
   `multiplicity_prime_fact` and `legendre_aux_less`, and `rhs_less`
   (lines 207-224) chains over `rhs_altdef` (*known-use*).

In my opinion the detail worth copying is the discipline of the middle of the
chain: the glue leaves the arithmetic rewrites (`n² = 2T + n ≤ 3T`, `8^T`)
inline but lifts every genuinely mathematical step (`fact T ≤ fact k`,
`rhs < 2^n²`, `fact T ≥ 8^T`) into a named lemma, so each step is a hole a
bounded prover can be pointed at.

## When to use it, and when not

Use it when the goal is a chain of inequalities whose individual steps are
non-trivial enough to each deserve a named lemma, and the chain can be written
in one direction with `also … finally` (`<`/`≤`/`=`), so transitivity is
automatic. This is the natural shape when the theorem collapses an infinite
family to a finite check: state each mathematical step as a lemma, thread them
in one chain, and let the arithmetic links stay inline.

Avoid it when the steps are one-off rewrites with no reuse (fold them inline),
when a direct induction or a single library theorem is shorter, or when the
chain needs `≥` steps — Isar's `also` does not compose `≥` by default, so a
downward chain forces you to either reverse each step or write an explicit
`le_trans`. Also avoid naming a step whose statement is needed only in one
direction but stated too weakly to survive the chain's `<`/`≤`/`=` end.

## Consequences

The move creates one obligation per link: each named lemma must be proved in
its own right before the chain composes them. Transitivity is discharged
automatically by `also`/`finally`, but a link stated too weakly breaks the end
result — here the strict `<` of the whole chain survives only because
`rhs_less` is strict after the equality `fact k = rhs`. The glue also has a
hidden precondition: `fact_bounds` needs `T ≥ 21`, so the proof first derives
`T ≥ 21` from `n ≥ 7` (lines 235-237); forgetting that leaves
`fact T ≥ 8^T` without its hypothesis. The final contradiction relies on both
`fact T < 8^T` and `fact T ≥ 8^T`, so dropping either child makes the proof
close vacuously wrong.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | not-run | no Isabelle toolchain on the harvest machine; mirror-afp-devel has no in-repo CI workflow (no .github/workflows or Jenkins/Travis/GitLab config in the 31441-file listing at the pinned commit), so there is no workflow file to cite for ci-record — the AFP's CI is an external Jenkins testboard | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| glue-cites-children | pass | cited: k_gt_T@thys/IMO2019/IMO2019_Q4.thy:246, rhs_less@thys/IMO2019/IMO2019_Q4.thy:248, fact_ge_power@thys/IMO2019/IMO2019_Q4.thy:258; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 07cd9ca548d180f234c63f06bf5d1cb85c7fc5df | check_provenance.py | 2026-11-12 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | read code/thys/IMO2019/IMO2019_Q4.thy (byte-identical to pinned commit per check_provenance): L245-246 fact T <= fact k via k_gt_T, L248 rhs_less, L257-258 fact_ge_power, qed at L260; child qeds at L38, L191, L224 | verifier |
| 2 | verified | grep -iE 'sorry|admit|oops' over library/cache/afp/files/thys/IMO2019/IMO2019_Q1.thy, IMO2019_Q4.thy, IMO2019_Q5.thy returned 0 matches | verifier |
| 3 | verified | counted in the copied file: glue L232-260 = 29 lines; direct same-file lemmas k_gt_T/rhs_less/fact_ge_power = 3; chain n_less_7 -> k_gt_T -> multiplicity_2_rhs -> rhs_altdef = depth 3; child lines 181-191=11, 207-224=18, 32-38=7 | verifier |
| 4 | verified | comment L226-230 reads: 'It is clear that 2^(n^2) <= 8^T and that 8^T < T! if T is sufficiently big ... We can therefore conclude that n must be less than 7.' | verifier |
| 5 | verified | k_gt_T (L181-191) uses multiplicity_2_rhs (L183), multiplicity_prime_fact (L187), legendre_aux_less (L189); rhs_less (L207-224) uses rhs_altdef (L209) | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Read the byte-identical copied code (per check_provenance). Parent n_less_7 (L231-260) closes at qed L260 from exactly three same-file children: k_gt_T (L246, gives fact T <= fact k), rhs_less (L248, gives rhs < 2^n^2), fact_ge_power (L258, gives fact T >= 8^T via [of _ 20]); each child ends in qed (L191, L224, L38). Child statements and closed_by match the code: k_gt_T chain T = multiplicity 2 rhs = legendre_aux k 2 < k over multiplicity_2_rhs/multiplicity_prime_fact/legendre_aux_less; rhs_less over rhs_altdef/prod_mono_strict/power_sum; fact_ge_power dec_induct with mult_mono step. No sorry/admit/oops. Shape numbers correct: direct_lemmas=3, depth=3 (n_less_7 -> k_gt_T -> multiplicity_2_rhs -> rhs_altdef), glue_lines=29 (L232-260), child_lines=[11,18,7] (L181-191, L207-224, L32-38). fact_bounds (L244) is an imported Stirling_Formula lemma, correctly not a child. | reviewer-correctness |
| generality | accept | Move stated generally (goal_shape 'a bound like n < N, or more generally an inequality between two expressions... collapses to a small finite check'; use_when/avoid_when and 'When to use it' prose describe a chain of inequalities with non-trivial named steps written in one direction with also/finally, not just IMO 2019 Q4). 'When not to use' and consequences are honest and specific: the >= limitation of Isar's also, folding one-off rewrites inline, a link stated too weak breaking the strict end, one obligation per link, and the hidden precondition that fact_bounds needs T >= 21. It explicitly says what makes the leaves good for a bounded prover: each child is a single self-contained inequality between named quantities whose proof closes on its own (fact_ge_power) or from named same-file siblings (k_gt_T, rhs_less), so each step is a hole a bounded prover can be pointed at. Minor: 'dropping either child makes the proof close vacuously wrong' is imprecise (it would leave the proof incomplete, not vacuously wrong), but the substance is correct and does not warrant objection. | reviewer-generality |
| provenance-licence | object | Permalinks and commit are consistent and traceable: every permalink points at 07cd9ca548d180f234c63f06bf5d1cb85c7fc5df, check_provenance reports the copied file byte-identical at that commit, and the line anchors match the copied file (n_less_7 L231-260, context L133-139, children L180-191/L206-224/L27-38). The licence is not consistent with the copied file: entry.json and SOURCE.md record LicenseRef-unknown and claim 'no licence file found at the root', but the IMO2019 entry's licence is traceable at the pinned commit - metadata/entries/IMO2019.toml has license = 'bsd' and metadata/licenses.toml maps bsd -> 'BSD'. Fix: record the licence as BSD and cite that metadata locator in the entry's source licence and in SOURCE.md, instead of LicenseRef-unknown. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/isabelle-prover/mirror-afp-devel at commit `07cd9ca548d180f234c63f06bf5d1cb85c7fc5df`, under `BSD-3-Clause`; see the [source note](../../sources/afp/SOURCE.md) for the licence text and attribution.
