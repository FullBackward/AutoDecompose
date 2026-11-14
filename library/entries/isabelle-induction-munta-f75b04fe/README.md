# Induction on k, split on a negative diagonal, for Floyd-Warshall correctness

| | |
|---|---|
| Kind | instance |
| Move | induction |
| Language | isabelle |
| Status | accepted |
| Source | [munta](../../sources/munta/SOURCE.md) at `62cb1a4a4dbc` |
| Licence | `MIT` |

## Intent

Prove the main correctness theorem of the Floyd-Warshall formalisation -- that
`fw m n k` preserves canonical form and cycle-freeness on the index set `{0..k}`
whenever the input `m` is cycle-free there -- by induction on `k`. The step case
splits on whether `fw m n (Suc k)` has a negative diagonal entry, which decides
between a negative-cycle contradiction and extending cycle-freeness one index
further.

## The decomposition

### parent `fw_correct`: [`DBM/Floyd_Warshall.thy` lines 1077-1114](https://github.com/wimmers/munta/blob/62cb1a4a4dbcfcf62c365e90faba15b0012d5a12/DBM/Floyd_Warshall.thy#L1077-L1114) ([local copy](code/DBM/Floyd_Warshall.thy))

```isabelle
theorem fw_correct:
  "canonical_subs n {0..k} (fw m n k) \<and> cyc_free_subs n {0..k} (fw m n k)"
  if "cyc_free_subs n {0..k} m" "k \<le> n"
  using that
proof (induction k)
  case 0
  then show ?case
    using fwi_cyc_free_subs[of n "{}" 0 m] fwi_canonical_extend[of n "{}"]
    by (auto simp: cyc_free_subs_diag)
next
  case (Suc k)
  then have IH:
    "canonical_subs n {0..k} (fw m n k) \<and> cyc_free_subs n {0..k} (fw m n k)"
    by fastforce
  have *: "{0..Suc k} = {0..k} \<union> {Suc k}" by auto
  then have **: "canonical_subs n {0..Suc k} (fw m n (Suc k))"
    apply simp
    apply (rule fwi_canonical_extend[of n "{0..k}" _ "Suc k", simplified])
    subgoal
      using IH ..
    subgoal
      using IH Suc.prems by (auto intro: cyc_free_subs_diag[of n "{0..k}" "fw m n k"])
    by (rule Suc)
  show ?case
  proof (cases "\<exists>i\<le>n. fw m n (Suc k) i i < 0")
    case True
    then obtain i where "i \<le> n" "len (fw m n (Suc k)) i i [] < 0"
      by auto
    from fw_neg_diag_neg_cycle[OF this(2,1) \<open>Suc k \<le> n\<close>] Suc.prems show ?thesis by fastforce
  next
    case False
    have "cyc_free_subs n {0..Suc k} (fw m n (Suc k))"
      apply (simp add: *)
      apply (rule fwi_cyc_free_subs'[of n "{0..k}", simplified])
      using Suc IH False by force+
    with ** show ?thesis by blast
  qed
qed
```

### child `fwi_canonical_extend`: [`DBM/Floyd_Warshall.thy` lines 871-927](https://github.com/wimmers/munta/blob/62cb1a4a4dbcfcf62c365e90faba15b0012d5a12/DBM/Floyd_Warshall.thy#L871-L927) ([local copy](code/DBM/Floyd_Warshall.thy))

```isabelle
lemma fwi_canonical_extend:
  "canonical_subs n (I \<union> {k}) (fwi m n k n n)" if
  "canonical_subs n I m" "I \<subseteq> {0..n}" "0 \<le> m k k" "k \<le> n"
  using that
  unfolding canonical_subs_def
  apply safe
  subgoal for i j k'
    apply (subst fwi_step', (auto; fail)+)+
    unfolding min_def
  proof (clarsimp, safe, goal_cases)
    case 1
    then show ?case by force
  next
    case prems: 2
    from prems have "m i k \<le> m i j + m j k"
      by auto
    with prems(10) show ?case
      by (auto simp: add.assoc[symmetric] add_mono intro: order.trans)
  next
    case prems: 3
    from prems have "m i k \<le> m i j + m j k"
      by auto
    with prems(10) show ?case
      by (auto simp: add.assoc[symmetric] add_mono intro: order.trans)
  next
    case prems: 4
    from prems have "m k k' \<le> m k j + m j k'"
      by auto
    with prems(10) show ?case
      by (auto simp: add_mono add.assoc intro: order.trans)
  next
    case prems: 5
    from prems have "m k k' \<le> m k j + m j k'"
      by auto
    with prems(10) show ?case
      by (auto simp: add_mono add.assoc intro: order.trans)
  next
    case prems: 6
    from prems have "0 \<le> m k j + m j k"
      by (auto intro: order.trans)
    with prems(10) show ?case
      apply -
      apply (rule order.trans, assumption)
      apply (simp add: add.assoc[symmetric])
      by (rule add_mono, auto simp: add_increasing2 add.assoc intro: order.trans)
  next
    case prems: 7
    from prems have "0 \<le> m k j + m j k"
      by (auto intro: order.trans)
    with prems(10) show ?case
      by (simp add: add.assoc[symmetric])
        (rule add_mono, auto simp: add_increasing2 add.assoc intro: order.trans)
  qed
  subgoal for i j k'
    apply (subst fwi_step', (auto; fail)+)+
    unfolding min_def by (auto intro: add_increasing add_increasing2)
  done
```

### child `cyc_free_subs_diag`: [`DBM/Floyd_Warshall.thy` lines 951-956](https://github.com/wimmers/munta/blob/62cb1a4a4dbcfcf62c365e90faba15b0012d5a12/DBM/Floyd_Warshall.thy#L951-L956) ([local copy](code/DBM/Floyd_Warshall.thy))

```isabelle
lemma cyc_free_subs_diag:
  "m i i \<ge> 0" if "cyc_free_subs n I m" "i \<le> n"
proof -
  have "set [] \<subseteq> I" by auto
  with that show ?thesis by fastforce
qed
```

### child `fwi_cyc_free_subs'`: [`DBM/Floyd_Warshall.thy` lines 958-971](https://github.com/wimmers/munta/blob/62cb1a4a4dbcfcf62c365e90faba15b0012d5a12/DBM/Floyd_Warshall.thy#L958-L971) ([local copy](code/DBM/Floyd_Warshall.thy))

```isabelle
lemma fwi_cyc_free_subs':
  "cyc_free_subs n (I \<union> {k}) (fwi m n k n n)" if
  "cyc_free_subs n I m" "canonical_subs n I m" "I \<subseteq> {0..n}" "k \<le> n"
  "\<forall> i \<le> n. fwi m n k n n i i \<ge> 0"
proof (safe, goal_cases)
  case prems: (1 i xs)
  from that(1) \<open>k \<le> n\<close> have "0 \<le> m k k" by (rule cyc_free_subs_diag)
  from that \<open>0 \<le> m k k\<close> have *: "canonical_subs n (I \<union> {k}) (fwi m n k n n)"
    by - (rule fwi_canonical_extend; auto)
  from prems that have "0 \<le> fwi m n k n n i i" by blast
  also from * prems that have "fwi m n k n n i i \<le> len (fwi m n k n n) i i xs"
    by (auto intro: canonical_subs_len)
  finally show ?case .
qed
```

### child `fwi_cyc_free_subs`: [`DBM/Floyd_Warshall.thy` lines 973-985](https://github.com/wimmers/munta/blob/62cb1a4a4dbcfcf62c365e90faba15b0012d5a12/DBM/Floyd_Warshall.thy#L973-L985) ([local copy](code/DBM/Floyd_Warshall.thy))

```isabelle
lemma fwi_cyc_free_subs:
  "cyc_free_subs n (I \<union> {k}) (fwi m n k n n)" if
  "cyc_free_subs n (I \<union> {k}) m" "canonical_subs n I m" "I \<subseteq> {0..n}" "k \<le> n"
proof (safe, goal_cases)
  case prems: (1 i xs)
  from that(1) \<open>k \<le> n\<close> have "0 \<le> m k k" by (rule cyc_free_subs_diag)
  from that \<open>0 \<le> m k k\<close> have *: "canonical_subs n (I \<union> {k}) (fwi m n k n n)"
    by - (rule fwi_canonical_extend; auto)
  from prems that \<open>0 \<le> m k k\<close> have "0 \<le> fwi m n k n n i i" by (auto intro!: fwi_cyc_free_diag)
  also from * prems that have "fwi m n k n n i i \<le> len (fwi m n k n n) i i xs"
    by (auto intro: canonical_subs_len)
  finally show ?case .
qed
```

### child `fw_neg_diag_neg_cycle`: [`DBM/Floyd_Warshall.thy` lines 1056-1074](https://github.com/wimmers/munta/blob/62cb1a4a4dbcfcf62c365e90faba15b0012d5a12/DBM/Floyd_Warshall.thy#L1056-L1074) ([local copy](code/DBM/Floyd_Warshall.thy))

```isabelle
lemma fw_neg_diag_neg_cycle:
  "\<exists> i \<le> n. \<exists> ys. set ys \<subseteq> set xs \<union> {0..k} \<and> len m i i ys < 0" if
  "len (fw m n k) i i xs < 0" "i \<le> n" "k \<le> n" "set xs \<subseteq> {0..n}"
  using that
  proof (induction k arbitrary: i xs)
    case 0
    then show ?case by simp (drule fwi_neg_cycle_neg_cycle; auto)
  next
    case (Suc k)
    from fwi_neg_cycle_neg_cycle[OF Suc.prems(1)[simplified]] Suc.prems obtain i' ys where
      "i' \<le> n"  "set ys \<subseteq> set xs \<union> {Suc k}" "len (fw m n k) i' i' ys < 0"
      by auto
    with Suc.prems obtain i'' zs where
      "i'' \<le> n" "set zs \<subseteq> set ys \<union> {0..k}" "len m i'' i'' zs < 0"
      by atomize_elim (auto intro!: Suc.IH)
    with \<open>set ys \<subseteq> _\<close> have "set zs \<subseteq> set xs \<union> {0..Suc k} \<and> len m i'' i'' zs < 0"
      by force
    with \<open>i'' \<le> n\<close> show ?case by blast
  qed
```

How the parts fit. The parent `fw_correct` is a proof by induction on `k`
whose step case is itself a case split. The lemma graph below the parent:

```
fw_correct
 |-- fwi_canonical_extend   (base 0 and step "**": canonicality)
 |-- cyc_free_subs_diag     (base 0 and step "**": non-negative diagonal)
 |-- fwi_cyc_free_subs      (base 0: cycle-freeness)
 |-- fw_neg_diag_neg_cycle  (step, some negative diagonal: contradiction)
 `-- fwi_cyc_free_subs'     (step, no negative diagonal: cycle-freeness)

fwi_cyc_free_subs      uses  cyc_free_subs_diag, fwi_canonical_extend, fwi_cyc_free_diag, canonical_subs_len
fwi_cyc_free_subs'     uses  cyc_free_subs_diag, fwi_canonical_extend, canonical_subs_len
fw_neg_diag_neg_cycle  uses  fwi_neg_cycle_neg_cycle
fwi_canonical_extend   uses  fwi_step'
fwi_step'              uses  single_iteration_inv, fwi_step
```

The base case (`k = 0`) establishes both conjuncts from the input's
cycle-freeness: `fwi_cyc_free_subs` gives cycle-freeness on `{0}`,
`fwi_canonical_extend` gives canonicality on `{0}`, and `cyc_free_subs_diag`
supplies the non-negative diagonal `0 ≤ m 0 0` they both need. In the step
case, the canonicality conjunct `**` is obtained by `fwi_canonical_extend`
with the induction hypothesis `IH` as the source of `canonical_subs n {0..k}
(fw m n k)` and `cyc_free_subs_diag` for the non-negative diagonal. The
cycle-freeness conjunct is decided by the case split on `∃ i ≤ n. fw m n
(Suc k) i i < 0`: in the `True` branch `fw_neg_diag_neg_cycle` turns the
negative diagonal into a negative cycle, contradicting the input's
cycle-freeness; in the `False` branch `fwi_cyc_free_subs'` extends
cycle-freeness, taking as its strengthened hypothesis that no diagonal entry
is negative.

Why each lemma is a good leaf:

- `fwi_canonical_extend` is self-contained: it unfolds `canonical_subs_def`
  and reduces each obligation with `fwi_step'` to a `min` inequality, then
  closes the 7 + 1 cases by `force`/`auto` with `add_mono`, `add_increasing`
  and `order.trans`. Its assumptions are exactly what the parent has at each
  induction step.
- `cyc_free_subs_diag` is a one-line leaf: instantiating the `cyc_free_subs`
  abbreviation with the empty path `[]` yields `m i i ≥ 0`, closed by
  `fastforce`.
- `fwi_cyc_free_subs'` and `fwi_cyc_free_subs` are near-identical leaves that
  each chain `0 ≤ fwi m n k n n i i` with `fwi m n k n n i i ≤ len (fwi m n k n
  n) i i xs` (from `canonical_subs_len` after `fwi_canonical_extend`). They
  differ only in where the non-negative diagonal comes from: the primed
  variant takes it as a hypothesis, the unprimed one derives it with
  `fwi_cyc_free_diag`. Both close by `fastforce`/`blast`.
- `fw_neg_diag_neg_cycle` closes by its own induction on `k` with `arbitrary:
  i xs`, using `fwi_neg_cycle_neg_cycle` in both the base and step cases.

## Why it is good

1. The glue is compact: the parent site `fw_correct` is 38 lines long,
   declaration and proof together, and it combines the five lemmas in that
   space (check, lines 1077-1114).
2. The glue cites its children: the parent proof cites `fw_neg_diag_neg_cycle`,
   the lemma behind the negative-diagonal branch of the case split, at
   line 1105 (check, lines 1077-1114).
3. The authors state the plan the theorem follows: "To prove the main result
   under the absence of negative cycles, we will proceed as follows: we show
   that an invocation of fwi m n k n n extends canonicality to index k, we show
   that an invocation of fw m n n computes a matrix in canonical form, and
   finally we show that canonical forms specify the lengths of shortest paths,
   provided that there are no negative cycles." (author-statement,
   lines 839-845).
4. The theorem is reused downstream: `fw_correct` is reused in four places
   after its statement -- the one-conjunct lemmas `fw_canonical_subs` and
   `fw_cyc_free_subs` (lines 1116-1117) and the later proofs `fw_subs_len`
   (line 1290) and `fw_shortest_path_up_to` (line 1628), counted by grepping
   `fw_correct` over the file (measurement).

In my opinion the detail worth copying is the *negative-diagonal case split*:
rather than prove both conjuncts directly, the author extends canonicality
unconditionally and only branches on the diagonal test to obtain
cycle-freeness, so the split introduces exactly one branch (`fwi_cyc_free_subs'`)
that is not already forced by the recursion.

## When to use it, and when not

Use induction on `k` when the goal is a property `P (f n k)` of a recursion
`f n (Suc k) = step (f n k)` that grows the index set `{0..k}` by one each
step, and when each one-step extension is already factored into named lemmas
(here `fwi_canonical_extend` and `fwi_cyc_free_subs`/`fwi_cyc_free_subs'`) so
the base and step cases close by citing them. Reach for the negative-diagonal
split when the invariant has two conjuncts that are not both forced by the
recursion: extend the one that always holds (canonicality) unconditionally,
then branch on the test (a negative diagonal) to obtain the other
(cycle-freeness).

Avoid it when the step needs a test that is not part of the invariant and the
negation of that test cannot be turned into the extra hypothesis of a
strengthening lemma (`fwi_cyc_free_subs'` takes `∀ i ≤ n. fwi m n k n n i i ≥ 0`);
if that hypothesis is not derivable, the `False` branch will not close. Avoid
it too when the two conjuncts cannot be stated as abbreviations over the same
growing set, since the induction then needs a stronger or more general
hypothesis before it is stated.

## Consequences

The induction creates a base case and a step case; the step case is further
split on `∃ i ≤ n. fw m n (Suc k) i i < 0`, whose exhaustiveness is by `cases`.
The negative-diagonal branch needs `fw_neg_diag_neg_cycle` -- itself proved by
a second induction on `k` with `arbitrary: i xs` -- to contradict the input's
cycle-freeness. The non-negative branch must supply the strengthened hypothesis
`∀ i ≤ n. fwi m n k n n i i ≥ 0` to `fwi_cyc_free_subs'`. The two conjuncts are
proved separately (canonicality by `fwi_canonical_extend`, cycle-freeness by
`fwi_cyc_free_subs`/`fwi_cyc_free_subs'`) and combined only at the end, so each
one-step invariant is stated and proved on its own. The main failure mode is a
mismatch between the diagonal test used to split and the extra hypothesis of
the strengthening lemma: if `fwi_cyc_free_subs'` had required a different
strengthening than "no negative diagonal", the `False` branch would not have
the hypothesis it needs.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .travis.yml builds session TA_Code with 'isabellectl --afp --version 2017 ... build -- -bv -d . ... "TA_Code"'; ROOT: TA_Code in Model_Checking = Simple_Networks + ... transitively includes session DBM with theory Floyd_Warshall; commit 62cb1a4 is latest on default branch master | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: fwi_canonical_extend@DBM/Floyd_Warshall.thy:1084, cyc_free_subs_diag@DBM/Floyd_Warshall.thy:1085, fwi_cyc_free_subs'@DBM/Floyd_Warshall.thy:1110, fwi_cyc_free_subs@DBM/Floyd_Warshall.thy:1084, fw_neg_diag_neg_cycle@DBM/Floyd_Warshall.thy:1105; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 62cb1a4a4dbcfcf62c365e90faba15b0012d5a12 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | lines(parent, 38) -> lines: site parent has 38 lines | check_claims.py |
| 2 | verified | cites(parent, fw_neg_diag_neg_cycle) -> cites: fw_neg_diag_neg_cycle occurs at DBM/Floyd_Warshall.thy:1105 | check_claims.py |
| 3 | verified | Read lines 839-845 of code/DBM/Floyd_Warshall.thy; the text block quotes the plan verbatim: 'To prove the main result under the absence of negative cycles ... provided that there are no negative cycles.' | verifier |
| 4 | verified | grep -n fw_correct over code/DBM/Floyd_Warshall.thy returns 1077, 1116, 1117, 1290, 1628; after the theorem (1077) it is used at 1116 (fw_canonical_subs = fw_correct[THEN conjunct1]), 1117 (fw_cyc_free_subs = fw_correct[THEN conjunct2]), 1290 (from fw_correct[OF ...]), 1628 (auto dest: fw_correct) | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent fw_correct (1077-1114) is a proof by induction on k whose step splits on the negative-diagonal test; the five children are exactly the lemmas the parent cites directly (fwi_cyc_free_subs@1084, fwi_canonical_extend@1084/1094, cyc_free_subs_diag@1085/1098, fw_neg_diag_neg_cycle@1105, fwi_cyc_free_subs'@1110) and no other named lemma. Each child's closed_by matches the code (fwi_canonical_extend: canonical_subs_def + fwi_step' + force/auto with add_mono/add_increasing/order.trans; cyc_free_subs_diag: empty path [] + fastforce; fwi_cyc_free_subs' and fwi_cyc_free_subs: cyc_free_subs_diag + fwi_canonical_extend + canonical_subs_len, primed/unprimed differ only in the non-negative diagonal source fwi_cyc_free_diag; fw_neg_diag_neg_cycle: induction k arbitrary i xs via fwi_neg_cycle_neg_cycle). Proof closes (ends qed, sorry-scan pass, glue-cites-children pass). Shape numbers exact: direct_lemmas=5, glue_lines=38 (1114-1077+1), child_lines=[57,6,14,13,19] (927-871+1, 956-951+1, 971-958+1, 985-973+1, 1074-1056+1). depth=5 matches the documented longest chain fw_correct->fwi_cyc_free_subs->fwi_canonical_extend->fwi_step'->single_iteration_inv counted with the root (the code's real chain continues one more level via single_iteration_inv->single_iteration_inv'->single_row_inv, but depth is 'that you checked' so 5 is defensible). Claims 1-4 all hold (lines(parent,38) verified; cites fw_neg_diag_neg_cycle@1105 verified; author statement 839-845 read and matches; reuse grep returns 1077,1116,1117,1290,1628 = four post-statement uses). | reviewer-correctness |
| generality | accept | Move generalised beyond Floyd-Warshall: applicability states the pattern as induction over a recursion fw m n (Suc k) = step (fw m n k) growing the index set {0..k} by one, with each one-step extension already factored into named lemmas, and a case split on a test to obtain the conjunct not forced by the recursion; confirmed against the fw recursion at lines 424-426 and the parent proof at 1077-1114. When-not-to-use is honest and specific: the avoid_when correctly identifies that the False branch needs the strengthened hypothesis to be exactly the negation of the diagonal test, matching 'using Suc IH False by force+' at line 1110-1111 and fwi_cyc_free_subs' hypothesis 'all i <= n. fwi m n k n n i i >= 0'. Consequences are specific, including the genuine failure mode (diagonal test / strengthening-lemma mismatch). Good-leaf question answered concretely per lemma in the 'Why each lemma is a good leaf' section plus metrics children_closed_by_automation=5 (force/auto/fastforce/blast, no nested interactive sub-proof). | reviewer-generality |
| provenance-licence | accept | Provenance passes: check_provenance.py reports 1 file byte-identical at 62cb1a4a4dbcfcf62c365e90faba15b0012d5a12; code/DBM/Floyd_Warshall.thy has sha256 6fd4bf2d18d54cee4c942be09e165957cccdefb96f54a74a2bc80e8cc879b90e and 82210 bytes, matching entry.json files[0] exactly. Commit is recorded consistently across entry.json source.commit, sources/munta/SOURCE.md, and source.json; the README source line's 62cb1a4a4dbc is a correct 12-char prefix of the full hash. Licence MIT is correct: sources/munta/upstream-LICENSE is the MIT License (Copyright (c) 2017 Simon Wimmer), consistent with entry.json source.licence and SOURCE.md. Permalinks use the full commit hash, repo wimmers/munta, path DBM/Floyd_Warshall.thy and correct #L ranges. Spot-checked cited line ranges in the copied file: fw_correct@1077, fwi_canonical_extend@871, cyc_free_subs_diag@951, fwi_cyc_free_subs'@958, fwi_cyc_free_subs@973, fw_neg_diag_neg_cycle@1056, author-statement@839-845, and reuse@1116,1117,1290,1628 all match. Fully traceable. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/wimmers/munta at commit `62cb1a4a4dbcfcf62c365e90faba15b0012d5a12`, under `MIT`; see the [source note](../../sources/munta/SOURCE.md) for the licence text and attribution.
