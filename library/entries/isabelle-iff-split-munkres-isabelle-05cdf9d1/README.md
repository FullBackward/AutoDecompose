# Iff-split of the sequential characterization of continuity into forward and metric converse

| | |
|---|---|
| Kind | instance |
| Move | iff-split |
| Language | isabelle |
| Status | draft |
| Source | [munkres-isabelle](../../sources/munkres-isabelle/SOURCE.md) at `90d108779e83` |
| Licence | `LicenseRef-unknown` |

## Intent

Prove the sequential characterization of continuity — a map is continuous iff
it sends convergent sequences to convergent sequences, the converse under
metrizability — by splitting it into its forward implication and its metric
converse, each stated and proved as its own named lemma, then gluing them as
the two `shows` clauses of `Theorem_21_3`.

## The decomposition

### parent `Theorem_21_3`: [`tst/i/Top1_Ch2.thy` lines 17155-17209](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/i/Top1_Ch2.thy#L17155-L17209) ([local copy](code/tst/i/Top1_Ch2.thy))

```isabelle
theorem Theorem_21_3:
  assumes hTX: "is_topology_on X TX"
  assumes hTY: "is_topology_on Y TY"
  assumes hmap: "\<forall>x\<in>X. f x \<in> Y"
  shows "top1_continuous_map_on X TX Y TY f
          \<longrightarrow> (\<forall>s x. seq_converges_to_on s x X TX
                 \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY)"
    and "top1_metrizable_on X TX
          \<longrightarrow> (\<forall>s x. seq_converges_to_on s x X TX
                 \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY)
          \<longrightarrow> top1_continuous_map_on X TX Y TY f"
proof -
  show "top1_continuous_map_on X TX Y TY f
          \<longrightarrow> (\<forall>s x. seq_converges_to_on s x X TX
                 \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY)"
  proof
    assume hcont: "top1_continuous_map_on X TX Y TY f"
    show "\<forall>s x. seq_converges_to_on s x X TX
            \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY"
    proof (intro allI impI)
      fix s x
      assume hx: "seq_converges_to_on s x X TX"
      show "seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY"
        by (rule Theorem_21_3_forward[OF hTX hTY hcont hx])
    qed
  qed

  show "top1_metrizable_on X TX
          \<longrightarrow> (\<forall>s x. seq_converges_to_on s x X TX
                 \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY)
          \<longrightarrow> top1_continuous_map_on X TX Y TY f"
  proof (intro impI)
    assume hmet: "top1_metrizable_on X TX"
    assume hseq:
      "\<forall>s x. seq_converges_to_on s x X TX
            \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY"
    obtain d where hd: "top1_metric_on X d" and hTXeq: "TX = top1_metric_topology_on X d"
      using hmet unfolding top1_metrizable_on_def by blast
    have hseq': "\<forall>s x. seq_converges_to_on s x X (top1_metric_topology_on X d)
            \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY"
    proof (intro allI impI)
      fix s x
      assume hs: "seq_converges_to_on s x X (top1_metric_topology_on X d)"
      have hsTX: "seq_converges_to_on s x X TX"
        unfolding hTXeq by (rule hs)
      show "seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY"
        using hseq hsTX by blast
    qed
    have hcont:
      "top1_continuous_map_on X (top1_metric_topology_on X d) Y TY f"
      by (rule Theorem_21_3_converse_metric[OF hd hTY hmap hseq'])
    show "top1_continuous_map_on X TX Y TY f"
      unfolding hTXeq using hcont by simp
  qed
qed
```

### child `Theorem_21_3_forward`: [`tst/i/Top1_Ch2.thy` lines 17055-17096](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/i/Top1_Ch2.thy#L17055-L17096) ([local copy](code/tst/i/Top1_Ch2.thy))

```isabelle
theorem Theorem_21_3_forward:
  assumes hTX: "is_topology_on X TX"
  assumes hTY: "is_topology_on Y TY"
  assumes hcont: "top1_continuous_map_on X TX Y TY f"
  assumes hx: "seq_converges_to_on s x X TX"
  shows "seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY"
proof -
  have hmap: "\<forall>x\<in>X. f x \<in> Y"
    using hcont unfolding top1_continuous_map_on_def by blast
  have hxX: "x \<in> X"
    using hx unfolding seq_converges_to_on_def by blast
  have hfxY: "f x \<in> Y"
    using hmap hxX by blast
  show ?thesis
    unfolding seq_converges_to_on_def
  proof (intro conjI)
    show "f x \<in> Y" by (rule hfxY)
    show "\<forall>V. neighborhood_of (f x) Y TY V \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. f (s n) \<in> V)"
    proof (intro allI impI)
      fix V assume hV: "neighborhood_of (f x) Y TY V"
      have hVTY: "V \<in> TY" and hfxV: "f x \<in> V"
        using hV unfolding neighborhood_of_def by blast+
      have hpre: "{u\<in>X. f u \<in> V} \<in> TX"
        using hcont hVTY unfolding top1_continuous_map_on_def by blast
      have hnbhd: "neighborhood_of x X TX {u\<in>X. f u \<in> V}"
        unfolding neighborhood_of_def using hpre hxX hfxV by simp
      obtain N where hN: "\<forall>n\<ge>N. s n \<in> {u\<in>X. f u \<in> V}"
        using hx hnbhd unfolding seq_converges_to_on_def by blast
      show "\<exists>N. \<forall>n\<ge>N. f (s n) \<in> V"
      proof (rule exI[where x=N])
        show "\<forall>n\<ge>N. f (s n) \<in> V"
        proof (intro allI impI)
          fix n assume hn: "n \<ge> N"
          have "s n \<in> {u\<in>X. f u \<in> V}"
            using hN hn by blast
          thus "f (s n) \<in> V"
            by simp
        qed
      qed
    qed
  qed
qed
```

### child `Theorem_21_3_converse_metric`: [`tst/i/Top1_Ch2.thy` lines 17098-17152](https://github.com/JUrban/isa_top_autoform1/blob/90d108779e83453e9cae2f55b513246e1cc044e0/tst/i/Top1_Ch2.thy#L17098-L17152) ([local copy](code/tst/i/Top1_Ch2.thy))

```isabelle
theorem Theorem_21_3_converse_metric:
  assumes hd: "top1_metric_on X d"
  assumes hTY: "is_topology_on Y TY"
  assumes hmap: "\<forall>x\<in>X. f x \<in> Y"
  assumes hseq:
    "\<forall>s x. seq_converges_to_on s x X (top1_metric_topology_on X d)
          \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY"
  shows "top1_continuous_map_on X (top1_metric_topology_on X d) Y TY f"
proof -
  have hTX: "is_topology_on X (top1_metric_topology_on X d)"
    by (rule top1_metric_topology_on_is_topology_on[OF hd])
  have hclosure:
    "\<forall>A. A \<subseteq> X \<longrightarrow> f ` closure_on X (top1_metric_topology_on X d) A \<subseteq> closure_on Y TY (f ` A)"
  proof (intro allI impI)
    fix A assume hAX: "A \<subseteq> X"
    show "f ` closure_on X (top1_metric_topology_on X d) A \<subseteq> closure_on Y TY (f ` A)"
    proof (rule subsetI)
      fix y assume hy: "y \<in> f ` closure_on X (top1_metric_topology_on X d) A"
      obtain x where hxcl: "x \<in> closure_on X (top1_metric_topology_on X d) A" and hyfx: "y = f x"
        using hy by blast
      obtain s where hsA: "\<forall>n. s n \<in> A"
          and hsconv: "seq_converges_to_on s x X (top1_metric_topology_on X d)"
        using Lemma_21_2_sequence_converse[OF hd hxcl hAX] by blast
      have hconvY: "seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY"
        using hseq hsconv by blast
      have hs_in: "\<forall>n. f (s n) \<in> f ` A"
      proof (intro allI)
        fix n
        have "s n \<in> A" using hsA by blast
        thus "f (s n) \<in> f ` A"
          by (rule imageI)
      qed
      have himg_sub: "f ` A \<subseteq> Y"
      proof (rule subsetI)
        fix y assume hy: "y \<in> f ` A"
        obtain a where haA: "a \<in> A" and hyfa: "y = f a"
          using hy by blast
        have haX: "a \<in> X" using hAX haA by blast
        have "f a \<in> Y" using hmap haX by blast
        thus "y \<in> Y" using hyfa by simp
      qed
      have hclY: "f x \<in> closure_on Y TY (f ` A)"
        by (rule Lemma_21_2_sequence[OF hTY hconvY hs_in himg_sub])
      show "y \<in> closure_on Y TY (f ` A)"
        using hclY hyfx by simp
    qed
  qed

  have "top1_continuous_map_on X (top1_metric_topology_on X d) Y TY f
        \<longleftrightarrow> ((\<forall>x\<in>X. f x \<in> Y) \<and>
             (\<forall>A. A \<subseteq> X \<longrightarrow> f ` closure_on X (top1_metric_topology_on X d) A \<subseteq> closure_on Y TY (f ` A)))"
    by (rule Theorem_18_1(1)[OF hTX hTY])
  thus ?thesis
    using hmap hclosure by blast
qed
```

The parent `Theorem_21_3` states the characterization as two implications (the
second under `top1_metrizable_on X TX`), and its proof is the glue: each `show`
is discharged by one application of a named lemma. The forward `show` is closed
by `by (rule Theorem_21_3_forward[OF hTX hTY hcont hx])`; the converse `show`
unfolds `top1_metrizable_on_def` to obtain a metric `d`, re-wraps the sequential
hypothesis over `top1_metric_topology_on X d` (as `hseq'`), and closes by
`by (rule Theorem_21_3_converse_metric[OF hd hTY hmap hseq'])`.

Lemma graph (which lemma the glue cites, and what each child cites in turn):

    Theorem_21_3 (glue)
     ├─ Theorem_21_3_forward                    (line 17178)
     └─ Theorem_21_3_converse_metric            (line 17205)
         ├─ top1_metric_topology_on_is_topology_on  (line 17107)
         ├─ Lemma_21_2_sequence_converse             (line 17120)
         ├─ Lemma_21_2_sequence                      (line 17140)
         └─ Theorem_18_1(1)                          (line 17149)

Why each lemma is a good leaf:

* `Theorem_21_3_forward` is self-contained: its proof never cites a project
  lemma; it unfolds `top1_continuous_map_on_def`, `seq_converges_to_on_def` and
  `neighborhood_of_def` and closes each conjunct from the local hypotheses with
  `blast`/`simp`. A bounded prover can close it on its own.
* `Theorem_21_3_converse_metric` closes from named siblings only: it proves the
  closure criterion for continuity (`Theorem_18_1(1)`) and then derives the
  closure inclusion from the two sequence lemmas. It does not re-prove their
  contents; it wires them to the criterion.

## Why it is good

1. The glue cites both child lemmas, each by a single `rule` application:
   `Theorem_21_3_forward` at line 17178 and `Theorem_21_3_converse_metric` at
   line 17205 (check, machine-decided by `cites`).
2. The parent and both children contain no `sorry` (check, machine-decided by
   `no_sorry` over lines 17055-17209).
3. The shape, measured from the copied file: glue 55 lines, children 42 and 55
   lines, and the longest checked chain of project lemmas below the theorem is
   3 deep (measurement; see claim 4 in `entry.json` for the citation walk).
4. The same bidirectional split — two implications, each glued from a named
   lemma — is used for the Sequence lemma immediately above, `Lemma_21_2`
   (lines 17012-17052), which shows its two directions by
   `Lemma_21_2_sequence` and `Lemma_21_2_sequence_converse` (known-use).

In my opinion the detail worth copying is that the metrizability hypothesis is
confined to the converse child: the forward direction is stated unconditionally,
so the split does not weaken the clean direction with a side condition it never
uses.

## When to use it, and when not

Use it when the goal is a characterization `P ⟺ Q` (or two implications) whose
two directions need different arguments, and especially when one direction needs
an extra hypothesis — metrizability here — that the other direction does not.
State each direction as its own named lemma, so the glue is two `rule`
applications.

Avoid it when a single argument proves both directions (then state one lemma),
when the two directions share so much that a plain `iffI`/`intro` with no
intermediate lemmas is clearer, or when the side condition must be threaded
through the whole theorem instead of being isolated in one child.

## Consequences

Splitting a characterization into two named lemmas obliges the glue to state
each `shows` clause exactly matching a lemma's conclusion, and to feed each
lemma the hypotheses it lists (`hTX`, `hTY`, `hcont`, `hx` for the forward;
`hd`, `hTY`, `hmap`, `hseq'` for the converse). The converse direction forces
the metrizability hypothesis into its own child, so the glue must first unfold
`top1_metrizable_on_def` to obtain a metric `d`, then re-wrap the sequential
hypothesis over the metric topology (`hseq'`) before applying the converse
lemma. The failure mode to watch for: if the side condition is not isolated in
its own child, the unconditional forward direction would also carry it,
weakening the theorem.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: Theorem_21_3_forward@tst/i/Top1_Ch2.thy:17178, Theorem_21_3_converse_metric@tst/i/Top1_Ch2.thy:17205; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, Theorem_21_3_forward) -> cites: Theorem_21_3_forward occurs at tst/i/Top1_Ch2.thy:17178 | check_claims.py |
| 2 | verified | cites(parent, Theorem_21_3_converse_metric) -> cites: Theorem_21_3_converse_metric occurs at tst/i/Top1_Ch2.thy:17205 | check_claims.py |
| 3 | verified | no_sorry(tst/i/Top1_Ch2.thy, 17055-17209) -> no_sorry: none of sorry in tst/i/Top1_Ch2.thy:17055-17209 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/JUrban/isa_top_autoform1 at commit `90d108779e83453e9cae2f55b513246e1cc044e0`, under `LicenseRef-unknown`; see the [source note](../../sources/munkres-isabelle/SOURCE.md) for the licence text and attribution.
