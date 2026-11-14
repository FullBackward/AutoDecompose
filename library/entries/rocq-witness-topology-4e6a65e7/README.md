# Banach fixed point from a Cauchy sequence's complete limit

| | |
|---|---|
| Kind | instance |
| Move | witness |
| Language | rocq |
| Status | accepted |
| Source | [topology](../../sources/topology/SOURCE.md) at `1e898b95f68f` |
| Licence | `LGPL-2.1` |

## Intent

A contraction `T` on a complete metric space has a unique fixed point. The proof
obtains the witness `x` by applying completeness `Hd_comp` to the iterated
sequence `BanachFixedPoint_seq x0`, whose Cauchy property is a named lemma; a
second named lemma shows the limit is fixed, and a third shows any two fixed
points agree, so the 16-line glue only names `x` and splits existence from
uniqueness.

## The decomposition

### parent `BanachFixedPoint`: [`theories/Topology/BanachFixedPoint.v` lines 473-488](https://github.com/rocq-community/topology/blob/1e898b95f68f9ce75bf44faa8446992b03c84052/theories/Topology/BanachFixedPoint.v#L473-L488) ([local copy](code/theories/Topology/BanachFixedPoint.v))

```coq
  Theorem BanachFixedPoint :
    inhabited X ->
    exists! x : X, T x = x.
  Proof.
    intros [x0].
    (* consider [BanachFixedPoint_seq_cauchy] and obtain its
      limit-point using completeness of [X].
      The fancy invocation is needed, to immediately obtain a [net_limit].
     *)
    specialize (Hd_comp (BanachFixedPoint_seq x0)
                  (BanachFixedPoint_seq_cauchy x0)) as [x Hx].
    apply metric_space_net_limit in Hx; auto.
    exists x. apply BanachFixedPoint_seq_limit_fixed in Hx.
    split; auto.
    intros. apply BanachFixedPoint_unique; auto.
  Qed.
```

### child `BanachFixedPoint_unique`: [`theories/Topology/BanachFixedPoint.v` lines 277-289](https://github.com/rocq-community/topology/blob/1e898b95f68f9ce75bf44faa8446992b03c84052/theories/Topology/BanachFixedPoint.v#L277-L289) ([local copy](code/theories/Topology/BanachFixedPoint.v))

```coq
  Lemma BanachFixedPoint_unique (x1 x2 : X) :
    T x1 = x1 -> T x2 = x2 -> x1 = x2.
  Proof.
    intros Hx1 Hx2.
    apply (metric_strict d_metric).
    specialize (HT x1 x2).
    rewrite Hx1, Hx2 in HT. clear Hx1 Hx2 T.
    pose proof (metric_nonneg d_metric x1 x2) as Hnneg.
    (* reduce the problem to algebra in [R]. [D := d x1 x2] *)
    remember (d x1 x2) as D. clear HeqD x1 x2 X d d_metric d_metrizes Hd_comp.
    apply Rle_antisym; try lra.
    apply Rle0_char' in HT; auto.
  Qed.
```

### child `BanachFixedPoint_seq_cauchy`: [`theories/Topology/BanachFixedPoint.v` lines 349-427](https://github.com/rocq-community/topology/blob/1e898b95f68f9ce75bf44faa8446992b03c84052/theories/Topology/BanachFixedPoint.v#L349-L427) ([local copy](code/theories/Topology/BanachFixedPoint.v))

```coq
  Local Lemma BanachFixedPoint_seq_cauchy (x : X) :
    cauchy d (BanachFixedPoint_seq x).
  Proof.
    (* do a case distinction, if [T x = x], since we want to
       divide by [d (T x) x] *)
    destruct (Req_dec 0 (d (T x) x)) as [Hx|Hx].
    { (* [T x = x], hence the sequence is constant. *)
      symmetry in Hx; apply metric_strict in Hx; auto.
      intros eps Heps.
      exists 0%nat. intros m n _ _.
      unfold BanachFixedPoint_seq.
      rewrite !Nat_iter_fix; auto.
      rewrite metric_zero; auto.
    }
    intros eps Heps.
    assert
      (exists N : nat,
          q^N < (eps * (1 - q))/(d (T x) x))
      as [N HN].
    { unshelve epose proof
        (pow_lt_1_zero q _ (eps * (1 - q) / d (T x) x) _) as [N HN].
      { rewrite Rabs_right; lra. }
      { apply Rmult_lt_0_compat.
        - apply Rmult_lt_0_compat; lra.
        - apply Rinv_0_lt_compat.
          pose proof (metric_nonneg d_metric (T x) x).
          lra.
      }
      exists N. specialize (HN N ltac:(lia)).
      rewrite Rabs_right in HN; auto.
      apply Rle_ge. apply pow_le. lra.
    }
    exists N.
    (* w.l.o.g. one of [m, n] is bigger than the other … *)
    cut
      (forall m n : nat,
          (n >= N)%nat ->
          d (BanachFixedPoint_seq x n)
            (BanachFixedPoint_seq x (m + n)) < eps).
    { intros H0.
      intros m n Hm Hn.
      destruct (Compare.le_dec m n) as [Hmn|Hnm].
      - destruct (Nat.le_exists_sub
                    m n Hmn) as [k [? _]].
        subst n. apply H0. assumption.
      - destruct (Nat.le_exists_sub
                    n m Hnm) as [k [? _]].
        subst m.
        rewrite metric_sym; try assumption.
        apply H0. assumption.
    }
    intros m n Hn.
    eapply Rle_lt_trans.
    { apply BanachFixedPoint_seq_dist_add. }
    (* some algebra of real numbers … *)

    assert (0 < d (T x) x) as Hx_pos. (* as a helper *)
    { pose proof (metric_nonneg d_metric (T x) x).
      lra.
    }

    (* remove all divisions. first in the goal, then in [HN] *)
    apply Rmult_lt_reg_r with (r := (1 - q)).
    1: lra.
    rewrite !Rmult_assoc.
    rewrite Rinv_l; [|lra]; rewrite Rmult_1_r.

    apply Rmult_lt_compat_l with (r := d (T x) x) in HN; auto.
    rewrite (Rmult_comm (d _ _) (_ / _)) in HN.
    rewrite Rdiv_mult_cancel_r in HN; auto.

    (* make the goal and [HN] match in structure. Note that [n] vs.
      [N] is the only difference. *)
    rewrite (Rmult_comm (q ^ n)).
    (* end proof *)
    apply Rle_lt_trans with (r2 := d (T x) x * q ^ N); auto.
    apply Rmult_le_compat_l; [lra|].
    apply Rle_pow_pos_lt_1; auto.
  Qed.
```

### child `BanachFixedPoint_seq_limit_fixed`: [`theories/Topology/BanachFixedPoint.v` lines 456-471](https://github.com/rocq-community/topology/blob/1e898b95f68f9ce75bf44faa8446992b03c84052/theories/Topology/BanachFixedPoint.v#L456-L471) ([local copy](code/theories/Topology/BanachFixedPoint.v))

```coq
  Local Lemma BanachFixedPoint_seq_limit_fixed (x0 x : X) :
    @net_limit nat_DS X (BanachFixedPoint_seq x0) x ->
    T x = x.
  Proof.
    intros Hx.
    unshelve epose proof
      (continuous_func_preserves_net_limits
         X X T _ x Hx _) as HTx.
    { apply continuous_func_continuous_everywhere.
      eapply Lipschitz_impl_continuous.
      6: eassumption. all: auto. apply Hq.
    }
    symmetry.
    apply BanachFixedPoint_seq_net_limit_shift with (x0 := x0);
      assumption.
  Qed.
```

### context `BanachFixedPoint_section`: [`theories/Topology/BanachFixedPoint.v` lines 262-275](https://github.com/rocq-community/topology/blob/1e898b95f68f9ce75bf44faa8446992b03c84052/theories/Topology/BanachFixedPoint.v#L262-L275) ([local copy](code/theories/Topology/BanachFixedPoint.v))

```coq
(** ** Banach Fixed Point Theorem
  Proof taken from https://en.wikipedia.org/wiki/Banach_fixed-point_theorem
 *)
Section BanachFixedPoint.
  Context
    {X : TopologicalSpace}
      (d : X -> X -> R)
      (d_metric : metric d)
      (d_metrizes : metrizes X d)
      (Hd_comp : complete d)
      (T : X -> X)
      {q : R}
      (Hq : 0 <= q < 1)
      (HT : Lipschitz d d T q).
```

How the parts fit. The glue (parent, lines 473-488) has the shape

```
BanachFixedPoint_seq_cauchy (child) ──▶ Hd_comp (complete) ──▶ witness x
   metric_space_net_limit (imported) ──▶ net_limit
BanachFixedPoint_seq_limit_fixed (child) ──▶ T x = x        (existence)
BanachFixedPoint_unique (child) ──▶ uniqueness
```

`specialize (Hd_comp (BanachFixedPoint_seq x0) (BanachFixedPoint_seq_cauchy x0))`
feeds the Cauchy certificate to completeness to obtain the witness `[x Hx]`;
`apply metric_space_net_limit` turns the completeness limit into a `net_limit`;
`apply BanachFixedPoint_seq_limit_fixed in Hx` shows `T x = x` (existence);
`split; intros; apply BanachFixedPoint_unique` proves the uniqueness clause of
`exists!`. Each child is a leaf whose proof closes on its own or from named
siblings:

- `BanachFixedPoint_unique` (277-289) closes from the section hypotheses alone:
  `metric_strict` reduces `x1 = x2` to `d x1 x2 = 0`, `HT` (Lipschitz) at `x1 x2`
  gives `d x1 x2 <= q * d x1 x2`, and the local `Rle0_char'` (191-221) turns that
  into `d x1 x2 <= 0` under `0 <= q < 1`, closed by `Rle_antisym`/`lra`.

- `BanachFixedPoint_seq_cauchy` (349-427) is the long leaf: it splits on
  `Req_dec 0 (d (T x) x)`; the constant case is closed by `Nat_iter_fix` and
  `metric_zero`, and the general case bounds the distance by
  `BanachFixedPoint_seq_dist_add` (312-347, itself built from the step bound
  `BanachFixedPoint_seq_dist_succ` 295-309 and the geometric bound
  `Rsum_geometric_upper_bound`) and closes with `Rle_pow_pos_lt_1`.

- `BanachFixedPoint_seq_limit_fixed` (456-471) shows the net-limit of the
  sequence is a fixed point: it uses `continuous_func_preserves_net_limits`
  (via `Lipschitz_impl_continuous`) to get `T` of the limit, then
  `BanachFixedPoint_seq_net_limit_shift` (436-454) to identify it with the limit.

The three leaves are self-contained statements: each is proved inside the same
`Section BanachFixedPoint` (context 262-275) and none depends on the parent or
on the other two children, so the glue is a pure assembly.

## Why it is good

1. The glue cites the Cauchy child directly: `BanachFixedPoint_seq_cauchy`
   occurs in the parent site (lines 473-488) — `check`, decided by
   `cites(parent, BanachFixedPoint_seq_cauchy)`.
2. The copied file closes everywhere: no `admit`, `Admitted`, `Axiom` or
   `axiom` token occurs in lines 1-489 of the file — `check`,
   `no_sorry(theories/Topology/BanachFixedPoint.v, 1-489)`.
3. The shape is theorem-scale with 3 direct lemmas and depth 3 (the Cauchy leaf
   chains down through `BanachFixedPoint_seq_dist_add` to
   `BanachFixedPoint_seq_dist_succ`), 16 lines of glue and child proofs of 13,
   79 and 16 lines — `measurement`, counted from the copied file.
4. The authors state the construction in a comment above the glue: "consider
   [BanachFixedPoint_seq_cauchy] and obtain its limit-point using completeness of
   [X]. The fancy invocation is needed, to immediately obtain a [net_limit]."
   (lines 478-481) — `author-statement`.

In my opinion the detail worth copying is that the glue keeps one imported
bridge — `metric_space_net_limit` — visible rather than hiding that `complete`
yields a metric-space limit while the fixed-point lemma is phrased for a
`net_limit`; a decomposition that omitted that bridge would not assemble.

## When to use it, and when not

Use it when the goal is `exists! x : X, P x` (or `exists x : X, P x`) and the
witness is produced by a construction that carries its own certificate — here
the Cauchy property of the iterated sequence, which completeness consumes. The
move pays off when existence and uniqueness are already separate named lemmas,
so the glue is naming plus one split. Avoid it when the witness's properties are
not already lemmas (then the glue carries the real mathematics), when existence
and uniqueness need hypotheses the other does not, or when the construction's
certificate cannot be stated without first naming the witness.

## Consequences

The move creates two obligations — the witness satisfies `P`, and any two
satisfiers are equal — plus a side certificate: here `BanachFixedPoint_seq x0`
must be shown Cauchy before `Hd_comp` yields the witness, and completeness's
metric-space limit must be converted to a `net_limit` (by the imported
`metric_space_net_limit`) so the fixed-point child applies. Failure modes: the
bridge between the construction's limit and the child's stated form can be
missed; and if the Cauchy child's internal case split (`T x = x` or not) leaks
into the glue, the assembly stops being a pure witness naming.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/docker-action.yml builds coq-topology (opam install -y coq-topology), which compiles theories/Topology/BanachFixedPoint.v, on push to default branch master; pinned commit 1e898b95f68f9ce75bf44faa8446992b03c84052 is on master (GitHub API branches-where-head) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: BanachFixedPoint_unique@theories/Topology/BanachFixedPoint.v:487, BanachFixedPoint_seq_cauchy@theories/Topology/BanachFixedPoint.v:478, BanachFixedPoint_seq_limit_fixed@theories/Topology/BanachFixedPoint.v:485; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 1e898b95f68f9ce75bf44faa8446992b03c84052 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(parent, BanachFixedPoint_seq_cauchy) -> cites: BanachFixedPoint_seq_cauchy occurs at theories/Topology/BanachFixedPoint.v:478 | check_claims.py |
| 2 | verified | no_sorry(theories/Topology/BanachFixedPoint.v, 1-489) -> no_sorry: none of admit, Admitted, Axiom, axiom in theories/Topology/BanachFixedPoint.v:1-489 | check_claims.py |
| 3 | verified | read code/theories/Topology/BanachFixedPoint.v: parent 473-488 = 16 lines; child spans 277-289 (13), 349-427 (79), 456-471 (16); direct_lemmas=3 = the 3 children; depth chain BanachFixedPoint (cites seq_cauchy:483, seq_limit_fixed:485, unique:487) -> seq_cauchy cites seq_dist_add at :402 -> seq_dist_add cites seq_dist_succ at :341 -> seq_dist_succ 295-309 | verifier |
| 4 | verified | read code/theories/Topology/BanachFixedPoint.v lines 478-481: comment reads 'consider [BanachFixedPoint_seq_cauchy] and obtain its limit-point using completeness of [X]. The fancy invocation is needed, to immediately obtain a [net_limit].' matching the quoted author-statement | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Correctness verified: glue (BanachFixedPoint.v:473-488) cites exactly three named lemmas from the section — BanachFixedPoint_seq_cauchy (478/483), BanachFixedPoint_seq_limit_fixed (485), BanachFixedPoint_unique (487) — matching the three children; metric_space_net_limit is imported and correctly not a child. Child statements and closed_by match the copied code verbatim (unique ends 'apply Rle0_char' in HT; auto', seq_cauchy ends 'apply Rle_pow_pos_lt_1; auto' with the constant case via Nat_iter_fix/metric_zero, seq_limit_fixed ends 'apply BanachFixedPoint_seq_net_limit_shift with (x0 := x0); assumption'). All three children close with Qed and no admit/Admitted/Axiom tokens exist in the file, so it closes. Shape numbers checked against the copy: direct_lemmas=3 (the three glue-cited lemmas), depth=3 (BanachFixedPoint -> seq_cauchy 349-427 -> seq_dist_add 312-347 -> seq_dist_succ 295-309), glue_lines=16 (473-488), child_lines=[13,79,16] (277-289, 349-427, 456-471) — all correct. Author comment at 478-481 matches claim 4. | reviewer-correctness |
| generality | accept | Move generalises beyond the example: stated for exists! x, P x (or exists x, P x) with a witness from a construction carrying its own certificate (Cauchy -> completeness), not just the Banach theorem; applicability/use_when fields repeat this at generic level. 'Avoid when' is specific and honest (properties not pre-factored into lemmas; existence/uniqueness needing unshared hypotheses; certificate not statable before naming the witness). Consequences name concrete obligations (Cauchy certificate, net_limit bridge) and concrete failure modes (missed bridge; case-split leak), and are honest about the 79-line Cauchy leaf and depth-3 chain rather than hiding them. Good-leaves question answered in substance: leaves are self-contained statements proved in the section context, none depending on the parent or the other two children, so glue is pure assembly (verified against code 262-289, 456-488, 295-349); independence + section-context hypotheses is what lets a bounded prover fill each hole. Minor note (not an objection): the entry never uses 'bounded prover' wording nor confronts that the Cauchy leaf is itself 79 lines with internal sub-lemmas, though it records sizes/depth honestly in shape. | reviewer-generality |
| provenance-licence | accept | Provenance and licence are consistent and traceable. check_provenance.py passes: 1 file byte-identical at commit 1e898b95f68f9ce75bf44faa8446992b03c84052. Commit, licence and repo are consistent across entry.json (source.commit=1e898b95f68f9ce75bf44faa8446992b03c84052, licence=LGPL-2.1), README.md, sources/topology/SOURCE.md, and sources/topology/source.json. All permalinks point to github.com/rocq-community/topology/blob/1e898b95f68f9ce75bf44faa8446992b03c84052/theories/Topology/BanachFixedPoint.v with line anchors matching the copied file's content (parent 473-488, context 262-275 verified by sed). Copied file code/theories/Topology/BanachFixedPoint.v is 13659 bytes, matching entry.json files[].bytes. The upstream LICENSE (sources/topology/upstream-LICENSE) states LGPL-2.1, matching the recorded licence. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/rocq-community/topology at commit `1e898b95f68f9ce75bf44faa8446992b03c84052`, under `LGPL-2.1`; see the [source note](../../sources/topology/SOURCE.md) for the licence text and attribution.
