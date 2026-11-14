# Sorrify-at-failure in the failed Tapir to SSER refinement (tapir_refines_sser)

| | |
|---|---|
| Kind | anti-pattern |
| Move | sorrify-at-failure |
| Language | isabelle |
| Status | draft |
| Source | [veriso](../../sources/veriso/SOURCE.md) at `6407b7205c3b` |
| Licence | `LicenseRef-unknown` |

## Intent

Records the Section 6.3 falsification attempt for Tapir: the author tries to
prove `tapir_refines_sser` (`tapir` refines `ET_SSER.ET_ES` up to `sim` and
`med`) by a simulation induction over events, and the four per-event
`abs_committed_reads` bookkeeping lemmas close — but the harder obligations
(the `fp_property` and `kvs_of_s` update of client commit, and the `Cl_ReadyC`,
`Commit`, `Abort` cases) are left as `sorry` with comments naming the invariant
still needed. The entry records which children of the decomposition were
sufficient and which were not, and why.

## The decomposition

### parent `tapir_refines_sser`: [`VerIso/Tapir_Falsification.thy` lines 434-563](https://github.com/shabnamrad/veriso/blob/6407b7205c3bfc4adc62e758795a7fc5142efb33/VerIso/Tapir_Falsification.thy#L434-L563) ([local copy](code/VerIso/Tapir_Falsification.thy))

```isabelle
lemma tapir_refines_sser: "tapir \<sqsubseteq>\<^bsub>[sim,med]\<^esub> ET_SSER.ET_ES"
proof (intro simulate_ES_fun_h)
  fix gs0 :: "'v global_conf"
  assume p: "init tapir gs0"
  then show "init ET_SSER.ET_ES (sim gs0)"
    by (auto simp add: ET_SSER.ET_ES_defs tapir_defs sim_all_defs kvs_init_def v_list_init_def 
                       version_init_def)
next
  fix gs a and gs' :: "'v global_conf"
  assume p: "tapir: gs\<midarrow>a\<rightarrow> gs'" and reach_s: "reach tapir gs" and "reach ET_SSER.ET_ES (sim gs)"
  then have reach_s': "reach tapir gs'" by auto
  with reach_s have I: "invariants_list gs" and I': "invariants_list gs'" by auto
  with p show "ET_SSER.ET_ES: sim gs\<midarrow>med a\<rightarrow> sim gs'"
  proof (induction a)
    case (Cl_Commit cl sn u'' F ts r_map w_map)
    show ?case 
    proof -
      { 
        assume cmt: \<open>cl_commit cl sn u'' F ts r_map w_map gs gs'\<close>
        have \<open>ET_SSER.ET_trans_and_fp 
                (kvs_of_s gs, views_of_s gs) (ET cl sn u'' F) (kvs_of_s gs', views_of_s gs')\<close>
        proof (rule ET_SSER.ET_trans_rule [where u'="view_init"])
          show \<open>views_of_s gs cl \<sqsubseteq> u''\<close> using cmt reach_s
            by (auto simp add: cl_commit_def views_of_s_def)
        next 
          show \<open>ET_SSER.canCommit (kvs_of_s gs) u'' F\<close> using cmt
            by (auto simp add: cl_commit_def full_view_satisfies_ET_SSER_canCommit)
        next 
          show \<open>view_wellformed (kvs_of_s gs) u''\<close> using cmt reach_s
            by (auto simp add: cl_commit_def)
        next 
          show \<open>view_wellformed (kvs_of_s gs') view_init\<close> using cmt reach_s' by auto
        next 
          show \<open>view_wellformed (kvs_of_s gs) (views_of_s gs cl)\<close> using reach_s
            by (auto simp add: views_of_s_def)
        next 
          show \<open>Tn_cl sn cl \<in> next_txids (kvs_of_s gs) cl\<close> using cmt I
            (* by (auto simp add: cl_commit_def t_is_fresh) (* provable *) *) sorry
        next 
          show \<open>fp_property F (kvs_of_s gs) u''\<close> unfolding fp_property_def
          proof (intro allI impI)
            fix k
            assume "R \<in> dom (F k)"
            then obtain t_wr where "r_map k = Some t_wr" using cmt
              apply (auto simp add: cl_commit_def)
              using \<open>R \<in> dom (F k)\<close> domIff fun_upd_apply op_type.distinct(1) by force
            then obtain ts' rto' v where "svr_state (svrs gs k) t_wr = committed ts' rto' (Some v)"
              using cmt reach_s Read_Twr_Cmt_def[of gs]
              apply (auto simp add: cl_commit_def)
              by (metis Un_iff domI is_committed_wr.elims(2))
            then show "F k R = Some (view_snapshot (kvs_of_s gs) u'' k)"
              using cmt \<open>r_map k = Some t_wr\<close>
              apply (auto simp add: cl_commit_def view_snapshot_def)
              (* need to prove:
                - no transactions after t_wr have written a new version to server k \<Rightarrow> unprovable!
                - no prepared (but client-committed) newer versions are on server k \<Rightarrow> unprovable! *)
              sorry
          qed
        next 
          show \<open>kvs_of_s gs' = update_kv (Tn_cl sn cl) F u'' (kvs_of_s gs)\<close> using cmt I (* provable *) sorry
        next 
          show \<open>views_of_s gs' = (views_of_s gs) (cl := view_init)\<close>
            by (auto simp add: views_of_s_def)
        qed simp
      }
      then show ?thesis using Cl_Commit
        by (simp only: ET_SSER.trans_ET_ES_eq tapir_trans s_trans.simps sim_def med.simps)
    qed
  next
    case (Cl_Issue x1 x2 x3)
    then show ?case
      apply (auto simp add: sim_def tapir_trans_defs)
      by (rule ext, auto simp add: sim_all_defs split: svr_state.split option.split)
  next
    case (Cl_Read_Resp x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: sim_def tapir_trans_defs)
      by (rule ext, auto simp add: sim_all_defs split: svr_state.split option.split)
  next
    case (Cl_Prep x1 x2 x3 x4)
    then show ?case
      apply (auto simp add: sim_def tapir_trans_defs)
      by (rule ext, auto simp add: sim_all_defs split: svr_state.split option.split)
  next
    case (Cl_Abort x)
    then show ?case
      apply (auto simp add: sim_def tapir_trans_defs)
      by (rule ext, auto simp add: sim_all_defs split: svr_state.split option.split)+
  next
    case (Cl_ReadyC x1 x2)
    then show ?case
      apply (auto simp add: sim_def tapir_trans_defs)
       apply (rule ext, auto simp add: sim_all_defs split: svr_state.split option.split)
      (* inv: new (uncommitted) write is not read by any transactions *) sorry
  next
    case (Cl_ReadyA x1 x2)
    then show ?case
      apply (auto simp add: sim_def tapir_trans_defs)
      by (rule ext, auto simp add: sim_all_defs split: svr_state.split option.split)
  next
    case (Read_Resp x1 x2 x3)
    then show ?case
      using read_resp_abs_committed_reads_inv[of gs]
      apply (auto simp add: sim_defs tapir_trans_defs)
      by (rule ext, auto split: svr_state.split)
  next
    case (Prep x1 x2 x3 x4 x5)
    then show ?case
      using prep_abs_committed_reads_inv[of gs] CO_Tid_def[of gs] reach_s
      apply (auto simp add: sim_defs tapir_trans_defs)
      apply (rule ext, auto split: svr_state.split)
      by (metis (no_types, lifting) cl_state.simps(26) nless_le txid0.collapse)
  next
    case (Commit x1 x2 x3 x4 x5)
    then show ?case
      using commit_abs_committed_reads_inv[of gs]
      apply (auto simp add: sim_defs tapir_trans_defs)
   (* apply (rule ext, auto split: svr_state.split)+
        inv: newly committed version's readerset is empty *)
      sorry
  next
    case (Abort x1 x2)
    then show ?case
      using abort_abs_committed_reads_inv[of gs]
      apply (auto simp add: sim_defs tapir_trans_defs)
   (* apply (rule ext, auto split: svr_state.split)+
        inv: aborted txn not in commit_order *)
      sorry
  qed simp                            
qed
```

### child `read_resp_abs_committed_reads_inv`: [`VerIso/Tapir_Falsification.thy` lines 18-25](https://github.com/shabnamrad/veriso/blob/6407b7205c3bfc4adc62e758795a7fc5142efb33/VerIso/Tapir_Falsification.thy#L18-L25) ([local copy](code/VerIso/Tapir_Falsification.thy))

```isabelle
lemma read_resp_abs_committed_reads_inv:
  assumes "svr_state (svrs s k) (Tn t) = idle"
  shows
    "abs_committed_reads (s \<lparr>svrs := (svrs s)
      (k := svrs s k \<lparr>svr_state := (svr_state (svrs s k)) (Tn t := read X)\<rparr>)\<rparr>) k' t_wr =
     abs_committed_reads s k' t_wr"
  using assms
  by (auto simp add: abs_committed_reads_def)
```

### child `prep_abs_committed_reads_inv`: [`VerIso/Tapir_Falsification.thy` lines 27-35](https://github.com/shabnamrad/veriso/blob/6407b7205c3bfc4adc62e758795a7fc5142efb33/VerIso/Tapir_Falsification.thy#L27-L35) ([local copy](code/VerIso/Tapir_Falsification.thy))

```isabelle
lemma prep_abs_committed_reads_inv:
  assumes "svr_state (svrs s k) (Tn t) = read X"
    and "cl_state (cls s (get_cl t)) = cl_prepared x y z"
  shows
    "abs_committed_reads (s \<lparr>svrs := (svrs s)
      (k := svrs s k \<lparr>svr_state := (svr_state (svrs s k)) (Tn t := occ_check a b c d e f)\<rparr>)\<rparr>) k' t_wr =
     abs_committed_reads s k' t_wr"
  using assms
  by (auto simp add: abs_committed_reads_def)
```

### child `commit_abs_committed_reads_inv`: [`VerIso/Tapir_Falsification.thy` lines 37-47](https://github.com/shabnamrad/veriso/blob/6407b7205c3bfc4adc62e758795a7fc5142efb33/VerIso/Tapir_Falsification.thy#L37-L47) ([local copy](code/VerIso/Tapir_Falsification.thy))

```isabelle
lemma commit_abs_committed_reads_inv:
  assumes "svr_state (svrs s k) (Tn t) = prepared ts rto wvo"
    and "cl_state (cls s (get_cl t)) = cl_committed ts r_map w_map"
    and "k \<in> dom r_map"
  shows
    "abs_committed_reads (s \<lparr>svrs := (svrs s)
      (k := svrs s k \<lparr>
        svr_state := (svr_state (svrs s k)) (Tn t := committed ts rto wvo)\<rparr>)\<rparr>) k' t_wr =
     abs_committed_reads s k' t_wr"
  using assms
  by (auto simp add: abs_committed_reads_def)
```

### child `abort_abs_committed_reads_inv`: [`VerIso/Tapir_Falsification.thy` lines 49-57](https://github.com/shabnamrad/veriso/blob/6407b7205c3bfc4adc62e758795a7fc5142efb33/VerIso/Tapir_Falsification.thy#L49-L57) ([local copy](code/VerIso/Tapir_Falsification.thy))

```isabelle
lemma abort_abs_committed_reads_inv:
  assumes "svr_state (svrs s k) (Tn t) \<in> {prepared a b c, aborted}"
    and "cl_state (cls s (get_cl t)) = cl_aborted"
  shows
    "abs_committed_reads (s \<lparr>svrs := (svrs s)
      (k := svrs s k \<lparr>svr_state := (svr_state (svrs s k)) (Tn t := aborted)\<rparr>)\<rparr>) k' t_wr =
     abs_committed_reads s k' t_wr"
  using assms
  by (auto simp add: abs_committed_reads_def)
```

### context `falsification-note`: [`Run.thy` lines 24-27](https://github.com/shabnamrad/veriso/blob/6407b7205c3bfc4adc62e758795a7fc5142efb33/Run.thy#L24-L27) ([local copy](code/Run.thy))

```isabelle
text \<open>Section 6.3\<close>

thm tapir_refines_sser
  \<comment> \<open>fails: checkout the proof state at line 486 (in Isabelle's "Output" tab)\<close>
```

How the parts fit. The parent `tapir_refines_sser` opens with
`intro simulate_ES_fun_h`, then `induction a` over the event constructors. The
`init` case closes by `auto` on the simulation and store definitions; most
event cases (`Cl_Issue`, `Cl_Read_Resp`, `Cl_Prep`, `Cl_ReadyA`, `Cl_Abort`)
close by `auto` + `rule ext` with no lemma. Four cases cite a named child:

```text
tapir_refines_sser
├── init case                     closed by auto (ET_SSER.ET_ES_defs, sim_all_defs)
└── induction over event a
    ├── Cl_Issue / Cl_Read_Resp / Cl_Prep / Cl_ReadyA / Cl_Abort   auto + ext
    ├── Read_Resp ── read_resp_abs_committed_reads_inv             closes
    ├── Prep      ── prep_abs_committed_reads_inv (+ CO_Tid_def)    closes
    ├── Commit    ── commit_abs_committed_reads_inv                still sorry ("readerset empty")
    ├── Abort     ── abort_abs_committed_reads_inv                 still sorry ("not in commit_order")
    ├── Cl_Commit ── sorry at next_txids, fp_property, kvs_of_s update
    └── Cl_ReadyC ── sorry ("new uncommitted write is not read")
```

Each child is a good leaf in exactly the same shape: it states that a single
state update leaves `abs_committed_reads` unchanged, and it closes on its own
by `by (auto simp add: abs_committed_reads_def)` — unfolding the one definition
`abs_committed_reads`, which counts only `committed` reads and
client-`committed`/`prepared` reads, none of which the update to `idle`,
`read X`, `committed`, or `aborted` creates. No child needs another lemma.

The decomposition is insufficient, and the `sorry`s name the gap. The failing
obligations need facts about *other* transactions — `no transactions after
t_wr have written a new version to server k` and `no prepared (but
client-committed) newer versions are on server k` (the `fp_property` goal),
`new (uncommitted) write is not read by any transactions` (`Cl_ReadyC`),
`newly committed version's readerset is empty` (`Commit`), and `aborted txn
not in commit_order` (`Abort`) — none of which `abs_committed_reads` captures.
So the four leaves close because they are easy, and the cases that need the
cross-transaction invariant stay open: the invariant, not the tactic, is what
was missing.

## Why it is good

1. `tapir_refines_sser` is declared in `VerIso/Tapir_Falsification.thy`,
   lines 434-435 (check).
2. `VerIso/Tapir_Falsification.thy` lines 18-57 contain no `sorry`: the four
   bookkeeping lemmas all close (check).
3. `sorry` occurs 6 times in `VerIso/Tapir_Falsification.thy` — six
   obligations were sorrified rather than proved (check).
4. The glue of `tapir_refines_sser` spans 130 lines (434-563) and its four
   direct children span 8, 9, 11 and 9 lines (18-25, 27-35, 37-47, 49-57), so
   the longest lemma chain below the theorem is 1 (measurement).
5. The authors record that `tapir_refines_sser` fails: `Run.thy` comments
   "fails: checkout the proof state at line 486 (in Isabelle's "Output" tab)"
   (author-statement).

In my opinion the detail worth copying is the asymmetry between the four
leaves — each a one-definition unfold — and the six open obligations, which all
need a cross-transaction invariant that the simulation's own
`abs_committed_reads` does not state. The `sorry` comments are the diagnosis:
they name the missing invariant instead of silently accepting a false proof.

## When to use it, and when not

Use sorrify-at-failure when a mostly-working decomposition has a few cases or
obligations that will not close, and you want to keep the proved lemmas while
recording exactly which sub-goals fail and what invariant each needs — the
comments name it, so the file doubles as a diagnosis artifact. Avoid it when
the shared invariant is too weak in the first place: sorrifying the failures
hides that the decomposition itself must be strengthened (a stronger invariant
stated as its own lemma), rather than patched per case. Here the easy leaves
closed because `abs_committed_reads` was exactly right for them, and the hard
cases stayed open because it was not right for them.

## Consequences

Replacing a failing block with `sorry` keeps the statement and lets the file
compile, but leaves a hole: the theorem is unproved and the file no longer
establishes the refinement. Each hole's obligation must be re-derived from a
stronger invariant; the comments name them — `no transactions after t_wr have
written a new version to server k` and `no prepared (but client-committed)
newer versions are on server k` (the `fp_property` goal), `new (uncommitted)
write is not read by any transactions` (`Cl_ReadyC`), `newly committed
version's readerset is empty` (`Commit`), and `aborted txn not in
commit_order` (`Abort`). The four bookkeeping lemmas all share the shape "a
state update leaves `abs_committed_reads` unchanged" and close by unfolding
`abs_committed_reads_def` alone, which is why they were easy; the failing cases
need facts about other transactions, which `abs_committed_reads` does not
capture.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| sorry-scan | fail | inside parent/child/skeleton sites: VerIso/Tapir_Falsification.thy:471 (sorry), VerIso/Tapir_Falsification.thy:490 (sorry), VerIso/Tapir_Falsification.thy:493 (sorry), VerIso/Tapir_Falsification.thy:527 (sorry), VerIso/Tapir_Falsification.thy:553 (sorry), VerIso/Tapir_Falsification.thy:561 (sorry); elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(tapir_refines_sser, VerIso/Tapir_Falsification.thy, 434-435) -> declared: tapir_refines_sser is declared at VerIso/Tapir_Falsification.thy:434 | check_claims.py |
| 2 | verified | no_sorry(VerIso/Tapir_Falsification.thy, 18-57) -> no_sorry: none of sorry in VerIso/Tapir_Falsification.thy:18-57 | check_claims.py |
| 3 | verified | count(sorry, 6, VerIso/Tapir_Falsification.thy) -> count: sorry occurs 6 times in 1 file(s) matching VerIso/Tapir_Falsification.thy | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/shabnamrad/veriso at commit `6407b7205c3bfc4adc62e758795a7fc5142efb33`, under `LicenseRef-unknown`; see the [source note](../../sources/veriso/SOURCE.md) for the licence text and attribution.
