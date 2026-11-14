# Fieldwise record equality between the abstract and executable seL4 states (absKState_correct)

| | |
|---|---|
| Kind | instance |
| Move | extensionality |
| Language | isabelle |
| Status | accepted |
| Source | [l4v](../../sources/l4v/SOURCE.md) at `1abfe5bce986` |
| Licence | `GPL-2.0-only` |

## Intent

Prove that the executable specification's observable state `absKState s'` equals
the abstract state `abs_state s` by `state.equality`, which splits the equality
of the two state records into one subgoal per field; each non-trivial field is
then closed by a named, independently proved lemma, so the headline
correspondence becomes nine field lemmas joined by a 28-line glue.

## The decomposition

### parent `absKState_correct`: [`proof/refine/Refine.thy` lines 94-121](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/Refine.thy#L94-L121) ([local copy](code/proof/refine/Refine.thy))

```isabelle
lemma absKState_correct:
  assumes invs: "einvs (s :: det_ext state)" and invs': "invs' s'"
  assumes rel: "(s,s') \<in> state_relation"
  shows "absKState s' = abs_state s"
  using assms
  apply (intro state.equality, simp_all add: absKState_def abs_state_def)
                  apply (rule absHeap_correct; clarsimp elim!: state_relationE)
                 apply (rule absCDT_correct; clarsimp)
                apply (rule absIsOriginalCap_correct; clarsimp)
               apply (simp add: state_relation_def)
              apply (simp add: state_relation_def)
             apply (clarsimp simp: state_relation_def)
             apply (rule absSchedulerAction_correct, simp add: state_relation_def)
            apply (simp add: domSchedule_map_relation)
           apply (simp add: state_relation_def)
          apply (simp add: state_relation_def)
         apply (simp add: state_relation_def)
        apply (simp add: state_relation_def)
       apply (simp add: state_relation_def ready_queues_relation_def ready_queue_relation_def Let_def
                        list_queue_relation_def)
       apply (fastforce dest: heap_ls_is_walk)
      apply (clarsimp simp:  user_mem_relation invs_def invs'_def)
      apply (simp add: state_relation_def)
     apply (rule absInterruptIRQNode_correct, simp add: state_relation_def)
    apply (rule absInterruptStates_correct, simp add: state_relation_def)
   apply (rule absArchState_correct, simp)
  apply (rule absExst_correct; simp)
  done
```

### child `absHeap_correct`: [`proof/refine/ADT_H.thy` lines 1080-1085](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/ADT_H.thy#L1080-L1085) ([local copy](code/proof/refine/ADT_H.thy))

```isabelle
  assumes absHeap_correct:
    "\<And>s s'.
     \<lbrakk>pspace_aligned s; pspace_distinct s; valid_objs s; valid_cur_fpu s;
      pspace_relation (kheap s) (ksPSpace s'); ghost_relation_wrapper s s';
      (arch_state s, ksArchState s') \<in> arch_state_relation (aobjs_of' s')\<rbrakk>
     \<Longrightarrow> absHeap (gsUserPages s') (gsCNodes s') (ksArchState s') (ksPSpace s') = kheap s"
```

### child `absCDT_correct`: [`proof/refine/ADT_H.thy` lines 726-726](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/ADT_H.thy#L726-L726) ([local copy](code/proof/refine/ADT_H.thy))

```isabelle
lemmas absCDT_correct = absCDT_correct'(1)
```

### child `absIsOriginalCap_correct`: [`proof/refine/ADT_H.thy` lines 456-515](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/ADT_H.thy#L456-L515) ([local copy](code/proof/refine/ADT_H.thy))

```isabelle
lemma absIsOriginalCap_correct:
  assumes valid_ioc: "valid_ioc s"
  assumes valid_objs: "valid_objs s"
  assumes rel: "(s,s') \<in> state_relation"
  assumes pspace_aligned: "pspace_aligned s"
  assumes pspace_distinct: "pspace_distinct s"
  assumes pspace_aligned': "pspace_aligned' s'"
  assumes pspace_distinct': "pspace_distinct' s'"
  shows "absIsOriginalCap (cteMap (gsCNodes s')) (ksPSpace s') = is_original_cap s"
proof -
  from valid_ioc
  have no_cap_not_orig:
    "\<forall>p. caps_of_state s p = None \<longrightarrow> is_original_cap s p = False"
  and null_cap_not_orig:
    "\<forall>p. caps_of_state s p = Some cap.NullCap \<longrightarrow> is_original_cap s p = False"
    by (fastforce simp: valid_ioc_def2 null_filter_def)+

  have cnp:
  "\<forall>a b. caps_of_state s (a, b) \<noteq> None \<longrightarrow>
         (cteMap (gsCNodes s')) (cte_map (a, b)) = (a, b)"
    using cteMap_correct[OF rel valid_objs pspace_aligned pspace_distinct
                            pspace_aligned' pspace_distinct']
    by (clarsimp simp: dom_def)

  show ?thesis
    apply (subgoal_tac "revokable_relation (is_original_cap s)
                          (null_filter (caps_of_state s)) (ctes_of s') \<and>
                        pspace_relation (kheap s) (ksPSpace s')")
     prefer 2
     using rel
     apply (clarsimp simp add: state_relation_def)
    apply (rule ext)
    apply (clarsimp simp add: revokable_relation_def
                              null_filter_def absIsOriginalCap_def
                       split: if_split_asm)
    apply (erule_tac x=a in allE)
    apply (erule_tac x=b in allE)
    apply (case_tac "caps_of_state s (a, b)")
     apply (clarsimp simp: no_cap_not_orig)
     apply (frule (1) pspace_relation_cte_wp_atI[OF _ _ valid_objs])
     apply (clarsimp simp: cte_wp_at_caps_of_state)
     apply (subgoal_tac "(a,b) = (aa,ba)", simp)
     apply (cut_tac a=aa and b=ba in cnp[rule_format], simp)
     apply (simp add: cte_map_def)
    apply simp
    apply (case_tac "aa = cap.NullCap")
     apply (clarsimp simp add: null_cap_not_orig)
     apply (frule (1) pspace_relation_ctes_ofI
              [OF _ caps_of_state_cteD pspace_aligned' pspace_distinct'])
     apply clarsimp
    apply (frule (1) pspace_relation_ctes_ofI
             [OF _ caps_of_state_cteD pspace_aligned' pspace_distinct'])
    apply (clarsimp simp add: dom_def)
    apply (cut_tac a=a and b=b in cnp[rule_format], simp+)
    apply (case_tac cte, clarsimp)
    apply (case_tac aa, simp_all)
    apply (rename_tac arch_cap)
    apply clarsimp
    done
qed
```

### child `absSchedulerAction_correct`: [`proof/refine/ADT_H.thy` lines 1041-1043](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/ADT_H.thy#L1041-L1043) ([local copy](code/proof/refine/ADT_H.thy))

```isabelle
lemma absSchedulerAction_correct:
  "sched_act_relation action action' \<Longrightarrow> absSchedulerAction action' = action"
  by (cases action; simp add: absSchedulerAction_def)
```

### child `domSchedule_map_relation`: [`proof/refine/ADT_H.thy` lines 1072-1074](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/ADT_H.thy#L1072-L1074) ([local copy](code/proof/refine/ADT_H.thy))

```isabelle
lemma domSchedule_map_relation:
  "(s, s') \<in> state_relation \<Longrightarrow> domSchedule_map (ksDomSchedule s') = domain_list s"
  by (fastforce elim: domSchedule_map_domain_list_map state_relationE)
```

### child `absInterruptIRQNode_correct`: [`proof/refine/ADT_H.thy` lines 1020-1023](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/ADT_H.thy#L1020-L1023) ([local copy](code/proof/refine/ADT_H.thy))

```isabelle
lemma absInterruptIRQNode_correct:
  "interrupt_state_relation (interrupt_irq_node s) (interrupt_states s) (ksInterruptState s') \<Longrightarrow>
   absInterruptIRQNode (ksInterruptState s') = interrupt_irq_node s"
   by (rule ext) (clarsimp simp add: absInterruptIRQNode_def interrupt_state_relation_def)
```

### child `absInterruptStates_correct`: [`proof/refine/ADT_H.thy` lines 1025-1033](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/ADT_H.thy#L1025-L1033) ([local copy](code/proof/refine/ADT_H.thy))

```isabelle
lemma absInterruptStates_correct:
  "interrupt_state_relation (interrupt_irq_node s) (interrupt_states s) (ksInterruptState s') \<Longrightarrow>
   absInterruptStates (ksInterruptState s') = interrupt_states s"
  apply (rule ext)
  apply (clarsimp simp : absInterruptStates_def IRQStateMap_def interrupt_state_relation_def
                         irq_state_relation_def)
  apply (erule_tac x=x in allE)+
  apply (clarsimp split: irq_state.splits irqstate.splits)
  done
```

### child `absExst_correct`: [`proof/refine/ADT_H.thy` lines 1050-1060](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/ADT_H.thy#L1050-L1060) ([local copy](code/proof/refine/ADT_H.thy))

```isabelle
lemma absExst_correct:
  assumes invs: "einvs s" and invs': "invs' s'"
  assumes rel: "(s, s') \<in> state_relation"
  shows "absExst s' = exst s"
  apply (rule det_ext.equality)
    using rel invs invs'
    apply (simp_all add: absExst_def absSchedulerAction_correct
                         absCDTList_correct[THEN fun_cong] state_relation_def invs_def valid_state_def
                         ready_queues_relation_def invs'_def valid_state'_def
                         valid_pspace_def valid_sched_def valid_pspace'_def curry_def fun_eq_iff)
  done
```

How the parts fit. The parent is a single equality of two big state records.
Its first step, `intro state.equality, simp_all add: absKState_def
abs_state_def`, expands both sides to their fields and then applies
extensionality *over the record*: `state.equality` turns one record equality
into one subgoal per field of `det_ext state`. From there the glue is a flat
list, one `apply` per field. Fields whose equality is already a direct
component of `state_relation` close by `simp add: state_relation_def` (e.g.
`cur_thread`, `idle_thread`, `domain_index`, `cur_domain`); the nine fields that
need a real argument each call a named lemma:

| field | closed by | lemma |
|---|---|---|
| `kheap` | `apply (rule absHeap_correct; clarsimp elim!: state_relationE)` | `absHeap_correct` |
| `cdt` | `apply (rule absCDT_correct; clarsimp)` | `absCDT_correct` |
| `is_original_cap` | `apply (rule absIsOriginalCap_correct; clarsimp)` | `absIsOriginalCap_correct` |
| `scheduler_action` | `apply (rule absSchedulerAction_correct, simp add: state_relation_def)` | `absSchedulerAction_correct` |
| `domain_list` | `apply (simp add: domSchedule_map_relation)` | `domSchedule_map_relation` |
| `interrupt_irq_node` | `apply (rule absInterruptIRQNode_correct, simp add: state_relation_def)` | `absInterruptIRQNode_correct` |
| `interrupt_states` | `apply (rule absInterruptStates_correct, simp add: state_relation_def)` | `absInterruptStates_correct` |
| `arch_state` | `apply (rule absArchState_correct, simp)` | `absArchState_correct` |
| `exst` | `apply (rule absExst_correct; simp)` | `absExst_correct` |

Eight of the nine are shown above as child sites; the ninth,
`absArchState_correct`, is a locale assumption just like `absHeap_correct` and
is listed here instead:
[`proof/refine/ADT_H.thy` lines 81-82](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/ADT_H.thy#L81-L82).

The lemma graph, in text: `absKState_correct` calls the nine lemmas above and
nothing else (every other step is `simp`/`fastforce`/`clarsimp`). Below them,
the argument fans out:

- `absCDT_correct` is the `lemmas` abbreviation `absCDT_correct =
  absCDT_correct'(1)`; `absCDT_correct'` is proved by `ext` over the cte map and
  relies on `cteMap_correct`, which bottoms out in the same-theory helpers
  `cte_at_CNodeI`, `TCB_implies_KOTCB` and `tcb_cap_cases_length`.
- `absIsOriginalCap_correct` is proved by `apply (rule ext)` over cap pairs and
  also relies on `cteMap_correct`.
- `absExst_correct` re-uses the *same* move one level down: it proves equality
  of the `exst` sub-record with `det_ext.equality`, closing its fields by
  `simp_all` with `absSchedulerAction_correct` and `absCDTList_correct`.
- `absHeap_correct` and `absArchState_correct` are not proved in this theory:
  they are parameters of the locales `ADT_H_2` and `ADT_H`, deferred to the
  per-architecture interpretation (e.g. `ARM/ArchADT_H.thy`).

Each of the nine is a good leaf for the same reason: it is a self-contained
statement about one field, stated in terms of the field's own relation
(`state_relation`, `interrupt_state_relation`, `sched_act_relation`, …), whose
proof closes on its own (or, for the two parameters, is discharged once per
architecture) without referring to the other fields.

## Why it is good

1. The parent `absKState_correct` is declared at `proof/refine/Refine.thy`
   lines 94-121 (`check`, [permalink](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/Refine.thy#L94-L121)).
2. The parent site cites `absHeap_correct` (`check`,
   [permalink](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/Refine.thy#L94-L121)).
3. No `sorry` closes any goal in `proof/refine/ADT_H.thy` lines 1-1177
   (`check`, [permalink](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/ADT_H.thy)).
4. The `shape` is a measurement: 9 direct lemmas, a checked longest chain of 4
   project lemmas below the theorem, a 28-line glue, and the 8 shown children
   totalling 97 lines (`measurement`; line counts and the depth chain
   `absKState_correct -> absCDT_correct -> absCDT_correct' -> cteMap_correct ->
   cte_at_CNodeI` are given in `entry.json` claim 4).
5. The same record-extensionality move recurs inside a child: `absExst_correct`
   proves equality of the `exst` sub-record with `det_ext.equality`, splitting
   it field-wise (`known-use`,
   [permalink](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/ADT_H.thy#L1050-L1060)).

In my opinion the detail worth copying is the *flat* shape of the glue: the
split produces one subgoal per field, and the glue is one `apply` per subgoal,
so the correspondence between a field and the lemma that closes it is
textually visible and each lemma can be replaced independently.

## When to use it, and when not

Use it when the goal is an equality between two large record-typed states (or
two functions over them) whose fields are related field-by-field by an existing
relation — here `state_relation` already states most field equalities as direct
components, so `state.equality` (or `ext`) plus `simp add: <relation>_def`
closes the easy fields for free, and only the hard fields need named lemmas.
Use it when the fields are genuinely independent, so each lemma is a
self-contained statement provable on its own.

Avoid it when the fields interact (one field's proof needs another's), when
there is no fieldwise relation to lean on so each field needs a new argument
rather than a one-line `rule`, or when the record is small enough that the
split is ceremony. Avoid it too when a field is too architecture- or
instantiation-specific to prove in the generic theory — unless, as here, you
are willing to make that field a locale *parameter* and move its proof to the
interpretation.

## Consequences

The move creates one obligation per field of the state record. Each is
discharged either by `simp add: state_relation_def` (a field whose equality is
a direct component of the relation) or by a named lemma/parameter. The two
heaviest fields (`kheap` and `arch_state`) are left as locale parameters, so
the generic refine layer does not prove them: the obligation moves to the
per-architecture interpretation (e.g. `ARM/ArchADT_H.thy`). Failure modes: a
field missing from `state_relation`, or a child stated slightly weaker than the
field equality, breaks the corresponding `apply (rule ...)` step in the glue; a
record that is later extended by a field silently adds a subgoal that the
shared `simp_all` must then handle.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/proof-deploy.yml: the 'Proof' job (seL4/ci-actions/aws-proofs) runs on push to master (default branch), building the full proof session set including session Refine (proof/ROOT 'session Refine in refine'), which compiles proof/refine/Refine.thy. Pinned commit 1abfe5bce98632a94ba52adf183045620c509340 is on the default branch. | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: absHeap_correct@proof/refine/Refine.thy:100, absCDT_correct@proof/refine/Refine.thy:101, absIsOriginalCap_correct@proof/refine/Refine.thy:102, absSchedulerAction_correct@proof/refine/Refine.thy:106, domSchedule_map_relation@proof/refine/Refine.thy:107, absInterruptIRQNode_correct@proof/refine/Refine.thy:117, absInterruptStates_correct@proof/refine/Refine.thy:118, absExst_correct@proof/refine/Refine.thy:120; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 2 file(s) byte-identical at 1abfe5bce98632a94ba52adf183045620c509340 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(absKState_correct, proof/refine/Refine.thy, 94-121) -> declared: absKState_correct is declared at proof/refine/Refine.thy:94 | check_claims.py |
| 2 | verified | cites(parent, absHeap_correct) -> cites: absHeap_correct occurs at proof/refine/Refine.thy:100 | check_claims.py |
| 3 | verified | no_sorry(proof/refine/ADT_H.thy, 1-1177) -> no_sorry: none of sorry in proof/refine/ADT_H.thy:1-1177 | check_claims.py |
| 4 | verified | Line counts checked at the pinned commit in code/: glue Refine.thy 94-121 = 28 lines; 8 shown children ADT_H.thy 1080-1085 (6), 726 (1), 456-515 (60), 1041-1043 (3), 1072-1074 (3), 1020-1023 (4), 1025-1033 (9), 1050-1060 (11) = 97; 9 direct lemmas cited in the glue (absHeap_correct:100, absCDT_correct:101, absIsOriginalCap_correct:102, absSchedulerAction_correct:106, domSchedule_map_relation:107, absInterruptIRQNode_correct:117, absInterruptStates_correct:118, absArchState_correct:119, absExst_correct:120). Depth chain confirmed: absKState_correct cites absCDT_correct (Refine.thy:101); absCDT_correct = absCDT_correct'(1) (ADT_H.thy:726); absCDT_correct' uses cteMap_correct (ADT_H.thy:569, inside absCDT_correct' starting 549); cteMap_correct uses cte_at_CNodeI (ADT_H.thy:345). | verifier |
| 5 | verified | ADT_H.thy 1050-1060: lemma absExst_correct proves 'absExst s' = exst s' by 'apply (rule det_ext.equality)' (line 1055), splitting the exst sub-record field-wise, then simp_all with absExst_def/absSchedulerAction_correct/absCDTList_correct[THEN fun_cong]/state_relation_def — the same record-extensionality move as the parent's state.equality. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent Refine.thy:94-121 is a single record equality opened by 'intro state.equality, simp_all add: absKState_def abs_state_def' then one apply per field, matching the stated decomposition; all 9 named lemmas cited in the glue (absHeap, absCDT, absIsOriginalCap, absSchedulerAction, domSchedule_map, absInterruptIRQNode, absInterruptStates, absArchState, absExst) are exactly the lemmas the proof uses, with 8 shown as child sites and absArchState_correct (ADT_H.thy:81-82, locale ADT_H) listed in the README. Each child's closing method matches the code: absHeap_correct is an 'assumes' of locale ADT_H_2 (1076+, 1080-1085), absCDT_correct = 'lemmas absCDT_correct = absCDT_correct'(1)' (726) with absCDT_correct' (549-723) closing by 'apply (rule ext)' (643) using cteMap_correct (569); absIsOriginalCap_correct (456-515) by 'apply (rule ext)' + case on caps_of_state; absSchedulerAction/domSchedule_map/absInterruptIRQNode close by their recorded by/apply; absExst_correct (1050-1060) by 'rule det_ext.equality'. Proof closes ('done'/'qed', no sorry). Shape numbers verified: glue_lines 28 (94-121), child_lines [6,1,60,3,3,4,9,11] sum 97 = shown_child_total_lines, direct_lemmas 9, depth 4 chain absKState_correct->absCDT_correct(Refine:101)->absCDT_correct'(ADT:726)->cteMap_correct(ADT:569)->cte_at_CNodeI(ADT:345) all confirmed. | reviewer-correctness |
| generality | accept | Move generalises cleanly beyond seL4: 'When to use it' abstracts to any equality of large record-typed states whose fields are fixed by an existing relation, and applicability.goal_shape/use_when/avoid_when repeat it independently of the example. 'When not to use' is specific and honest (interacting fields, no fieldwise relation, too-small record, architecture-specific field without a locale parameter), and consequences name concrete failure modes (field missing from state_relation, child slightly weaker than the field equality, record extension silently adding a subgoal). Good-leaf question answered explicitly: each leaf is self-contained, stated in its own field's relation, closes on its own without referring to other fields, and the two heavy fields are deferred as locale parameters discharged per architecture - exactly the bounded-context property a bounded prover needs. Verified parent glue (Refine.thy 94-121) and exemplar children (absHeap, absSchedulerAction, absExst) in the local code match the description. | reviewer-generality |
| provenance-licence | accept | Provenance and licence now consistent and traceable. check_provenance.py passes: 2 file(s) byte-identical at commit 1abfe5bce98632a94ba52adf183045620c509340, so the pinned commit and all permalinks resolve. Both copied files carry SPDX-License-Identifier: GPL-2.0-only in their headers (Refine.thy:6, ADT_H.thy:5), matching entry.json source.licence=GPL-2.0-only, the README Licence row, and the Source-and-licence section. The earlier objection is met: SOURCE.md now records Licence GPL-2.0-only AND BSD-2-Clause and source.json licence=GPL-2.0-only AND BSD-2-Clause (the old CC-BY-SA-4.0 survives only as licence_detected with a licence_note explaining the supersession). The entry-level GPL-2.0-only is a correct subset of the source-level per-file licences (proof files GPL-2.0, libraries BSD-2-Clause), confirmed against upstream-LICENSE.md: its CC-BY-SA-4.0 SPDX tag licenses LICENSE.md itself, not the code. No contradiction remains. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/seL4/l4v at commit `1abfe5bce98632a94ba52adf183045620c509340`. Both copied files carry `SPDX-License-Identifier: GPL-2.0-only` in their headers ([`Refine.thy` line 6](code/proof/refine/Refine.thy), [`ADT_H.thy` line 5](code/proof/refine/ADT_H.thy)), so this entry's code is under `GPL-2.0-only`. The upstream [LICENSE.md](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/LICENSE.md) states that proofs about the seL4 kernel are GPL v2 and general libraries/tools BSD-2-Clause; its own `SPDX-License-Identifier: CC-BY-SA-4.0` tag is the licence of LICENSE.md only, not of these proof files. See the [source note](../../sources/l4v/SOURCE.md) for attribution.
