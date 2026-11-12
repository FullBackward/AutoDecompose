# Strengthen the seL4 abstract-to-design refinement to an invariant-guarded forward simulation

| | |
|---|---|
| Kind | instance |
| Move | suffices-or-strengthen |
| Language | isabelle |
| Status | verified |
| Source | [l4v](../../sources/l4v/SOURCE.md) at `1abfe5bce986` |
| Licence | `CC-BY-SA-4.0` |

## Intent

Replace the headline refinement `ADT_H uop ⊑ ADT_A uop` — a global property
over all executions that is too hard to prove directly — with a stronger,
decomposable statement: an invariant-guarded forward simulation. Applying two
library rules backwards (`sim_imp_refines`, then `L_invariantI`) turns the
single goal into three named lemmas — the abstract invariant, the concrete
invariant, and the simulation — each proved separately and each closing on its
own.

## The decomposition

### parent `refinement`: [`proof/refine/Refine.thy` lines 842-849](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/Refine.thy#L842-L849) ([local copy](code/proof/refine/Refine.thy))

```isabelle
theorem refinement:
  "ADT_H uop \<sqsubseteq> ADT_A uop"
  apply (rule sim_imp_refines)
  apply (rule L_invariantI)
    apply (rule akernel_invariant)
   apply (rule ckernel_invariant)
  apply (rule fw_sim_A_H)
  done
```

### child `akernel_invariant`: [`proof/refine/Refine.thy` lines 232-262](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/Refine.thy#L232-L262) ([local copy](code/proof/refine/Refine.thy))

```isabelle
lemma (in Refine) akernel_invariant:
  "ADT_A uop \<Turnstile> full_invs"
  unfolding full_invs_def
  apply (rule invariantI)
   apply (clarsimp simp: ADT_A_def subset_iff)
   apply (frule bspec[OF akernel_init_invs])
   apply (simp add: Let_def Init_A_def ext_init_def)
  apply (clarsimp simp: ADT_A_def global_automaton_def)
  apply (rename_tac tc' s' mode' e' tc s mode e)
  apply (elim disjE)
             apply ((clarsimp simp: kernel_call_A_def
                   | drule use_valid[OF _ kernel_entry_invs])+)[2]
           apply ((clarsimp simp: do_user_op_A_def monad_to_transition_def
                                  check_active_irq_A_def
                 | drule use_valid[OF _ do_user_op_invs2]
                 | drule use_valid[OF _ check_active_irq_invs_just_running])+)[2]
         apply ((clarsimp simp add: check_active_irq_A_def
               | drule use_valid[OF _ check_active_irq_invs])+)[1]
        apply (clarsimp simp: ct_in_state_def st_tcb_at_def obj_at_def)
       apply ((clarsimp simp add: do_user_op_A_def check_active_irq_A_def
             | drule use_valid[OF _ do_user_op_invs2]
             | drule use_valid[OF _ check_active_irq_invs_just_running])+)[1]
      apply (clarsimp simp: ct_in_state_def st_tcb_at_def obj_at_def)
     apply (clarsimp simp: ct_in_state_def st_tcb_at_def obj_at_def)
    apply ((clarsimp simp add: check_active_irq_A_def
         | drule use_valid[OF _ check_active_irq_invs])+)[1]
   apply ((clarsimp simp add: check_active_irq_A_def
        | drule use_valid[OF _ check_active_irq_invs_just_idle])+)[1]
  apply ((clarsimp simp add: check_active_irq_A_def
        | drule use_valid[OF _ check_active_irq_invs])+)[1]
  done
```

### child `ckernel_invariant`: [`proof/refine/Refine.thy` lines 652-765](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/Refine.thy#L652-L765) ([local copy](code/proof/refine/Refine.thy))

```isabelle
lemma ckernel_invariant:
  "ADT_H uop \<Turnstile> full_invs'"
  unfolding full_invs'_def
  supply word_neq_0_conv[simp]
  supply domain_time_rel_eq[simp]
  apply (rule invariantI)
   apply (clarsimp simp add: ADT_H_def)
   apply (subst conj_commute, simp)
   apply (rule conjI)
    apply (drule ckernel_init_valid_duplicates'[rule_format], simp)
   apply (rule conjI)
    apply (frule init_refinement[simplified subset_eq, THEN bspec])
    apply (clarsimp simp: ex_abs_def lift_state_relation_def)
    apply (frule akernel_init_invs[THEN bspec])
    apply (rule_tac x=s in exI)
    apply (clarsimp simp: Init_A_def)
   apply (insert ckernel_init_invs)[1]
   apply clarsimp
   apply (frule ckernel_init_sch_norm)
   apply (frule ckernel_init_ctr)
   apply (frule ckernel_init_domain_time)
   apply (frule ckernel_init_domain_list)
   apply (fastforce simp: Init_H_def)
  apply (clarsimp simp: ADT_A_def ADT_H_def global_automaton_def)
  apply (erule_tac P="a \<and> (\<exists>x. b x)" for a b in disjE)
  apply (clarsimp simp: kernel_call_H_def)
   apply (drule use_valid[OF _ valid_corres_combined
                            [OF kernel_entry_invs entry_corres],
                            OF _ kernelEntry_invs'[THEN hoare_weaken_pre]])
     apply fastforce
    apply (clarsimp simp: ex_abs_def sch_act_simple_def ct_running_related ct_idle_related
                           sched_act_rct_related)
    apply (rule exI, rule conjI, assumption)
    apply simp
    apply (fastforce simp: ex_abs_def sch_act_simple_def ct_running_related ct_idle_related
                           sched_act_rct_related valid_domain_list_from_invs')
   apply (clarsimp simp: kernel_call_H_def)
   apply (fastforce simp: ex_abs_def sch_act_simple_def ct_running_related ct_idle_related
                          sched_act_rct_related)

  apply (erule_tac P="a \<and> b" for a b in disjE)
   apply (clarsimp simp add: do_user_op_H_def monad_to_transition_def)
   apply (drule use_valid)
     apply (rule hoare_vcg_conj_lift)
      apply (rule doUserOp_valid_objs')
     apply (rule hoare_vcg_conj_lift)
      apply (rule doUserOp_valid_duplicates')
     apply (rule valid_corres_combined[OF do_user_op_invs2 corres_guard_imp2[OF do_user_op_corres]])
      apply clarsimp
     apply (rule doUserOp_invs'[THEN hoare_weaken_pre])
     apply (fastforce simp: ex_abs_def)
    apply (clarsimp simp: invs_valid_objs' ex_abs_def, rule_tac x=s in exI,
            clarsimp simp: ct_running_related sched_act_rct_related valid_domain_list_from_invs')
   apply (clarsimp simp: ex_abs_def)
   apply (fastforce simp: ex_abs_def ct_running_related sched_act_rct_related)

  apply (erule_tac P="a \<and> b \<and> c \<and> (\<exists>x. d x)" for a b c d in disjE)
   apply (clarsimp simp add: do_user_op_H_def monad_to_transition_def)
   apply (drule use_valid)
     apply (rule hoare_vcg_conj_lift)
      apply (rule doUserOp_valid_objs')
     apply (rule hoare_vcg_conj_lift)
      apply (rule doUserOp_valid_duplicates')
     apply (rule valid_corres_combined[OF do_user_op_invs2 corres_guard_imp2[OF do_user_op_corres]])
      apply clarsimp
     apply (rule doUserOp_invs'[THEN hoare_weaken_pre])
     apply (fastforce simp: ex_abs_def)
    apply (fastforce simp: ex_abs_def ct_running_related sched_act_rct_related
                           valid_domain_list_from_invs')
   apply (fastforce simp: ex_abs_def)

  apply (erule_tac P="a \<and> b" for a b in disjE)
   apply (clarsimp simp: check_active_irq_H_def)
   apply (drule use_valid)
     apply (rule hoare_vcg_conj_lift)
      apply (rule checkActiveIRQ_valid_objs')
     apply (rule hoare_vcg_conj_lift)
      apply (rule checkActiveIRQ_valid_duplicates')
     apply (rule valid_corres_combined[OF check_active_irq_invs_just_running checkActiveIRQ_just_running_corres])
     apply (rule checkActiveIRQ_invs'_just_running[THEN hoare_weaken_pre])
     apply (fastforce simp: ex_abs_def)
    apply (fastforce simp: ex_abs_def ct_running_related sched_act_rct_related
                           valid_domain_list_from_invs')
   apply (fastforce simp: ex_abs_def)

  apply (erule_tac P="a \<and> b" for a b in disjE)
   apply (clarsimp simp: check_active_irq_H_def)
   apply (drule use_valid)
     apply (rule hoare_vcg_conj_lift)
      apply (rule checkActiveIRQ_valid_objs')
     apply (rule hoare_vcg_conj_lift)
      apply (rule checkActiveIRQ_valid_duplicates')
     apply (rule valid_corres_combined[OF check_active_irq_invs_just_idle checkActiveIRQ_just_idle_corres])
     apply (rule checkActiveIRQ_invs'_just_idle[THEN hoare_weaken_pre])
     apply clarsimp
     apply (fastforce simp: ex_abs_def)
    apply (fastforce simp: ex_abs_def ct_idle_related sched_act_rct_related
                           valid_domain_list_from_invs')
   apply (fastforce simp: ex_abs_def)

  apply (clarsimp simp: check_active_irq_H_def)
  apply (drule use_valid)
    apply (rule hoare_vcg_conj_lift)
     apply (rule checkActiveIRQ_valid_objs')
    apply (rule hoare_vcg_conj_lift)
     apply (rule checkActiveIRQ_valid_duplicates')
    apply (rule valid_corres_combined[OF check_active_irq_invs check_active_irq_corres])
    apply (rule checkActiveIRQ_invs'[THEN hoare_weaken_pre])
    apply clarsimp
    apply (fastforce simp: ex_abs_def)
   apply (fastforce simp: ex_abs_def ct_running_related ct_idle_related sched_act_rct_related
                          valid_domain_list_from_invs')
  apply (fastforce simp: ex_abs_def)
  done
```

### child `fw_sim_A_H`: [`proof/refine/Refine.thy` lines 769-840](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/Refine.thy#L769-L840) ([local copy](code/proof/refine/Refine.thy))

```isabelle
lemma fw_sim_A_H:
  "LI (ADT_A uop)
      (ADT_H uop)
      (lift_state_relation state_relation)
      (full_invs \<times> full_invs')"
  apply (unfold LI_def full_invs_def full_invs'_def)
  apply (simp add: ADT_H_def ADT_A_def)
  apply (intro conjI)
    apply (rule init_refinement)
   apply (clarsimp simp: rel_semi_def relcomp_unfold in_lift_state_relation_eq)
   apply (rename_tac tc ak m ev tc' ck' m' ev' ck)
   apply (simp add: global_automaton_def)

   apply (erule_tac P="a \<and> (\<exists>x. b x)" for a b in disjE)
    apply (clarsimp simp add: kernel_call_H_def kernel_call_A_def)
    apply (rule rev_mp, rule_tac tc=tc and event=x in entry_corres)
    apply (clarsimp simp: corres_underlying_def)
    apply (drule (1) bspec)
    apply (clarsimp simp: sch_act_simple_def)
    apply (drule (1) bspec)
    apply clarsimp
    apply (rule conjI)
     apply clarsimp
     apply (rule_tac x=b in exI)
     apply (rule conjI)
      apply (rule impI, simp)
     apply (frule (2) ct_running_related)
    apply clarsimp
    apply (rule_tac x=b in exI)
    apply (drule use_valid, rule kernelEntry_invs')
     apply (simp add: sch_act_simple_def)
    apply clarsimp
    apply (frule (1) ct_idle_related)
    apply (clarsimp simp: ct_in_state_def st_tcb_at_def obj_at_def)

   apply (erule_tac P="a \<and> b" for a b in disjE)
    apply (clarsimp simp: do_user_op_H_def do_user_op_A_def monad_to_transition_def)
    apply (rule rev_mp, rule_tac tc1=tc and f1=uop and P="ct_running and einvs" in corres_guard_imp2[OF do_user_op_corres])
     apply simp
    apply (clarsimp simp add: corres_underlying_def)
    apply (drule (1) bspec, clarsimp)
    apply (drule (1) bspec, clarsimp)
    apply fastforce

   apply (erule_tac P="a \<and> b \<and> c \<and> (\<exists>x. d x)" for a b c d in disjE)
    apply (clarsimp simp: do_user_op_H_def do_user_op_A_def monad_to_transition_def)
    apply (rule rev_mp, rule_tac tc1=tc and f1=uop and P="ct_running and einvs" in corres_guard_imp2[OF do_user_op_corres])
     apply simp
    apply (clarsimp simp add: corres_underlying_def)
    apply (drule (1) bspec, clarsimp)
    apply (drule (1) bspec, clarsimp)
    apply fastforce

   apply (erule_tac P="a \<and> b" for a b in disjE)
    apply (clarsimp simp: check_active_irq_H_def check_active_irq_A_def)
    apply (rule rev_mp, rule check_active_irq_corres)
    apply (clarsimp simp: corres_underlying_def)
    apply fastforce

   apply (erule_tac P="a \<and> b" for a b in disjE)
    apply (clarsimp simp: check_active_irq_H_def check_active_irq_A_def)
    apply (rule rev_mp, rule check_active_irq_corres)
    apply (clarsimp simp: corres_underlying_def)
    apply fastforce

   apply (clarsimp simp: check_active_irq_H_def check_active_irq_A_def)
   apply (rule rev_mp, rule check_active_irq_corres)
   apply (clarsimp simp: corres_underlying_def)
    apply fastforce

  apply (clarsimp simp: absKState_correct dest!: lift_state_relationD)
  done
```

### context `refines`: [`lib/Simulation.thy` lines 77-80](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/lib/Simulation.thy#L77-L80) ([local copy](code/lib/Simulation.thy))

```isabelle
definition
  refines :: "('c,'b,'j) data_type \<Rightarrow> ('a,'b,'j) data_type \<Rightarrow> bool" (infix "\<sqsubseteq>" 60)
where
  "C \<sqsubseteq> A \<equiv> \<forall>js s. execution C s js \<subseteq> execution A s js"
```

### context `sim_imp_refines`: [`lib/Simulation.thy` lines 140-152](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/lib/Simulation.thy#L140-L152) ([local copy](code/lib/Simulation.thy))

```isabelle
lemma sim_imp_refines:
  "C \<sqsubseteq>\<^sub>F A \<Longrightarrow> C \<sqsubseteq> A"
  apply (clarsimp simp: refines_def execution_def fw_simulates_def)
  apply (rename_tac t)
  apply (drule fw_sim_steps)
    prefer 2
    apply assumption
   apply (simp add: fw_sim_def)
   apply blast
  apply clarsimp
  apply (erule rev_image_eqI)
  apply (simp add: fw_sim_def)
  done
```

### context `LI`: [`lib/Simulation.thy` lines 200-205](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/lib/Simulation.thy#L200-L205) ([local copy](code/lib/Simulation.thy))

```isabelle
definition
  LI :: "('a,'b,'j) data_type \<Rightarrow> ('c,'b,'j) data_type \<Rightarrow> ('a \<times> 'c) set \<Rightarrow> ('a \<times> 'c) set \<Rightarrow> bool"
where
  "LI A C R I \<equiv> (\<forall>s. Init C s \<subseteq> R `` Init A s) \<and>
                (\<forall>j. (R \<inter> I) ;;; Step C j \<subseteq> Step A j ;;; R) \<and>
                (\<forall>s s'. (s,s') \<in> R \<inter> I \<longrightarrow> Fin C s' = Fin A s)"
```

### context `L_invariantI`: [`lib/Simulation.thy` lines 267-272](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/lib/Simulation.thy#L267-L272) ([local copy](code/lib/Simulation.thy))

```isabelle
lemma L_invariantI:
  assumes  "A \<Turnstile> I\<^sub>a" and "C \<Turnstile> I\<^sub>c" and "LI A C r (I\<^sub>a \<times> I\<^sub>c)"
  shows "C \<sqsubseteq>\<^sub>F A"
  using assms
  by (simp add: fw_simulates_def, rule_tac x="r \<inter> I\<^sub>a \<times> I\<^sub>c" in exI,
      simp add: LI_fw_sim)
```

How the parts fit. The parent `refinement` does no code reasoning at all: it
applies two library rules backwards and then hands off. `sim_imp_refines`
(Simulation.thy 140) says a forward simulation `C ⊑F A` implies refinement
`C ⊑ A`, so the goal becomes `ADT_H uop ⊑F ADT_A uop`. `L_invariantI`
(Simulation.thy 267) then says that to prove forward simulation it suffices to
prove two per-side invariants and an invariant-guarded `LI`; applying it
produces exactly three subgoals, which the three children discharge one for
one:

```text
refinement : ADT_H uop ⊑ ADT_A uop                    (842-849, 6-line glue)
  │ apply (rule sim_imp_refines)                      refine ⊑ → forward sim ⊑F
  ▼
  ADT_H uop ⊑F ADT_A uop
  │ apply (rule L_invariantI)                         forward sim → 3 premises
  ├─ apply (rule akernel_invariant)  ── ADT_A uop ⊨ full_invs        (232-262)
  ├─ apply (rule ckernel_invariant)  ── ADT_H uop ⊨ full_invs'       (652-765)
  └─ apply (rule fw_sim_A_H)         ── LI (ADT_A uop) (ADT_H uop)
                                          (lift_state_relation state_relation)
                                          (full_invs × full_invs')   (769-840)
  done
```

Each child is a good leaf because its statement is self-contained (an
invariant `⊨` or a `LI`) and its proof closes on its own from lemmas proved
earlier in the same file or imported, never from a sibling. `akernel_invariant`
is closed by `invariantI` (init from `akernel_init_invs`, step by `elim disjE`
over the abstract transition and `use_valid` with the abstract WP lemmas
`kernel_entry_invs`/`do_user_op_invs2`/`check_active_irq_invs*`).
`ckernel_invariant` is the concrete mirror, closed by `invariantI` (init from
`ckernel_init_*` and `init_refinement`, step by `use_valid` with
`valid_corres_combined` of the correspondence lemmas and the concrete WP lemmas
`kernelEntry_invs'`/`doUserOp_invs'`/`checkActiveIRQ_invs'*`). `fw_sim_A_H` is
closed by unfolding `LI` and case-splitting the transition, each case by
`rev_mp` with `entry_corres`/`do_user_op_corres`/`check_active_irq_corres`
plus `ct_running_related`/`ct_idle_related`/`absKState_correct`.

The two invariant children and the simulation child are independent of each
other, so they can be proved (or handed to separate provers) in parallel. The
proof also nests one level deeper than the three children: `fw_sim_A_H` uses
`entry_corres` (465-500), which uses `kernel_corres` (425-451), which uses
`kernel_corres'` (382-416), giving a chain of four project lemmas below the
main theorem (see claim 3).

The directory README calls this the top-level theory: "The top-level theory
where the refinement statement is established over the entire kernel is
[`Refine`](Refine.thy)" ([proof/refine/README.md lines 30-35](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/README.md#L30-L35)).

## Why it is good

1. The parent closes in six lines with no code reasoning: two strengthening
   rules then three named lemmas (check — [Refine.thy 842-849](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/Refine.thy#L842-L849)).
2. Each child is a self-contained `lemma … done` in the same file, and the
   file has no `sorry`, `oops` or `admit` (check — the three child ranges plus
   a grep over the whole file: [232-262](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/Refine.thy#L232-L262), [652-765](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/Refine.thy#L652-L765), [769-840](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/Refine.thy#L769-L840)).
3. Below the main theorem sits a chain of four project lemmas,
   `refinement → fw_sim_A_H → entry_corres → kernel_corres → kernel_corres'`,
   each applied by an explicit `rule` step (check — [Refine.thy #L848, #L784, #L483, #L443](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/Refine.thy)).
4. The authors justify the move: "Refinement is a global property over all
   executions and/or all hoare triples. As this is hard to show, we define the
   weaker concept of forward simulation." (author-statement —
   [Simulation.thy 97-100](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/lib/Simulation.thy#L97-L100)).
5. The shape is a measurement: a 6-line glue delegates 217 lines of proof to
   the three children (measurement — [Refine.thy](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/refine/Refine.thy)).

In my opinion the part worth copying is the two-step backward application:
first swap the hard global property for the simulation, then swap the bare
simulation for the invariant-guarded one — so that the only remaining work is
three independent statements, each with an invariant or relation already
sized to one file.

## When to use it, and when not

Use it when the goal is a relation between two transition systems
(refinement, simulation, bisimulation) stated as a global property that is
hard to prove pointwise, and you can name per-side invariants such that the
relation only needs to hold on invariant states. This is the standard way to
make a refinement proof into three independent, parallelisable statements:
two invariant proofs and one simulation. It applies at any abstraction
boundary where the two sides have their own state spaces and a shared
relation.

Avoid it when there is no invariant that genuinely weakens the simulation
obligation (then the strengthen step adds two lemmas without reducing the
third), when the two invariants depend on each other so the split does not
separate concerns, or when the original goal is already as easy as the
stronger one. Also avoid it if the invariant cannot be kept in scope: every
transition case of the simulation must preserve it, and that obligation
surfaces inside `fw_sim_A_H`.

## Consequences

The move turns one obligation into three: two invariant-preservation goals
(one per side) and one simulation goal. The simulation goal is weaker than raw
refinement because its step and final cases may assume the invariant holds —
`LI` restricts the relation to `R ∩ I` (Simulation.thy 200-205). The price is
that both invariants must be established first, and the relation must be
invariant-closed on both sides. The invariant is the shared design decision
coupling all three children: pick it too weak and `fw_sim_A_H` is unprovable;
pick it too strong and the invariant lemmas are unprovable. In seL4 the
invariants are `full_invs` (abstract) and `full_invs'` (concrete), and the
concrete one must additionally carry the state-relation-existence condition
`ex_abs einvs` (Refine.thy 560-570), which is where the abstract invariant
leaks back into the concrete side.

## Rule mapping

This supports survey F §10 rule 8 ("Backward rule, `suffices`, and witnesses
as templates"): `apply (rule sim_imp_refines)` then `apply (rule L_invariantI)`
make the rule's premises into the children exactly as the rule describes
(`proof (rule r)` makes r's premises children).

## Verification

<!-- verification:start -->
Status: **verified**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/proof-deploy.yml runs the 'Proofs' job (seL4/ci-actions/aws-proofs) on push to master, the default branch; it builds the full proof session set including session Refine (proof/ROOT lines 29-42), which compiles proof/refine/Refine.thy. Pinned commit 1abfe5bce98632a94ba52adf183045620c509340 is on the default branch (source registered with ref=HEAD, resolved by git ls-remote HEAD). | verifier | 2026-11-12 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |
| provenance | pass | 2 file(s) byte-identical at 1abfe5bce98632a94ba52adf183045620c509340 | reviewer-provenance-licence | 2026-11-12 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-12 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | Refine.thy#L842-L849: theorem refinement; proof is exactly six lines 844-849 = rule sim_imp_refines, rule L_invariantI, rule akernel_invariant, rule ckernel_invariant, rule fw_sim_A_H, done. Two strengthening rules then three named project lemmas, no other step. | verifier |
| 2 | verified | Refine.thy: akernel_invariant lemma at L232 ends done at L262; ckernel_invariant lemma at L652 ends done at L765; fw_sim_A_H lemma at L769 ends done at L840. Grep '\b(sorry|oops|admit)\b' over the whole file returns no match. | verifier |
| 3 | verified | Refine.thy: L848 rule fw_sim_A_H (in refinement); L784 rule_tac ... in entry_corres (in fw_sim_A_H); L483 corres_split[OF kernel_corres] (in entry_corres, which starts L465); L443 rule kernel_corres' (in kernel_corres, which starts L425). Four-link chain confirmed. | verifier |
| 4 | verified | Simulation.thy#L97-L100 text block reads verbatim: 'Refinement is a global property over all executions and/or all hoare triples. As this is hard to show, we define the weaker concept of forward simulation.' | verifier |
| 5 | verified | Line counts at pinned commit confirmed: glue 844-849 = 6; akernel_invariant 232-262 = 31; ckernel_invariant 652-765 = 114; fw_sim_A_H 769-840 = 72; total = 31+114+72 = 217. | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Verified against copied code: parent theorem refinement (Refine.thy 842-849) states ADT_H uop <sqsubseteq> ADT_A uop and closes in 6 proof lines (844-849) by rule sim_imp_refines then rule L_invariantI, then exactly three project lemmas akernel_invariant (L846), ckernel_invariant (L847), fw_sim_A_H (L848), then done; no other step. Children match the code verbatim: akernel_invariant (232-262, ADT_A uop |= full_invs), ckernel_invariant (652-765, ADT_H uop |= full_invs'), fw_sim_A_H (769-840, LI (ADT_A uop) (ADT_H uop) (lift_state_relation state_relation) (full_invs x full_invs')); each is lemma..done and closes on its own. L_invariantI (Simulation.thy 267-272) yields exactly the three subgoals the three children discharge; sim_imp_refines (140-152) is the strengthening rule. grep over the file finds no sorry/oops/admit. Shape numbers all correct: direct_lemmas=3 (the three children, each used directly), depth=4 (chain fw_sim_A_H->entry_corres->kernel_corres->kernel_corres' via L848/L784/L483/L443), glue_lines=6 (844-849), child_lines=[31,114,72] (232-262, 652-765, 769-840). | reviewer-correctness |
| generality | accept | Generalizes beyond the example: applicability.goal_shape and use_when/avoid_when restate the move for any relation between two transition systems (refinement/simulation/bisimulation) too hard to show pointwise, scoped honestly to invariant-guarded forward simulation rather than all 'suffices' uses; intent frames it as backward application of two library rules making premises into children. When-not-to-use is honest and specific (no invariant that actually weakens the simulation; invariants that depend on each other; goal already as easy; README adds: invariant must stay in scope across every transition case). Consequences are specific with a real failure mode (invariant too weak => fw_sim_A_H unprovable, too strong => invariant lemmas unprovable) and name the concrete leak (concrete side must carry ex_abs einvs, Refine.thy 560-570), all consistent with the shown LI/L_invariantI code. It says what makes the leaves good for a bounded prover: each child's statement is self-contained (an invariant |= or LI), closes on its own from earlier/imported lemmas never a sibling, and the three children are independent so parallelisable. | reviewer-generality |
| provenance-licence | object | Permalinks, commit (1abfe5bce98632a94ba52adf183045620c509340) and source-note URL are consistent and traceable: check_provenance.py reports both copied files byte-identical at the pinned commit, and every site permalink uses that commit. But the recorded licence is wrong. entry.json source.licence, SOURCE.md and the README all record CC-BY-SA-4.0, which is only the licence of the LICENSE.md document itself, not the code. The two copied files carry their own SPDX headers: proof/refine/Refine.thy is GPL-2.0-only and lib/Simulation.thy is BSD-2-Clause; the upstream LICENSE.md (copied as upstream-LICENSE.md) states this exactly ('proofs about the seL4 kernel code itself are licensed under GPL version 2, and general libraries and tools under the 2-Clause BSD license'). Fix: record the per-file licences (GPL-2.0-only for Refine.thy, BSD-2-Clause for Simulation.thy) and mark the entry copyleft in the index per protocol decision 1. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/seL4/l4v at commit `1abfe5bce98632a94ba52adf183045620c509340`, under `CC-BY-SA-4.0`; see the [source note](../../sources/l4v/SOURCE.md) for the licence text and attribution.
