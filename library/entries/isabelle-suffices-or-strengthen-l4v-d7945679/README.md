# Well-foundedness of the next_slot order by strengthening to finite-and-acyclic

| | |
|---|---|
| Kind | instance |
| Move | suffices-or-strengthen |
| Language | isabelle |
| Status | accepted |
| Source | [l4v](../../sources/l4v/SOURCE.md) at `1abfe5bce986` |
| Licence | `GPL-2.0-only` |
| Licence recorded | 2026-11-14T14:01:07Z |

## Intent

A goal of the shape `wf R` — well-foundedness of the relation that `next_slot`
walks over the capability-derivation tree/list — is replaced in one step by the
*stronger* conjunction `finite R ∧ acyclic R`, through the library rule
`finite_acyclic_wf`. Finiteness and acyclicity are then two independent halves,
each with its own named lemmas, instead of one monolithic well-foundedness
proof.

## The decomposition

### parent `wf_next_slot`: [`proof/invariant-abstract/Deterministic_AI.thy` lines 4322-4337](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/invariant-abstract/Deterministic_AI.thy#L4322-L4337) ([local copy](code/proof/invariant-abstract/Deterministic_AI.thy))

```isabelle
lemma wf_next_slot:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>valid_mdb s; valid_list s\<rbrakk>
    \<Longrightarrow> wf {(next, p). next_slot p (cdt_list s) (cdt s) = Some next}"
  apply(rule finite_acyclic_wf)
   apply(insert cte_wp_at_set_finite)[1]
   apply(rule_tac B="{p. cte_wp_at \<top> p s} \<times> {p. cte_wp_at \<top> p s}" in finite_subset)
    apply(fastforce dest: cte_at_next_slot cte_at_next_slot' simp: finite_depth)
   apply(fastforce intro: finite_cartesian_product)
  apply(rule acyclicI)
  apply(frule finite_depth)
  apply(rule allI)
  apply(drule next_slot_no_loop, simp add: valid_mdb_def, simp add: finite_depth)
  apply(fastforce simp: next_slot_set_def)
  done
```

### child `next_slot_no_loop`: [`proof/invariant-abstract/Deterministic_AI.thy` lines 4303-4320](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/invariant-abstract/Deterministic_AI.thy#L4303-L4320) ([local copy](code/proof/invariant-abstract/Deterministic_AI.thy))

```isabelle
lemma next_slot_no_loop:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>valid_list_2 t m; no_mloop m; finite_depth m\<rbrakk>
    \<Longrightarrow> x \<notin> next_slot_set x t m"
  apply(rule notI)
  apply(case_tac "m x")
   apply(drule(2) next_slot_setD, simp)
   apply(simp add: next_sib_set_not_self)
   apply(erule disjE)
    apply(simp add: no_mloop_def descendants_of_def)
   apply(elim exE conjE)
   apply(erule disjE)
    apply(fastforce simp: descendants_of_def cdt_parent_defs dest: tranclD2)
   apply(fastforce simp: next_sib_set_def next_sib_def split: option.splits dest: tranclD2)
  apply(drule next_slot_set_after_in_list)
       apply(assumption)+
  apply(simp add: next_sib_set_not_self)
  done
```

### child `cte_at_next_slot`: [`proof/invariant-abstract/Deterministic_AI.thy` lines 1602-1629](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/invariant-abstract/Deterministic_AI.thy#L1602-L1629) ([local copy](code/proof/invariant-abstract/Deterministic_AI.thy))

```isabelle
lemma cte_at_next_slot:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>valid_list s; valid_mdb s; finite_depth (cdt s)\<rbrakk>
    \<Longrightarrow> next_slot p (cdt_list s) (cdt s) = Some n \<Longrightarrow> cte_at p s"
  apply(simp add: next_slot_def)
  apply(simp split: if_split_asm)
   apply(drule next_childD, simp)
   apply(rule_tac p=n in descendants_of_cte_at2)
    apply(simp add: child_descendant)
   apply(simp)
  apply(subgoal_tac "next_not_child_dom (p, cdt_list s, cdt s)")
   prefer 2
   apply(simp add: next_not_child_termination valid_mdb_def valid_list_2_def)
  apply(simp split: if_split_asm)
   apply(case_tac "cdt s p")
    apply(simp)
   apply(rule descendants_of_cte_at)
    apply(simp add: descendants_of_def cdt_parent_defs)
    apply(rule r_into_trancl, simp)
   apply(simp)
  apply(drule next_sibD)
  apply(elim exE conjE)
  apply(drule after_in_list_in_list)
  apply(rule descendants_of_cte_at)
   apply(simp add: descendants_of_def cdt_parent_defs)
   apply(rule r_into_trancl, simp)
  apply(simp)
  done
```

### child `cte_at_next_slot'`: [`proof/invariant-abstract/Deterministic_AI.thy` lines 1631-1665](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/invariant-abstract/Deterministic_AI.thy#L1631-L1665) ([local copy](code/proof/invariant-abstract/Deterministic_AI.thy))

```isabelle
lemma cte_at_next_slot':
  "\<lbrakk>valid_list s; valid_mdb s; finite_depth (cdt s)\<rbrakk>
    \<Longrightarrow> next_slot p (cdt_list s) (cdt s) = Some n \<Longrightarrow> cte_at n s"
  apply(simp add: next_slot_def)
  apply(simp split: if_split_asm)
   apply(drule next_childD, simp)
   apply(rule_tac x=p in descendants_of_cte_at, simp add: child_descendant, simp)
  apply(rule next_not_child_pinduct2[where t="cdt_list s" and p=p
                                             and m="cdt s"])
      apply(rule_tac p=a in descendants_of_cte_at2)
       apply(fastforce simp: descendants_of_def cdt_parent_defs)
      apply(simp)
     apply(assumption)
    apply(simp add: next_not_child_termination valid_mdb_def valid_list_2_def
               split: if_split_asm)
     apply(case_tac "cdt s p")
      apply(simp)
     apply(simp)
     apply(rule descendants_of_cte_at)
      apply(fastforce simp: descendants_of_def cdt_parent_defs)
     apply(simp add: valid_mdb_def)
    apply(drule next_sibD)
    apply(case_tac "cdt s p")
     apply(simp)
    apply(rule descendants_of_cte_at)
     apply(fastforce simp: descendants_of_def cdt_parent_defs)
    apply(simp add: valid_mdb_def)
   apply(intro allI impI, drule next_sibD)
    apply(simp)
   apply(elim exE conjE)
   apply(drule_tac after_in_list_in_list)
   apply(simp add: valid_list_2_def)
   apply(rule_tac x="(aa, b)" in descendants_of_cte_at, simp add: child_descendant, simp)
  apply(simp)
  done
```

### child `finite_depth`: [`proof/invariant-abstract/Deterministic_AI.thy` lines 206-257](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/proof/invariant-abstract/Deterministic_AI.thy#L206-L257) ([local copy](code/proof/invariant-abstract/Deterministic_AI.thy))

```isabelle
lemma finite_depth:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "valid_mdb s \<Longrightarrow> finite_depth (cdt s)"
  apply(simp add: finite_depth_def)
  apply(intro allI)
  apply(subgoal_tac "{x. slot \<in> descendants_of x (cdt s)} \<subseteq> {x. cte_wp_at (\<lambda>_. True) x s}")
   prefer 2
   apply(fastforce simp: descendants_of_cte_at2)
  apply(drule finite_subset)
   apply(simp add: cte_wp_at_set_finite)
  apply(case_tac "cdt s slot")
   apply(fastforce)
  apply(rule ccontr)
  apply(simp)
  apply(frule_tac f="\<lambda>x. THE y. cdt s x = Some y" in inj_on_iff_eq_card)
  apply(subgoal_tac "inj_on (\<lambda>x. THE y. cdt s x = Some y) {x. slot \<in> descendants_of x (cdt s)}")
   prefer 2
   apply(simp(no_asm) add: inj_on_def)
   apply(intro allI impI)
   apply(rule ccontr)
   apply(frule_tac b=x and c=y in descendants_linear)
     apply(simp)
    apply(simp)
   apply(case_tac "cdt s x")
    apply(fastforce)
   apply(case_tac "cdt s y")
    apply(fastforce)
   apply(fastforce simp: valid_mdb_def sib_not_desc)
  apply(simp)
  apply(subgoal_tac "((\<lambda>x. THE y. cdt s x = Some y) ` {x. slot \<in> descendants_of x (cdt s)})
                      \<subset> {x. slot \<in> descendants_of x (cdt s)}")
   prefer 2
   apply(rule psubsetI)
    apply(rule subsetI)
    apply(simp)
    apply(erule imageE)
    apply(case_tac "cdt s xa")
     apply(fastforce)
    apply(rule_tac b=xa in descendants_trans)
     apply(simp)
    apply(fastforce simp: descendants_of_def cdt_parent_defs)
   apply(rule_tac x=a in set_neqI[symmetric])
    apply(fastforce simp: descendants_of_def cdt_parent_defs)
   apply(rule notI)
   apply(erule imageE)
   apply(case_tac "cdt s x")
    apply(fastforce)
   apply(fastforce simp: sib_not_desc valid_mdb_def)
  apply(drule psubset_card_mono)
   apply(assumption)
  apply(simp)
  done
```

How the parts fit. `apply(rule finite_acyclic_wf)` turns the single `wf`
goal into the two halves `finite R ∧ acyclic R`, where
`R = {(next, p). next_slot p (cdt_list s) (cdt s) = Some next}`.

- *Finiteness* (lines 4328-4331). The relation is shown to be a subset of the
  finite product `{p. cte_wp_at ⊤ p s} × {p. cte_wp_at ⊤ p s}` (finite by the
  library fact `cte_wp_at_set_finite`). Each pair `(next, p)` of `R` has both
  endpoints a `cte_at`: `cte_at_next_slot` gives `cte_at p s`, and
  `cte_at_next_slot'` gives `cte_at n s`. Both need the `finite_depth (cdt s)`
  hypothesis, discharged by `finite_depth` (via `valid_mdb s`).
- *Acyclicity* (lines 4332-4336). `apply(rule acyclicI)` reduces acyclicity to
  "no `x` reaches itself in `R⁺`". `frule finite_depth` recovers
  `finite_depth (cdt s)` from `valid_mdb s`, and `next_slot_no_loop` then gives
  `x ∉ next_slot_set x t m`; unfolding `next_slot_set_def` finishes.

The lemma graph, in text (each arrow "uses", all in `Deterministic_AI.thy`):

```
wf_next_slot (4322)
├─ finite_acyclic_wf, cte_wp_at_set_finite, acyclicI, valid_mdb_def, next_slot_set_def   [library / definitions]
├─ cte_at_next_slot   (1602) ── next_childD, next_sibD, descendants_of_cte_at(_2), next_not_child_termination
├─ cte_at_next_slot'  (1631) ── next_not_child_pinduct2, descendants_of_cte_at(_2), next_sibD
├─ finite_depth       (206)  ── descendants_of_cte_at2, cte_wp_at_set_finite, descendants_linear, descendants_trans, sib_not_desc, psubset_card_mono
└─ next_slot_no_loop  (4303) ── next_slot_setD (4123), next_slot_set_after_in_list (4263), next_sib_set_not_self (4250)
      next_slot_set_after_in_list ── next_slot_setD, next_sib_set_same_parent (4117), sib_not_desc
      next_slot_setD ── next_not_childD (617), next_childD, child_descendant, descendants_trans
            next_not_childD ── next_not_childD' (551)
```

Why each child is a good leaf:

- `next_slot_no_loop` is a self-contained "no self-loop in `next_slot_set`"
  statement; its proof closes from two named siblings (`next_slot_setD`,
  `next_slot_set_after_in_list`) plus `next_sib_set_not_self`.
- `cte_at_next_slot` and `cte_at_next_slot'` are the two direction-matching
  endpoints of the same fact (`next_slot ... = Some n` lands on a `cte_at`); each
  closes by unfolding `next_slot_def` and dispatching the child/sibling cases
  through `descendants_of_cte_at(_2)`.
- `finite_depth` is the depth-descent leaf: `valid_mdb s` implies the traversal
  tree is finite-depth, closed by a strict-subset cardinality argument. It is
  used by *both* halves, so it is the shared leaf that ties them together.

## Why it is good

1. `wf_next_slot` is declared in `Deterministic_AI.thy` at lines 4322-4337
   (`check`: `declared`).
2. No `sorry` occurs anywhere in `Deterministic_AI.thy` (`check`: `no_sorry`
   over the whole file, 5224 lines; my grep also found no `oops` or `admit`).
3. The decomposition is shallow-and-deep at once: the glue is 16 lines and
   cites 4 direct lemmas whose proofs total 133 lines, and the longest chain of
   project lemmas below `wf_next_slot` is 5 deep (`measurement`).
4. The same finite-and-acyclic strengthening is used a second time at
   `wf_last_child` (4575-4587), paired with `last_child_no_loop` and consumed by
   `last_child_induct` (`known-use`).

In my opinion the detail worth copying is that the strengthening is *not* a
`have`/`suffices` of a new statement: it is a single backward application of a
library rule whose premises (`finite`, `acyclic`) are exactly the two named
lemmas the author had already proved. The move costs one line and buys two
clean obligations.

## When to use it, and when not

Use it when the goal is `wf R` for a relation `R` over a *finite* state graph
(a traversal, a dependency, a derivation order) and you can (a) bound `R`'s
pairs by a known finite carrier, and (b) reduce acyclicity to a no-loop lemma
`x ∉ R⁺ x`. This is exactly the situation where `finite_acyclic_wf` gives you
two obligations that are each easier than the direct well-foundedness proof.
Avoid it when `R` is infinite or only well-founded through a measure (e.g. the
natural-number `<` order), where finiteness is out of reach; when acyclicity
needs more than a no-loop fact; or when the two halves share so much that one
direct proof is shorter.

## Consequences

The move replaces one `wf R` obligation with two: `finite R` and `acyclic R`.
The finiteness half must bound every pair of the relation in a finite carrier —
here `cte_at_next_slot` / `cte_at_next_slot'` show each endpoint is a `cte_at`,
so `R` is a subset of a finite product. The acyclicity half needs a no-loop
lemma whose `finite_depth` precondition is discharged by `finite_depth` itself.
Failure modes: `finite_depth` is the real content (a 52-line cardinality
argument) and its cost is inherited by both halves; `finite_acyclic_wf` yields
`wf` only for literally finite relations, so the move does not reach infinite
well-founded orders.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .github/workflows/proof-deploy.yml: runs on push to master (default branch) via seL4/ci-actions/aws-proofs, building all sessions including AInvs (proof/invariant-abstract/Deterministic_AI.thy) | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: next_slot_no_loop@proof/invariant-abstract/Deterministic_AI.thy:4335, cte_at_next_slot@proof/invariant-abstract/Deterministic_AI.thy:4330, cte_at_next_slot'@proof/invariant-abstract/Deterministic_AI.thy:4330, finite_depth@proof/invariant-abstract/Deterministic_AI.thy:4330; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 1 file(s) byte-identical at 1abfe5bce98632a94ba52adf183045620c509340 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(wf_next_slot, proof/invariant-abstract/Deterministic_AI.thy, 4322-4337) -> declared: wf_next_slot is declared at proof/invariant-abstract/Deterministic_AI.thy:4322 | check_claims.py |
| 2 | verified | no_sorry(proof/invariant-abstract/Deterministic_AI.thy, 1-5224) -> no_sorry: none of sorry in proof/invariant-abstract/Deterministic_AI.thy:1-5224 | check_claims.py |
| 3 | verified | Read site line spans in copied Deterministic_AI.thy: parent wf_next_slot 4322-4337 (16 lines), next_slot_no_loop 4303-4320 (18), cte_at_next_slot 1602-1629 (28), cte_at_next_slot' 1631-1665 (35), finite_depth 206-257 (52); glue cites all 4. Depth chain verified edge-by-edge: wf_next_slot->next_slot_no_loop (drule next_slot_no_loop@4335), ->next_slot_set_after_in_list@4263 (drule), ->next_slot_setD@4123 (drule(3) next_slot_setD@4268), ->next_not_childD@617 (drule(2) next_not_childD), ->next_not_childD'@551 (by simp add: next_not_childD'@628); 5 edges deep, all in Deterministic_AI.thy | verifier |
| 4 | verified | Read lines 4565-4596: wf_last_child declared 4575-4587 uses finite_acyclic_wf (4577) and last_child_no_loop (declared 4565, cited 4585); last_child_induct (4589) consumes it at 4594 'apply(simp add: wf_last_child)' | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent wf_next_slot (4322-4337, 16 lines) and all four children (next_slot_no_loop 4303-4320=18, cte_at_next_slot 1602-1629=28, cte_at_next_slot' 1631-1665=35, finite_depth 206-257=52) read verbatim from the copied file and match the entry's statements and closed_by. The glue cites exactly these four project lemmas (finite_depth/cte_at_next_slot/cte_at_next_slot' at 4330, next_slot_no_loop at 4335) plus library facts; every proof ends in done and sorry-scan is clean, so it closes. Shape numbers recompute: glue_lines 16, child_lines [18,28,35,52], direct_lemmas 4; the depth chain wf_next_slot -> next_slot_no_loop -> next_slot_set_after_in_list(4263) -> next_slot_setD(4123) -> next_not_childD(617) -> next_not_childD'(551) is verified in the code, giving depth 5. wf_last_child (4575-4587) reuses finite_acyclic_wf + last_child_no_loop as the known-use claim states. | reviewer-correctness |
| generality | accept | Generality holds. The move is stated as a reusable rule (replace wf R by finite R & acyclic R via finite_acyclic_wf) not tied to next_slot; applicability.use_when/avoid_when give concrete conditions (finite carrier bound, acyclicity as a no-loop fact), and a known-use (wf_last_child 4575-4587, verified: uses finite_acyclic_wf, pairs with last_child_no_loop 4565, consumed by last_child_induct 4589/4594) shows reuse beyond the example. avoid_when and consequences are honest and specific: they name the failure mode that finite_depth is the real 52-line content inherited by both halves, and that finite_acyclic_wf yields wf only for literally finite relations, so infinite/measure-based orders are out of reach. The 'Why each child is a good leaf' section answers the bounded-prover question: next_slot_no_loop is self-contained closing from two named siblings, the cte_at_next_slot pair are direction-matching endpoints, finite_depth is the shared depth-descent leaf. | reviewer-generality |
| provenance-licence | accept | Provenance and licence are now consistent and traceable. check_provenance passes (Deterministic_AI.thy byte-identical at 1abfe5bce98632a94ba52adf183045620c509340); the commit is pinned identically across README, entry.json and sources/l4v/SOURCE.md. entry.json source.licence and the README licence field both now record GPL-2.0-only, matching the copied file's own header (SPDX-License-Identifier: GPL-2.0-only, lines 1-5) and upstream LICENSE.md (proofs about the seL4 kernel code licensed under GPL version 2; its own document header is CC-BY-SA-4.0, the source of the earlier error). Cited ranges open on the declared lemmas (206/257 finite_depth, 1602/1629 cte_at_next_slot, 1631/1665 cte_at_next_slot', 4303/4320 next_slot_no_loop, 4322/4337 wf_next_slot). The README source note records GPL-2.0-only for the copied file and explicitly flags the residual sources/l4v/SOURCE.md 'Licence (detected): CC-BY-SA-4.0' as out-of-scope, with the correct explanation. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/seL4/l4v at commit `1abfe5bce98632a94ba52adf183045620c509340`. The only copied file here, `proof/invariant-abstract/Deterministic_AI.thy`, is licensed `GPL-2.0-only`, as its own header declares (`SPDX-License-Identifier: GPL-2.0-only`, lines 1-5 of the [local copy](code/proof/invariant-abstract/Deterministic_AI.thy)). Upstream [`LICENSE.md`](https://github.com/seL4/l4v/blob/1abfe5bce98632a94ba52adf183045620c509340/LICENSE.md) confirms this: "proofs about the seL4 kernel code itself are licensed under GPL version 2". (Note: the [source note](../../sources/l4v/SOURCE.md) still records `CC-BY-SA-4.0`, which is the licence of the `LICENSE.md` document's own comment header — not of the code — and is outside this entry's editable scope.)
