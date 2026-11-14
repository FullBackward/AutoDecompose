# Per-slot CNode initialisation split on original_cap_at

| | |
|---|---|
| Kind | instance |
| Move | case-split |
| Language | isabelle |
| Status | accepted |
| Source | [jormungand](../../sources/jormungand/SOURCE.md) at `bad97f9817b4` |
| Licence | `GPL-2.0-only` |

## Intent

Reduce the per-slot CNode-initialisation theorem — a Hoare triple that
`init_cnode_slot … Move` turns a half-initialised slot into an initialised
slot — to a case split on whether the slot holds an original capability,
dispatching each branch to one of two framed separation-logic lemmas already
proved for exactly that case.

## The decomposition

### parent `init_cnode_slot_move_sep`: [`case_study/l4v/sys-init/InitCSpace_SI.thy` lines 1215-1231](https://github.com/sel4proj/jormungand/blob/bad97f9817b4034cd705cd295a1f86af880a7631/case_study/l4v/sys-init/InitCSpace_SI.thy#L1215-L1231) ([local copy](code/case_study/l4v/sys-init/InitCSpace_SI.thy))

```isabelle
lemma init_cnode_slot_move_sep:
  "\<lbrakk>well_formed spec; cnode_at obj_id spec;cap_at (\<lambda>c. is_device_cap c = dev) (obj_id, slot) spec\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>cnode_slot_half_initialised spec t obj_id slot \<and>*
     si_obj_cap_at t orig_caps spec dev obj_id slot \<and>*
     si_spec_irq_cap_at irq_caps spec obj_id slot \<and>*
     si_cap_at t dup_caps spec dev obj_id \<and>*
     object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright> \<rbrace>
   init_cnode_slot spec orig_caps dup_caps irq_caps Move obj_id slot
   \<lbrace>\<lambda>_.\<guillemotleft>object_slot_initialised spec t obj_id slot \<and>*
        si_spec_obj_null_cap_at t orig_caps spec obj_id slot \<and>*
        si_spec_irq_null_cap_at irq_caps spec obj_id slot \<and>*
        si_cap_at t dup_caps spec dev obj_id \<and>*
        object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (case_tac "original_cap_at (obj_id, slot) spec")
   apply (wp init_cnode_slot_move_original_sep)
  apply (wp init_cnode_slot_move_not_original_sep)
  done
```

### child `init_cnode_slot_move_original_sep`: [`case_study/l4v/sys-init/InitCSpace_SI.thy` lines 1106-1175](https://github.com/sel4proj/jormungand/blob/bad97f9817b4034cd705cd295a1f86af880a7631/case_study/l4v/sys-init/InitCSpace_SI.thy#L1106-L1175) ([local copy](code/case_study/l4v/sys-init/InitCSpace_SI.thy))

```isabelle
lemma init_cnode_slot_move_original_sep:
  "\<lbrakk>well_formed spec; cnode_at obj_id spec;
    original_cap_at (obj_id, slot) spec;
    cap_at (\<lambda>c. is_device_cap c = dev) (obj_id, slot)  spec\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>cnode_slot_half_initialised spec t obj_id slot \<and>*
     si_obj_cap_at t orig_caps spec dev obj_id slot \<and>*
     si_spec_irq_cap_at irq_caps spec obj_id slot \<and>*
     si_cap_at t dup_caps spec dev obj_id \<and>*
     object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright> \<rbrace>
   init_cnode_slot spec orig_caps dup_caps irq_caps Move obj_id slot
   \<lbrace>\<lambda>_.\<guillemotleft>object_slot_initialised spec t obj_id slot \<and>*
        si_spec_obj_null_cap_at t orig_caps spec obj_id slot \<and>*
        si_spec_irq_null_cap_at irq_caps spec obj_id slot \<and>*
        si_cap_at t dup_caps spec dev obj_id \<and>*
        object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (subst cnode_slot_half_initialised_original_slot, assumption+)
  apply (frule cnode_at_not_tcb_at)

  (* Case: opt_cap (obj_id, slot) spec = Some NullCap *)
  apply (case_tac "opt_cap (obj_id, slot) spec = Some NullCap")
   apply (clarsimp simp: init_cnode_slot_def sep_conj_exists opt_object_def cap_at_def
                         si_obj_cap_at_def si_spec_irq_cap_at_def
                         si_spec_obj_null_cap_at_def si_spec_irq_null_cap_at_def)
   apply (frule opt_cap_cdl_objects)
   apply (wp | clarsimp)+
   apply (subst (asm) object_slot_empty_initialised_NullCap, assumption+)

  (* Case: opt_cap (obj_id, slot) spec = None *)
  apply (case_tac "opt_cap (obj_id, slot) spec = None")
   apply (clarsimp simp: init_cnode_slot_def assert_opt_def)
  apply clarsimp

  (* Case: cap_at cap_has_object (obj_id, slot) spec *)
  apply (case_tac "cap_at cap_has_object (obj_id, slot) spec")
   apply (clarsimp simp: cap_at_def)
   apply (rename_tac cap)
   apply (frule (2) well_formed_cap_object)
   apply (frule (2) well_formed_is_untyped_cap)
   apply (clarsimp simp: init_cnode_slot_def)
   apply (clarsimp simp: si_obj_cap_at_def si_obj_cap_at'_def cap_at_def
                         si_spec_obj_null_cap_at_def si_spec_obj_null_cap_at'_def
                         si_spec_irq_cap_at_def si_spec_irq_cap_at'_def
                         si_spec_irq_null_cap_at_def si_spec_irq_null_cap_at'_def)
   apply (wp seL4_CNode_Mutate_object_slot_initialised_sep seL4_CNode_Move_object_slot_initialised_cap_has_object_sep |
          clarsimp)+
   apply (intro impI conjI,simp_all add:opt_object_def)
          apply (drule(1) well_formed_well_formed_cap[where obj_id = obj_id])
            apply (simp add:opt_cap_def opt_object_def slots_of_def)
           apply (simp add:cap_type_null)
          apply simp
         apply (metis cap_has_object_not_NullCap well_formed_cap_valid_src_cap well_formed_well_formed_cap')
        apply (metis cap_has_object_not_NullCap well_formed_orig_ep_cap_is_default)
       apply (simp add: ep_related_cap_def cap_type_def split:cdl_cap.splits)
      apply (erule (3) well_formed_cnode_object_size_bits_eq)
     apply (metis cap_has_object_NullCap well_formed_cap_has_object_has_type well_formed_well_formed_cap')
    apply (metis cap_has_object_NullCap well_formed_cap_valid_src_cap well_formed_well_formed_cap')
   apply (erule (3) well_formed_cnode_object_size_bits_eq)

  (* Case: cap_at is_irqhandler_cap (obj_id, slot) spec *)
  apply (frule (3) well_formed_cap_no_object_irqhandler_cap)
  apply (clarsimp simp: cap_at_def)
  apply (rename_tac cap)
  apply (clarsimp simp: init_cnode_slot_def)
  apply (clarsimp simp: si_obj_cap_at_def si_obj_cap_at'_def cap_at_def
                        si_spec_obj_null_cap_at_def si_spec_obj_null_cap_at'_def
                        si_spec_irq_cap_at_def si_spec_irq_cap_at'_def
                        si_spec_irq_null_cap_at_def si_spec_irq_null_cap_at'_def)
  apply (wp seL4_CNode_Move_object_slot_initialised_irqhandler_cap_sep | clarsimp)+
  apply (clarsimp simp: opt_object_def)
  done
```

### child `init_cnode_slot_move_not_original_sep`: [`case_study/l4v/sys-init/InitCSpace_SI.thy` lines 1195-1213](https://github.com/sel4proj/jormungand/blob/bad97f9817b4034cd705cd295a1f86af880a7631/case_study/l4v/sys-init/InitCSpace_SI.thy#L1195-L1213) ([local copy](code/case_study/l4v/sys-init/InitCSpace_SI.thy))

```isabelle
lemma init_cnode_slot_move_not_original_sep:
  "\<lbrakk>well_formed spec; cnode_at obj_id spec;
    \<not> original_cap_at (obj_id, slot) spec\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>cnode_slot_half_initialised spec t obj_id slot \<and>*
     si_obj_cap_at t orig_caps spec dev obj_id slot \<and>*
     si_spec_irq_cap_at irq_caps spec obj_id slot \<and>*
     si_cap_at t dup_caps spec dev obj_id \<and>*
     object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright> \<rbrace>
   init_cnode_slot spec orig_caps dup_caps irq_caps Move obj_id slot
   \<lbrace>\<lambda>_.\<guillemotleft>object_slot_initialised spec t obj_id slot \<and>*
        si_spec_obj_null_cap_at t orig_caps spec obj_id slot \<and>*
        si_spec_irq_null_cap_at irq_caps spec obj_id slot \<and>*
        si_cap_at t dup_caps spec dev obj_id \<and>*
        object_fields_empty spec t obj_id \<and>* si_objects \<and>* R\<guillemotright>\<rbrace>"
  apply (wp init_cnode_slot_move_not_original_inv)
  apply (subst (asm) cnode_slot_half_initialised_not_original_slot, assumption+)
  apply (subst (asm) si_obj_cap_at_si_spec_obj_null_cap_at_not_original, assumption)
  apply (clarsimp simp: si_spec_irq_cap_at_def si_spec_irq_null_cap_at_def original_cap_at_def)
  done
```

How the parts fit. The parent states the per-slot contract — `init_cnode_slot …
Move` carries a half-initialised slot (plus its frame of `si_obj_cap_at`,
`si_spec_irq_cap_at`, `si_cap_at`, `object_fields_empty`, `si_objects`, `R`) to
an initialised slot. Its whole proof is the glue:

- `case_tac "original_cap_at (obj_id, slot) spec"` splits the goal into two
  cases: the slot holds an original capability, or it does not. Because the
  predicate is boolean, the split is exhaustive by construction — no separate
  `original_cap_at … ∨ ¬ original_cap_at …` lemma needs to be stated.
- `apply (wp init_cnode_slot_move_original_sep)` closes the first branch, and
  `apply (wp init_cnode_slot_move_not_original_sep)` the second. `wp` selects
  the right lemma in each goal because the two branch lemmas carry the
  discriminating predicate (or its negation) as a premise and share the
  parent's frame, so no further glue is needed.

Lemma graph (an arrow reads "applied by / closes with"):

```
init_cnode_slot_move_sep (1215)                         -- parent, the glue
├── init_cnode_slot_move_original_sep (1106)            -- premise original_cap_at
│     ├── seL4_CNode_Mutate_object_slot_initialised_sep (1062)
│     │     └── seL4_CNode_Mutate_object_slot_initialised_sep_helper (781)
│     ├── seL4_CNode_Move_object_slot_initialised_cap_has_object_sep (964)
│     └── seL4_CNode_Move_object_slot_initialised_irqhandler_cap_sep (1005)
└── init_cnode_slot_move_not_original_sep (1195)        -- premise ¬ original_cap_at
      ├── init_cnode_slot_move_not_original_inv (1177)
      ├── cnode_slot_half_initialised_not_original_slot (221)
      └── si_obj_cap_at_si_spec_obj_null_cap_at_not_original (1189)
```

Why each child is a good leaf. `init_cnode_slot_move_original_sep` is a
self-contained statement whose proof closes on its own by a second-level case
split on the shape of the spec cap — `NullCap`, `None`, `cap_has_object`, or
`is_irqhandler_cap` — each branch closed by one `wp` against a named
`seL4_CNode_Move`/`seL4_CNode_Mutate` object-slot lemma followed by
`clarsimp`/`metis` side-condition discharge. Those three object-slot lemmas are
themselves leaves that close by `wp` against one `_helper` lemma each.
`init_cnode_slot_move_not_original_sep` closes from named siblings: `wp
init_cnode_slot_move_not_original_inv` (the slot is untouched, so the frame is
preserved), then `subst cnode_slot_half_initialised_not_original_slot` and
`subst si_obj_cap_at_si_spec_obj_null_cap_at_not_original` collapse the
pre/post predicates, and one `clarsimp` finishes.

## Why it is good

1. The glue is three lines — a `case_tac` and two `wp` applications, one per
   child — with nothing else (lines 1228-1230). Both citations are
   machine-checked by `check_claims.py` (`cites`).
2. The parent cites each of its two children directly: `wp
   init_cnode_slot_move_original_sep` (line 1229) and `wp
   init_cnode_slot_move_not_original_sep` (line 1230).
3. No `sorry` closes the parent or either child (lines 1106-1231).
4. Shape: `direct_lemmas = 2`, `glue_lines = 17` (the full parent lemma, lines
   1215-1231), child proof lines `70` (original, 1106-1175) and `19`
   (not_original, 1195-1213), and `depth = 3` via the chain
   `init_cnode_slot_move_sep → init_cnode_slot_move_original_sep →
   seL4_CNode_Mutate_object_slot_initialised_sep →
   seL4_CNode_Mutate_object_slot_initialised_sep_helper`.
5. The same split recurs in the Copy mode of the same file:
   `init_cnode_slot_copy_sep` (lines 1545-1562) does
   `case_tac "original_cap_at (obj_id, slot) spec"` and dispatches to
   `init_cnode_slot_copy_original_sep` and
   `init_cnode_slot_copy_not_original_sep`.

The design that makes the split the right one is stated by the authors in the
definition of `init_cnode_slot`: “Any original caps (which includes IRQ Hander
caps) are moved, not copied” (`SysInit_SI.thy`, the comment beside `move_cap ←
return (original_cap_at (cnode_id, cnode_slot) spec)`), so the Move-mode proof
is naturally a split on exactly that predicate.

In my opinion the detail worth copying is the discipline of writing the two
branch lemmas with the discriminating predicate as a premise and an identical
frame, so that the glue reduces to `case_tac` + two `wp` calls and never needs
to unfold the program.

## When to use it, and when not

Use it when a Hoare-triple goal branches on a single boolean predicate of the
spec (here `original_cap_at (obj_id, slot) spec`), when one framed lemma
already exists for each branch carrying that predicate (or its negation) as an
extra premise and sharing the same pre/post frame, and when the predicate is
exhaustive (a boolean, so `case_tac` yields exactly two goals).

Avoid it when the two branches need different frames or different
generalisations (then `wp` against the branch lemmas will not close the split
goal and the glue must do real work); when the predicate is not exhaustive (a
non-boolean `case_tac` would leave a third case); or when the branch lemmas
have not been proved yet, since then the split merely exposes goals that must
be solved from raw definitions.

## Consequences

The split on a boolean predicate creates exactly two goals plus an
exhaustiveness obligation that `case_tac` discharges itself (the predicate is
either true or false), so no separate disjunction lemma is stated. The two
branch lemmas must each carry the discriminating predicate as a premise for
`wp` to select them; if a branch had to derive the predicate instead of
assuming it, the `wp` dispatch would not close. The original branch is itself a
second-level split on the shape of the spec cap, so that side of the
decomposition is two layers deep and its leaves are the three seL4 object-slot
lemmas; the not-original side is one layer deep.

## Verification

<!-- verification:start -->
Status: **accepted**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | ci-record | .travis.yml (commit bad97f98 on default branch HEAD): 'L4V_ARCH=ARM Isabelle2016-1/bin/isabelle build -v -D .' builds all sessions recursively; case_study/l4v/sys-init/ROOT session SysInit imports Proof_SI, which imports InitCSpace_SI.thy | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: init_cnode_slot_move_original_sep@case_study/l4v/sys-init/InitCSpace_SI.thy:1229, init_cnode_slot_move_not_original_sep@case_study/l4v/sys-init/InitCSpace_SI.thy:1230; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 4 file(s) byte-identical at bad97f9817b4034cd705cd295a1f86af880a7631 | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | cites(init_cnode_slot_move_sep, init_cnode_slot_move_original_sep) -> cites: init_cnode_slot_move_original_sep occurs at case_study/l4v/sys-init/InitCSpace_SI.thy:1229 | check_claims.py |
| 2 | verified | cites(init_cnode_slot_move_sep, init_cnode_slot_move_not_original_sep) -> cites: init_cnode_slot_move_not_original_sep occurs at case_study/l4v/sys-init/InitCSpace_SI.thy:1230 | check_claims.py |
| 3 | verified | no_sorry(case_study/l4v/sys-init/InitCSpace_SI.thy, 1106-1231) -> no_sorry: none of sorry in case_study/l4v/sys-init/InitCSpace_SI.thy:1106-1231 | check_claims.py |
| 4 | verified | glue_lines: parent site 1215-1231 = 17 lines; child_lines: original 1106-1175 = 70, not_original 1195-1213 = 19; direct_lemmas=2 (parent applies init_cnode_slot_move_original_sep and init_cnode_slot_move_not_original_sep); depth=3 chain confirmed: parent cites child (line 1229), child cites seL4_CNode_Mutate_object_slot_initialised_sep (line 1146), which cites seL4_CNode_Mutate_object_slot_initialised_sep_helper (lemma at line 781, applied at ~1089) | verifier |
| 5 | verified | InitCSpace_SI.thy lines 1545-1562: init_cnode_slot_copy_sep applies 'case_tac original_cap_at (obj_id, slot) spec' (line 1559) and dispatches to init_cnode_slot_copy_original_sep (line 1560) and init_cnode_slot_copy_not_original_sep (line 1562) | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Parent init_cnode_slot_move_sep (1215-1231) is case_tac on original_cap_at (obj_id,slot) spec then wp of exactly its two children at lines 1229 and 1230, then done; parent and both children end in done, no sorry in 1106-1231. Child statements in entry.json are verbatim copies of the code. closed_by matches: the original child case-splits on opt_cap being Some NullCap, None, a cap with an object, or an IRQ-handler cap and closes via wp seL4_CNode_Mutate_object_slot_initialised_sep, seL4_CNode_Move_object_slot_initialised_cap_has_object_sep and seL4_CNode_Move_object_slot_initialised_irqhandler_cap_sep; the not_original child closes via wp init_cnode_slot_move_not_original_inv, two substs and clarsimp (closed_by omits the substs, a minor abbreviation). Shape numbers check out: glue_lines 17 (1215-1231), child_lines 70 and 19 (1106-1175, 1195-1213), direct_lemmas 2, depth 3 via 1215 to 1106 to 1062 (Mutate) to 781 (helper). Copy mode 1545-1562 does the same case_tac and dispatches to the copy original/not_original lemmas. | reviewer-correctness |
| generality | accept | Generality holds. The move is stated beyond this one example: entry.json use_when abstracts to 'the program's behaviour branches on a single boolean predicate of the spec' with one pre-proved framed lemma per branch carrying the predicate (or its negation) as premise and sharing the same frame, and the README's opinion paragraph names the transferable discipline (branch lemmas carry the discriminating predicate as premise + identical frame so glue = case_tac + two wp, never unfolding the program). avoid_when is honest and specific: different frames/generalisations (wp won't close), non-exhaustive predicate (third case), unproved branch lemmas. Consequences are accurate: case_tac on a boolean yields exactly two goals and discharges its own exhaustiveness (verified at code:1215-1231), and the branch lemmas must carry the predicate as premise. A verified independent known-use (Copy mode, InitCSpace_SI.thy:1545-1562) recurs the same split, confirmed by reading it. Leaf quality for a bounded prover is stated in substance: 'self-contained', 'closes on its own' by one wp against a named seL4 lemma then clarsimp/metis, each object-slot leaf closing by wp against one _helper lemma. Minor unstated nuance, not an objection: the Copy-mode known-use has a different frame (empty->half vs half->initialised) so its glue needs extra subst/simp, which is itself one of the avoid_when conditions; the known-use claim remains accurate as written. | reviewer-generality |
| provenance-licence | accept | Objection resolved. check_provenance.py passes: 4 files byte-identical at bad97f9817b4034cd705cd295a1f86af880a7631, and that commit matches across entry.json source.commit, README (abbreviated bad97f9817b4), sources/jormungand/SOURCE.md and source.json. Licence now consistent: all four copied files under code/case_study/l4v/sys-init/ carry the GPL-2.0 header (@TAG(NICTA_GPL), 'GNU General Public License version 2') at lines 1-9 (tag at line 8), verified by reading each. entry.json source.licence is GPL-2.0-only, README licence row and Source-and-licence section both say GPL-2.0-only and state all four files carry the GPL header, and SOURCE.md/source.json record 'BSD-2-Clause AND GPL-2.0-only' with licence_files listing both LICENSE_BSD2.txt and case_study/l4v/LICENSE_GPLv2.txt, both copied (upstream-LICENSE_BSD2.txt, upstream-case_study--l4v--LICENSE_GPLv2.txt, the latter the real GPL v2 text). GPL-2.0-only is copyleft so the index will flag it (protocol 2.1). Minor non-objection: README says the header is 'lines 1-8' but the closing '*)' is line 9 and the tag line 8; immaterial to traceability. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/sel4proj/jormungand at commit `bad97f9817b4034cd705cd295a1f86af880a7631`, under `GPL-2.0-only`; see the [source note](../../sources/jormungand/SOURCE.md) for the licence text and attribution. All four copied files lie in the vendored `case_study/l4v/` tree and carry its GPL version 2 header (`@TAG(NICTA_GPL)`, lines 1-8), so `GPL-2.0-only` governs them; the repository's own theories are under `BSD-2-Clause` (`LICENSE_BSD2.txt`).
