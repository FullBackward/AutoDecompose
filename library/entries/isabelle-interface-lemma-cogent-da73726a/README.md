# Function-boundary correspondence lemma refine_sync for the BilbyFs sync operation

| | |
|---|---|
| Kind | instance |
| Move | interface-lemma |
| Language | isabelle |
| Status | draft |
| Source | [cogent](../../sources/cogent/SOURCE.md) at `49b6ceb0d033` |
| Licence | `GPL-2.0-only` |
| Licence recorded | 2026-11-14T22:40:52Z |

## Intent

`refine_sync` is the function-boundary lemma of the BilbyFs `fsop_sync`
operation: it states, once, that the abstract `afs_sync` and the generated
concrete `fsop_sync_fs` correspond under the relation `rsync_res`, with the
exception `ex` left universally quantified so a client instantiates it. Its
proof does not reason about the generated program's contents; it peels the
generated monadic structure with the generic `cogent_corres_*` rules and hands
each leaf obligation to a named helper lemma, so the parent system-call
refinement can cite `refine_sync` without ever unfolding `fsop_sync`.

## The decomposition

### parent `refine_sync`: [`impl/fs/bilby/proof/refine/FsopSyncR.thy` lines 53-116](https://github.com/au-ts/cogent/blob/49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a/impl/fs/bilby/proof/refine/FsopSyncR.thy#L53-L116) ([local copy](code/impl/fs/bilby/proof/refine/FsopSyncR.thy))

```isabelle
lemma refine_sync:
notes length_drop[simp del]
assumes rel:"afs_fsop_rel afs fs_st"
shows
  "\<And>ex. cogent_corres rsync_res
         (afs_sync afs) (fsop_sync_fs (FsopFsP.make ex fs_st))"
  unfolding afs_sync_def fsop_sync_fs_def[simplified tuple_simps sanitizers, folded eIO_def]
using [[goals_limit=5]]
  apply (rule cogent_corres_conc_let_exec, simp only: prod.case_eq_if)
  apply (rule cogent_corres_conc_let_exec, simp only: prod.case_eq_if)
  apply (rule cogent_corres_if)
    apply (simp add: FsopFsP.make_def)
    apply (fold eRoFs_def)
    apply (rule corres_sync_err[OF rel])
   apply (rule cogent_corres_conc_let_exec, simp only: prod.case_eq_if)
   apply (rule cogent_corres_conc_let_exec, simp only: prod.case_eq_if)
   apply (simp only:  FsopFsP.defs)
   apply (fold ostoreWriteNone_def)

  apply (rule ostore_sync_ret)
       using rel apply (simp add: rsync_simp)
      using rel apply (simp add: rsync_simp)
     using rel apply (simp add: rsync_simp)
     apply (clarsimp)
    apply (rule_tac v="length (a_medium_updates afs)" in cogent_corres_select, simp)
    apply (simp add: Let_def)
    apply (rule cogent_corres_return)
    using rel apply (clarsimp simp add: rsync_simp prod.case_eq_if)
    apply (erule_tac x="length (a_medium_updates afs)" in allE)
    apply (clarsimp simp: updated_afs_def id_def a_afs_updated_def \<alpha>_ostore_uptodate_def)
    apply (drule afs_inv_steps_updated_afsD)
    apply (simp add: afs_inv_steps_def updated_afs_def a_afs_updated_def id_def)
   apply clarsimp
   apply (rule_tac v="n" in cogent_corres_select)
    apply (simp)
    using length_updates_eqD[OF rel]
    apply simp
   using length_updates_eqD[OF rel]
   apply (simp add: Let_def)
   apply (rule_tac v="e" in cogent_corres_select, simp)
   apply (rule cogent_corres_return)
   using rel apply (clarsimp simp add: rsync_simp updated_afs_def)
    apply (rule conjI)
    apply (simp add: afs_inv_steps_def updated_afs_def a_afs_updated_def id_def)
     apply (fold id_def)
     apply clarsimp
     apply (subst fold_comp[symmetric], rule refl)+
     apply (erule_tac x="n+na" in allE)
     apply (fastforce simp add: take_add length_drop)
   apply (rule conjI)
    using length_updates_eqD[OF rel]
    apply (fastforce simp add: length_drop)
   apply clarsimp
    apply (rename_tac na)
    apply (erule_tac x="n + na" in allE)
    apply (erule impE)
     apply (drule sym[where s="length _" and t = "length _"])
     apply (simp only: length_drop)
     apply (subst fold_comp[symmetric], rule refl)+
     apply (erule afs_fsop_match_updates)
     apply (fastforce simp only: take_add)+
   using rel
   apply (simp add: rsync_simp FsopFsP.defs)
 done
```

### child `fold_comp`: [`impl/fs/bilby/proof/refine/FsopSyncR.thy` lines 26-28](https://github.com/au-ts/cogent/blob/49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a/impl/fs/bilby/proof/refine/FsopSyncR.thy#L26-L28) ([local copy](code/impl/fs/bilby/proof/refine/FsopSyncR.thy))

```isabelle
lemma fold_comp[rule_format]:
  "xs = ys @ zs \<longrightarrow> fold f xs accu = (fold f zs (fold f ys accu))"
  by (induct_tac xs, simp+)
```

### child `corres_sync_err`: [`impl/fs/bilby/proof/refine/FsopSyncR.thy` lines 30-33](https://github.com/au-ts/cogent/blob/49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a/impl/fs/bilby/proof/refine/FsopSyncR.thy#L30-L33) ([local copy](code/impl/fs/bilby/proof/refine/FsopSyncR.thy))

```isabelle
lemma corres_sync_err:
"afs_fsop_rel afs fs_st \<Longrightarrow>
 cogent_corres rsync_res (return (afs, R.Error e)) (\<lparr>FsopFsP.ex\<^sub>f = ex, fs_st\<^sub>f = fs_st\<rparr>, R.Error e)"
  by (simp add: rsync_res_def cogent_corres_def  return_def)
```

### child `length_updates_eqD`: [`impl/fs/bilby/proof/refine/FsopSyncR.thy` lines 35-38](https://github.com/au-ts/cogent/blob/49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a/impl/fs/bilby/proof/refine/FsopSyncR.thy#L35-L38) ([local copy](code/impl/fs/bilby/proof/refine/FsopSyncR.thy))

```isabelle
lemma length_updates_eqD:
 "afs_fsop_rel afs fs_st \<Longrightarrow>
 length (\<alpha>_updates (FsState.ostore_st\<^sub>f fs_st)) = length (a_medium_updates afs)"
 by (clarsimp simp: rsync_simp)
```

### child `afs_fsop_match_updates`: [`impl/fs/bilby/proof/refine/FsopSyncR.thy` lines 40-43](https://github.com/au-ts/cogent/blob/49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a/impl/fs/bilby/proof/refine/FsopSyncR.thy#L40-L43) ([local copy](code/impl/fs/bilby/proof/refine/FsopSyncR.thy))

```isabelle
lemma afs_fsop_match_updates:
 "afs_fsop_match (fold id xs' a) (fold id ys' c) \<Longrightarrow> xs' = xs \<Longrightarrow> ys' = ys \<Longrightarrow>
  afs_fsop_match (fold id xs a) (fold id ys c)"
by simp
```

### child `afs_inv_steps_updated_afsD`: [`impl/fs/bilby/proof/refine/AfsFsopR.thy` lines 235-241](https://github.com/au-ts/cogent/blob/49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a/impl/fs/bilby/proof/refine/AfsFsopR.thy#L235-L241) ([local copy](code/impl/fs/bilby/proof/refine/AfsFsopR.thy))

```isabelle
lemma afs_inv_steps_updated_afsD:
 "afs_inv_steps afs \<Longrightarrow> afs_inv (updated_afs afs)"
  apply (simp add: updated_afs_def)
  apply (simp add: afs_inv_steps_def)
  apply (erule_tac x="length (a_medium_updates afs)" in allE)
  apply (fastforce simp add: a_afs_updated_def)
 done
```

### child `ostore_sync_ret`: [`impl/fs/bilby/proof/refine/OstoreR.thy` lines 2379-2487](https://github.com/au-ts/cogent/blob/49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a/impl/fs/bilby/proof/refine/OstoreR.thy#L2379-L2487) ([local copy](code/impl/fs/bilby/proof/refine/OstoreR.thy))

```isabelle
lemma ostore_sync_ret:
 assumes inv_ostore: "inv_ostore mount_st ostore_st"
 and inv_mount_st: "inv_mount_st mount_st"
 and inv_step: "inv_\<alpha>_ostore (\<alpha>_ostore_uptodate ostore_st)"
 and suc: "\<And>ostore_st' ex'. \<lbrakk> inv_ostore mount_st ostore_st';
        inv_\<alpha>_ostore (\<alpha>_ostore_uptodate ostore_st');
        \<alpha>_ostore_medium ostore_st' = \<alpha>_ostore_uptodate ostore_st;
        \<alpha>_updates ostore_st' = []
        \<rbrakk> \<Longrightarrow>
      P ((ex', ostore_st'), Success ())"
 and err: "\<And>e ostore_st' ex' n. \<lbrakk> inv_ostore mount_st ostore_st';
       inv_\<alpha>_ostore (\<alpha>_ostore_uptodate ostore_st');
       e \<in> {eIO, eNoMem, eNoSpc,eOverflow};
       n < length (\<alpha>_updates ostore_st); 
       \<alpha>_ostore_medium ostore_st' = apply_n_updates n (\<alpha>_ostore_medium ostore_st) (\<alpha>_updates ostore_st);
       \<alpha>_updates ostore_st' = (drop n $ \<alpha>_updates ostore_st)
       \<rbrakk> \<Longrightarrow>
      P ((ex', ostore_st'), Error e)"

 notes pad_simps = padding_to_def[unfolded tuple_simps sanitizers] ostoreWriteNone_def

 shows "P (ostore_sync (ex, mount_st, ostore_st, ostoreWriteNone))"
using [[goals_limit=2]]
  unfolding ostore_sync_def[unfolded tuple_simps sanitizers]
  apply (case_tac "sync_offs\<^sub>f ostore_st = used\<^sub>f ostore_st")
   apply (simp add: ostoreWriteNone_def Let_def ostoreWriteNewEb_def)
   apply (rule suc[OF inv_ostore inv_step])
    apply (simp add: \<alpha>_ostore_uptodate_def used_eq_sync_offs_means_no_update)
   apply ( simp add: \<alpha>_updates_def buf_simps )
  apply (simp add: Let_def)
  apply (rule prepare_wbuf_ret[OF inv_ostore inv_mount_st inv_step])
      apply (rule refl)     
     using inv_ostore[simplified inv_ostore_def] apply clarsimp apply unat_arith
    using inv_ostore[simplified inv_ostore_def] apply clarsimp apply unat_arith
  apply (simp split: prod.split)
   apply (rule err[OF inv_ostore inv_step, where e=eOverflow and n=0, simplified])
    apply (erule used_neq_sync_offs_means_updates_not_Nil[OF inv_ostore])
  apply (simp)
  apply (rule ostore_sync_summary_if_eb_new_ret[OF _ inv_mount_st], simp_all)
  apply clarsimp
(*  apply (subgoal_tac "used\<^sub>f ostore_st' =  padding_to (mount_st, ostore_st, ostoreWriteNone)")
   apply (subgoal_tac "sync_offs\<^sub>f ostore_st' =  sync_offs\<^sub>f ostore_st")*)
    apply (rule ostore_write_buf_ret[OF _ inv_mount_st])
               apply simp
              apply (fastforce)
              apply clarsimp
              using used_le_padding_to[OF inv_ostore inv_mount_st ]
                    inv_ostore_sync_offsD[OF inv_ostore]  apply unat_arith
             using used_le_padding_to[OF inv_ostore inv_mount_st]
                   inv_ostore_sync_offsD[OF inv_ostore]
             apply (simp add: )
            apply (clarsimp simp add: OstoreState.splits OstoreState_ext_eq_expand offs_pl_padding_to_le_eb_size[OF inv_ostore inv_mount_st])
           apply (clarsimp simp: OstoreState.splits OstoreState_ext_eq_expand  extra_padding_is_aligned[OF inv_ostore inv_mount_st])
          apply (clarsimp simp: OstoreState.splits OstoreState_ext_eq_expand)
         apply (clarsimp simp: OstoreState.splits OstoreState_ext_eq_expand)
         apply (clarsimp simp: OstoreState.splits OstoreState_ext_eq_expand)
       apply (simp add: pad_simps)
       apply (subst align32_idempotence)
        using inv_mount_st[simplified inv_mount_st_def] apply (clarsimp simp: Let_def)
       using inv_ostore_used_no_overflowD[OF inv_ostore] apply simp
      apply simp
     apply (clarsimp)
    apply (rule err[where e=eIO and n=0, simplified])
         apply simp
        apply simp
      using inv_ostore_sync_offsD[OF inv_ostore]
            \<alpha>_updates_buf_prepare_eq[OF inv_ostore inv_mount_st]
            used_neq_sync_offs_means_updates_not_Nil[OF inv_ostore]
      apply (fastforce) 
    apply (fastforce simp add: \<alpha>_ostore_medium_def)
   using inv_ostore_sync_offsD[OF inv_ostore]
         \<alpha>_updates_buf_prepare_eq[OF inv_ostore inv_mount_st]
         used_neq_sync_offs_means_updates_not_Nil[OF inv_ostore]
   apply (fastforce)
  apply simp
  apply (rename_tac ex' ostore_st'')
  apply (subgoal_tac "padding_to (mount_st, ostore_st, ostoreWriteNone) = used\<^sub>f ostore_st''")
   apply (rule suc)
      apply clarsimp
     apply clarsimp
        apply (cut_tac v=v and crc=crc and ostore_st'=ostore_st''
                 and len=len and oaddr=oaddr and nxtsqnum=nxtsqnum
                 and sqnum=sqnum in
                ostore_sync_\<alpha>_ostore_uptodate[OF inv_ostore inv_mount_st])
           apply (rule refl)
          using used_le_padding_to[OF inv_ostore inv_mount_st ]
                inv_ostore_sync_offsD[OF inv_ostore]  apply unat_arith
         using [[goals_limit=1]]
         using inv_ostore_sync_offsD[OF inv_ostore] apply simp
         apply simp
         apply simp
    apply (rename_tac v)
    apply (drule_tac t=" used\<^sub>f ostore_st''" in sym)
    using inv_step apply (simp add: \<alpha>_ostore_uptodate_def \<alpha>_updates_def buf_slice_n_n)
    apply clarsimp
    apply (rename_tac v)
    apply (cut_tac v=v and crc=crc and ostore_st'=ostore_st''
                  and len=len and oaddr=oaddr and nxtsqnum=nxtsqnum
                  and sqnum=sqnum in
                ostore_sync_\<alpha>_ostore_uptodate[OF inv_ostore inv_mount_st])
         apply (rule refl)
        using inv_ostore_sync_offsD[OF inv_ostore] apply  unat_arith
       using inv_ostore_sync_offsD[OF inv_ostore] apply  unat_arith
      using inv_bufsD[OF inv_ostore] apply simp
      apply simp
     apply (simp add: buf_slice_n_n \<alpha>_updates_def)
    apply (simp add: \<alpha>_updates_def buf_slice_n_n)
  apply (clarsimp, drule arg_cong[where f=used\<^sub>f], simp)
 done
```

How the parts fit. `refine_sync` unfolds `afs_sync_def` and
`fsop_sync_fs_def` (line 27), then peels the generated program with
`cogent_corres_conc_let_exec` (lines 29-30, 35-36) and splits the top-level
branch with `cogent_corres_if` (line 31). The error branch closes by
`corres_sync_err[OF rel]` (line 34). The success branch peels two more `let`s,
folds `ostoreWriteNone_def`, and hands the remaining obligation to the
ostore-layer interface lemma `ostore_sync_ret` (line 40); its premises are then
discharged inline by `rsync_simp` (lines 41-43) and three `cogent_corres_select`
witnesses (`length (a_medium_updates afs)`, `n`, `e`, lines 45-61). Inside
those, the named helpers close the remaining goals:

- `afs_inv_steps_updated_afsD` (line 51) turns the all-steps invariant into
  `afs_inv (updated_afs afs)` for the first witness.
- `length_updates_eqD[OF rel]` (lines 56, 58, 71) supplies the equality of the
  two update-list lengths, used to bound `n` and the `drop`.
- `fold_comp[symmetric]` (lines 67, 79) reassociates the `fold` over the update
  list, twice.
- `afs_fsop_match_updates` (line 80) closes the final on-medium/abstract match.

Lemma graph (text): `refine_sync` → `corres_sync_err` (error branch) and
`refine_sync` → `ostore_sync_ret` (success branch) → `afs_inv_steps_updated_afsD`,
`length_updates_eqD`, `fold_comp`, `afs_fsop_match_updates` (the four lemmas used
while discharging `ostore_sync_ret`'s premises).

Each is a good leaf because its statement is self-contained and its proof closes
on its own (or from named siblings):

- `fold_comp`: a standalone `fold`/`(@)` associativity fact, closed by induction
  on `xs`.
- `corres_sync_err`: the whole error case of the correspondence, closed by
  unfolding the definitions.
- `length_updates_eqD`: derives the update-list length equality from
  `afs_fsop_rel`, closed by `clarsimp` over the relation's simp bundle.
- `afs_fsop_match_updates`: a congruence for `afs_fsop_match`, closed by `simp`.
- `afs_inv_steps_updated_afsD`: the invariant step at the full update length,
  closed by instantiating the `∀` and `fastforce`.
- `ostore_sync_ret`: the ostore layer's own interface lemma; a long structured
  proof whose `suc`/`err` continuations let the client choose the success or
  error continuation (its statement is generic over `P`).

Note: `updates_take_eq` (FsopSyncR.thy 45-51) is declared right after the four
local helpers but is never cited by `refine_sync`; the glue discharges the
take/drop arithmetic inline with `take_add`/`length_drop` instead.

## Why it is good

1. `refine_sync` is declared in `FsopSyncR.thy` at line 53 (check,
   `declared`, [L53-L116](https://github.com/au-ts/cogent/blob/49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a/impl/fs/bilby/proof/refine/FsopSyncR.thy#L53-L116)).
2. The parent proof closes with `done` and contains no `sorry` (check,
   `no_sorry`, [L53-L116](https://github.com/au-ts/cogent/blob/49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a/impl/fs/bilby/proof/refine/FsopSyncR.thy#L53-L116)).
3. `fold_comp` occurs 3 times in `FsopSyncR.thy` — its declaration and the two
   `subst fold_comp[symmetric]` uses — so the leaf is genuinely reused inside
   the glue (check, `count`, [L26-L116](https://github.com/au-ts/cogent/blob/49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a/impl/fs/bilby/proof/refine/FsopSyncR.thy#L26-L116)).
4. The theorem-scale shape is 6 direct lemmas (4 local, 2 imported), glue
   64 lines, child proof lengths [3, 4, 4, 4, 7, 109], and the longest checked
   dependency chain below `refine_sync` has depth 2
   (`refine_sync` → `ostore_sync_ret` → `ostore_sync_summary_if_eb_new_ret`)
   (measurement).
5. The same move appears in the sibling theory `FsopIgetR.thy`: `refine_iget`
   (line 90) is the analogous interface lemma for `fsop_iget`, peeled with the
   same `cogent_corres_conc_let_exec`/`cogent_corres_R` rules and reusing
   `afs_inv_steps_updated_afsD` ([L90-L123](https://github.com/au-ts/cogent/blob/49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a/impl/fs/bilby/proof/refine/FsopIgetR.thy#L90-L123))
   (known-use).

In my opinion the detail worth copying is the two-layer split: the generic
`cogent_corres_*` rules handle the *shape* of the generated program (each `let`
and `if`), while the six named lemmas handle its *content* (the error case, the
invariant, the update-list arithmetic). That separation is what keeps
`refine_sync`'s glue short and its leaves independently provable.

Survey F §10 has no rule that names "interface lemma at an abstraction
boundary", so this entry's `rule` is `{f10_rule: null, relation: "none"}`; the
closest in spirit is rule 8 (backward rule: `rule r` makes `r`'s premises
children), which is how the glue applies `ostore_sync_ret`, but the move itself
is not one of the 18 rules.

## When to use it, and when not

Use it when a refinement proof must not unfold a generated (or otherwise opaque)
function, so a single boundary lemma is proven once by structure-directed
peeling with generic correspondence rules and each leaf obligation is a
self-contained named lemma. The generic statement (the exception or the
`P`-continuation universally quantified) lets each client instantiate it.

Avoid it when the generated program contains a monadic combinator with no
matching correspondence rule (the peeling stalls at that constructor), or when
the leaf obligations are not independent: the four local helpers here each close
with one automated tactic, so a goal whose obligations are intertwined would not
split this cleanly.

## Consequences

The glue depends on the exact shape of the generated program: each
`cogent_corres_conc_let_exec` peels one `let`, so a change in the Cogent code
generator's output shape breaks the peeling sequence and must be re-fitted by
hand. The generic `⋀ ex` statement moves the exception instantiation to the
client. The error branch and the update-list arithmetic are separate obligations
(`corres_sync_err`, `length_updates_eqD`, `afs_fsop_match_updates`, `fold_comp`)
that the correspondence rules do not discharge. A new monadic combinator without
a matching rule stalls the glue; and `updates_take_eq` being unused shows that
what the glue needs is narrower than the theory's helper surface.

`OstoreR.thy` is copied whole and contains an unrelated abandoned proof
`ostore_write_ret` ending in `oops` (line 2510); it is not in `refine_sync`'s
dependency cone, and the lemmas this entry names all close with `done` or `by`.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: fold_comp@impl/fs/bilby/proof/refine/FsopSyncR.thy:99, corres_sync_err@impl/fs/bilby/proof/refine/FsopSyncR.thy:66, length_updates_eqD@impl/fs/bilby/proof/refine/FsopSyncR.thy:88, afs_fsop_match_updates@impl/fs/bilby/proof/refine/FsopSyncR.thy:112, afs_inv_steps_updated_afsD@impl/fs/bilby/proof/refine/FsopSyncR.thy:83, ostore_sync_ret@impl/fs/bilby/proof/refine/FsopSyncR.thy:72; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none; oops (listed, not failed): impl/fs/bilby/proof/refine/OstoreR.thy:2510 (oops) | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(refine_sync, impl/fs/bilby/proof/refine/FsopSyncR.thy, 53-53) -> declared: refine_sync is declared at impl/fs/bilby/proof/refine/FsopSyncR.thy:53 | check_claims.py |
| 2 | verified | no_sorry(impl/fs/bilby/proof/refine/FsopSyncR.thy, 53-116) -> no_sorry: none of sorry in impl/fs/bilby/proof/refine/FsopSyncR.thy:53-116 | check_claims.py |
| 3 | verified | count(fold_comp, 3, impl/fs/bilby/proof/refine/FsopSyncR.thy) -> count: fold_comp occurs 3 times in 1 file(s) matching impl/fs/bilby/proof/refine/FsopSyncR.thy | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/au-ts/cogent at commit `49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a`, under `GPL-2.0-only`; see the [source note](../../sources/cogent/SOURCE.md) for the licence text and attribution.
