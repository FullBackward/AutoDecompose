# Per-callee refinement lemmas for the ostore sync function

| | |
|---|---|
| Kind | instance |
| Move | per-callee-lemma |
| Language | isabelle |
| Status | draft |
| Source | [cogent](../../sources/cogent/SOURCE.md) at `49b6ceb0d033` |
| Licence | `GPL-2.0-only` |

## Intent

The refinement of the generated `ostore_sync` operation is proved by one
`_ret` lemma per function its body calls — `prepare_wbuf`,
`ostore_sync_summary_if_eb_new`, `ostore_write_buf` — so the sync glue only
threads their post-states. The glue's own case split (`sync_offs = used`) and
the padding alignment are discharged by five small side lemmas.

## The decomposition

### parent `ostore_sync_ret`: [`impl/fs/bilby/proof/refine/OstoreR.thy` lines 2379-2487](https://github.com/au-ts/cogent/blob/49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a/impl/fs/bilby/proof/refine/OstoreR.thy#L2379-L2487) ([local copy](code/impl/fs/bilby/proof/refine/OstoreR.thy))

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

### child `prepare_wbuf_ret`: [`impl/fs/bilby/proof/refine/OstoreR.thy` lines 1480-1661](https://github.com/au-ts/cogent/blob/49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a/impl/fs/bilby/proof/refine/OstoreR.thy#L1480-L1661) ([local copy](code/impl/fs/bilby/proof/refine/OstoreR.thy))

```isabelle
lemma prepare_wbuf_ret:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and inv_mount_st: "inv_mount_st mount_st"
  and inv_step: "inv_\<alpha>_ostore (\<alpha>_ostore_uptodate ostore_st)"
  and pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
  and used_gt_zero: "0 < used\<^sub>f ostore_st"
  and sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"
  and err:                    
   "\<And>ex'.  P ((ex',ostore_st), Error eOverflow)"
  and suc:
  "\<And>ex' ostore_st'. \<lbrakk>
     inv_ostore mount_st ostore_st';
     inv_\<alpha>_ostore (\<alpha>_ostore_uptodate ostore_st');
     \<exists>len sqnum crc oaddr nxtsqnum. ostore_st' =
       ostore_st\<lparr>wbuf\<^sub>f := wbuf\<^sub>f ostore_st\<lparr>data\<^sub>f:=WordArrayT.make $
         buf_prepared ostore_st (used\<^sub>f ostore_st) pad_to (prepared_pad_obj ostore_st pad_to crc)\<rparr>,
         used\<^sub>f := pad_to,
         fsm_st\<^sub>f := prepared_fsm_padding_obj ostore_st pad_to,
         OstoreState.oaddr\<^sub>f:= oaddr, 
         OstoreState.next_sqnum\<^sub>f:= nxtsqnum,
         opad\<^sub>f:=opad\<^sub>f ostore_st \<lparr>Obj.len\<^sub>f:=len, Obj.sqnum\<^sub>f := sqnum, Obj.crc\<^sub>f := crc\<rparr>\<rparr>;
     OstoreState.next_sqnum\<^sub>f ostore_st \<le> OstoreState.next_sqnum\<^sub>f ostore_st'
     \<rbrakk>
     \<Longrightarrow>  P ((ex',ostore_st'), Success ())"
  notes pad_simps = padding_to_eq_align32_simp[OF inv_mount_st_no_summaryD[OF inv_mount_st]]
  notes pad_to' = pad_to[simplified pad_simps]
  and   ostore_update_padding_obj' = ostore_update_padding_obj_def[unfolded tuple_simps sanitizers]
  shows "P (prepare_wbuf (ex, mount_st, ostore_st, pad_to))"
 proof cases
  assume no_padding_obj: "pad_to - used\<^sub>f ostore_st < bilbyFsObjHeaderSize"
  let ?wbuf = "buf_memset (wbuf\<^sub>f ostore_st, used\<^sub>f ostore_st, pad_to - used\<^sub>f ostore_st, bilbyFsPadByte)"
  let ?ostore_st = "ostore_st\<lparr>wbuf\<^sub>f := ?wbuf, used\<^sub>f := pad_to\<rparr>"
  have bound: "unat (bound\<^sub>f (wbuf\<^sub>f ostore_st)) \<le> length (\<alpha>wa (data\<^sub>f (wbuf\<^sub>f ostore_st)))"
   using  inv_ostore_bound_le_lenD[OF inv_ostore] by simp
  have index_unchanged: "index_st\<^sub>f ?ostore_st = index_st\<^sub>f ostore_st" by simp
  have list_eb_log_eq: "list_eb_log (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ?ostore_st)) = list_eb_log (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st))"
   by (simp add: list_eb_log_def)
  have pad_to_le: "unat pad_to \<le> length (\<alpha>wa $ data\<^sub>f $ wbuf\<^sub>f ostore_st)"
  using align32_upper_bound[where v="used\<^sub>f ostore_st" and al="io_size\<^sub>f (super\<^sub>f mount_st)" and bound="eb_size\<^sub>f (super\<^sub>f mount_st)"]
    inv_ostore[simplified inv_ostore_def]  inv_mount_st[simplified Let_def inv_mount_st_def]
    inv_ostore_eb_size_wbuf_eqD[OF inv_ostore]
   by (simp add : pad_to')  unat_arith

  have used_le_pad_to: "used\<^sub>f ostore_st \<le>  pad_to"
   using align32_le[where v="used\<^sub>f ostore_st" and al="io_size\<^sub>f (super\<^sub>f mount_st)"] inv_mount_st[simplified inv_mount_st_def Let_def]
          pad_to' inv_ostore_used_no_overflowD[OF inv_ostore]
   by simp
  have unat_used_le_pad_to: "unat (used\<^sub>f ostore_st) \<le> unat pad_to" using used_le_pad_to by unat_arith
  have \<alpha>_updates_eq: "\<alpha>_updates ?ostore_st = \<alpha>_updates ostore_st"
   by (rule prepare_wbuf_memset_\<alpha>_updates_eq[OF inv_ostore inv_mount_st pad_to sync_lt_used])
  have \<alpha>_medium_eq: "\<alpha>_ostore_medium ?ostore_st = \<alpha>_ostore_medium ostore_st"
   by (simp add: \<alpha>_ostore_medium_def abstract_mount_\<alpha>_ostore_def list_eb_log_eq)
  have inv_step': "inv_\<alpha>_ostore (\<alpha>_ostore_uptodate ?ostore_st)"
   using inv_step
   by (clarsimp simp add: \<alpha>_ostore_uptodate_def Let_def \<alpha>_medium_eq \<alpha>_updates_eq)
  have inv_ostore': "inv_ostore mount_st ?ostore_st"
   using inv_ostore_padding_bytes_preserved[OF inv_ostore inv_mount_st pad_to used_gt_zero sync_lt_used] .
  show ?thesis
  unfolding prepare_wbuf_def[unfolded tuple_simps sanitizers]
  apply (fold bilbyFsObjHeaderSize_def)
  using no_padding_obj apply (simp add: pad_to')
  apply (rule suc)
      apply (fold bilbyFsPadByte_def)
  using inv_ostore'  apply (simp add: pad_to padding_to_def ostoreWriteNone_def)
     apply(fastforce intro: subst[where P=\<open>inv_ostore mount_st\<close>,rotated])
  using inv_step' apply (simp add: pad_to padding_to_def ostoreWriteNone_def)
    apply (fastforce intro: subst[where P=\<open>\<lambda>x. inv_\<alpha>_ostore (\<alpha>_ostore_uptodate x)\<close>,rotated])
   apply (rule_tac x="Obj.len\<^sub>f (opad\<^sub>f ?ostore_st)" in exI)
   apply (rule_tac x="Obj.sqnum\<^sub>f (opad\<^sub>f ?ostore_st)" in exI)
   apply (rule_tac x="Obj.crc\<^sub>f (opad\<^sub>f ?ostore_st)" in exI)
   apply (rule_tac x="(OstoreState.oaddr\<^sub>f ?ostore_st)" in exI)
   apply (rule_tac x="(OstoreState.next_sqnum\<^sub>f ?ostore_st)" in exI)
      apply (subst buf_memset_eq)
         using bound apply simp
        using used_le_padding_to[OF inv_ostore inv_mount_st] apply (simp add: pad_to' pad_simps)
   apply (fastforce simp add: pad_to padding_to_def 
           ostoreWriteNone_def buf_prepared_def prepared_fsm_padding_obj_def)
  apply simp
 done

 next
  assume padding_obj: "\<not> (pad_to - used\<^sub>f ostore_st < bilbyFsObjHeaderSize)"

  have pad_to_upd:
    "used\<^sub>f ostore_st +
     Obj.len\<^sub>f (ostore_update_padding_obj(opad\<^sub>f ostore_st, OstoreState.next_sqnum\<^sub>f ostore_st,
               pad_to - used\<^sub>f ostore_st - bilbyFsObjHeaderSize))
      = pad_to"
    by (simp add: ostore_update_padding_obj' pad_to pad_simps bilbyFsObjHeaderSize_def)

  have dummy_upds: "\<And>x. x = x\<lparr>fsm_st\<^sub>f := fsm_st\<^sub>f x, OstoreState.oaddr\<^sub>f := OstoreState.oaddr\<^sub>f x\<rparr>"
   by simp

  have dummy_upds': "\<And>x a b c d. x\<lparr>OstoreState.next_sqnum\<^sub>f := a, used\<^sub>f := b, opad\<^sub>f := c, wbuf\<^sub>f := d\<rparr> = x\<lparr>wbuf\<^sub>f := d, opad\<^sub>f := c, used\<^sub>f := b, OstoreState.next_sqnum\<^sub>f := a, fsm_st\<^sub>f := fsm_st\<^sub>f x, OstoreState.oaddr\<^sub>f := OstoreState.oaddr\<^sub>f x\<rparr>"
    by simp

  have ostore_upds_reorder: "\<And>x a b c d e f. x\<lparr>OstoreState.next_sqnum\<^sub>f := a, used\<^sub>f := b, opad\<^sub>f := c, wbuf\<^sub>f := d, fsm_st\<^sub>f := e, OstoreState.oaddr\<^sub>f := f\<rparr> = x\<lparr>wbuf\<^sub>f := d, opad\<^sub>f := c, used\<^sub>f := b, OstoreState.next_sqnum\<^sub>f := a, fsm_st\<^sub>f := e, OstoreState.oaddr\<^sub>f := f\<rparr>" by simp

  have ostore_upds_reorder': "\<And>x a b c d e f. x\<lparr>OstoreState.next_sqnum\<^sub>f := a, used\<^sub>f := b, opad\<^sub>f := c, wbuf\<^sub>f := d, fsm_st\<^sub>f := e, OstoreState.oaddr\<^sub>f := f\<rparr> = x\<lparr>wbuf\<^sub>f := d, used\<^sub>f := b, fsm_st\<^sub>f := e, OstoreState.oaddr\<^sub>f := f, OstoreState.next_sqnum\<^sub>f := a, opad\<^sub>f := c\<rparr>" by simp

  have obj_upds_reorder: "\<And>x a b c. x \<lparr>trans\<^sub>f := a, Obj.len\<^sub>f := b, Obj.sqnum\<^sub>f := c\<rparr> = x \<lparr>Obj.sqnum\<^sub>f := c, Obj.len\<^sub>f := b, trans\<^sub>f := a\<rparr>" by simp

  from padding_obj show ?thesis
    unfolding prepare_wbuf_def[unfolded tuple_simps sanitizers, folded bilbyFsObjHeaderSize_def]
    apply (simp add: Let_def)
    apply (rule safe_add64)
     apply (simp add: Let_def, fold eOverflow_def )
     apply (simp add: err)
    apply (simp add: Let_def )
    apply (rule serialise_Obj_ret)
        apply (simp add:  pad_to' bilbyFsObjHeaderSize_def ostore_update_padding_obj')
        using used_le_padding_to[OF inv_ostore inv_mount_st] apply (simp add: pad_simps) 
       using opad_is_valid_ObjHeader[OF inv_ostore inv_mount_st padding_obj pad_to] apply simp
      using inv_opadD[OF inv_ostore] apply (clarsimp simp add: ostore_update_padding_obj' )
      using inv_opadD[OF inv_ostore] apply (clarsimp simp add: ostore_update_padding_obj' )
       using inv_ostore_eb_size_wbuf_eqD[OF inv_ostore]
             inv_ostore_wbuf_boundD[OF inv_ostore]
             padding_to_le_eb_size[OF inv_ostore inv_mount_st]
             apply (clarsimp simp add: pad_to buf_simps ostore_update_padding_obj' bilbyFsObjHeaderSize_def)
      apply (rename_tac buf')
      apply (simp add: prod.case_eq_if)
       apply (rule update_obj_pad_ret[OF _ inv_mount_st])
       apply (rule ssubst[OF dummy_upds'])
       apply (rule inv_ostore_preserved_padding_obj[OF inv_ostore inv_mount_st _ used_gt_zero sync_lt_used])
          using pad_to_upd apply (simp add: pad_to)
         apply (simp add: ostore_update_padding_obj' pad_to pad_simps bilbyFsObjHeaderSize_def)
         apply (rule_tac x="crc\<^sub>f (opad\<^sub>f ostore_st)" in exI)
         apply simp

         using inv_ostore_valid_pad_objD[OF inv_ostore] apply (clarsimp simp:ostore_update_padding_obj' valid_pad_obj_def is_valid_Obj_def)
        apply (simp add: ostore_update_padding_obj' bilbyFsObjHeaderSize_def)
       using inv_opadD[OF inv_ostore] apply (clarsimp simp add:  ostore_update_padding_obj' bilbyFsObjHeaderSize_def)
      using inv_ostore_wbuf_eb_rangeD[OF inv_ostore]
      apply (simp add: ostore_update_padding_obj' pad_to pad_simps bilbyFsObjHeaderSize_def)
     using inv_ostore_wbuf_eb_rangeD[OF inv_ostore] apply simp

    apply (rule suc)
      apply simp
     apply(subst ostore_upds_reorder)
     apply (rule inv_ostore_preserved_padding_obj[OF inv_ostore 
                    inv_mount_st _ used_gt_zero sync_lt_used])
           using pad_to_upd apply (simp add: pad_to)
          apply (simp add: ostore_update_padding_obj' pad_to pad_simps bilbyFsObjHeaderSize_def)
          apply (rule_tac x="crc\<^sub>f (opad\<^sub>f ostore_st)" in exI)
          apply simp
         apply (simp add: ostore_update_padding_obj' bilbyFsObjHeaderSize_def)
         using inv_ostore_valid_pad_objD[OF inv_ostore] apply (clarsimp simp:ostore_update_padding_obj' valid_pad_obj_def is_valid_Obj_def)
       using inv_opadD[OF inv_ostore] apply (clarsimp simp add:  ostore_update_padding_obj' bilbyFsObjHeaderSize_def)
      using inv_ostore_wbuf_eb_rangeD[OF inv_ostore]
      apply (simp add: ostore_update_padding_obj' pad_to pad_simps bilbyFsObjHeaderSize_def)
     using padding_obj apply (simp add: prepared_fsm_padding_obj_def pad_simps bilbyFsObjHeaderSize_def pad_to' ostore_update_padding_obj')
       apply simp
     apply(subst ostore_upds_reorder)
    apply (rule inv_step_padding_obj[OF inv_ostore inv_mount_st _  used_gt_zero sync_lt_used ])
          using pad_to_upd apply (simp add: pad_to)
         apply (rule_tac x="crc\<^sub>f (opad\<^sub>f ostore_st)" in exI)
         using pad_to_upd apply (clarsimp simp add: pad_to ostore_update_padding_obj_def Let\<^sub>d\<^sub>s_def)
        using inv_ostore_valid_pad_objD[OF inv_ostore] apply (clarsimp simp: valid_pad_obj_def ostore_update_padding_obj' is_valid_Obj_def)
       using pad_to_upd apply (clarsimp simp add: pad_to ostore_update_padding_obj')
      using pad_to_upd apply (clarsimp simp add: pad_to ostore_update_padding_obj')
     using pad_to_upd apply (clarsimp simp add: pad_to ostore_update_padding_obj' prepared_fsm_padding_obj_def)
    using inv_step apply simp
   apply simp
  using [[goals_limit=2]]
   apply (rule_tac x="pad_to - used\<^sub>f ostore_st" in exI)
      apply (rule_tac x="OstoreState.next_sqnum\<^sub>f ostore_st" in exI)
      apply (rule_tac x="crc\<^sub>f (opad\<^sub>f ostore_st)" in exI)
      apply (rule_tac x="v" in exI)
      apply (rule_tac x="OstoreState.next_sqnum\<^sub>f ostore_st + 1" in exI)
      apply simp
     apply (simp add: prepared_fsm_padding_obj_def buf_prepared_def padding_obj pad_to_upd)
     apply (simp add: ostore_update_padding_obj' prepared_pad_obj_def Let_def
         bilbyFsObjHeaderSize_def prepared_pad_obj_no_crc_def bilbyFsTransCommit_def  )
 (* FIX Cogent code, currently it updates the otype field but shouldn't because
    the type of opad is part of the invariant *)
      using inv_opadD[OF inv_ostore] apply (clarsimp simp: bilbyFsTransCommit_def)
      using inv_ostore_wbuf_eb_rangeD[OF inv_ostore]
      apply (subst ostore_upds_reorder')
      apply (subst obj_upds_reorder)+
      apply (simp)+
      done
  qed
```

### child `ostore_sync_summary_if_eb_new_ret`: [`impl/fs/bilby/proof/refine/OstoreR.thy` lines 1674-1680](https://github.com/au-ts/cogent/blob/49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a/impl/fs/bilby/proof/refine/OstoreR.thy#L1674-L1680) ([local copy](code/impl/fs/bilby/proof/refine/OstoreR.thy))

```isabelle
lemma ostore_sync_summary_if_eb_new_ret:
  "inv_ostore mount_st ostore_st \<Longrightarrow>
   inv_mount_st mount_st \<Longrightarrow>
   inv_\<alpha>_ostore (\<alpha>_ostore_uptodate ostore_st) \<Longrightarrow>
   (\<And>ex'. P ((ex', ostore_st), R.Success ())) \<Longrightarrow>
  P (ostore_sync_summary_if_eb_new (ex, mount_st, ostore_st, ostoreWriteNone))"
 by (simp add: ostore_sync_summary_if_eb_new_def[unfolded tuple_simps sanitizers])
```

### child `ostore_write_buf_ret`: [`impl/fs/bilby/proof/refine/OstoreR.thy` lines 2314-2354](https://github.com/au-ts/cogent/blob/49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a/impl/fs/bilby/proof/refine/OstoreR.thy#L2314-L2354) ([local copy](code/impl/fs/bilby/proof/refine/OstoreR.thy))

```isabelle
lemma ostore_write_buf_ret:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and inv_mount_st: "inv_mount_st mount_st"
  and inv_step: "inv_\<alpha>_ostore (\<alpha>_ostore_uptodate ostore_st)"
  and used_gt_zero: "0 < used\<^sub>f ostore_st"
  and sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"
  and offs_ok: "unat (sync_offs\<^sub>f ostore_st) + unat nb_bytes \<le> unat (eb_size\<^sub>f (super\<^sub>f mount_st))"
  and nb_bytes_ok: "io_size\<^sub>f (super\<^sub>f mount_st) udvd nb_bytes"
  and sync_offs: "sync_offs = sync_offs\<^sub>f ostore_st"
  and nb_bytes_eq: "sync_offs\<^sub>f ostore_st + nb_bytes = used\<^sub>f ostore_st"
  and nb_bytes_eq_pad_to_minus_sync: "nb_bytes = padding_to (mount_st, ostore_st, ostoreWriteNone) - sync_offs\<^sub>f ostore_st"
  and err:
   "\<And>ex'. P ((ex',ostore_st), Error eIO)"
  and suc:
  "\<And>ex' ostore_st'. \<lbrakk>
     inv_ostore mount_st (ostore_st' \<lparr> sync_offs\<^sub>f := used\<^sub>f ostore_st\<rparr>);
     \<exists>v. ostore_st'\<lparr>OstoreState.ubi_vol\<^sub>f := v\<rparr> = ostore_st;
     \<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st') = (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st))[(unat (wbuf_eb\<^sub>f ostore_st)):=((\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st)!(unat (wbuf_eb\<^sub>f ostore_st)))@buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st + nb_bytes))] \<rbrakk> \<Longrightarrow>
      P ((ex', ostore_st'), Success ())
 "
shows
"P (ostore_write_buf(ex, mount_st, ostore_st, sync_offs, nb_bytes, ostoreWriteNone))"
unfolding ostore_write_buf_def[unfolded tuple_simps sanitizers, simplified take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def]
  apply (simp add: sync_offs)
  apply safe
   apply (rule wubi_leb_write_ret[where mount_st=mount_st])
         apply (rule length_ubi_buf_eq_sync_offsD[OF inv_ostore inv_mount_st])
        apply (rule inv_ostore_wbuf_lengthD[OF inv_ostore])
       apply (rule offs_ok)
      apply (rule nb_bytes_ok)
     using inv_bufsD[OF inv_ostore] apply clarsimp
    apply (simp add: err)
   apply simp
   apply (rule suc)
      apply (erule (2) inv_ostore_updated_ubi_preserved[OF inv_ostore inv_mount_st nb_bytes_eq_pad_to_minus_sync _  used_gt_zero sync_lt_used])
       apply (simp add: nb_bytes_eq)
    apply (rule_tac x="OstoreState.ubi_vol\<^sub>f ostore_st" in exI, fastforce)
   apply simp
  apply (rule suc)
     using sync_lt_used nb_bytes_eq inv_ostore apply (clarsimp simp: word_not_0_gr_n)+
 done
```

### child `extra_padding_is_aligned`: [`impl/fs/bilby/proof/refine/OstoreR.thy` lines 2356-2374](https://github.com/au-ts/cogent/blob/49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a/impl/fs/bilby/proof/refine/OstoreR.thy#L2356-L2374) ([local copy](code/impl/fs/bilby/proof/refine/OstoreR.thy))

```isabelle
lemma extra_padding_is_aligned:
 assumes inv_ostore: "inv_ostore mount_st ostore_st"
 and     inv_mount_st: "inv_mount_st mount_st"
 and     sync_neq_used: "sync_offs\<^sub>f ostore_st \<noteq> used\<^sub>f ostore_st"
 shows
 "io_size\<^sub>f (super\<^sub>f mount_st) udvd  padding_to (mount_st, ostore_st, ostoreWriteNone) - sync_offs\<^sub>f ostore_st"
proof -
  have io_size_dvd_sync_offs: "io_size\<^sub>f (super\<^sub>f mount_st) udvd sync_offs\<^sub>f ostore_st"
    using inv_ostore by (clarsimp simp: inv_ostore_def)
  show ?thesis
  using inv_mount_st[simplified inv_mount_st_def Let_def]
  apply clarsimp
  apply (drule al_dvd_align32[OF _ inv_ostore_used_no_overflowD[OF inv_ostore]])
  using sync_offs_le_padding_to[OF inv_ostore inv_mount_st ]
        io_size_dvd_sync_offs
  apply (simp add: padding_to_def[unfolded tuple_simps sanitizers] ostoreWriteNone_def )
  apply (simp add: udvd_iff_dvd word_le_nat_alt unat_sub_if')
 done
qed
```

### child `ostore_sync_\<alpha>_ostore_uptodate`: [`impl/fs/bilby/proof/refine/OstoreR.thy` lines 1998-2083](https://github.com/au-ts/cogent/blob/49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a/impl/fs/bilby/proof/refine/OstoreR.thy#L1998-L2083) ([local copy](code/impl/fs/bilby/proof/refine/OstoreR.thy))

```isabelle
lemma ostore_sync_\<alpha>_ostore_uptodate:
  assumes inv_ostore: "inv_ostore mount_st ostore_st"
  and     inv_mount_st: "inv_mount_st mount_st"
  and     pad_to: "pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)"
  and     used_gt_zero: "0 < used\<^sub>f ostore_st"
  and     sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"
  and     wubi: "list_eb_log (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st')) = 
list_eb_log ((\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st))
 [unat (wbuf_eb\<^sub>f ostore_st) :=
    \<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st) ! unat (wbuf_eb\<^sub>f ostore_st) @
    buf_slice
     (wbuf\<^sub>f ostore_st
      \<lparr>data\<^sub>f :=
         WordArrayT.make
          (buf_prepared ostore_st (used\<^sub>f ostore_st)
            (padding_to (mount_st, ostore_st, ostoreWriteNone))
            (prepared_pad_obj ostore_st (padding_to (mount_st, ostore_st, ostoreWriteNone)) crc))\<rparr>)
     (sync_offs\<^sub>f ostore_st) (padding_to (mount_st, ostore_st, ostoreWriteNone))])"
     (is "... = list_eb_log (?ubi[?wbuf_eb:=?old_ubi@?buf_prepared])")
 and ostore_m: "ostore_st'\<lparr>OstoreState.ubi_vol\<^sub>f := v\<rparr> = ostore_st
       \<lparr>wbuf\<^sub>f := wbuf\<^sub>f ostore_st
          \<lparr>data\<^sub>f :=
             WordArrayT.make
              (buf_prepared ostore_st (used\<^sub>f ostore_st)
                (padding_to (mount_st, ostore_st, ostoreWriteNone))
                (prepared_pad_obj ostore_st (padding_to (mount_st, ostore_st, ostoreWriteNone)) crc))\<rparr>,
          used\<^sub>f := padding_to (mount_st, ostore_st, ostoreWriteNone),
          fsm_st\<^sub>f := prepared_fsm_padding_obj ostore_st (used\<^sub>f ostore_st'), OstoreState.oaddr\<^sub>f := oaddr,
          OstoreState.next_sqnum\<^sub>f := nxtsqnum, opad\<^sub>f := opad\<^sub>f ostore_st\<lparr>Obj.len\<^sub>f := len, Obj.sqnum\<^sub>f := sqnum, crc\<^sub>f := crc\<rparr>\<rparr>" 
          (is "... = ?ostore_st")

  notes invs_pad_offs = inv_ostore inv_mount_st pad_to used_gt_zero sync_lt_used

shows
 "\<alpha>_ostore_medium (ostore_st'\<lparr>sync_offs\<^sub>f := used\<^sub>f ostore_st'\<rparr>) = \<alpha>_ostore_uptodate ostore_st"
 
proof -

have sort_key_trans_key_eq: "sort_key trans_order (concat  (map (prod.snd \<circ> list_trans_no_pad)
   (drop (unat bilbyFsFirstLogEbNum) (?ubi
       [?wbuf_eb := ?ubi ! ?wbuf_eb @ ?buf_prepared])))) =
 sort_key trans_order (concat  (map (prod.snd \<circ> list_trans_no_pad)
   (drop (unat bilbyFsFirstLogEbNum) ?ubi @ [?buf_prepared])))"
   apply (subst sort_key_concat_ignores_order[OF inv_ostore _ _ used_gt_zero])
       using snd_list_trans_buf_prepared_eq[OF invs_pad_offs]
       apply (simp only: )
       using inv_logD[OF inv_ostore]
       apply clarsimp
      apply (simp only: map_append)
       using snd_list_trans_buf_prepared_eq[OF invs_pad_offs]
             inv_logD[OF inv_ostore]
       apply (fastforce simp: list_eb_log_def)
      using sync_lt_used inv_bufsD[OF inv_ostore] apply clarsimp
      using valid_list_trans_buf_prepared_eq[OF invs_pad_offs]
      apply (simp add: pad_to)+
   done

  have sort_trans_key_list_eb_log_eq_append_list_trans: 
  "sort_key trans_order (concat (list_eb_log (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st')))) =
    sort_key trans_order (concat (list_eb_log (\<alpha>wubi (OstoreState.ubi_vol\<^sub>f ostore_st))) @
      prod.snd (list_trans_no_pad (buf_slice (wbuf\<^sub>f ostore_st) (sync_offs\<^sub>f ostore_st) (used\<^sub>f ostore_st))))"
   apply (simp only: wubi)
   apply (simp add:  ostore_m list_eb_log_def Let_def)
   apply (simp only: sort_key_trans_key_eq)
   apply simp
   apply (simp only: snd_list_trans_buf_prepared_eq[OF invs_pad_offs])
  done

 from inv_logD[OF inv_ostore] have trans_order':
 "\<forall>x\<in>set (concat $ list_eb_log $ \<alpha>wubi $ OstoreState.ubi_vol\<^sub>f ostore_st).
       \<forall>y\<in>set (prod.snd (list_trans_no_pad (buf_slice (wbuf\<^sub>f ostore_st)
                (sync_offs\<^sub>f ostore_st) (used\<^sub>f ostore_st)))).
          trans_order x < trans_order y"
    by (simp add: snd_list_trans_buf_prepared_eq[OF inv_ostore inv_mount_st])

show ?thesis
   apply (simp add: \<alpha>_ostore_uptodate_def \<alpha>_ostore_medium_def abstract_mount_\<alpha>_ostore_def
       wubi \<alpha>_updates_def del: list_trans.simps)
   apply (simp only: fold_id_append map_ostore_update_append)
   apply (rule arg_cong[where f="\<lambda>x. fold id x Map.empty"])
   apply (rule arg_cong[where f="map ostore_update"])
   apply (subst inv_ostore_list_trans_wbuf_sorted[OF inv_ostore, symmetric])
   using sort_key_append[OF trans_order'[unfolded fun_app_def] ]
   apply (simp add: sort_trans_key_list_eb_log_eq_append_list_trans[simplified wubi])
  done
qed
```

### child `\<alpha>_updates_buf_prepare_eq`: [`impl/fs/bilby/proof/refine/OstoreR.thy` lines 2246-2312](https://github.com/au-ts/cogent/blob/49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a/impl/fs/bilby/proof/refine/OstoreR.thy#L2246-L2312) ([local copy](code/impl/fs/bilby/proof/refine/OstoreR.thy))

```isabelle
lemma \<alpha>_updates_buf_prepare_eq:
assumes inv_ostore: "inv_ostore mount_st ostore_st"
and     inv_mount_st: "inv_mount_st mount_st"
and     sync_lt_used: "sync_offs\<^sub>f ostore_st < used\<^sub>f ostore_st"
shows
 "
  OstoreState.next_sqnum\<^sub>f ostore_st \<le> next_sqnum \<Longrightarrow>
  inv_ostore mount_st
   (ostore_st
    \<lparr>wbuf\<^sub>f := wbuf\<^sub>f ostore_st
       \<lparr>data\<^sub>f :=
          WordArrayT.make
           (buf_prepared ostore_st (used\<^sub>f ostore_st)
             (padding_to (mount_st, ostore_st, ostoreWriteNone))
             (prepared_pad_obj ostore_st (padding_to (mount_st, ostore_st, ostoreWriteNone)) crc))\<rparr>,
       used\<^sub>f := padding_to (mount_st, ostore_st, ostoreWriteNone),
      fsm_st\<^sub>f := prepared_fsm_padding_obj ostore_st (padding_to (mount_st, ostore_st, ostoreWriteNone)), OstoreState.oaddr\<^sub>f := oaddr,
      OstoreState.next_sqnum\<^sub>f := nxtsqnum, opad\<^sub>f := opad\<^sub>f ostore_st\<lparr>Obj.len\<^sub>f := len, Obj.sqnum\<^sub>f := sqnum, crc\<^sub>f := crc\<rparr>\<rparr>) \<Longrightarrow>
  \<alpha>_updates
       (ostore_st
        \<lparr>wbuf\<^sub>f := wbuf\<^sub>f ostore_st
           \<lparr>data\<^sub>f :=
              WordArrayT.make
               (buf_prepared ostore_st (used\<^sub>f ostore_st)
                 (padding_to (mount_st, ostore_st, ostoreWriteNone))
                 (prepared_pad_obj ostore_st (padding_to (mount_st, ostore_st, ostoreWriteNone)) crc))\<rparr>,
           used\<^sub>f := padding_to (mount_st, ostore_st, ostoreWriteNone),
          fsm_st\<^sub>f := prepared_fsm_padding_obj ostore_st (padding_to (mount_st, ostore_st, ostoreWriteNone)), OstoreState.oaddr\<^sub>f := oaddr,
          OstoreState.next_sqnum\<^sub>f := nxtsqnum, opad\<^sub>f := opad\<^sub>f ostore_st\<lparr>Obj.len\<^sub>f := len, Obj.sqnum\<^sub>f := sqnum, crc\<^sub>f := crc\<rparr>
        \<rparr>) =  \<alpha>_updates ostore_st"
   proof -
     obtain pad_to::U32 where pad_to:"pad_to = padding_to (mount_st, ostore_st, ostoreWriteNone)" by simp
     have used_gt_zero: "0 < used\<^sub>f ostore_st"
      using sync_lt_used by unat_arith

     have bound: "unat (bound\<^sub>f (wbuf\<^sub>f ostore_st)) \<le> length (\<alpha>wa (data\<^sub>f (wbuf\<^sub>f ostore_st)))"
        using  inv_ostore_bound_le_lenD[OF inv_ostore] by simp
     have used_of: "used\<^sub>f ostore_st \<le> used\<^sub>f ostore_st + (pad_to - used\<^sub>f ostore_st)"
        apply (simp add: pad_to)
        using used_le_padding_to[OF inv_ostore inv_mount_st] by simp

    show ?thesis
   apply (simp add: buf_prepared_def)
   apply (case_tac "padding_to (mount_st, ostore_st, ostoreWriteNone) - used\<^sub>f ostore_st
                 < bilbyFsObjHeaderSize")

    apply (simp add: \<alpha>_updates_def)
    apply (rule arg_cong[where f="map ostore_update"])
    using buf_slice_buf_memset_is_append_padding[OF inv_ostore inv_mount_st pad_to, where frm="sync_offs\<^sub>f ostore_st", simplified pad_to]
    using  buf_memset_eq[OF bound used_of, simplified pad_to]
    apply (simp )
    apply (rule snd_list_trans_no_pad_padding_unchanged)
    using inv_bufsD[OF inv_ostore] sync_lt_used
     apply (simp add: valid_list_trans_no_pad_imp_valid_list_trans)
   apply (simp add: \<alpha>_updates_def)
   apply (rule arg_cong[where f="map ostore_update"])
   apply (rule snd_list_trans_no_pad_padding_obj_sync_pad_to[OF inv_ostore inv_mount_st pad_to used_gt_zero sync_lt_used, simplified pad_to])
   apply (rule valid_commit_pad_obj[OF inv_ostore inv_mount_st pad_to, simplified is_valid_ObjTrans, THEN conjunct1])
      apply (rule_tac x=crc in exI)
      apply (simp add: prepared_pad_obj_def prepared_pad_obj_no_crc_def ostore_update_padding_obj' pad_to bilbyFsObjHeaderSize_def bilbyFsTransCommit_def)+
     apply (rule_tac x=crc in exI)
     apply (simp add: prepared_pad_obj_def prepared_pad_obj_no_crc_def ostore_update_padding_obj' pad_to bilbyFsObjHeaderSize_def bilbyFsTransCommit_def)+
          using inv_ostore_valid_pad_objD[OF inv_ostore]
      apply (clarsimp simp add: prepared_pad_obj_no_crc_def valid_pad_obj_def prepared_pad_obj_def is_valid_Obj_def)
     apply simp
  done
qed
```

### child `used_neq_sync_offs_means_updates_not_Nil`: [`impl/fs/bilby/proof/spec/OstoreInvS.thy` lines 846-853](https://github.com/au-ts/cogent/blob/49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a/impl/fs/bilby/proof/spec/OstoreInvS.thy#L846-L853) ([local copy](code/impl/fs/bilby/proof/spec/OstoreInvS.thy))

```isabelle
lemma used_neq_sync_offs_means_updates_not_Nil:
assumes inv_ostore: "inv_ostore mount_st ostore_st"
shows
 "sync_offs\<^sub>f ostore_st \<noteq> used\<^sub>f ostore_st \<Longrightarrow>
  \<alpha>_updates ostore_st \<noteq> []"
 unfolding \<alpha>_updates_def 
using inv_bufsD[OF inv_ostore]  inv_ostore_sync_offsD[OF inv_ostore]
 by (fastforce simp add: valid_list_trans_no_pad_def)
```

### child `used_eq_sync_offs_means_no_update`: [`impl/fs/bilby/proof/spec/OstoreInvS.thy` lines 776-779](https://github.com/au-ts/cogent/blob/49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a/impl/fs/bilby/proof/spec/OstoreInvS.thy#L776-L779) ([local copy](code/impl/fs/bilby/proof/spec/OstoreInvS.thy))

```isabelle
lemma used_eq_sync_offs_means_no_update:
 "sync_offs\<^sub>f ostore_st = used\<^sub>f ostore_st \<Longrightarrow>
  \<alpha>_updates ostore_st = []"
 unfolding \<alpha>_updates_def by (simp add:  buf_simps)
```

How the parts fit. The glue `ostore_sync_ret` (lines 2379-2487) first unfolds
the generated `ostore_sync_def`, then splits on `sync_offs = used`. The `=`
branch closes immediately: `suc` needs `α_updates = []`, supplied by the side
lemma `used_eq_sync_offs_means_no_update`. The `≠` branch is the call
sequence of the generated body, discharged one callee at a time:

```
ostore_sync_ret (glue)
├── case sync_offs = used ── used_eq_sync_offs_means_no_update (⇒ α_updates = [])
└── case sync_offs ≠ used
    ├── prepare_wbuf_ret           (first callee: prepare_wbuf)
    │     └─ used_neq_sync_offs_means_updates_not_Nil (⇒ α_updates ≠ [], for the overflow case)
    ├── ostore_sync_summary_if_eb_new_ret  (second callee: summary)
    ├── ostore_write_buf_ret       (third callee: write_buf)
    │     ├─ extra_padding_is_aligned      (discharges the nb_bytes_ok side condition)
    │     └─ α_updates_buf_prepare_eq      (post-state of the buffer prepare step)
    └── ostore_sync_α_ostore_uptodate      (post-state: α_ostore_medium = α_ostore_uptodate)
```

`prepare_wbuf_ret` is cited at line 2409, `ostore_sync_summary_if_eb_new_ret`
at 2417, `ostore_write_buf_ret` at 2421, `extra_padding_is_aligned` at 2431,
`α_updates_buf_prepare_eq` at 2445 and 2450,
`ostore_sync_α_ostore_uptodate` at 2462 and 2478,
`used_neq_sync_offs_means_updates_not_Nil` at 2415, 2446 and 2451, and
`used_eq_sync_offs_means_no_update` at 2406.

Each child is a leaf because it is a self-contained statement whose proof
closes on its own or from named siblings, never by re-entering the parent:

- `prepare_wbuf_ret` (182 lines) is the heavy child. It states the refinement
  of `prepare_wbuf` once, then proves it by a case split on whether the
  padding fits in the header (`pad_to − used < bilbyFsObjHeaderSize`); both
  cases end by instantiating the `suc`/`err` assumptions, so the parent never
  sees `prepare_wbuf`'s internals.
- `ostore_sync_summary_if_eb_new_ret` (7 lines) closes by one `simp` unfolding
  of `ostore_sync_summary_if_eb_new_def` — the summary callee is a no-op from
  the refinement's point of view.
- `ostore_write_buf_ret` (41 lines) discharges `ostore_write_buf` through
  `wubi_leb_write_ret` and `inv_ostore_updated_ubi_preserved`, then the
  `suc`/`err` pair.
- `extra_padding_is_aligned` (19 lines) proves the `io_size` divides the
  padding beyond `sync_offs`, which the parent needs as `ostore_write_buf_ret`'s
  `nb_bytes_ok` side condition.
- `ostore_sync_α_ostore_uptodate` (86 lines) shows the final abstract store
  equals the up-to-date view, closing the parent's `suc` branch after the
  write-buffer step.
- `α_updates_buf_prepare_eq` (67 lines) shows preparing the buffer leaves
  `α_updates` unchanged, needed by the parent's `err` branches.
- `used_neq_sync_offs_means_updates_not_Nil` and
  `used_eq_sync_offs_means_no_update` (8 and 4 lines) are the two directions of
  the parent's case split, each a one-liner over `α_updates_def`.

The glue also cites shared invariant-destruction and arithmetic lemmas
(`used_le_padding_to`, `inv_ostore_sync_offsD`,
`offs_pl_padding_to_le_eb_size`, `align32_idempotence`,
`inv_ostore_used_no_overflowD`, `buf_slice_n_n`, `inv_bufsD`) and the `notes`
`pad_simps` and `lemmas OstoreState_ext_eq_expand`; these are one-line
unfolders of the invariant definitions or numeric facts, not part of the
per-callee decomposition, so they are not counted as children.

A verified dependency chain three lemmas deep (the `depth` in `shape`):
`ostore_sync_ret` (line 2379) → `prepare_wbuf_ret` (1480) →
`inv_ostore_preserved_padding_obj` (1240, cited at 1619) →
`valid_commit_pad_obj` (876, cited at 1271); `valid_commit_pad_obj` itself
bottoms out in the invariant D-rule `inv_opadD` (OstoreInvS.thy:868) and the
library lemma `length_sObj`, so the chain ends there.

## Why it is good

1. `ostore_sync_ret` is declared in `impl/fs/bilby/proof/refine/OstoreR.thy`
   lines 2379-2487 (check; permalink above).
2. `prepare_wbuf_ret` occurs in the parent site, i.e. the glue cites it
   (check; line 2409 of the parent).
3. `impl/fs/bilby/proof/refine/OstoreR.thy` lines 2379-2487 contain no `sorry`
   — the glue closes without admitting any subgoal (check; the only `oops` in
   the file is the unrelated `ostore_write_ret` at line 2510, outside the
   parent site).
4. The parent site is 109 lines long, matching `shape.glue_lines` (check).
5. The ostore refinement file declares 8 `_ret` lemmas — one per generated
   function of the layer — so the per-callee shape recurses across the file
   rather than appearing once (measurement: `grep -c '^lemma .*_ret:'` at the
   pinned commit returns 8).
6. The sibling `ostore_read_ret` in `OstoreReadR.thy` uses the same per-callee
   move, its proof calling `index_get_addr_ret` then `deserialise_Obj_ret`
   (known-use).

In my opinion the detail worth copying is the `suc`/`err` post-state pair: each
callee's `_ret` lemma describes *all* its possible outcomes as two assumptions,
so the parent can combine callees by `rule` without ever reasoning about their
bodies. The cost is that the post-states are enormous `∃`-packed record
updates, which is why `prepare_wbuf_ret` is 182 lines.

## When to use it, and when not

Use it when the function you are refining is generated from a fixed structure
(Cogent's shallow-embedded code, seL4's `crunch`, a compiler pass), so the
per-callee lemmas mirror the code one-to-one; when the invariant
(`inv_ostore`, `inv_mount_st`, `inv_α_ostore`) is shared across all callees;
and when each callee's effect can be captured by a `suc`/`err` pair of
assumptions rather than by its full implementation. Avoid it when callees
interact through state that is not expressible in their post-state assumptions
(the parent would have to re-prove instead of thread results); when a callee
has no clean characterisation — its `_ret` lemma is left as `oops`, as with
`ostore_write_ret` at line 2510; or when the body is not a fixed call
sequence, so there is no structure to generate the lemmas against.

## Consequences

One `_ret` lemma per callee plus side lemmas, so the obligations are: each
callee's post-state must be characterised by a `suc`/`err` assumption pair,
and the parent must re-establish that pair before every `rule <callee>_ret`;
the case split `sync_offs = used` must be exhaustive (here the two branches
`used_eq_sync_offs_means_no_update` and
`used_neq_sync_offs_means_updates_not_Nil` are complementary by construction,
but the parent still has to apply the right one in each branch); and a callee
whose refinement lemma is `oops` cannot be used by the glue. The failure mode
is that the per-callee post-states are highly specific (`∃`-packed
`ostore_st'` updates), so a change to the generated code's state layout breaks
the whole family at once. In this file the consequence is visible: the sibling
`ostore_write_ret` (line 2489) is left as `oops`, so `ostore_write` is not
part of the assembled sync proof.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: prepare_wbuf_ret@impl/fs/bilby/proof/refine/OstoreR.thy:2409, ostore_sync_summary_if_eb_new_ret@impl/fs/bilby/proof/refine/OstoreR.thy:2417, ostore_write_buf_ret@impl/fs/bilby/proof/refine/OstoreR.thy:2421, extra_padding_is_aligned@impl/fs/bilby/proof/refine/OstoreR.thy:2431, ostore_sync_\<alpha>_ostore_uptodate@impl/fs/bilby/proof/refine/OstoreR.thy:2462, \<alpha>_updates_buf_prepare_eq@impl/fs/bilby/proof/refine/OstoreR.thy:2445, used_neq_sync_offs_means_updates_not_Nil@impl/fs/bilby/proof/refine/OstoreR.thy:2415, used_eq_sync_offs_means_no_update@impl/fs/bilby/proof/refine/OstoreR.thy:2406; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none; oops (listed, not failed): impl/fs/bilby/proof/refine/OstoreR.thy:2510 (oops) | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(ostore_sync_ret, impl/fs/bilby/proof/refine/OstoreR.thy, 2379-2487) -> declared: ostore_sync_ret is declared at impl/fs/bilby/proof/refine/OstoreR.thy:2379 | check_claims.py |
| 2 | verified | cites(parent, prepare_wbuf_ret) -> cites: prepare_wbuf_ret occurs at impl/fs/bilby/proof/refine/OstoreR.thy:2409 | check_claims.py |
| 3 | verified | no_sorry(impl/fs/bilby/proof/refine/OstoreR.thy, 2379-2487) -> no_sorry: none of sorry in impl/fs/bilby/proof/refine/OstoreR.thy:2379-2487 | check_claims.py |
| 4 | verified | lines(parent, 109) -> lines: site parent has 109 lines | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/au-ts/cogent at commit `49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a`, under `GPL-2.0-only`; see the [source note](../../sources/cogent/SOURCE.md) for the licence text and attribution.
