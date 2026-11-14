# Interface lemmas at the AIR-constraint boundary close the whitepaper's main theorem

| | |
|---|---|
| Kind | instance |
| Move | interface-lemma |
| Language | lean |
| Status | draft |
| Source | [formal-proofs](../../sources/formal-proofs/SOURCE.md) at `d0dd8279612a` |
| Licence | `LicenseRef-unknown` |
| Licence recorded | 2026-11-14T15:30:20Z |

## Intent

Prove the whitepaper's main theorem — that trace data satisfying the AIR
`Constraints` yields an agreeing execution — by composing one named interface
lemma per constraint family (memory, range check, range-check builtin,
instruction, step), each crossing the boundary from the `Constraints` record
to the execution semantics (`Option.FnExtends`, `NextState`), so the glue
never unfolds a constraint definition.

## The decomposition

### parent `execution_exists`: [`Verification/Semantics/AirEncoding/Correctness.lean` lines 39-126](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/Correctness.lean#L39-L126) ([local copy](code/Verification/Semantics/AirEncoding/Correctness.lean))

```lean
theorem execution_exists (char_ge : ringChar F ≥ 2 ^ 63) (inp : InputDataAux F)
    (c : Constraints inp) (hp : Hprob c) :
    ∃ mem : F → F,
      Option.FnExtends mem inp.memStar ∧
        (∀ i < inp.rcLen, ∃ (n : ℕ), n < 2 ^ 128 ∧ mem (inp.initialRcAddr + i) = (↑n : F)) ∧
          ∃ exec : Fin (inp.t + 1) → RegisterState F,
            (exec 0).pc = inp.pcI ∧
              (exec 0).ap = inp.apI ∧
                (exec 0).fp = inp.apI ∧
                  (exec (Fin.last inp.t)).pc = inp.pcF ∧
                    (exec (Fin.last inp.t)).ap = inp.apF ∧
                      ∀ i : Fin inp.t, NextState mem (exec i.castSucc) (exec i.succ) := by
  have char_gt : ringChar F > 2 ^ 16 := by
    apply lt_of_lt_of_le _ char_ge
    apply pow_lt_pow_right <;> norm_num
  let m := mem c.mc.mb.a' c.mc.mb.v'
  have mem_extends : Option.FnExtends m inp.memStar :=
    mem_extends c.mc.mb.h_continuity c.mc.mb.h_single_valued c.mc.mb.h_initial c.mc.mb.h_cumulative
      c.mc.mb.h_final c.mc.em.h_embedDom c.mc.em.h_embedVal c.mc.em.h_embedMem_inj hp.hprob₃
      hp.hprob₁ hp.hprob₂ c.mc.h_n_lt
  have mem_pcAddr : ∀ i : Fin inp.t, m (c.pc i.castSucc) = c.inst i :=
    mem_pc c.mc.mb.h_continuity c.mc.mb.h_single_valued c.mc.mb.h_initial c.mc.mb.h_cumulative
      c.mc.mb.h_final c.mc.em.h_embed_pc c.mc.em.h_embedInst c.mc.em.h_embedDom
      c.mc.em.h_embedVal c.mc.em.h_embedMem_inj c.mc.em.h_embedMem_disj_inst hp.hprob₃ hp.hprob₁
      hp.hprob₂ c.mc.h_n_lt
  have mem_dst_addr : ∀ i, m (c.dstAddr i) = c.dst i :=
    mem_dst_addr c.mc.mb.h_continuity c.mc.mb.h_single_valued c.mc.mb.h_initial c.mc.mb.h_cumulative
      c.mc.mb.h_final c.mc.em.h_embedDstAddr c.mc.em.h_embedDst c.mc.em.h_embedDom
      c.mc.em.h_embedVal c.mc.em.h_embedMem_inj c.mc.em.h_embedMem_disj_dst hp.hprob₃ hp.hprob₁
      hp.hprob₂ c.mc.h_n_lt
  have mem_op0Addr : ∀ i, m (c.op0Addr i) = c.op0 i :=
    mem_op0_addr c.mc.mb.h_continuity c.mc.mb.h_single_valued c.mc.mb.h_initial c.mc.mb.h_cumulative
      c.mc.mb.h_final c.mc.em.h_embedOp0Addr c.mc.em.h_embedOp0 c.mc.em.h_embedDom
      c.mc.em.h_embedVal c.mc.em.h_embedMem_inj c.mc.em.h_embedMem_disj_op0 hp.hprob₃ hp.hprob₁
      hp.hprob₂ c.mc.h_n_lt
  have mem_op1Addr : ∀ i, m (c.op1Addr i) = c.op1 i :=
    mem_op1_addr c.mc.mb.h_continuity c.mc.mb.h_single_valued c.mc.mb.h_initial c.mc.mb.h_cumulative
      c.mc.mb.h_final c.mc.em.h_embedOp1Addr c.mc.em.h_embedOp1 c.mc.em.h_embedDom
      c.mc.em.h_embedVal c.mc.em.h_embedMem_inj c.mc.em.h_embedMem_disj_op1 hp.hprob₃ hp.hprob₁
      hp.hprob₂ c.mc.h_n_lt
  have mem_rcAddr : ∀ i, m (c.rcAddr i) = c.rcVal i :=
    mem_rc_addr c.mc.mb.h_continuity c.mc.mb.h_single_valued c.mc.mb.h_initial c.mc.mb.h_cumulative
      c.mc.mb.h_final c.mc.em.h_embedRcAddr c.mc.em.h_embedRc c.mc.em.h_embedDom
      c.mc.em.h_embedVal c.mc.em.h_embedMem_inj c.mc.em.h_embedMem_disj_rc hp.hprob₃ hp.hprob₁
      hp.hprob₂ c.mc.h_n_lt
  have off_op0_in_range : ∀ i, ∃ k : ℕ, k < 2 ^ 16 ∧ c.offOp0Tilde i = ↑k :=
    off_op0_in_range c.rc.h_continuity c.rc.h_initial c.rc.h_cumulative c.rc.h_final c.rc.h_rc_min
      c.rc.h_rcMax c.rc.h_embedOp0 c.rc.h_n_lt inp.h_rc_lt inp.h_rc_le char_gt hp.hprob₄
  have off_op1_in_range : ∀ i, ∃ k : ℕ, k < 2 ^ 16 ∧ c.offOp1Tilde i = ↑k :=
    off_op1_in_range c.rc.h_continuity c.rc.h_initial c.rc.h_cumulative c.rc.h_final c.rc.h_rc_min
      c.rc.h_rcMax c.rc.h_embedOp1 c.rc.h_n_lt inp.h_rc_lt inp.h_rc_le char_gt hp.hprob₄
  have off_dst_in_range : ∀ i, ∃ k : ℕ, k < 2 ^ 16 ∧ c.offDstTilde i = ↑k :=
    off_dst_in_range c.rc.h_continuity c.rc.h_initial c.rc.h_cumulative c.rc.h_final c.rc.h_rc_min
      c.rc.h_rcMax c.rc.h_embedDst c.rc.h_n_lt inp.h_rc_lt inp.h_rc_le char_gt hp.hprob₄
  have rc16Vals_in_range : ∀ i, ∃ k : ℕ, k < 2 ^ 16 ∧ c.rc16Val i = ↑k :=
    rc16_vals_in_range c.rc.h_continuity c.rc.h_initial c.rc.h_cumulative c.rc.h_final c.rc.h_rc_min
      c.rc.h_rcMax c.rc.h_embedRc16 c.rc.h_n_lt inp.h_rc_lt inp.h_rc_le char_gt hp.hprob₄
  have range_checked : ∀ i < inp.rcLen, ∃ n : ℕ,n < 2 ^ 128 ∧ m (inp.initialRcAddr + i) = ↑n := by
    intro i hi
    rcases rc_val_checked rc16Vals_in_range c.rcb.h_rcValue ⟨i, hi⟩ with ⟨n, nlt, neq⟩
    use n, nlt
    rw [← neq, ←mem_rcAddr]
    rw [rc_addr_eq c.rcb.h_rc_init_addr c.rcb.h_rcAddr_step ⟨i, hi⟩]
  use m, mem_extends, range_checked
  let e := fun i : Fin (inp.t + 1) => RegisterState.mk (c.pc i) (c.ap i) (c.fp i)
  use e, c.h_pcI, c.h_apI, c.h_fpI, c.h_pcF, c.h_apF
  intro i
  show NextState m (e i.castSucc) (e i.succ)
  let inst' :=
    theInstruction (c.ic i).h_bit (off_op0_in_range i) (off_op1_in_range i) (off_dst_in_range i)
  have inst_eq : c.inst i = ↑inst'.toNat :=
    inst_eq (c.ic i).h_instruction (c.ic i).h_bit (c.ic i).h_last_value (off_op0_in_range i)
      (off_op1_in_range i) (off_dst_in_range i)
  have offDstTilde_eq : c.offDstTilde i = ↑inst'.offDst.toNat :=
    offDst_tilde_eq (c.ic i).h_bit (off_op0_in_range i) (off_op1_in_range i) (off_dst_in_range i)
  have offOp0Tilde_eq : c.offOp0Tilde i = ↑inst'.offOp0.toNat :=
    offOp0_tilde_eq (c.ic i).h_bit (off_op0_in_range i) (off_op1_in_range i) (off_dst_in_range i)
  have offOp1Tilde_eq : c.offOp1Tilde i = ↑inst'.offOp1.toNat :=
    offOp1_tilde_eq (c.ic i).h_bit (off_op0_in_range i) (off_op1_in_range i) (off_dst_in_range i)
  have f_tilde_to_f_eq : ∀ j, (c.fTilde i).toF j = ↑(Bool.toNat (BitVec.getLsbD inst'.flags j)) :=
    f_tilde_toF_eq (c.ic i).h_bit (off_op0_in_range i) (off_op1_in_range i) (off_dst_in_range i)
  exact
    nextState_eq offDstTilde_eq offOp0Tilde_eq offOp1Tilde_eq f_tilde_to_f_eq
      ((mem_pcAddr i).trans inst_eq) (mem_dst_addr i) (mem_op0Addr i) (mem_op1Addr i)
      (c.sc i).h_dstAddr (c.sc i).h_op0Addr (c.sc i).h_op1Addr (c.sc i).h_mul (c.sc i).h_res
      (c.sc i).h_t0_eq (c.sc i).h_t1_eq (c.sc i).h_nextPc_eq (c.sc i).h_nextPc_eq'
      (c.sc i).h_opcode_call (c.sc i).h_opcode_call' (c.sc i).h_opcode_assert_eq (c.sc i).h_nextAp
      (c.sc i).h_nextFp
```

### child `mem_extends`: [`Verification/Semantics/AirEncoding/Memory.lean` lines 273-290](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/Memory.lean#L273-L290) ([local copy](code/Verification/Semantics/AirEncoding/Memory.lean))

```lean
theorem mem_extends : Option.FnExtends (mem a' v') mem_star := by
  intro addr
  cases' h : mem_star addr with val <;> simp only [Option.Agrees]
  have h' : (Option.isSome (mem_star addr) : Prop) := by rw [h]; simp
  let aelt : MemDom mem_star := ⟨addr, h'⟩
  have h₀ : ∃ i, embed_mem i = embed_mem aelt := ⟨aelt, rfl⟩
  have h₁ : Classical.choose h₀ = aelt := by apply h_embed_mem_inj; apply Classical.choose_spec h₀
  have h₂ : realA mem_star a embed_mem (embed_mem aelt) = addr := by
    rw [realA, dif_pos h₀, h₁]
  have h₃ : realV mem_star v embed_mem (embed_mem aelt) = val := by
    rw [realV, dif_pos h₀, h₁]
    apply Option.some_inj.mp
    rw [← h, memVal, Option.some_get]
  rw [← h₂, ← h₃]; symm
  dsimp
  exact
    mem_unique h_continuity h_single_valued h_initial h_cumulative h_final h_embed_dom h_embed_val
      h_embed_mem_inj h_z_ne_zero hprob₁ hprob₂ h_char_lt (embed_mem ⟨addr, h'⟩)
```

### child `mem_pc`: [`Verification/Semantics/AirEncoding/Memory.lean` lines 244-248](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/Memory.lean#L244-L248) ([local copy](code/Verification/Semantics/AirEncoding/Memory.lean))

```lean
theorem mem_pc (i : Fin T) : mem a' v' (pc i) = inst i := by
  rw [← @realA_embed_inst _ T pc mem_star _ a embed_inst embed_mem _ h_embed_pc h_embed_mem_disj_inst]
  rw [← @realV_embed_inst _ T inst mem_star _ v embed_inst embed_mem _ h_embed_inst h_embed_mem_disj_inst]
  apply mem_unique h_continuity h_single_valued h_initial h_cumulative h_final h_embed_dom h_embed_val
      h_embed_mem_inj h_z_ne_zero hprob₁ hprob₂ h_char_lt
```

### child `mem_dst_addr`: [`Verification/Semantics/AirEncoding/Memory.lean` lines 251-253](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/Memory.lean#L251-L253) ([local copy](code/Verification/Semantics/AirEncoding/Memory.lean))

```lean
theorem mem_dst_addr (i : Fin T) : mem a' v' (dst_addr i) = dst i :=
  mem_pc h_continuity h_single_valued h_initial h_cumulative h_final h_embed_dst_addr h_embed_dst
    h_embed_dom h_embed_val h_embed_mem_inj h_embed_mem_disj_dst h_z_ne_zero hprob₁ hprob₂ h_char_lt i
```

### child `off_op0_in_range`: [`Verification/Semantics/AirEncoding/RangeCheck.lean` lines 108-116](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/RangeCheck.lean#L108-L116) ([local copy](code/Verification/Semantics/AirEncoding/RangeCheck.lean))

```lean
theorem off_op0_in_range (i : Fin T) : ∃ k : ℕ, k < 2 ^ 16 ∧ off_op0_tilde i = ↑k := by
  rcases rc_permutation h_initial h_cumulative h_final hprob₃ (embed_off_op0 i) with ⟨j, hj⟩
  have : a' j = a' 0 + a'NatOffset a' j := a'NatOffset_spec h_continuity _
  rw [this, h_embed_op0, h_rc_min, ← Nat.cast_add] at hj
  use rc_min + a'NatOffset a' j
  constructor
  · apply lt_of_le_of_lt _ h_rc_lt
    apply rc_nat_offset_le h_continuity h_rc_min h_rc_max h_n_lt h_rc_lt h_rc_le h_ring_char_gt
  exact hj
```

### child `rc16_vals_in_range`: [`Verification/Semantics/AirEncoding/RangeCheck.lean` lines 129-131](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/RangeCheck.lean#L129-L131) ([local copy](code/Verification/Semantics/AirEncoding/RangeCheck.lean))

```lean
theorem rc16_vals_in_range (i : Fin T) : ∃ k : ℕ, k < 2 ^ 16 ∧ rc16_vals i = ↑k :=
  off_op0_in_range h_continuity h_initial h_cumulative h_final h_rc_min h_rc_max h_embed_rc h_n_lt
    h_rc_lt h_rc_le h_ring_char_gt hprob₃ i
```

### child `rc_val_checked`: [`Verification/Semantics/AirEncoding/RangeCheckBuiltin.lean` lines 54-92](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/RangeCheckBuiltin.lean#L54-L92) ([local copy](code/Verification/Semantics/AirEncoding/RangeCheckBuiltin.lean))

```lean
theorem rc_val_checked (i : Fin rc_len) : ∃ k : ℕ, k < 2 ^ 128 ∧ rc_val i = ↑k := by
  have rc_val_aux : ∀ {n : ℕ} (_ : n < 2 ^ 16), n ≤ 2 ^ 16 - 1 := by
    intro n h
    apply Nat.le_of_succ_le_succ
    apply le_trans (Nat.succ_le_of_lt h)
    norm_num
  rw [h_rc_value]; rcases h_rc16_val (rc_to_rc16 i 0) with ⟨k0, k0_lt, k0eq⟩
  rw [k0eq]; rcases h_rc16_val (rc_to_rc16 i 1) with ⟨k1, k1_lt, k1eq⟩
  rw [k1eq]; rcases h_rc16_val (rc_to_rc16 i 2) with ⟨k2, k2_lt, k2eq⟩
  rw [k2eq]; rcases h_rc16_val (rc_to_rc16 i 3) with ⟨k3, k3_lt, k3eq⟩
  rw [k3eq]; rcases h_rc16_val (rc_to_rc16 i 4) with ⟨k4, k4_lt, k4eq⟩
  rw [k4eq]; rcases h_rc16_val (rc_to_rc16 i 5) with ⟨k5, k5_lt, k5eq⟩
  rw [k5eq]; rcases h_rc16_val (rc_to_rc16 i 6) with ⟨k6, k6_lt, k6eq⟩
  rw [k6eq]; rcases h_rc16_val (rc_to_rc16 i 7) with ⟨k7, k7_lt, k7eq⟩
  rw [k7eq]
  use ((((((k0 * 2 ^ 16 + k1) * 2 ^ 16 + k2) * 2 ^ 16 + k3) * 2 ^ 16 + k4) * 2 ^ 16 +
    k5) * 2 ^ 16 + k6) * 2 ^ 16 + k7
  constructor; swap; norm_num
  have :
    (((((((2 ^ 16 - 1) * 2 ^ 16 + (2 ^ 16 - 1)) * 2 ^ 16 + (2 ^ 16 - 1)) * 2 ^ 16 + (2 ^ 16 - 1)) *
      2 ^ 16 + (2 ^ 16 - 1)) * 2 ^ 16 + (2 ^ 16 - 1)) * 2 ^ 16 + (2 ^ 16 - 1)) *
        2 ^ 16 + (2 ^ 16 - 1) < 2 ^ 128 :=
    by norm_num
  apply lt_of_le_of_lt _ this
  apply add_le_add _ (rc_val_aux k7_lt)
  apply Nat.mul_le_mul_right
  apply add_le_add _ (rc_val_aux k6_lt)
  apply Nat.mul_le_mul_right
  apply add_le_add _ (rc_val_aux k5_lt)
  apply Nat.mul_le_mul_right
  apply add_le_add _ (rc_val_aux k4_lt)
  apply Nat.mul_le_mul_right
  apply add_le_add _ (rc_val_aux k3_lt)
  apply Nat.mul_le_mul_right
  apply add_le_add _ (rc_val_aux k2_lt)
  apply Nat.mul_le_mul_right
  apply add_le_add _ (rc_val_aux k1_lt)
  apply Nat.mul_le_mul_right
  apply rc_val_aux k0_lt
```

### child `inst_eq`: [`Verification/Semantics/AirEncoding/Instruction.lean` lines 272-282](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/Instruction.lean#L272-L282) ([local copy](code/Verification/Semantics/AirEncoding/Instruction.lean))

```lean
theorem inst_eq :
  inst = (theInstruction h_bit offOp0_in_range offOp1_in_range offDst_in_range).toNat := by
  rw [h_instruction, Instruction.toNat, theInstruction_flags_eq, theInstruction]
  simp only [Fin.isValue, BitVec.toNat_ofNat, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  have := f_tilde_eq h_bit h_last_value 0
  rw [Nat.mod_eq_of_lt (offOp0_lt offOp0_in_range),
    Nat.mod_eq_of_lt (offOp1_lt offOp1_in_range), Nat.mod_eq_of_lt (offDst_lt offDst_in_range),
    ← offOp0_eq offOp0_in_range, ← offOp1_eq offOp1_in_range, ← offDst_eq offDst_in_range,
    this, BitVec.tilde_zero_eq]
  norm_num
```

### child `nextState_eq`: [`Verification/Semantics/AirEncoding/Step.lean` lines 295-305](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/Step.lean#L295-L305) ([local copy](code/Verification/Semantics/AirEncoding/Step.lean))

```lean
theorem nextState_eq : NextState mem ⟨pc, ap, fp⟩ ⟨next_pc, next_ap, next_fp⟩ :=
   ⟨inst, h_mem_pc,
    nextPc_agrees h_off_dst_tilde h_off_op0_tilde h_off_op1_tilde h_flags
      h_mem_dst_addr h_mem_op0_addr h_mem_op1_addr h_dst_addr h_op0_addr h_op1_addr
      h_mul h_res h_t0_eq h_t1_eq h_next_pc_eq h_next_pc_eq',
    nextAp_agrees h_off_op0_tilde h_off_op1_tilde h_flags h_mem_op0_addr h_mem_op1_addr h_op0_addr
      h_op1_addr h_mul h_res h_next_ap,
    nextFp_agrees h_off_dst_tilde h_flags h_mem_dst_addr h_dst_addr h_next_fp,
    asserts_hold h_off_dst_tilde h_off_op0_tilde h_off_op1_tilde h_flags h_mem_dst_addr
      h_mem_op0_addr h_mem_op1_addr h_dst_addr h_op0_addr h_op1_addr h_mul h_res h_opcode_call
      h_opcode_call' h_opcode_assert_eq⟩
```

How the parts fit. The glue `execution_exists` is a straight-line assembly:
it names the memory `m := mem c.mc.mb.a' c.mc.mb.v'`, then writes one `have`
per conjunct of the goal, each discharged by one bridge lemma whose arguments
are the fields of a single constraint family (`c.mc`, `c.rc`, `c.rcb`,
`c.ic`, `c.sc`). No constraint definition is unfolded anywhere in the proof.
The witness is closed by `use m, mem_extends, range_checked`, a second `use`
for the execution `e`, and one `exact nextState_eq …`.

Lemma graph, in text (which lemma uses which):

```
execution_exists (glue)
├─ mem_extends        → closes Option.FnExtends m inp.memStar
│    └─ mem_unique ── real_perm ── real_permutation_prod_eq   (Memory.lean)
├─ mem_pc             → closes m (c.pc i) = c.inst i
│    └─ mem_unique   (mem_dst_addr, mem_op0_addr, mem_op1_addr, mem_rc_addr := mem_pc)
├─ off_op0_in_range   → closes each offset is < 2^16
│    └─ rc_permutation (off_op1_in_range, off_dst_in_range, rc16_vals_in_range := off_op0_in_range)
├─ rc_val_checked     → closes range_checked, with rc_addr_eq and rc16_vals_in_range
├─ inst_eq            → closes c.inst i = ↑inst'.toNat, with the four *_tilde_eq lemmas
└─ nextState_eq       → closes NextState in one application
     └─ nextPc_agrees, nextAp_agrees, nextFp_agrees, asserts_hold
```

Why each shown child is a good leaf:

- `mem_extends` (18 lines): self-contained statement `Option.FnExtends (mem a'
  v') mem_star`; its proof closes from the project's `mem_unique` plus a
  `cases'` on the input option, naming no sibling.
- `mem_pc` (5 lines): reduces the pc-address agreement to `mem_unique` through
  two `rw`s of `realA_embed_inst`/`realV_embed_inst`; it is the single
  implementation the other four address lemmas reuse.
- `mem_dst_addr` (3 lines): a term-mode proof `:= mem_pc …`, so it closes from
  its sibling at once.
- `off_op0_in_range` (9 lines): the offset range fact; its proof closes from
  `rc_permutation` and a small `constructor`, and it is the single
  implementation the op1/dst/rc16 lemmas reuse.
- `rc16_vals_in_range` (3 lines): `:= off_op0_in_range …`, closed from its
  sibling.
- `rc_val_checked` (39 lines): the longest leaf, self-contained — it packs
  eight 16-bit witnesses into one 128-bit witness and closes the bound by
  `norm_num`, depending only on `h_rc_value` and `h_rc16_val`.
- `inst_eq` (11 lines): self-contained — it reconstructs the instruction's
  `toNat` from `h_instruction` plus the `theInstruction`/flag rewrites,
  closing by `norm_num`.
- `nextState_eq` (11 lines): the step bridge; it closes `NextState` as a
  single application with four per-component lemmas (`nextPc_agrees`,
  `nextAp_agrees`, `nextFp_agrees`, `asserts_hold`) that the glue never names
  directly.

The remaining ten direct lemmas, listed rather than shown:

- `mem_op0_addr`, `mem_op1_addr`, `mem_rc_addr` — [Memory.lean lines
  256-258](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/Memory.lean#L256-L258),
  [261-263](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/Memory.lean#L261-L263),
  [266-271](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/Memory.lean#L266-L271);
  the other three address families, each `:= mem_pc`.
- `off_op1_in_range`, `off_dst_in_range` — [RangeCheck.lean lines
  119-121](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/RangeCheck.lean#L119-L121),
  [124-126](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/RangeCheck.lean#L124-L126);
  the other two offsets, each `:= off_op0_in_range`.
- `rc_addr_eq` — [RangeCheckBuiltin.lean lines
  46-51](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/RangeCheckBuiltin.lean#L46-L51);
  closes the rc-address rewrite inside `range_checked`.
- `offDst_tilde_eq`, `offOp0_tilde_eq`, `offOp1_tilde_eq`, `f_tilde_toF_eq` —
  [Instruction.lean lines
  284-289](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/Instruction.lean#L284-L289),
  [291-296](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/Instruction.lean#L291-L296),
  [298-303](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/Instruction.lean#L298-L303),
  [305-309](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/Instruction.lean#L305-L309);
  the instruction offset/flag reconstruction facts that feed `nextState_eq`.

## Why it is good

1. The child `nextState_eq` is declared in
   `Verification/Semantics/AirEncoding/Step.lean` at lines 295-305
   ([permalink](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/Step.lean#L295-L305));
   `check`, form `declared(nextState_eq, Verification/Semantics/AirEncoding/Step.lean, 295-305)`.
2. The parent site cites the child `mem_extends`
   ([permalink](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/Correctness.lean#L39-L126));
   `check`, form `cites(parent, mem_extends)`.
3. No closing-by-`sorry` token occurs in
   `Verification/Semantics/AirEncoding/Correctness.lean` lines 39-126
   ([permalink](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/Correctness.lean#L39-L126));
   `check`, form `no_sorry(Verification/Semantics/AirEncoding/Correctness.lean, 39-126)`.
4. The file header states the goal is the whitepaper's main theorem: "A proof
   of the main theorem of the whitepaper" ([lines
   1-7](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/Correctness.lean#L1-L7));
   `author-statement`.
5. The glue applies 18 named project lemmas directly
   (`shape.direct_lemmas = 18`), counted by reading Correctness.lean lines
   51-126
   ([permalink](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Verification/Semantics/AirEncoding/Correctness.lean#L51-L126));
   `measurement`.

In my opinion the detail worth copying is the *boundary discipline*: every
`have` in the glue is a single bridge lemma crossing from one constraint
record to one semantic fact, and the only place the glue itself reasons is the
`range_checked` sub-proof, which still uses only `rc_val_checked` and
`rc_addr_eq`. The author chose the boundary so that "does this constraint
family hold" and "what execution does it produce" stay in separate files.

## When to use it, and when not

Use it when each constraint family's hypotheses are bundled in one structure
(or locale/section variables) whose fields are exactly the premises of one
bridge lemma per family; the proof is then a straight-line assembly of
`have := bridge_lemma …` calls, supplying the structure fields as arguments,
and a final `use`/`exact` of the assembled facts. The goal shape is
`Constraints c → ∃ witness, P₀ witness ∧ P₁ witness ∧ … ∧ Pₖ witness` where
each conjunct is a separate obligation and each is already a named lemma in
the project.

Avoid it when a family must be partially unfolded to state the fact (the
bridge lemma is not a clean consequence of one structure), when the client
needs the constraint internals rather than the abstract fact, or when there
is no shared boundary the children can cross independently, so the glue still
has to reason inside the definitions.

## Consequences

The glue becomes a straight-line list of `have`s, but each bridge lemma takes
a long argument list of the family's constraint fields (10-16 premises here),
so a missing field surfaces as an elaboration error at the call site rather
than a proof error. The boundary lemmas must be stated at the right level: too
coarse and a conjunct cannot be discharged, too fine and the glue still
unfolds. Correctness now rests on each bridge lemma being true of its whole
family, so a family split across several lemmas — the instruction family here
needs `inst_eq` plus the four `tilde_eq` lemmas before `nextState_eq` — still
has to be re-assembled in the glue.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: mem_extends@Verification/Semantics/AirEncoding/Correctness.lean:55, mem_pc@Verification/Semantics/AirEncoding/Correctness.lean:60, mem_dst_addr@Verification/Semantics/AirEncoding/Correctness.lean:64, off_op0_in_range@Verification/Semantics/AirEncoding/Correctness.lean:84, rc16_vals_in_range@Verification/Semantics/AirEncoding/Correctness.lean:94, rc_val_checked@Verification/Semantics/AirEncoding/Correctness.lean:98, inst_eq@Verification/Semantics/AirEncoding/Correctness.lean:109, nextState_eq@Verification/Semantics/AirEncoding/Correctness.lean:121; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(nextState_eq, Verification/Semantics/AirEncoding/Step.lean, 295-305) -> declared: nextState_eq is declared at Verification/Semantics/AirEncoding/Step.lean:295 | check_claims.py |
| 2 | verified | cites(parent, mem_extends) -> cites: mem_extends occurs at Verification/Semantics/AirEncoding/Correctness.lean:55 | check_claims.py |
| 3 | verified | no_sorry(Verification/Semantics/AirEncoding/Correctness.lean, 39-126) -> no_sorry: none of sorry, admit, axiom in Verification/Semantics/AirEncoding/Correctness.lean:39-126 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/starkware-libs/formal-proofs at commit `d0dd8279612a248cbc6bf6d286030bf0bb2a37ff`, under `LicenseRef-unknown`; see the [source note](../../sources/formal-proofs/SOURCE.md) for the licence text and attribution.
