# One soundness lemma per Opcode constructor, glued by a bare cases-dispatch

| | |
|---|---|
| Kind | instance |
| Move | per-callee-lemma |
| Language | lean |
| Status | draft |
| Source | [formal-proofs](../../sources/formal-proofs/SOURCE.md) at `d0dd8279612a` |
| Licence | `LicenseRef-unknown` |
| Licence recorded | 2026-11-14T12:55:50Z |

## Intent

`exec_step_sound` proves one step of a Cairo VM opcode is sound: given the
opcode's constraints and lookup terms are satisfied, the output state is
`strongly_bounded` and related to the input by `NextState`. It is proved by
splitting on the `Opcode` inductive and applying one pre-written lemma per
constructor, so the decomposition is read straight off the `Opcode` type.

## The decomposition

### parent `exec_step_sound`: [`Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean` lines 317-403](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean#L317-L403) ([local copy](code/Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean))

```lean
lemma exec_step_sound [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : ℕ}
      {o : Opcode}
      {v : VarAssign}
      -- memory
      {memAssign : Felt252IdMemoryAssign}
      {mem : Felt252 → Felt252}
      (h_mem_agrees : memAssign.Agrees mem)
      -- Lookups
      {h_satisfied : LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels}
      -- opcode constraints
      (h_opcode_satisfied : (OpcodeAirFns o).1.SatisfiedBy v)
      -- Terms agree
      (h_lookup_terms_agree : (OpcodeAirFns o).2.1.UseAgree v h_satisfied.values h_satisfied.partitions h_satisfied.tuples)
      -- other relations
      (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
      (h_mem : AirLookupTerms.MemYieldsAgreeAndRangeChecked memAssign h_satisfied.values
          (h_satisfied.tuples RANGE_CHECK_REL_INDEX)
          (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX)
          (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
      (h_verify_instr : AirLookupTerms.VerifyInstrYieldAgrees h_satisfied.tuples)
      (num_steps : Nat)
      (h_num_steps : num_steps < 2 ^ 29) :
      (OpcodeInStateVal (o, v)).strongly_bounded₀ num_steps →
        (OpcodeOutStateVal (o, v)).strongly_bounded (num_steps + 1)
          ∧ NextState mem (OpcodeInStateVal (o, v)).toRegisterStateFelt252 (OpcodeOutStateVal (o, v)).toRegisterStateFelt252 := by
  have h_agree1 := AirLookupTerms.UseAgree_add.mp h_lookup_terms_agree
  rcases AirLookupTerms.UseAgree_add.mp h_agree1.2 with ⟨_, h_agree⟩
  simp [OpcodeAirFns, OpcodeLookupCall, OpcodeCall] at h_opcode_satisfied
  revert h_opcode_satisfied h_agree
  cases o
  case Generic =>
    intro h_sat h_agree h_bound
    apply GenericOpcode.sound_generic v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case CallRel =>
    intro h_sat h_agree h_bound
    apply CallOpcode.sound_call_rel v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case CallAbsBaseFP =>
    intro h_sat h_agree h_bound
    apply CallOpcode.sound_call_abs_base_fp v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case CallAbsBaseAP =>
    intro h_sat h_agree h_bound
    apply CallOpcode.sound_call_abs_base_ap v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case Ret =>
    intro h_sat h_agree h_bound
    apply RetOpcode.sound_ret v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case AssertEq =>
    intro h_sat h_agree h_bound
    apply AssertEqOpcode.sound_assert_eq v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case AssertEqImm =>
    intro h_sat h_agree h_bound
    apply AssertEqOpcode.sound_assert_eq_imm v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case AssertEqDoubleDeref =>
    intro h_sat h_agree h_bound
    apply AssertEqOpcode.sound_assert_eq_double_deref v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case JumpImm =>
    intro h_sat h_agree h_bound
    apply JumpOpcode.sound_jump_imm v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case JumpDoubleDeref =>
    intro h_sat h_agree h_bound
    apply JumpOpcode.sound_jump_double_deref v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case JumpRel =>
    intro h_sat h_agree h_bound
    apply JumpOpcode.sound_jump_rel v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case JumpAbs =>
    intro h_sat h_agree h_bound
    apply JumpOpcode.sound_jump_abs v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case JnzNotTaken =>
    intro h_sat h_agree h_bound
    apply JnzOpcode.JnzNotTakenOpcode.sound_jnz_not_taken v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case JnzTaken =>
    intro h_sat h_agree h_bound
    apply JnzOpcode.JnzTakenOpcode.sound_jnz_taken v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case AddAp =>
    intro h_sat h_agree h_bound
    apply AddApOpcode.sound_add_ap v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case AddSmall =>
    intro h_sat h_agree h_bound
    apply AddOpcode.AddSmallOpcode.sound_add_small v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case Add252 =>
    intro h_sat h_agree h_bound
    apply AddOpcode.Add252Opcode.sound_add_252 v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case MulSmall =>
    intro h_sat h_agree h_bound
    apply MulOpcode.MulSmallOpcode.sound_mul_small v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
  case Mul252 =>
    intro h_sat h_agree h_bound
    apply MulOpcode.Mul252Opcode.sound_mul_252 v h_mem_agrees _ _ h_rc h_mem h_verify_instr h_num_steps h_bound h_sat h_agree
```

### context `Opcode`: [`Stwo/Verification/AirInfra/Soundness/Components.lean` lines 9-29](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Soundness/Components.lean#L9-L29) ([local copy](code/Stwo/Verification/AirInfra/Soundness/Components.lean))

```lean
inductive Opcode where
  | Generic : Opcode
  | CallRel : Opcode
  | CallAbsBaseFP : Opcode
  | CallAbsBaseAP : Opcode
  | Ret : Opcode
  | AssertEq : Opcode
  | AssertEqImm : Opcode
  | AssertEqDoubleDeref : Opcode
  | JumpImm : Opcode
  | JumpDoubleDeref : Opcode
  | JumpRel : Opcode
  | JumpAbs : Opcode
  | JnzNotTaken : Opcode
  | JnzTaken : Opcode
  | AddAp : Opcode
  | AddSmall : Opcode
  | Add252 : Opcode
  | MulSmall : Opcode
  | Mul252 : Opcode
  deriving Fintype, DecidableEq
```

### child `sound_generic`: [`Stwo/Verification/AirInfra/Airs/Casm/Opcodes/GenericOpcode/GenericOpcode.lean` lines 735-765](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/GenericOpcode/GenericOpcode.lean#L735-L765) ([local copy](code/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/GenericOpcode/GenericOpcode.lean))

```lean
theorem sound_generic [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
      (varAssign : VarAssign)
      {memAssign : Felt252IdMemoryAssign}
      {mem : Felt252 → Felt252}
      (h_mem_agrees : memAssign.Agrees mem)
      (ab : AirBuilder)
      (lt : AirLookupTerms)
      {h_satisfied : LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels}
      (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
      (h_mem : AirLookupTerms.MemYieldsAgreeAndRangeChecked memAssign h_satisfied.values
            (h_satisfied.tuples RANGE_CHECK_REL_INDEX)
            (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX)
            (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
      (h_verify_instr : AirLookupTerms.VerifyInstrYieldAgrees h_satisfied.tuples)
      {casmState : CasmState}
      {num_steps: Nat} :
    let ⟨new_ab, new_lt, ρCasmState⟩ := call ab lt casmState
    num_steps < 2^29 →
    (casmState.eval varAssign).strongly_bounded₀ num_steps →
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      (ρCasmState.eval varAssign).strongly_bounded (num_steps+1) ∧
      NextState mem (casmState.eval varAssign).toRegisterStateFelt252 (ρCasmState.eval varAssign).toRegisterStateFelt252 := by
  intro h_num_steps h_bound h_sat h_agree
  rcases sound_auto varAssign memAssign ab lt h_satisfied h_rc h_mem h_verify_instr _ num_steps h_sat h_agree
    with ⟨_, _, h_spec⟩
  rcases h_spec h_num_steps h_bound with ⟨h_bound, h_step⟩
  use h_bound
  rcases h_step mem h_mem_agrees with ⟨instr, h_instr, h_next⟩
  use instr
  use h_instr
```

### child `sound_call_rel`: [`Stwo/Verification/AirInfra/Airs/Casm/Opcodes/CallOpcode.lean` lines 398-431](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/CallOpcode.lean#L398-L431) ([local copy](code/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/CallOpcode.lean))

```lean
theorem sound_call_rel [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
      (varAssign : VarAssign)
      {memAssign : Felt252IdMemoryAssign}
      {mem : Felt252 → Felt252}
      (h_mem_agrees : memAssign.Agrees mem)
      (ab : AirBuilder)
      (lt : AirLookupTerms)
      {h_satisfied : LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels}
      (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
      (h_mem : AirLookupTerms.MemYieldsAgreeAndRangeChecked memAssign h_satisfied.values
            (h_satisfied.tuples RANGE_CHECK_REL_INDEX)
            (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX)
            (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
      (h_verify_instr : AirLookupTerms.VerifyInstrYieldAgrees h_satisfied.tuples)
      {casmState : CasmState}
      {num_steps: Nat} :
    let ⟨new_ab, new_lt, ρCasmState⟩ := call true false ab lt casmState
    num_steps < 2^29 →
    (casmState.eval varAssign).strongly_bounded₀ num_steps →
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      (ρCasmState.eval varAssign).strongly_bounded (num_steps+1) ∧
      NextState mem (casmState.eval varAssign).toRegisterStateFelt252 (ρCasmState.eval varAssign).toRegisterStateFelt252 := by
  intro h_num_steps h_bound h_sat h_agree
  rcases CallOpcode.sound_auto varAssign memAssign ab lt
      h_satisfied h_rc h_mem h_verify_instr _ true false
      num_steps h_sat h_agree
    with ⟨_, _, h_spec⟩
  have h_flags : CallOpcode.flag_assert true false := by simp [CallOpcode.flag_assert]
  rcases h_spec h_flags h_num_steps h_bound with ⟨h_bound, h_step⟩
  use h_bound
  rcases h_step mem h_mem_agrees with ⟨offset2, h_instr, h_next⟩
  use (CallOpcode.call_instr true false offset2).toInstruction
  use h_instr
```

### child `sound_ret`: [`Stwo/Verification/AirInfra/Airs/Casm/Opcodes/RetOpcode.lean` lines 195-225](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/RetOpcode.lean#L195-L225) ([local copy](code/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/RetOpcode.lean))

```lean
theorem sound_ret [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
      (varAssign : VarAssign)
      {memAssign : Felt252IdMemoryAssign}
      {mem : Felt252 → Felt252}
      (h_mem_agrees : memAssign.Agrees mem)
      (ab : AirBuilder)
      (lt : AirLookupTerms)
      {h_satisfied : LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels}
      (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
      (h_mem : AirLookupTerms.MemYieldsAgreeAndRangeChecked memAssign h_satisfied.values
            (h_satisfied.tuples RANGE_CHECK_REL_INDEX)
            (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX)
            (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
      (h_verify_instr : AirLookupTerms.VerifyInstrYieldAgrees h_satisfied.tuples)
      {casmState : CasmState}
      {num_steps: Nat} :
    let ⟨new_ab, new_lt, ρCasmState⟩ := call ab lt casmState
    num_steps < 2^29 →
    (casmState.eval varAssign).strongly_bounded₀ num_steps →
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      (ρCasmState.eval varAssign).strongly_bounded (num_steps+1) ∧
      NextState mem (casmState.eval varAssign).toRegisterStateFelt252 (ρCasmState.eval varAssign).toRegisterStateFelt252 := by
  intro h_num_steps h_bound h_sat h_agree
  rcases sound_auto varAssign memAssign ab lt h_satisfied h_rc h_mem h_verify_instr _ num_steps h_sat h_agree
    with ⟨_, _, h_spec⟩
  rcases h_spec h_num_steps (CasmStateVal.strongly_bounded_of_strongly_bounded₀ h_bound) with ⟨h_bound, h_step⟩
  use h_bound
  rcases h_step mem h_mem_agrees with ⟨h_instr, h_next⟩
  use retInstr.toInstruction
  use h_instr
```

### child `sound_assert_eq`: [`Stwo/Verification/AirInfra/Airs/Casm/Opcodes/AssertEqOpcode.lean` lines 471-505](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/AssertEqOpcode.lean#L471-L505) ([local copy](code/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/AssertEqOpcode.lean))

```lean
theorem sound_assert_eq [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
      (varAssign : VarAssign)
      {memAssign : Felt252IdMemoryAssign}
      {mem : Felt252 → Felt252}
      (h_mem_agrees : memAssign.Agrees mem)
      (ab : AirBuilder)
      (lt : AirLookupTerms)
      {h_satisfied : LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels}
      (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
      (h_mem : AirLookupTerms.MemYieldsAgreeAndRangeChecked memAssign h_satisfied.values
            (h_satisfied.tuples RANGE_CHECK_REL_INDEX)
            (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX)
            (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
      (h_verify_instr : AirLookupTerms.VerifyInstrYieldAgrees h_satisfied.tuples)
      {casmState : CasmState}
      {num_steps: Nat} :
    let ⟨new_ab, new_lt, ρCasmState⟩ := call false false ab lt casmState
    num_steps < 2^29 →
    (casmState.eval varAssign).strongly_bounded₀ num_steps →
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      (ρCasmState.eval varAssign).strongly_bounded (num_steps+1) ∧
      NextState mem (casmState.eval varAssign).toRegisterStateFelt252 (ρCasmState.eval varAssign).toRegisterStateFelt252 := by
  intro h_num_steps h_bound h_sat h_agree
  rcases sound_auto varAssign memAssign ab lt
      h_satisfied h_rc h_mem h_verify_instr _ false false
      num_steps h_sat h_agree
    with ⟨_, _, h_spec⟩
  have h_flags : AssertEqOpcode.flag_assert false false := by simp [AssertEqOpcode.flag_assert]
  rcases h_spec h_flags h_num_steps (CasmStateVal.strongly_bounded_of_strongly_bounded₀ h_bound) with ⟨h_bound, h_step⟩
  use h_bound
  rcases h_step mem h_mem_agrees with ⟨dst_base_fp, op0_base_fp, op1_base_fp, ap_update_add_1, offset0, offset1, offset2, h_instr, h_next⟩
  use (AssertEqOpcode.mkAssertEqInstr false false
        dst_base_fp op0_base_fp op1_base_fp ap_update_add_1 offset0 offset1 offset2).toInstruction
  use h_instr
```

### child `sound_jump_imm`: [`Stwo/Verification/AirInfra/Airs/Casm/Opcodes/JumpOpcode.lean` lines 597-631](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/JumpOpcode.lean#L597-L631) ([local copy](code/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/JumpOpcode.lean))

```lean
theorem sound_jump_imm [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
      (varAssign : VarAssign)
      {memAssign : Felt252IdMemoryAssign}
      {mem : Felt252 → Felt252}
      (h_mem_agrees : memAssign.Agrees mem)
      (ab : AirBuilder)
      (lt : AirLookupTerms)
      {h_satisfied : LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels}
      (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
      (h_mem : AirLookupTerms.MemYieldsAgreeAndRangeChecked memAssign h_satisfied.values
            (h_satisfied.tuples RANGE_CHECK_REL_INDEX)
            (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX)
            (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
      (h_verify_instr : AirLookupTerms.VerifyInstrYieldAgrees h_satisfied.tuples)
      {casmState : CasmState}
      {num_steps: Nat} :
    let ⟨new_ab, new_lt, ρCasmState⟩ := call true true false ab lt casmState
    num_steps < 2^29 →
    (casmState.eval varAssign).strongly_bounded₀ num_steps →
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      (ρCasmState.eval varAssign).strongly_bounded (num_steps+1) ∧
      NextState mem (casmState.eval varAssign).toRegisterStateFelt252 (ρCasmState.eval varAssign).toRegisterStateFelt252 := by
  intro h_num_steps h_bound h_sat h_agree
  rcases sound_auto varAssign memAssign ab lt
      h_satisfied h_rc h_mem h_verify_instr _ num_steps true true false
      h_sat h_agree
    with ⟨_, _, h_spec⟩
  have h_flags : flag_assert true true false := by simp [flag_assert]
  rcases h_spec h_flags h_num_steps (CasmStateVal.strongly_bounded_of_strongly_bounded₀ h_bound) with ⟨h_bound, h_step⟩
  use h_bound
  rcases h_step mem h_mem_agrees with ⟨op0_base_fp, op1_base_fp, ap_update_add_1, offset1, offset2, h_instr, h_next⟩
  use (mkJumpInstr true true false
        op0_base_fp op1_base_fp ap_update_add_1 offset1 offset2).toInstruction
  use h_instr
```

### child `sound_jnz_not_taken`: [`Stwo/Verification/AirInfra/Airs/Casm/Opcodes/JnzOpcode.lean` lines 559-589](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/JnzOpcode.lean#L559-L589) ([local copy](code/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/JnzOpcode.lean))

```lean
theorem sound_jnz_not_taken [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
      (varAssign : VarAssign)
      {memAssign : Felt252IdMemoryAssign}
      {mem : Felt252 → Felt252}
      (h_mem_agrees : memAssign.Agrees mem)
      (ab : AirBuilder)
      (lt : AirLookupTerms)
      {h_satisfied : LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels}
      (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
      (h_mem : AirLookupTerms.MemYieldsAgreeAndRangeChecked memAssign h_satisfied.values
            (h_satisfied.tuples RANGE_CHECK_REL_INDEX)
            (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX)
            (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
      (h_verify_instr : AirLookupTerms.VerifyInstrYieldAgrees h_satisfied.tuples)
      {casmState : CasmState}
      {num_steps: Nat} :
    let ⟨new_ab, new_lt, ρCasmState⟩ := call ab lt casmState
    num_steps < 2^29 →
    (casmState.eval varAssign).strongly_bounded₀ num_steps →
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      (ρCasmState.eval varAssign).strongly_bounded (num_steps+1) ∧
      NextState mem (casmState.eval varAssign).toRegisterStateFelt252 (ρCasmState.eval varAssign).toRegisterStateFelt252 := by
  intro h_num_steps h_bound h_sat h_agree
  rcases sound_auto varAssign memAssign ab lt h_satisfied h_rc h_mem h_verify_instr _ num_steps h_sat h_agree
    with ⟨_, _, h_spec⟩
  rcases h_spec h_num_steps (CasmStateVal.strongly_bounded_of_strongly_bounded₀ h_bound) with ⟨h_bound, h_step⟩
  use h_bound
  rcases h_step mem h_mem_agrees with ⟨offset_dst, dst_base_fp, ap_update_add_1, h_instr, h_next⟩
  use (jnz_instr dst_base_fp ap_update_add_1 offset_dst).toInstruction
  use h_instr
```

### child `sound_add_ap`: [`Stwo/Verification/AirInfra/Airs/Casm/Opcodes/AddApOpcode.lean` lines 604-634](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/AddApOpcode.lean#L604-L634) ([local copy](code/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/AddApOpcode.lean))

```lean
theorem sound_add_ap [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
      (varAssign : VarAssign)
      {memAssign : Felt252IdMemoryAssign}
      {mem : Felt252 → Felt252}
      (h_mem_agrees : memAssign.Agrees mem)
      (ab : AirBuilder)
      (lt : AirLookupTerms)
      {h_satisfied : LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels}
      (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
      (h_mem : AirLookupTerms.MemYieldsAgreeAndRangeChecked memAssign h_satisfied.values
            (h_satisfied.tuples RANGE_CHECK_REL_INDEX)
            (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX)
            (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
      (h_verify_instr : AirLookupTerms.VerifyInstrYieldAgrees h_satisfied.tuples)
      {casmState : CasmState}
      {num_steps: Nat} :
    let ⟨new_ab, new_lt, ρCasmState⟩ := call ab lt casmState
    num_steps < 2^29 →
    (casmState.eval varAssign).strongly_bounded₀ num_steps →
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      (ρCasmState.eval varAssign).strongly_bounded (num_steps+1) ∧
      NextState mem (casmState.eval varAssign).toRegisterStateFelt252 (ρCasmState.eval varAssign).toRegisterStateFelt252 := by
  intro h_num_steps h_bound h_sat h_agree
  rcases sound_auto varAssign memAssign ab lt h_satisfied h_rc h_mem h_verify_instr _ num_steps h_sat h_agree
    with ⟨_, _, h_spec⟩
  rcases h_spec h_num_steps (CasmStateVal.strongly_bounded_of_strongly_bounded₀ h_bound) with ⟨h_bound, h_step⟩
  use h_bound
  rcases h_step mem h_mem_agrees with ⟨offset2, op1_imm, op1_base_fp, h_instr, h_next⟩
  use (add_ap_instr op1_imm op1_base_fp offset2).toInstruction
  use h_instr
```

### child `sound_add_252`: [`Stwo/Verification/AirInfra/Airs/Casm/Opcodes/AddOpcode.lean` lines 1772-1802](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/AddOpcode.lean#L1772-L1802) ([local copy](code/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/AddOpcode.lean))

```lean
theorem sound_add_252 [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : Nat}
      (varAssign : VarAssign)
      {memAssign : Felt252IdMemoryAssign}
      {mem : Felt252 → Felt252}
      (h_mem_agrees : memAssign.Agrees mem)
      (ab : AirBuilder)
      (lt : AirLookupTerms)
      {h_satisfied : LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels}
      (h_rc : RangeCheckYields h_satisfied.values (h_satisfied.tuples RANGE_CHECK_REL_INDEX))
      (h_mem : AirLookupTerms.MemYieldsAgreeAndRangeChecked memAssign h_satisfied.values
            (h_satisfied.tuples RANGE_CHECK_REL_INDEX)
            (h_satisfied.tuples MEMORY_ADDR_TO_ID_REL_INDEX)
            (h_satisfied.tuples MEMORY_ID_TO_VALUE_REL_INDEX))
      (h_verify_instr : AirLookupTerms.VerifyInstrYieldAgrees h_satisfied.tuples)
      {casmState : CasmState}
      {num_steps: Nat} :
    let ⟨new_ab, new_lt, ρCasmState⟩ := call ab lt casmState
    num_steps < 2^29 →
    (casmState.eval varAssign).strongly_bounded₀ num_steps →
    new_ab.SatisfiedBy varAssign →
    new_lt.UseAgree varAssign h_satisfied.values h_satisfied.partitions h_satisfied.tuples →
      (ρCasmState.eval varAssign).strongly_bounded (num_steps+1) ∧
      NextState mem (casmState.eval varAssign).toRegisterStateFelt252 (ρCasmState.eval varAssign).toRegisterStateFelt252 := by
  intro h_num_steps h_bound h_sat h_agree
  rcases sound_auto varAssign memAssign ab lt h_satisfied h_rc h_mem h_verify_instr _ num_steps h_sat h_agree
    with ⟨_, _, h_spec⟩
  rcases h_spec h_num_steps (CasmStateVal.strongly_bounded_of_strongly_bounded₀ h_bound) with ⟨h_bound, h_step⟩
  use h_bound
  rcases h_step mem h_mem_agrees with ⟨offset0, offset1, offset2, dst_base_fp, op0_base_fp, op1_imm, op1_base_fp, ap_update_add_1, h_instr, h_next⟩
  use (add_instr dst_base_fp op0_base_fp op1_imm op1_base_fp ap_update_add_1 offset0 offset1 offset2).toInstruction
  use h_instr
```

How the parts fit. The glue is a bare `cases o` (line 346) after a little
normalisation (`simp [OpcodeAirFns, OpcodeLookupCall, OpcodeCall]` and
`revert h_opcode_satisfied h_agree`). Each of the 19 `Opcode` constructors
becomes one `case` whose body is `intro h_sat h_agree h_bound` followed by a
single `apply <Module>.sound_<ctor>` with the *same* argument list in every
case. There is no other proof work in the glue: the dispatch is generated by
the `Opcode` inductive (context site above), and `cases o` covers all 19
constructors by the type's totality, so there is no separate exhaustiveness
child.

Each child `sound_X` is itself a thin wrapper. Its proof (a) instantiates the
module's spec-level lemma `sound_auto` with the opcode's fixed flag values —
`CallOpcode.sound_call_rel` calls `CallOpcode.sound_auto … true false`,
`AssertEqOpcode.sound_assert_eq` calls it with `false false` — and (b) unwraps
the resulting `spec` into the `strongly_bounded (num_steps+1) ∧ NextState` goal
by `use h_bound`, `use <instr>.toInstruction`, `use h_instr`. The `Generic`
and `Ret` cases carry no flags and call their module's `sound_auto` directly.

Why each child is a good leaf: its statement is self-contained (every
hypothesis — the memory/lookup/range-check agreements — is an explicit
parameter, none free), and its proof closes on two named siblings (`sound_auto`
and the module's `flag_assert`), one shared library lemma
(`CasmStateVal.strongly_bounded_of_strongly_bounded₀`) and the module's
instruction builder. Below `sound_auto` the chain continues into
per-subcomponent lemmas — `GenericOpcode.sound_auto` applies
`UpdateRegisters.sound_auto`, `HandleOpcodes.sound_auto`,
`EvalOperands.sound_auto` and `DecodeGenericInstruction.sound_auto` — so the
deepest chain I traced is `exec_step_sound` → `sound_generic` → `sound_auto`
→ `DecodeGenericInstruction.sound_auto` (depth 3).

The other 11 direct lemmas are shown here only by pointer; each is a
near-identical wrapper over its module's `sound_auto`, differing only in the
flag values and the instruction builder:

| constructor | lemma | declaration |
|---|---|---|
| `CallAbsBaseFP` | `CallOpcode.sound_call_abs_base_fp` | [CallOpcode.lean:433](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/CallOpcode.lean#L433) |
| `CallAbsBaseAP` | `CallOpcode.sound_call_abs_base_ap` | [CallOpcode.lean:468](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/CallOpcode.lean#L468) |
| `AssertEqImm` | `AssertEqOpcode.sound_assert_eq_imm` | [AssertEqOpcode.lean:507](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/AssertEqOpcode.lean#L507) |
| `AssertEqDoubleDeref` | `AssertEqOpcode.sound_assert_eq_double_deref` | [AssertEqOpcode.lean:543](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/AssertEqOpcode.lean#L543) |
| `JumpDoubleDeref` | `JumpOpcode.sound_jump_double_deref` | [JumpOpcode.lean:633](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/JumpOpcode.lean#L633) |
| `JumpRel` | `JumpOpcode.sound_jump_rel` | [JumpOpcode.lean:669](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/JumpOpcode.lean#L669) |
| `JumpAbs` | `JumpOpcode.sound_jump_abs` | [JumpOpcode.lean:705](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/JumpOpcode.lean#L705) |
| `JnzTaken` | `JnzOpcode.JnzTakenOpcode.sound_jnz_taken` | [JnzOpcode.lean:972](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/JnzOpcode.lean#L972) |
| `AddSmall` | `AddOpcode.AddSmallOpcode.sound_add_small` | [AddOpcode.lean:893](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/AddOpcode.lean#L893) |
| `MulSmall` | `MulOpcode.MulSmallOpcode.sound_mul_small` | [MulOpcode.lean:970](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/MulOpcode.lean#L970) |
| `Mul252` | `MulOpcode.Mul252Opcode.sound_mul_252` | [MulOpcode.lean:1899](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Airs/Casm/Opcodes/MulOpcode.lean#L1899) |

In my opinion the detail worth copying is not the `cases` itself but that the
whole proof *is* just the type: with one lemma per constructor already in
place, the soundness proof is a mechanical dispatch with no per-case reasoning
left over.

## Why it is good

1. The parent `exec_step_sound` is a real declaration spanning
   `FinalSoundness.lean` lines 317-403 (`check`, `declared`).
2. `sound_generic` occurs in the parent site, at the `Generic` case
   (`check`, `cites`).
3. The parent site contains no `sorry`, `admit` or `axiom`, so no case is
   closed by a hole (`check`, `no_sorry`).
4. The shape: 19 direct lemmas (one `apply` per `Opcode` constructor in the
   glue, lines 347-403, matching the 19 constructors in `Components.lean`
   lines 9-29), depth 3 (the longest project-lemma chain I traced below the
   theorem), a glue of 87 lines and 8 shown children of 31-35 lines each
   (`measurement`, counted from the site ranges).
5. The same per-opcode lemma shape — a module-level `sound_auto` plus 1-4
   `sound_X` wrappers that fix the opcode's flags and unwrap the spec — is
   repeated across 9 opcode modules for 19 wrappers total; the 11 wrappers
   not shown as sites are listed above (`known-use`, pointers to their
   declarations).

## When to use it, and when not

Use it when the goal is parameterised by a finite inductive type (here
`Opcode`) and every constructor already has a pre-written lemma of exactly the
goal's shape, so the glue is a `cases` plus one `apply` per constructor and the
exhaustiveness is discharged by the type. It is the natural shape for a
machine-code or bytecode interpreter whose opcode semantics are each proven
once, in their own module, and then glued at the dispatcher.

Avoid it when the constructors do not share one statement template, so each
case needs a different argument rather than a bare `apply`; when the
per-constructor lemmas do not exist yet (the move's cost is N proofs, one per
constructor, and they are near-identical, so the cost is better spent on the
shared `sound_auto`/`spec` layer than on the wrappers); or when the glue must
do real work besides dispatching, such as rearranging hypotheses per case.

## Consequences

The move creates one obligation per constructor of the underlying type. Here
the exhaustiveness obligation is discharged automatically — `cases o` covers
all 19 `Opcode` constructors because the type is total, so no separate
exhaustiveness child is needed. Two obligations remain for the author: each
constructor's lemma must have exactly the goal's shape
(`strongly_bounded₀ num_steps → strongly_bounded (num_steps+1) ∧ NextState`
after the opcode's `call`), or the bare `apply` will not match; and adding a
constructor to `Opcode` forces both a new `sound_X` lemma and a new `case`, so
the proof is coupled to the opcode set. The failure mode is a monolith break:
the 19 wrappers are near-identical templates over the shared `sound_auto`/`spec`
infrastructure, so a change to that layer breaks the whole family at once.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: sound_generic@Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:349, sound_call_rel@Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:352, sound_ret@Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:361, sound_assert_eq@Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:364, sound_jump_imm@Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:373, sound_jnz_not_taken@Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:385, sound_add_ap@Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:391, sound_add_252@Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:397; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(exec_step_sound, Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean, 317-403) -> declared: exec_step_sound is declared at Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:317 | check_claims.py |
| 2 | verified | cites(parent, sound_generic) -> cites: sound_generic occurs at Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:349 | check_claims.py |
| 3 | verified | no_sorry(Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean, 317-403) -> no_sorry: none of sorry, admit, axiom in Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:317-403 | check_claims.py |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/starkware-libs/formal-proofs at commit `d0dd8279612a248cbc6bf6d286030bf0bb2a37ff`, under `LicenseRef-unknown`; see the [source note](../../sources/formal-proofs/SOURCE.md) for the licence text and attribution.
