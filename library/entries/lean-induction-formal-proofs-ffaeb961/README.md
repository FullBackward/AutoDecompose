# Fin.induction along an opcode execution path for the Stwo AIR soundness lemma (exec_sound)

| | |
|---|---|
| Kind | instance |
| Move | induction |
| Language | lean |
| Status | draft |
| Source | [formal-proofs](../../sources/formal-proofs/SOURCE.md) at `d0dd8279612a` |
| Licence | `LicenseRef-unknown` |
| Licence recorded | 2026-11-14T12:12:07Z |

## Intent

The Stwo AIR soundness lemma `exec_sound` is reduced to a path of opcode
steps: an existence lemma `exec_path` supplies the execution path, and the
step relation `NextState` is then proved to hold along that path by
`Fin.induction`, every step closed by the per-step lemma `exec_step_sound`
whose six side conditions are each built by one named lemma.

## The decomposition

### parent `exec_sound`: [`Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean` lines 405-497](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean#L405-L497) ([local copy](code/Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean))

```lean
lemma exec_sound [Fact (Nat.Prime Stwo.P)] [Fact (Nat.Prime Felt252Prime)] {t n_s : ℕ}

      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign}

      (h_pubMem : PublicMem.LookupsAgree inp.mStar pubMemLookups)

      -- Lookups are satisfied
      (h_satisfied: LookupsSatisfied t n_s NUM_PARTITIONS NUM_LOOKUP_REL_MINUS_ONE partition_lengths rel_partition chain_rels)

      -- Lookups agree with the assignments to the lookup terms
      (h_use_agree : ∀ rel, RelUseLookupsAgree inp pubMemLookups varAssigns rel (h_satisfied.tuples rel))
      (h_yield_agree : ∀ rel, RelYieldLookupsAgree inp pubMemLookups varAssigns rel (h_satisfied.tuples rel))
      -- Memory assignments are functions.
      (h_is_mem_addr_to_id : IsMemAssign (varAssigns .MemoryAddrToId))
      (h_is_mem_id_to_value : IsMemAssign (varAssigns .MemoryIdToValue))
      -- Range check rows are range checked.
      (h_rc : IsRangeCheckAssign (varAssigns .RangeCheck))
      -- The constraints of the components are satisfied.
      (h_components: ComponentsSatisfied varAssigns)

      -- Number of steps
      (h_num_steps :  (RelLookups inp pubMemLookups varAssigns OPCODE_TRACE_REL_INDEX .use).size ≤ 2^29)
      (h_state_bound : (initialState inp).strongly_bounded₀ 0) :

    ∃ memAssign : Felt252IdMemoryAssign,
      ∀ mem : Felt252 → Felt252,
        memAssign.Agrees mem →
          Option.FnExtends mem inp.mStar ∧
          (initialState inp = finalState inp ∨
              ∃ n : Nat, n < (RelLookups inp pubMemLookups varAssigns OPCODE_TRACE_REL_INDEX .use).size
              ∧ ∃ exec : Fin (n + 1) → (Opcode × VarAssign),
                (∀ i, (exec i).2 ∈ varAssigns (.Opcode (exec i).1))
                ∧ OpcodeInStateVal (exec 0) = initialState inp
                ∧ OpcodeOutStateVal (exec (Fin.last n)) = finalState inp
                ∧ (∀ i : Fin n, OpcodeOutStateVal (exec i.castSucc)  = OpcodeInStateVal (exec i.succ))
                ∧ ∀ i : Fin (n + 1),
                  (OpcodeOutStateVal (exec i)).strongly_bounded (i.val + 1) ∧
                  NextState mem (OpcodeInStateVal (exec i)).toRegisterStateFelt252 (OpcodeOutStateVal (exec i)).toRegisterStateFelt252) := by
  have h_verify_instr := VerifyInstrYieldAgrees_of_agree_and_satisfy
    varAssigns h_components h_use_agree (h_yield_agree VERIFY_INSTR_REL_INDEX)
  have h_opcodes_satisfied : ∀ o, ∀ v ∈ varAssigns (.Opcode o), (OpcodeAirFns o).1.SatisfiedBy v := by
    intro o v ; exact h_components (.Opcode o) v
  have h_lookup_terms_agree :
      ∀ o, ∀ v ∈ varAssigns (.Opcode o), (OpcodeAirFns o).2.1.UseAgree v h_satisfied.values h_satisfied.partitions h_satisfied.tuples := by
    intro o v
    exact UseAgree_of_RelLookupsAgree h_use_agree (.Opcode o) v
  have h_opcode_agree : OpcodeStatesAgree inp (h_satisfied.tuples OPCODE_TRACE_REL_INDEX) (OpcodeVarAssigns varAssigns) := by
    exact OpcodeStatesAgree_of_lookups_agree
      (h_satisfied.tuples OPCODE_TRACE_REL_INDEX)
      (h_use_agree OPCODE_TRACE_REL_INDEX)
      (h_yield_agree OPCODE_TRACE_REL_INDEX)
  have h_mem_assign := memory_assign_MemYieldsAgreeAndRangeChecked_of_agrees
                        varAssigns h_use_agree h_yield_agree h_is_mem_addr_to_id h_is_mem_id_to_value
  have h_rc_yield := range_checked_yields_of_range_check_assign varAssigns h_yield_agree h_rc
  have h_disjoint := partition_tuples_disjoint_of_rel_in_rel (h_satisfied.covering) h_use_agree h_yield_agree OPCODE_TRACE_REL_INDEX

  use (MemAssignFromVarAssigns (varAssigns .MemoryAddrToId) (varAssigns .MemoryIdToValue))
  intro mem h_mem_agrees
  use mem_extends_pub_mem h_pubMem h_satisfied h_use_agree h_yield_agree h_is_mem_addr_to_id h_is_mem_id_to_value h_rc h_mem_agrees
  cases exec_path h_satisfied.constraints h_disjoint (h_satisfied.h_bad OPCODE_TRACE_REL_INDEX)
          (h_satisfied.h_inj OPCODE_TRACE_REL_INDEX opcode_trace_is_chain_rel)
          (h_satisfied.h_chain OPCODE_TRACE_REL_INDEX opcode_trace_is_chain_rel)
          inp _ h_opcode_agree
  case inl h => left ; exact h
  case inr h_exec =>
    right
    rcases h_exec with ⟨n, h_n_lt, path, h_path_mem, h_path_start, h_path_end, h_path_succ⟩
    replace h_n_lt := (Nat.lt_succ_of_lt h_n_lt)
    rw [Nat.succ_eq_add_one, ←@RelLookups_OPCODE_TRACE_OpcodeStatePairVals_size_eq _ inp pubMemLookups varAssigns] at h_n_lt
    use n, h_n_lt, path, h_path_mem, h_path_start, h_path_end, h_path_succ
    intro i
    induction i using Fin.induction
    case zero =>
      rw [←h_path_start] at h_state_bound
      exact (exec_step_sound h_mem_agrees
              (h_opcodes_satisfied (path 0).1 (path 0).2 (h_path_mem 0))
              (h_lookup_terms_agree (path 0).1 (path 0).2 (h_path_mem 0))
              h_rc_yield h_mem_assign h_verify_instr 0 (by norm_num) h_state_bound)
    case succ i ih =>
    · apply exec_step_sound h_mem_agrees
              (h_opcodes_satisfied (path i.succ).1 (path i.succ).2 (h_path_mem i.succ))
              (h_lookup_terms_agree (path i.succ).1 (path i.succ).2 (h_path_mem i.succ))
              h_rc_yield h_mem_assign h_verify_instr i.succ
      · rw [Fin.val_succ, Nat.add_lt_iff_lt_sub_right]
        apply lt_of_lt_of_le (Fin.isLt i)
        apply Nat.le_sub_one_of_lt
        exact lt_of_lt_of_le h_n_lt h_num_steps
      apply CasmStateVal.strongly_bounded₀_of_strongly_bounded
      · simp
      rw [←h_path_succ i]
      apply ih.1
```

### child `exec_path`: [`Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean` lines 272-315](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean#L272-L315) ([local copy](code/Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean))

```lean
lemma exec_path [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {values : LookupValues t n_s NUM_PARTITIONS}
      (h_constraints : LookupConstraints values)
      {partition : LookupPartition values (rel_partition OPCODE_TRACE_REL_INDEX) (rel_lengths OPCODE_TRACE_REL_INDEX)}
      {h_tuples : RelationTuples partition}
      (h_disjoint : ∀ i ∈ h_tuples.use_i ∪ h_tuples.yield_i, ∀ j ∉ h_tuples.use_i ∪ h_tuples.yield_i, partition.tuples i ≠ partition.tuples j)
      (h_bad : NotInBadSet OPCODE_TRACE_REL_INDEX chain_rels h_tuples)
      (h_inj : (fun (i : {i // i ∈ h_tuples.use_i ∪ h_tuples.yield_i}) => partition.to_all_indxs i).Injective)
      (h_y : ∀ i ∈ h_tuples.yield_i, values.m (partition.to_all_indxs i) = -1)
      (inp : InputData)
      (varAssigns : Opcode → Array VarAssign)
      (h_agree : OpcodeStatesAgree inp h_tuples varAssigns) :
    initialState inp = finalState inp ∨
    ∃ n : Nat, n < (OpcodeStatePairVals varAssigns).size
      ∧ ∃ path : Fin (n + 1) → (Opcode × VarAssign),
        (∀ i, (path i).2 ∈ varAssigns (path i).1)
        ∧ OpcodeInStateVal (path 0) = initialState inp
        ∧ OpcodeOutStateVal (path (Fin.last n)) = finalState inp
        ∧ ∀ i : Fin n, OpcodeOutStateVal (path i.castSucc)  = OpcodeInStateVal (path i.succ) := by
  cases cycle_through_state_pairs h_constraints h_disjoint h_bad h_inj h_y inp varAssigns h_agree
  · case inl h =>
      left
      apply CasmStateValTuple_inj
      simp at h
      exact h.symm
  case inr h =>
    right
    rcases h with ⟨n, h_n_lt, path, h_path_mem, h_path_start, h_path_end, h_path_succ⟩
    use n
    constructor
    · apply lt_of_lt_of_le h_n_lt
      simp [StatePairTuples]
    simp only [tuple_pair_mem] at h_path_mem
    rcases opcode_path_of_tuple_path h_path_mem with ⟨spath, h_spath⟩
    use spath
    rw [forall_and] at h_spath
    use h_spath.1
    simp [h_spath.2] at h_path_start
    use CasmStateValTuple_inj h_path_start
    simp [h_spath.2] at h_path_end
    use CasmStateValTuple_inj h_path_end
    simp [h_spath.2] at h_path_succ
    intro i
    exact CasmStateValTuple_inj (h_path_succ i)
```

### child `exec_step_sound`: [`Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean` lines 317-403](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean#L317-L403) ([local copy](code/Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean))

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

### child `UseAgree_of_RelLookupsAgree`: [`Stwo/Verification/AirInfra/Soundness/ComponentLookupCall.lean` lines 317-349](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Soundness/ComponentLookupCall.lean#L317-L349) ([local copy](code/Stwo/Verification/AirInfra/Soundness/ComponentLookupCall.lean))

```lean
lemma UseAgree_of_RelLookupsAgree [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign}
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partitions : (p : Fin (NUM_PARTITIONS + 1)) → LookupPartition values p (partition_lengths p)}
      {tuples : (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) → RelationTuples (partitions (rel_partition k))}
      (h_agree : ∀ rel, RelUseLookupsAgree inp pubMemLookups varAssigns rel (tuples rel)) :
    ∀ c, ∀ v ∈ varAssigns c, (ComponentLookupCall c).2.UseAgree v values partitions tuples := by
  intro c v h_v
  simp only [AirLookupTerms.UseAgree]
  intro t h_t_mem h_t_use
  rw [use_mem_iff_mem, h_agree t.rel]
  simp only [Multiset.mem_coe, Array.mem_toList_iff]
  simp only [RelLookupTuples, Array.mem_map]
  simp only [Array.mem_attach, true_and, Subtype.exists]
  use t.eval v
  have h_mem : LookupTerm.eval v t ∈ RelLookups inp pubMemLookups varAssigns t.rel UseOrYield.use := by
    simp [RelLookups]
    constructor
    · simp only [AllLookups, Array.mem_push]
      left ; left
      simp only [Array.append_eq_append, Array.mem_append]
      left
      simp only [ComponentLookups, Array.mem_flatMap]
      use c
      rw [Array.mem_toArray]
      use Component.univ_complete c
      simp [ComponentLookupTermsEval]
      use t, h_t_mem, v
    simp [LookupTerm.eval, h_t_use]
  use h_mem
  simp
```

### child `VerifyInstrYieldAgrees_of_agree_and_satisfy`: [`Stwo/Verification/AirInfra/Soundness/ComponentLookupCall.lean` lines 471-501](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Soundness/ComponentLookupCall.lean#L471-L501) ([local copy](code/Stwo/Verification/AirInfra/Soundness/ComponentLookupCall.lean))

```lean
lemma VerifyInstrYieldAgrees_of_agree_and_satisfy [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      (varAssigns : Component → Array VarAssign)
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partitions : (p : Fin (NUM_PARTITIONS + 1)) → LookupPartition values p (partition_lengths p)}
      {tuples : (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) → RelationTuples (partitions (rel_partition k))}
      (h_components: ComponentsSatisfied varAssigns)
      (h_use_agree : ∀ rel, RelUseLookupsAgree inp pubMemLookups varAssigns rel (tuples rel))
      (h_agree : RelYieldLookupsAgree inp pubMemLookups varAssigns VERIFY_INSTR_REL_INDEX (tuples VERIFY_INSTR_REL_INDEX)) :
    AirLookupTerms.VerifyInstrYieldAgrees tuples := by
  unfold AirLookupTerms.VerifyInstrYieldAgrees
  intro tuple h_tuple_mem
  rw [yield_mem_iff_mem, h_agree] at h_tuple_mem
  simp only [Multiset.mem_coe, Array.mem_toList_iff] at h_tuple_mem
  simp only [RelLookupTuples, Array.mem_map] at h_tuple_mem
  simp only [Array.mem_attach, true_and, Subtype.exists] at h_tuple_mem
  rcases h_tuple_mem with ⟨t, h_t_mem, h_t_eq⟩
  rcases mem_VerifyInstrLookups t h_t_mem with ⟨t_verify, h_t_verify_mem, v, h_v_mem, h_eval_eq⟩
  use t_verify, h_t_verify_mem
  simp only [RelLookups, Array.mem_filter, decide_eq_true_eq] at h_t_mem
  subst h_eval_eq
  simp only [LookupTerm.eval] at h_t_mem
  use h_t_mem.2.1, h_t_mem.2.2
  use v, h_components .VerifyInstr v h_v_mem
  use UseAgree_of_RelLookupsAgree h_use_agree .VerifyInstr v h_v_mem
  simp only [←h_t_eq]
  simp only [LookupTerm.eval]
  apply funext
  intro i
  simp
```

### child `OpcodeStatesAgree_of_lookups_agree`: [`Stwo/Verification/AirInfra/Soundness/ComponentLookupCall.lean` lines 726-738](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Soundness/ComponentLookupCall.lean#L726-L738) ([local copy](code/Stwo/Verification/AirInfra/Soundness/ComponentLookupCall.lean))

```lean
lemma OpcodeStatesAgree_of_lookups_agree [Fact (Nat.Prime Stwo.P)] {t n_s : Nat}
      {inp: InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign}
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partition : LookupPartition values (rel_partition OPCODE_TRACE_REL_INDEX) (rel_lengths OPCODE_TRACE_REL_INDEX)}
      (h_tuples : RelationTuples partition)
      (h_use_agree : RelUseLookupsAgree inp pubMemLookups varAssigns OPCODE_TRACE_REL_INDEX h_tuples)
      (h_yield_agree : RelYieldLookupsAgree inp pubMemLookups varAssigns OPCODE_TRACE_REL_INDEX h_tuples) :
    OpcodeStatesAgree inp h_tuples (OpcodeVarAssigns varAssigns) := by
  constructor
  · exact InOpcodeStatesAgree_of_RelUseLookupsAgree h_use_agree
  exact OutOpcodeStatesAgree_of_RelYieldLookupsAgree h_yield_agree
```

### child `memory_assign_MemYieldsAgreeAndRangeChecked_of_agrees`: [`Stwo/Verification/AirInfra/Soundness/ComponentLookupCall.lean` lines 1186-1208](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Soundness/ComponentLookupCall.lean#L1186-L1208) ([local copy](code/Stwo/Verification/AirInfra/Soundness/ComponentLookupCall.lean))

```lean
lemma memory_assign_MemYieldsAgreeAndRangeChecked_of_agrees [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      (varAssigns : Component → Array VarAssign)
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partitions : (p : Fin (NUM_PARTITIONS + 1)) → LookupPartition values p (partition_lengths p)}
      {tuples : (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) → RelationTuples (partitions (rel_partition k))}
      (h_use_agree : ∀ rel, RelUseLookupsAgree inp pubMemLookups varAssigns rel (tuples rel))
      (h_yield_agree : ∀ rel, RelYieldLookupsAgree inp pubMemLookups varAssigns rel (tuples rel))
      (h_is_mem_addr_to_id : IsMemAssign (varAssigns .MemoryAddrToId))
      (h_is_mem_id_to_value : IsMemAssign (varAssigns .MemoryIdToValue)) :
      AirLookupTerms.MemYieldsAgreeAndRangeChecked
        (MemAssignFromVarAssigns (varAssigns .MemoryAddrToId) (varAssigns .MemoryIdToValue))
        values
        (tuples RANGE_CHECK_REL_INDEX)
        (tuples MEMORY_ADDR_TO_ID_REL_INDEX)
        (tuples MEMORY_ID_TO_VALUE_REL_INDEX) := by
  unfold AirLookupTerms.MemYieldsAgreeAndRangeChecked
  constructor
  · use memory_assign_addr_to_id_of_mem_yields_agree varAssigns tuples h_yield_agree h_is_mem_addr_to_id
    use memory_assign_id_to_value_of_mem_yields_agree varAssigns tuples h_yield_agree h_is_mem_id_to_value
  use memory_assign_addr_range_checked_of_agrees varAssigns tuples h_use_agree
  exact memory_assign_value_range_checked_of_agrees varAssigns tuples h_use_agree
```

### child `range_checked_yields_of_range_check_assign`: [`Stwo/Verification/AirInfra/Soundness/ComponentLookupCall.lean` lines 1327-1350](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Soundness/ComponentLookupCall.lean#L1327-L1350) ([local copy](code/Stwo/Verification/AirInfra/Soundness/ComponentLookupCall.lean))

```lean
lemma range_checked_yields_of_range_check_assign [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      (varAssigns : Component → Array VarAssign)
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partitions : (p : Fin (NUM_PARTITIONS + 1)) → LookupPartition values p (partition_lengths p)}
      {tuples : (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) → RelationTuples (partitions (rel_partition k))}
      (h_yield_agree : ∀ rel, RelYieldLookupsAgree inp pubMemLookups varAssigns rel (tuples rel))
      (h_rc : IsRangeCheckAssign (varAssigns .RangeCheck)) :
    RangeCheckYields _ (tuples RANGE_CHECK_REL_INDEX) := by
  intro y h_y_mem
  simp only [yield_mem_iff_mem] at h_y_mem
  rw [h_yield_agree RANGE_CHECK_REL_INDEX] at h_y_mem
  simp [mem_RelLookupTuples_iff _] at h_y_mem
  rcases h_y_mem with ⟨t, h_t_mem, h_t_useOrYield, ⟨h_rel, h_tuple⟩⟩
  rcases mem_RangeCheckYieldLookups' t h_t_mem with ⟨v, h_v_mem, h_t_eq⟩
  subst h_t_eq
  simp at h_tuple
  rw [h_tuple, p_tuple_one_eq_tuple_zero, p_tuple_two_eq_tuple_one]
  simp
  rw [Array.mem_iff_getElem] at h_v_mem
  rcases h_v_mem with ⟨i, h_i_lt, h_eq⟩
  simp only [←h_eq]
  exact h_rc i h_i_lt
```

### child `partition_tuples_disjoint_of_rel_in_rel`: [`Stwo/Verification/AirInfra/Soundness/ComponentLookupCall.lean` lines 1506-1541](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Soundness/ComponentLookupCall.lean#L1506-L1541) ([local copy](code/Stwo/Verification/AirInfra/Soundness/ComponentLookupCall.lean))

```lean
lemma partition_tuples_disjoint_of_rel_in_rel [Fact (Nat.Prime Stwo.P)] {t n_s : ℕ}
      {values : LookupValues t n_s NUM_PARTITIONS}
      {partitions : (p : Fin (NUM_PARTITIONS + 1)) → LookupPartition values p (partition_lengths p)}
      {tuples : (k : Fin (NUM_LOOKUP_REL_MINUS_ONE + 1)) → RelationTuples (partitions (rel_partition k))}
      (covering: RelationsCoverPartitions tuples)
      {inp : InputData}
      {pubMemLookups : PublicMem.Lookups}
      {varAssigns : Component → Array VarAssign}
      (h_use_agree : ∀ rel, RelUseLookupsAgree inp pubMemLookups varAssigns rel (tuples rel))
      (h_yield_agree : ∀ rel, RelYieldLookupsAgree inp pubMemLookups varAssigns rel (tuples rel)) :
    ∀ k, ∀ i ∈ (tuples k).use_i ∪ (tuples k).yield_i,
      ∀ j ∉ (tuples k).use_i ∪ (tuples k).yield_i, (partitions (rel_partition k)).tuples i ≠ (partitions (rel_partition k)).tuples j := by
  intro k i h_i_mem j h_j_nin
  rcases covering (rel_partition k) j with ⟨k_j, h_k_rel, h_k_j_mem⟩
  simp only [Fin.cast_eq_self] at h_k_j_mem
  have h_k_j_ne : ¬(k_j = k) := by
    by_contra h_k ; rw [h_k] at h_k_j_mem ; exact h_j_nin h_k_j_mem
  have h_k_mem_rel := partition_tuple_mem_RelLookupTuples h_use_agree h_yield_agree k i h_i_mem
  have h_k_j_mem_rel := partition_tuple_mem_RelLookupTuples h_use_agree h_yield_agree k_j j h_k_j_mem
  rw [Array.mem_append] at h_k_mem_rel h_k_j_mem_rel
  have h_0_eq_k : (partitions (rel_partition k)).tuples i 0 = k := by
    cases h_k_mem_rel with | inl h | inr h
    all_goals apply rel_in_RelLookupTuples _ h
  have h_0_eq_k_j : (partitions (rel_partition k)).tuples j 0 = k_j := by
    cases h_k_j_mem_rel with | inl h | inr h
    all_goals apply rel_in_RelLookupTuples _ h
  rw [ne_eq, funext_iff, Classical.not_forall]
  use 0
  simp [h_0_eq_k, h_0_eq_k_j]
  intro h_eq
  apply h_k_j_ne
  rw [←Fin.val_eq_val]
  apply Nat.cast_inj_of_lt_char _ _ h_eq.symm
  all_goals
    apply lt_trans (Fin.isLt _)
    simp [NUM_LOOKUP_REL_MINUS_ONE, Felt, ZMod.ringChar_zmod_n, Stwo.P]
```

How the parts fit. `exec_sound`'s proof (the glue, lines 444-497) runs in
two acts. First it *assembles the side conditions*, each with exactly one
named lemma:

- `h_verify_instr := VerifyInstrYieldAgrees_of_agree_and_satisfy …` (line 445);
- `h_lookup_terms_agree := UseAgree_of_RelLookupsAgree …` (line 452);
- `h_opcode_agree := OpcodeStatesAgree_of_lookups_agree …` (line 454);
- `h_mem_assign := memory_assign_MemYieldsAgreeAndRangeChecked_of_agrees …` (line 458);
- `h_rc_yield := range_checked_yields_of_range_check_assign …` (line 460);
- `h_disjoint := partition_tuples_disjoint_of_rel_in_rel …` (line 461).

It then introduces the memory witness `MemAssignFromVarAssigns …`, proves the
`Option.FnExtends` conjunct with `mem_extends_pub_mem` (line 465), and cases on
`exec_path` (line 466) to get either `initialState = finalState` (trivial) or a
path `n, path, h_path_mem, h_path_start, h_path_end, h_path_succ`.

Second, and this is the move, it proves the step relation along the path by
`induction i using Fin.induction` (line 478). The `zero` case applies
`exec_step_sound` with the transferred initial bound (line 481); the `succ i
ih` case applies `exec_step_sound` again at `path i.succ` and gets its bound
from the induction hypothesis `ih.1` through
`CasmStateVal.strongly_bounded₀_of_strongly_bounded` (lines 486-497).

Lemma graph (glue → children; arrows read "feeds"):

```
exec_sound ── h_verify_instr ── VerifyInstrYieldAgrees_of_agree_and_satisfy
          ├─ h_lookup_terms_agree ── UseAgree_of_RelLookupsAgree
          ├─ h_opcode_agree ── OpcodeStatesAgree_of_lookups_agree
          ├─ h_mem_assign ── memory_assign_MemYieldsAgreeAndRangeChecked_of_agrees
          ├─ h_rc_yield ── range_checked_yields_of_range_check_assign
          ├─ h_disjoint ── partition_tuples_disjoint_of_rel_in_rel
          ├─ Option.FnExtends ── mem_extends_pub_mem
          ├─ path ── exec_path        (consumes h_disjoint, h_opcode_agree)
          └─ step ── exec_step_sound  (consumes h_verify_instr, h_lookup_terms_agree, h_rc_yield, h_mem_assign)
```

Why each shown child is a good leaf (a self-contained statement whose proof
closes on its own or from named siblings):

- `exec_path` and `exec_step_sound` are the two lemmas that carry the
  induction: the first supplies the thing to induct over, the second is the
  uniform per-step step whose own proof is a `cases o` dispatch to one
  per-opcode `sound_*` lemma. They close on their own hypotheses.
- The six `h_*` side-condition lemmas are each a leaf that turns a group of
  `exec_sound`'s hypotheses into exactly the hypothesis `exec_path` or
  `exec_step_sound` expects: `UseAgree_of_RelLookupsAgree` lifts use-agreement
  to `UseAgree` (closes by `rw [use_mem_iff_mem, h_agree t.rel]`);
  `VerifyInstrYieldAgrees_of_agree_and_satisfy` and
  `OpcodeStatesAgree_of_lookups_agree` close by `constructor` and named
  siblings (`InOpcodeStatesAgree_of_RelUseLookupsAgree`,
  `OutOpcodeStatesAgree_of_RelYieldLookupsAgree`); `memory_assign_…`,
  `range_checked_yields_…` and `partition_tuples_disjoint_…` close on their
  own hypotheses (the last by `contradiction` after deriving two differing
  tuples).

The ninth direct lemma, `mem_extends_pub_mem`
([`ComponentLookupCall.lean` lines 1394-1426](https://github.com/starkware-libs/formal-proofs/blob/d0dd8279612a248cbc6bf6d286030bf0bb2a37ff/Stwo/Verification/AirInfra/Soundness/ComponentLookupCall.lean#L1394-L1426)),
proves the `Option.FnExtends mem inp.mStar` conjunct. It is listed rather than
shown because it is the one child not part of the induction — it is a
precondition of the whole theorem — and it is not a leaf: it itself reuses two
of the siblings shown above (`range_checked_yields_of_range_check_assign` and
`memory_assign_MemYieldsAgreeAndRangeChecked_of_agrees`, lines 1418-1420).

Depth. The longest chain of project lemmas below `exec_sound` that was
checked, of length 5, runs entirely inside `FinalSoundness.lean`:
`exec_sound` (405) → `exec_path` (272) → `cycle_through_state_pairs` (206,
used at 291) → `equal_count_states_of_multiplicity_one` (186, used at 229) →
`equal_count_state_tuples_of_multiplicity_one` (162, used at 203) →
`equal_count_tuples_chain_rel_of_multiplicity_one` (111, used at 181). The
chain continues deeper through `equal_count_tuples_of_multiplicity_one`, which
is imported from outside the copied files, so 5 is a lower bound, not the
maximum.

## Why it is good

1. `exec_sound` is declared at `FinalSoundness.lean:405-497` (check,
   permalink above).
2. The glue cites `exec_step_sound` — the per-step lemma it applies at the
   `zero` and `succ` cases of the `Fin.induction` (check, permalink above).
3. The `exec_sound` proof contains no `sorry`/`admit`/`axiom` (check,
   permalink above).
4. `exec_sound` is assembled from 9 named lemmas: the glue is the 93-line site
   `FinalSoundness.lean:405-497`, and the `Fin.induction` applies
   `exec_step_sound` twice, at line 481 (zero) and 486 (succ) (measurement,
   counted from the file).
5. The theorem `trace_sound` (`FinalSoundness.lean:499-573`), the file's
   trace-level soundness theorem, consumes `exec_sound` via
   `rcases exec_sound …` at line 532 (known-use), so the assembled lemma is a
   reusable interface rather than a dead end.

In my opinion the detail worth copying is the *strong* `Fin.induction`
discipline: the induction hypothesis is exactly the boundedness predicate of
the previous step, and `h_path_succ` (from `exec_path`) is what lets the
`succ` case feed the previous output into the next input — the path lemma and
the step lemma are designed so their hypotheses line up without further glue.

## When to use it, and when not

Use this move when a soundness or reachability goal is a disjunction
"trivial terminal case ∨ there is a path", and the step relation along the
path is uniform, so one per-step lemma closes every position. It needs three
things to line up: a path-existence lemma (here `exec_path`), a per-step lemma
whose input and output bounds match the induction hypothesis
(`exec_step_sound`'s `strongly_bounded₀ num_steps → strongly_bounded
(num_steps + 1)`), and a strong induction on the path index that exposes the
previous step's output as the hypothesis (`Fin.induction` over `i : Fin
(n + 1)`, applied at `i.succ` with `ih` about `i.castSucc`).

Avoid it when the step obligation varies along the path (then no single
per-step lemma applies and the induction is better replaced by a case split on
the step kind), when there is no path-existence lemma and the induction must
itself construct the path, or when the per-step lemma is the hard part and not
yet proved — the induction then merely reduces the theorem to one unclosed
leaf. Also avoid it when the path is not finite or not indexed by a `Fin` with
a natural induction principle.

## Consequences

The induction creates one obligation per path position, all closed by the
same per-step lemma `exec_step_sound`, so the proof's size is uniform rather
than growing with the path length. The induction hypothesis must be exactly
the boundedness predicate of the previous step (`strongly_bounded₀ num_steps →
strongly_bounded (num_steps + 1)`), so the `succ` case composes through
`CasmStateVal.strongly_bounded₀_of_strongly_bounded`; the `zero` case needs the
initial bound `h_state_bound` transferred through `h_path_start`, and the
`succ` case needs `h_path_succ` to connect the previous output to the current
input. Known failure mode: if the per-step lemma's input/output bounds do not
match the induction-hypothesis shape, the `succ` case cannot use `ih.1`, and
either the per-step lemma must be generalised (a `suffices`/strengthen step)
or the induction must be over a different variable.

## Verification

<!-- verification:start -->
Status: **draft**

| Check | Result | Evidence | By | Date |
|---|---|---|---|---|
| build | not-run | no CI workflow in the repository at the pinned commit d0dd8279612a248cbc6bf6d286030bf0bb2a37ff (list_files.py shows no .github/workflows or any .yml/.yaml among 312 files); no Lean toolchain on the harvest machine | verifier | 2026-11-14 |
| fidelity | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |
| glue-cites-children | pass | cited: exec_path@Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:466, exec_step_sound@Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:481, UseAgree_of_RelLookupsAgree@Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:452, VerifyInstrYieldAgrees_of_agree_and_satisfy@Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:445, OpcodeStatesAgree_of_lookups_agree@Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:454, memory_assign_MemYieldsAgreeAndRangeChecked_of_agrees@Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:458, range_checked_yields_of_range_check_assign@Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:460, partition_tuples_disjoint_of_rel_in_rel@Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:461; subgoals (no name to cite): 0 | validate_entry.py | 2026-11-14 |
| provenance | pass | 3 file(s) byte-identical at d0dd8279612a248cbc6bf6d286030bf0bb2a37ff | check_provenance.py | 2026-11-14 |
| sorry-scan | pass | inside parent/child/skeleton sites: none; elsewhere in the copied files (not failed): none | sorry_scan.py | 2026-11-14 |
| sufficiency | not-run | no Lean or Rocq toolchain on the harvest machine, so the check was not run (protocol section 6, 'Checks without a local toolchain') | driver | 2026-11-14 |

| Claim | Verdict | Evidence | By |
|---|---|---|---|
| 1 | verified | declared(exec_sound, Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean, 405-497) -> declared: exec_sound is declared at Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:405 | check_claims.py |
| 2 | verified | cites(exec_sound, exec_step_sound) -> cites: exec_step_sound occurs at Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:481 | check_claims.py |
| 3 | verified | no_sorry(Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean, 405-497) -> no_sorry: none of sorry, admit, axiom in Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:405-497 | check_claims.py |
| 4 | verified | read code/Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:405-497. Glue site is 93 lines (497-405+1). The 9 named lemmas in the proof body: VerifyInstrYieldAgrees_of_agree_and_satisfy (L445), UseAgree_of_RelLookupsAgree (L452), OpcodeStatesAgree_of_lookups_agree (L454), memory_assign_MemYieldsAgreeAndRangeChecked_of_agrees (L458), range_checked_yields_of_range_check_assign (L460), partition_tuples_disjoint_of_rel_in_rel (L461), mem_extends_pub_mem (L465), exec_path (L466), exec_step_sound (L481,486). Fin.induction at L478; exec_step_sound applied in zero case at L481 and succ case at L486. | verifier |
| 5 | verified | read code/Stwo/Verification/AirInfra/Soundness/FinalSoundness.lean:499-573. theorem trace_sound starts at L499 and its proof ends at L573. It consumes exec_sound via 'rcases exec_sound' at L532 (args continue L533-534). | verifier |

| Review lens | Decision | Reason | By |
|---|---|---|---|
| correctness | accept | Verified against the local code copies. Parent exec_sound is declared at FinalSoundness.lean:405-497 and its proof closes via 'induction i using Fin.induction' (line 478), zero and succ cases each applying exec_step_sound at lines 481 and 486. All 8 children's declarations, statements and closed_by descriptions match their cited ranges verbatim (exec_path 272-315, exec_step_sound 317-403, UseAgree_of_RelLookupsAgree 317-349, VerifyInstrYieldAgrees_of_agree_and_satisfy 471-501, OpcodeStatesAgree_of_lookups_agree 726-738, memory_assign_... 1186-1208, range_checked_yields_... 1327-1350, partition_tuples_disjoint_... 1506-1541). No sorry/admit/axiom token in either copied file, so the proof closes. Glue cites 9 project lemmas (the 8 children plus mem_extends_pub_mem at line 465); the 9th is documented as a direct lemma not shown (children_shown=8), consistent with direct_lemmas=9. Shape numbers are exact: glue_lines=93 (497-405+1), child_lines=[44,87,33,31,13,23,24,36] match the 8 child-site line counts, depth=5 confirmed via exec_sound->exec_path->cycle_through_state_pairs(206, used 291)->equal_count_states_of_multiplicity_one(186, used 229)->equal_count_state_tuples_of_multiplicity_one(162, used 203)->equal_count_tuples_chain_rel_of_multiplicity_one(111, used 181), and trace_sound consumes exec_sound at line 532. | reviewer-correctness |
| generality | accept | Generality: the move is stated beyond the Stwo example — 'When to use' and applicability.goal_shape/use_when abstract it to a path induction (trivial-terminal-case disjunction + uniform per-step relation), and name the three things that must line up (path-existence lemma, per-step lemma with matching input/output bounds, strong Fin.induction exposing the previous output as the IH). 'When not to use' gives four honest, mechanism-tied conditions (step obligation varies -> case split; no path lemma -> induction must construct the path; per-step lemma unproved -> unclosed leaf; non-Fin-indexed path). Consequences are specific and match the code: one obligation per position closed by exec_step_sound, IH shape strongly_bounded0 n -> strongly_bounded (n+1), zero case needs h_state_bound via h_path_start, succ needs h_path_succ + strongly_bounded0_of_strongly_bounded + ih.1. The 'good leaf' section answers the bounded-prover question: each leaf is self-contained and closes on its own hypotheses or named siblings, with per-leaf closing tactics named. Verified cited anchors read true: induction at 478, exec_step_sound at 481/486, six h_* at 445-461, mem_extends_pub_mem 465, cases exec_path 466, trace_sound rcases exec_sound 532, depth chain declarations 111/162/186/206. Minor non-blocking nits: prose lists h_lookup_terms_agree at 452 (binder is 449) and h_opcode_agree at 454 (binder 453); 'bounded prover' is never literally named but the self-contained/short-proof criterion is the bounded-prover criterion in substance. | reviewer-generality |
| provenance-licence | accept | Permalinks, commit, licence and source note are mutually consistent and traceable. All 3 copied files' sha256 and byte counts match entry.json's files[] exactly (FinalSoundness.lean 26fde019.../30017, ComponentLookupCall.lean 1dc28e79.../71576, OpcodeLookupCall.lean 12cc2fd8.../18824). Every permalink (3 file + 9 site + known_uses trace_sound) pins commit d0dd8279612a248cbc6bf6d286030bf0bb2a37ff, identical to source.commit, sources/formal-proofs/source.json.commit and SOURCE.md's pinned commit. Licence is recorded as LicenseRef-unknown consistently in entry.json.source.licence, README, source.json and SOURCE.md; SOURCE.md states 'no licence file found at the root' matching licence_files:[], and the unknown-licence tag is allowed by protocol §2 decision 1. check_provenance.py already recorded '3 file(s) byte-identical at d0dd827...' (pass). No inconsistency found. | reviewer-provenance-licence |
<!-- verification:end -->

## Source and licence

Every file under [`code/`](code/) is copied whole and unmodified from https://github.com/starkware-libs/formal-proofs at commit `d0dd8279612a248cbc6bf6d286030bf0bb2a37ff`, under `LicenseRef-unknown`; see the [source note](../../sources/formal-proofs/SOURCE.md) for the licence text and attribution.
