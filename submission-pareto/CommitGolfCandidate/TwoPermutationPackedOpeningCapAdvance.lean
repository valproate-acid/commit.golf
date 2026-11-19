import CommitGolfCandidate.TwoPermutationPackedOpeningCapCursor

namespace TwoPermutationPrototype.PackedOpening
set_option maxRecDepth 4096
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem

@[local simp] private theorem step_pc_set (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

@[local simp] private theorem step_zeroreg (state : MachineState) : state.getReg .x0 = 0#64 := rfl

def advanceCode : List Instr :=
  [.ADDI .x7 .x0 1, .BEQ .x6 .x7 28, .ANDI .x7 .x6 1, .BEQ .x7 .x0 12,
   .SRLI .x6 .x6 1, .JAL .x0 2097132, .ADDI .x6 .x6 1, .JAL .x0 2096964]

theorem at_root_test : capWalkInstructions.drop 41 = advanceCode := rfl
theorem at_parity_test : capWalkInstructions.drop 43 = advanceCode.drop 2 := rfl
theorem at_parent_step : capWalkInstructions.drop 45 = advanceCode.drop 4 := rfl
theorem at_right_step : capWalkInstructions.drop 47 = advanceCode.drop 6 := rfl

attribute [local simp] at_root_test at_parity_test at_parent_step at_right_step

def advancePrefix (state : MachineState) (index count : Nat) : MachineState :=
  ((capWalkInstructions.drop index).take count).foldl execInstrBr state

/-- Two adjacent, ordinary cap instructions with no accessed memory. The first
instruction in each such pair follows the straight-line PC. -/
private theorem execute_cap_pair (state : MachineState) (index : Nat) (fuel : Nat)
    (allowCoins : Bool) (bounded : index + 1 < 49)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (614 + index)))
    (firstPC : (advancePrefix state index 1).pc = BitVec.ofNat 64 (4096 + 4 * (614 + (index + 1))))
    (trace : ∀ i < 2,
      (openingImage.code[614 + (index + i)]?).bind Opening.decodeBase =
        some ((capWalkInstructions.drop index)[i]?.getD .EBREAK) ∧
      ordinaryStep (advancePrefix state index i)
        (.base ((capWalkInstructions.drop index)[i]?.getD .EBREAK)) =
          some (advancePrefix state index (i+1)) ∧
      instructionCycles (.base ((capWalkInstructions.drop index)[i]?.getD .EBREAK)) = 1) :
    execute openingImage (2 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (advancePrefix state index 2) allowCoins
          return result.charge 2 0) := by
  apply execute_unit_steps (states := advancePrefix state index)
  intro i hi
  obtain ⟨decodes, steps, cost⟩ := trace i hi
  refine ⟨.base ((capWalkInstructions.drop index)[i]?.getD .EBREAK), ?_, steps, cost⟩
  apply packed_fetch_base _ (614 + (index + i)) _ (by omega) _ decodes
  interval_cases i
  · exact pc
  · exact firstPC

theorem execute_advance_root_test (state : MachineState) (pc : state.pc = 0x1a3c)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (2 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (advancePrefix state 41 2) allowCoins
          return result.charge 2 0) := by
  apply execute_cap_pair _ 41 _ _ (by decide) pc
  · simp [advancePrefix, advanceCode, execInstrBr, pc]
  · intro i hi
    interval_cases i <;> exact ⟨rfl, rfl, rfl⟩

theorem advance_root_target (state : MachineState) (pc : state.pc = 0x1a3c) :
    (advancePrefix state 41 2).pc =
      if state.getReg .x6 = 1#64 then 0x1a5c else 0x1a44 := by
  by_cases root : state.getReg .x6 = 1#64 <;>
    simp [advancePrefix, advanceCode, execInstrBr, signExtend12, signExtend13, pc, root]

theorem execute_advance_parity_test (state : MachineState) (pc : state.pc = 0x1a44)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (2 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (advancePrefix state 43 2) allowCoins
          return result.charge 2 0) := by
  apply execute_cap_pair _ 43 _ _ (by decide) pc
  · simp [advancePrefix, advanceCode, execInstrBr, pc]
  · intro i hi
    interval_cases i <;> exact ⟨rfl, rfl, rfl⟩

theorem advance_parity_target (state : MachineState) (pc : state.pc = 0x1a44) :
    (advancePrefix state 43 2).pc =
      if (state.getReg .x6 &&& 1#64) = 0#64 then 0x1a54 else 0x1a4c := by
  by_cases even : (state.getReg .x6 &&& 1#64) = 0#64 <;>
    simp [advancePrefix, advanceCode, execInstrBr, signExtend12, signExtend13, pc, even]

theorem execute_advance_up (state : MachineState) (pc : state.pc = 0x1a4c)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (2 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (advancePrefix state 45 2) allowCoins
          return result.charge 2 0) := by
  apply execute_cap_pair _ 45 _ _ (by decide) pc
  · simp [advancePrefix, advanceCode, execInstrBr, pc]
  · intro i hi
    interval_cases i <;> exact ⟨rfl, rfl, rfl⟩

theorem advance_up_post (state : MachineState) (pc : state.pc = 0x1a4c) :
    let after := advancePrefix state 45 2
    after.pc = 0x1a3c ∧ after.getReg .x6 = state.getReg .x6 >>> 1 ∧
      after.getReg .x21 = state.getReg .x21 ∧ after.mem = state.mem := by
  simp [advancePrefix, advanceCode, execInstrBr, signExtend21, pc]
  rfl

theorem execute_advance_right (state : MachineState) (pc : state.pc = 0x1a54)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (2 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (advancePrefix state 47 2) allowCoins
          return result.charge 2 0) := by
  apply execute_cap_pair _ 47 _ _ (by decide) pc
  · simp [advancePrefix, advanceCode, execInstrBr, pc]
  · intro i hi
    interval_cases i <;> exact ⟨rfl, rfl, rfl⟩

theorem advance_right_post (state : MachineState) (pc : state.pc = 0x1a54) :
    let after := advancePrefix state 47 2
    after.pc = 0x199c ∧ after.getReg .x6 = state.getReg .x6 + 1#64 ∧
      after.getReg .x21 = state.getReg .x21 ∧ after.mem = state.mem := by
  simp [advancePrefix, advanceCode, execInstrBr, signExtend12, signExtend21, pc]
  rfl

end TwoPermutationPrototype.PackedOpening
