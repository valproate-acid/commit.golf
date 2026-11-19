import CommitGolfCandidate.QOpeningCapCursor

namespace TwoPermutationPrototype.QOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] getReg_setReg getReg_setMem

@[local simp] private theorem step_pc_set (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

@[local simp] private theorem step_zeroreg (state : MachineState) : state.getReg .x0 = 0#64 := rfl

def advancePrefix (state : MachineState) (index count : Nat) : MachineState :=
  ((capWalkInstructions.drop index).take count).foldl execInstrBr state

/-- Two adjacent, ordinary cap instructions with no accessed memory. The first
instruction in each such pair follows the straight-line PC. -/
private theorem execute_cap_pair (state : MachineState) (index : Nat) (fuel : Nat)
    (allowCoins : Bool) (bounded : index + 1 < 27)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (55 + index)))
    (firstPC : (advancePrefix state index 1).pc = BitVec.ofNat 64 (4096 + 4 * (55 + (index + 1))))
    (trace : ∀ i < 2,
      (openingImage.code[55 + (index + i)]?).bind decodeInstruction =
        some (.base ((capWalkInstructions.drop index)[i]?.getD .EBREAK)) ∧
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
  apply opening_fetch _ (55 + (index + i)) _ (by omega) _ decodes
  interval_cases i
  · exact pc
  · exact firstPC

theorem execute_advance_root_test (state : MachineState) (pc : state.pc = 0x1128)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (2 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (advancePrefix state 19 2) allowCoins
          return result.charge 2 0) := by
  apply execute_cap_pair _ 19 _ _ (by decide) pc
  · simp [advancePrefix, capWalkInstructions, execInstrBr, pc]
  · intro i hi
    interval_cases i <;> exact ⟨rfl, rfl, rfl⟩

theorem advance_root_target (state : MachineState) (pc : state.pc = 0x1128) :
    (advancePrefix state 19 2).pc =
      if state.getReg .x6 = 1#64 then 0x1148 else 0x1130 := by
  by_cases root : state.getReg .x6 = 1#64 <;>
    simp [advancePrefix, capWalkInstructions, execInstrBr, signExtend12, signExtend13, pc, root]

theorem execute_advance_parity_test (state : MachineState) (pc : state.pc = 0x1130)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (2 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (advancePrefix state 21 2) allowCoins
          return result.charge 2 0) := by
  apply execute_cap_pair _ 21 _ _ (by decide) pc
  · simp [advancePrefix, capWalkInstructions, execInstrBr, pc]
  · intro i hi
    interval_cases i <;> exact ⟨rfl, rfl, rfl⟩

theorem advance_parity_target (state : MachineState) (pc : state.pc = 0x1130) :
    (advancePrefix state 21 2).pc =
      if (state.getReg .x6 &&& 1#64) = 0#64 then 0x1140 else 0x1138 := by
  by_cases even : (state.getReg .x6 &&& 1#64) = 0#64 <;>
    simp [advancePrefix, capWalkInstructions, execInstrBr, signExtend12, signExtend13, pc, even]

theorem execute_advance_up (state : MachineState) (pc : state.pc = 0x1138)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (2 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (advancePrefix state 23 2) allowCoins
          return result.charge 2 0) := by
  apply execute_cap_pair _ 23 _ _ (by decide) pc
  · simp [advancePrefix, capWalkInstructions, execInstrBr, pc]
  · intro i hi
    interval_cases i <;> exact ⟨rfl, rfl, rfl⟩

theorem advance_up_post (state : MachineState) (pc : state.pc = 0x1138) :
    let after := advancePrefix state 23 2
    after.pc = 0x1128 ∧ after.getReg .x6 = state.getReg .x6 >>> 1 ∧
      after.getReg .x21 = state.getReg .x21 ∧ after.mem = state.mem := by
  simp [advancePrefix, capWalkInstructions, execInstrBr, signExtend21, pc]
  rfl

theorem execute_advance_right (state : MachineState) (pc : state.pc = 0x1140)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (2 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (advancePrefix state 25 2) allowCoins
          return result.charge 2 0) := by
  apply execute_cap_pair _ 25 _ _ (by decide) pc
  · simp [advancePrefix, capWalkInstructions, execInstrBr, pc]
  · intro i hi
    interval_cases i <;> exact ⟨rfl, rfl, rfl⟩

theorem advance_right_post (state : MachineState) (pc : state.pc = 0x1140) :
    let after := advancePrefix state 25 2
    after.pc = 0x10e0 ∧ after.getReg .x6 = state.getReg .x6 + 1#64 ∧
      after.getReg .x21 = state.getReg .x21 ∧ after.mem = state.mem := by
  simp [advancePrefix, capWalkInstructions, execInstrBr, signExtend12, signExtend21, pc]
  rfl

end TwoPermutationPrototype.QOpening
