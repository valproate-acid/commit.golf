import CommitGolfCandidate.TwoPermutationPackedCapLookup
import CommitGolfCandidate.TwoPermutationCheckerCopyDigest

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64

set_option maxRecDepth 4096
attribute [local simp] MachineState.getReg_setPC Opening.getReg_setReg
@[local simp] private theorem pc_after (state : MachineState) (pc : Word) : (state.setPC pc).pc = pc := rfl

@[local simp] private theorem zero_register (state : MachineState) : state.getReg .x0 = 0#64 := rfl

def blockPrefix (code : List Instr) (state : MachineState) (count : Nat) : MachineState :=
  (code.take count).foldl execInstrBr state

def capRootTestCode : List Instr := [.ADDI .x7 .x0 1, .BEQ .x6 .x7 52]

def capRootTest (state : MachineState) := blockPrefix capRootTestCode state 2

theorem execute_cap_root_test (state : MachineState) (pc : state.pc = 0x1528) (fuel : Nat) :
    execute packedImage (2+fuel) state false =
      (do let next ← execute packedImage fuel (capRootTest state) false
          return next.charge 2 0) := by
  apply execute_unit_steps (states := blockPrefix capRootTestCode state)
  intro i inside
  refine ⟨.base (capRootTestCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_fetch _ (330+i) _ (by omega)
    · interval_cases i <;> simp [blockPrefix, capRootTestCode, execInstrBr, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

def capParityTestCode : List Instr := [.ANDI .x7 .x6 1, .BEQ .x7 .x0 36]

def capParityTest (state : MachineState) := blockPrefix capParityTestCode state 2

theorem execute_cap_parity_test (state : MachineState) (pc : state.pc = 0x1530) (fuel : Nat) :
    execute packedImage (2+fuel) state false =
      (do let next ← execute packedImage fuel (capParityTest state) false
          return next.charge 2 0) := by
  apply execute_unit_steps (states := blockPrefix capParityTestCode state)
  intro i inside
  refine ⟨.base (capParityTestCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_fetch _ (332+i) _ (by omega)
    · interval_cases i <;> simp [blockPrefix, capParityTestCode, execInstrBr, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

def capRightCode : List Instr := [.ADDI .x6 .x6 1, .JAL .x0 2096928]

def capRight (state : MachineState) := blockPrefix capRightCode state 2

theorem execute_cap_right (state : MachineState) (pc : state.pc = 0x1558) (fuel : Nat) :
    execute packedImage (2+fuel) state false =
      (do let next ← execute packedImage fuel (capRight state) false
          return next.charge 2 0) := by
  apply execute_unit_steps (states := blockPrefix capRightCode state)
  intro i inside
  refine ⟨.base (capRightCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_fetch _ (342+i) _ (by omega)
    · interval_cases i <;> simp [blockPrefix, capRightCode, execInstrBr, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

def capParentCode : List Instr := [.SRLI .x6 .x6 1, .SLLI .x10 .x6 6, .ADD .x10 .x25 .x10,
   .SLLI .x12 .x6 5, .ADD .x12 .x25 .x12]

def capParent (state : MachineState) := blockPrefix capParentCode state 5

theorem execute_cap_parent_setup (state : MachineState) (pc : state.pc = 0x1538) (fuel : Nat) :
    execute packedImage (5+fuel) state false =
      (do let next ← execute packedImage fuel (capParent state) false
          return next.charge 5 0) := by
  apply execute_unit_steps (states := blockPrefix capParentCode state)
  intro i inside
  refine ⟨.base (capParentCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_fetch _ (334+i) _ (by omega)
    · interval_cases i <;> simp [blockPrefix, capParentCode, execInstrBr, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

def capStartCode : List Instr := [.ADDI .x11 .x0 64, .ADDI .x13 .x0 0, .ADDI .x6 .x0 1]

def capStart (state : MachineState) := blockPrefix capStartCode state 3

theorem execute_cap_start (state : MachineState) (pc : state.pc = 0x1470) (fuel : Nat) :
    execute packedImage (3+fuel) state false =
      (do let next ← execute packedImage fuel (capStart state) false
          return next.charge 3 0) := by
  apply execute_unit_steps (states := blockPrefix capStartCode state)
  intro i inside
  refine ⟨.base (capStartCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_fetch _ (284+i) _ (by omega)
    · interval_cases i <;> simp [blockPrefix, capStartCode, execInstrBr, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem cap_root_post (state : MachineState) (pc : state.pc = 0x1528) :
    (capRootTest state).pc = if state.getReg .x6 = 1#64 then 0x1560 else 0x1530 := by
  by_cases root : state.getReg .x6 = 1#64 <;>
    simp [capRootTest, blockPrefix, capRootTestCode, execInstrBr, signExtend12, signExtend13, pc, root]

theorem cap_parity_post (state : MachineState) (pc : state.pc = 0x1530) :
    (capParityTest state).pc = if state.getReg .x6 &&& 1#64 = 0#64 then 0x1558 else 0x1538 := by
  by_cases parity : state.getReg .x6 &&& 1#64 = 0#64 <;>
    simp [capParityTest, blockPrefix, capParityTestCode, execInstrBr, signExtend12, signExtend13, pc, parity]

theorem cap_right_post (state : MachineState) (pc : state.pc = 0x1558) :
    let next := capRight state
    next.pc = 0x147c ∧ next.getReg .x6 = state.getReg .x6+1#64 ∧ next.mem = state.mem := by
  simp [capRight, blockPrefix, capRightCode, execInstrBr, signExtend12, signExtend21, pc]
  <;> rfl

theorem cap_parent_post (state : MachineState) (pc : state.pc = 0x1538) :
    let next := capParent state
    let parent := state.getReg .x6 >>> 1
    next.pc = 0x154c ∧ next.getReg .x6 = parent ∧
    next.getReg .x10 = state.getReg .x25 + (parent <<< 6) ∧
    next.getReg .x12 = state.getReg .x25 + (parent <<< 5) ∧ next.mem = state.mem := by
  simp [capParent, blockPrefix, capParentCode, execInstrBr, pc, BitVec.add_assoc] <;> rfl

theorem cap_parent_register (state : MachineState) (r : Reg)
    (node : r ≠ .x6) (source : r ≠ .x10) (dest : r ≠ .x12) :
    (capParent state).getReg r = state.getReg r := by
  simp [capParent, blockPrefix, capParentCode, execInstrBr, Ne.symm node, Ne.symm source, Ne.symm dest]

end TwoPermutationPrototype.Packed.Checker
