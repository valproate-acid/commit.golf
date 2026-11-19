import CommitGolfCandidate.TwoPermutationPackedCheckerSteps
import CommitGolfCandidate.TwoPermutationSyscall
import CommitGolfCandidate.TwoPermutationOpeningBlocks

namespace TwoPermutationPrototype.Packed.RecordLeaf
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Packed.Checker (packedImage fetch_at)
open TwoPermutationPrototype.RV64
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
attribute [local simp] Opening.getReg_setMem Opening.getReg_setReg MachineState.getReg_setPC
@[local simp] private theorem mem_set_reg (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).mem = s.mem := by cases r <;> rfl

@[local simp] private theorem mem_set_pc (s : MachineState) (v : Word) :
    (s.setPC v).mem = s.mem := rfl

@[local simp] private theorem set_pc_pc (s : MachineState) (pc : Word) :
    (s.setPC pc).pc = pc := rfl

def firstPreamble : List Instr := [.ADDI .x12 .x10 8, .ADDI .x10 .x10 40]

def secondPreamble : List Instr :=
  [.ADDI .x10 .x10 56, .ADDI .x31 .x28 96, .ADDI .x0 .x0 0, .ADDI .x0 .x0 0,
   .SD .x10 .x31 0, .LD .x31 .x4 0, .SD .x10 .x31 8,
   .LD .x31 .x4 8, .SD .x10 .x31 16, .ADDI .x12 .x23 0]

def firstPrefix (state : MachineState) (count : Nat) : MachineState :=
  (firstPreamble.take count).foldl execInstrBr state

def secondPrefix (state : MachineState) (count : Nat) : MachineState :=
  (secondPreamble.take count).foldl execInstrBr state

theorem execute_first_prefix (state : MachineState) (pc : state.pc = 0x10b0) (fuel : Nat) :
    execute packedImage (2 + fuel) state false =
      (do let result ← execute packedImage fuel (firstPrefix state 2) false
          return result.charge 2 0) := by
  apply execute_unit_steps (states := firstPrefix state)
  intro i bounded
  refine ⟨.base (firstPreamble[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetch_at _ (44+i) _ (by omega)
    · interval_cases i <;> simp [firstPrefix,firstPreamble,execInstrBr,pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem execute_second_prefix (state : MachineState) (pc : state.pc = 0x10bc) (fuel : Nat)
    (tagDst : accessValid (state.getReg .x10 + 56#64) 8 = true)
    (saltDst : accessValid (state.getReg .x10 + 64#64) 8 = true)
    (saltDstTail : accessValid (state.getReg .x10 + 72#64) 8 = true)
    (saltSrc : accessValid (state.getReg .x4) 8 = true)
    (saltSrcTail : accessValid (state.getReg .x4 + 8#64) 8 = true) :
    execute packedImage (10 + fuel) state false =
      (do let result ← execute packedImage fuel (secondPrefix state 10) false
          return result.charge 10 0) := by
  apply execute_unit_steps (states := secondPrefix state)
  intro i bounded
  refine ⟨.base (secondPreamble[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetch_at _ (47+i) _ (by omega)
    · interval_cases i <;> simp [secondPrefix,secondPreamble,execInstrBr,pc]
    · interval_cases i <;> rfl
  · interval_cases i <;>
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,
        secondPrefix,secondPreamble,BitVec.add_assoc,
        show 56#64+8#64=64#64 by decide,show 56#64+16#64=72#64 by decide,
        tagDst,saltDst,saltDstTail,saltSrc,saltSrcTail] <;> assumption
  · interval_cases i <;> rfl

theorem checker_first_ecall (state : MachineState) (pc : state.pc = 0x10b8) :
    fetch packedImage state = some (.base .ECALL) :=
  fetch_at state 46 .ECALL (by decide) pc rfl

theorem checker_second_ecall (state : MachineState) (pc : state.pc = 0x10e4) :
    fetch packedImage state = some (.base .ECALL) :=
  fetch_at state 57 .ECALL (by decide) pc rfl

def checkerNonce (state : MachineState) : Words 2 := fun i =>
  if i.val = 0 then state.getMem (state.getReg .x4) else state.getMem (state.getReg .x4+8#64)

def secondHeaderMemory (state : MachineState) : MachineState :=
  let tag := state.getReg .x28+96#64
  let afterTag := state.setMem (state.getReg .x10+56#64) tag
  let afterNonce := afterTag.setMem (state.getReg .x10+64#64) (checkerNonce state 0)
  afterNonce.setMem (state.getReg .x10+72#64) (checkerNonce state 1)

theorem first_prefix_post (state : MachineState) :
    let after := firstPrefix state 2
    after.mem = state.mem ∧ after.getReg .x10 = state.getReg .x10 + 40 ∧
    after.getReg .x12 = state.getReg .x10 + 8 ∧ after.pc = state.pc + 8 ∧
    after.getReg .x5 = state.getReg .x5 ∧ after.getReg .x11 = state.getReg .x11 ∧
    after.getReg .x13 = state.getReg .x13 := by
  simp [firstPrefix,firstPreamble,execInstrBr,signExtend12,BitVec.add_assoc] <;> rfl

theorem second_prefix_post (state : MachineState)
    (d0 : state.getReg .x4 ≠ state.getReg .x10+56#64)
    (e0 : state.getReg .x4+8#64 ≠ state.getReg .x10+56#64)
    (e8 : state.getReg .x4+8#64 ≠ state.getReg .x10+64#64) :
    let after := secondPrefix state 10
    after.mem = (secondHeaderMemory state).mem ∧
    after.getReg .x10 = state.getReg .x10+56#64 ∧ after.getReg .x12 = state.getReg .x23 ∧
    after.pc = state.pc + 40 ∧ after.getReg .x5 = state.getReg .x5 ∧
    after.getReg .x11 = state.getReg .x11 ∧ after.getReg .x13 = state.getReg .x13 := by
  simp [secondPrefix,secondPreamble,secondHeaderMemory,checkerNonce,execInstrBr,signExtend12,
    MachineState.setPC,MachineState.setMem,MachineState.getMem, MachineState.getReg,
    MachineState.setReg,BitVec.add_assoc] at d0 e0 e8 ⊢
  simp [d0,e0,e8]

theorem first_prefix_register (state : MachineState) (reg : Reg)
    (a : reg ≠ .x10) (b : reg ≠ .x12) :
    (firstPrefix state 2).getReg reg = state.getReg reg := by
  simp [firstPrefix,firstPreamble,execInstrBr,Ne.symm a,Ne.symm b]

theorem second_prefix_register (state : MachineState) (reg : Reg)
    (a : reg ≠ .x10) (b : reg ≠ .x12) (c : reg ≠ .x31) :
    (secondPrefix state 10).getReg reg = state.getReg reg := by
  simp [secondPrefix,secondPreamble,execInstrBr,Ne.symm a,Ne.symm b,Ne.symm c]

end TwoPermutationPrototype.Packed.RecordLeaf
