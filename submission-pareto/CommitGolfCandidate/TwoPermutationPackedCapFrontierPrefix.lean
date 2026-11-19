import CommitGolfCandidate.TwoPermutationPackedCapFetch

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64

set_option maxRecDepth 4096
attribute [local simp] MachineState.getReg_setPC Opening.getReg_setReg
@[local simp] private theorem pc_after (state : MachineState) (pc : Word) : (state.setPC pc).pc = pc := rfl

def frontierCode : List Instr :=
  [.SLLI .x7 .x6 5, .ADD .x7 .x25 .x7, .ADDI .x28 .x21 30, .BLTU .x22 .x28 268]

def frontierPrefix (state : MachineState) (count : Nat) : MachineState :=
  (frontierCode.take count).foldl execInstrBr state

theorem execute_frontier_prefix (state : MachineState) (pc : state.pc = 0x1498) (fuel : Nat) :
    execute packedImage (4+fuel) state false =
      (do let next ← execute packedImage fuel (frontierPrefix state 4) false
          return next.charge 4 0) := by
  apply execute_unit_steps (states := frontierPrefix state)
  intro i bounded
  refine ⟨.base (frontierCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_fetch _ (294+i) _ (by omega)
    · interval_cases i <;> simp [frontierPrefix, frontierCode, execInstrBr, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem frontier_prefix_post (state : MachineState) (pc : state.pc = 0x1498) :
    let next := frontierPrefix state 4
    next.pc = (if state.getReg .x22 < state.getReg .x21+30#64 then 0x15b0 else 0x14a8) ∧
    next.getReg .x7 = state.getReg .x25+(state.getReg .x6 <<< 5) ∧
    next.getReg .x28 = state.getReg .x21+30#64 ∧ next.mem = state.mem := by
  by_cases short : state.getReg .x22 < state.getReg .x21+30#64
  · have branch : (state.getReg .x22).ult (state.getReg .x21+30#64) = true := decide_eq_true short
    simp [frontierPrefix, frontierCode, execInstrBr, signExtend12, signExtend13, pc, short, branch]
    rfl
  · have branch : (state.getReg .x22).ult (state.getReg .x21+30#64) = false := decide_eq_false short
    simp [frontierPrefix, frontierCode, execInstrBr, signExtend12, signExtend13, pc, short, branch]
    rfl

theorem frontier_prefix_register (state : MachineState) (r : Reg) (dest : r ≠ .x7) (endPtr : r ≠ .x28) :
    (frontierPrefix state 4).getReg r = state.getReg r := by
  by_cases short : (state.getReg .x22).ult (state.getReg .x21+30#64)
  · simp [frontierPrefix, frontierCode, execInstrBr, signExtend12, Ne.symm dest, Ne.symm endPtr, short]
  · simp [frontierPrefix, frontierCode, execInstrBr, signExtend12, Ne.symm dest, Ne.symm endPtr, short]

def frontierFinish (state : MachineState) :=
  (state.setReg .x21 (state.getReg .x21+30#64)).setPC 0x1528

theorem execute_frontier_finish (state : MachineState) (pc : state.pc = 0x1524) (fuel : Nat) :
    execute packedImage (1+fuel) state false =
      (do let result ← execute packedImage fuel (frontierFinish state) false
          return result.charge 1 0) := by
  have fetched := cap_fetch state 329 (.ADDI .x21 .x21 30) (by decide) pc rfl
  have stepped : ordinaryStep state (.base (.ADDI .x21 .x21 30)) = some (frontierFinish state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, frontierFinish, pc]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

end TwoPermutationPrototype.Packed.Checker
