import CommitGolfCandidate.QuadCheckerSteps
import CommitGolfCandidate.TwoPermutationOpeningBlocks
import CommitGolfCandidate.TwoPermutationOpeningGeometry

namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype

private def setFactor (state : MachineState) := execInstrBr state (.ADDI .x6 .x0 1424)
def measureState (state : MachineState) := execInstrBr (setFactor state) (.MUL .x6 .x16 .x6)

theorem execute_measure (state : MachineState) (pc : state.pc = 4096) :
    Hop state (measureState state) 2 5 := by
  intro fuel
  have first := fetch_at state 0 (.ADDI .x6 .x0 1424) (by decide) pc rfl
  have nextPC : (setFactor state).pc = 4100 := by
    change state.pc+4 = _
    rw [pc]
    rfl
  have second := fetch_at (setFactor state) 1 (.MUL .x6 .x16 .x6) (by decide) nextPC rfl
  have execFirst : ordinaryStep state (.base (.ADDI .x6 .x0 1424)) = some (setFactor state) := rfl
  have execSecond : ordinaryStep (setFactor state) (.base (.MUL .x6 .x16 .x6)) =
      some (measureState state) := rfl
  rw [show 2+fuel = (fuel+1)+1 by omega,
    execute_ordinary_step _ _ _ _ _ _ first execFirst,
    execute_ordinary_step _ _ _ _ _ _ second execSecond]
  simp [instructionCycles, Execution.charge, bind_assoc, ← Nat.add_assoc]

theorem measure_post (state : MachineState) (pc : state.pc = 4096) :
    let next := measureState state
    next.pc = 4104 ∧ next.getReg .x6 = state.getReg .x16*1424 ∧
      next.mem = state.mem ∧ ∀ r, r ≠ .x6 → next.getReg r = state.getReg r := by
  have zero : state.getReg .x0 = 0#64 := rfl
  refine ⟨?_,?_,rfl,?_⟩
  · change state.pc+4+4 = _
    rw [pc]
    rfl
  · simp [measureState,setFactor,execInstrBr,signExtend12,zero,MachineState.getReg_setPC,
      Opening.getReg_setReg]
  · intro r saved
    simp [measureState,setFactor,execInstrBr,signExtend12,zero,MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm saved)]

end TwoPermutationPrototype.Quad.Checker
