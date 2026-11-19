import CommitGolfCandidate.TwoPermutationPackedOpeningFields
import CommitGolfCandidate.TwoPermutationOpeningCapImage

namespace TwoPermutationPrototype.PackedOpening
set_option maxRecDepth 4096
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem

def exitPrefix (state : MachineState) (count : Nat) : MachineState :=
  (Opening.exitInstructions.take count).foldl execInstrBr state

/-- The common return block returns the final proof pointer minus its start. -/
theorem execute_exit (state : MachineState) (pc : state.pc = 0x1a5c) (fuel : Nat)
    (allowCoins : Bool) :
    execute openingImage (4 + fuel) state allowCoins =
      pure ⟨.success, exitPrefix state 3, 4, 0⟩ := by
  have ranPrefix : execute openingImage (3 + (fuel + 1)) state allowCoins =
      (do let result ← execute openingImage (fuel + 1) (exitPrefix state 3) allowCoins
          return result.charge 3 0) := by
    apply execute_unit_steps (states := exitPrefix state)
    intro i bounded
    refine ⟨.base ((Opening.exitInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply packed_fetch_base _ (663 + i) _ (by omega)
      · interval_cases i <;> simp [exitPrefix, Opening.exitInstructions, execInstrBr, MachineState.setPC, pc]
      · interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have halted : fetch openingImage (exitPrefix state 3) = some (.base .ECALL) := by
    apply packed_fetch_base _ 666 _ (by decide)
    · simp [exitPrefix, Opening.exitInstructions, execInstrBr, MachineState.setPC, pc]
    · rfl
  have haltFlag : (exitPrefix state 3).getReg .x5 = 1 := by
    simp [exitPrefix, Opening.exitInstructions, execInstrBr, signExtend12,
      show state.getReg .x0 = 0 from rfl]
  have successFlag : (exitPrefix state 3).getReg .x10 = 0 := by
    simp [exitPrefix, Opening.exitInstructions, execInstrBr, signExtend12,
      show state.getReg .x0 = 0 from rfl]
  rw [show 4 + fuel = 3 + (fuel + 1) by omega, ranPrefix]
  simp [execute, halted, haltFlag, successFlag, Execution.charge]

theorem exit_register (state : MachineState) :
    (exitPrefix state 3).getReg .x11 = state.getReg .x21 - state.getReg .x20 := by
  simp [exitPrefix, Opening.exitInstructions, execInstrBr]

theorem exit_memory (state : MachineState) : (exitPrefix state 3).mem = state.mem := rfl

end TwoPermutationPrototype.PackedOpening
