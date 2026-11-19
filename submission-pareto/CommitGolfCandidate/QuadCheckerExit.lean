import CommitGolfCandidate.QuadCheckerSteps
import CommitGolfCandidate.TwoPermutationCheckerRecording

namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Sampling

def headerRejectState (state : MachineState) : MachineState :=
  ((state.setReg .x5 1).setReg .x10 1).setPC 0x15b8

theorem execute_header_reject (state : MachineState) (pc : state.pc = 0x15b0) (fuel : Nat) :
    execute packedImage (3+fuel) state false = pure ⟨.failure, headerRejectState state, 3, 0⟩ := by
  let first := (state.setReg .x5 1).setPC 0x15b4
  have a := fetch_at state 364 (.ADDI .x5 .x0 1) (by decide) pc rfl
  have b := fetch_at first 365 (.ADDI .x10 .x0 1) (by decide) rfl rfl
  have c := fetch_at (headerRejectState state) 366 .ECALL (by decide) rfl rfl
  have r : ordinaryStep state (.base (.ADDI .x5 .x0 1)) = some first := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, pc, first] <;> rfl
  have t : ordinaryStep first (.base (.ADDI .x10 .x0 1)) = some (headerRejectState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, first, headerRejectState] <;> rfl
  rw [Nat.add_comm 3 fuel]
  simp only [execute, a, b, c, r, t, instructionCycles, pure_bind]
  rfl

def emptyBranch (state : MachineState) : MachineState :=
  state.setPC (if state.getReg .x17 = 0#64 then 0x15a4 else 0x15b0)

private theorem execute_empty_guard (state : MachineState) (pc : state.pc = 0x15a0) (fuel : Nat) :
    execute packedImage (1+fuel) state false =
      (do let next ← execute packedImage fuel (emptyBranch state) false
          return next.charge 1 0) := by
  have fetched := fetch_at state 360 (.BNE .x17 .x0 16) (by decide) pc rfl
  have stepped : ordinaryStep state (.base (.BNE .x17 .x0 16)) = some (emptyBranch state) := by
    by_cases zero : state.getReg .x17 = 0#64 <;>
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
        show state.getReg .x0 = 0#64 from rfl, emptyBranch, pc, zero]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

def emptySuccessState (state : MachineState) : MachineState :=
  ((state.setReg .x5 1).setReg .x10 0).setPC 0x15ac

private theorem execute_empty_success (state : MachineState) (pc : state.pc = 0x15a4) (fuel : Nat) :
    execute packedImage (3+fuel) state false = pure ⟨.success, emptySuccessState state,3,0⟩ := by
  let first := (state.setReg .x5 1).setPC 0x15a8
  have a := fetch_at state 361 (.ADDI .x5 .x0 1) (by decide) pc rfl
  have b := fetch_at first 362 (.ADDI .x10 .x0 0) (by decide) rfl rfl
  have c := fetch_at (emptySuccessState state) 363 .ECALL (by decide) rfl rfl
  have r : ordinaryStep state (.base (.ADDI .x5 .x0 1)) = some first := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, pc, first] <;> rfl
  have s : ordinaryStep first (.base (.ADDI .x10 .x0 0)) = some (emptySuccessState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, first, emptySuccessState] <;> rfl
  rw [Nat.add_comm 3 fuel]
  simp only [execute, a, b, c, r, s, instructionCycles, pure_bind]
  rfl

/-- The zero-cardinality branch accepts exactly an empty proof and makes no
public calls for either terminal exit. -/
theorem execute_empty_check (state : MachineState) (pc : state.pc = 0x15a0) (fuel : Nat) :
    ∃ result : Execution,
      (result.exit = .success ↔ state.getReg .x17 = 0#64) ∧ result.exit ≠ .unfinished ∧
      result.oracleCalls = 0 ∧ execute packedImage (4+fuel) state false = pure result := by
  rw [show 4+fuel = 1+(3+fuel) by omega, execute_empty_guard state pc]
  by_cases zero : state.getReg .x17 = 0#64
  · have next : (emptyBranch state).pc = 0x15a4 := by simp [emptyBranch, zero, MachineState.setPC]
    rw [execute_empty_success _ next]
    refine ⟨⟨.success,emptySuccessState (emptyBranch state),4,0⟩, by simp [zero],
      (show Exit.success ≠ Exit.unfinished by decide), rfl, ?_⟩
    simp [Execution.charge]
  · have next : (emptyBranch state).pc = 0x15b0 := by simp [emptyBranch, zero, MachineState.setPC]
    rw [execute_header_reject _ next]
    refine ⟨⟨.failure,headerRejectState (emptyBranch state),4,0⟩, by simp [zero],
      (show Exit.failure ≠ Exit.unfinished by decide), rfl, ?_⟩
    simp [Execution.charge]

theorem empty_check_recorded (oracle : Oracle) (state : MachineState) (pc : state.pc = 0x15a0)
    (fuel : Nat) :
    let observed := checkEvaluation oracle (recordRows (execute packedImage (4+fuel) state false))
    (observed.1.1.exit = .success ↔ state.getReg .x17 = 0#64) ∧
      observed.1.1.exit ≠ .unfinished ∧ observed.1.2 = [] ∧ observed.2 = 0 := by
  obtain ⟨result, accepts, ends, _, executed⟩ := execute_empty_check state pc fuel
  rw [executed, record_rows_pure, check_evaluation_pure]
  exact ⟨accepts, ends, rfl, rfl⟩

end TwoPermutationPrototype.Quad.Checker
