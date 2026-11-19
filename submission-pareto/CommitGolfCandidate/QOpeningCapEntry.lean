import CommitGolfCandidate.QOpeningMarkSweep

namespace TwoPermutationPrototype.QOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

def markSweepEntry (state : MachineState) : MachineState :=
  (state.setReg .x6 255).setPC 0x10b4

def cursorEntry (state : MachineState) : MachineState :=
  (state.setReg .x6 1).setPC 0x10e0

/-- Enter the descending sweep at parent 255, immediately after the last record. -/
theorem execute_mark_entry (state : MachineState) (pc : state.pc = 0x10b0)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (1 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (markSweepEntry state) allowCoins
          return result.charge 1 0) := by
  have fetched := opening_fetch state 44 (.ADDI .x6 .x0 255) (by decide) pc rfl
  have stepped : ordinaryStep state (.base (.ADDI .x6 .x0 255)) = some (markSweepEntry state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      markSweepEntry, pc, show state.getReg .x0 = 0#64 from rfl]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

/-- Start the cap cursor at the root after all parent marks are set. -/
theorem execute_cursor_entry (state : MachineState) (pc : state.pc = 0x10dc)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (1 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (cursorEntry state) allowCoins
          return result.charge 1 0) := by
  have fetched := opening_fetch state 55 (.ADDI .x6 .x0 1) (by decide) pc rfl
  have stepped : ordinaryStep state (.base (.ADDI .x6 .x0 1)) = some (cursorEntry state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      cursorEntry, pc, show state.getReg .x0 = 0#64 from rfl]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

end TwoPermutationPrototype.QOpening
