import CommitGolfCandidate.CapMemoryFrame

/-! Instruction bridges used by the descending occupancy pass. The fetch premise
ties each step to an actual image. Normal range/alignment checks remain required
at each store; memory framing does not replace those machine checks. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def capMarkOrState (state : MachineState) : MachineState :=
  (state.setReg .x6 (state.getReg .x6 ||| state.getReg .x7)).setPC (state.pc + 4)

theorem cap_mark_or_step (image : Image) (state : MachineState) (fuel : Nat)
    (allowCoins : Bool)
    (fetched : fetch image state = some (.base (.OR .x6 .x6 .x7))) :
    execute image (1 + fuel) state allowCoins =
      (do let result ← execute image fuel (capMarkOrState state) allowCoins
          return result.charge 1 0) := by
  have stepped : ordinaryStep state (.base (.OR .x6 .x6 .x7)) =
      some (capMarkOrState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, capMarkOrState]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

theorem cap_mark_or_frame (state reference : MachineState)
    (frame : CapHighBytes state reference) :
    CapHighBytes (capMarkOrState state) reference :=
  cap_high_bytes_memory state _ reference rfl frame

def capMarkStoreState (state : MachineState) : MachineState :=
  (state.setMem (state.getReg .x23) (state.getReg .x6)).setPC (state.pc + 4)

theorem cap_mark_store_step (image : Image) (state : MachineState) (fuel : Nat)
    (allowCoins : Bool)
    (fetched : fetch image state = some (.base (.SD .x23 .x6 0)))
    (valid : accessValid (state.getReg .x23) 8 = true) :
    execute image (1 + fuel) state allowCoins =
      (do let result ← execute image fuel (capMarkStoreState state) allowCoins
          return result.charge 1 0) := by
  have stepped : ordinaryStep state (.base (.SD .x23 .x6 0)) =
      some (capMarkStoreState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      valid, capMarkStoreState]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

theorem cap_mark_store_frame (state reference : MachineState)
    (low : (state.getReg .x23).toNat < 32768) (frame : CapHighBytes state reference) :
    CapHighBytes (capMarkStoreState state) reference := by
  apply cap_high_bytes_memory
    (state.setMem (state.getReg .x23) (state.getReg .x6)) _ reference rfl
  have preserved := cap_high_bytes_store state reference
    (state.getReg .x23).toNat (state.getReg .x6) low frame
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using preserved
end CommitGolfCandidate
