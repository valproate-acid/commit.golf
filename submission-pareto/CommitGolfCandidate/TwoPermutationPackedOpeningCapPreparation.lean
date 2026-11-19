import CommitGolfCandidate.TwoPermutationPackedOpeningMark
import CommitGolfCandidate.TwoPermutationPackedOpeningCapMoves

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

open Opening (markParentPrefix markMachine markBase machineMarks markParent mark_addresses
  markWord mark_word_parent nat_address_injective capMarkInstructions)

attribute [local irreducible] markParentPrefix
set_option maxRecDepth 4096

private theorem observed_mark_update (before after : MachineState) (node other : Nat)
    (bounded : node < 256) (otherBound : other < 512)
    (memory : after.mem = (before.setMem (BitVec.ofNat 64 (markBase + 8 * node))
      (machineMarks before (2 * node) ||| machineMarks before (2 * node + 1))).mem) :
    machineMarks after other = markParent (machineMarks before) node other := by
  have point := congrFun memory (BitVec.ofNat 64 (markBase + 8 * other))
  unfold machineMarks at *
  refine point.trans ?_
  by_cases same : other = node
  · subst other
    simp [markParent, MachineState.setMem, MachineState.getMem]
  · have different : BitVec.ofNat 64 (markBase + 8 * other) ≠
        BitVec.ofNat 64 (markBase + 8 * node) := by
      intro equal
      unfold markBase at equal
      have := nat_address_injective (by omega) (by omega) equal
      omega
    simp [markParent, same, MachineState.setMem, MachineState.getMem, different]

/-- In physical memory, one mark iteration implements the corresponding array update. -/
theorem machine_mark_parent (state : MachineState) (node other : Nat)
    (bounded : node < 256) (otherBound : other < 512) (pc : state.pc = 0x1970)
    (base : state.getReg .x26 = BitVec.ofNat 64 markBase)
    (count : state.getReg .x6 = BitVec.ofNat 64 node) :
    machineMarks (markParentPrefix state 10) other = markParent (machineMarks state) node other := by
  have ⟨left, right, parent⟩ := mark_addresses state node base count
  have memory := (mark_parent_post state pc).1
  rw [right, left, parent] at memory
  exact observed_mark_update state _ node other bounded otherBound memory

/-- Memory after the complete sweep contains the exact occupancy of every cap subtree. -/
theorem machine_mark_sweep (state : MachineState) (groups : List Nat) (remaining : Nat)
    (bounded : remaining < 256)
    (pc : state.pc = if remaining = 0 then 0x1998 else 0x1970)
    (base : state.getReg .x26 = BitVec.ofNat 64 markBase)
    (count : state.getReg .x6 = BitVec.ofNat 64 remaining)
    (finished : ∀ node, remaining < node → node < 512 →
      machineMarks state node = markWord groups node) :
    ∀ node, 0 < node → node < 512 →
      machineMarks (markMachine state remaining) node = markWord groups node := by
  induction remaining generalizing state with
  | zero => exact finished
  | succ remaining ih =>
    have headPC : state.pc = 0x1970 := by simpa using pc
    have ⟨nextPC, nextCount⟩ := mark_sweep_pc state remaining (by omega) headPC count
    have nextBase := (mark_parent_post state headPC).2.1.trans base
    apply ih _ (by omega) nextPC nextBase nextCount
    intro node after inside
    rw [machine_mark_parent state (remaining+1) node bounded inside headPC base count]
    by_cases same : node = remaining + 1
    · subst node
      have children := mark_word_parent groups ⟨remaining + 1, bounded⟩
        (show 0 < remaining + 1 by omega)
      change markWord groups (remaining + 1) =
        markWord groups (2 * (remaining + 1)) ||| markWord groups (2 * (remaining + 1) + 1) at children
      rw [markParent, ite_eq_left rfl, finished _ (by omega) (by omega),
        finished _ (by omega) (by omega), children]
    · rw [markParent, ite_eq_right same, finished _ (by omega) inside]

def markSweepEntry (state : MachineState) : MachineState :=
  (state.setReg .x6 255).setPC 0x1970

def cursorEntry (state : MachineState) : MachineState :=
  (state.setReg .x6 1).setPC 0x199c

/-- Enter the descending sweep at parent 255, immediately after the last record. -/
theorem execute_mark_entry (state : MachineState) (pc : state.pc = 0x196c)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (1 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (markSweepEntry state) allowCoins
          return result.charge 1 0) := by
  have fetched := packed_fetch_base state 603 (.ADDI .x6 .x0 255) (by decide) pc rfl
  have stepped : ordinaryStep state (.base (.ADDI .x6 .x0 255)) = some (markSweepEntry state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      markSweepEntry, pc, show state.getReg .x0 = 0#64 from rfl]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

/-- Start the cap cursor at the root after all parent marks are set. -/
theorem execute_cursor_entry (state : MachineState) (pc : state.pc = 0x1998)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (1 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (cursorEntry state) allowCoins
          return result.charge 1 0) := by
  have fetched := packed_fetch_base state 614 (.ADDI .x6 .x0 1) (by decide) pc rfl
  have stepped : ordinaryStep state (.base (.ADDI .x6 .x0 1)) = some (cursorEntry state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      cursorEntry, pc, show state.getReg .x0 = 0#64 from rfl]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem

@[local simp] private theorem prep_reg_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

private theorem mark_parent_register (state : MachineState) (reg : Reg)
    (a : reg ≠ .x6) (b : reg ≠ .x7) (c : reg ≠ .x28) (d : reg ≠ .x29) :
    (markParentPrefix state 10).getReg reg = state.getReg reg := by
  by_cases done : state.getReg .x6 + 18446744073709551615#64 = 0#64 <;>
    simp [markParentPrefix, capMarkInstructions, execInstrBr, signExtend12, done,
      Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d]

attribute [local irreducible] execute

private theorem mark_sweep_register (state : MachineState) (remaining : Nat) (reg : Reg)
    (a : reg ≠ .x6) (b : reg ≠ .x7) (c : reg ≠ .x28) (d : reg ≠ .x29) :
    (markMachine state remaining).getReg reg = state.getReg reg := by
  induction remaining generalizing state with
  | zero => rfl
  | succ remaining ih =>
    change (markMachine (markParentPrefix state 10) remaining).getReg reg = _
    exact (ih _).trans (mark_parent_register state reg a b c d)

private theorem mark_sweep_finished (state : MachineState) (remaining : Nat)
    (bounded : remaining < 256)
    (pc : state.pc = if remaining = 0 then 0x1998 else 0x1970)
    (count : state.getReg .x6 = BitVec.ofNat 64 remaining) :
    (markMachine state remaining).pc = 0x1998 := by
  induction remaining generalizing state with
  | zero => simpa [markMachine] using pc
  | succ remaining ih =>
    have incoming : state.pc = 0x1970 := by simpa using pc
    have ⟨next, remainingWord⟩ := mark_sweep_pc state remaining (by omega) incoming count
    exact ih _ (by omega) next remainingWord

def capPreparation (state : MachineState) : MachineState :=
  cursorEntry (markMachine (markSweepEntry state) 255)

/-- Starting one instruction after the final record, prepare all subtree marks
and enter the real cursor at node one in 2,552 cycles. -/
theorem execute_cap_preparation (state : MachineState) (pc : state.pc = 0x196c)
    (base : state.getReg .x26 = BitVec.ofNat 64 markBase) (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (2552 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (capPreparation state) allowCoins
          return result.charge 2552 0) := by
  let first := markSweepEntry state
  have baseAtSweep : first.getReg .x26 = BitVec.ofNat 64 markBase := base
  have count : first.getReg .x6 = BitVec.ofNat 64 255 := rfl
  have markEntry := execute_mark_entry state pc (2551 + fuel) allowCoins
  have sweep := execute_mark_sweep first 255 (1+fuel) allowCoins (by decide) rfl baseAtSweep count
  have beforeCursor := mark_sweep_finished first 255 (by decide) rfl count
  have walkEntry := execute_cursor_entry _ beforeCursor fuel allowCoins
  rw [show 2552 + fuel = 1 + (2551 + fuel) by omega, markEntry,
    show 2551 + fuel = 10 * 255 + (1 + fuel) by omega, sweep, walkEntry]
  simp [capPreparation, Execution.charge, ← Nat.add_assoc, first]

/-- The packed cap enters the exact traversal with the same marks, heap and output cursor. -/
theorem cap_preparation_context (state : MachineState) (groups : List Nat) (dest : Nat)
    (markBaseReg : state.getReg .x26 = BitVec.ofNat 64 markBase)
    (heap : state.getReg .x25 = BitVec.ofNat 64 Opening.trapdoorBase)
    (leaves : state.getReg .x27 = 256#64)
    (proofStart : state.getReg .x20 = BitVec.ofNat 64 Opening.proofBase)
    (pointer : state.getReg .x21 = BitVec.ofNat 64 dest)
    (marks : ∀ node, 255 < node → node < 512 → machineMarks state node = markWord groups node) :
    let after := capPreparation state
    after.pc = 0x199c ∧ CapPosition groups after 1 dest := by
  let first := markSweepEntry state
  have count : first.getReg .x6 = BitVec.ofNat 64 255 := rfl
  have baseAtSweep : first.getReg .x26 = BitVec.ofNat 64 markBase := markBaseReg
  have preserve (reg : Reg) (a : reg ≠ .x6) (b : reg ≠ .x7) (c : reg ≠ .x28) (d : reg ≠ .x29) :
      (capPreparation state).getReg reg = state.getReg reg := by
    unfold capPreparation cursorEntry
    simp only [MachineState.getReg_setPC, Opening.getReg_setReg, Ne.symm a, false_and, ite_false]
    rw [mark_sweep_register _ _ reg a b c d]
    unfold markSweepEntry
    simp [Ne.symm a]
  refine ⟨rfl, ⟨⟨(preserve .x25 (by decide) (by decide) (by decide) (by decide)).trans heap,
      (preserve .x26 (by decide) (by decide) (by decide) (by decide)).trans markBaseReg,
      (preserve .x27 (by decide) (by decide) (by decide) (by decide)).trans leaves,
      (preserve .x20 (by decide) (by decide) (by decide) (by decide)).trans proofStart, ?_⟩, rfl,
    (preserve .x21 (by decide) (by decide) (by decide) (by decide)).trans pointer⟩⟩
  intro node positive inside
  change machineMarks (markMachine first 255) node = markWord groups node
  exact machine_mark_sweep first groups 255 (by decide) rfl baseAtSweep count marks node positive inside

end TwoPermutationPrototype.PackedOpening
