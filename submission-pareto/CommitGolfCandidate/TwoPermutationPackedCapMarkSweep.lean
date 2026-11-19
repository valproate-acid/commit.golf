import CommitGolfCandidate.TwoPermutationPackedCapMarks
import CommitGolfCandidate.TwoPermutationPackedCapAdvance
import CommitGolfCandidate.TwoPermutationOpeningMarkContents

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Opening hiding markParentPrefix execute_mark_parent mark_parent_post
  mark_sweep_pc markMachine machineMarks machine_mark_parent

attribute [local irreducible] execute markParentPrefix
set_option maxRecDepth 4096

def machineMarks (state : MachineState) (node : Nat) : Word :=
  state.getMem (BitVec.ofNat 64 (markBase + 8 * node))

def markMachine (state : MachineState) : Nat → MachineState
  | 0 => state
  | remaining + 1 => markMachine (markParentPrefix state 10) remaining

theorem mark_sweep_pc (state : MachineState) (remaining : Nat) (within : remaining < 256)
    (pc : state.pc = 0x1448)
    (count : state.getReg .x6 = BitVec.ofNat 64 (remaining + 1)) :
    (markParentPrefix state 10).pc = (if remaining = 0 then 0x1470 else 0x1448) ∧
      (markParentPrefix state 10).getReg .x6 = BitVec.ofNat 64 remaining := by
  have decrease : state.getReg .x6 - 1 = BitVec.ofNat 64 remaining := by
    rw [count]
    change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by decide) (by omega)]
    rw [Nat.add_sub_cancel]
  have zero : BitVec.ofNat 64 remaining = 0#64 ↔ remaining = 0 := by
    constructor
    · intro h
      exact nat_address_injective (left := remaining) (right := 0) (by omega) (by decide) h
    · rintro rfl
      rfl
  exact ⟨by rw [(mark_parent_post state pc).2.2.2, decrease]; simp [zero],
    (mark_parent_post state pc).2.2.1.trans decrease⟩

private theorem mark_cell_access (node : Nat) (bounded : node < 512) :
    accessValid (BitVec.ofNat 64 (markBase + 8 * node)) 8 = true := by
  apply Opening.aligned_access
  · unfold markBase
    omega
  · unfold markBase MEMORY_BYTES
    omega

/-- Execute the actual entire descending sweep, accounting for every iteration. -/
theorem execute_mark_sweep (state : MachineState) (remaining fuel : Nat)
    (bounded : remaining < 256)
    (pc : state.pc = if remaining = 0 then 0x1470 else 0x1448)
    (base : state.getReg .x26 = BitVec.ofNat 64 markBase)
    (count : state.getReg .x6 = BitVec.ofNat 64 remaining) :
    execute packedImage (10 * remaining + fuel) state false =
      (do let result ← execute packedImage fuel (markMachine state remaining) false
          return result.charge (10 * remaining) 0) := by
  induction remaining generalizing state with
  | zero => simp [markMachine, Execution.charge]
  | succ remaining ih =>
    have headPC : state.pc = 0x1448 := by simpa using pc
    have ⟨left, right, parent⟩ := mark_addresses state (remaining + 1) base count
    change childrenAddress state = _ at left
    change childrenAddress state + 8#64 = _ at right
    change parentAddress state = _ at parent
    have leftValid : accessValid (childrenAddress state) 8 = true := by
      rw [left]
      exact mark_cell_access _ (by omega)
    have rightValid : accessValid (childrenAddress state + 8#64) 8 = true := by
      rw [right]
      exact mark_cell_access _ (by omega)
    have parentValid : accessValid (parentAddress state) 8 = true := by
      rw [parent]
      exact mark_cell_access _ (by omega)
    have head := execute_mark_parent state headPC (10 * remaining + fuel)
      leftValid rightValid parentValid
    have ⟨nextPC, nextCount⟩ := mark_sweep_pc state remaining (by omega) headPC count
    have nextBase := (mark_parent_post state headPC).2.1.trans base
    rw [show 10 * (remaining + 1) + fuel = 10 + (10 * remaining + fuel) by omega, head,
      ih _ (by omega) nextPC nextBase nextCount]
    simp [markMachine, Execution.charge, Nat.add_assoc, Nat.mul_succ, Nat.add_comm 10]

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
    (bounded : node < 256) (otherBound : other < 512) (pc : state.pc = 0x1448)
    (base : state.getReg .x26 = BitVec.ofNat 64 markBase)
    (count : state.getReg .x6 = BitVec.ofNat 64 node) :
    machineMarks (markParentPrefix state 10) other = markParent (machineMarks state) node other := by
  have ⟨left, right, parent⟩ := mark_addresses state node base count
  change childrenAddress state = _ at left
  change childrenAddress state + 8#64 = _ at right
  change parentAddress state = _ at parent
  have memory := (mark_parent_post state pc).1
  rw [right, left, parent] at memory
  exact observed_mark_update state _ node other bounded otherBound memory

/-- Memory after the complete sweep contains the exact occupancy of every cap subtree. -/
theorem machine_mark_sweep (state : MachineState) (groups : List Nat) (remaining : Nat)
    (bounded : remaining < 256)
    (pc : state.pc = if remaining = 0 then 0x1470 else 0x1448)
    (base : state.getReg .x26 = BitVec.ofNat 64 markBase)
    (count : state.getReg .x6 = BitVec.ofNat 64 remaining)
    (finished : ∀ node, remaining < node → node < 512 →
      machineMarks state node = markWord groups node) :
    ∀ node, 0 < node → node < 512 →
      machineMarks (markMachine state remaining) node = markWord groups node := by
  induction remaining generalizing state with
  | zero => exact finished
  | succ remaining ih =>
    have headPC : state.pc = 0x1448 := by simpa using pc
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

def startMark (state : MachineState) : MachineState :=
  (state.setReg .x6 255).setPC 0x1448

theorem execute_start_mark (state : MachineState) (pc : state.pc = 0x1444) (fuel : Nat) :
    execute packedImage (1+fuel) state false =
      (do let result ← execute packedImage fuel (startMark state) false
          return result.charge 1 0) := by
  have fetched := cap_fetch state 273 (.ADDI .x6 .x0 255) (by decide) pc rfl
  have next : ordinaryStep state (.base (.ADDI .x6 .x0 255)) = some (startMark state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, startMark, pc]
    rfl
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched next]
  rfl

theorem mark_machine_pc (state : MachineState) (remaining : Nat) (bounded : remaining < 256)
    (pc : state.pc = if remaining = 0 then 0x1470 else 0x1448)
    (count : state.getReg .x6 = BitVec.ofNat 64 remaining) :
    (markMachine state remaining).pc = 0x1470 := by
  induction remaining generalizing state with
  | zero => exact pc
  | succ remaining ih =>
    have atLoop : state.pc = 0x1448 := by simpa using pc
    have ⟨tailPC, tailCount⟩ := mark_sweep_pc state remaining (by omega) atLoop count
    exact ih _ (by omega) tailPC tailCount

def startedCap (state : MachineState) := capStart (markMachine (startMark state) 255)

theorem execute_started_cap (state : MachineState) (pc : state.pc = 0x1444) (fuel : Nat)
    (base : state.getReg .x26 = BitVec.ofNat 64 markBase) :
    execute packedImage (2554+fuel) state false =
      (do let result ← execute packedImage fuel (startedCap state) false
          return result.charge 2554 0) := by
  have markPC : (startMark state).pc = 0x1448 := rfl
  have bound : 255 < 256 := by decide
  have count : (startMark state).getReg .x6 = BitVec.ofNat 64 255 := by
    simp [startMark, MachineState.getReg_setPC, Opening.getReg_setReg]
  have markBaseReg : (startMark state).getReg .x26 = BitVec.ofNat 64 markBase := by
    simpa [startMark, MachineState.getReg_setPC, Opening.getReg_setReg] using base
  have tailPC := mark_machine_pc (startMark state) 255 bound markPC count
  rw [show 2554+fuel = 1+(10*255+(3+fuel)) by omega, execute_start_mark state pc,
    execute_mark_sweep (startMark state) 255 _ bound markPC markBaseReg count,
    execute_cap_start _ tailPC]
  simp [startedCap, Execution.charge, ← Nat.add_assoc]

end TwoPermutationPrototype.Packed.Checker
