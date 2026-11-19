import CommitGolfCandidate.TwoPermutationOpeningMarkSweep

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64

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
    (bounded : node < 256) (otherBound : other < 512) (pc : state.pc = 0x10b4)
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
    (pc : state.pc = if remaining = 0 then 0x10dc else 0x10b4)
    (base : state.getReg .x26 = BitVec.ofNat 64 markBase)
    (count : state.getReg .x6 = BitVec.ofNat 64 remaining)
    (finished : ∀ node, remaining < node → node < 512 →
      machineMarks state node = markWord groups node) :
    ∀ node, 0 < node → node < 512 →
      machineMarks (markMachine state remaining) node = markWord groups node := by
  induction remaining generalizing state with
  | zero => exact finished
  | succ remaining ih =>
    have headPC : state.pc = 0x10b4 := by simpa using pc
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

end TwoPermutationPrototype.Opening
