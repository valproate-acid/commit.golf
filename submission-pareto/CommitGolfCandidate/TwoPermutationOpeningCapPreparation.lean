import CommitGolfCandidate.TwoPermutationOpeningRecordGroups

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.Sampling
  RiscvZkvm.Rv64 OracleComp

attribute [local simp] getReg_setReg getReg_setMem

@[local simp] private theorem prep_reg_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

private theorem mark_parent_register (state : MachineState) (reg : Reg)
    (a : reg ≠ .x6) (b : reg ≠ .x7) (c : reg ≠ .x28) (d : reg ≠ .x29) :
    (markParentPrefix state 10).getReg reg = state.getReg reg := by
  by_cases done : state.getReg .x6 + 18446744073709551615#64 = 0#64 <;>
    simp [markParentPrefix, capMarkInstructions, execInstrBr, signExtend12, done,
      Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d]

attribute [local irreducible] markParentPrefix execute

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
    (pc : state.pc = if remaining = 0 then 0x10dc else 0x10b4)
    (count : state.getReg .x6 = BitVec.ofNat 64 remaining) :
    (markMachine state remaining).pc = 0x10dc := by
  induction remaining generalizing state with
  | zero => simpa [markMachine] using pc
  | succ remaining ih =>
    have incoming : state.pc = 0x10b4 := by simpa using pc
    have ⟨next, remainingWord⟩ := mark_sweep_pc state remaining (by omega) incoming count
    exact ih _ (by omega) next remainingWord

structure CapContext (groups : List Nat) (state : MachineState) : Prop where
  heap : state.getReg .x25 = BitVec.ofNat 64 trapdoorBase
  markBaseWord : state.getReg .x26 = BitVec.ofNat 64 markBase
  capLeavesWord : state.getReg .x27 = 256#64
  proofStart : state.getReg .x20 = BitVec.ofNat 64 proofBase
  markValue : ∀ node, 0 < node → node < 512 → machineMarks state node = markWord groups node

def capPreparation (state : MachineState) : MachineState :=
  cursorEntry (markMachine (markSweepEntry state) 255)

/-- Starting one instruction after the final record, prepare all subtree marks
and enter the real cursor at node one in 2,552 cycles. -/
theorem execute_cap_preparation (state : MachineState) (pc : state.pc = 0x10b0)
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

/-- The concrete prepared cap starts at the root with every mark populated by the
same grouping as the transcript. -/
theorem cap_preparation_context (s : Submission) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) (state : MachineState)
    (boundary : RecordBoundary s trapdoor positions state positions.card)
    (marks : RecordMarks positions state positions.card) :
    let after := capPreparation state
    after.pc = 0x10e0 ∧ after.getReg .x6 = 1#64 ∧
    after.getReg .x21 = BitVec.ofNat 64 (recordBase positions.card) ∧
    CapContext (groupsBefore positions positions.card) after := by
  let first := markSweepEntry state
  let groups := groupsBefore positions positions.card
  have count : first.getReg .x6 = BitVec.ofNat 64 255 := rfl
  have baseAtSweep : first.getReg .x26 = BitVec.ofNat 64 markBase := boundary.marks
  have preserve (reg : Reg) (a : reg ≠ .x6) (b : reg ≠ .x7) (c : reg ≠ .x28) (d : reg ≠ .x29) :
      (capPreparation state).getReg reg = state.getReg reg := by
    unfold capPreparation cursorEntry
    simp only [MachineState.getReg_setPC, getReg_setReg, Ne.symm a, false_and, ite_false]
    rw [mark_sweep_register _ _ reg a b c d]
    unfold markSweepEntry
    simp [Ne.symm a]
  refine ⟨rfl, rfl, (preserve .x21 (by decide) (by decide) (by decide) (by decide)).trans boundary.dest,
    ⟨(preserve .x25 (by decide) (by decide) (by decide) (by decide)).trans boundary.capHeap,
     (preserve .x26 (by decide) (by decide) (by decide) (by decide)).trans boundary.marks,
     (preserve .x27 (by decide) (by decide) (by decide) (by decide)).trans boundary.capLeaves,
     (preserve .x20 (by decide) (by decide) (by decide) (by decide)).trans boundary.proofBegin, ?_⟩⟩
  have initial (node : Nat) (leaf : 255 < node) (inside : node < 512) :
      machineMarks first node = markWord groups node := by
    change machineMarks state node = markWord groups node
    rw [marks node inside]
    exact (mark_word_leaf groups ⟨node, inside⟩ (show 256 ≤ node by omega)).symm
  intro node positive inside
  change machineMarks (markMachine first 255) node = markWord groups node
  exact machine_mark_sweep first groups 255 (by decide) rfl baseAtSweep count initial node positive inside

end TwoPermutationPrototype.Opening
