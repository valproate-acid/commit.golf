import CommitGolfCandidate.CapMarkStep
import CommitGolfCandidate.CapMarkAlgebra

/-! Register/address specialization of the generic mark iteration. Opening uses
x22 for the mark base; checking uses x9. Both survive all scratch writes. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def CapMarksRegister (marks : Reg) : Prop := marks = .x9 ∨ marks = .x22

theorem cap_marks_register_outside (marks : Reg) (selected : CapMarksRegister marks) :
    marks ≠ .x6 ∧ marks ≠ .x7 ∧ marks ≠ .x20 ∧ marks ≠ .x23 ∧ marks ≠ .x30 := by
  rcases selected with rfl | rfl <;> decide

theorem cap_mark_source_register (marks : Reg) (state : MachineState) (node : Nat)
    (selected : CapMarksRegister marks) (base : state.getReg marks = 28672)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) :
    (capMarkPrefix marks state 2).getReg .x30 = capMarkAddress (2 * node) := by
  rcases selected with rfl | rfl <;>
    simp (disch := decide) only [capMarkPrefix, capMarkInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, base, index,
      show (4 : BitVec 6).toNat = 4 by decide] <;>
    exact cap_mark_child_pointer node

theorem cap_mark_right_register (marks : Reg) (state : MachineState) (node : Nat)
    (selected : CapMarksRegister marks) (base : state.getReg marks = 28672)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) :
    (capMarkPrefix marks state 3).getReg .x30 + 8 = capMarkAddress (2 * node + 1) := by
  rw [cap_mark_prefix_succ marks state 2 (by omega)]
  simp (disch := decide) only [capMarkInstructions, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne]
  rw [cap_mark_source_register marks state node selected base index]
  exact cap_mark_right_pointer node

theorem cap_mark_parent_register (marks : Reg) (state : MachineState) (node : Nat)
    (selected : CapMarksRegister marks) (base : state.getReg marks = 28672)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) :
    (capMarkPrefix marks state 7).getReg .x23 = capMarkAddress node := by
  have unchanged := cap_mark_prefix_register marks state 6 (by omega) marks
    (cap_marks_register_outside marks selected)
  rw [cap_mark_prefix_succ marks state 6 (by omega)]
  simp (disch := decide) only [capMarkInstructions, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq, unchanged, base]
  have shifted : (capMarkPrefix marks state 6).getReg .x23 =
      BitVec.ofNat 64 node <<< 3 := by
    rcases selected with rfl | rfl <;>
      simp (disch := decide) only [capMarkPrefix, capMarkInstructions, List.take, List.foldl, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne, index,
        show (3 : BitVec 6).toNat = 3 by decide]
  rw [shifted]
  exact cap_mark_parent_pointer node

/-- Natural child and parent bounds discharge the three actual access premises. -/
theorem cap_mark_access (marks : Reg) (state : MachineState) (leaves node : Nat)
    (selected : CapMarksRegister marks) (base : state.getReg marks = 28672)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (bounded : leaves ≤ 256) (internal : node < leaves) :
    accessValid ((capMarkPrefix marks state 2).getReg .x30) 8 = true ∧
    accessValid ((capMarkPrefix marks state 3).getReg .x30 + 8) 8 = true ∧
    accessValid ((capMarkPrefix marks state 7).getReg .x23) 8 = true ∧
      ((capMarkPrefix marks state 7).getReg .x23).toNat < 32768 := by
  rw [cap_mark_source_register marks state node selected base index,
    cap_mark_right_register marks state node selected base index,
    cap_mark_parent_register marks state node selected base index]
  exact ⟨(cap_mark_address_valid leaves (2 * node) bounded (by omega)).1,
    (cap_mark_address_valid leaves (2 * node + 1) bounded (by omega)).1,
    cap_mark_address_valid leaves node bounded (by omega)⟩

end CommitGolfCandidate
