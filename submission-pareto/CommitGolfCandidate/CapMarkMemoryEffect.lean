import CommitGolfCandidate.CapMarkState

/-! The actual mark store reads the two original child words and changes exactly
the parent word. This projection lets the pure descending invariant apply
without equating the deliberately changed scratch registers or branch PC. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

private theorem zero_offset (address : Word) :
    address + signExtend12 (0 : BitVec 12) = address := by
  simp [signExtend12]

private theorem before_read (marks : Reg) (state : MachineState) (count : Nat)
    (bounded : count ≤ 7) (address : Word) :
    (capMarkPrefix marks state count).getMem address = state.getMem address :=
  congrFun (cap_mark_prefix_memory marks state count bounded) address

theorem cap_mark_data_register (marks : Reg) (state : MachineState) (node : Nat)
    (selected : CapMarksRegister marks) (base : state.getReg marks = 28672)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) :
    (capMarkPrefix marks state 7).getReg .x6 =
      state.getMem (capMarkAddress (2 * node)) |||
        state.getMem (capMarkAddress (2 * node + 1)) := by
  have left : (capMarkPrefix marks state 3).getReg .x6 =
      state.getMem (capMarkAddress (2 * node)) := by
    rw [cap_mark_prefix_succ marks state 2 (by omega)]
    simp (disch := decide) only [capMarkInstructions, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, zero_offset]
    rw [cap_mark_source_register marks state node selected base index]
    exact before_read marks state 2 (by omega) _
  have right : (capMarkPrefix marks state 4).getReg .x7 =
      state.getMem (capMarkAddress (2 * node + 1)) := by
    rw [cap_mark_prefix_succ marks state 3 (by omega)]
    simp (disch := decide) only [capMarkInstructions, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      show signExtend12 (8 : BitVec 12) = (8 : Word) by decide]
    rw [cap_mark_right_register marks state node selected base index]
    exact before_read marks state 3 (by omega) _
  have left4 : (capMarkPrefix marks state 4).getReg .x6 =
      state.getMem (capMarkAddress (2 * node)) := by
    rw [cap_mark_prefix_succ marks state 3 (by omega)]
    simpa (disch := decide) only [capMarkInstructions, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_ne] using left
  have combined : (capMarkPrefix marks state 5).getReg .x6 =
      state.getMem (capMarkAddress (2 * node)) |||
        state.getMem (capMarkAddress (2 * node + 1)) := by
    rw [cap_mark_prefix_succ marks state 4 (by omega)]
    simp (disch := decide) only [capMarkInstructions, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, left4, right]
  rw [cap_mark_prefix_succ marks state 6 (by omega)]
  simp (disch := decide) only [capMarkInstructions, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, execInstrBr,
    MachineState.getReg_setPC, MachineState.getReg_setReg_ne]
  rw [cap_mark_prefix_succ marks state 5 (by omega)]
  simpa (disch := decide) only [capMarkInstructions, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, execInstrBr,
    MachineState.getReg_setPC, MachineState.getReg_setReg_ne] using combined

private theorem suffix_memory (state : MachineState) (offset : BitVec 13) :
    (execInstrBr (execInstrBr (execInstrBr state (.SD .x23 .x6 0))
      (.ADDI .x20 .x20 4095)) (.BNE .x20 .x0 offset)).mem =
        (state.setMem (state.getReg .x23) (state.getReg .x6)).mem := by
  have branch (current : MachineState) :
      (execInstrBr current (.BNE .x20 .x0 offset)).mem = current.mem := by
    simp only [execInstrBr]
    split <;> simp only [MachineState.setPC]
  rw [branch]
  simp only [execInstrBr, MachineState.setPC, MachineState.setReg, zero_offset]

theorem cap_mark_memory_effect (marks : Reg) (state : MachineState) (node : Nat)
    (selected : CapMarksRegister marks) (base : state.getReg marks = 28672)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) :
    (capMarkPrefix marks state 10).mem = (capMarkWrite state node).mem := by
  have suffix : (capMarkPrefix marks state 10).mem =
      ((capMarkPrefix marks state 7).setMem
        ((capMarkPrefix marks state 7).getReg .x23)
        ((capMarkPrefix marks state 7).getReg .x6)).mem := by
    rw [cap_mark_prefix_succ marks state 9 (by omega),
      cap_mark_prefix_succ marks state 8 (by omega),
      cap_mark_prefix_succ marks state 7 (by omega)]
    simp only [capMarkInstructions, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    exact suffix_memory (capMarkPrefix marks state 7) _
  rw [suffix, cap_mark_parent_register marks state node selected base index,
    cap_mark_data_register marks state node selected base index]
  simp only [MachineState.setMem, capMarkWrite,
    cap_mark_prefix_memory marks state 7 (by omega)]

end CommitGolfCandidate
