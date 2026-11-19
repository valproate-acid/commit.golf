import CommitGolfCandidate.CapMarkState

/-! Observable effects of one real occupancy iteration. Memory agrees with the
pure parent store, while the actual counter and branch PC are retained as
separate projections. Scratch registers are intentionally not equated. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_mark_before_counter (marks : Reg) (state : MachineState) (count : Nat)
    (bounded : count ≤ 8) :
    (capMarkPrefix marks state count).getReg .x20 = state.getReg .x20 := by
  have step (current : MachineState) (i : Nat) (hi : i < 8) :
      (execInstrBr current (((capMarkInstructions marks)[i]?).getD .EBREAK)).getReg .x20 =
        current.getReg .x20 := by
    interval_cases i <;>
      simp (disch := decide) only [capMarkInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some, execInstrBr,
        MachineState.getReg_setPC, MachineState.getReg_setReg_ne]
    rfl
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [cap_mark_prefix_succ marks state count (by omega), step _ count (by omega)]
      exact ih (by omega)

theorem cap_mark_prefix_pc (marks : Reg) (state : MachineState) (count : Nat)
    (bounded : count ≤ 9) :
    (capMarkPrefix marks state count).pc = state.pc + BitVec.ofNat 64 (4 * count) := by
  have step (current : MachineState) (i : Nat) (hi : i < 9) :
      (execInstrBr current (((capMarkInstructions marks)[i]?).getD .EBREAK)).pc =
        current.pc + 4 := by
    interval_cases i <;> rfl
  induction count with
  | zero => simp [capMarkPrefix]
  | succ count ih =>
      rw [cap_mark_prefix_succ marks state count (by omega), step _ count (by omega),
        ih (by omega)]
      rw [show 4 * (count + 1) = 4 * count + 4 by omega, BitVec.ofNat_add]
      exact BitVec.add_assoc _ _ _

theorem cap_mark_counter (marks : Reg) (state : MachineState) (node : Nat)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) (positive : 0 < node) :
    (capMarkPrefix marks state 10).getReg .x20 = BitVec.ofNat 64 (node - 1) := by
  rw [cap_mark_prefix_succ marks state 9 (by omega)]
  simp only [capMarkInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, execInstrBr]
  split <;> rw [MachineState.getReg_setPC]
  all_goals
    rw [cap_mark_prefix_succ marks state 8 (by omega)]
    simp (disch := decide) only [capMarkInstructions, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq]
    rw [cap_mark_before_counter marks state 8 (by omega), index]
    exact cap_mark_decrement node positive

theorem cap_mark_latch_pc (marks : Reg) (state : MachineState) (start : Word)
    (node : Nat) (pc : state.pc = start)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (positive : 0 < node) (bounded : node < 256) :
    (capMarkPrefix marks state 10).pc = if node = 1 then start + 40 else start := by
  have counter : (capMarkPrefix marks state 9).getReg .x20 =
      BitVec.ofNat 64 (node - 1) := by
    rw [cap_mark_prefix_succ marks state 8 (by omega)]
    simp (disch := decide) only [capMarkInstructions, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq]
    rw [cap_mark_before_counter marks state 8 (by omega), index]
    exact cap_mark_decrement node positive
  rw [cap_mark_prefix_succ marks state 9 (by omega)]
  simp only [capMarkInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, execInstrBr, counter, cap_mark_prefix_pc marks state 9 (by omega), pc]
  have zero : (capMarkPrefix marks state 9).getReg .x0 = 0 := by
    rfl
  rw [zero]
  have forty : start + 36 + 4 = start + 40 := by
    rw [BitVec.add_assoc]
    rfl
  by_cases last : node = 1
  · subst node
    simp only [Nat.sub_self, show BitVec.ofNat 64 0 = (0 : Word) by rfl,
      bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true, MachineState.setPC]
    exact forty
  · have nonzero : BitVec.ofNat 64 (node - 1) ≠ 0 :=
      fun equal => last ((cap_mark_last_iff node positive bounded).mp equal)
    rw [ite_eq_left (bne_iff_ne.mpr nonzero)]
    simp only [MachineState.setPC, last, ite_false]
    exact cap_mark_back_pc start

end CommitGolfCandidate
