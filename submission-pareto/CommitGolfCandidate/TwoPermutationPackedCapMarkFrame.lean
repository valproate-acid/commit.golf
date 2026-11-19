import CommitGolfCandidate.TwoPermutationPackedCapMarkSweep

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC
set_option maxRecDepth 4096

set_option maxHeartbeats 300000 in
theorem mark_parent_register (state : MachineState) (reg : Reg)
    (a : reg ≠ .x6) (b : reg ≠ .x7) (c : reg ≠ .x28) (d : reg ≠ .x29) :
    (markParentPrefix state 10).getReg reg = state.getReg reg := by
  have step (before : MachineState) (i : Fin 10) :
      (execInstrBr before ((Opening.capMarkInstructions.drop 1)[i.val]?.getD .EBREAK)).getReg reg =
        before.getReg reg := by
    fin_cases i
    all_goals simp [Opening.capMarkInstructions, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d]
    by_cases held : before.getReg .x6 = before.getReg .x0 <;> simp [held]
  have keeps (n : Nat) (bound : n ≤ 10) :
      (markParentPrefix state n).getReg reg = state.getReg reg := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [mark_prefix_succ _ n (by omega)]
      exact (step _ ⟨n, by omega⟩).trans (ih (by omega))
  exact keeps 10 (by decide)

attribute [local irreducible] markMachine

set_option maxHeartbeats 300000 in
theorem mark_sweep_register (state : MachineState) (remaining : Nat) (reg : Reg)
    (a : reg ≠ .x6) (b : reg ≠ .x7) (c : reg ≠ .x28) (d : reg ≠ .x29) :
    (markMachine state remaining).getReg reg = state.getReg reg := by
  induction remaining generalizing state with
  | zero => simp [markMachine]
  | succ remaining ih =>
    rw [markMachine]
    change (markMachine (markParentPrefix state 10) remaining).getReg reg = _
    exact (ih (markParentPrefix state 10)).trans (mark_parent_register state reg a b c d)

private theorem mark_parent_address_before_write (state : MachineState) :
    (markParentPrefix state 7).getReg .x7 = parentAddress state := by
  simp [markParentPrefix, parentAddress, Opening.capMarkInstructions, execInstrBr]

set_option maxHeartbeats 600000 in
private theorem mark_parent_keeps_word (state : MachineState) (address : Word)
    (diff : address ≠ parentAddress state) :
    (markParentPrefix state 10).getMem address = state.getMem address := by
  have preserve (step : Nat) (inside : step < 10) :
      (markParentPrefix state (step+1)).getMem address = (markParentPrefix state step).getMem address := by
    rw [mark_prefix_succ _ _ inside]
    interval_cases step
    all_goals simp [Opening.capMarkInstructions, execInstrBr, signExtend12,
      mark_parent_address_before_write, diff]
    all_goals split <;> exact MachineState.getMem_setPC
  have fold (count : Nat) (within : count ≤ 10) :
      (markParentPrefix state count).getMem address = state.getMem address := by
    induction count with
    | zero => rfl
    | succ count ih => exact (preserve count (by omega)).trans (ih (by omega))
  exact fold 10 (by decide)

theorem mark_sweep_getMem (state : MachineState) (remaining : Nat)
    (bounded : remaining < 256) (pc : state.pc = if remaining = 0 then 0x1470 else 0x1448)
    (base : state.getReg .x26 = BitVec.ofNat 64 Opening.markBase)
    (count : state.getReg .x6 = BitVec.ofNat 64 remaining)
    (address : Word) (outside : ∀ node, 0 < node → node < 256 →
      address ≠ BitVec.ofNat 64 (Opening.markBase+8*node)) :
    (markMachine state remaining).getMem address = state.getMem address := by
  induction remaining generalizing state with
  | zero => simp [markMachine]
  | succ remaining ih =>
    have start : state.pc = 0x1448 := by simpa using pc
    have ⟨tailPC, counter⟩ := mark_sweep_pc state remaining (by omega) start count
    obtain ⟨mem, baseReg, _, _⟩ := mark_parent_post state start
    have addressAt := (Opening.mark_addresses state (remaining+1) base count).2.2
    change parentAddress state = _ at addressAt
    have diff : address ≠ parentAddress state :=
      fun same => outside (remaining+1) (by omega) bounded (same.trans addressAt)
    rw [markMachine]
    exact (ih (markParentPrefix state 10) (by omega) tailPC (baseReg.trans base) counter).trans
      (mark_parent_keeps_word state address diff)


theorem mark_sweep_word (state : MachineState) (remaining : Nat)
    (bounded : remaining < 256) (pc : state.pc = if remaining = 0 then 0x1470 else 0x1448)
    (base : state.getReg .x26 = BitVec.ofNat 64 Opening.markBase)
    (count : state.getReg .x6 = BitVec.ofNat 64 remaining)
    (word : Nat) (wordBound : word < 2^61) (outside : word < 513 ∨ 768 ≤ word) :
    memoryView (markMachine state remaining) word = memoryView state word := by
  apply mark_sweep_getMem state remaining bounded pc base count
  intro node low high
  have atNode : BitVec.ofNat 64 (Opening.markBase+8*node) = wordAddress (512+node) := by
    unfold Opening.markBase wordAddress
    congr 1
    omega
  rw [atNode]
  intro same
  have hit := wordAddress_injective_of_bound wordBound (by omega) same
  omega

end TwoPermutationPrototype.Packed.Checker
