import CommitGolfCandidate.TwoPermutationPackedCapMarkFrame

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC
attribute [local irreducible] markMachine

@[local simp] private theorem set_pc_field (state : MachineState) (pc : Word) : (state.setPC pc).pc = pc := rfl
@[local simp] private theorem zero_register (state : MachineState) : state.getReg .x0 = 0#64 := rfl

private theorem cap_start_stamp (state : MachineState) :
    (capStart state).pc = state.pc+12#64 ∧ (capStart state).getReg .x6 = 1#64 ∧
    (capStart state).getReg .x11 = 64#64 ∧ (capStart state).getReg .x13 = 0#64 := by
  simp [capStart, blockPrefix, capStartCode, execInstrBr, signExtend12, BitVec.add_assoc]
  <;> rfl

theorem started_cap_register (state : MachineState) (reg : Reg)
    (a : reg ≠ .x6) (b : reg ≠ .x7) (c : reg ≠ .x28) (d : reg ≠ .x29)
    (size : reg ≠ .x11) (kind : reg ≠ .x13) :
    (startedCap state).getReg reg = state.getReg reg := by
  have cap_preserves (s : MachineState) : (capStart s).getReg reg = s.getReg reg := by
    simp [capStart, blockPrefix, capStartCode, execInstrBr, Ne.symm a, Ne.symm size, Ne.symm kind]
  rw [startedCap, cap_preserves, mark_sweep_register _ _ reg a b c d]
  simp [startMark, Ne.symm a]

theorem started_cap_fixed (state : MachineState) :
    (startedCap state).pc = 0x147c ∧ (startedCap state).getReg .x6 = 1#64 ∧
      (startedCap state).getReg .x11 = 64#64 ∧ (startedCap state).getReg .x13 = 0#64 := by
  have pc := mark_machine_pc (startMark state) 255 (by decide) rfl rfl
  obtain ⟨next, node, size, kind⟩ := cap_start_stamp (markMachine (startMark state) 255)
  exact ⟨next.trans (congrArg (· + 12#64) pc), node, size, kind⟩

theorem started_cap_mark (state : MachineState) (groups : List Nat)
    (base : state.getReg .x26 = BitVec.ofNat 64 Opening.markBase)
    (leaves : ∀ node, 256 ≤ node → node < 512 → machineMarks state node = Opening.markWord groups node)
    (node : Nat) (positive : 0 < node) (bounded : node < 512) :
    machineMarks (startedCap state) node = Opening.markWord groups node := by
  unfold startedCap
  rw [show ∀ next : MachineState, machineMarks (capStart next) node = machineMarks next node from
    fun _ => rfl]
  exact machine_mark_sweep (startMark state) groups 255 (by decide) rfl base rfl
    (fun n lower upper => leaves n (by omega) upper) node positive bounded

theorem started_cap_word (state : MachineState)
    (base : state.getReg .x26 = BitVec.ofNat 64 Opening.markBase)
    (word : Nat) (bound : word < 2^61) (outside : word < 513 ∨ 768 ≤ word) :
    memoryView (startedCap state) word = memoryView state word := by
  unfold startedCap
  rw [show ∀ next : MachineState, memoryView (capStart next) word = memoryView next word from fun _ => rfl]
  rw [show memoryView state word = memoryView (startMark state) word from rfl]
  exact mark_sweep_word (startMark state) 255 (by decide) rfl base rfl word bound outside

end TwoPermutationPrototype.Packed.Checker
