import CommitGolfCandidate.TwoPermutationCheckerCapFrontier

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64

theorem cap_hash_register (state : MachineState) (parent : Nat) (answer : BitVec 256) (r : Reg)
    (node : r ≠ .x6) (source : r ≠ .x10) (dest : r ≠ .x12) :
    (capHashReply state parent answer).getReg r = state.getReg r := by
  rw [capHashReply, MachineState.getReg_setPC, writeBits_register]
  exact cap_parent_register state r node source dest

private theorem cap_pc_frame (state : MachineState) (pc : Word) (word : Nat) :
    memoryView (state.setPC pc) word = memoryView state word := rfl

attribute [local irreducible] writeBits capParent

theorem cap_hash_frame {state : MachineState} {node : Nat}
    (ready : CapHashReady state node) (answer : BitVec 256) (word : Nat)
    (bound : word < 2^61) (outside : word < 2048+4*(node/2) ∨ 2048+4*(node/2)+4 ≤ word) :
    memoryView (capHashReply state (node/2) answer) word = memoryView state word := by
  have destinationBound := ready.bound
  have mem := (cap_parent_post state ready.pc).2.2.2.2
  rw [capHashReply, cap_pc_frame, write_bits_word_outside _ answer _ _ (by omega) bound (by omega)]
  exact congrFun mem _

theorem frontier_register (state : MachineState) (r : Reg)
    (target : r ≠ .x7) (proof : r ≠ .x21) (endPtr : r ≠ .x28) (temp : r ≠ .x31) :
    (frontierRead state).getReg r = state.getReg r := by
  rw [frontierRead, frontierFinish, MachineState.getReg_setPC, Opening.getReg_setReg,
    ite_eq_right (by simp [Ne.symm proof]), copied_register _ _ _ temp]
  exact frontier_prefix_register state r target endPtr

theorem frontier_read_pointer {state : MachineState} {node proof : Nat}
    (ready : FrontierReady state node proof) :
    (frontierRead state).pc = 0x12e4 ∧ (frontierRead state).getReg .x21 = wordAddress (proof+4) := by
  refine ⟨rfl, ?_⟩
  rw [frontierRead, frontierFinish, MachineState.getReg_setPC, Opening.getReg_setReg,
    ite_eq_left (by decide : Reg.x21 = .x21 ∧ Reg.x21 ≠ .x0),
    copied_register _ _ _ (by decide), frontier_prefix_register _ _ (by decide) (by decide), ready.proofReg]
  exact word_offset proof 4

theorem frontier_read_frame {state : MachineState} {node proof : Nat}
    (ready : FrontierReady state node proof) (word : Nat) (bound : word < 2^61)
    (outside : word < 2048+4*node ∨ 2048+4*node+4 ≤ word) :
    memoryView (frontierRead state) word = memoryView state word := by
  have ⟨src, dest⟩ := frontier_copy_regs ready
  have dst : (frontierPrefix state 4).getReg (copyTarget 176) + BitVec.ofNat 64 (copyOffset 176) =
      wordAddress (2048+4*node) := by
    change (frontierPrefix state 4).getReg .x7 + 0#64 = _
    rw [BitVec.add_zero]
    exact dest
  have room := ready.room
  have above := ready.above
  have below := ready.below
  calc
    _ = memoryView (copied (frontierPrefix state 4) 176) word := rfl
    _ = memoryView (frontierPrefix state 4) word :=
      copied_word_outside _ 176 proof (2048+4*node) word (by unfold CopyBlock; decide) src dst
        (by omega) (by omega) bound (Or.inr (by omega)) outside
    _ = _ := congrFun (frontier_prefix_post state ready.pc).2.2.2 _

end TwoPermutationPrototype.Checker
