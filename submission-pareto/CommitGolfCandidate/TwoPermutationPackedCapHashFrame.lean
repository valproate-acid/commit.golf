import CommitGolfCandidate.TwoPermutationPackedCapHash

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 CommitGolfCandidate.ShortTree
open TwoPermutationPrototype.Checker (write_bits_word_outside)

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
  rw [capHashReply, cap_pc_frame, write_bits_word_outside _ (padLow answer) _ _ (by omega) bound (by omega)]
  exact congrFun mem _

end TwoPermutationPrototype.Packed.Checker
