import CommitGolfCandidate.TwoPermutationCheckerCopyDigest
import CommitGolfCandidate.InputMemory

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64

theorem read_buffer_word (state : MachineState) (word : Nat) :
    readBuffer state (8*word) 8 = memoryView state word := by
  have slice := read_buffer_slice state (8*word) 32 0 8 (by decide)
  have assembled := read_digest_word state (8*word) 0 (by omega) (by decide)
  exact (by
    simp only [Nat.mul_zero, Nat.add_zero] at slice assembled
    exact slice.symm.trans assembled)

theorem word_eq_of_byte_frame (before after : MachineState) (word : Nat)
    (frame : ∀ i < 8, after.getByte (BitVec.ofNat 64 (8*word+i)) =
      before.getByte (BitVec.ofNat 64 (8*word+i))) :
    memoryView after word = memoryView before word := by
  rw [← read_buffer_word, ← read_buffer_word]
  unfold readBuffer
  apply congrArg (BitVec.ofNat 64)
  apply Finset.sum_congr rfl
  intro i hi
  rw [frame i (Finset.mem_range.mp hi)]

theorem byte_eq_of_word_frame (before after : MachineState) (address : Nat)
    (same : memoryView after (address/8) = memoryView before (address/8)) :
    after.getByte (BitVec.ofNat 64 address) = before.getByte (BitVec.ofNat 64 address) := by
  have sum : 8*(address/8)+address%8=address := by omega
  have small : address%8 < 8 := Nat.mod_lt _ (by decide)
  have left := aligned_byte after (address/8) (address%8) (by omega)
  have right := aligned_byte before (address/8) (address%8) (by omega)
  rw [sum, Nat.div_eq_of_lt small, Nat.mul_zero, Nat.add_zero] at left right
  exact left.trans ((congrArg (fun w => extractByte w (address%8%8)) same).trans right.symm)

theorem read_buffer_above (before after : MachineState) (start count firstWord : Nat)
    (above : 8*firstWord ≤ start) (room : start+count ≤ 2^64)
    (frame : ∀ q, firstWord ≤ q → q < 2^61 → memoryView after q = memoryView before q) :
    readBuffer after start count = readBuffer before start count := by
  unfold readBuffer
  apply congrArg (BitVec.ofNat (8*count))
  apply Finset.sum_congr rfl
  intro i hi
  have small := Finset.mem_range.mp hi
  rw [byte_eq_of_word_frame before after (start+i) (frame _ (by omega) (by omega))]

end TwoPermutationPrototype.Packed.Checker
