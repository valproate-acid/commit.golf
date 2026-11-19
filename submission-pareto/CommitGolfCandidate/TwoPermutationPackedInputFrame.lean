import CommitGolfCandidate.TwoPermutationPackedCheckCursor

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Checker (checkIndexWord checkSourceWord checker_positions_bound
  RecordInputAddress RecordInputFrame)

/-- Packed records and their footer may begin between two consecutive aligned words. -/
theorem byte_frame (before after : MachineState) (address : Nat)
    (unchanged : memoryView after (address/8) = memoryView before (address/8)) :
    after.getByte (BitVec.ofNat 64 address) = before.getByte (BitVec.ofNat 64 address) := by
  have addr : 8*(address/8)+address%8=address := by omega
  have fit : address%8<64 := by omega
  have a := aligned_byte after (address/8) (address%8) fit
  have b := aligned_byte before (address/8) (address%8) fit
  rw [addr, Nat.div_eq_of_lt (show address%8<8 from by omega), Nat.mul_zero, Nat.add_zero] at a b
  rw [a,b]
  exact congrArg (fun word : Word => extractByte word (address%8%8)) unchanged

theorem buffer_byte_frame (before after : MachineState) (address count : Nat)
    (unchanged : ∀ j < count, memoryView after ((address+j)/8) = memoryView before ((address+j)/8)) :
    readBuffer after address count = readBuffer before address count := by
  unfold readBuffer
  congr 1
  apply Finset.sum_congr rfl
  intro j inside
  rw [byte_frame before after _ (unchanged j (Finset.mem_range.mp inside))]

theorem packed_input_address_after (input : CheckInput) (ordinal word : Nat)
    (used : RecordInputAddress input (ordinal+1) word) :
    (word < checkSourceWord ordinal ∨ checkSourceWord ordinal+26 ≤ word) ∧
      1576 ≤ word := by
  have card := checker_positions_bound input
  rcases used with ⟨first, last⟩ | ⟨first, last⟩ | source
  · unfold checkSourceWord
    omega
  · unfold checkIndexWord at first last
    unfold checkSourceWord
    omega
  · unfold checkSourceWord at *
    omega

theorem record_proof_frame (input : CheckInput) (ordinal offset count : Nat) (state : MachineState)
    (frame : RecordInputFrame input ordinal state) (before : ordinal ≤ input.positions.card)
    (bounded : checkProofByte ordinal+offset+count ≤ 2^36) :
    readBuffer state (checkProofByte ordinal+offset) count =
      readBuffer (Assembly.submission.initialState .check input) (checkProofByte ordinal+offset) count := by
  apply buffer_byte_frame
  intro j inside
  have card := checker_positions_bound input
  apply frame _ (by omega)
  exact Or.inr (Or.inr (by unfold checkSourceWord checkProofByte; omega))

end TwoPermutationPrototype.Packed.Checker
