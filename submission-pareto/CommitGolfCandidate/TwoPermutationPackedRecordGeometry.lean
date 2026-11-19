import CommitGolfCandidate.TwoPermutationPackedHonestLower

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Checker (checker_positions_bound checkSourceWord)

/-- Byte cursor before consuming the sibling at this level, or after the record at level sixteen. -/
def lowerProofByte (ordinal level : Nat) : Nat :=
  if level=0 then checkProofByte ordinal+16 else checkProofByte ordinal+48+30*(level-1)

def lowerSiblingWidth (level : Nat) : Nat := if level=0 then 32 else 30

theorem lower_proof_byte_next (ordinal level : Nat) :
    lowerProofByte ordinal (level+1) = lowerProofByte ordinal level+lowerSiblingWidth level := by
  by_cases h : level=0
  · subst level
    simp [lowerProofByte,lowerSiblingWidth,Nat.add_assoc]
  · simp only [lowerProofByte,lowerSiblingWidth,h,ite_false,Nat.succ_ne_zero,Nat.add_sub_cancel]
    omega

theorem lower_proof_byte_end (ordinal : Nat) :
    lowerProofByte ordinal 16 = checkProofByte (ordinal+1) := by
  unfold lowerProofByte checkProofByte
  simp only [show (16:Nat) ≠ 0 by decide,ite_false]
  omega

theorem packed_record_geometry (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (fits : ProofWithin input) :
    checkProofByte ordinal % 2 = 0 ∧
      checkProofByte ordinal + 498 ≤ 10334769248 + input.proof.length ∧
      32768 ≤ checkProofByte ordinal ∧
      checkProofByte ordinal + 498 ≤ MEMORY_BYTES ∧
      checkSourceWord ordinal+32 ≤ 2^33 := by
  have count := checker_positions_bound input
  obtain ⟨atLeast, atMost⟩ := fits
  unfold checkProofByte checkSourceWord MEMORY_BYTES
  omega

theorem lower_proof_geometry (ordinal level : Nat) (inside : level<16)
    (room : checkProofByte ordinal+498 ≤ MEMORY_BYTES) :
    32768 ≤ lowerProofByte ordinal level ∧ lowerProofByte ordinal level % 2 = 0 ∧
      lowerProofByte ordinal level+lowerSiblingWidth level ≤ MEMORY_BYTES := by
  by_cases first : level=0
  · simp only [lowerProofByte,lowerSiblingWidth,first,ite_true]
    unfold checkProofByte at room ⊢
    omega
  · simp only [lowerProofByte,lowerSiblingWidth,first,ite_false]
    unfold checkProofByte at room ⊢
    omega

theorem lower_width_from_counter (level : Nat) :
    lowerSiblingWidth level = if 16-level=16 then 32 else 30 := by
  unfold lowerSiblingWidth
  simp only [show 16-level=16 ↔ level=0 by omega]

theorem lower_wire_sibling_from_cursor (state : MachineState) (ordinal level : Nat) :
    lowerWireSibling state ordinal level =
      if 16-level=16 then readBuffer state (lowerProofByte ordinal level) 32
      else 0#16 ++ readBuffer state (lowerProofByte ordinal level) 30 := by
  simp only [show 16-level=16 ↔ level=0 by omega]
  by_cases first : level=0 <;> simp [lowerWireSibling,lowerProofByte,first]

theorem lower_wire_sibling_frame (before after : MachineState) (ordinal level : Nat)
    (frame : ∀ j < lowerSiblingWidth level,
      memoryView after ((lowerProofByte ordinal level+j)/8) =
        memoryView before ((lowerProofByte ordinal level+j)/8)) :
    lowerWireSibling after ordinal level=lowerWireSibling before ordinal level := by
  by_cases first : level=0
  · have words : ∀ j < 32, memoryView after ((checkProofByte ordinal+16+j)/8) =
        memoryView before ((checkProofByte ordinal+16+j)/8) := by
      simpa only [lowerSiblingWidth,lowerProofByte,first,ite_true] using frame
    simpa only [lowerWireSibling,first,ite_true] using buffer_byte_frame before after _ 32 words
  · have words : ∀ j < 30, memoryView after ((checkProofByte ordinal+48+30*(level-1)+j)/8) =
        memoryView before ((checkProofByte ordinal+48+30*(level-1)+j)/8) := by
      simpa only [lowerSiblingWidth,lowerProofByte,first,ite_false] using frame
    simp only [lowerWireSibling,first,ite_false,buffer_byte_frame before after _ 30 words]

end TwoPermutationPrototype.Packed.Checker
