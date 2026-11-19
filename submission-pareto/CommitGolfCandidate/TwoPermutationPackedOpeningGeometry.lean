import CommitGolfCandidate.TwoPermutationPackedOpeningSibling
import CommitGolfCandidate.TwoPermutationPackedOpeningFields
import CommitGolfCandidate.TwoPermutationOpeningGeometry

namespace TwoPermutationPrototype.PackedOpening
set_option maxRecDepth 4096
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Opening (trapdoorBase proofBase nonceBase indicesBase lowerNode)

def nonceAddress (index : Index) : Nat := nonceBase+16*index.val

def siblingAddress (index : Index) (level : Nat) : Nat :=
  trapdoorBase+32*(lowerNode index level ^^^ 1)

theorem packed_proof_memory : proofBase+capacity ≤ MEMORY_BYTES := by decide

theorem all_record_ends_fit (ordinal : Nat) (inside : ordinal < LENGTH) :
    recordBase (ordinal+1) ≤ MEMORY_BYTES := by
  apply Nat.le_trans _ packed_proof_memory
  unfold recordBase capacity
  apply Nat.add_le_add_left
  exact (Nat.mul_le_mul_left _ (Nat.succ_le_of_lt inside)).trans (Nat.le_add_right _ _)

theorem all_nonce_copies_fit (index : Index) (ordinal : Nat) (inside : ordinal < LENGTH) :
    nonceAddress index % 2 = 0 ∧ recordBase ordinal % 2 = 0 ∧
      nonceAddress index+16 ≤ recordBase ordinal ∧ recordBase ordinal+16 ≤ MEMORY_BYTES := by
  have endRecord := all_record_ends_fit ordinal inside
  have indexBound := index.isLt
  have tapeEnd := Opening.nonces_end_at_indices
  have indexEnd := Opening.indices_before_records
  have nonceEven : nonceBase % 2 = 0 := by decide
  have proofEven : proofBase % 2 = 0 := by decide
  unfold nonceAddress recordBase recordBytes at *
  omega

private theorem sibling_inside_record (level : Nat) (inside : level < 16) :
    siblingOffset level+siblingWidth level ≤ recordBytes := by
  unfold siblingOffset siblingWidth recordBytes
  split <;> omega

theorem all_sibling_copies_fit (index : Index) (ordinal level : Nat)
    (inside : ordinal < LENGTH) (valid : level < 16) :
    siblingAddress index level % 2 = 0 ∧ siblingDestination ordinal level % 2 = 0 ∧
      siblingAddress index level+siblingWidth level ≤ siblingDestination ordinal level ∧
      siblingDestination ordinal level+siblingWidth level ≤ MEMORY_BYTES := by
  have endRecord := all_record_ends_fit ordinal inside
  have offsets := sibling_inside_record level valid
  have bound := Opening.lower_swap_bound index level
  have heapEnd := Opening.heap_before_nonces
  have indexEnd := Opening.indices_before_records
  have tapeEnd := Opening.nonces_end_at_indices
  have heapEven : trapdoorBase % 2 = 0 := by decide
  have widthBound : siblingWidth level ≤ 32 := by unfold siblingWidth; split <;> decide
  refine ⟨?_, even_sibling_destination ordinal level, ?_, ?_⟩
  all_goals simp only [siblingAddress, siblingDestination, recordBase, recordBytes, Nat.mul_add] at * <;> omega

theorem physical_nonce_source (state : MachineState) (index : Index)
    (tape : state.getReg .x22 = BitVec.ofNat 64 nonceBase)
    (readIndex : state.getMem (state.getReg .x8) = BitVec.ofNat 64 index.val) :
    (nonceSetup state).getReg .x7 = BitVec.ofNat 64 (nonceAddress index) := by
  exact (nonce_setup_post state).2.2.1.trans (Opening.nonce_address state index.val tape readIndex)

theorem physical_sibling_source (state : MachineState) (index : Index) (level : Nat)
    (heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase)
    (node : state.getReg .x6 = BitVec.ofNat 64 (lowerNode index level)) :
    (headPrefix state 3).getReg .x7 = BitVec.ofNat 64 (siblingAddress index level) := by
  rw [(sibling_head_post state).2.2.1, heap, node, ← BitVec.ofNat_xor,
    BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 trapdoorBase + BitVec.ofNat 64 (lowerNode index level ^^^ 1) *
    BitVec.ofNat 64 32 = _
  rw [← BitVec.ofNat_mul, Nat.mul_comm _ 32, ← BitVec.ofNat_add]
  rfl

theorem physical_sibling_parent {state : MachineState} (index : Index) (level : Fin 16)
    (node : state.getReg .x6 = BitVec.ofNat 64 (lowerNode index level.val)) :
    (tailPrefix state level 2).getReg .x6 = BitVec.ofNat 64 (lowerNode index (level.val+1)) := by
  rw [(sibling_tail_post state level).2.2.2.1, node, Opening.lower_node_next]
  apply BitVec.eq_of_toNat_eq
  have size := Opening.lower_node_bound index level.val
  have length64 : 2*LENGTH < 2^64 := by decide
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show lowerNode index level.val < 2^64 by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]

theorem physical_sibling_destination {state : MachineState} (ordinal : Nat) (level : Fin 16)
    (dest : state.getReg .x21 = BitVec.ofNat 64 (siblingDestination ordinal level.val)) :
    (tailPrefix state level 2).getReg .x21 =
      BitVec.ofNat 64 (siblingDestination ordinal (level.val+1)) := by
  rw [(sibling_tail_post state level).2.2.1, dest, ← BitVec.ofNat_add]
  congr 1
  simp [siblingDestination, sibling_offset_next, Nat.add_assoc]

end TwoPermutationPrototype.PackedOpening
