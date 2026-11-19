import CommitGolfCandidate.TaggedPinnedModel

namespace TwoPermutationPrototype.Sampling
open CommitGolf TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

private theorem pinned_block_eq_of_words (a b : BitVec 1600)
    (words : ∀ j : Fin 25, a.extractLsb' (64 * j.val) 64 = b.extractLsb' (64 * j.val) 64) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  have same := congrArg (fun chunk : BitVec 64 => chunk.getLsbD (bit % 64)) (words ⟨bit / 64, by omega⟩)
  have inner : bit % 64 < 64 := by omega
  have address : 64 * (bit / 64) + bit % 64 = bit := by omega
  simpa [inner, address] using same

private theorem pinned_nested_slice {size : Nat} (word : BitVec size) {outer width start len : Nat}
    (room : start + len ≤ width) :
    (word.extractLsb' outer width).extractLsb' start len = word.extractLsb' (outer + start) len := by
  apply BitVec.eq_of_getLsbD_eq
  intro i inside
  have mid : start + i < width := by omega
  simp [mid, inside, Nat.add_assoc]

theorem pinned_pack_first_input (message : Message) (i : Index) :
    packBuffer (pinnedFirstInput (messageWords message i)) = (message i).extractLsb' 0 1600 := by
  apply pinned_block_eq_of_words
  intro j
  rw [packed_word, BitVec.extractLsb'_extractLsb'_of_le (by have := j.isLt; omega)]
  rfl

theorem pinned_pack_second_input (message : Message) (index : Index) (reply : Block) (nonce : BitVec 128) :
    packBuffer (pinnedSecondInput index (saltWords nonce) (replyWords reply) (messageWords message index)) =
      (message index).extractLsb' 1344 704 ++ (reply.extractLsb' 896 704 ++ (nonce ++ pinnedPositionTag index)) := by
  apply pinned_block_eq_of_words
  intro j
  rw [packed_word]
  let phase := nonce ++ pinnedPositionTag index
  let chain := reply.extractLsb' 896 704
  let values := (message index).extractLsb' 1344 704
  change _ = (values ++ (chain ++ phase)).extractLsb' (64 * j.val) 64
  have fits := j.isLt
  by_cases zero : j.val = 0
  · simp only [pinnedSecondInput, zero, ite_true, Nat.mul_zero]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 896),
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 192)]
    exact BitVec.extractLsb'_append_eq_right.symm
  · by_cases nonceWord : j.val < 3
    · simp only [pinnedSecondInput, zero, ite_false, nonceWord, dite_true, saltWords]
      rw [BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * j.val + 64 ≤ 896),
        BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * j.val + 64 ≤ 192)]
      change _ = (nonce ++ pinnedPositionTag index).extractLsb' (64 * j.val) 64
      rw [BitVec.extractLsb'_append_eq_of_le (by omega : 64 ≤ 64 * j.val)]
      congr 1
      omega
    · by_cases chainWord : j.val < 14
      · simp only [pinnedSecondInput, zero, ite_false, nonceWord, chainWord, dite_false, dite_true, replyWords]
        rw [BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * j.val + 64 ≤ 896),
          BitVec.extractLsb'_append_eq_of_le (by omega : 192 ≤ 64 * j.val)]
        change _ = (reply.extractLsb' 896 704).extractLsb' (64 * j.val - 192) 64
        rw [pinned_nested_slice _ (by omega : 64 * j.val - 192 + 64 ≤ 704)]
        congr 1
        omega
      · simp only [pinnedSecondInput, zero, ite_false, nonceWord, chainWord, dite_false, messageWords]
        rw [BitVec.extractLsb'_append_eq_of_le (by omega : 896 ≤ 64 * j.val)]
        change _ = ((message index).extractLsb' 1344 704).extractLsb' (64 * j.val - 896) 64
        rw [pinned_nested_slice _ (by omega : 64 * j.val - 896 + 64 ≤ 704)]
        congr 1
        omega

end TwoPermutationPrototype.Sampling
