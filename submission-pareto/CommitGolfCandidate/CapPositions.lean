import CommitGolfCandidate.CapRequestedGroups

/-! Requested cap paths and original position orientation bits. The finite
height-eight bit identity is kernel checked with ordinary decide. -/
namespace CommitGolfCandidate
open CommitGolf

def capPathOfIndex : (height index : Nat) → Path height
  | 0, _ => .here
  | height + 1, index =>
      if index < 2^height then .left (capPathOfIndex height index)
      else .right (capPathOfIndex height (index - 2^height))

theorem cap_path_index_inverse (height index : Nat) (bound : index < 2^height) :
    capPathIndex (capPathOfIndex height index) = index := by
  induction height generalizing index with
  | zero =>
      simp only [pow_zero] at bound
      have : index = 0 := by omega
      subst index
      rfl
  | succ height ih =>
      simp only [pow_succ] at bound
      by_cases left : index < 2^height
      · simp [capPathOfIndex, left, capPathIndex, ih index left]
      · have rightBound : index - 2^height < 2^height := by omega
        simp [capPathOfIndex, left, capPathIndex, ih _ rightBound]
        omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem cap_seven_path_bits : ∀ group : Fin 256,
    capPathBits (capPathOfIndex 8 group.val) = (List.range 8).map (group.val.testBit) := by
  decide

def capRequestedPath (index : Index) : Path 8 := capPathOfIndex 8 (capGroup index).val

theorem cap_requested_path_index (index : Index) :
    capPathIndex (capRequestedPath index) = (capGroup index).val := by
  exact cap_path_index_inverse 8 (capGroup index).val (capGroup index).isLt

/-- The cap contributes exactly bits 16..23 of the original index. -/
theorem cap_requested_path_bits (index : Index) :
    capPathBits (capRequestedPath index) =
      (List.range 8).map (fun level => index.val.testBit (16 + level)) := by
  rw [capRequestedPath, cap_seven_path_bits]
  apply List.map_congr_left
  intro level _
  change (index.val / 2^16).testBit level = _
  simpa [Nat.add_comm] using (Nat.testBit_div_two_pow (n := 16) index.val level)

/-- Appending the lower path and cap witness retains the old 24-bit directions,
so the retained collision extractor compares the same original position. -/
theorem cap_full_path_bits (index : Index) :
    (List.range 16).map (index.val.testBit) ++ capPathBits (capRequestedPath index) =
      (List.range 24).map (index.val.testBit) := by
  rw [cap_requested_path_bits]
  change _ = (List.range (16 + 8)).map _
  rw [List.range_add, List.map_append, List.map_map]
  rfl

theorem cap_requested_known_leaf (positions : Positions) (lowerRoot : Index → Digest)
    (roots : CapRootMap)
    (accepted : capCollectForward (capGroupRecords positions lowerRoot) = some roots)
    (index : Index) (requested : index ∈ positions) :
    capLeafValue (capKnownView roots 8 0) (capRequestedPath index) = some (lowerRoot index) := by
  rw [cap_known_view_leaf, cap_requested_path_index, Nat.zero_add]
  apply cap_collect_forward_member _ roots accepted
  simp only [capGroupRecords, List.mem_map, Finset.mem_sort]
  exact ⟨index, requested, rfl⟩
end CommitGolfCandidate
