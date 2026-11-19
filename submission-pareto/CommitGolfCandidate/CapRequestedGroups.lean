import CommitGolfCandidate.CapKnownView

/-! Connect duplicate-checked records to the requested finite positions. A supplied
proof cannot choose a different occupied cap shape. Lower-root computations and
the actual image's record parsing remain external obligations. -/
namespace CommitGolfCandidate
open CommitGolf

def capGroupRecords (positions : Positions) (lowerRoot : Index → Digest) :
    List (Nat × Digest) :=
  (positions.sort (· ≤ ·)).map (fun index => ((capGroup index).val, lowerRoot index))

theorem cap_group_records_member (positions : Positions) (lowerRoot : Index → Digest)
    (group : Nat) :
    (∃ value, (group, value) ∈ capGroupRecords positions lowerRoot) ↔
      ∃ index ∈ positions, (capGroup index).val = group := by
  simp only [capGroupRecords, List.mem_map, Finset.mem_sort]
  constructor
  · rintro ⟨value, index, member, same⟩
    exact ⟨index, member, congrArg Prod.fst same⟩
  · rintro ⟨index, member, same⟩
    exact ⟨lowerRoot index, index, member, by simp [same]⟩

theorem cap_requested_domain (positions : Positions) (lowerRoot : Index → Digest)
    (roots : CapRootMap) (accepted : capCollectForward (capGroupRecords positions lowerRoot) = some roots)
    (group : Nat) :
    (roots group).isSome = true ↔ ∃ index ∈ positions, (capGroup index).val = group := by
  rw [cap_collect_forward_domain _ roots accepted group, cap_group_records_member]

theorem cap_requested_set (positions : Positions) (lowerRoot : Index → Digest)
    (roots : CapRootMap) (accepted : capCollectForward (capGroupRecords positions lowerRoot) = some roots) :
    (Finset.range 256).filter (fun group => (roots group).isSome = true) =
      (capGroups positions).image (fun group => group.val) := by
  ext group
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, cap_requested_domain _ _ _ accepted]
  constructor
  · rintro ⟨bound, index, member, same⟩
    exact ⟨capGroup index, (cap_groups_member _ _).mpr ⟨index, member, rfl⟩, same⟩
  · rintro ⟨cap, member, same⟩
    obtain ⟨index, requested, equal⟩ := (cap_groups_member _ _).mp member
    exact ⟨by simpa [← same] using cap.isLt, index, requested, by simpa [equal] using same⟩

/-- Known leaves count distinct requested groups, not the number of records. -/
theorem cap_requested_count (positions : Positions) (lowerRoot : Index → Digest)
    (roots : CapRootMap) (accepted : capCollectForward (capGroupRecords positions lowerRoot) = some roots) :
    capMarkedCount (capKnownView roots 8 0) = (capGroups positions).card := by
  rw [cap_known_view_card, cap_requested_set _ _ _ accepted]
  exact Finset.card_image_of_injective _ Fin.val_injective

theorem cap_requested_calls (positions : Positions) (lowerRoot : Index → Digest)
    (roots : CapRootMap) (accepted : capCollectForward (capGroupRecords positions lowerRoot) = some roots) :
    capCalls (capKnownView roots 8 0) ≤ 8 * (capGroups positions).card := by
  simpa [cap_requested_count _ _ _ accepted] using cap_calls_bound (capKnownView roots 8 0)

theorem cap_requested_nonempty (positions : Positions) (lowerRoot : Index → Digest)
    (roots : CapRootMap) (accepted : capCollectForward (capGroupRecords positions lowerRoot) = some roots)
    (nonempty : positions.Nonempty) :
    capOccupied (capKnownView roots 8 0) = true := by
  rw [cap_occupied_count, cap_requested_count _ _ _ accepted]
  obtain ⟨index, member⟩ := nonempty
  exact Finset.card_pos.mpr ⟨capGroup index, (cap_groups_member _ _).mpr ⟨index, member, rfl⟩⟩
end CommitGolfCandidate
