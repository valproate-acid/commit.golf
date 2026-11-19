import CommitGolfCandidate.TaggedPinnedOpenedLows
import CommitGolfCandidate.TaggedPinnedHighSupport

namespace TwoPermutationPrototype.Sampling
open OracleComp

theorem pinned_unique_mapped_key {α β : Type} {items : List α} (key : α → β)
    (unique : (items.map key).Nodup) {a b : α}
    (aIn : a ∈ items) (bIn : b ∈ items) (same : key a = key b) : a = b := by
  induction items with
  | nil => simp at aIn
  | cons head rest ih =>
    have distinct := List.nodup_cons.mp (show (key head :: rest.map key).Nodup from unique)
    rcases List.mem_cons.mp aIn with rfl | aTail
    · rcases List.mem_cons.mp bIn with rfl | bTail
      · rfl
      · exact (distinct.1 (List.mem_map.mpr ⟨_, bTail, same.symm⟩)).elim
    · rcases List.mem_cons.mp bIn with rfl | bTail
      · exact (distinct.1 (List.mem_map.mpr ⟨_, aTail, same⟩)).elim
      · exact ih distinct.2 aTail bTail

abbrev PinnedOpenedState.PrivateSlot {base : Cache} {count : Nat} (state : PinnedOpenedState base count) :=
  {i : Fin count // ¬ state.isRevealed i}

theorem PinnedOpenedState.slot_private {base : Cache} {count : Nat} (state : PinnedOpenedState base count)
    (valid : state.high.Valid count) {row : PinnedHighRow} (included : row ∈ state.high.added)
    (hidden : row.input ∉ state.opened) : ¬ state.isRevealed ⟨row.slot, state.slots row included⟩ := by
  rintro ⟨other, otherIn, same, opened⟩
  have rowEq := pinned_unique_mapped_key PinnedHighRow.slot valid.slotUnique otherIn included same
  exact hidden (rowEq ▸ opened)

noncomputable def PinnedOpenedState.targetSlot {base : Cache} {count : Nat} (state : PinnedOpenedState base count)
    (valid : state.high.Valid count) (address : Block) : Option state.PrivateSlot := by
  classical
  exact if hit : ∃ row ∈ state.high.added, row.input = address ∧ address ∉ state.opened then
    let row := Classical.choose hit
    have found := Classical.choose_spec hit
    some ⟨⟨row.slot, state.slots row found.1⟩, state.slot_private valid found.1 (found.2.1.symm ▸ found.2.2)⟩
  else none

theorem pinned_target_slot_sound {base : Cache} {count : Nat} (state : PinnedOpenedState base count)
    (valid : state.high.Valid count) (address : Block) (i : state.PrivateSlot)
    (found : state.targetSlot valid address = some i) :
    ∃ row ∈ state.high.added, row.input = address ∧ row.slot = i.val.val := by
  classical
  unfold PinnedOpenedState.targetSlot at found
  split at found
  · rename_i hit
    have witness := Classical.choose_spec hit
    have same := congrArg (fun r : state.PrivateSlot => r.val.val) (Option.some.inj found)
    exact ⟨Classical.choose hit, witness.1, witness.2.1, same⟩
  · cases found

theorem pinned_targets_distinct {base : Cache} {count : Nat} {I : Type}
    (state : PinnedOpenedState base count) (valid : state.high.Valid count)
    (addresses : I → Block) (unique : Function.Injective addresses) :
    PinnedTargetsDistinct (fun i => state.targetSlot valid (addresses i)) := by
  intro slot left right a b
  obtain ⟨x, xIn, xRead, xSlot⟩ := pinned_target_slot_sound state valid (addresses left) slot a
  obtain ⟨y, yIn, yRead, ySlot⟩ := pinned_target_slot_sound state valid (addresses right) slot b
  have eq := pinned_unique_mapped_key PinnedHighRow.slot valid.slotUnique xIn yIn (xSlot.trans ySlot.symm)
  apply unique
  rw [← xRead, ← yRead, eq]

theorem pinned_reused_slot_reads_digest {base : Cache} {count : Nat} (state : PinnedOpenedState base count)
    [DecidablePred state.isRevealed] (valid : state.high.Valid count)
    (visible : {i : Fin count // state.isRevealed i} → BitVec 256) (privateLow : state.PrivateSlot → BitVec 256)
    (address : Block) (slot : state.PrivateSlot) (found : state.targetSlot valid address = some slot) :
    pinnedOutputDigest ((state.high.realize (pinnedFinLowTape (state.merge visible privateLow))).example.val.forward address) =
      privateLow slot := by
  obtain ⟨row, present, atRow, sameSlot⟩ := pinned_target_slot_sound state valid address slot found
  let low := pinnedFinLowTape (state.merge visible privateLow)
  have agree := (state.high.realize low).example.property (row.realize low)
    (List.mem_append_left _ (List.mem_map_of_mem present))
  have now : pinnedOutputDigest ((state.high.realize low).example.val.forward address) = low row.slot :=
    (congrArg pinnedOutputDigest (show (state.high.realize low).example.val.forward address =
        (row.realize low).2 by exact (congrArg (state.high.realize low).example.val.forward atRow).symm.trans agree)).trans
      (pinned_high_row_digest row low)
  refine now.trans ?_
  have finite : row.slot < count := state.slots row present
  have exactSlot : (⟨row.slot, finite⟩ : Fin count) = slot.val := Fin.ext sameSlot
  change (if fit : row.slot < count then state.merge visible privateLow ⟨row.slot, fit⟩ else 0) = _
  rw [dite_eq_left finite, exactSlot]
  simp only [PinnedOpenedState.merge, dite_eq_right (show ¬ state.isRevealed slot.val from slot.property)]

end TwoPermutationPrototype.Sampling
