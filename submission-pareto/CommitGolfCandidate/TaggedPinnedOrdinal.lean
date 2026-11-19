import CommitGolfCandidate.TaggedPinnedCommon

namespace TwoPermutationPrototype.Sampling
open OracleComp
set_option maxRecDepth 8192

theorem pinned_new_row_ordinal {base : Cache} (cache : PinnedHighCache base) (slot : Nat)
    (answers : List (BitVec 1344)) (addresses : List Block)
    (result : List (BitVec 1344) × PinnedHighCache base)
    (possible : result ∈ support (runPinnedHigh cache slot answers (pinnedConstantPlans addresses)))
    (row : PinnedHighRow) (present : row ∈ result.2.added) (new : row ∉ cache.added) :
    ∃ i : Fin addresses.length, row.input = addresses[i] ∧ row.slot = slot + i.val := by
  induction addresses generalizing cache slot answers result with
  | nil =>
    simp only [pinnedConstantPlans, List.map_nil, runPinnedHigh, support_pure, Set.mem_singleton_iff] at possible
    subst result
    exact (new present).elim
  | cons address rest ih =>
    simp only [pinnedConstantPlans, List.map_cons, runPinnedHigh] at possible
    obtain ⟨⟨answer, head⟩, first, restRun⟩ := (mem_support_bind_iff _ _ _).mp possible
    by_cases cameEarly : row ∈ head.added
    · rcases pinned_high_step_support cache slot address (answer, head) first with same | ⟨r, where_, _, time, grows⟩
      · exact (new (same ▸ cameEarly)).elim
      · change head.added = r :: cache.added at grows
        rw [grows] at cameEarly
        rcases List.mem_cons.mp cameEarly with equal | earlier
        · subst r
          exact ⟨⟨0, by simp⟩, where_, by simpa only [Nat.add_zero] using time⟩
        · exact (new earlier).elim
    · obtain ⟨i, index, tick⟩ := ih head (slot+1) (answer :: answers) result restRun present cameEarly
      let next : Fin (address :: rest).length := ⟨i.val+1, by simp only [List.length_cons]; omega⟩
      refine ⟨next, ?_, ?_⟩
      · exact index
      · change _ = slot + (i.val+1)
        omega

theorem pinned_target_slot_of_row {base : Cache} {count : Nat} (state : PinnedOpenedState base count)
    (valid : state.high.Valid count) (row : PinnedHighRow) (present : row ∈ state.high.added)
    (closed : row.input ∉ state.opened) :
    state.targetSlot valid row.input =
      some ⟨⟨row.slot, state.slots row present⟩, state.slot_private valid present closed⟩ := by
  classical
  have existsHere : ∃ a ∈ state.high.added, a.input = row.input ∧ row.input ∉ state.opened :=
    ⟨row, present, rfl, closed⟩
  unfold PinnedOpenedState.targetSlot
  rw [dite_eq_left existsHere]
  have chosen := Classical.choose_spec existsHere
  have eq := pinned_unique_mapped_key PinnedHighRow.input valid.inputUnique chosen.1 present chosen.2.1
  apply congrArg some
  apply Subtype.ext
  exact Fin.ext (congrArg PinnedHighRow.slot eq)

theorem pinned_target_slot_none {base : Cache} {count : Nat} (state : PinnedOpenedState base count)
    (valid : state.high.Valid count) (address : Block)
    (missing : ∀ row ∈ state.high.added, row.input ≠ address) :
    state.targetSlot valid address = none := by
  classical
  have no : ¬ ∃ row ∈ state.high.added, row.input = address ∧ address ∉ state.opened :=
    fun ⟨row, present, found, _⟩ => missing row present found
  simp only [PinnedOpenedState.targetSlot, no, dite_false]

end TwoPermutationPrototype.Sampling
