import CommitGolfCandidate.TaggedPinnedPlanning

namespace TwoPermutationPrototype.Sampling
open OracleComp
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

def PinnedHighCache.Covers {base : Cache} (cache : PinnedHighCache base) (input : Block) : Prop :=
  ∃ row ∈ cache.zero.entries, row.1 = input

theorem PinnedHighCache.covers_iff {base : Cache} (cache : PinnedHighCache base) (input : Block) :
    cache.Covers input ↔ ¬ UnusedInput cache.zero.entries input := by
  classical
  constructor
  · rintro ⟨row, present, eq⟩ unused
    exact unused row present eq
  · intro notNew
    by_contra missing
    exact notNew (fun row present eq => missing ⟨row, present, eq⟩)

structure PinnedHighCache.Valid {base : Cache} (cache : PinnedHighCache base) (slot : Nat) : Prop where
  inputUnique : (cache.added.map PinnedHighRow.input).Nodup
  tailUnique : (cache.added.map PinnedHighRow.upper).Nodup
  slotUnique : (cache.added.map PinnedHighRow.slot).Nodup
  slotRoom : ∀ row ∈ cache.added, row.slot < slot
  chooserInput : ∀ row ∈ cache.added, UnusedInput base.entries row.input
  chooserTail : ∀ row ∈ cache.added, pinnedUnusedTail (pinnedCachedTails base) row.upper

theorem pinned_high_empty_valid (base : Cache) : (PinnedHighCache.empty base).Valid 0 := by
  constructor <;> simp [PinnedHighCache.empty]

theorem pinned_high_step_provenance {base : Cache} (cache : PinnedHighCache base) (slot : Nat) (input : Block)
    (result : BitVec 1344 × PinnedHighCache base) (possible : result ∈ support (pinnedHighStep cache slot input))
    (room : cache.zero.entries.length ≤ 2^121) :
    (result.2.added = cache.added ∧ cache.Covers input) ∨ ∃ row : PinnedHighRow,
      row.input = input ∧ row.upper = result.1 ∧ row.slot = slot ∧ result.2.added = row :: cache.added ∧
      UnusedInput cache.zero.entries row.input ∧ pinnedUnusedTail (pinnedCachedTails cache.zero) row.upper := by
  classical
  unfold pinnedHighStep at possible
  by_cases fresh : UnusedInput cache.zero.entries input
  · have existsTail := pinned_current_tails_nonempty cache.zero room
    simp only [fresh, existsTail, dite_true] at possible
    obtain ⟨tail, _, eq⟩ := (mem_support_bind_iff _ _ _).mp possible
    simp only [support_pure, Set.mem_singleton_iff] at eq
    subst result
    exact Or.inr ⟨_, rfl, rfl, rfl, rfl, fresh, tail.property⟩
  · simp only [fresh, dite_false, support_pure, Set.mem_singleton_iff] at possible
    subst result
    exact Or.inl ⟨rfl, (cache.covers_iff input).mpr fresh⟩

theorem pinned_high_step_valid {base : Cache} {cache : PinnedHighCache base} {slot : Nat}
    (valid : cache.Valid slot) (input : Block) (result : BitVec 1344 × PinnedHighCache base)
    (possible : result ∈ support (pinnedHighStep cache slot input)) (room : cache.zero.entries.length ≤ 2^121) :
    result.2.Valid (slot+1) := by
  rcases pinned_high_step_provenance cache slot input result possible room with ⟨same, _⟩ |
      ⟨row, _, _, here, grows, fresh, newTail⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [same] using valid.inputUnique
    · simpa only [same] using valid.tailUnique
    · simpa only [same] using valid.slotUnique
    · intro old seen
      exact (valid.slotRoom old (same ▸ seen)).trans (Nat.lt_succ_self _)
    · simpa only [same] using valid.chooserInput
    · simpa only [same] using valid.chooserTail
  · have freshInput : row.input ∉ cache.added.map PinnedHighRow.input := by
      intro seen
      obtain ⟨old, included, equal⟩ := List.mem_map.mp seen
      exact fresh (old.realize (fun _ => 0)) (List.mem_append_left _ (List.mem_map_of_mem included)) equal
    have freshTail : row.upper ∉ cache.added.map PinnedHighRow.upper := by
      intro seen
      apply newTail
      change row.upper ∈ pinnedCachedTails (cache.realize (fun _ => 0))
      rw [cache.tails]
      exact List.mem_append_left _ seen
    have freshSlot : row.slot ∉ cache.added.map PinnedHighRow.slot := by
      intro seen
      obtain ⟨old, included, equal⟩ := List.mem_map.mp seen
      exact (Nat.ne_of_lt (valid.slotRoom old included)) (equal.trans here)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [grows, List.map_cons, List.nodup_cons]
      exact ⟨freshInput, valid.inputUnique⟩
    · simp only [grows, List.map_cons, List.nodup_cons]
      exact ⟨freshTail, valid.tailUnique⟩
    · simp only [grows, List.map_cons, List.nodup_cons]
      exact ⟨freshSlot, valid.slotUnique⟩
    · intro old seen
      rw [grows] at seen
      rcases List.mem_cons.mp seen with rfl | earlier
      · rw [here]; exact Nat.lt_succ_self _
      · exact (valid.slotRoom old earlier).trans (Nat.lt_succ_self _)
    · intro old seen
      rw [grows] at seen
      rcases List.mem_cons.mp seen with rfl | earlier
      · exact fun previous present => fresh previous (List.mem_append_right _ present)
      · exact valid.chooserInput old earlier
    · intro old seen
      rw [grows] at seen
      rcases List.mem_cons.mp seen with rfl | earlier
      · intro tail
        apply newTail
        change _ ∈ pinnedCachedTails (cache.realize (fun _ => 0))
        rw [cache.tails]
        exact List.mem_append_right _ tail
      · exact valid.chooserTail old earlier

theorem pinned_high_step_covers {base : Cache} (cache : PinnedHighCache base) (slot : Nat) (input : Block)
    (result : BitVec 1344 × PinnedHighCache base) (possible : result ∈ support (pinnedHighStep cache slot input))
    (room : cache.zero.entries.length ≤ 2^121) :
    (∀ address, cache.Covers address → result.2.Covers address) ∧ result.2.Covers input := by
  rcases pinned_high_step_provenance cache slot input result possible room with ⟨same, found⟩ |
      ⟨row, equal, _, _, added, _, _⟩
  · unfold PinnedHighCache.Covers PinnedHighCache.zero at *
    change ∃ value ∈ pinnedHighTable base cache.added (fun _ => 0), value.1 = input at found
    change (∀ address, (∃ value ∈ pinnedHighTable base cache.added (fun _ => 0), value.1 = address) →
      ∃ value ∈ pinnedHighTable base result.2.added (fun _ => 0), value.1 = address) ∧
      (∃ value ∈ pinnedHighTable base result.2.added (fun _ => 0), value.1 = input)
    rw [same]
    exact ⟨fun _ => id, found⟩
  · have entries : result.2.zero.entries = row.realize (fun _ => 0) :: cache.zero.entries := by
      change pinnedHighTable base result.2.added (fun _ => 0) = _
      rw [added]
      rfl
    refine ⟨?_, ?_⟩
    · rintro address ⟨previous, included, reply⟩
      exact ⟨previous, entries.symm ▸ List.mem_cons_of_mem _ included, reply⟩
    · exact ⟨row.realize (fun _ => 0), entries.symm ▸ List.mem_cons_self, equal⟩

theorem pinned_high_step_length {base : Cache} (cache : PinnedHighCache base) (slot : Nat) (input : Block)
    (result : BitVec 1344 × PinnedHighCache base) (possible : result ∈ support (pinnedHighStep cache slot input)) :
    result.2.zero.entries.length ≤ cache.zero.entries.length + 1 := by
  simp only [PinnedHighCache.zero, PinnedHighCache.entries_length]
  rcases pinned_high_step_support cache slot input result possible with same | ⟨row, _, _, _, grows⟩
  · rw [same]
    omega
  · rw [grows, List.length_cons]
    omega

private theorem pinned_high_step_rows_keep {base : Cache} (cache : PinnedHighCache base) (slot : Nat) (input : Block)
    (result : BitVec 1344 × PinnedHighCache base) (possible : result ∈ support (pinnedHighStep cache slot input))
    (row : PinnedHighRow) (old : row ∈ cache.added) : row ∈ result.2.added := by
  rcases pinned_high_step_support cache slot input result possible with same | ⟨extra, _, _, _, more⟩
  · simpa only [same] using old
  · exact more.symm ▸ List.mem_cons_of_mem _ old

theorem pinned_high_rows_keep {base : Cache} (cache : PinnedHighCache base) (slot : Nat)
    (answers : List (BitVec 1344)) (plans : List PinnedHighPlan)
    (result : List (BitVec 1344) × PinnedHighCache base)
    (possible : result ∈ support (runPinnedHigh cache slot answers plans))
    (row : PinnedHighRow) (old : row ∈ cache.added) :
    row ∈ result.2.added := by
  induction plans generalizing cache slot answers result with
  | nil =>
    simp only [runPinnedHigh, support_pure, Set.mem_singleton_iff] at possible
    subst result
    exact old
  | cons plan rest ih =>
    simp only [runPinnedHigh] at possible
    obtain ⟨⟨reply, middle⟩, earlier, later⟩ := (mem_support_bind_iff _ _ _).mp possible
    apply ih middle (slot+1) (reply :: answers) result later
    exact pinned_high_step_rows_keep cache slot (plan answers) (reply, middle) earlier row old

theorem PinnedHighCache.forward_agrees_on_old {base : Cache} (first last : PinnedHighCache base)
    (keeps : ∀ row ∈ first.added, row ∈ last.added) (address : Block) (found : first.Covers address)
    (low : PinnedLowTape) :
    (last.realize low).example.val.forward address = (first.realize low).example.val.forward address := by
  obtain ⟨row, present, same⟩ := found
  change row ∈ pinnedHighTable base first.added (fun _ => 0) at present
  rcases List.mem_append.mp present with fresh | original
  · obtain ⟨stored, included, rfl⟩ := List.mem_map.mp fresh
    have a := (last.realize low).example.property (stored.realize low)
      (List.mem_append_left _ (List.mem_map_of_mem (keeps stored included)))
    have b := (first.realize low).example.property (stored.realize low)
      (List.mem_append_left _ (List.mem_map_of_mem included))
    change stored.input = address at same
    exact ((congrArg (last.realize low).example.val.forward same).symm.trans a).trans
      (b.symm.trans (congrArg (first.realize low).example.val.forward same))
  · have a := (last.realize low).example.property row (List.mem_append_right _ original)
    have b := (first.realize low).example.property row (List.mem_append_right _ original)
    exact ((congrArg (last.realize low).example.val.forward same).symm.trans a).trans
      (b.symm.trans (congrArg (first.realize low).example.val.forward same))
theorem pinned_high_const_support {base : Cache} (cache : PinnedHighCache base) (slot : Nat)
    (answers : List (BitVec 1344)) (addresses : List Block) (valid : cache.Valid slot)
    (room : cache.zero.entries.length + addresses.length ≤ 2^121)
    (result : List (BitVec 1344) × PinnedHighCache base)
    (possible : result ∈ support (runPinnedHigh cache slot answers (pinnedConstantPlans addresses))) :
    result.2.Valid (slot + addresses.length) ∧
    result.2.zero.entries.length ≤ cache.zero.entries.length + addresses.length ∧
    (∀ address, cache.Covers address → result.2.Covers address) ∧
    (∀ address ∈ addresses, result.2.Covers address) := by
  induction addresses generalizing cache slot answers result with
  | nil =>
    simp only [pinnedConstantPlans, List.map_nil, runPinnedHigh, support_pure, Set.mem_singleton_iff] at possible
    subst result
    exact ⟨by simpa using valid, by simp, fun _ => id, by simp⟩
  | cons address rest ih =>
    simp only [pinnedConstantPlans, List.map_cons, runPinnedHigh] at possible
    obtain ⟨⟨answer, middle⟩, head, tail⟩ := (mem_support_bind_iff _ _ _).mp possible
    have headRoom : cache.zero.entries.length ≤ 2^121 := by omega
    have headValid := pinned_high_step_valid valid address (answer, middle) head headRoom
    have headCovers := pinned_high_step_covers cache slot address (answer, middle) head headRoom
    have headSize := pinned_high_step_length cache slot address (answer, middle) head
    have middleRoom : middle.zero.entries.length + rest.length ≤ 2^121 := by
      change middle.zero.entries.length ≤ cache.zero.entries.length + 1 at headSize
      simp only [List.length_cons] at room
      omega
    obtain ⟨finalValid, finalSize, keep, covered⟩ := ih middle (slot+1) (answer :: answers) headValid middleRoom result tail
    refine ⟨?_, ?_, fun addr known => keep addr (headCovers.1 addr known), ?_⟩
    · rw [List.length_cons, show slot + (rest.length+1) = (slot+1)+rest.length by omega]
      exact finalValid
    · change middle.zero.entries.length ≤ cache.zero.entries.length + 1 at headSize
      simp only [List.length_cons]
      omega
    · intro someAddress found
      rcases List.mem_cons.mp found with rfl | found
      · exact keep _ headCovers.2
      · exact covered _ found

end TwoPermutationPrototype.Sampling
