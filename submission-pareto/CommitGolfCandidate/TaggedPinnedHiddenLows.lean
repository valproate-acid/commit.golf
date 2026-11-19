import CommitGolfCandidate.TaggedPinnedHiddenWrites
import CommitGolfCandidate.TaggedPinnedOrdinal

namespace TwoPermutationPrototype.Sampling
open OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

noncomputable def pinnedDigestByAddress (addresses : List Block) (digests : Fin addresses.length → BitVec 256)
    (input : Block) : BitVec 256 := by
  classical
  exact if found : ∃ i : Fin addresses.length, addresses[i] = input then digests (Classical.choose found) else 0

theorem pinned_digest_by_address_get (addresses : List Block) (unique : addresses.Nodup)
    (digests : Fin addresses.length → BitVec 256) (i : Fin addresses.length) :
    pinnedDigestByAddress addresses digests addresses[i] = digests i := by
  classical
  unfold pinnedDigestByAddress
  have existsAt : ∃ j : Fin addresses.length, addresses[j] = addresses[i] := ⟨i, rfl⟩
  rw [dite_eq_left existsAt]
  exact congrArg digests (unique.injective_get (Classical.choose_spec existsAt))

noncomputable def PinnedOpenedState.lowFromTape {base : Cache} {count : Nat} (state : PinnedOpenedState base count)
    [DecidablePred state.isRevealed] {I : Type}
    (opened : {i : Fin count // state.isRevealed i} → BitVec 256)
    (tape : PinnedDigestTape state.PrivateSlot I) : PinnedLowTape :=
  pinnedFinLowTape (state.merge opened (fun slot => tape (.inl slot)))

noncomputable def PinnedOpenedState.hiddenAddressSlot {base : Cache} {count : Nat} (state : PinnedOpenedState base count)
    (valid : state.high.Valid count) (addresses : List Block) (i : Fin addresses.length) : Option state.PrivateSlot :=
  state.targetSlot valid addresses[i]

private theorem pinned_swap_tape_on_hidden_row {base : Cache} {count : Nat}
    (state : PinnedOpenedState base count) [DecidablePred state.isRevealed] (valid : state.high.Valid count)
    (opened : {i : Fin count // state.isRevealed i} → BitVec 256)
    (addresses : List Block) (unique : addresses.Nodup) (away : ∀ a ∈ addresses, a ∉ state.opened)
    (final : List (BitVec 1344) × PinnedHighCache base)
    (possible : final ∈ support (runPinnedHigh state.high count [] (pinnedConstantPlans addresses)))
    (lastValid : final.2.Valid (count+addresses.length))
    (tape : PinnedDigestTape state.PrivateSlot (Fin addresses.length))
    (row : PinnedHighRow) (present : row ∈ final.2.added) :
    let swapped := pinnedSwapDigestTape (state.hiddenAddressSlot valid addresses) tape
    pinnedPlaceLows (state.lowFromTape opened swapped) count (List.ofFn (fun i => swapped (.inr i))) row.slot =
      if row.input ∈ addresses then pinnedDigestByAddress addresses (fun i => tape (.inr i)) row.input
      else state.lowFromTape opened tape row.slot := by
  classical
  let target := state.hiddenAddressSlot valid addresses
  let swapped := pinnedSwapDigestTape target tape
  let digest := pinnedDigestByAddress addresses (fun i => tape (.inr i))
  let noLow := state.lowFromTape opened tape
  let swappedLow := state.lowFromTape opened swapped
  change pinnedPlaceLows swappedLow count (List.ofFn (fun i => swapped (.inr i))) row.slot =
    (if row.input ∈ addresses then digest row.input else noLow row.slot)
  by_cases before : row ∈ state.high.added
  · have room := state.slots row before
    rw [pinned_place_below _ _ _ _ room]
    let i : Fin count := ⟨row.slot, room⟩
    have swappedVal : swappedLow row.slot = state.merge opened (fun s => swapped (.inl s)) i := by
      exact dite_eq_left room
    have oldVal : noLow row.slot = state.merge opened (fun s => tape (.inl s)) i := by
      exact dite_eq_left room
    rw [swappedVal, oldVal]
    by_cases revealed : state.isRevealed i
    · have location : row.input ∈ state.opened := by
        obtain ⟨chosen, listed, same, known⟩ := revealed
        exact (pinned_unique_mapped_key PinnedHighRow.slot valid.slotUnique listed before same) ▸ known
      have outside : row.input ∉ addresses := fun inside => away row.input inside location
      simp only [PinnedOpenedState.merge, dite_eq_left revealed, outside, ite_false]
    · let privateSlot : state.PrivateSlot := ⟨i, revealed⟩
      simp only [PinnedOpenedState.merge, dite_eq_right revealed]
      change swapped (.inl privateSlot) = if row.input ∈ addresses then digest row.input else tape (.inl privateSlot)
      by_cases tested : row.input ∈ addresses
      · obtain ⟨j, site⟩ := List.mem_iff_get.mp tested
        have secret := pinned_target_slot_of_row state valid row before (away row.input tested)
        have fits : target j = some privateSlot := by
          unfold target PinnedOpenedState.hiddenAddressSlot
          change addresses[j] = row.input at site
          rw [site]
          exact secret
        have injective : PinnedTargetsDistinct target := pinned_targets_distinct state valid
          (fun j : Fin addresses.length => addresses[j]) unique.injective_get
        have found := (pinned_digest_source_iff injective privateSlot j).2 fits
        have digestEq : digest row.input = tape (.inr j) := by
          rw [← site]
          exact pinned_digest_by_address_get addresses unique _ j
        simp only [tested, ite_true, digestEq, swapped, pinnedSwapDigestTape, Function.comp_def,
          pinnedSwapDigestIndex, found, Option.elim_some]
      · have absent : pinnedDigestSource target privateSlot = none := by
          cases selected : pinnedDigestSource target privateSlot with
          | none => rfl
          | some j =>
            have injective : PinnedTargetsDistinct target := pinned_targets_distinct state valid
              (fun j : Fin addresses.length => addresses[j]) unique.injective_get
            have fits := (pinned_digest_source_iff injective privateSlot j).1 selected
            obtain ⟨other, included, atInput, atSlot⟩ := pinned_target_slot_sound state valid addresses[j] privateSlot fits
            have eq := pinned_unique_mapped_key PinnedHighRow.slot valid.slotUnique included before atSlot
            subst other
            exact (tested (atInput.symm ▸ List.get_mem addresses j)).elim
        simp only [tested, ite_false, swapped, pinnedSwapDigestTape, Function.comp_def,
          pinnedSwapDigestIndex, absent, Option.elim_none]
  · obtain ⟨i, address, where_⟩ := pinned_new_row_ordinal state.high count [] addresses final possible row present before
    have freshAddress : ∀ other ∈ state.high.added, other.input ≠ addresses[i] := by
      intro other known same
      have earlier := pinned_high_rows_keep state.high count [] (pinnedConstantPlans addresses) final possible other known
      have eq := pinned_unique_mapped_key PinnedHighRow.input lastValid.inputUnique earlier present (same.trans address.symm)
      exact before (eq ▸ known)
    have freshSlot : target i = none := pinned_target_slot_none state valid _ freshAddress
    have used : row.input ∈ addresses := address.symm ▸ List.get_mem addresses i
    have read := pinned_place_fin swappedLow count (fun j => swapped (.inr j)) i
    rw [where_, read, ite_eq_left used, address]
    have plain : swapped (.inr i) = tape (.inr i) := by
      simp only [swapped, pinnedSwapDigestTape, Function.comp_def, pinnedSwapDigestIndex, freshSlot, Option.elim_none]
    exact plain.trans (pinned_digest_by_address_get addresses unique (fun j => tape (.inr j)) i).symm

/-- The completion after all hidden reads can be sampled by programming the
common reference. A low-tape permutation supplies independent hidden digests
even when a B address reuses a private A row. -/
theorem pinned_conditional_hidden_program_equivalence {α : Type} {base : Cache} {count : Nat}
    (state : PinnedOpenedState base count) [DecidablePred state.isRevealed] (valid : state.high.Valid count)
    (opened : {i : Fin count // state.isRevealed i} → BitVec 256)
    (addresses : List Block) (unique : addresses.Nodup) (away : ∀ a ∈ addresses, a ∉ state.opened)
    (outside : ∀ a ∈ addresses, UnusedInput base.entries a)
    (room : state.high.zero.entries.length + addresses.length ≤ 2^121)
    (final : List (BitVec 1344) × PinnedHighCache base)
    (possible : final ∈ support (runPinnedHigh state.high count [] (pinnedConstantPlans addresses)))
    (tape : PinnedDigestTape state.PrivateSlot (Fin addresses.length))
    (next : BiPermutation Block → ProbComp α) :
    let target := state.hiddenAddressSlot valid addresses
    let swapped := pinnedSwapDigestTape target tape
    let finalLow := pinnedPlaceLows (state.lowFromTape opened swapped) count (List.ofFn (fun i => swapped (.inr i)))
    (do let p ← (state.high.realize (state.lowFromTape opened tape)).sample
        let rows := addresses.map (fun addr => (addr, pinnedCachedUpper final.2.zero addr ++
          pinnedDigestByAddress addresses (fun i => tape (.inr i)) addr))
        next (p.val.programRows rows)) =ᵈ
      (do let p ← (final.2.realize finalLow).sample; next p.val) := by
  classical
  dsimp only
  let original := state.lowFromTape opened tape
  let wanted := pinnedDigestByAddress addresses (fun i => tape (.inr i))
  let swapped := pinnedSwapDigestTape (state.hiddenAddressSlot valid addresses) tape
  let finalLow := pinnedPlaceLows (state.lowFromTape opened swapped) count (List.ofFn (fun i => swapped (.inr i)))
  obtain ⟨calculated, schedule, rows, placement⟩ := pinned_build_hidden_writes state.high count [] addresses
    valid room unique outside final possible original wanted
  have endValid := (pinned_high_const_support state.high count [] addresses valid room final possible).1
  have coincides : final.2.realize calculated = final.2.realize finalLow := by
    apply final.2.same_realization
    intro row included
    exact (placement row included).trans
      (pinned_swap_tape_on_hidden_row state valid opened addresses unique away final possible endValid tape row included).symm
  have law := pinned_uniform_write_schedule schedule next
  rw [rows, coincides] at law
  exact law

theorem pinned_swapped_hidden_digest_read {base : Cache} {count : Nat}
    (state : PinnedOpenedState base count) [DecidablePred state.isRevealed] (valid : state.high.Valid count)
    (opened : {i : Fin count // state.isRevealed i} → BitVec 256)
    (addresses : List Block) (unique : addresses.Nodup) (away : ∀ a ∈ addresses, a ∉ state.opened)
    (outside : ∀ a ∈ addresses, UnusedInput base.entries a)
    (room : state.high.zero.entries.length + addresses.length ≤ 2^121)
    (final : List (BitVec 1344) × PinnedHighCache base)
    (possible : final ∈ support (runPinnedHigh state.high count [] (pinnedConstantPlans addresses)))
    (tape : PinnedDigestTape state.PrivateSlot (Fin addresses.length)) (i : Fin addresses.length)
    (p : Completion (final.2.realize (pinnedPlaceLows
      (state.lowFromTape opened (pinnedSwapDigestTape (state.hiddenAddressSlot valid addresses) tape)) count
      (List.ofFn (fun j => pinnedSwapDigestTape (state.hiddenAddressSlot valid addresses) tape (.inr j))))).entries) :
    pinnedOutputDigest (p.val.forward addresses[i]) = tape (.inr i) := by
  let swapped := pinnedSwapDigestTape (state.hiddenAddressSlot valid addresses) tape
  let finalLow := pinnedPlaceLows (state.lowFromTape opened swapped) count (List.ofFn (fun j => swapped (.inr j)))
  have fact := pinned_high_const_support state.high count [] addresses valid room final possible
  have iIn : addresses[i] ∈ addresses := List.get_mem addresses i
  obtain ⟨row, present, actual⟩ :=
    pinned_row_from_covers final.2 addresses[i] (fact.2.2.2 _ iIn) (outside _ iIn)
  have read := p.property (row.realize finalLow) (List.mem_append_left _ (List.mem_map_of_mem present))
  change p.val.forward row.input = (row.realize finalLow).2 at read
  have here := pinned_swap_tape_on_hidden_row state valid opened addresses unique away final possible fact.1 tape row present
  have included : row.input ∈ addresses := actual.symm ▸ iIn
  have assigned : finalLow row.slot = pinnedDigestByAddress addresses (fun j => tape (.inr j)) row.input := by
    simpa only [included, ite_true] using here
  have digs := (congrArg pinnedOutputDigest ((congrArg p.val.forward actual).symm.trans read)).trans
    (pinned_high_row_digest row finalLow)
  refine (digs.trans assigned).trans ?_
  rw [actual, pinned_digest_by_address_get addresses unique]

end TwoPermutationPrototype.Sampling
