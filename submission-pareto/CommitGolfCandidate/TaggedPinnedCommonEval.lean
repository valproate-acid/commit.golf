import CommitGolfCandidate.TaggedPinnedCommon

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2048
attribute [local irreducible] pinnedFirstAddresses

local instance pinnedCommonEvalDiscrete {α : Type} : MeasurableSpace α := ⊤

noncomputable def pinnedBoundedHigh (addresses : List Block) (cache : Cache) (input : Block) : BitVec 1344 :=
  if input ∈ addresses then pinnedOutputTail (cache.example.val.forward input) else 0

noncomputable def pinnedCommonFull {α : Type} (base : Cache) (positions : Positions) (left right : Message)
    (salts : OpenedSalts positions) (next : (Block → BitVec 1344) → Cache → ProbComp α) : ProbComp α := do
  let firstAddresses := pinnedFirstAddresses left right
  let first ← runPinnedFull base [] (pinnedConstantPlans firstAddresses)
  let upper := pinnedBoundedHigh firstAddresses first.2
  let final ← runPinnedFull first.2 [] (pinnedConstantPlans (pinnedOpenedAddresses positions left upper salts))
  next upper final.2

theorem pinned_bound_high_at {base : Cache} (cache : PinnedHighCache base) (low : PinnedLowTape)
    (addresses : List Block) (covered : ∀ address ∈ addresses, cache.Covers address) :
    pinnedBoundedHigh addresses (cache.realize low) = pinnedBoundedHigh addresses cache.zero := by
  funext address
  unfold pinnedBoundedHigh
  by_cases present : address ∈ addresses
  · simp only [present, ite_true]
    exact cache.read_tail address ((cache.covers_iff address).mp (covered address present)) low
  · simp only [present, ite_false]

theorem pinned_bound_high_opened (addresses : List Block) (cache : Cache) (positions : Positions)
    (message : Message) (salts : OpenedSalts positions) (covered : ∀ i ∈ positions, pinnedFirstAddress message i ∈ addresses) :
    pinnedOpenedAddresses positions message (pinnedBoundedHigh addresses cache) salts =
      pinnedOpenedAddresses positions message (fun input => pinnedOutputTail (cache.example.val.forward input)) salts := by
  unfold pinnedOpenedAddresses
  apply List.map_congr_left
  intro i present
  simp only [pinnedPublicAddress, pinnedBoundedHigh, covered i (Finset.mem_toList.mp present), ite_true]

/-- Running the real restricted fresh-output sampler through both preloads
gives the exact common high history followed by a single independent low tape. -/
theorem pinned_common_full_separates {α : Type} (base : Cache) (positions : Positions) (left right : Message)
    (salts : OpenedSalts positions) (room : base.entries.length + 2 * LENGTH + positions.card ≤ 2^121)
    (next : (Block → BitVec 1344) → Cache → ProbComp α) :
    pinnedCommonFull base positions left right salts next =ᵈ
      (do let common ← pinnedCommonHigh base positions left right salts
          let draws ← samplePinnedLows (2 * LENGTH + positions.card)
          next (pinnedBoundedHigh (pinnedFirstAddresses left right) common.first.zero)
            (common.final.realize (pinnedPlaceLows (fun _ => 0) 0 draws))) := by
  classical
  let addresses := pinnedFirstAddresses left right
  let start := PinnedHighCache.empty base
  let firstPlans := pinnedConstantPlans addresses
  let finishFirst (full : Cache) : ProbComp α := do
    let upper := pinnedBoundedHigh addresses full
    let read ← runPinnedFull full [] (pinnedConstantPlans (pinnedOpenedAddresses positions left upper salts))
    next upper read.2
  have firstRoom : start.zero.entries.length + firstPlans.length ≤ 2^121 := by
    simp only [start, PinnedHighCache.zero, PinnedHighCache.empty_realize, firstPlans, pinnedConstantPlans,
      List.length_map, addresses, pinned_first_addresses_length]
    omega
  apply (pinned_full_high_low_equivalence start 0 (fun _ => 0) [] firstPlans (by simp [start, PinnedHighCache.empty])
    firstRoom (fun _ => finishFirst)).trans
  simp only [firstPlans, pinnedConstantPlans, List.length_map, addresses, pinned_first_addresses_length,
    pinnedCommonHigh, bind_assoc, pure_bind]
  apply EvalDistEq.bind_congr_of_support
  intro first reached
  have firstBound : start.zero.entries.length + addresses.length ≤ 2^121 := by
    simpa only [firstPlans, pinnedConstantPlans, List.length_map] using firstRoom
  obtain ⟨ready, enlarged, _, covered⟩ := pinned_high_const_support start 0 [] addresses
    (pinned_high_empty_valid base) firstBound first reached
  simp only [addresses, pinned_first_addresses_length, Nat.zero_add] at ready enlarged
  simp only [start, PinnedHighCache.zero, PinnedHighCache.empty_realize] at enlarged
  change first.2.zero.entries.length ≤ base.entries.length + 2 * LENGTH at enlarged
  let upper := pinnedBoundedHigh addresses first.2.zero
  let opened := pinnedOpenedAddresses positions left
      (fun address => pinnedOutputTail (first.2.zero.example.val.forward address)) salts
  let openPlans := pinnedConstantPlans opened
  let nextHigh := runPinnedHigh first.2 (2*LENGTH) [] openPlans
  have commonOpened : pinnedOpenedAddresses positions left upper salts = opened := by
    apply pinned_bound_high_opened
    intro i _
    exact pinned_first_address_mem left right false i
  have openRoom : first.2.zero.entries.length + openPlans.length ≤ 2^121 := by
    simp only [openPlans, pinnedConstantPlans, List.length_map, opened, pinned_opened_addresses_length]
    omega
  let lowsFirst := samplePinnedLows (2*LENGTH)
  let lowsOpened := samplePinnedLows positions.card
  let tail (firstLows : List (BitVec 256)) (final : List (BitVec 1344) × PinnedHighCache base) : ProbComp α := do
    let last ← lowsOpened
    next upper (final.2.realize (pinnedPlaceLows (fun _ => 0) 0 (firstLows ++ last)))
  trans (lowsFirst >>= fun firstLows => nextHigh >>= tail firstLows)
  · apply EvalDistEq.bind_congr_of_support
    intro firstLows supported
    have used : firstLows.length = 2*LENGTH := pinned_low_draw_length supported
    let low := pinnedPlaceLows (fun _ => 0) 0 firstLows
    have highUnchanged := pinned_bound_high_at first.2 low addresses covered
    unfold finishFirst
    change (do
      let last ← runPinnedFull (first.2.realize low) []
        (pinnedConstantPlans (pinnedOpenedAddresses positions left
          (pinnedBoundedHigh addresses (first.2.realize low)) salts))
      next (pinnedBoundedHigh addresses (first.2.realize low)) last.2) =ᵈ _
    rw [highUnchanged, commonOpened]
    apply (pinned_full_high_low_equivalence first.2 (2*LENGTH) low [] openPlans ready.slotRoom openRoom
      (fun _ => next upper)).trans
    unfold nextHigh tail lowsOpened
    simp only [openPlans, pinnedConstantPlans, List.length_map, opened, pinned_opened_addresses_length]
    apply EvalDistEq.bind_right
    intro value
    apply EvalDistEq.bind_right
    intro last
    have all := pinned_place_low_append (fun _ => 0) 0 firstLows last
    simp only [Nat.zero_add, used] at all
    change next upper (value.2.realize (pinnedPlaceLows
        (pinnedPlaceLows (fun _ => 0) 0 firstLows) (2*LENGTH) last)) =ᵈ
      next upper (value.2.realize (pinnedPlaceLows (fun _ => 0) 0 (firstLows ++ last)))
    rw [all]
  · apply (EvalDistEq.of_evalDist_eq (distribution_bind_comm lowsFirst nextHigh tail)).trans
    unfold nextHigh tail lowsFirst lowsOpened upper openPlans opened addresses
    simp only [pinned_lows_sum, bind_assoc, pure_bind]
    rfl

end TwoPermutationPrototype.Sampling
