import CommitGolfCandidate.TaggedPinnedTargets

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048
attribute [local irreducible] pinnedFirstAddresses

structure PinnedCommonHigh (base : Cache) where
  first : PinnedHighCache base
  final : PinnedHighCache base
  opened : List Block

noncomputable def PinnedCommonHigh.upper {base : Cache} (state : PinnedCommonHigh base) (input : Block) : BitVec 1344 :=
  pinnedOutputTail (state.first.zero.example.val.forward input)

noncomputable def pinnedCommonHigh (base : Cache) (positions : Positions) (left right : Message)
    (salts : OpenedSalts positions) : ProbComp (PinnedCommonHigh base) := do
  let first ← runPinnedHigh (PinnedHighCache.empty base) 0 []
    (pinnedConstantPlans (pinnedFirstAddresses left right))
  let opened := pinnedOpenedAddresses positions left
    (fun input => pinnedOutputTail (first.2.zero.example.val.forward input)) salts
  let final ← runPinnedHigh first.2 (2 * LENGTH) [] (pinnedConstantPlans opened)
  pure ⟨first.2, final.2, opened⟩

structure PinnedCommonHigh.Facts {base : Cache} (state : PinnedCommonHigh base) (positions : Positions)
    (left right : Message) (salts : OpenedSalts positions) : Prop where
  tableBound : state.final.zero.entries.length ≤ base.entries.length + 2 * LENGTH + positions.card
  valid : state.final.Valid (2 * LENGTH + positions.card)
  firstCovered : ∀ input ∈ pinnedFirstAddresses left right, state.first.Covers input
  firstRetained : ∀ row ∈ state.first.added, row ∈ state.final.added
  openedCovered : ∀ input ∈ state.opened, state.final.Covers input
  openedShape : state.opened = pinnedOpenedAddresses positions left state.upper salts

theorem pinned_common_high_facts (base : Cache) (positions : Positions) (left right : Message)
    (salts : OpenedSalts positions) (room : base.entries.length + 2 * LENGTH + positions.card ≤ 2 ^ 121)
    (state : PinnedCommonHigh base) (possible : state ∈ support (pinnedCommonHigh base positions left right salts)) :
    state.Facts positions left right salts := by
  let before : ProbComp (List (BitVec 1344) × PinnedHighCache base) :=
    runPinnedHigh (PinnedHighCache.empty base) 0 [] (pinnedConstantPlans (pinnedFirstAddresses left right))
  let addresses (first : List (BitVec 1344) × PinnedHighCache base) :=
    pinnedOpenedAddresses positions left (fun input => pinnedOutputTail (first.2.zero.example.val.forward input)) salts
  let openedPhase (first : List (BitVec 1344) × PinnedHighCache base) : ProbComp (PinnedCommonHigh base) :=
    runPinnedHigh first.2 (2*LENGTH) [] (pinnedConstantPlans (addresses first)) >>= fun final =>
      pure ⟨first.2, final.2, addresses first⟩
  change state ∈ support (before >>= openedPhase) at possible
  obtain ⟨first, reachedFirst, possible⟩ := (mem_support_bind_iff before openedPhase state).mp possible
  obtain ⟨final, reachedFinal, equal⟩ := (mem_support_bind_iff
    (runPinnedHigh first.2 (2*LENGTH) [] (pinnedConstantPlans (addresses first)))
    (fun (final : List (BitVec 1344) × PinnedHighCache base) => pure ⟨first.2, final.2, addresses first⟩) state).mp possible
  simp only [support_pure, Set.mem_singleton_iff] at equal
  subst state
  let opened := pinnedOpenedAddresses positions left
    (fun input => pinnedOutputTail (first.2.zero.example.val.forward input)) salts
  have firstRoom : (PinnedHighCache.empty base).zero.entries.length +
      (pinnedFirstAddresses left right).length ≤ 2 ^ 121 := by
    simp only [PinnedHighCache.zero, PinnedHighCache.empty_realize, pinned_first_addresses_length]
    omega
  obtain ⟨validFirst, firstLength, _, firstCovers⟩ := pinned_high_const_support
    (PinnedHighCache.empty base) 0 [] (pinnedFirstAddresses left right) (pinned_high_empty_valid base)
    firstRoom first reachedFirst
  simp only [PinnedHighCache.zero, PinnedHighCache.empty_realize, pinned_first_addresses_length, Nat.zero_add]
    at validFirst firstLength
  change first.2.zero.entries.length ≤ base.entries.length + 2 * LENGTH at firstLength
  have openedRoom : first.2.zero.entries.length + opened.length ≤ 2 ^ 121 := by
    simp only [opened, pinned_opened_addresses_length]
    omega
  obtain ⟨validLast, lastLength, _, lastCovers⟩ := pinned_high_const_support first.2 (2*LENGTH)
    [] opened validFirst openedRoom final reachedFinal
  refine ⟨?_, ?_, firstCovers, ?_, lastCovers, rfl⟩
  · change final.2.zero.entries.length ≤ base.entries.length + 2 * LENGTH + positions.card
    simp only [opened, pinned_opened_addresses_length] at lastLength
    omega
  · simpa only [opened, pinned_opened_addresses_length] using validLast
  · intro row seen
    exact pinned_high_rows_keep first.2 (2*LENGTH) [] (pinnedConstantPlans opened) final reachedFinal row seen

def PinnedCommonHigh.openedState {base : Cache} {state : PinnedCommonHigh base} {positions : Positions}
    {left right : Message} {salts : OpenedSalts positions} (facts : state.Facts positions left right salts) :
    PinnedOpenedState base (2 * LENGTH + positions.card) :=
  ⟨state.final, facts.valid.slotRoom, state.opened,
    fun address present => (state.final.covers_iff address).mp (facts.openedCovered address present)⟩

theorem pinned_common_first_tail {base : Cache} {state : PinnedCommonHigh base} {positions : Positions}
    {left right : Message} {salts : OpenedSalts positions} (facts : state.Facts positions left right salts)
    (low : PinnedLowTape) (address : Block) (included : address ∈ pinnedFirstAddresses left right) :
    pinnedOutputTail ((state.final.realize low).example.val.forward address) = state.upper address := by
  have found := facts.firstCovered address included
  rw [state.first.forward_agrees_on_old state.final facts.firstRetained address found low]
  exact state.first.read_tail address ((state.first.covers_iff address).mp found) low

end TwoPermutationPrototype.Sampling
