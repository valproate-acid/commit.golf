import CommitGolfCandidate.TwoPermutationOpeningResources

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf TwoPermutationPrototype.Sampling

def recordBytes : Nat := 498
def capacity : Nat := recordBytes * LENGTH + 30*256

def proofLength (positions : Positions) : Nat :=
  recordBytes*positions.card + 30*(Opening.openingNodes positions).length

/-- Packed frontier emission replaces a 32-byte doubleword copy with 15 pairs of halfword instructions. -/
def capSubtreeCycles (groups : List Nat) (node : Nat) : Nat → Nat
  | 0 => if capIsMarked groups node 0 then 5 else 37
  | height+1 =>
    if capIsMarked groups node (height+1) then
      19 + capSubtreeCycles groups (2*node) height + capSubtreeCycles groups (2*node+1) height
    else 37

theorem cap_cycle_delta (groups : List Nat) (node height : Nat) :
    capSubtreeCycles groups node height =
      Opening.capSubtreeCycles groups node height + 22*(capFrontierNodes groups node height).length := by
  induction height generalizing node with
  | zero =>
    cases marked : capIsMarked groups node 0 <;> simp [capSubtreeCycles, Opening.capSubtreeCycles, capFrontierNodes, marked]
  | succ height ih =>
    cases marked : capIsMarked groups node (height+1)
    · simp [capSubtreeCycles, Opening.capSubtreeCycles, capFrontierNodes, marked]
    · simp only [capSubtreeCycles, Opening.capSubtreeCycles, capFrontierNodes, marked, ite_true,
        List.length_append, ih (2*node), ih (2*node+1)]
      omega

def scheduledCycles (positions : Positions) : Nat :=
  if positions.card = 0 then 7 else
    13 + (590*positions.card-1) + 2551 +
      (capSubtreeCycles (Opening.groupsBefore positions positions.card) 1 8 + 3) + 4

def siblingWidth (level : Nat) : Nat := if level = 0 then 32 else 30

def siblingOffset (level : Nat) : Nat :=
  if level = 0 then 16 else 48+30*(level-1)

def recordBase (ordinal : Nat) : Nat := Opening.proofBase+recordBytes*ordinal

def siblingDestination (ordinal level : Nat) : Nat := recordBase ordinal+siblingOffset level

theorem sibling_offset_next (level : Nat) :
    siblingOffset (level+1) = siblingOffset level+siblingWidth level := by
  cases level <;> simp [siblingOffset, siblingWidth, Nat.mul_succ] <;> omega

theorem record_end (ordinal : Nat) :
    siblingDestination ordinal 16 = recordBase (ordinal+1) := by
  simp [siblingDestination, recordBase, recordBytes, siblingOffset]
  omega

theorem even_sibling_destination (ordinal level : Nat) :
    siblingDestination ordinal level % 2 = 0 := by
  have base : Opening.proofBase % 2 = 0 := by decide
  unfold siblingDestination recordBase recordBytes siblingOffset
  split <;> omega

theorem proof_fits_every_cardinality (positions : Positions) :
    proofLength positions ≤ capacity := by
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  have nodes := Opening.opening_nodes_bound positions
  unfold proofLength capacity recordBytes
  omega

theorem scheduled_fuel_fits (positions : Positions) : scheduledCycles positions ≤ 17179934720 := by
  have cardinal : positions.card ≤ 16777216 := by
    have bound : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
    exact bound
  unfold scheduledCycles
  split
  · decide
  · rw [cap_cycle_delta]
    have counts := Opening.opening_cap_cycles_bound (Opening.groupsBefore positions positions.card)
    have nodes := Opening.opening_nodes_bound positions
    simp only [Opening.openingNodes, ite_eq_right (by assumption)] at nodes
    omega

theorem scheduled_scored_limits (positions : Positions) (count : positions.card = BATCH) :
    scheduledCycles positions ≤ 88311 ∧ proofLength positions ≤ 67584 := by
  have size : positions.card = 128 := count
  have cap := Opening.opening_cap_cycles_bound (Opening.groupsBefore positions positions.card)
  have bytes := Opening.opening_nodes_bound positions
  have positive : positions.card ≠ 0 := by omega
  rw [scheduledCycles, ite_eq_right positive, cap_cycle_delta]
  unfold proofLength recordBytes
  simp only [Opening.openingNodes, ite_eq_right positive] at bytes ⊢
  omega

theorem scheduled_scored_attainment :
    ∃ positions : Positions, positions.card = BATCH ∧ scheduledCycles positions = 88311 ∧
      proofLength positions = 67584 := by
  obtain ⟨positions, count, cycles, bytes⟩ := Opening.opening_scored_attainment
  have size : positions.card = 128 := count
  have positive : positions.card ≠ 0 := by omega
  unfold Opening.openingMachineCycles at cycles
  rw [ite_eq_right positive] at cycles
  have exactCount : (Opening.openingNodes positions).length = 128 := by
    unfold Opening.openingLength at bytes
    omega
  refine ⟨positions, count, ?_, ?_⟩
  · rw [scheduledCycles, ite_eq_right positive, cap_cycle_delta]
    simp only [Opening.openingNodes, ite_eq_right positive] at exactCount
    omega
  · unfold proofLength recordBytes
    omega

end TwoPermutationPrototype.PackedOpening
