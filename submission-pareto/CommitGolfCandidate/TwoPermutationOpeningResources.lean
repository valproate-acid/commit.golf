import CommitGolfCandidate.TwoPermutationOpeningProofBytes

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.Sampling

private def capWorst : Nat → Nat
  | 0 => 39
  | remaining + 1 => 19 + 2 * capWorst remaining

private theorem cap_subtree_sharp_bound (groups : List Nat) (node height : Nat) :
    capSubtreeCycles groups node (height+1) ≤ capWorst height := by
  induction height generalizing node with
  | zero =>
    rw [capSubtreeCycles, cap_marked_children]
    cases left : capIsMarked groups (2*node) 0 <;>
      cases right : capIsMarked groups (2*node+1) 0 <;>
      simp [capSubtreeCycles, capWorst, left, right]
  | succ height ih =>
    have left := ih (2*node)
    have right := ih (2*node+1)
    rw [capSubtreeCycles, capWorst]
    split <;> omega

/-- A marked height-one subtree must contain at least one occupied leaf. Its
worst case is 39 cycles, which yields the tight bound at the production cap. -/
theorem opening_cap_cycles_bound (groups : List Nat) :
    capSubtreeCycles groups 1 8 ≤ 7405 :=
  cap_subtree_sharp_bound groups 1 7

/-- Both scored opening limits follow from the actual interpreter proof. -/
theorem opening_scored_limits (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (result : Execution) (physical : OpenPhysical s trapdoor positions result)
    (count : positions.card = BATCH) :
    result.cycles ≤ 42744 ∧ (result.state.getReg .x11).toNat ≤ 71680 := by
  have cap := opening_cap_cycles_bound (groupsBefore positions positions.card)
  have bytes := opening_nodes_bound positions
  have size : positions.card = 128 := count
  rw [physical.cycles, physical.length]
  unfold openingMachineCycles openingLength
  rw [ite_eq_right (by omega)]
  omega

private def scatteredIndex : Fin 128 ↪ Index where
  toFun i := ⟨131072*i.val, by
    have bounded := i.isLt
    norm_num [LENGTH, LOG_LENGTH]
    omega⟩
  inj' := by
    intro a b same
    have values := congrArg Fin.val same
    apply Fin.ext
    change 131072*a.val = 131072*b.val at values
    omega

private def scattered128 : Positions := (Finset.univ : Finset (Fin 128)).map scatteredIndex

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
/-- One request per even cap group attains both sharp scored opening bounds. -/
theorem opening_scored_attainment :
    ∃ positions : Positions, positions.card = BATCH ∧
      openingMachineCycles positions = 42744 ∧ openingLength positions = 71680 := by
  have count : scattered128.card = 128 := by decide
  let groups := ((List.finRange 128).map scatteredIndex).map capGroup
  have order : scattered128.sort (· ≤ ·) = (List.finRange 128).map scatteredIndex := by
    have transport := Finset.map_sort (r := fun a b : Fin 128 => a ≤ b)
      (r' := fun a b : Index => a ≤ b) (f := scatteredIndex) (s := Finset.univ)
      (by
        intro a _ b _
        change a.val ≤ b.val ↔ 131072*a.val ≤ 131072*b.val
        omega)
    simpa only [scattered128, Fin.sort_univ] using transport.symm
  have exactGroups : groupsBefore scattered128 128 = groups := by
    unfold groupsBefore groups
    rw [order, List.take_of_length_le (by simp)]
  have cap : capSubtreeCycles groups 1 8 = 7405 := by decide
  have frontier : (capFrontierNodes groups 1 8).length = 128 := by decide
  refine ⟨scattered128, count, ?_, ?_⟩
  · simp [openingMachineCycles, count, exactGroups, cap]
  · simp [openingLength, openingNodes, count, exactGroups, frontier]

end TwoPermutationPrototype.Opening
