import CommitGolfCandidate.TwoPermutationOpeningProofBytes

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.Sampling OracleComp
open Opening (groupsBefore lower_swap_bound lowerNode trapdoorHeap trapdoorSalt openingNodes
  cap_frontier_nodes_small cap_span_root cap_span_node cap_span_children)

def proofFromTrapdoor {s : Submission} (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) : Proof :=
  (positions.sort (· ≤ ·)).flatMap (fun i => lowerRecord true (trapdoorHeap (s := s) trapdoor)
    i (trapdoorSalt (s := s) trapdoor i)) ++
    (openingNodes positions).flatMap (fun node => proofDigestBytes true (trapdoorHeap (s := s) trapdoor node))

private theorem sorted_value_indices (positions : Positions) :
    (positions.attach.sort (fun i j => i.val ≤ j.val)).map Subtype.val =
      positions.sort (· ≤ ·) := by
  have mapped := Finset.map_sort (r := fun i j : {i // i ∈ positions} => i.val ≤ j.val)
    (r' := fun i j : Index => i ≤ j) (f := Function.Embedding.subtype (· ∈ positions))
    (s := positions.attach) (by intro a _ b _; rfl)
  simpa only [Finset.attach_map_val, Function.Embedding.coe_subtype] using mapped

private theorem grouping_sorted (positions : Positions) :
    groupsBefore positions positions.card =
      (positions.attach.sort (fun i j => i.val ≤ j.val)).map (capGroup ∘ Subtype.val) := by
  unfold groupsBefore
  have size : (positions.sort (· ≤ ·)).length = positions.card := by simp
  rw [← size, List.take_length, ← sorted_value_indices positions, List.map_map]

private theorem grouping_empty (positions : Positions) :
    (groupsBefore positions positions.card).isEmpty = true ↔ positions.card = 0 := by
  have size : (groupsBefore positions positions.card).length = positions.card := by
    simp [groupsBefore]
  rw [List.isEmpty_iff]
  simpa only [size] using (List.length_eq_zero_iff (l := groupsBefore positions positions.card)).symm

private theorem lower_sibling_positive (index : Index) (level : Nat) (bound : level < 16) :
    0 < (lowerNode index level ^^^ 1) := by
  have depth : 2^level ≤ 2^16 := Nat.pow_le_pow_right (by decide) (by omega)
  have leafBound : 2*2^level ≤ LENGTH+index.val := by
    have room : 2*2^16 ≤ LENGTH := by decide
    omega
  have above : 2 ≤ lowerNode index level := by
    unfold lowerNode
    exact (Nat.le_div_iff_mul_le (by positivity)).mpr leafBound
  by_contra! zero
  have emptied : (lowerNode index level ^^^ 1) = 0 := by omega
  have collapsed := congrArg (fun n : Nat => n ^^^ 1) emptied
  simp [Nat.xor_assoc] at collapsed
  omega

private theorem cap_frontier_positive (groups : List Nat) (node height : Nat)
    (span : Opening.CapSpan node height) :
    ∀ n ∈ capFrontierNodes groups node height, 0 < n := by
  induction height generalizing node with
  | zero =>
    have positive := (cap_span_node node 0 span).1
    cases mark : capIsMarked groups node 0 <;> simp [capFrontierNodes, mark, positive]
  | succ height ih =>
    have positive := (cap_span_node node (height+1) span).1
    have ⟨left, right⟩ := cap_span_children node height span
    cases mark : capIsMarked groups node (height+1)
    · simp [capFrontierNodes, mark, positive]
    · intro n member
      simp only [capFrontierNodes, mark, ite_true, List.mem_append] at member
      exact member.elim (ih _ left n) (ih _ right n)

private theorem lower_record_matches (s : Submission) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (heap : Nat → BitVec 256) (salts : CompleteSaltTape) (index : Index)
    (digest : ∀ node, 0<node → node<2*LENGTH → trapdoorHeap (s := s) trapdoor node = heap node)
    (salt : ∀ i, trapdoorSalt (s := s) trapdoor i = salts i) :
    lowerRecord true (trapdoorHeap (s := s) trapdoor) index (trapdoorSalt (s := s) trapdoor index) =
      lowerRecord true heap index (salts index) := by
  unfold lowerRecord
  rw [salt]
  congr 1
  apply List.flatMap_congr
  intro level live
  have inside := List.mem_range.mp live
  have same := digest _ (lower_sibling_positive index level inside) (lower_swap_bound index level)
  simp only [lowerNode] at same
  rw [same]

/-- The pure transcript reconstructed from the concrete trapdoor slices agrees
with the reference transcript for any heap and nonce tape stored by commit. -/
theorem proof_from_trapdoor_matches (s : Submission) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) (compress : Compression) (leaves : DigestTape) (salts : CompleteSaltTape)
    (digest : ∀ node, 0<node → node<2*LENGTH →
      trapdoorHeap (s := s) trapdoor node = transcriptHeap true compress leaves node)
    (salt : ∀ index, trapdoorSalt (s := s) trapdoor index = salts index) :
    proofFromTrapdoor (s := s) trapdoor positions =
      (transcriptBuilder true compress positions (fun i => salts i.val) leaves).2 := by
  let heap := transcriptHeap true compress leaves
  unfold proofFromTrapdoor transcriptBuilder
  dsimp only
  congr 1
  · rw [← sorted_value_indices positions, List.flatMap_map]
    apply List.flatMap_congr
    intro index _
    exact lower_record_matches s trapdoor heap salts index.val digest salt
  · unfold frontierProof
    rw [← grouping_sorted positions]
    by_cases empty : positions.card = 0
    · simp [openingNodes, empty, groupsBefore]
    · have someGroups : (groupsBefore positions positions.card).isEmpty = false := by
        cases h : (groupsBefore positions positions.card).isEmpty
        · rfl
        · exact False.elim (empty ((grouping_empty positions).mp h))
      simp only [openingNodes, empty, someGroups, Bool.false_eq_true, ite_false]
      apply List.flatMap_congr
      intro node member
      have small := cap_frontier_nodes_small _ 1 8 cap_span_root node member
      have capacity : 512 < 2*LENGTH := by decide
      rw [digest _ (cap_frontier_positive _ 1 8 cap_span_root node member) (small.trans capacity)]

end TwoPermutationPrototype.PackedOpening
