import CommitGolfCandidate.CapBinding
import CommitGolfCandidate.CapPositions

/-! Connect lower authentication records and shared cap witnesses to the retained
salted-leaf collision extractor. Replay of the entire checker and the random
oracle probability reduction are still separate obligations. -/
namespace CommitGolfCandidate
open CommitGolf

theorem cap_opening_inputs_subset (compress : Compression) (salt : Digest) (value : Entry)
    (lower upper : List (Bool × Digest)) (capInputs : List (BitVec 512))
    (included : ∀ input ∈ pathInputs compress
      (climb compress (leafDigest compress salt value) lower) upper, input ∈ capInputs) :
    ∀ input ∈ openingInputs compress salt value (lower ++ upper),
      input ∈ openingInputs compress salt value lower ++ capInputs := by
  intro input member
  simp only [openingInputs, cap_path_inputs_append, List.mem_append] at member ⊢
  rcases member with chain | lowerOrUpper
  · exact Or.inl (Or.inl chain)
  · rcases lowerOrUpper with lowerMember | upperMember
    · exact Or.inl (Or.inr lowerMember)
    · exact Or.inr (included input upperMember)

/-- Conflicting values at the same original index produce a collision in the
selected lower-record inputs or the paid cap replay inputs. Directions are fixed
by the original index, including the seven cap bits. -/
theorem cap_record_collision (oracle : Oracle) (index : Index)
    (leftView rightView : CapView 8) (leftProof rightProof leftRest rightRest : List Digest)
    (root leftSalt rightSalt : Digest) (leftValue rightValue : Entry)
    (leftLower rightLower : List (Bool × Digest))
    (leftDirections : leftLower.map Prod.fst = (List.range 16).map index.val.testBit)
    (rightDirections : rightLower.map Prod.fst = (List.range 16).map index.val.testBit)
    (leftAccepted : capDecode oracle.compression leftView leftProof = some (root, leftRest))
    (rightAccepted : capDecode oracle.compression rightView rightProof = some (root, rightRest))
    (leftKnown : capLeafValue leftView (capRequestedPath index) =
      some (climb oracle.compression (leafDigest oracle.compression leftSalt leftValue) leftLower))
    (rightKnown : capLeafValue rightView (capRequestedPath index) =
      some (climb oracle.compression (leafDigest oracle.compression rightSalt rightValue) rightLower))
    (different : leftValue ≠ rightValue) :
    ∃ leftCapInputs rightCapInputs : List (BitVec 512),
      oracle.run (capReplayQ leftView leftProof) =
        pure (some (root, leftRest, leftCapInputs), leftCapInputs.length) ∧
      oracle.run (capReplayQ rightView rightProof) =
        pure (some (root, rightRest, rightCapInputs), rightCapInputs.length) ∧
      ∃ input ∈ openingInputs oracle.compression leftSalt leftValue leftLower ++ leftCapInputs,
        ∃ input' ∈ openingInputs oracle.compression rightSalt rightValue rightLower ++ rightCapInputs,
          input ≠ input' ∧ oracle.compression input = oracle.compression input' := by
  obtain ⟨leftCapInputs, leftRun, leftUpper, leftLength, leftBits, leftRoot, leftIncluded⟩ :=
    cap_accepted_replay_path oracle leftView leftProof leftRest root leftAccepted
      (capRequestedPath index) _ leftKnown
  obtain ⟨rightCapInputs, rightRun, rightUpper, rightLength, rightBits, rightRoot, rightIncluded⟩ :=
    cap_accepted_replay_path oracle rightView rightProof rightRest root rightAccepted
      (capRequestedPath index) _ rightKnown
  have directions : (leftLower ++ leftUpper).map Prod.fst =
      (rightLower ++ rightUpper).map Prod.fst := by
    simp only [List.map_append, leftDirections, rightDirections, leftBits, rightBits]
  have roots : climb oracle.compression (leafDigest oracle.compression leftSalt leftValue)
      (leftLower ++ leftUpper) =
      climb oracle.compression (leafDigest oracle.compression rightSalt rightValue)
        (rightLower ++ rightUpper) := by
    simpa only [climb, List.foldl_append] using leftRoot.trans rightRoot.symm
  obtain ⟨input, leftMember, input', rightMember, collision⟩ :=
    collision_of_openings_eq oracle.compression leftSalt rightSalt leftValue rightValue
      (leftLower ++ leftUpper) (rightLower ++ rightUpper) directions different roots
  exact ⟨leftCapInputs, rightCapInputs, leftRun, rightRun, input,
    cap_opening_inputs_subset _ _ _ _ _ _ leftIncluded input leftMember, input',
    cap_opening_inputs_subset _ _ _ _ _ _ rightIncluded input' rightMember, collision⟩
end CommitGolfCandidate
