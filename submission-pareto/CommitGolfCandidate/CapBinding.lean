import CommitGolfCandidate.CapReplay

/-! Collision extraction from two arbitrary accepted cap proofs. These lemmas
account for paid replay traces but do not yet instantiate the full machine
binding game or its detector probability theorem. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp

theorem cap_replay_height_seven_bound (view : CapView 8) (proof : List Digest) :
    IsTotalQueryBound (capReplayQ view proof) 255 := by
  apply (cap_replay_query_bound view proof).mono
  simpa using cap_calls_full_bound view

/-- Different known roots at the same cap leaf, accepted against one commitment,
yield a compression collision among the two actual cap replay input lists. -/
theorem cap_known_root_collision (oracle : Oracle) {height : Nat}
    (leftView rightView : CapView height) (leftProof rightProof leftRest rightRest : List Digest)
    (root leftValue rightValue : Digest) (path : Path height)
    (leftAccepted : capDecode oracle.compression leftView leftProof = some (root, leftRest))
    (rightAccepted : capDecode oracle.compression rightView rightProof = some (root, rightRest))
    (leftKnown : capLeafValue leftView path = some leftValue)
    (rightKnown : capLeafValue rightView path = some rightValue)
    (different : leftValue ≠ rightValue) :
    ∃ leftInputs rightInputs : List (BitVec 512),
      oracle.run (capReplayQ leftView leftProof) =
        pure (some (root, leftRest, leftInputs), leftInputs.length) ∧
      oracle.run (capReplayQ rightView rightProof) =
        pure (some (root, rightRest, rightInputs), rightInputs.length) ∧
      ∃ input ∈ leftInputs, ∃ input' ∈ rightInputs,
        input ≠ input' ∧ oracle.compression input = oracle.compression input' := by
  obtain ⟨leftInputs, leftRun, leftPath, leftLength, leftBits, leftRoot, leftIncluded⟩ :=
    cap_accepted_replay_path oracle leftView leftProof leftRest root leftAccepted path leftValue leftKnown
  obtain ⟨rightInputs, rightRun, rightPath, rightLength, rightBits, rightRoot, rightIncluded⟩ :=
    cap_accepted_replay_path oracle rightView rightProof rightRest root rightAccepted path rightValue rightKnown
  obtain ⟨input, leftMember, input', rightMember, collision⟩ :=
    collision_of_climb_eq oracle.compression leftValue rightValue leftPath rightPath
      (leftBits.trans rightBits.symm) different (leftRoot.trans rightRoot.symm)
  exact ⟨leftInputs, rightInputs, leftRun, rightRun, input, leftIncluded input leftMember,
    input', rightIncluded input' rightMember, collision⟩
end CommitGolfCandidate
