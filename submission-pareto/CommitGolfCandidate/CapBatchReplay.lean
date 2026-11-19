import CommitGolfCandidate.CapLowerReplay
import CommitGolfCandidate.CapRecordBinding

/-! Complete parsed-batch replay: all lower records are queried and duplicate
checked, then the shared cap is queried with strict suffix/root rejection.
This is the paid semantic bridge; byte parsing and image execution remain
separate obligations before instantiating the machine binding game. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec

def capReplayBatch (records : List CapLowerRecord) (proof : List Digest) (root : Digest) :
    OracleComp World (Option (List (BitVec 512))) := do
  let lowerResult ← capReplayLowerBatch records (fun _ => none)
  match lowerResult with
  | none => pure none
  | some (roots, lowerInputs) =>
      let capResult ← capReplayQ (capKnownView roots 8 0) proof
      return capResult.bind fun (reported, rest, capInputs) =>
        if reported = root ∧ rest = [] then some (lowerInputs ++ capInputs) else none

/-- The conservative ceiling counts every lower record, including duplicates,
and every internal cap node on all possible reply continuations. -/
theorem cap_replay_batch_query_bound (records : List CapLowerRecord)
    (proof : List Digest) (root : Digest) :
    IsTotalQueryBound (capReplayBatch records proof root) (24 * records.length + 255) := by
  unfold capReplayBatch
  apply isTotalQueryBound_bind (cap_replay_lower_batch_query_bound records (fun _ => none))
  intro lowerResult
  cases lowerResult with
  | none => trivial
  | some result =>
      rcases result with ⟨roots, lowerInputs⟩
      simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
        cap_replay_height_seven_bound (capKnownView roots 8 0) proof

theorem cap_lower_batch_known (compress : Compression) (records : List CapLowerRecord)
    (roots : CapRootMap)
    (accepted : capLowerBatchRoots compress records (fun _ => none) = some roots)
    (record : CapLowerRecord) (member : record ∈ records) :
    capLeafValue (capKnownView roots 8 0) (capRequestedPath record.index) =
      some (record.root compress) := by
  rw [cap_known_view_leaf, cap_requested_path_index, Nat.zero_add]
  exact cap_lower_batch_member compress records _ roots accepted record member

theorem cap_lower_batch_input_member (compress : Compression) (records : List CapLowerRecord)
    (record : CapLowerRecord) (member : record ∈ records)
    (input : BitVec 512) (queried : input ∈ record.inputs compress) :
    input ∈ capLowerBatchInputs compress records := by
  exact List.mem_flatMap.mpr ⟨record, member, queried⟩

/-- Successful decoding pays for the entire accepted lower and cap trace. The
cap trace length itself is the number of cap calls; no free query list is used. -/
theorem cap_replay_batch_run (oracle : Oracle) (records : List CapLowerRecord)
    (proof : List Digest) (root : Digest) (roots : CapRootMap)
    (lowerAccepted : capLowerBatchRoots oracle.compression records (fun _ => none) = some roots)
    (capAccepted : capDecode oracle.compression (capKnownView roots 8 0) proof = some (root, [])) :
    ∃ capInputs : List (BitVec 512),
      oracle.run (capReplayQ (capKnownView roots 8 0) proof) =
        pure (some (root, [], capInputs), capInputs.length) ∧
      oracle.run (capReplayBatch records proof root) =
        pure (some (capLowerBatchInputs oracle.compression records ++ capInputs),
          24 * records.length + capInputs.length) := by
  obtain ⟨capInputs, witness⟩ := cap_decode_witness oracle.compression
    (capKnownView roots 8 0) proof [] root capAccepted
  have capRun := cap_replay_witness_run oracle witness
  refine ⟨capInputs, capRun, ?_⟩
  simp only [capReplayBatch]
  erw [oracle_run_bind, cap_replay_lower_batch_run oracle records _ roots lowerAccepted]
  simp only [pure_bind]
  erw [oracle_run_bind, capRun]
  simp [oracle_run_pure]

/-- Any conflicting original values at one index yield a collision in the full
paid accepted batch traces. This includes equal cap roots with a collision in a
leaf chain or lower path, as well as different cap roots colliding in the cap. -/
theorem cap_batch_collision (oracle : Oracle)
    (leftRecords rightRecords : List CapLowerRecord)
    (leftProof rightProof : List Digest) (root : Digest)
    (leftRoots rightRoots : CapRootMap)
    (leftLower : capLowerBatchRoots oracle.compression leftRecords (fun _ => none) = some leftRoots)
    (rightLower : capLowerBatchRoots oracle.compression rightRecords (fun _ => none) = some rightRoots)
    (leftCap : capDecode oracle.compression (capKnownView leftRoots 8 0) leftProof = some (root, []))
    (rightCap : capDecode oracle.compression (capKnownView rightRoots 8 0) rightProof = some (root, []))
    (leftRecord rightRecord : CapLowerRecord)
    (leftMember : leftRecord ∈ leftRecords) (rightMember : rightRecord ∈ rightRecords)
    (sameIndex : leftRecord.index = rightRecord.index)
    (different : leftRecord.value ≠ rightRecord.value) :
    ∃ leftCapInputs rightCapInputs : List (BitVec 512),
      oracle.run (capReplayBatch leftRecords leftProof root) =
        pure (some (capLowerBatchInputs oracle.compression leftRecords ++ leftCapInputs),
          24 * leftRecords.length + leftCapInputs.length) ∧
      oracle.run (capReplayBatch rightRecords rightProof root) =
        pure (some (capLowerBatchInputs oracle.compression rightRecords ++ rightCapInputs),
          24 * rightRecords.length + rightCapInputs.length) ∧
      ∃ input ∈ capLowerBatchInputs oracle.compression leftRecords ++ leftCapInputs,
        ∃ input' ∈ capLowerBatchInputs oracle.compression rightRecords ++ rightCapInputs,
          input ≠ input' ∧ oracle.compression input = oracle.compression input' := by
  have rightDirections : rightRecord.path.map Prod.fst =
      (List.range 16).map leftRecord.index.val.testBit := by
    rw [cap_lower_path_directions, sameIndex]
  have rightKnown : capLeafValue (capKnownView rightRoots 8 0)
      (capRequestedPath leftRecord.index) = some (rightRecord.root oracle.compression) := by
    rw [sameIndex]
    exact cap_lower_batch_known _ _ _ rightLower _ rightMember
  obtain ⟨leftInputs, rightInputs, leftCapRun, rightCapRun,
      input, inputMember, input', inputMember', collision⟩ :=
    cap_record_collision oracle leftRecord.index
      (capKnownView leftRoots 8 0) (capKnownView rightRoots 8 0)
      leftProof rightProof [] [] root leftRecord.salt rightRecord.salt
      leftRecord.value rightRecord.value leftRecord.path rightRecord.path
      (cap_lower_path_directions leftRecord) rightDirections leftCap rightCap
      (cap_lower_batch_known _ _ _ leftLower _ leftMember) rightKnown different
  have leftBatch : oracle.run (capReplayBatch leftRecords leftProof root) =
      pure (some (capLowerBatchInputs oracle.compression leftRecords ++ leftInputs),
        24 * leftRecords.length + leftInputs.length) := by
    simp only [capReplayBatch]
    erw [oracle_run_bind, cap_replay_lower_batch_run oracle leftRecords _ leftRoots leftLower]
    simp only [pure_bind]
    erw [oracle_run_bind, leftCapRun]
    simp [oracle_run_pure]
  have rightBatch : oracle.run (capReplayBatch rightRecords rightProof root) =
      pure (some (capLowerBatchInputs oracle.compression rightRecords ++ rightInputs),
        24 * rightRecords.length + rightInputs.length) := by
    simp only [capReplayBatch]
    erw [oracle_run_bind, cap_replay_lower_batch_run oracle rightRecords _ rightRoots rightLower]
    simp only [pure_bind]
    erw [oracle_run_bind, rightCapRun]
    simp [oracle_run_pure]
  refine ⟨leftInputs, rightInputs, leftBatch, rightBatch, input, ?_, input', ?_, collision⟩
  · rcases List.mem_append.mp inputMember with lower | cap
    · exact List.mem_append_left _ (cap_lower_batch_input_member _ _ _ leftMember _ lower)
    · exact List.mem_append_right _ cap
  · rcases List.mem_append.mp inputMember' with lower | cap
    · exact List.mem_append_left _ (cap_lower_batch_input_member _ _ _ rightMember _ lower)
    · exact List.mem_append_right _ cap
end CommitGolfCandidate
