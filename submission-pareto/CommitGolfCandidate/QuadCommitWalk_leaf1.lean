import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem leaf_block_1024 : walk 32 Artifact.commitCode leafWords 11309 (List.range' 1024 128) = some 12721 := by
  decide +kernel
theorem leaf_block_1152 : walk 32 Artifact.commitCode leafWords 12721 (List.range' 1152 128) = some 14132 := by
  decide +kernel
theorem leaf_block_1280 : walk 32 Artifact.commitCode leafWords 14132 (List.range' 1280 128) = some 15544 := by
  decide +kernel
theorem leaf_block_1408 : walk 32 Artifact.commitCode leafWords 15544 (List.range' 1408 128) = some 16955 := by
  decide +kernel
theorem leaf_block_1536 : walk 32 Artifact.commitCode leafWords 16955 (List.range' 1536 128) = some 18366 := by
  decide +kernel
theorem leaf_block_1664 : walk 32 Artifact.commitCode leafWords 18366 (List.range' 1664 128) = some 19777 := by
  decide +kernel
theorem leaf_block_1792 : walk 32 Artifact.commitCode leafWords 19777 (List.range' 1792 128) = some 21189 := by
  decide +kernel
theorem leaf_block_1920 : walk 32 Artifact.commitCode leafWords 21189 (List.range' 1920 128) = some 22600 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
