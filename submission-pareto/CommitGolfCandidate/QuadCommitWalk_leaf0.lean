import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem leaf_block_0 : walk 32 Artifact.commitCode leafWords 19 (List.range' 0 128) = some 1430 := by
  decide +kernel
theorem leaf_block_128 : walk 32 Artifact.commitCode leafWords 1430 (List.range' 128 128) = some 2841 := by
  decide +kernel
theorem leaf_block_256 : walk 32 Artifact.commitCode leafWords 2841 (List.range' 256 128) = some 4253 := by
  decide +kernel
theorem leaf_block_384 : walk 32 Artifact.commitCode leafWords 4253 (List.range' 384 128) = some 5664 := by
  decide +kernel
theorem leaf_block_512 : walk 32 Artifact.commitCode leafWords 5664 (List.range' 512 128) = some 7076 := by
  decide +kernel
theorem leaf_block_640 : walk 32 Artifact.commitCode leafWords 7076 (List.range' 640 128) = some 8487 := by
  decide +kernel
theorem leaf_block_768 : walk 32 Artifact.commitCode leafWords 8487 (List.range' 768 128) = some 9898 := by
  decide +kernel
theorem leaf_block_896 : walk 32 Artifact.commitCode leafWords 9898 (List.range' 896 128) = some 11309 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
