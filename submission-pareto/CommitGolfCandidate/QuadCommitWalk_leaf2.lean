import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem leaf_block_2048 : walk 32 Artifact.commitCode leafWords 22600 (List.range' 2048 128) = some 24012 := by
  decide +kernel
theorem leaf_block_2176 : walk 32 Artifact.commitCode leafWords 24012 (List.range' 2176 128) = some 25423 := by
  decide +kernel
theorem leaf_block_2304 : walk 32 Artifact.commitCode leafWords 25423 (List.range' 2304 128) = some 26835 := by
  decide +kernel
theorem leaf_block_2432 : walk 32 Artifact.commitCode leafWords 26835 (List.range' 2432 128) = some 28245 := by
  decide +kernel
theorem leaf_block_2560 : walk 32 Artifact.commitCode leafWords 28245 (List.range' 2560 128) = some 29657 := by
  decide +kernel
theorem leaf_block_2688 : walk 32 Artifact.commitCode leafWords 29657 (List.range' 2688 128) = some 31068 := by
  decide +kernel
theorem leaf_block_2816 : walk 32 Artifact.commitCode leafWords 31068 (List.range' 2816 128) = some 32480 := by
  decide +kernel
theorem leaf_block_2944 : walk 32 Artifact.commitCode leafWords 32480 (List.range' 2944 128) = some 33891 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
