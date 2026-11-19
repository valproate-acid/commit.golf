import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem leaf_block_3072 : walk 32 Artifact.commitCode leafWords 33891 (List.range' 3072 128) = some 35303 := by
  decide +kernel
theorem leaf_block_3200 : walk 32 Artifact.commitCode leafWords 35303 (List.range' 3200 128) = some 36713 := by
  decide +kernel
theorem leaf_block_3328 : walk 32 Artifact.commitCode leafWords 36713 (List.range' 3328 128) = some 38125 := by
  decide +kernel
theorem leaf_block_3456 : walk 32 Artifact.commitCode leafWords 38125 (List.range' 3456 128) = some 39536 := by
  decide +kernel
theorem leaf_block_3584 : walk 32 Artifact.commitCode leafWords 39536 (List.range' 3584 128) = some 40948 := by
  decide +kernel
theorem leaf_block_3712 : walk 32 Artifact.commitCode leafWords 40948 (List.range' 3712 128) = some 42359 := by
  decide +kernel
theorem leaf_block_3840 : walk 32 Artifact.commitCode leafWords 42359 (List.range' 3840 128) = some 43771 := by
  decide +kernel
theorem leaf_block_3968 : walk 32 Artifact.commitCode leafWords 43771 (List.range' 3968 128) = some 45183 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
