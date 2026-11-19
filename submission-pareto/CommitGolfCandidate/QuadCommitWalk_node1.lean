import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n1s_block_8704 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 71338 (List.range' 8704 512) = some 72874 := by
  decide +kernel
theorem n1s_block_9216 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 72874 (List.range' 9216 512) = some 74410 := by
  decide +kernel
theorem n1s_block_9728 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 74410 (List.range' 9728 512) = some 75946 := by
  decide +kernel
theorem n1s_block_10240 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 75946 (List.range' 10240 512) = some 77482 := by
  decide +kernel
theorem n1s_block_10752 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 77482 (List.range' 10752 512) = some 79018 := by
  decide +kernel
theorem n1s_block_11264 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 79018 (List.range' 11264 512) = some 80554 := by
  decide +kernel
theorem n1s_block_11776 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 80554 (List.range' 11776 512) = some 82090 := by
  decide +kernel
theorem n1s_block_12288 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 82090 (List.range' 12288 512) = some 83626 := by
  decide +kernel
theorem n1s_block_12800 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 83626 (List.range' 12800 512) = some 85162 := by
  decide +kernel
theorem n1s_block_13312 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 85162 (List.range' 13312 512) = some 86698 := by
  decide +kernel
theorem n1s_block_13824 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 86698 (List.range' 13824 512) = some 88234 := by
  decide +kernel
theorem n1s_block_14336 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 88234 (List.range' 14336 512) = some 89770 := by
  decide +kernel
theorem n1s_block_14848 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 89770 (List.range' 14848 512) = some 91306 := by
  decide +kernel
theorem n1s_block_15360 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 91306 (List.range' 15360 512) = some 92842 := by
  decide +kernel
theorem n1s_block_15872 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 92842 (List.range' 15872 512) = some 94378 := by
  decide +kernel
theorem n1s_block_16384 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 94378 (List.range' 16384 512) = some 95914 := by
  decide +kernel
theorem n1s_block_16896 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 95914 (List.range' 16896 512) = some 97450 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
