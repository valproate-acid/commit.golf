import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n1s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 45226 (List.range' 0 512) = some 46762 := by
  decide +kernel
theorem n1s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 46762 (List.range' 512 512) = some 48298 := by
  decide +kernel
theorem n1s_block_1024 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 48298 (List.range' 1024 512) = some 49834 := by
  decide +kernel
theorem n1s_block_1536 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 49834 (List.range' 1536 512) = some 51370 := by
  decide +kernel
theorem n1s_block_2048 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 51370 (List.range' 2048 512) = some 52906 := by
  decide +kernel
theorem n1s_block_2560 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 52906 (List.range' 2560 512) = some 54442 := by
  decide +kernel
theorem n1s_block_3072 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 54442 (List.range' 3072 512) = some 55978 := by
  decide +kernel
theorem n1s_block_3584 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 55978 (List.range' 3584 512) = some 57514 := by
  decide +kernel
theorem n1s_block_4096 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 57514 (List.range' 4096 512) = some 59050 := by
  decide +kernel
theorem n1s_block_4608 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 59050 (List.range' 4608 512) = some 60586 := by
  decide +kernel
theorem n1s_block_5120 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 60586 (List.range' 5120 512) = some 62122 := by
  decide +kernel
theorem n1s_block_5632 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 62122 (List.range' 5632 512) = some 63658 := by
  decide +kernel
theorem n1s_block_6144 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 63658 (List.range' 6144 512) = some 65194 := by
  decide +kernel
theorem n1s_block_6656 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 65194 (List.range' 6656 512) = some 66730 := by
  decide +kernel
theorem n1s_block_7168 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 66730 (List.range' 7168 512) = some 68266 := by
  decide +kernel
theorem n1s_block_7680 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 68266 (List.range' 7680 512) = some 69802 := by
  decide +kernel
theorem n1s_block_8192 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 69802 (List.range' 8192 512) = some 71338 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
