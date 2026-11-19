import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n1s_block_26112 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 123562 (List.range' 26112 512) = some 125098 := by
  decide +kernel
theorem n1s_block_26624 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 125098 (List.range' 26624 512) = some 126634 := by
  decide +kernel
theorem n1s_block_27136 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 126634 (List.range' 27136 512) = some 128170 := by
  decide +kernel
theorem n1s_block_27648 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 128170 (List.range' 27648 512) = some 129706 := by
  decide +kernel
theorem n1s_block_28160 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 129706 (List.range' 28160 512) = some 131242 := by
  decide +kernel
theorem n1s_block_28672 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 131242 (List.range' 28672 512) = some 132778 := by
  decide +kernel
theorem n1s_block_29184 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 132778 (List.range' 29184 246) = some 133516 := by
  decide +kernel
theorem n1r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 133518 (List.range' 0 424) = some 134790 := by
  decide +kernel
theorem n2s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 134803 (List.range' 0 512) = some 136339 := by
  decide +kernel
theorem n2s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 136339 (List.range' 512 512) = some 137875 := by
  decide +kernel
theorem n2s_block_1024 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 137875 (List.range' 1024 512) = some 139411 := by
  decide +kernel
theorem n2s_block_1536 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 139411 (List.range' 1536 512) = some 140947 := by
  decide +kernel
theorem n2s_block_2048 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 140947 (List.range' 2048 512) = some 142483 := by
  decide +kernel
theorem n2s_block_2560 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 142483 (List.range' 2560 512) = some 144019 := by
  decide +kernel
theorem n2s_block_3072 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 144019 (List.range' 3072 512) = some 145555 := by
  decide +kernel
theorem n2s_block_3584 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 145555 (List.range' 3584 512) = some 147091 := by
  decide +kernel
theorem n2s_block_4096 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 147091 (List.range' 4096 512) = some 148627 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
