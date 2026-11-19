import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n5r_block_1536 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 220928 (List.range' 1536 512) = some 222464 := by
  decide +kernel
theorem n5r_block_2048 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 222464 (List.range' 2048 512) = some 224000 := by
  decide +kernel
theorem n5r_block_2560 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 224000 (List.range' 2560 512) = some 225536 := by
  decide +kernel
theorem n5r_block_3072 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 225536 (List.range' 3072 512) = some 227072 := by
  decide +kernel
theorem n5r_block_3584 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 227072 (List.range' 3584 512) = some 228608 := by
  decide +kernel
theorem n5r_block_4096 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 228608 (List.range' 4096 512) = some 230144 := by
  decide +kernel
theorem n5r_block_4608 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 230144 (List.range' 4608 512) = some 231680 := by
  decide +kernel
theorem n5r_block_5120 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 231680 (List.range' 5120 249) = some 232427 := by
  decide +kernel
theorem n6r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 232440 (List.range' 0 512) = some 233976 := by
  decide +kernel
theorem n6r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 233976 (List.range' 512 512) = some 235512 := by
  decide +kernel
theorem n6r_block_1024 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 235512 (List.range' 1024 50) = some 235662 := by
  decide +kernel
theorem n7r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 235675 (List.range' 0 215) = some 236320 := by
  decide +kernel
theorem n8r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 236329 (List.range' 0 43) = some 236458 := by
  decide +kernel
theorem n9r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 236475 (List.range' 0 9) = some 236502 := by
  decide +kernel
theorem n10r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 236515 (List.range' 0 2) = some 236521 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
