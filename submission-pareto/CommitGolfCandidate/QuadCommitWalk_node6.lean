import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n3s_block_6656 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 199078 (List.range' 6656 512) = some 200614 := by
  decide +kernel
theorem n3s_block_7168 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 200614 (List.range' 7168 512) = some 202150 := by
  decide +kernel
theorem n3s_block_7680 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 202150 (List.range' 7680 215) = some 202795 := by
  decide +kernel
theorem n3r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 202797 (List.range' 0 3) = some 202806 := by
  decide +kernel
theorem n4s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 202823 (List.range' 0 512) = some 204359 := by
  decide +kernel
theorem n4s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 204359 (List.range' 512 512) = some 205895 := by
  decide +kernel
theorem n4s_block_1024 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 205895 (List.range' 1024 512) = some 207431 := by
  decide +kernel
theorem n4s_block_1536 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 207431 (List.range' 1536 512) = some 208967 := by
  decide +kernel
theorem n4s_block_2048 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 208967 (List.range' 2048 512) = some 210503 := by
  decide +kernel
theorem n4s_block_2560 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 210503 (List.range' 2560 512) = some 212039 := by
  decide +kernel
theorem n4s_block_3072 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 212039 (List.range' 3072 512) = some 213575 := by
  decide +kernel
theorem n4s_block_3584 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 213575 (List.range' 3584 512) = some 215111 := by
  decide +kernel
theorem n4s_block_4096 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 215111 (List.range' 4096 374) = some 216233 := by
  decide +kernel
theorem n4r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 216235 (List.range' 0 24) = some 216307 := by
  decide +kernel
theorem n5r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 216320 (List.range' 0 512) = some 217856 := by
  decide +kernel
theorem n5r_block_512 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 217856 (List.range' 512 512) = some 219392 := by
  decide +kernel
theorem n5r_block_1024 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 219392 (List.range' 1024 512) = some 220928 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
