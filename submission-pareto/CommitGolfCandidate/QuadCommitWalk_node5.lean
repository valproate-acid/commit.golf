import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n2s_block_13312 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 174739 (List.range' 13312 512) = some 176275 := by
  decide +kernel
theorem n2s_block_13824 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 176275 (List.range' 13824 512) = some 177811 := by
  decide +kernel
theorem n2s_block_14336 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 177811 (List.range' 14336 249) = some 178558 := by
  decide +kernel
theorem n2r_block_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 178560 (List.range' 0 179) = some 179097 := by
  decide +kernel
theorem n3s_block_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 179110 (List.range' 0 512) = some 180646 := by
  decide +kernel
theorem n3s_block_512 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 180646 (List.range' 512 512) = some 182182 := by
  decide +kernel
theorem n3s_block_1024 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 182182 (List.range' 1024 512) = some 183718 := by
  decide +kernel
theorem n3s_block_1536 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 183718 (List.range' 1536 512) = some 185254 := by
  decide +kernel
theorem n3s_block_2048 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 185254 (List.range' 2048 512) = some 186790 := by
  decide +kernel
theorem n3s_block_2560 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 186790 (List.range' 2560 512) = some 188326 := by
  decide +kernel
theorem n3s_block_3072 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 188326 (List.range' 3072 512) = some 189862 := by
  decide +kernel
theorem n3s_block_3584 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 189862 (List.range' 3584 512) = some 191398 := by
  decide +kernel
theorem n3s_block_4096 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 191398 (List.range' 4096 512) = some 192934 := by
  decide +kernel
theorem n3s_block_4608 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 192934 (List.range' 4608 512) = some 194470 := by
  decide +kernel
theorem n3s_block_5120 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 194470 (List.range' 5120 512) = some 196006 := by
  decide +kernel
theorem n3s_block_5632 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 196006 (List.range' 5632 512) = some 197542 := by
  decide +kernel
theorem n3s_block_6144 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 197542 (List.range' 6144 512) = some 199078 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
