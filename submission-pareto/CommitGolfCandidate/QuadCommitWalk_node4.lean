import CommitGolf.Artifact
import CommitGolfCandidate.QuadCommitImage
import CommitGolfCandidate.QuadArtifactWalk
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem n2s_block_4608 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 148627 (List.range' 4608 512) = some 150163 := by
  decide +kernel
theorem n2s_block_5120 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 150163 (List.range' 5120 512) = some 151699 := by
  decide +kernel
theorem n2s_block_5632 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 151699 (List.range' 5632 512) = some 153235 := by
  decide +kernel
theorem n2s_block_6144 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 153235 (List.range' 6144 512) = some 154771 := by
  decide +kernel
theorem n2s_block_6656 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 154771 (List.range' 6656 512) = some 156307 := by
  decide +kernel
theorem n2s_block_7168 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 156307 (List.range' 7168 512) = some 157843 := by
  decide +kernel
theorem n2s_block_7680 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 157843 (List.range' 7680 512) = some 159379 := by
  decide +kernel
theorem n2s_block_8192 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 159379 (List.range' 8192 512) = some 160915 := by
  decide +kernel
theorem n2s_block_8704 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 160915 (List.range' 8704 512) = some 162451 := by
  decide +kernel
theorem n2s_block_9216 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 162451 (List.range' 9216 512) = some 163987 := by
  decide +kernel
theorem n2s_block_9728 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 163987 (List.range' 9728 512) = some 165523 := by
  decide +kernel
theorem n2s_block_10240 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 165523 (List.range' 10240 512) = some 167059 := by
  decide +kernel
theorem n2s_block_10752 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 167059 (List.range' 10752 512) = some 168595 := by
  decide +kernel
theorem n2s_block_11264 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 168595 (List.range' 11264 512) = some 170131 := by
  decide +kernel
theorem n2s_block_11776 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 170131 (List.range' 11776 512) = some 171667 := by
  decide +kernel
theorem n2s_block_12288 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 171667 (List.range' 12288 512) = some 173203 := by
  decide +kernel
theorem n2s_block_12800 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 173203 (List.range' 12800 512) = some 174739 := by
  decide +kernel
end TwoPermutationPrototype.ArtifactMatchB
