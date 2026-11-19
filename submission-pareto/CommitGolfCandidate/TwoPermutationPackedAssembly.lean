import CommitGolfCandidate.TwoPermutationPinnedTranscript
import CommitGolfCandidate.TwoPermutationPackedCertificate
import CommitGolfCandidate.TwoPermutationPackedMeaning
import CommitGolfCandidate.TwoPermutationPackedOpeningTranscript

namespace TwoPermutationPrototype.PackedCertificate
open CommitGolf CommitGolf.Riscv OracleComp TwoPermutationPrototype.Sampling
open RV64 (packedSubmission PackedLeafExecution PackedLeafMeaning PackedCommitTranscript)

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem packed_admitted : packedSubmission.Admission := by
  intro program
  cases program <;>
    simp only [RV64.packedSubmission, Artifact.submission, Image.Valid, Image.byteSize, LayoutValid,
      dataBase, ArtifactEncoding.length_decode] <;> decide

theorem packed_opening_abi : PackedOpening.OpeningABI packedSubmission where
  toOpeningLayout := ⟨rfl, rfl, rfl, rfl⟩
  image := rfl
  capacity := by decide
  fuel := by decide

theorem packed_opening_facts (committed : PackedCommitTranscript) : OpeningFacts packedSubmission where
  runs trapdoor positions := by
    obtain ⟨result, run, physical⟩ :=
      PackedOpening.opening_physical packedSubmission packed_opening_abi trapdoor positions
    have successful := PackedOpening.opening_success packedSubmission packed_opening_abi trapdoor positions result physical
    refine ⟨result, run, physical.success, successful, fun batch => ?_⟩
    have limits := PackedOpening.opening_scored_limits packedSubmission trapdoor positions result physical batch
    have length := PackedOpening.opening_proof_size packedSubmission packed_opening_abi trapdoor positions result physical
    exact ⟨limits.1, length.trans_le limits.2⟩
  refines := PackedOpening.transcript_refines packedSubmission packed_opening_abi
    committed.trapdoor committed.distribution committed.nonce committed.heap

theorem packed_commit_resources (leaves : PackedLeafExecution) (message : Message)
    (result : Execution) (reachable : result ∈ support (packedSubmission.run .commit message)) :
    result.exit = .success ∧ result.cycles = 637936351 ∧ result.oracleCalls = 50331647 := by
  have entry : RV64.CommitEntry (packedSubmission.initialState .commit message) := ⟨rfl,rfl,rfl,rfl⟩
  erw [RV64.packed_submission_wide_commit_run leaves packedSubmission RV64.packed_manifest_image.symm
    (by decide) message entry] at reachable
  simp only [RV64.packed_wideCommitTrace, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨salts,_,state,_,rfl⟩ := reachable
  exact ⟨rfl,rfl,rfl⟩

theorem packed_certificate (leaves : PackedLeafExecution) (meaning : PackedLeafMeaning leaves)
    (checks : CheckerFacts packedSubmission)
    (privateView : packedSubmission.scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120))) :
    Certificate packedSubmission 67584 637936351 88311 :=
  certificate_of_facts (packed_commit_resources leaves) packed_admitted
    (packed_opening_facts (RV64.packedVerifiedTranscript leaves meaning)) checks privateView

end TwoPermutationPrototype.PackedCertificate
