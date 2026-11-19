import CommitGolfCandidate.TwoPermutationPackedLeafMeaning

/-! The production-width commitment trace and canonical heap/nonce transcript for the exact
packed manifest. Every input to `packedVerifiedTranscript` is provided by the physical leaf
execution and memory induction checked in this module's dependencies. -/
namespace TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolf CommitGolf.Riscv OracleComp

noncomputable def executableTranscript : PackedCommitTranscript :=
  packedVerifiedTranscript executableLeaves executableMeaning

theorem exact_commit_run (message : Message) :
    packedSubmission.run .commit message =
      packed_wideCommitTrace executableLeaves (packedSubmission.initialState .commit message) :=
  packed_submission_wide_commit_run executableLeaves packedSubmission packed_manifest_image.symm
    (by decide) message ⟨rfl,rfl,rfl,rfl⟩

end TwoPermutationPrototype.RV64.PackedLeaves
