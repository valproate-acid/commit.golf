import CommitGolf.Artifact
import CommitGolfCandidate.QuadOpeningABI
import CommitGolfCandidate.QuadCheckImage

/-! The delivered quad submission: facts about `Artifact.submission` that do not depend on a
program's execution (admission, opening ABI, image identities). -/
namespace TwoPermutationPrototype.QuadCertificate
open CommitGolf CommitGolf.Riscv

set_option maxRecDepth 100000

abbrev quadSubmission : Submission := Artifact.submission

theorem quad_opening_image : quadSubmission.image .opening = QuadOpening.openingImage := by
  simp only [quadSubmission, Artifact.submission]; rfl

theorem quad_check_image : quadSubmission.image .check = Quad.Checker.quadCheckImage := by
  simp only [quadSubmission, Artifact.submission]; rfl

theorem quad_admitted : quadSubmission.Admission := by
  intro program
  cases program <;>
    simp only [quadSubmission, Artifact.submission, Image.Valid, Image.byteSize, LayoutValid,
      dataBase, ArtifactEncoding.length_decode] <;> decide

theorem quad_opening_abi : QuadOpening.OpeningABI quadSubmission where
  toOpeningLayout := ⟨rfl, rfl, rfl, rfl⟩
  image := quad_opening_image
  capacity := by decide
  fuel := by decide

end TwoPermutationPrototype.QuadCertificate
