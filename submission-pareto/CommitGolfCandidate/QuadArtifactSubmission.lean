import CommitGolfCandidate.QuadCommitArtifactW
import CommitGolfCandidate.QuadSubmission

/-! The delivered artifact is exactly W3's parameterized quad submission, instantiated with the
quad opening and checker images. This lets W3's commit facts, stated for
`Quad.Commit.submission opening checker`, apply to `Artifact.submission`. -/
namespace TwoPermutationPrototype.QuadCertificate
open CommitGolf CommitGolf.Riscv

theorem artifact_is_quad :
    Artifact.submission =
      Quad.Commit.submission QuadOpening.openingImage Quad.Checker.quadCheckImage := by
  have commit := ArtifactMatchB.quad_commit_image
  have opening := quad_opening_image
  have check := quad_check_image
  have sizes : Artifact.submission.sizes =
      (Quad.Commit.submission QuadOpening.openingImage Quad.Checker.quadCheckImage).sizes := by
    simp only [Artifact.submission, Quad.Commit.submission]
  have layout : Artifact.submission.layout =
      (Quad.Commit.submission QuadOpening.openingImage Quad.Checker.quadCheckImage).layout := by
    simp only [Artifact.submission, Quad.Commit.submission]
  have image : Artifact.submission.image =
      (Quad.Commit.submission QuadOpening.openingImage Quad.Checker.quadCheckImage).image := by
    funext program
    cases program
    · exact commit
    · exact opening
    · exact check
  have steps : Artifact.submission.steps =
      (Quad.Commit.submission QuadOpening.openingImage Quad.Checker.quadCheckImage).steps := by
    funext program
    cases program <;> simp only [Artifact.submission, Quad.Commit.submission]
  cases hA : Artifact.submission with
  | mk s l i t =>
    rw [hA] at sizes layout image steps
    simp only at sizes layout image steps
    rw [sizes, layout, image, steps]

end TwoPermutationPrototype.QuadCertificate
