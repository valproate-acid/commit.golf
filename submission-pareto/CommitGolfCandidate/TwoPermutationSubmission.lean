import CommitGolf.Statements
import CommitGolfCandidate.TwoPermutationOpeningABI
import CommitGolfCandidate.TwoPermutationCheckerImage

/-! A checker reference with the exact loader, opening, check image and fuel. The commit image is supplied independently. -/
namespace TwoPermutationPrototype.Assembly
open CommitGolf CommitGolf.Riscv OracleComp
set_option autoImplicit false

def checkerReference (commitImage : Image) : Submission where
  sizes := ⟨1610612736, 8858378240⟩
  layout := ⟨4096, 4294971392, 4294971424, 5905584160, 6039801952, 10334769248⟩
  image
    | .commit => commitImage
    | .opening => Opening.openingImage
    | .check => Checker.checkerImage
  steps
    | .commit => 1073807360
    | .opening => 8590000128
    | .check => 17179934720

/-- The checker proof uses no commitment execution. The generic certificate
transports its checker facts to the production submission. -/
abbrev submission : Submission := checkerReference ⟨[], []⟩

theorem opening_abi : Opening.OpeningABI submission where
  toOpeningLayout := ⟨rfl, rfl, rfl, rfl⟩
  image := rfl
  capacity := Nat.le_refl _
  fuel := Nat.le_refl _

/-- Only the check image, its ABI, proof admission, and check fuel affect
the trusted check run. Commit and opening code can be linked independently. -/
theorem checker_reference_run (s : Submission)
    (proofCapacity : s.sizes.proof = submission.sizes.proof)
    (layout : s.layout = submission.layout)
    (code : s.image .check = Checker.checkerImage)
    (fuel : s.steps .check = submission.steps .check)
    (input : CheckInput) : s.run .check input = submission.run .check input := by
  have buffers : s.inputBuffers .check input = submission.inputBuffers .check input := by
    unfold Submission.inputBuffers
    rw [layout]
  have initial : s.initialState .check input = submission.initialState .check input := by
    unfold Submission.initialState
    rw [buffers, code, layout]
    rfl
  unfold Submission.run
  dsimp only
  rw [proofCapacity, code, fuel, initial]
  rfl

end TwoPermutationPrototype.Assembly
