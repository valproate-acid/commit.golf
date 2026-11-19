import CommitGolfCandidate.QuadCheckImage
import CommitGolfCandidate.TwoPermutationPentaSpec
import CommitGolfCandidate.TwoPermutationCheckerReplay

/-! Checker-only linking interface. Commit/opening images remain parameters;
all honest-input statements use the shared PentaSpec transcript verbatim. -/
namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate
open TwoPermutationPrototype.Sampling
set_option autoImplicit false

/-- Checker reference at the shared PentaSpec trapdoor layout. The final proof
capacity and fuel can be supplied before commit/opening images are finalized. -/
def checkerReference (commitImage openingImage : Image) (proofCapacity checkFuel : Nat) : Submission where
  sizes := ⟨QUAD_TRAPDOOR_BYTES, proofCapacity⟩
  layout := ⟨4096, 4294971392, 4294971424,
    4294971424 + QUAD_TRAPDOOR_BYTES,
    4294971424 + QUAD_TRAPDOOR_BYTES + 2^27 + 64,
    4294971424 + QUAD_TRAPDOOR_BYTES + 2^27 + 64 + 2^32⟩
  image
    | .commit => commitImage
    | .opening => openingImage
    | .check => quadCheckImage
  steps
    | .commit => 1073807360
    | .opening => 17179934720
    | .check => checkFuel

/-- An honest checker input is exactly the PentaSpec path and frontier. -/
def honestCheckInput (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) : CheckInput :=
  let view := pentaHonestView pentaTranscriptBuilder
    (BiPermutation.equiv Block oracle.permutation) message positions salts
  ⟨view.1, positions, message.restrict positions, view.2⟩

structure CheckerFacts (s : Submission) : Prop where
  terminates : ∀ oracle input,
    (TwoPermutationPrototype.Checker.checkObservation s oracle input).1.1.exit ≠ .unfinished
  queryBudget : ∀ oracle input,
    (TwoPermutationPrototype.Checker.checkObservation s oracle input).2 ≤ 100*input.positions.card
  binding : s.scheme.Binding
  honestAccepted : ∀ oracle message positions salts,
    (TwoPermutationPrototype.Checker.checkObservation s oracle
      (honestCheckInput oracle message positions salts)).1.1.exit = .success

/-- Linking changes no checker execution when its four actual dependencies
(proof admission, loader layout, image bytes, and fuel) agree. -/
theorem checker_reference_run (s : Submission) (commitImage openingImage : Image)
    (proofCapacity checkFuel : Nat)
    (capacity : s.sizes.proof = proofCapacity)
    (layout : s.layout = (checkerReference commitImage openingImage proofCapacity checkFuel).layout)
    (code : s.image .check = quadCheckImage) (fuel : s.steps .check = checkFuel)
    (input : CheckInput) :
    s.run .check input = (checkerReference commitImage openingImage proofCapacity checkFuel).run .check input := by
  let ref := checkerReference commitImage openingImage proofCapacity checkFuel
  have buffers : s.inputBuffers .check input = ref.inputBuffers .check input := by
    unfold Submission.inputBuffers
    rw [layout]
  have initial : s.initialState .check input = ref.initialState .check input := by
    unfold Submission.initialState
    rw [buffers, code, layout]
    rfl
  unfold Submission.run
  dsimp only
  rw [capacity, code, fuel, initial]
  rfl

end TwoPermutationPrototype.Quad.Checker
