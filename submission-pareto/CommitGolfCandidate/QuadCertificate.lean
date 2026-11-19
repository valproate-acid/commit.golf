import CommitGolfCandidate.TwoPermutationPinnedTranscript
import CommitGolfCandidate.TwoPermutationPentaSpec
import CommitGolfCandidate.TwoPermutationTranscript
import CommitGolf.Statements
import CommitGolfCandidate.TwoPermutationCheckerReplay
import CommitGolfCandidate.CountingCoins
import CommitGolfCandidate.Machine

/-! The checker-side facts consumed by the certificate assembly: termination,
query budget, binding, and acceptance of the honest penta transcript. -/
namespace TwoPermutationPrototype.QuadCertificate
open CommitGolf CommitGolf.Riscv CommitGolfCandidate OracleComp TwoPermutationPrototype.Sampling

set_option autoImplicit false

/-- An honest checker input is exactly the shared penta records. -/
def honestCheckInput (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) : CheckInput :=
  let view := pentaHonestView pentaTranscriptBuilder
    (BiPermutation.equiv Block oracle.permutation) message positions salts
  ⟨view.1, positions, message.restrict positions, view.2⟩

structure CheckerFacts (s : Submission) : Prop where
  terminates : ∀ oracle input, (Checker.checkObservation s oracle input).1.1.exit ≠ .unfinished
  queryBudget : ∀ oracle input, (Checker.checkObservation s oracle input).2 ≤ 100*input.positions.card
  binding : s.scheme.Binding
  honestAccepted : ∀ oracle message positions salts,
    (Checker.checkObservation s oracle (honestCheckInput oracle message positions salts)).1.1.exit = .success

end TwoPermutationPrototype.QuadCertificate
