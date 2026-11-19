import CommitGolfCandidate.TwoPermutationPackedCheckerObservation
import CommitGolfCandidate.TwoPermutationPackedCheckCapABI

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf RiscvZkvm.Rv64
open TwoPermutationPrototype.Sampling (PinnedReplayBound)

theorem checker_facts_from_record (bound : PinnedReplayBound) (record : Oracle → Nat → Index → MachineState → RecordBlock)
    (verified : RecordRefines record) : PackedCertificate.CheckerFacts PackedChecker.submission :=
  checker_facts_of_observations bound (checker_complete_observation record verified checker_cap_facts)

end TwoPermutationPrototype.Packed.Checker
