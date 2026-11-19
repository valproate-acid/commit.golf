import CommitGolfCandidate.TwoPermutationPackedCheckerFromRecord
import CommitGolfCandidate.TwoPermutationPackedRecordComposition
import CommitGolfCandidate.TwoPermutationPackedLeafComplete
import CommitGolfCandidate.TwoPermutationPackedLowerAdapter
import CommitGolfCandidate.TwoPermutationPackedLevel

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf RiscvZkvm.Rv64
open TwoPermutationPrototype.Sampling (PinnedReplayBound)

theorem checker_from_phases (bound : PinnedReplayBound) (leaf : Oracle → Nat → Index → MachineState → RecordBlock)
    (step : Oracle → Nat → Index → Nat → MachineState → RecordBlock)
    (leafVerified : LeafBlockRefines leaf) (stepVerified : LowerStepRefines step) :
    PackedCertificate.CheckerFacts PackedChecker.submission :=
  checker_facts_from_record bound (joinedRecord leaf step) (joined_record_refines leaf step leafVerified stepVerified)

theorem executable_checker_facts (bound : PinnedReplayBound) : PackedCertificate.CheckerFacts PackedChecker.submission :=
  checker_from_phases bound RecordLeaf.block (adaptLowerStep levelResult) RecordLeaf.actual_leaf_block
    (lower_step_from_level levelResult levelFacts)

end TwoPermutationPrototype.Packed.Checker
