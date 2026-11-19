import CommitGolfCandidate.TwoPermutationCheckLoader
import CommitGolfCandidate.TwoPermutationCheckerReplay

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.Sampling

theorem check_observation_admitted (oracle : Oracle) (input : CheckInput)
    (admitted : input.proof.length ≤ Assembly.submission.sizes.proof) :
    checkObservation Assembly.submission oracle input =
      checkEvaluation oracle (recordRows
        (execute checkerImage 17179934720 (Assembly.submission.initialState .check input) false)) := by
  unfold checkObservation
  erw [check_run_admitted input admitted]

theorem check_observation_oversized (oracle : Oracle) (input : CheckInput)
    (oversized : Assembly.submission.sizes.proof < input.proof.length) :
    checkObservation Assembly.submission oracle input = ((⟨.failure,initialMachine,0,0⟩,[]),0) := by
  unfold checkObservation
  erw [check_run_oversized input oversized]
  rw [record_rows_pure, check_evaluation_pure]

end TwoPermutationPrototype.Checker
