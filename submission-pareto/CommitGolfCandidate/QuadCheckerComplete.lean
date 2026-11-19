import CommitGolfCandidate.QuadCheckerObservation

namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (checkObservation)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

/-- All checker facts for the actual penta image, with commit and opening images
left arbitrary for the final assembly. -/
theorem loader_checker_observation (oracle : Oracle) (input : CheckInput) :
    CheckerObservationFacts oracle input (checkObservation loaderReference oracle input) :=
  checker_complete_observation oracle input

/-- This reference already runs the exact penta checker and production loader. -/
theorem loader_checker_facts : QuadCertificate.CheckerFacts loaderReference :=
  checker_facts_of_observations loaderReference loader_checker_observation

/-- The production layout of the penta checker (message, commitment, trapdoor,
indices, values, proof): the quad base layout. -/
theorem loader_layout :
    loaderReference.layout = ⟨4096, 4294971392, 4294971424, 6375350304, 6509568096, 10804535392⟩ := rfl

/-- Final-image linking: only the actual checker dependencies are required. -/
theorem checker_facts (s : Submission)
    (capacity : s.sizes.proof = PENTA_PROOF_CAPACITY)
    (layout : s.layout = loaderReference.layout)
    (code : s.image .check = quadCheckImage)
    (fuel : s.steps .check = 34359803904) : QuadCertificate.CheckerFacts s := by
  apply checker_facts_of_observations s
  intro oracle input
  have same := checker_reference_run s quadCheckImage quadCheckImage 23890755584 34359803904
    capacity layout code fuel input
  have observed : checkObservation s oracle input = checkObservation loaderReference oracle input := by
    unfold checkObservation
    rw [same]
    rfl
  rw [observed]
  exact loader_checker_observation oracle input

end TwoPermutationPrototype.Quad.Checker
