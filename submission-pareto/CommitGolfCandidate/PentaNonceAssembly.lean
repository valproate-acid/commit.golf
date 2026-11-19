import CommitGolfCandidate.PentaNonceCertificate
import CommitGolfCandidate.QuadOpeningTranscript
import CommitGolfCandidate.PentaNonceSecurity

/-! Penta (5-ary) + NonceChain certificate assembly. Inputs: the penta opening ABI, the commit side's
`PentaNonceCommitTranscript`, its resource fact, and the penta checker facts. -/
namespace TwoPermutationPrototype.PentaNonceCertificate
open CommitGolf CommitGolf.Riscv OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.QuadCertificate (CheckerFacts)

set_option autoImplicit false

theorem penta_nonce_opening_facts (s : Submission) (abi : QuadOpening.OpeningABI s)
    (commit : PentaNonceCommitTranscript s) : OpeningFacts s 73103 182272 where
  runs trapdoor positions := by
    obtain ⟨result, run, physical⟩ := QuadOpening.opening_physical s abi trapdoor positions
    have successful := QuadOpening.opening_success s abi trapdoor positions result physical
    refine ⟨result, run, physical.success, successful, fun batch => ?_⟩
    have limits := QuadOpening.opening_scored_limits s trapdoor positions result physical batch
    have length := QuadOpening.opening_proof_size s abi trapdoor positions result physical
    exact ⟨limits.1, length.trans_le limits.2⟩
  refines := QuadOpening.transcript_refines s abi commit

/-- Penta (5-ary) + NonceChain certificate for any commit cycle count the commit image proves. -/
theorem penta_nonce_certificate (s : Submission) (admitted : s.Admission) (abi : QuadOpening.OpeningABI s)
    (commit : PentaNonceCommitTranscript s) (commitCycles : Nat)
    (resources : ∀ (message : Message) (result : Execution), result ∈ support (s.run .commit message) →
      result.exit = .success ∧ result.cycles = commitCycles ∧ result.oracleCalls ≤ COMMIT_BUDGET)
    (checks : CheckerFacts s) :
    Certificate s 182272 commitCycles 73103 :=
  let opens := penta_nonce_opening_facts s abi commit
  certificate_of_facts resources admitted opens checks
    (penta_nonce_hiding s.scheme opens.refines)

end TwoPermutationPrototype.PentaNonceCertificate
