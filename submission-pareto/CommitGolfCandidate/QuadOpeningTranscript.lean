import CommitGolfCandidate.QuadOpeningProofBytes
import CommitGolfCandidate.HidingDistribution
import CommitGolfCandidate.CompressionSampling

/-! Deliverables of the penta opener (see `QuadOpeningABI` for `OpeningABI`, `opening_physical`,
`opening_success`, `opening_scored_limits`; `QuadOpeningProofBytes` for `scheme_open_bytes`,
`opening_proof_size`; `QuadOpeningModel` for `proof_from_trapdoor_matches`). -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.Sampling OracleComp
open CommitGolfCandidate.Permutation.NonceChain (Key actualNonces)

local instance openingDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

private def firstIndices : Fin 128 ↪ Index where
  toFun i := ⟨i.val, by have := i.isLt; have : LENGTH = 16777216 := rfl; omega⟩
  inj' := by
    intro a b same
    have values := congrArg Fin.val same
    exact Fin.ext (by simpa using values)

/-- Every 128-position opening costs exactly 73,103 cycles and 182,272 bytes. -/
theorem opening_scored_attainment (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) :
    ∃ (positions : Positions) (result : Execution), positions.card = BATCH ∧
      s.run .opening (trapdoor, positions) = pure result ∧
      result.cycles = 73103 ∧ (s.readProof result).length = 182272 := by
  let positions : Positions := (Finset.univ : Finset (Fin 128)).map firstIndices
  have count : positions.card = 128 := by simp [positions]
  obtain ⟨result, run, physical⟩ := opening_physical s abi trapdoor positions
  refine ⟨positions, result, count, run, ?_, ?_⟩
  · rw [physical.cycles]
    simp [scheduledCycles, count]
  · rw [opening_proof_size s abi trapdoor positions result physical, physical.length]
    simp [proofLength, count]

/-- Compose the exact penta opener with the seed-keyed commit distribution supplied by the penta
commit proof (`PentaNonceCommitTranscript`). -/
theorem transcript_refines (s : Submission) (abi : OpeningABI s) (commit : PentaNonceCommitTranscript s) :
    PentaNonceTranscriptRefines s.scheme pentaTranscriptBuilder := by
  intro oracle message positions
  unfold executableTranscript
  rw [fixed_oracle_run_bind]
  apply ((commit.distribution oracle message).bind_left _).trans
  simp only [bind_assoc, pure_bind]
  apply EvalDistEq.bind_right
  intro k
  rw [scheme_open_bytes s abi, pure_bind, fixed_oracle_run_pure]
  have proof := proof_from_trapdoor_matches s (commit.trapdoor oracle message k) positions
    (pentaFunction oracle.permutation)
    (quadPublicLeaves oracle message (actualNonces oracle.permutation k)) (actualNonces oracle.permutation k)
    (fun level j hl hj => commit.node oracle message k level j hl hj)
    (fun index => commit.nonce oracle message k index)
  rw [proof]
  rfl

end TwoPermutationPrototype.QuadOpening
