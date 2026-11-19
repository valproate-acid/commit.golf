import CommitGolfCandidate.QuadInputFrame

namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64

def ProofWithin (input : CheckInput) : Prop :=
  1424*input.positions.card≤ input.proof.length ∧ input.proof.length≤1424*2^24

theorem quad_record_geometry (input : CheckInput) (ordinal : Nat)
    (present : ordinal< input.positions.card) (fits : ProofWithin input) :
    checkProofByte ordinal%2=0 ∧
      checkProofByte ordinal+1424≤10804535392+input.proof.length ∧
      32768≤checkProofByte ordinal ∧ checkProofByte ordinal+1424≤MEMORY_BYTES ∧
      checkSourceWord ordinal+37≤2^33 := by
  have count := checker_positions_bound input
  obtain ⟨atLeast,atMost⟩ := fits
  unfold checkProofByte checkSourceWord MEMORY_BYTES
  omega

theorem check_proof_byte_aligned (ordinal : Nat) : checkProofByte ordinal%8=0 := by
  unfold checkProofByte
  omega

end TwoPermutationPrototype.Quad.Checker
