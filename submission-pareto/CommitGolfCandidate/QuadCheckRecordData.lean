import CommitGolfCandidate.QuadHonestInput

/-! Honest record fields, read in a machine state that frames the remaining proof. -/
namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (honestIndex)
open TwoPermutationPrototype.Quad.Honest (honest_input_nonce honest_input_sibling)
set_option maxRecDepth 8192
set_option maxHeartbeats 1100000

theorem quad_record_nonce (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape)
    (ordinal : Nat) (present : ordinal < positions.card) (state : MachineState)
    (framed : RecordInputFrame (honestCheckInput oracle message positions salts) ordinal state) :
    readBuffer state (checkProofByte ordinal) 16 = salts (honestIndex positions ordinal present) := by
  let input := honestCheckInput oracle message positions salts
  have card := checker_positions_bound input
  have fit : checkProofByte ordinal+0+16 ≤ 2^36 := by
    change positions.card ≤ 16777216 at card
    unfold checkProofByte
    omega
  have frame := record_proof_frame input ordinal 0 16 state framed (Nat.le_of_lt present) fit
  have loaded := honest_input_nonce oracle message positions salts ordinal present
  rw [Nat.add_zero] at frame
  exact frame.trans loaded

theorem quad_record_sibling (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal level child : Nat) (present : ordinal<positions.card)
    (deep : level<11) (which : child<4)
    (state : MachineState) (framed : RecordInputFrame (honestCheckInput oracle message positions salts) ordinal state) :
    readBuffer state (checkProofByte ordinal+(16+128*level+32*child)) 32 =
      pentaNode (Honest.honestPenta oracle) (Honest.honestLeaves oracle message salts) level
        (pentaNeighbour (honestIndex positions ordinal present) level child) := by
  let input := honestCheckInput oracle message positions salts
  have card := checker_positions_bound input
  have fit : checkProofByte ordinal+(16+128*level+32*child)+32≤2^36 := by
    change positions.card≤16777216 at card
    unfold checkProofByte
    omega
  have frame := record_proof_frame input ordinal (16+128*level+32*child) 32 state framed (Nat.le_of_lt present) fit
  have loaded := honest_input_sibling oracle message positions salts ordinal level child present deep which
  have addr : loaderReference.layout.proof+(1424*ordinal+16+128*level+32*child)=
      checkProofByte ordinal+(16+128*level+32*child) := by
    change 10804535392+(1424*ordinal+16+128*level+32*child)=10804535392+1424*ordinal+(16+128*level+32*child)
    omega
  rw [addr] at loaded
  exact frame.trans loaded

end TwoPermutationPrototype.Quad.Checker
