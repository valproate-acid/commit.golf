import CommitGolfCandidate.TwoPermutationCollectInput

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Checker (checkIndexWord checkSourceWord)

def checkProofByte (ordinal : Nat) : Nat := 10334769248+498*ordinal

/-- The packed checker cursor points to byte-aligned 498-byte records. -/
structure RecordCursor (input : CheckInput) (ordinal : Nat) (state : MachineState) : Prop where
  pc : state.pc = if ordinal = input.positions.card then 0x1444 else 0x1058
  index : state.getReg .x8 = wordAddress (checkIndexWord ordinal)
  value : state.getReg .x19 = wordAddress (checkSourceWord ordinal)
  proof : state.getReg .x21 = BitVec.ofNat 64 (checkProofByte ordinal)
  remaining : state.getReg .x18 = BitVec.ofNat 64 (input.positions.card-ordinal)
  tag : state.getReg .x3 = 4056
  commitment : state.getReg .x9 = 4294971392
  challengeLength : state.getReg .x20 = BitVec.ofNat 64 LENGTH
  proofEnd : state.getReg .x22 = BitVec.ofNat 64 (10334769248+input.proof.length)
  digest : state.getReg .x23 = wordAddress 1536
  pair : state.getReg .x24 = wordAddress 1568
  capRoots : state.getReg .x25 = wordAddress 2048
  marks : state.getReg .x26 = wordAddress 512
  capCount : state.getReg .x27 = 256
  selector : state.getReg .x5 = 0
  nonceScratch : state.getReg .x4 = 12272

end TwoPermutationPrototype.Packed.Checker
