import CommitGolfCandidate.TwoPermutationPackedOperands
import CommitGolfCandidate.TwoPermutationPackedLowerControl
import CommitGolfCandidate.TwoPermutationPackedLowerRecursion

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate CommitGolfCandidate.ShortTree RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192

structure LevelReady (s : MachineState) (node proof left : Nat) : Prop where
  pc : s.pc=4348
  nodeReg : s.getReg .x6=BitVec.ofNat 64 node
  proofReg : s.getReg .x21=BitVec.ofNat 64 proof
  counter : s.getReg .x29=BitVec.ofNat 64 left
  digest : s.getReg .x23=12288
  pair : s.getReg .x24=12544
  selector : s.getReg .x5=0
  syscallBytes : s.getReg .x11=64
  syscallSelector : s.getReg .x13=0
  nodeBound : node<2^64
  leftPositive : 0<left
  leftBound : left≤16
  above : 32768≤proof
  even : proof%2=0
  room : proof+width (decide (left=16))≤MEMORY_BYTES

def levelPair (s : MachineState) (node proof left : Nat) :=
  pathPair node (readBuffer s 12288 32) (wire s proof (decide (left=16)))

structure LevelFacts (oracle : Oracle) (s : MachineState) (node proof left : Nat) (block : RecordBlock) : Prop where
  pc : block.state.pc=(if left=1 then 5056 else 4348)
  nodeReg : block.state.getReg .x6=BitVec.ofNat 64 (node/2)
  proofReg : block.state.getReg .x21=BitVec.ofNat 64 (proof+width (decide (left=16)))
  counter : block.state.getReg .x29=BitVec.ofNat 64 (left-1)
  syscallBytes : block.state.getReg .x11=64
  syscallSelector : block.state.getReg .x13=0
  saved : ∀ r, RecordSaved r → block.state.getReg r=s.getReg r
  frame : LowerFrame s block.state
  cost : block.steps≤116
  digest : readBuffer block.state 12288 32=padLow (oracle.compression (levelPair s node proof left))
  row : PublicRow.compression (levelPair s node proof left) (oracle.compression (levelPair s node proof left)) ∈ block.rows
  run : ∀ fuel,
    let tail := checkEvaluation oracle (recordRows (execute packedImage fuel block.state false))
    checkEvaluation oracle (recordRows (execute packedImage (block.steps+fuel) s false)) =
      ((tail.1.1.charge block.cycles 1,block.rows++tail.1.2),1+tail.2)

end TwoPermutationPrototype.Packed.Checker
