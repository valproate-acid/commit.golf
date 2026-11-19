import CommitGolfCandidate.TwoPermutationCommitSetup
import CommitGolfCandidate.HeapModel

/-! A descending production parent consumes the two consecutive 32-byte child
digests, writes their compression at the parent, and retreats both cursors. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate (read_compression_halves)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] execute writeBits

def treeWord (n : Nat) := 516+32*2^24+4*n
def nodeDigest (s : MachineState) (n : Nat) := readBuffer s (8*treeWord n) 32
def parentInput (s : MachineState) (n : Nat) := readBuffer s (8*treeWord (2*n)) 64

theorem child_pair (s : MachineState) (n : Nat) :
    parentInput s n = nodeDigest s (2*n+1) ++ nodeDigest s (2*n) := by
  unfold parentInput nodeDigest
  rw [read_compression_halves s _ (by omega)]
  rw [show 8*treeWord (2*n+1)=8*treeWord (2*n)+32 by unfold treeWord;omega]

structure ParentRegs (s : MachineState) (n : Nat) : Prop where
  source : s.getReg .x10 = wordAddress (treeWord (2*n))
  target : s.getReg .x12 = wordAddress (treeWord n)
  selector : s.getReg .x5 = 0
  size : s.getReg .x11 = 64
  primitive : s.getReg .x13 = 0
  heap : s.getReg .x9 = wordAddress (treeWord 0)

def parentWritten (s : MachineState) (n : Nat) (reply : BitVec 256) :=
  writeBits s (wordAddress (treeWord n)) reply

def parentAfter (s : MachineState) (n : Nat) (reply : BitVec 256) :=
  execInstrBr (execInstrBr (parentWritten s n reply) (.ADDI .x10 .x10 4032)) (.ADDI .x12 .x12 4064)

theorem parent_call (s : MachineState) (n fuel : Nat) (bound : n < 2^24) (r : ParentRegs s n)
    (fetched : fetch commitImage s=some (.base .ECALL)) :
    execute commitImage (fuel+1) s true =
      (do let answer ← (liftM (World.query (.inr (.inl (parentInput s n)))) : OracleComp World (BitVec 256))
          let result ← execute commitImage fuel (parentWritten s n answer) true
          return result.charge 8 1) := by
  have src := word_address_value (word := treeWord (2*n)) (by unfold treeWord;omega)
  have dst := word_address_value (word := treeWord n) (by unfold treeWord;omega)
  have inRange : 8*treeWord (2*n)+64 ≤ MEMORY_BYTES := by unfold treeWord MEMORY_BYTES;omega
  have outRange : 8*treeWord n+32 ≤ MEMORY_BYTES := by unfold treeWord MEMORY_BYTES;omega
  have q : oracleInput s=some (.inl (parentInput s n)) := by
    have kind : (s.getReg .x13).toNat=0 := by rw [r.primitive];rfl
    unfold oracleInput
    dsimp only
    rw [kind]
    simp [r.source,r.target,r.size,COMPRESSION_INPUT_LENGTH,COMPRESSION_OUTPUT_LENGTH,
      rangeValid,src,dst,inRange,outRange,parentInput]

  simp [execute,fetched,r.selector,q,writeOracleAnswer,r.target,parentWritten,oracleCycles,COMPRESSION_CYCLES]
  rfl

def ParentFetched (pc : Word) : Prop :=
  ∀ s : MachineState,
    (s.pc=pc → fetch commitImage s=some (.base .ECALL)) ∧
    (s.pc=pc+4 → fetch commitImage s=some (.base (.ADDI .x10 .x10 4032))) ∧
    (s.pc=pc+8 → fetch commitImage s=some (.base (.ADDI .x12 .x12 4064)))

theorem parent_triple (s : MachineState) (n fuel : Nat) (pc : Word) (here : s.pc=pc) (bound : n<2^24)
    (r : ParentRegs s n) (fetched : ParentFetched pc) :
    execute commitImage (3+fuel) s true =
      (do let answer ← (liftM (World.query (.inr (.inl (parentInput s n)))) : OracleComp World (BitVec 256))
          let result ← execute commitImage fuel (parentAfter s n answer) true
          return result.charge 10 1) := by
  rw [show 3+fuel=(fuel+2)+1 by omega,parent_call s n _ bound r ((fetched s).1 here)]
  apply bind_congr_of_forall_mem_support
  intro answer _
  let a := parentWritten s n answer
  let b := execInstrBr a (.ADDI .x10 .x10 4032)
  have p1 : a.pc=pc+4 := by simp only [a,parentWritten,written_pc,here]
  have p2 : b.pc=pc+8 := by change a.pc+4=_; rw [p1,BitVec.add_assoc];rfl
  rw [CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ ((fetched a).2.1 p1) (show ordinaryStep a _=some b from rfl),
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ ((fetched b).2.2 p2) (show ordinaryStep b _=some (parentAfter s n answer) from rfl)]
  simp [instructionCycles,Execution.charge,←Nat.add_assoc]

theorem parent_pc (s : MachineState) (n : Nat) (reply : BitVec 256) :
    (parentAfter s n reply).pc=s.pc+12 := by
  change (parentWritten s n reply).pc+4+4=s.pc+12
  rw [parentWritten,written_pc]
  rw [BitVec.add_assoc,BitVec.add_assoc];rfl

theorem next_parent_regs (s : MachineState) (n : Nat) (reply : BitVec 256) (r : ParentRegs s (n+1)) :
    ParentRegs (parentAfter s (n+1) reply) n := by
  have holds (reg : Reg) : (parentWritten s (n+1) reply).getReg reg=s.getReg reg :=
    CommitGolfCandidate.writeBits_register ..
  constructor
  · change (parentWritten s (n+1) reply).getReg .x10 + signExtend12 4032 = _
    rw [holds,r.source]
    have advance : treeWord (2*(n+1))=treeWord (2*n)+8 := by unfold treeWord;omega
    rw [advance,wordAddress_add,BitVec.add_assoc];simp [wordAddress,signExtend12]
  · change (parentWritten s (n+1) reply).getReg .x12 + signExtend12 4064 = _
    rw [holds,r.target]
    have advance : treeWord (n+1)=treeWord n+4 := by unfold treeWord;omega
    rw [advance,wordAddress_add,BitVec.add_assoc];simp [wordAddress,signExtend12]
  · exact (holds .x5).trans r.selector
  · exact (holds .x11).trans r.size
  · exact (holds .x13).trans r.primitive
  · exact (holds .x9).trans r.heap

end TwoPermutationPrototype.RV64
