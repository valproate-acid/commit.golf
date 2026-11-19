import CommitGolfCandidate.TwoPermutationPackedOperands
import CommitGolfCandidate.TwoPermutationPackedLowerControl

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

def mergeEnd (leaf even : Bool) : Nat :=
  if even then (siblingSite leaf even).start+siblingCost leaf else childSite leaf even+8

def merge (s : MachineState) (leaf even : Bool) : MachineState :=
  if even then siblingState (childCopied s (childSite leaf even)) leaf even
  else childCopied (siblingState s leaf even) (childSite leaf even)

theorem OperandFacts.read_outside {s t : MachineState} {steps next dest : Nat} {v : BitVec 256}
    (op : OperandFacts s t steps next dest v) (base count : Nat) (bound : base+count≤2^64)
    (away : base+count≤8*dest ∨ 8*(dest+4)≤base) : readBuffer t base count=readBuffer s base count := by
  unfold readBuffer
  apply congrArg (BitVec.ofNat _)
  apply Finset.sum_congr rfl
  intro i hi
  have hb := Finset.mem_range.mp hi
  rw [byte_eq_of_word_frame s t (base+i) (op.frame _ (by omega) (by omega))]

structure MergeFacts (s t : MachineState) (leaf even : Bool) (proof : Nat) : Prop where
  run : GroupHop s t (8+siblingCost leaf)
  pc : t.pc=BitVec.ofNat 64 (4096+4*mergeEnd leaf even)
  register : ∀ r, r≠.x31 → t.getReg r=s.getReg r
  child : readBuffer t (8*slotWord (!even)) 32=readBuffer s 12288 32
  sibling : readBuffer t (8*slotWord even) 32=wire s proof leaf
  frame : ∀ w<2^61, (w<1568 ∨ 1576≤w) → memoryView t w=memoryView s w

attribute [local irreducible] readBuffer childCopied siblingState execute

theorem merge_facts (s : MachineState) (leaf even : Bool) (proof : Nat)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*dispatchStart leaf even))
    (src : s.getReg .x21=BitVec.ofNat 64 proof) (child : s.getReg .x23=12288)
    (dst : s.getReg .x24=12544) (above : 32768≤proof) (aligned : proof%2=0)
    (room : proof+(if leaf then 32 else 30)≤MEMORY_BYTES) :
    MergeFacts s (merge s leaf even) leaf even proof := by
  have lim : MEMORY_BYTES<2^64 := by decide
  cases even with
  | true =>
    have c := child_operand s leaf true (by cases leaf <;> exact pc) child dst
    let t := childCopied s (childSite leaf true)
    have q := sibling_operand t leaf true proof (by cases leaf <;> exact c.pc)
      ((c.register _ (by decide)).trans src) ((c.register _ (by decide)).trans dst) above aligned room
    refine ⟨GroupHop.thenDo c.execute q.execute,q.pc,fun r h => (q.register r h).trans (c.register r h),
      ?_,?_,?_⟩
    · exact (q.read_outside 12544 32 (by decide) (Or.inl (by decide))).trans c.digest
    · refine q.digest.trans ?_
      unfold wire
      split
      · exact c.read_outside proof 32 (by split at room <;> omega) (Or.inr (by change 12576≤proof;omega))
      · apply congrArg (fun x : BitVec 240 => 0#16 ++ x)
        exact c.read_outside proof 30 (by split at room <;> omega) (Or.inr (by change 12576≤proof;omega))
    · intro w hw h
      exact (q.frame w hw (by change w<1572 ∨ 1572+4≤w; omega)).trans
        (c.frame w hw (by change w<1568 ∨ 1568+4≤w; omega))
  | false =>
    have q := sibling_operand s leaf false proof (by cases leaf <;> exact pc) src dst above aligned room
    let t := siblingState s leaf false
    have c := child_operand t leaf false (by cases leaf <;> exact q.pc)
      ((q.register _ (by decide)).trans child) ((q.register _ (by decide)).trans dst)
    refine ⟨?_,c.pc,fun r h => (c.register r h).trans (q.register r h),?_,?_,?_⟩
    · rw [Nat.add_comm 8]; exact GroupHop.thenDo q.execute c.execute
    · exact c.digest.trans (q.read_outside 12288 32 (by decide) (Or.inl (by decide)))
    · exact (c.read_outside 12544 32 (by decide) (Or.inl (by decide))).trans q.digest
    · intro w hw h
      exact (c.frame w hw (by change w<1572 ∨ 1572+4≤w; omega)).trans
        (q.frame w hw (by change w<1568 ∨ 1568+4≤w; omega))

def routeCost (leaf even : Bool) : Nat := if leaf&&even then 0 else 1
def route (s : MachineState) (leaf even : Bool) := if leaf&&even then s else s.setPC 5024

theorem route_pc (s : MachineState) (leaf even : Bool) (pc : s.pc=BitVec.ofNat 64 (4096+4*mergeEnd leaf even)) :
    (route s leaf even).pc=5024 := by cases leaf <;> cases even <;> first | rfl | exact pc

theorem route_run (s : MachineState) (leaf even : Bool) (pc : s.pc=BitVec.ofNat 64 (4096+4*mergeEnd leaf even)) :
    GroupHop s (route s leaf even) (routeCost leaf even) := by
  have jump (ord imm : Nat) (here : s.pc=BitVec.ofNat 64 (4096+4*ord)) (ordBound : ord<367)
      (fetched : (packedImage.code[ord]?).bind decodeInstruction=some (.base (.JAL .x0 (BitVec.ofNat 21 imm))))
      (landing : s.pc+signExtend21 (BitVec.ofNat 21 imm)=5024) :
      GroupHop s (s.setPC 5024) 1 := by
    intro fuel
    have ran : ordinaryStep s (.base (.JAL .x0 (BitVec.ofNat 21 imm)))=some (s.setPC 5024) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,MachineState.setReg,landing]
    rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ (fetch_at s ord _ ordBound here fetched) ran]
    rfl
  cases leaf <;> cases even
  · exact jump 107 500 pc (by decide) rfl (by rw [pc];rfl)
  · exact jump 147 340 pc (by decide) rfl (by rw [pc];rfl)
  · exact jump 191 164 pc (by decide) rfl (by rw [pc];rfl)
  · intro fuel
    simp [routeCost,route,Execution.charge]

end TwoPermutationPrototype.Packed.Checker
