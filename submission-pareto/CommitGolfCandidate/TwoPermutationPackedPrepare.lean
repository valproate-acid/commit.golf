import CommitGolfCandidate.TwoPermutationPackedPair
import CommitGolfCandidate.TwoPermutationPackedLevelSpec

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
attribute [local irreducible] execute readBuffer childCopied siblingState merge

def prepare (s : MachineState) (node left : Nat) : MachineState :=
  let leaf := decide (left=16)
  let even := decide (node%2=0)
  hashSetup (route (merge (dispatch s leaf even) leaf even) leaf even)

def prepareCost (node left : Nat) : Nat :=
  let leaf := decide (left=16)
  let even := decide (node%2=0)
  5+(8+siblingCost leaf)+routeCost leaf even+2

structure PrepareFacts (s h : MachineState) (node proof left : Nat) : Prop where
  run : GroupHop s h (prepareCost node left)
  pc : h.pc=5032
  src : h.getReg .x10=12544
  dst : h.getReg .x12=12288
  widthReg : h.getReg .x30=BitVec.ofNat 64 (width (decide (left=16)))
  reg : ∀ r, r≠.x10 → r≠.x12 → r≠.x31 → r≠.x7 → r≠.x30 → h.getReg r=s.getReg r
  frame : ∀ w<2^61, w<1568 ∨ 1576≤w → memoryView h w=memoryView s w
  input : readBuffer h 12576 32 ++ readBuffer h 12544 32=levelPair s node proof left

private theorem dispatch_reg (s : MachineState) (leaf even : Bool) (r : Reg) (q : r≠.x7) (t : r≠.x30) :
    (dispatch s leaf even).getReg r=s.getReg r := by
  simp only [dispatch,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm q),MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm t)]

private theorem route_reg (s : MachineState) (leaf even : Bool) (r : Reg) : (route s leaf even).getReg r=s.getReg r := by
  unfold route; split <;> rfl

private theorem route_mem (s : MachineState) (leaf even : Bool) : (route s leaf even).mem=s.mem := by
  unfold route; split <;> rfl

private theorem hash_reg (s : MachineState) (r : Reg) (a : r≠.x10) (b : r≠.x12) :
    (hashSetup s).getReg r=s.getReg r := by
  simp only [hashSetup,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm b),MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm a)]

private theorem hash_regs (s : MachineState) : (hashSetup s).getReg .x10=s.getReg .x24 ∧
    (hashSetup s).getReg .x12=s.getReg .x23 := by
  simp only [hashSetup,MachineState.getReg_setPC,Opening.getReg_setReg]
  simp

private theorem same_buffer {s t : MachineState} (mem : s.mem=t.mem) (base sz : Nat) :
    readBuffer s base sz=readBuffer t base sz := by unfold readBuffer; simp only [MachineState.getByte,MachineState.getMem,mem]

theorem prepare_facts (s : MachineState) (node proof left : Nat) (ready : LevelReady s node proof left) :
    PrepareFacts s (prepare s node left) node proof left := by
  let leaf := decide (left=16)
  let even := decide (node%2=0)
  let d := dispatch s leaf even
  let m := merge d leaf even
  let r := route m leaf even
  let h := hashSetup r
  have cnt : (leaf=true) ↔ s.getReg .x29=16 := by
    have h := ready.leftBound
    rw [ready.counter,←BitVec.toNat_inj,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : left<2^64)]
    exact decide_eq_true_iff
  have par : (even=true) ↔ s.getReg .x6 &&& 1=0 := by
    rw [ready.nodeReg,←BitVec.toNat_inj,BitVec.toNat_and,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ready.nodeBound]
    change (decide (node%2=0)=true) ↔ node &&& 1=0
    rw [Nat.and_one_is_mod,decide_eq_true_iff]
  have dp := execute_dispatch s leaf even ready.pc cnt par
  have mg : MergeFacts d m leaf even proof := merge_facts d leaf even proof rfl
    ((dispatch_reg _ _ _ _ (by decide) (by decide)).trans ready.proofReg)
    ((dispatch_reg _ _ _ _ (by decide) (by decide)).trans ready.digest)
    ((dispatch_reg _ _ _ _ (by decide) (by decide)).trans ready.pair) ready.above ready.even ready.room
  have runR := route_run m leaf even mg.pc
  have rpc : r.pc=5024 := route_pc m leaf even mg.pc
  have hashHop : GroupHop r h 2 := execute_hash_setup r rpc
  have unchanged (reg : Reg) (a : reg≠.x31) (b : reg≠.x7) (c : reg≠.x30) : r.getReg reg=s.getReg reg :=
    (route_reg m leaf even reg).trans ((mg.register reg a).trans (dispatch_reg s leaf even reg b c))
  have mH : h.mem=m.mem := route_mem _ _ _
  have mD : d.mem=s.mem := rfl
  have pairChild : readBuffer h (8*slotWord (!even)) 32=readBuffer s 12288 32 :=
    (same_buffer mH _ _).trans (mg.child.trans (same_buffer mD _ _))
  have pairSib : readBuffer h (8*slotWord even) 32=wire s proof leaf := by
    refine (same_buffer mH _ _).trans (mg.sibling.trans ?_)
    unfold wire; split
    · exact same_buffer mD _ _
    · exact congrArg (fun x : BitVec 240 => 0#16 ++ x) (same_buffer mD _ _)
  refine ⟨GroupHop.thenDo (GroupHop.thenDo (GroupHop.thenDo dp mg.run) runR) hashHop,rfl,
    (hash_regs r).1.trans ((unchanged _ (by decide) (by decide) (by decide)).trans ready.pair),
    (hash_regs r).2.trans ((unchanged _ (by decide) (by decide) (by decide)).trans ready.digest),
    ?_,fun reg a b c e f => (hash_reg r reg a b).trans (unchanged reg c e f),?_,?_⟩
  · change h.getReg .x30=_
    rw [show h.getReg .x30=r.getReg .x30 from hash_reg r _ (by decide) (by decide),route_reg m leaf even,
      mg.register _ (by decide)]
    simp [d,dispatch,MachineState.getReg_setPC,Opening.getReg_setReg,leaf]
  · intro w wb safe
    change h.getMem (wordAddress w)=s.getMem (wordAddress w)
    exact (congrFun mH _).trans ((mg.frame w wb safe).trans (congrFun mD _))
  · change readBuffer h 12576 32 ++ readBuffer h 12544 32=pathPair node _ _
    by_cases e : node%2=0
    · have yes : even=true := decide_eq_true e
      rw [yes] at pairChild pairSib
      rw [pathPair,ite_eq_left e]
      exact congrArg₂ BitVec.append pairSib pairChild
    · have no : even=false := decide_eq_false e
      rw [no] at pairChild pairSib
      rw [pathPair,ite_eq_right e]
      exact congrArg₂ BitVec.append pairChild pairSib

end TwoPermutationPrototype.Packed.Checker
