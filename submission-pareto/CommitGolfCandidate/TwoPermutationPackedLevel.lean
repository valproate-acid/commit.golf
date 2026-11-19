import CommitGolfCandidate.TwoPermutationPackedPrepare
import CommitGolfCandidate.TwoPermutationPackedParent
import CommitGolfCandidate.TwoPermutationCheckerLowerRun

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate CommitGolfCandidate.ShortTree RiscvZkvm.Rv64 OracleComp OracleSpec
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (check_recorded_bind check_recorded_map compressed_digest write_bits_word_outside)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] readBuffer execute prepare writeBits

def resume (s : MachineState) (node left : Nat) (answer : BitVec 256) : MachineState :=
  (writeBits (prepare s node left) (wordAddress 1536) (padLow answer)).setPC 5040

def levelQuery (s : MachineState) (node proof left : Nat) : OracleComp World MachineState := do
  let answer ← World.query (.inr (.inl (levelPair s node proof left)))
  return latch (resume s node left answer)

def levelResult (oracle : Oracle) (s : MachineState) (node proof left : Nat) : RecordBlock :=
  let pair := levelPair s node proof left
  let answer := oracle.compression pair
  ⟨latch (resume s node left answer),prepareCost node left+6,prepareCost node left+13,[.compression pair answer]⟩

private theorem level_execute (s : MachineState) (node proof left : Nat) (ready : LevelReady s node proof left)
    (fuel : Nat) : execute packedImage (prepareCost node left+6+fuel) s false = do
      let next ← levelQuery s node proof left
      let result ← execute packedImage fuel next false
      return result.charge (prepareCost node left+13) 1 := by
  let h := prepare s node left
  have p := prepare_facts _ _ _ _ ready
  have x23 : h.getReg .x23=12288 := (p.reg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.digest
  have sel : h.getReg .x5=0 ∧ h.getReg .x11=64 ∧ h.getReg .x13=0 := by
    refine ⟨(p.reg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.selector,
      (p.reg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.syscallBytes,
      (p.reg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.syscallSelector⟩
  have hash := parent_hash_step .lower h 12544 12288 p.pc p.src p.dst (x23.trans p.dst.symm) sel
    (by decide) (by decide) (by decide) (by decide) (4+fuel)
  rw [show prepareCost node left+6+fuel=prepareCost node left+(2+(4+fuel)) by omega,p.run,hash]
  erw [p.input]
  simp only [levelQuery,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro answer _
  have endState : (capCompressionAnswer h (padLow answer)).setPC (h.pc+8)=resume s node left answer := by
    unfold capCompressionAnswer resume
    change (writeBits h (h.getReg .x12) (padLow answer)).setPC (h.pc+8)=(writeBits h _ _).setPC _
    rw [show h.getReg .x12=12288 from p.dst, show h.pc=5032 from p.pc]
    rfl
  rw [endState]
  erw [execute_latch (resume s node left answer) rfl fuel]
  simp only [bind_assoc,pure_bind,Execution.charge,Nat.zero_add,←Nat.add_assoc]

private theorem level_rows (oracle : Oracle) (s : MachineState) (node proof left : Nat) :
    let pair := levelPair s node proof left
    let answer := oracle.compression pair
    checkEvaluation oracle (recordRows (levelQuery s node proof left)) =
      ((latch (resume s node left answer),[.compression pair answer]),1) := by
  simp only [levelQuery,record_rows_query,check_evaluation_public_bind,check_evaluation_map,record_rows_pure,check_evaluation_pure]
  rfl

private theorem resume_register (s : MachineState) (node left : Nat) (ans : BitVec 256) (r : Reg) :
    (resume s node left ans).getReg r=(prepare s node left).getReg r := by
  simp only [resume,MachineState.getReg_setPC,writeBits_register]

private theorem latch_keeps (s : MachineState) (r : Reg) (n : r≠.x6) (p : r≠.x21) (l : r≠.x29) :
    (latch s).getReg r=s.getReg r := by
  simp only [latch,MachineState.getReg_setPC,Opening.getReg_setReg,Ne.symm n,Ne.symm p,Ne.symm l,false_and,if_false]

private theorem latch_regs (s : MachineState) :
    (latch s).getReg .x6=s.getReg .x6 >>> 1 ∧ (latch s).getReg .x21=s.getReg .x21+s.getReg .x30 ∧
    (latch s).getReg .x29=s.getReg .x29-1 ∧ (latch s).pc=(if s.getReg .x29-1=0 then 5056 else 4348) := by
  simp [latch, MachineState.getReg_setPC,Opening.getReg_setReg]
  rfl

private theorem shift_word (word : Nat) (bound : word<2^64) :
    BitVec.ofNat 64 word >>> 1=BitVec.ofNat 64 (word/2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt bound,Nat.mod_eq_of_lt (by omega : word/2<2^64),Nat.shiftRight_eq_div_pow]

private theorem sub_word (left : Nat) (positive : 0<left) : BitVec.ofNat 64 left-1=BitVec.ofNat 64 (left-1) := by
  have eq : BitVec.ofNat 64 left=BitVec.ofNat 64 (left-1)+1 := by
    change _=BitVec.ofNat 64 (left-1)+BitVec.ofNat 64 1
    rw [←BitVec.ofNat_add,show left-1+1=left by omega]
  rw [eq,BitVec.add_sub_cancel]

theorem levelFacts (oracle : Oracle) (s : MachineState) (node proof left : Nat) (ready : LevelReady s node proof left) :
    LevelFacts oracle s node proof left (levelResult oracle s node proof left) := by
  let pair := levelPair s node proof left
  let answer := oracle.compression pair
  let mid := resume s node left answer
  let h := prepare s node left
  have p := prepare_facts _ _ _ _ ready
  have pre (r : Reg) (a : r≠.x10) (b : r≠.x12) (c : r≠.x31) (d : r≠.x7) (e : r≠.x30) :
      mid.getReg r=s.getReg r := (resume_register _ _ _ _ r).trans (p.reg r a b c d e)
  have proofReg : mid.getReg .x21=BitVec.ofNat 64 proof := (pre _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.proofReg
  have nodeReg : mid.getReg .x6=BitVec.ofNat 64 node := (pre _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.nodeReg
  have counter : mid.getReg .x29=BitVec.ofNat 64 left := (pre _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.counter
  have wreg : mid.getReg .x30=BitVec.ofNat 64 (width (decide (left=16))) := (resume_register _ _ _ _ _).trans p.widthReg
  have unchanged (r : Reg) (ok : r≠.x10 ∧ r≠.x12 ∧ r≠.x31 ∧ r≠.x7 ∧ r≠.x30 ∧ r≠.x6 ∧ r≠.x21 ∧ r≠.x29) :
      (latch mid).getReg r=s.getReg r := (latch_keeps mid r ok.2.2.2.2.2.1 ok.2.2.2.2.2.2.1 ok.2.2.2.2.2.2.2).trans
        (pre r ok.1 ok.2.1 ok.2.2.1 ok.2.2.2.1 ok.2.2.2.2.1)
  obtain ⟨nodeAfter, ptrAfter, cntAfter, pcAfter⟩ := latch_regs mid
  rw [nodeReg,shift_word node ready.nodeBound] at nodeAfter
  rw [proofReg,wreg,←BitVec.ofNat_add] at ptrAfter
  rw [counter,sub_word left ready.leftPositive] at cntAfter pcAfter
  have mem : (latch mid).mem=(writeBits h (wordAddress 1536) (padLow answer)).mem := rfl
  refine ⟨?_,nodeAfter,ptrAfter,cntAfter,(unchanged _ (by decide)).trans ready.syscallBytes,
    (unchanged _ (by decide)).trans ready.syscallSelector,?_,?_,?_,?_,by exact List.mem_cons_self,?_⟩
  · change (latch mid).pc=_
    rw [pcAfter]
    have test : BitVec.ofNat 64 (left-1)=0 ↔ left=1 := by
      have lo := ready.leftPositive
      have hi := ready.leftBound
      rw [←BitVec.toNat_inj,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : left-1<2^64)]
      change left-1=0 ↔ _
      omega
    simp only [test]
  · intro r ok
    apply unchanged
    unfold RecordSaved at ok
    rcases ok with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst r <;> decide
  · intro w wb outside pairAway
    change (latch mid).getMem (wordAddress w)=s.getMem (wordAddress w)
    rw [MachineState.getMem,mem]
    exact (write_bits_word_outside h (padLow answer) 1536 w (by decide) (by omega) (by omega)).trans
      (p.frame _ (by omega) pairAway)
  · change prepareCost node left+6≤116
    unfold prepareCost routeCost siblingCost
    dsimp only
    split <;> split <;> omega
  · change readBuffer (latch mid) 12288 32=padLow answer
    rw [read_digest_congr _ (writeBits h (wordAddress 1536) (padLow answer)) _ (by decide) (fun _ _ => congrFun mem _)]
    exact compressed_digest _ _ _
  · intro fuel
    change checkEvaluation oracle (recordRows (execute packedImage (prepareCost node left+6+fuel) s false))=_
    rw [level_execute _ _ _ _ ready,check_recorded_bind,level_rows]
    dsimp only
    erw [show (do
      let result ← execute packedImage fuel (latch mid) false
      pure (result.charge (prepareCost node left+13) 1)) =
      (fun result => result.charge (prepareCost node left+13) 1) <$> execute packedImage fuel (latch mid) false
      from bind_pure_comp _ _]
    rw [check_recorded_map]
    rfl

end TwoPermutationPrototype.Packed.Checker
