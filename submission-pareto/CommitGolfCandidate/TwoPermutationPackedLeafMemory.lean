import CommitGolfCandidate.TwoPermutationPackedLeafOps

namespace TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 650000

structure LeafReady (s : MachineState) (slot : Fin 4096) (start index dst salts : Nat) : Prop where
  source : s.getReg .x10=wordAddress (start+5)
  destination : s.getReg .x20+BitVec.ofNat 64 (32*(slot.val%64))=wordAddress dst
  nonces : s.getReg .x22=wordAddress salts
  tag : firstTag index=wordAddress start
  sourceBound : start+37≤2^33
  heapBound : dst+25≤2^33
  nonceBound : salts+256≤2^33
  separate : start+37≤salts
  selector : s.getReg .x5=0
  size : s.getReg .x11=200
  primitive : s.getReg .x13=1

theorem after_a_memory (s : MachineState) (slot : Fin 4096) (start index dst salts w : Nat)
    (ready : LeafReady s slot start index dst salts) (a : BitVec 1600) (bounded : w<2^33) :
    memoryView (repliedA s slot start a) w=writeWindow (memoryView s) (start+1) (replyWords a) w := by
  have room := ready.sourceBound
  unfold repliedA
  rw [permutation_write_memory _ _ _ _ (by omega) bounded]
  by_cases hit : start+1≤w ∧ w<start+1+25
  · simp only [writeWindow,dite_eq_left hit]
  · simp only [writeWindow,dite_eq_right hit]
    exact congrFun (first_execution s slot).1 _

theorem after_a_input_cursor (s : MachineState) (slot : Fin 4096) (start index dst salts : Nat)
    (ready : LeafReady s slot start index dst salts) (a : BitVec 1600) :
    (repliedA s slot start a).getReg .x10=wordAddress (start+5) := by
  rw [repliedA,CommitGolfCandidate.writeBits_register,(first_execution s slot).2.1,ready.source]

theorem after_a_reg (s : MachineState) (slot : Fin 4096) (start : Nat) (a : BitVec 1600) (r : Reg)
    (p : r≠.x10) (q : r≠.x12) : (repliedA s slot start a).getReg r=s.getReg r := by
  rw [repliedA,CommitGolfCandidate.writeBits_register,first_keeps _ _ _ p q]

def saltWord (salts : Nat) (slot : Fin 4096) := salts+2*(slot.val%128)

private theorem salt_addr (salts : Nat) (slot : Fin 4096) :
    wordAddress salts+BitVec.ofNat 64 (16*(slot.val%128))=wordAddress (saltWord salts slot) ∧
    wordAddress salts+BitVec.ofNat 64 (16*(slot.val%128)+8)=wordAddress (saltWord salts slot+1) := by
  unfold saltWord wordAddress
  constructor <;> rw [←BitVec.ofNat_add] <;> congr 1 <;> omega

private theorem address_const (base n : Nat) : wordAddress base+BitVec.ofNat 64 (8*n)=wordAddress (base+n) :=
  (wordAddress_add base n).symm

private theorem tagged_addr (s : MachineState) (slot : Fin 4096) (start index dst salts : Nat)
    (ready : LeafReady s slot start index dst salts) (a : BitVec 1600) :
    (repliedA s slot start a).getReg .x10+56=wordAddress (start+12) := by
  rw [after_a_input_cursor _ _ _ _ _ _ ready]
  exact address_const (start+5) 7

theorem second_separate (s : MachineState) (slot : Fin 4096) (start index dst salts : Nat)
    (ready : LeafReady s slot start index dst salts) (a : BitVec 1600) :
    StampSeparate (repliedA s slot start a) slot := by
  have sBound := ready.sourceBound
  have nb := ready.nonceBound
  have dis := ready.separate
  have so : salts≤saltWord salts slot ∧ saltWord salts slot+1<salts+256 := by unfold saltWord; omega
  have distinct (u v : Nat) (ub : u<2^61) (vb : v<2^61) (ne : u≠v) :
      wordAddress u ≠ wordAddress v := fun eq => ne (wordAddress_injective_of_bound ub vb eq)
  unfold StampSeparate
  rw [tagged_addr _ _ _ _ _ _ ready,after_a_reg _ _ _ _ _ (by decide) (by decide),ready.nonces,(salt_addr salts slot).1]
  change wordAddress _≠_ ∧ wordAddress _+BitVec.ofNat 64 (8*1)≠_ ∧
    wordAddress _+BitVec.ofNat 64 (8*1)≠wordAddress _+BitVec.ofNat 64 (8*1)
  simp only [address_const]
  exact ⟨distinct _ _ (by omega) (by omega) (by omega),distinct _ _ (by omega) (by omega) (by omega),
    distinct _ _ (by omega) (by omega) (by omega)⟩

theorem after_a_nonce (s : MachineState) (slot : Fin 4096) (start index dst salts : Nat)
    (ready : LeafReady s slot start index dst salts) (a : BitVec 1600) :
    nonceWords (repliedA s slot start a) slot=nonceWords s slot := by
  have separate := ready.separate
  have room := ready.nonceBound
  have outside (w : Nat) (lo : salts≤w) (hi : w<2^33) :
      memoryView (repliedA s slot start a) w=memoryView s w := by
    rw [after_a_memory s slot start index dst salts w ready a hi]
    exact dif_neg (by omega)
  have so : salts≤saltWord salts slot ∧ saltWord salts slot+1<salts+256 := by unfold saltWord; omega
  funext i
  simp only [nonceWords,after_a_reg _ _ _ _ _ (by decide : Reg.x22≠.x10) (by decide),ready.nonces,
    (salt_addr salts slot).1,(salt_addr salts slot).2]
  split <;> apply outside _ (by omega) (by omega)

theorem prepared_b_memory (s : MachineState) (slot : Fin 4096) (start index dst salts w : Nat)
    (ready : LeafReady s slot start index dst salts) (a : BitVec 1600) (bounded : w<2^33) :
    memoryView (preparedB s slot start a) w=stamp (writeWindow (memoryView s) (start+1) (replyWords a))
      start (secondTag index) (nonceWords s slot) w := by
  let prev := repliedA s slot start a
  have m : (preparedB s slot start a).mem=(secondMemory prev slot).mem :=
    (second_execution prev slot (second_separate _ _ _ _ _ _ ready _)).1
  have t : prev.getReg .x10+56=wordAddress (start+12) := tagged_addr _ _ _ _ _ _ ready _
  have tag : secondTag index=wordAddress (start+12) := by rw [secondTag,ready.tag];exact address_const start 12
  have post : nonceWords prev slot=nonceWords s slot := after_a_nonce _ _ _ _ _ _ ready _
  have b := ready.sourceBound
  change (preparedB s slot start a).mem (wordAddress w)=_
  rw [m]
  change memoryView (secondMemory prev slot) w=_
  unfold secondMemory
  rw [t,post,tag]
  change memoryView (((prev.setMem _ _).setMem (wordAddress (start+12)+BitVec.ofNat 64 (8*1)) _).setMem
    (wordAddress (start+12)+BitVec.ofNat 64 (8*2)) _) w=_
  rw [address_const,address_const,memory_at_store (by omega) (by omega),writeWord,memory_at_store (by omega) (by omega),writeWord,
    memory_at_store (by omega) (by omega)]
  simp only [stamp,writeWord,Nat.add_assoc,Nat.reduceAdd]
  rw [show memoryView prev w=_ from after_a_memory s slot start index dst salts w ready a bounded]

theorem after_b_input (s : MachineState) (slot : Fin 4096) (start index dst salts : Nat)
    (ready : LeafReady s slot start index dst salts) (a : BitVec 1600) :
    window (memoryView (preparedB s slot start a)) (start+12) =
      pinnedWords (secondTag index) (nonceWords s slot) (replyWords a) (window (memoryView s) (start+5)) := by
  rw [←pinned_second_window]
  funext k
  have room := ready.sourceBound
  have bounded := k.isLt
  exact prepared_b_memory _ _ _ _ _ _ _ ready _ (by omega)

theorem finished_leaf_memory (s : MachineState) (slot : Fin 4096) (start index dst salts w : Nat)
    (ready : LeafReady s slot start index dst salts) (a b : BitVec 1600) (bounded : w<2^33) :
    memoryView (finishedLeaf s slot start dst a b) w =
      pinnedWrites (memoryView s) (secondTag index) (nonceWords s slot) start dst a b w := by
  change memoryView (writeBits (preparedB s slot start a) (wordAddress dst) b) w=_
  rw [permutation_write_memory _ _ _ _ ready.heapBound bounded]
  by_cases hit : dst≤w ∧ w<dst+25
  · simp only [pinnedWrites,writeWindow,dite_eq_left hit]
  · simp only [pinnedWrites,writeWindow,dite_eq_right hit]
    exact prepared_b_memory _ _ _ _ _ _ _ ready _ bounded

end TwoPermutationPrototype.RV64.PackedLeaves
