import CommitGolfCandidate.QuadRecordLeafCode
import CommitGolfCandidate.TwoPermutationCheckerReplay
import CommitGolfCandidate.TaggedPinnedModel

namespace TwoPermutationPrototype.Quad.RecordLeaf
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp OracleSpec
open TwoPermutationPrototype.Quad.Checker (packedImage)
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000

private theorem add_word (a b : Nat) :
    wordAddress a + BitVec.ofNat 64 (8*b) = wordAddress (a+b) :=
  (wordAddress_add a b).symm

theorem checker_nonce_words (state : MachineState) (nonce : Nat)
    (source : state.getReg .x4 = wordAddress nonce) :
    checkerNonce state = window (memoryView state) nonce := by
  funext i
  fin_cases i <;> simp [checkerNonce, source, window, memoryView, wordAddress_add] <;> rfl

structure LeafReady (state : MachineState) (src nonce : Nat) (index : Index) where
  pc : state.pc = 0x10b0
  source : state.getReg .x10 = wordAddress src
  proofPointer : state.getReg .x4 = wordAddress nonce
  destination : state.getReg .x23 = wordAddress 1536
  tag : state.getReg .x28 = firstTag index.val
  selector : state.getReg .x5 = 0
  size : state.getReg .x11 = 200
  primitive : state.getReg .x13 = 1
  separated : nonce + 2 ≤ src
  endBound : src + 37 ≤ 2^33

theorem aligned_access (word : Nat) (bounded : word < 2 ^ 33) :
    accessValid (wordAddress word) 8 = true := by
  have width := word_address_value (word := word) (by omega)
  simp [accessValid, rangeValid, width, MEMORY_BYTES]
  omega

def firstReplyState (state : MachineState) (src : Nat) (reply : Block) : MachineState :=
  writeBits (firstPrefix state 2) (wordAddress (src+1)) reply

def secondReplyState (state : MachineState) (src : Nat) (first second : Block) : MachineState :=
  writeBits (secondPrefix (firstReplyState state src first) 10) (wordAddress 1536) second

theorem after_first_register {state : MachineState} (src : Nat) (answer : Block)
    (reg : Reg) (input : reg ≠ .x10) (output : reg ≠ .x12) :
    (firstReplyState state src answer).getReg reg = state.getReg reg := by
  rw [firstReplyState,writeBits_register,first_prefix_register _ _ input output]

theorem after_first_pc {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) (answer : Block) :
    (firstReplyState state src answer).pc = 0x10bc := by
  change (firstPrefix state 2).pc+4=_
  rw [(first_prefix_post state).2.2.2.1,ready.pc]
  rfl

private theorem first_reply_pointer {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) (reply : Block) :
    (firstReplyState state src reply).getReg .x10=wordAddress (src+5) := by
  rw [firstReplyState,writeBits_register,(first_prefix_post state).2.1,ready.source]
  exact add_word src 5

private theorem first_reply_word {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) (answer : Block) (word : Nat) (bounded : word<2^33) :
    memoryView (firstReplyState state src answer) word =
      writeWindow (memoryView state) (src+1) (replyWords answer) word := by
  have room := ready.endBound
  have memory : memoryView (firstPrefix state 2) = memoryView state := by
    funext atWord
    exact congrFun (first_prefix_post state).1 (wordAddress atWord)
  calc
    _ = writeWindow (memoryView (firstPrefix state 2)) (src+1) (replyWords answer) word :=
      permutation_write_memory (firstPrefix state 2) (src+1) word answer (by omega) bounded
    _ = _ := by rw [memory]

private theorem first_reply_nonce {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) (answer : Block) :
    checkerNonce (firstReplyState state src answer) = checkerNonce state := by
  have ptr := (after_first_register src answer .x4 (by decide) (by decide)).trans ready.proofPointer
  rw [checker_nonce_words _ nonce ptr,checker_nonce_words _ nonce ready.proofPointer]
  funext i
  have room := ready.endBound
  have gap := ready.separated
  have inside := i.isLt
  change memoryView (firstReplyState state src answer) (nonce+i.val) = memoryView state (nonce+i.val)
  rw [first_reply_word ready answer _ (by omega),writeWindow,
    dite_eq_right (by omega : ¬(src+1≤nonce+i.val ∧ nonce+i.val<src+1+25))]

private theorem staged_nonce_separate {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) (answer : Block) (i j : Nat) (inside : i<2) (small : j<3) :
    (firstReplyState state src answer).getReg .x4 + BitVec.ofNat 64 (8*i) ≠
      (firstReplyState state src answer).getReg .x10 + BitVec.ofNat 64 (56+8*j) := by
  rw [(after_first_register src answer .x4 (by decide) (by decide)).trans ready.proofPointer,
    first_reply_pointer ready answer, add_word nonce i,show 56+8*j=8*(7+j) by omega,add_word (src+5) (7+j)]
  intro equal
  have room := ready.endBound
  have gap := ready.separated
  have same := wordAddress_injective_of_bound (by omega : nonce+i<2^61) (by omega : src+5+(7+j)<2^61) equal
  omega

private theorem second_setup {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) (answer : Block) :
    let before := firstReplyState state src answer
    let after := secondPrefix before 10
    after.mem = (secondHeaderMemory before).mem ∧
    after.getReg .x10 = before.getReg .x10+56#64 ∧ after.getReg .x12 = before.getReg .x23 ∧
    after.pc = before.pc+40 ∧ after.getReg .x5=before.getReg .x5 ∧
    after.getReg .x11=before.getReg .x11 ∧ after.getReg .x13=before.getReg .x13 := by
  let before := firstReplyState state src answer
  have a := staged_nonce_separate ready answer 0 0 (by decide) (by decide)
  have b := staged_nonce_separate ready answer 1 0 (by decide) (by decide)
  have c := staged_nonce_separate ready answer 1 1 (by decide) (by decide)
  apply second_prefix_post
  · change before.getReg .x4 + 0#64 ≠ before.getReg .x10+56#64 at a
    simpa only [BitVec.add_zero] using a
  · exact b
  · exact c

private theorem second_header_view {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) (answer : Block) (word : Nat) (bounded : word<2^33) :
    let before := firstReplyState state src answer
    memoryView (secondPrefix before 10) word =
      writeWord (writeWord (writeWord (memoryView before) (src+12) (pinnedPositionTag index))
        (src+13) (checkerNonce state 0)) (src+14) (checkerNonce state 1) word := by
  let before := firstReplyState state src answer
  have mem := (second_setup ready answer).1
  have r := first_reply_pointer ready answer
  have room := ready.endBound
  have a : before.getReg .x10+56#64=wordAddress (src+12) := by rw [r]; exact add_word (src+5) 7
  have b : before.getReg .x10+64#64=wordAddress (src+13) := by rw [r]; exact add_word (src+5) 8
  have c : before.getReg .x10+72#64=wordAddress (src+14) := by rw [r]; exact add_word (src+5) 9
  have tag : before.getReg .x28+96#64=pinnedPositionTag index := by
    rw [(after_first_register src answer .x28 (by decide) (by decide)).trans ready.tag]
    change BitVec.ofNat 64 (4056+256*index.val)+BitVec.ofNat 64 96=_
    rw [← BitVec.ofNat_add]
    unfold pinnedPositionTag
    congr 1
    omega
  calc
    _ = memoryView (secondHeaderMemory before) word := congrFun mem (wordAddress word)
    _ = _ := by
      unfold secondHeaderMemory
      dsimp only
      rw [a,b,c,tag,first_reply_nonce ready answer,
        memory_at_store (by omega : src+14<2^61) (by omega : word<2^61)]
      simp only [writeWord]
      split
      · rfl
      · rw [memory_at_store (by omega : src+13<2^61) (by omega : word<2^61)]
        simp only [writeWord]
        split
        · rfl
        · rw [memory_at_store (by omega : src+12<2^61) (by omega : word<2^61)]
          rfl

theorem checker_second_input {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) (answer : Block) :
    window (memoryView (secondPrefix (firstReplyState state src answer) 10)) (src+12) =
      pinnedSecondInput index (checkerNonce state) (replyWords answer) (window (memoryView state) (src+5)) := by
  funext i
  have room := ready.endBound
  have bounded := i.isLt
  have word : src+12+i.val<2^33 := by omega
  change memoryView (secondPrefix (firstReplyState state src answer) 10) (src+12+i.val) = _
  rw [second_header_view ready answer _ word]
  unfold pinnedSecondInput
  by_cases prologue : i.val < 3
  · have slots : i.val=0 ∨ i.val=1 ∨ i.val=2 := by omega
    rcases slots with z | o | t
    · simp [writeWord,z]
    · simp [writeWord,o,show src+12+1=src+13 by omega]
    · simp [writeWord,t,show src+12+2=src+14 by omega]
  · rw [writeWord,ite_eq_right (by omega : src+12+i.val≠src+14),writeWord,
      ite_eq_right (by omega : src+12+i.val≠src+13),writeWord,ite_eq_right (by omega : src+12+i.val≠src+12),
      ite_eq_right (by omega : i.val≠0),dite_eq_right prologue,first_reply_word ready answer _ word]
    by_cases inside : i.val < 14
    · rw [writeWindow,dite_eq_left (by omega : src+1≤src+12+i.val ∧ src+12+i.val<src+1+25),
        dite_eq_left inside]
      congr 1
      apply Fin.ext
      change src+12+i.val-(src+1)=i.val+11
      omega
    · rw [writeWindow,dite_eq_right (by omega : ¬(src+1≤src+12+i.val ∧ src+12+i.val<src+1+25)),
        dite_eq_right inside]
      change memoryView state (src+12+i.val) = memoryView state (src+5+(i.val+7))
      congr 1
      omega

attribute [local irreducible] execute readBuffer writeBits packBuffer

private theorem first_call_run {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) (fuel : Nat) :
    execute packedImage (3+fuel) state false =
      (do let a ← World.query (.inr (.inr (.inl (packBuffer
            (pinnedFirstInput (window (memoryView state) (src+5)))))))
          let r ← execute packedImage fuel (firstReplyState state src a) false
          return r.charge 10 1) := by
  obtain ⟨mem,r10,r12,pc,r5,r11,r13⟩ := first_prefix_post state
  have room := ready.endBound
  have callPC : (firstPrefix state 2).pc = 0x10b8 := by rw [pc,ready.pc]; rfl
  have input : (firstPrefix state 2).getReg .x10=wordAddress (src+5) :=
    r10.trans ((congrArg (·+40) ready.source).trans (add_word src 5))
  have output : (firstPrefix state 2).getReg .x12=wordAddress (src+1) :=
    r12.trans ((congrArg (·+8) ready.source).trans (add_word src 1))
  have call := execute_permutation_call packedImage fuel (firstPrefix state 2) false (src+5) (src+1)
    (by omega) (by omega) input output (r5.trans ready.selector) (r11.trans ready.size)
    (r13.trans ready.primitive) (checker_first_ecall _ callPC)
  have windowEq : window (memoryView (firstPrefix state 2)) (src+5) =
      pinnedFirstInput (window (memoryView state) (src+5)) := by
    funext i
    exact congrFun mem (wordAddress (src+5+i.val))
  rw [windowEq] at call
  rw [show 3+fuel=2+(fuel+1) by omega,execute_first_prefix state ready.pc _,call]
  simp [firstReplyState,Execution.charge,← Nat.add_assoc]

private theorem second_call_run {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) (a : Block) (fuel : Nat) :
    execute packedImage (11+fuel) (firstReplyState state src a) false =
      (do let b ← World.query (.inr (.inr (.inl (packBuffer
            (pinnedSecondInput index (checkerNonce state) (replyWords a) (window (memoryView state) (src+5)))))))
          let r ← execute packedImage fuel (secondReplyState state src a b) false
          return r.charge 18 1) := by
  let prev := firstReplyState state src a
  have keep (reg : Reg) (h10 : reg ≠ .x10) (h12 : reg ≠ .x12) :
      prev.getReg reg = state.getReg reg := after_first_register src a reg h10 h12
  have srcReg := first_reply_pointer ready a
  have nonceReg := (keep .x4 (by decide) (by decide)).trans ready.proofPointer
  have secondStart := after_first_pc ready a
  obtain ⟨_,r10,r12,pc,r5,r11,r13⟩ := second_setup ready a
  have callPC : (secondPrefix prev 10).pc = 0x10e4 := by rw [pc,secondStart]; rfl
  have addr : prev.getReg .x10+56#64=wordAddress (src+12) :=
    (congrArg (·+56#64) srcReg).trans (add_word (src+5) 7)
  have room := ready.endBound
  have gap := ready.separated
  have call := execute_permutation_call packedImage fuel (secondPrefix prev 10) false (src+12) 1536
    (by omega) (by decide) (r10.trans addr)
    (r12.trans ((keep _ (by decide) (by decide)).trans ready.destination))
    (r5.trans ((keep _ (by decide) (by decide)).trans ready.selector))
    (r11.trans ((keep _ (by decide) (by decide)).trans ready.size))
    (r13.trans ((keep _ (by decide) (by decide)).trans ready.primitive))
    (checker_second_ecall _ callPC)
  rw [show prev=firstReplyState state src a from rfl,checker_second_input ready] at call
  have dstAccess (j : Nat) (small : j<3) :
      accessValid (prev.getReg .x10+BitVec.ofNat 64 (56+8*j)) 8=true := by
    rw [srcReg,show 56+8*j=8*(7+j) by omega,add_word]
    exact aligned_access _ (by omega)
  have nonceTail : accessValid (prev.getReg .x4+8#64) 8=true := by
    rw [nonceReg,show wordAddress nonce+8#64=wordAddress (nonce+1) from add_word nonce 1]
    exact aligned_access _ (by omega)
  rw [show 11+fuel=10+(fuel+1) by omega,execute_second_prefix prev secondStart _
    (dstAccess 0 (by decide)) (dstAccess 1 (by decide)) (dstAccess 2 (by decide))
    (nonceReg ▸ aligned_access nonce (by omega)) nonceTail,call]
  simp [secondReplyState,Execution.charge,← Nat.add_assoc]

def leafQueries (state : MachineState) (src : Nat) (index : Index) : OracleComp World MachineState := do
  let message := window (memoryView state) (src+5)
  let first ← World.query (.inr (.inr (.inl (packBuffer (pinnedFirstInput message)))))
  let second ← World.query (.inr (.inr (.inl (packBuffer
    (pinnedSecondInput index (checkerNonce state) (replyWords first) message)))))
  return secondReplyState state src first second

theorem execute_checker_leaf {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) (fuel : Nat) :
    execute packedImage (14+fuel) state false =
      (do let intermediate ← leafQueries state src index
          let result ← execute packedImage fuel intermediate false
          return result.charge 28 2) := by
  rw [show 14+fuel=3+(11+fuel) by omega,first_call_run ready]
  simp only [leafQueries,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a _
  change Block at a
  rw [second_call_run ready a fuel]
  simp [Execution.charge,← Nat.add_assoc]

theorem checker_leaf_rows (oracle : Oracle) (state : MachineState) (src : Nat) (index : Index) :
    let message := window (memoryView state) (src+5)
    let nonce := checkerNonce state
    let a := pinnedFirstRow oracle.permutation message
    let b := pinnedSecondRow oracle.permutation index nonce a.2 message
    checkEvaluation oracle (recordRows (leafQueries state src index)) =
      ((secondReplyState state src a.2 b.2,[.permutation a.1 a.2,.permutation b.1 b.2]),2) := by
  simp only [leafQueries,pinnedFirstRow,pinnedSecondRow,record_rows_query,check_evaluation_public_bind,
    check_evaluation_map,record_rows_pure,check_evaluation_pure]
  rfl

theorem checker_leaf_digest (state : MachineState) (src : Nat) (a b : Block) :
    readBuffer (secondReplyState state src a b) 12288 32 = outputDigest b := by
  unfold secondReplyState
  simpa only [wordAddress,Nat.add_zero,Nat.mul_zero,outputDigest] using
    write_bits_digest (secondPrefix (firstReplyState state src a) 10) 12288 0 b (by decide) (by decide)

theorem checker_leaf_finished_pc {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) (a b : Block) :
    (secondReplyState state src a b).pc=0x10e8 := by
  unfold secondReplyState writeBits
  change (secondPrefix (firstReplyState state src a) 10).pc+4=_
  rw [(second_setup ready a).2.2.2.1,after_first_pc ready a]
  rfl

theorem checker_leaf_preserved_register (state : MachineState) (src : Nat) (a b : Block)
    (reg : Reg) (input : reg ≠ .x10) (output : reg ≠ .x12) (temporary : reg ≠ .x31) :
    (secondReplyState state src a b).getReg reg=state.getReg reg := by
  rw [secondReplyState,writeBits_register,second_prefix_register _ _ input output temporary,
    after_first_register _ _ _ input output]

theorem checker_leaf_frame {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) (a b : Block) (word : Nat)
    (bound : word<2^33) (inputOutside : word<src ∨ src+26≤word)
    (scratchOutside : word<1536 ∨ 1561≤word) :
    memoryView (secondReplyState state src a b) word=memoryView state word := by
  change BitVec 1600 at a b
  let prev := firstReplyState state src a
  change memoryView (writeBits (secondPrefix prev 10) (wordAddress 1536) b) word=_
  rw [permutation_write_memory (secondPrefix prev 10) 1536 word b (by decide) bound,writeWindow,
    dite_eq_right (by omega : ¬(1536≤word ∧ word<1536+25)),second_header_view ready a word bound]
  rw [writeWord,ite_eq_right (by omega : word≠src+14),writeWord,ite_eq_right (by omega : word≠src+13),
    writeWord,ite_eq_right (by omega : word≠src+12),first_reply_word ready a word bound,writeWindow,
    dite_eq_right (by omega : ¬(src+1≤word ∧ word<src+1+25))]

end TwoPermutationPrototype.Quad.RecordLeaf
