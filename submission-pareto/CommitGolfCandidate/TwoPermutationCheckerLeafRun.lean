import CommitGolfCandidate.TwoPermutationCheckerLeafCode
import CommitGolfCandidate.TwoPermutationCheckerReplay

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp OracleSpec
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 4096

private theorem add_word (a b : Nat) :
    wordAddress a + BitVec.ofNat 64 (8*b) = wordAddress (a+b) :=
  (wordAddress_add a b).symm

theorem checker_nonce_words (state : MachineState) (nonce : Nat)
    (source : state.getReg .x21 = wordAddress nonce) :
    checkerNonce state = window (memoryView state) nonce := by
  funext i
  fin_cases i <;> simp [checkerNonce, source, window, memoryView, wordAddress_add] <;> rfl

structure LeafReady (state : MachineState) (src nonce : Nat) (index : Index) where
  pc : state.pc = 0x10e4
  source : state.getReg .x10 = wordAddress src
  proofPointer : state.getReg .x21 = wordAddress nonce
  destination : state.getReg .x23 = wordAddress 1536
  tag : state.getReg .x28 = firstTag index.val
  selector : state.getReg .x5 = 0
  size : state.getReg .x11 = 200
  primitive : state.getReg .x13 = 1
  separated : src + 37 ≤ nonce
  endBound : nonce + 2 ≤ 2^33

theorem LeafReady.disjoint {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) (i : Fin 2) (j : Fin 5) :
    state.getReg .x21 + BitVec.ofNat 64 (8*i.val) ≠
      state.getReg .x10 + BitVec.ofNat 64 (8*j.val) := by
  rw [ready.proofPointer, ready.source, add_word, add_word]
  intro equal
  have eq := wordAddress_injective_of_bound (by have := ready.endBound; omega)
    (by have := ready.separated; have := ready.endBound; omega) equal
  have := ready.separated
  omega

theorem aligned_access (word : Nat) (bounded : word < 2 ^ 33) :
    accessValid (wordAddress word) 8 = true := by
  have width := word_address_value (word := word) (by omega)
  simp [accessValid, rangeValid, width, MEMORY_BYTES]
  omega

theorem first_header_view {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) (word : Nat) (bounded : word < 2^33) :
    memoryView (firstPrefix state 8) word =
      writeWindow (memoryView state) src (header index.val (checkerNonce state)) word := by
  have mem := (first_prefix_post state ready.disjoint).1
  simp only [memoryView, MachineState.getMem, mem]
  change memoryView (firstHeaderMemory state) word = _
  rw [header_as_stores]
  unfold firstHeaderMemory
  dsimp only
  rw [ready.source, ready.tag]
  have b := ready.endBound
  have s := ready.separated
  have a1 : wordAddress src + 8#64 = wordAddress (src+1) := add_word src 1
  have a2 : wordAddress src + 16#64 = wordAddress (src+2) := add_word src 2
  have a3 : wordAddress src + 24#64 = wordAddress (src+3) := add_word src 3
  have a4 : wordAddress src + 32#64 = wordAddress (src+4) := add_word src 4
  rw [a1, a2, a3, a4]
  simp only [memory_at_store (by omega : src+4 < 2^61) (by omega : word < 2^61),
    memory_at_store (by omega : src+3 < 2^61) (by omega : word < 2^61),
    memory_at_store (by omega : src+2 < 2^61) (by omega : word < 2^61),
    memory_at_store (by omega : src+1 < 2^61) (by omega : word < 2^61),
    memory_at_store (by omega : src < 2^61) (by omega : word < 2^61), writeWord]

theorem checker_first_input {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) :
    window (memoryView (firstPrefix state 8)) src =
      firstInput index.val (checkerNonce state) (window (memoryView state) (src+5)) := by
  rw [← first_window]
  funext i
  have := ready.endBound
  have := ready.separated
  exact first_header_view ready _ (by omega)

def firstReplyState (state : MachineState) (src : Nat) (reply : Block) : MachineState :=
  writeBits (firstPrefix state 8) (wordAddress src) reply

def secondReplyState (state : MachineState) (src : Nat) (first second : Block) : MachineState :=
  writeBits (secondPrefix (firstReplyState state src first) 4) (wordAddress 1536) second

theorem checker_second_input {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) (answer : Block) :
    window (memoryView (secondPrefix (firstReplyState state src answer) 4)) (src+12) =
      secondInput index.val (replyWords answer) (window (memoryView state) (src+5)) := by
  change BitVec 1600 at answer
  rw [← second_window (memoryView state) src index.val (checkerNonce state) (replyWords answer)]
  funext i
  let after := firstReplyState state src answer
  have b := ready.endBound
  have s := ready.separated
  have srcReg : after.getReg .x10 = wordAddress src := by
    change (writeBits (firstPrefix state 8) (wordAddress src) answer).getReg .x10 = _
    rw [writeBits_register]
    exact (first_prefix_post state ready.disjoint).2.1.trans ready.source
  have tagReg : after.getReg .x28 = firstTag index.val := by
    change (writeBits (firstPrefix state 8) (wordAddress src) answer).getReg .x28 = _
    rw [writeBits_register, first_prefix_register _ _ (by decide) (by decide), ready.tag]
  have addr : wordAddress src + 96#64 = wordAddress (src+12) := add_word src 12
  have tag : after.getReg .x28 + 96#64 = secondTag index.val := by rw [tagReg, secondTag]; rfl
  have a : src+12 < 2^61 := by omega
  have w : src+12+i.val < 2^61 := by omega
  change memoryView (secondPrefix after 4) (src+12+i.val) = _
  simp only [memoryView, MachineState.getMem, (second_prefix_post after).1]
  change memoryView (after.setMem (after.getReg .x10 + 96#64) (after.getReg .x28+96#64))
    (src+12+i.val) = _
  rw [srcReg, addr, tag, memory_at_store a w]
  have view : memoryView after (src+12+i.val) =
      writeWindow (writeWindow (memoryView state) src (header index.val (checkerNonce state)))
        src (replyWords answer) (src+12+i.val) := by
    change memoryView (writeBits (firstPrefix state 8) (wordAddress src) answer) _ = _
    rw [permutation_write_memory (firstPrefix state 8) src (src+12+i.val) answer (by omega) (by omega)]
    simp only [writeWindow]
    split
    · rfl
    · exact first_header_view ready _ (by omega)
  simp only [writeWord, view, window]

attribute [local irreducible] execute readBuffer writeBits packBuffer

private theorem first_call_run {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) (fuel : Nat) :
    execute checkerImage (9+fuel) state false =
      (do let a ← World.query (.inr (.inr (.inl (packBuffer
            (firstInput index.val (checkerNonce state) (window (memoryView state) (src+5)))))))
          let r ← execute checkerImage fuel (firstReplyState state src a) false
          return r.charge 16 1) := by
  obtain ⟨_, r10, r12, pc, r5, r11, r13⟩ := first_prefix_post state ready.disjoint
  have bound := ready.endBound
  have gap := ready.separated
  have callPC : (firstPrefix state 8).pc = 0x1104 := by rw [pc, ready.pc]; rfl
  have call := execute_permutation_call checkerImage fuel (firstPrefix state 8) false src src
    (by omega) (by omega) (r10.trans ready.source) (r12.trans ready.source)
    (r5.trans ready.selector) (r11.trans ready.size) (r13.trans ready.primitive)
    (checker_first_ecall _ callPC)
  rw [checker_first_input ready] at call
  have atSrc (w : Nat) (small : w < 5) :
      accessValid (state.getReg .x10 + BitVec.ofNat 64 (8*w)) 8 = true := by
    rw [ready.source, add_word]
    exact aligned_access _ (by omega)
  have atNonce (w : Nat) (small : w < 2) :
      accessValid (state.getReg .x21 + BitVec.ofNat 64 (8*w)) 8 = true := by
    rw [ready.proofPointer, add_word]
    exact aligned_access _ (by omega)
  rw [show 9+fuel = 8+(fuel+1) by omega, execute_first_prefix state ready.pc _
    (by simpa using atSrc 0 (by decide))
    (atSrc 1 (by decide)) (atSrc 2 (by decide)) (atSrc 3 (by decide)) (atSrc 4 (by decide))
    (by simpa using atNonce 0 (by decide)) (atNonce 1 (by decide)), call]
  simp [firstReplyState, Execution.charge, bind_assoc, ← Nat.add_assoc] <;> rfl

theorem after_first_register {state : MachineState} (src : Nat) (answer : Block)
    (reg : Reg) (a : reg ≠ .x12) (b : reg ≠ .x31) :
    (firstReplyState state src answer).getReg reg = state.getReg reg := by
  rw [firstReplyState, writeBits_register, first_prefix_register _ _ a b]

theorem after_first_pc {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) (answer : Block) :
    (firstReplyState state src answer).pc = 0x1108 := by
  unfold firstReplyState writeBits
  change (firstPrefix state 8).pc + 4 = _
  rw [(first_prefix_post state ready.disjoint).2.2.2.1, ready.pc]
  rfl

private theorem second_call_run {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) (a : Block) (fuel : Nat) :
    execute checkerImage (5+fuel) (firstReplyState state src a) false =
      (do let b ← World.query (.inr (.inr (.inl (packBuffer
            (secondInput index.val (replyWords a) (window (memoryView state) (src+5)))))))
          let r ← execute checkerImage fuel (secondReplyState state src a b) false
          return r.charge 12 1) := by
  let prev := firstReplyState state src a
  have equation (reg : Reg) (a : reg ≠ .x12) (b : reg ≠ .x31) :
      prev.getReg reg = state.getReg reg := after_first_register src _ reg a b
  have srcReg : prev.getReg .x10 = wordAddress src :=
    (equation _ (by decide) (by decide)).trans ready.source
  have secondStart := after_first_pc ready a
  obtain ⟨_, r10, r12, pc, r5, r11, r13⟩ := second_prefix_post prev
  have callPC : (secondPrefix prev 4).pc = 0x1118 := by rw [pc, secondStart]; rfl
  have address : prev.getReg .x10 + 96#64 = wordAddress (src+12) :=
    congrArg (· + 96#64) srcReg |>.trans (add_word src 12)
  have bound := ready.endBound
  have gap := ready.separated
  have call := execute_permutation_call checkerImage fuel (secondPrefix prev 4) false (src+12) 1536
    (by omega) (by decide) (r10.trans address)
    (r12.trans ((equation _ (by decide) (by decide)).trans ready.destination))
    (r5.trans ((equation _ (by decide) (by decide)).trans ready.selector))
    (r11.trans ((equation _ (by decide) (by decide)).trans ready.size))
    (r13.trans ((equation _ (by decide) (by decide)).trans ready.primitive))
    (checker_second_ecall _ callPC)
  rw [show prev = firstReplyState state src a from rfl, checker_second_input ready] at call
  have access : accessValid (prev.getReg .x10 + 96#64) 8 = true := by
    rw [address]
    exact aligned_access _ (by omega)
  rw [show 5+fuel = 4+(fuel+1) by omega, execute_second_prefix prev secondStart _ access, call]
  simp [secondReplyState, Execution.charge, bind_assoc, ← Nat.add_assoc] <;> rfl

def leafQueries (state : MachineState) (src : Nat) (index : Index) : OracleComp World MachineState := do
  let message := window (memoryView state) (src+5)
  let first ← World.query (.inr (.inr (.inl (packBuffer (firstInput index.val (checkerNonce state) message)))))
  let second ← World.query (.inr (.inr (.inl (packBuffer (secondInput index.val (replyWords first) message)))))
  return secondReplyState state src first second

/-- One checker leaf traverses the two ordered forward-permutation rows before
the lower authentication path starts. This holds for arbitrary oracle replies. -/
theorem execute_checker_leaf {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) (fuel : Nat) :
    execute checkerImage (14+fuel) state false =
      (do let intermediate ← leafQueries state src index
          let result ← execute checkerImage fuel intermediate false
          return result.charge 28 2) := by
  rw [show 14+fuel = 9+(5+fuel) by omega, first_call_run ready]
  simp only [leafQueries, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a _
  change Block at a
  rw [second_call_run ready a fuel]
  simp [Execution.charge, bind_assoc, ← Nat.add_assoc] <;> rfl

theorem checker_leaf_rows (oracle : Oracle) (state : MachineState) (src : Nat) (index : Index) :
    let message := window (memoryView state) (src+5)
    let a := firstRow oracle.permutation index (checkerNonce state) message
    let b := secondRow oracle.permutation index message a.2
    checkEvaluation oracle (recordRows (leafQueries state src index)) =
      ((secondReplyState state src a.2 b.2, [.permutation a.1 a.2, .permutation b.1 b.2]), 2) := by
  simp only [leafQueries, firstRow, secondRow, record_rows_query, check_evaluation_public_bind,
    check_evaluation_map, record_rows_pure, check_evaluation_pure]
  rfl

theorem checker_leaf_digest (state : MachineState) (src : Nat) (a b : Block) :
    readBuffer (secondReplyState state src a b) 12288 32 = outputDigest b := by
  unfold secondReplyState
  simpa only [wordAddress, Nat.add_zero, Nat.mul_zero, outputDigest] using
    write_bits_digest (secondPrefix (firstReplyState state src a) 4) 12288 0 b (by decide) (by decide)

theorem checker_leaf_finished_pc {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) (a b : Block) :
    (secondReplyState state src a b).pc = 0x111c := by
  unfold secondReplyState writeBits
  change (secondPrefix (firstReplyState state src a) 4).pc + 4 = _
  rw [(second_prefix_post _).2.2.2.1, after_first_pc ready a]
  rfl

theorem checker_leaf_preserved_register (state : MachineState) (src : Nat) (a b : Block)
    (reg : Reg) (input : reg ≠ .x10) (output : reg ≠ .x12) (temporary : reg ≠ .x31) :
    (secondReplyState state src a b).getReg reg = state.getReg reg := by
  rw [secondReplyState, writeBits_register, second_prefix_register _ _ input output temporary,
    after_first_register _ _ _ output temporary]

theorem checker_leaf_frame {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : LeafReady state src nonce index) (a b : Block) (word : Nat)
    (bound : word < 2^33) (inputOutside : word < src ∨ src+25 ≤ word)
    (scratchOutside : word < 1536 ∨ 1561 ≤ word) :
    memoryView (secondReplyState state src a b) word = memoryView state word := by
  change BitVec 1600 at a b
  have room := ready.endBound
  have gap := ready.separated
  let prev := firstReplyState state src a
  change memoryView (writeBits (secondPrefix prev 4) (wordAddress 1536) b) word = _
  rw [permutation_write_memory (secondPrefix prev 4) 1536 word b (by decide) bound,
    writeWindow, dite_eq_right (by omega : ¬(1536 ≤ word ∧ word < 1536+25))]
  have mem := (second_prefix_post prev).1
  simp only [memoryView, MachineState.getMem, mem]
  change memoryView (prev.setMem (prev.getReg .x10+96#64) (prev.getReg .x28+96#64)) word = _
  rw [(after_first_register src a .x10 (by decide) (by decide)).trans ready.source,
    show wordAddress src + 96#64 = wordAddress (src+12) from add_word src 12,
    memory_at_store (by omega : src+12 < 2^61) (by omega : word < 2^61),
    writeWord, ite_eq_right (by omega : word ≠ src+12)]
  change memoryView (writeBits (firstPrefix state 8) (wordAddress src) a) word = _
  rw [permutation_write_memory (firstPrefix state 8) src word a (by omega) bound,
    writeWindow, dite_eq_right (by omega : ¬(src ≤ word ∧ word < src+25)),
    first_header_view ready word bound, writeWindow, dite_eq_right (by omega : ¬(src ≤ word ∧ word < src+5))]
  rfl

end TwoPermutationPrototype.Checker
