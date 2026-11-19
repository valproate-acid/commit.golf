import CommitGolfCandidate.TwoPermutationCheckerCopyDigest
import CommitGolfCandidate.TwoPermutationCheckerLowerCode

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling

private theorem branch_read (state : MachineState) (word : Nat) :
    readBuffer (lowerBranch state) (8*word) 32 = readBuffer state (8*word) 32 := by
  apply read_digest_congr _ _ _ (by omega)
  intro i _
  rfl

private theorem compression_setup_read (state : MachineState) (word : Nat) :
    readBuffer (lowerCompressionState state) (8*word) 32 = readBuffer state (8*word) 32 := by
  apply read_digest_congr _ _ _ (by omega)
  intro i _
  rfl

private theorem set_pc_read (state : MachineState) (pc : Word) (word : Nat) :
    readBuffer (state.setPC pc) (8*word) 32 = readBuffer state (8*word) 32 := by
  apply read_digest_congr _ _ _ (by omega)
  intro i _
  rfl

private theorem even_iff {state : MachineState} {node proof : Nat}
    (ready : LowerReady state node proof) (bound : node < 2^64) :
    (state.getReg .x6 &&& 1 = 0) ↔ node % 2 = 0 := by
  change (state.getReg .x6 &&& 1#64 = 0#64) ↔ _
  rw [ready.nodeReg, ← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt bound]
  change (node &&& 1 = 0) ↔ node % 2 = 0
  rw [Nat.and_one_is_mod]

theorem lower_pair_input {state : MachineState} {node proof : Nat}
    (ready : LowerReady state node proof) (bounded : node < 2^64) :
    readBuffer (lowerCompressionState (lowerPrepare state)) 12544 64 =
      pathPair node (readBuffer state 12288 32) (readBuffer state (8*proof) 32) := by
  let branched := lowerBranch state
  have p := ready.proofAbove
  have q := ready.proofBound
  have b0 : branched.getReg .x24 = wordAddress 1568 :=
    (lower_branch_register _ _ (by decide)).trans ready.pairReg
  have s0 : branched.getReg .x21 = wordAddress proof :=
    (lower_branch_register _ _ (by decide)).trans ready.proofReg
  have d0 : branched.getReg .x23 = wordAddress 1536 :=
    (lower_branch_register _ _ (by decide)).trans ready.digestReg
  have high (s : MachineState) (reg : s.getReg .x24 = wordAddress 1568) :
      s.getReg .x24 + BitVec.ofNat 64 32 = wordAddress 1572 := by rw [reg]; rfl
  apply path_pair_read (src := 1568)
  · change readBuffer (lowerCompressionState (lowerPrepare state)) (8*1568) 32 = _
    rw [compression_setup_read]
    by_cases parity : node % 2 = 0
    · have even := (even_iff ready bounded).mpr parity
      rw [lowerPrepare, ite_eq_left even, ite_eq_left parity]
      let middle := copied branched 95
      have s1 : middle.getReg .x21 = wordAddress proof :=
        (copied_register _ _ _ (by decide)).trans s0
      have b1 : middle.getReg .x24 = wordAddress 1568 :=
        (copied_register _ _ _ (by decide)).trans b0
      calc
        _ = readBuffer middle (8*1568) 32 :=
          copied_digest_outside middle 103 proof 1572 1568 (by unfold CopyBlock; decide) s1
            (high middle b1) (by omega) (by decide) (by decide) (Or.inr (by omega)) (Or.inl (by decide))
        _ = readBuffer branched (8*1536) 32 :=
          copied_digest branched 95 1536 1568 (by unfold CopyBlock; decide) d0
            (by simpa [copyTarget, copyOffset] using b0) (by decide) (by decide) (Or.inl (by decide))
        _ = _ := branch_read state 1536
    · have odd : ¬ state.getReg .x6 &&& 1 = 0 := mt (even_iff ready bounded).mp parity
      rw [lowerPrepare, ite_eq_right odd, ite_eq_right parity, set_pc_read]
      let middle := copied branched 78
      have d1 : middle.getReg .x23 = wordAddress 1536 :=
        (copied_register _ _ _ (by decide)).trans d0
      have b1 : middle.getReg .x24 = wordAddress 1568 :=
        (copied_register _ _ _ (by decide)).trans b0
      calc
        _ = readBuffer middle (8*1568) 32 :=
          copied_digest_outside middle 86 1536 1572 1568 (by unfold CopyBlock; decide) d1
            (high middle b1) (by decide) (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide))
        _ = readBuffer branched (8*proof) 32 :=
          copied_digest branched 78 proof 1568 (by unfold CopyBlock; decide) s0
            (by simpa [copyTarget, copyOffset] using b0) (by omega) (by decide) (Or.inr (by omega))
        _ = _ := branch_read state proof
  · change readBuffer (lowerCompressionState (lowerPrepare state)) (8*1572) 32 = _
    rw [compression_setup_read]
    by_cases parity : node % 2 = 0
    · have even := (even_iff ready bounded).mpr parity
      rw [lowerPrepare, ite_eq_left even, ite_eq_left parity]
      let middle := copied branched 95
      have s1 : middle.getReg .x21 = wordAddress proof :=
        (copied_register _ _ _ (by decide)).trans s0
      have b1 : middle.getReg .x24 = wordAddress 1568 :=
        (copied_register _ _ _ (by decide)).trans b0
      calc
        _ = readBuffer middle (8*proof) 32 :=
          copied_digest middle 103 proof 1572 (by unfold CopyBlock; decide) s1
            (high middle b1) (by omega) (by decide) (Or.inr (by omega))
        _ = readBuffer branched (8*proof) 32 :=
          copied_digest_outside branched 95 1536 1568 proof (by unfold CopyBlock; decide) d0
            (by simpa [copyTarget, copyOffset] using b0) (by decide) (by decide) (by omega)
            (Or.inl (by decide)) (Or.inr (by omega))
        _ = _ := branch_read state proof
    · have odd : ¬ state.getReg .x6 &&& 1 = 0 := mt (even_iff ready bounded).mp parity
      rw [lowerPrepare, ite_eq_right odd, ite_eq_right parity, set_pc_read]
      let middle := copied branched 78
      have d1 : middle.getReg .x23 = wordAddress 1536 :=
        (copied_register _ _ _ (by decide)).trans d0
      have b1 : middle.getReg .x24 = wordAddress 1568 :=
        (copied_register _ _ _ (by decide)).trans b0
      calc
        _ = readBuffer middle (8*1536) 32 :=
          copied_digest middle 86 1536 1572 (by unfold CopyBlock; decide) d1
            (high middle b1) (by decide) (by decide) (Or.inl (by decide))
        _ = readBuffer branched (8*1536) 32 :=
          copied_digest_outside branched 78 proof 1568 1536 (by unfold CopyBlock; decide) s0
            (by simpa [copyTarget, copyOffset] using b0) (by omega) (by decide) (by decide)
            (Or.inr (by omega)) (Or.inl (by decide))
        _ = _ := branch_read state 1536

private theorem lower_next_read (state : MachineState) (word : Nat) :
    readBuffer (lowerNext state) (8*word) 32 = readBuffer state (8*word) 32 := by
  apply read_digest_congr _ _ _ (by omega)
  intro i _
  rfl

theorem lower_reply_digest (state : MachineState) (answer : BitVec 256) :
    readBuffer (lowerReply state answer) 12288 32 = answer := by
  unfold lowerReply
  change readBuffer (lowerNext _) (8*1536) 32 = answer
  rw [lower_next_read]
  exact compressed_digest _ 1536 answer

attribute [local irreducible] readBuffer lowerReply

theorem lower_recorded_query (oracle : Oracle) {state : MachineState} {node proof : Nat}
    (ready : LowerReady state node proof) (bounded : node < 2^64) :
    let pair := pathPair node (readBuffer state 12288 32) (readBuffer state (8*proof) 32)
    checkEvaluation oracle (recordRows (lowerQuery state)) =
      ((lowerReply state (oracle.compression pair), [.compression pair (oracle.compression pair)]), 1) := by
  have pair := lower_pair_input ready bounded
  unfold lowerQuery
  erw [pair]
  simp only [record_rows_query, check_evaluation_public_bind, check_evaluation_map, record_rows_pure,
    check_evaluation_pure]
  rfl

theorem lower_reply_post (state : MachineState) (answer : BitVec 256) :
    let next := lowerReply state answer
    next.getReg .x21 = state.getReg .x21+32 ∧
    next.getReg .x6 = state.getReg .x6 >>> 1 ∧
    next.getReg .x29 = state.getReg .x29-1 ∧
    next.pc = if state.getReg .x29-1 = 0 then 0x11d8 else 0x1130 := by
  simp [lowerReply, lowerNext, writeBits_register, lowerCompressionState, MachineState.getReg_setPC,
    Opening.getReg_setReg, lower_prepared_register]
  rfl

theorem lower_reply_register (state : MachineState) (answer : BitVec 256) (r : Reg)
    (input : r ≠ .x10) (output : r ≠ .x12) (node : r ≠ .x6) (pointer : r ≠ .x21)
    (counter : r ≠ .x29) (temporary : r ≠ .x31) (parity : r ≠ .x7) :
    (lowerReply state answer).getReg r = state.getReg r := by
  simp [lowerReply, lowerNext, writeBits_register, lowerCompressionState, MachineState.getReg_setPC,
    Opening.getReg_setReg, Ne.symm input, Ne.symm output, Ne.symm node, Ne.symm pointer, Ne.symm counter,
    lower_prepared_register _ _ temporary parity]

private theorem nat_word_shift (word : Nat) (bound : word < 2^64) :
    BitVec.ofNat 64 word >>> 1 = BitVec.ofNat 64 (word/2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt (by omega : word/2 < 2^64), Nat.shiftRight_eq_div_pow]

private theorem nat_word_sub (word : Nat) : BitVec.ofNat 64 (word+1) - 1 = BitVec.ofNat 64 word := by
  rw [BitVec.ofNat_add]
  change BitVec.ofNat 64 word + 1#64 - 1#64 = _
  exact BitVec.add_sub_cancel _ _

theorem lower_reply_geometry {state : MachineState} {node proof : Nat}
    (ready : LowerReady state node proof) (nodeBound : node < 2^64) (answer : BitVec 256)
    (left : Nat) (counter : state.getReg .x29 = BitVec.ofNat 64 (left+1)) (bounded : left < 2^64) :
    let next := lowerReply state answer
    next.getReg .x21 = wordAddress (proof+4) ∧
    next.getReg .x6 = BitVec.ofNat 64 (node/2) ∧
    next.getReg .x29 = BitVec.ofNat 64 left ∧
    next.pc = if left = 0 then 0x11d8 else 0x1130 := by
  obtain ⟨pointer, heap, length, pc⟩ := lower_reply_post state answer
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pointer, ready.proofReg]
    exact word_offset proof 4
  · rw [heap, ready.nodeReg, nat_word_shift node nodeBound]
  · rw [length, counter, nat_word_sub]
  · rw [pc, counter, nat_word_sub]
    by_cases empty : left = 0
    · subst left
      rfl
    · have h : BitVec.ofNat 64 left ≠ 0#64 := by
        intro zero
        have := congrArg BitVec.toNat zero
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded] at this
        apply empty
        exact this
      simp [h, empty]

theorem lower_reply_ready {state : MachineState} {node proof : Nat}
    (ready : LowerReady state node proof) (nodeBound : node < 2^64) (answer : BitVec 256)
    (left : Nat) (counter : state.getReg .x29 = BitVec.ofNat 64 (left+1)) (bounded : left < 2^64)
    (more : 0 < left) (room : proof+8 ≤ 2^33) :
    LowerReady (lowerReply state answer) (node/2) (proof+4) := by
  obtain ⟨pointer, heap, _, pc⟩ := lower_reply_geometry ready nodeBound answer left counter bounded
  have reg (r : Reg) (a : r ≠ .x10) (b : r ≠ .x12) (c : r ≠ .x6) (d : r ≠ .x21) (e : r ≠ .x29)
      (f : r ≠ .x31) (g : r ≠ .x7) : (lowerReply state answer).getReg r = state.getReg r :=
    lower_reply_register state answer r a b c d e f g
  refine ⟨by simpa [Nat.ne_of_gt more] using pc, heap, pointer, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
  · exact (reg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.digestReg
  · exact (reg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.pairReg
  · exact (reg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.selector
  · exact (reg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.size
  · exact (reg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.primitive
  · have := ready.proofAbove
    omega

private theorem lower_next_view (state : MachineState) (word : Nat) :
    memoryView (lowerNext state) word = memoryView state word := rfl

private theorem lower_compression_view (state : MachineState) (word : Nat) :
    memoryView (lowerCompressionState state) word = memoryView state word := rfl

private theorem lower_branch_view (state : MachineState) (word : Nat) :
    memoryView (lowerBranch state) word = memoryView state word := rfl

private theorem pc_view (state : MachineState) (pc : Word) (word : Nat) :
    memoryView (state.setPC pc) word = memoryView state word := rfl

attribute [local irreducible] writeBits copied

set_option maxHeartbeats 500000 in
theorem lower_reply_frame {state : MachineState} {node proof : Nat}
    (ready : LowerReady state node proof) (answer : BitVec 256) (word : Nat)
    (bound : word < 2^61) (digestOutside : word < 1536 ∨ 1540 ≤ word)
    (pairOutside : word < 1568 ∨ 1576 ≤ word) :
    memoryView (lowerReply state answer) word = memoryView state word := by
  let branched := lowerBranch state
  have p := ready.proofAbove
  have q := ready.proofBound
  have b0 : branched.getReg .x24 = wordAddress 1568 :=
    (lower_branch_register _ _ (by decide)).trans ready.pairReg
  have s0 : branched.getReg .x21 = wordAddress proof :=
    (lower_branch_register _ _ (by decide)).trans ready.proofReg
  have d0 : branched.getReg .x23 = wordAddress 1536 :=
    (lower_branch_register _ _ (by decide)).trans ready.digestReg
  have high (s : MachineState) (reg : s.getReg .x24 = wordAddress 1568) :
      s.getReg .x24 + BitVec.ofNat 64 32 = wordAddress 1572 := by rw [reg]; rfl
  rw [lowerReply, lower_next_view, write_bits_word_outside _ answer 1536 word (by decide) bound (by omega),
    lower_compression_view, ← lower_branch_view state word]
  by_cases parity : state.getReg .x6 &&& 1 = 0
  · rw [lowerPrepare, ite_eq_left parity]
    let middle := copied branched 95
    have s1 : middle.getReg .x21 = wordAddress proof :=
      (copied_register branched 95 .x21 (by decide)).trans s0
    have b1 : middle.getReg .x24 = wordAddress 1568 :=
      (copied_register branched 95 .x24 (by decide)).trans b0
    exact (copied_word_outside middle 103 proof 1572 word (by unfold CopyBlock; decide) s1
      (high middle b1) (by omega) (by decide) bound (Or.inr (by omega)) (by omega)).trans
      (copied_word_outside branched 95 1536 1568 word (by unfold CopyBlock; decide) d0
       (by simpa [copyTarget, copyOffset] using b0) (by decide) (by decide) bound (Or.inl (by decide)) (by omega))
  · rw [lowerPrepare, ite_eq_right parity, pc_view]
    let middle := copied branched 78
    have d1 : middle.getReg .x23 = wordAddress 1536 :=
      (copied_register branched 78 .x23 (by decide)).trans d0
    have b1 : middle.getReg .x24 = wordAddress 1568 :=
      (copied_register branched 78 .x24 (by decide)).trans b0
    exact (copied_word_outside middle 86 1536 1572 word (by unfold CopyBlock; decide) d1
      (high middle b1) (by decide) (by decide) bound (Or.inl (by decide)) (by omega)).trans
      (copied_word_outside branched 78 proof 1568 word (by unfold CopyBlock; decide) s0
       (by simpa [copyTarget, copyOffset] using b0) (by omega) (by decide) bound (Or.inr (by omega)) (by omega))

end TwoPermutationPrototype.Checker
