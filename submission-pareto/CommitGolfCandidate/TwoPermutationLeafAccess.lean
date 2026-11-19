import CommitGolfCandidate.TwoPermutationLeafFrame

/-! The actual 64-GiB bounds discharge every aligned load and store before
either permutation call. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192

theorem leaf_word_access (start offset : Nat) (bound : start + offset < 2^33) :
    accessValid (wordAddress start + BitVec.ofNat 64 (8*offset)) 8 = true := by
  change accessValid (wordAddress start + wordAddress offset) 8 = true
  rw [← wordAddress_add]
  simp [accessValid,rangeValid,word_address_value (by omega : start+offset < 2^61),
    MEMORY_BYTES] <;> omega

private theorem nonce_immediates : ∀ slot : Fin 16,
    signExtend12 (BitVec.ofNat 12 (16*slot.val)) = BitVec.ofNat 64 (8*(2*slot.val)) ∧
    signExtend12 (BitVec.ofNat 12 (16*slot.val+8)) = BitVec.ofNat 64 (8*(2*slot.val+1)) := by decide

theorem first_accesses (s : MachineState) (slot : Fin 16) (start index dst salts : Nat)
    (ready : LeafReady s slot start index dst salts) (i : Nat) (hi : i < 8) :
    memoryArgumentsValid (firstPrefix s slot i) (leafInstr slot i) = true := by
  have a := ready.sourceBound
  have b := ready.nonceBound
  have u := slot.isLt
  interval_cases i
  · change accessValid (s.getReg .x10 + 0) 8 = true
    rw [ready.source]; exact leaf_word_access start 0 (by omega)
  · change accessValid (s.getReg .x10 + 8) 8 = true
    rw [ready.source]; exact leaf_word_access start 1 (by omega)
  · change accessValid (s.getReg .x10 + 16) 8 = true
    rw [ready.source]; exact leaf_word_access start 2 (by omega)
  · change accessValid (s.getReg .x22 + signExtend12 (BitVec.ofNat 12 (16*slot.val))) 8 = true
    rw [ready.nonces,(nonce_immediates slot).1];exact leaf_word_access _ _ (by omega)
  · change accessValid (s.getReg .x10 + 24) 8 = true
    rw [ready.source]; exact leaf_word_access start 3 (by omega)
  · change accessValid (s.getReg .x22 + signExtend12 (BitVec.ofNat 12 (16*slot.val+8))) 8 = true
    rw [ready.nonces,(nonce_immediates slot).2];exact leaf_word_access _ _ (by omega)
  · change accessValid (s.getReg .x10 + 32) 8 = true
    rw [ready.source]; exact leaf_word_access start 4 (by omega)
  · rfl

theorem second_accesses (s : MachineState) (slot : Fin 16) (start : Nat)
    (source : s.getReg .x10 = wordAddress start) (bound : start + 37 ≤ 2^33)
    (i : Nat) (hi : i < 4) :
    memoryArgumentsValid (secondPrefix s slot i) (leafInstr slot (9+i)) = true := by
  interval_cases i
  · rfl
  · rfl
  · change accessValid (s.getReg .x10 + 96 + 0) 8 = true
    rw [source,BitVec.add_assoc]
    change accessValid (wordAddress start + 96) 8 = true
    exact leaf_word_access start 12 (by omega)
  · rfl

theorem after_a_control (s : MachineState) (slot : Fin 16) (start index dst salts : Nat)
    (ready : LeafReady s slot start index dst salts) (pc : s.pc = leafPC slot 0) (a : BitVec 1600) :
    let after := repliedA s slot start a
    after.getReg .x5 = 0 ∧ after.getReg .x11 = 200 ∧ after.getReg .x13 = 1 ∧
      after.getReg .x20 = s.getReg .x20 ∧ after.pc = leafPC slot 9 := by
  obtain ⟨d0,d1⟩ := leaf_nonce_separate _ _ _ _ _ _ ready
  have ⟨_,_,_,r5,r11,r13,hpc⟩ := first_execution s slot d0 d1
  simp only [repliedA,CommitGolfCandidate.writeBits_register,preparedA]
  refine ⟨r5.trans ready.selector,r11.trans ready.size,r13.trans ready.primitive,rfl,?_⟩
  change ((firstInstructions slot).foldl execInstrBr s).pc + 4 = _
  rw [hpc,pc,BitVec.add_assoc]
  exact leaf_pc_add slot 0 9

end TwoPermutationPrototype.RV64
