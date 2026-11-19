import CommitGolfCandidate.QuadCommitLeafIndex

/-! Image-specific fetches for centered output and salt-window rebases. -/
namespace TwoPermutationPrototype.Quad.Commit.Leaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] image decodeInstruction leafCode levelsCode

theorem fetch_leaf_word (slot : Fin 4096) (k : Nat) (inside : k<(leafWords slot.val).length)
    (s : MachineState) (pc : s.pc=leafPC slot k) (instruction : Instr)
    (decoded : ((leafWords slot.val)[k]?).bind decodeInstruction=some (.base instruction)) :
    fetch image s=some (.base instruction) := by
  have idxBound := leaf_prefix_length_bound slot.val
  have slotBound := slot.isLt
  have kBound := leaf_words_length_bound slot.val
  have numeric : s.pc.toNat=4096+4*(leafIndex slot.val+k) := by
    rw [pc,leafPC,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    unfold leafIndex
    omega
  rw [fetch,numeric,if_pos (by omega),show (4096+4*(leafIndex slot.val+k)-4096)/4=leafIndex slot.val+k by omega]
  rw [←leaf_code_at slot.val k slot.isLt inside] at decoded
  cases result : image.code[leafIndex slot.val+k]? with
  | none => simp [result] at decoded
  | some w => simpa [result] using decoded

theorem fetch_heap_rebase (slot : Fin 4096) (h : slot.val%45=44)
    (s : MachineState) (pc : s.pc=leafPC slot 11) :
    fetch image s=some (.base (.ADDI .x20 .x12 1776)) := by
  apply fetch_leaf_word slot 11 (by rw [leaf_word_count];unfold extra heapExtra;rw [if_pos h];omega) s pc
  simp only [leafWords,if_pos h,List.cons_append,List.nil_append,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.bind_some]
  unfold decodeInstruction
  rfl

theorem fetch_nonce_rebase (slot : Fin 4096) (h : slot.val%256=127)
    (s : MachineState) (pc : s.pc=leafPC slot (11+heapExtra slot.val)) :
    fetch image s=some (.base (.ADD .x22 .x22 .x7)) := by
  apply fetch_leaf_word slot (11+heapExtra slot.val) (by rw [leaf_word_count];unfold extra nonceExtra;rw [if_pos h];omega) s pc
  by_cases heap : slot.val%45=44
  · simp only [leafWords,heapExtra,if_pos heap,if_pos h,List.cons_append,List.nil_append,
      List.getElem?_cons_succ,List.getElem?_cons_zero,Option.bind_some]
    change decodeInstruction 0x007b0b33=some (.base (.ADD .x22 .x22 .x7))
    unfold decodeInstruction
    rfl
  · simp only [leafWords,heapExtra,if_neg heap,if_pos h,List.cons_append,List.nil_append,
      List.getElem?_cons_succ,List.getElem?_cons_zero,Option.bind_some]
    change decodeInstruction 0x007b0b33=some (.base (.ADD .x22 .x22 .x7))
    unfold decodeInstruction
    rfl

/-- After leaf 4095 the salt cursor steps back one salt (the loop re-enters at leaf 1). -/
theorem fetch_salt_adjust (slot : Fin 4096) (h : slot.val=4095)
    (s : MachineState) (pc : s.pc=leafPC slot 11) :
    fetch image s=some (.base (.ADDI .x22 .x22 4080)) := by
  have heap : ¬ slot.val%45=44 := by omega
  have nonce : ¬ slot.val%256=127 := by omega
  apply fetch_leaf_word slot 11 (by rw [leaf_word_count];unfold extra heapExtra nonceExtra adjustExtra;rw [if_neg heap,if_neg nonce,if_pos h];omega) s pc
  simp only [leafWords,if_neg heap,if_neg nonce,if_pos h,List.cons_append,List.nil_append,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.bind_some]
  change decodeInstruction 0xff0b0b13=some (.base (.ADDI .x22 .x22 4080))
  unfold decodeInstruction
  rfl

end TwoPermutationPrototype.Quad.Commit.Leaves
