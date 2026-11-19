import CommitGolfCandidate.ProjectedCompression
import CommitGolfCandidate.CapCompressionStep
import CommitGolfCandidate.WriteMemory

/-! A hardware SH of zero at offset 30 clears precisely the two high bytes
of a compression reply. This segment accepts both commit and checker images. -/
namespace CommitGolfCandidate.ShortTree
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] readBuffer

private theorem last_mask (x : BitVec 256) :
    replaceHalfword (x.extractLsb' 192 64) 3 0 = (padLow x).extractLsb' 192 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit hb
  simp only [replaceHalfword, padLow, low240, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not]
  interval_cases bit <;> simp

private theorem low_words (x : BitVec 256) (w : Nat) (hw : w < 3) :
    x.extractLsb' (64*w) 64 = (padLow x).extractLsb' (64*w) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit hb
  have inside : 64*w+bit < 240 := by omega
  change (x.extractLsb' (64*w) 64).getLsbD bit =
    (((0 : BitVec 16) ++ low240 x).extractLsb' (64*w) 64).getLsbD bit
  simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_append (x := (0 : BitVec 16)) (y := low240 x) (i := 64*w+bit),
    if_pos inside]
  simp [low240, BitVec.getLsbD_extractLsb', inside]

private theorem output_word (state : MachineState) (base k : Nat) (answer : BitVec 256)
    (aligned : base % 8 = 0) (inside : k < 4) :
    (writeBits state (BitVec.ofNat 64 base) answer).getMem (BitVec.ofNat 64 (base+8*k)) =
      answer.extractLsb' (64*k) 64 := by
  have written := write_bits_digest state base 0 answer (by decide) (by decide)
  simp only [Nat.add_zero, Nat.mul_zero, BitVec.extractLsb'_eq_self] at written
  rw [← read_digest_word _ _ _ aligned inside, written]

private theorem byte_offset (a : Word) : byteOffset a = a.toNat % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod _ 3

private theorem split_address (a : Word) : alignToDword a + BitVec.ofNat 64 (byteOffset a) = a := by
  unfold alignToDword byteOffset
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have disjoint : (a &&& ~~~7#64) &&& (a &&& 7#64) = 0 := by
    ext i
    simp only [BitVec.getElem_and, BitVec.getElem_not]
    cases h : (7#64)[i] <;> simp
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ disjoint]
  ext i
  simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
  cases h : (7#64)[i] <;> simp

private theorem word_address (base i : Nat) (aligned : base % 8 = 0) :
    alignToDword (BitVec.ofNat 64 (base+i)) = BitVec.ofNat 64 (base+8*(i/8)) := by
  have offset : byteOffset (BitVec.ofNat 64 (base+i)) = i%8 := by
    rw [byte_offset, BitVec.toNat_ofNat]; omega
  have parts := split_address (BitVec.ofNat 64 (base+i))
  rw [offset] at parts
  have joined : BitVec.ofNat 64 (base+8*(i/8)) + BitVec.ofNat 64 (i%8) =
      BitVec.ofNat 64 (base+i) := by
    rw [← BitVec.ofNat_add]; congr 1; omega
  have eq := congrArg (fun v : Word => v - BitVec.ofNat 64 (i%8)) (parts.trans joined.symm)
  simpa only [BitVec.add_sub_cancel] using eq

/-- The result memory is exactly what the padded oracle response would
have written, including every unaligned memory lookup outside that reply. -/
theorem masked_reply_memory (state : MachineState) (base : Nat) (answer : BitVec 256)
    (aligned : base % 8 = 0) (bound : base + 32 ≤ 2^64) :
    ((writeBits state (BitVec.ofNat 64 base) answer).setHalfword
      (BitVec.ofNat 64 (base+30)) 0).mem =
    (writeBits state (BitVec.ofNat 64 base) (padLow answer)).mem := by
  have off : byteOffset (BitVec.ofNat 64 (base+30)) = 6 := by
    rw [byte_offset, BitVec.toNat_ofNat]; omega
  have addr : alignToDword (BitVec.ofNat 64 (base+30)) = BitVec.ofNat 64 (base+24) :=
    word_address base 30 aligned
  funext q
  change (((writeBits state (BitVec.ofNat 64 base) answer).setHalfword _ 0).getMem q) = _
  by_cases last : q = BitVec.ofNat 64 (base+24)
  · subst q
    rw [MachineState.setHalfword, addr, off, MachineState.getMem_setMem_eq]
    change replaceHalfword _ 3 _ = (writeBits state _ _).getMem (BitVec.ofNat 64 (base+8*3))
    rw [output_word state base 3 _ aligned (by decide), output_word state base 3 _ aligned (by decide)]
    exact last_mask answer
  · rw [MachineState.setHalfword, addr, MachineState.getMem_setMem_ne last]
    by_cases someWord : ∃ k < 4, q = BitVec.ofNat 64 (base+8*k)
    · obtain ⟨k, hk, rfl⟩ := someWord
      change _ = (writeBits state _ _).getMem _
      rw [output_word state base k _ aligned hk, output_word state base k _ aligned hk]
      apply low_words
      by_contra! large
      have eq : k=3 := by omega
      exact last (by rw [eq])
    · have away : ∀ i < 32, q ≠ alignToDword (BitVec.ofNat 64 base + BitVec.ofNat 64 i) := by
        intro i hi eq; apply someWord
        exact ⟨i/8, by omega, eq.trans (by rw [← BitVec.ofNat_add, word_address base i aligned])⟩
      exact (writeBits_memory_outside state _ q answer away).trans
        (writeBits_memory_outside state _ q (padLow answer) away).symm


private theorem write_frame {bits : Nat} (state : MachineState) (address : Word) (answer : BitVec bits) :
    writeBits state address answer =
      { state with mem := (writeBits state address answer).mem, pc := state.pc+4 } := by
  let put (s : MachineState) (i : Nat) := s.setByte (address + BitVec.ofNat 64 i)
      (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))
  have onlyMemory (is : List Nat) (s : MachineState) :
      is.foldl put s = { s with mem := (is.foldl put s).mem } := by
    induction is generalizing s with
    | nil => rfl
    | cons i rest ih => exact ih (put s i)
  unfold writeBits
  change ((List.range ((bits+7)/8)).foldl put state).setPC (state.pc+4) = _
  rw [onlyMemory (List.range ((bits+7)/8)) state]
  rfl

theorem masked_reply_step (state : MachineState) (base : Nat) (answer : BitVec 256)
    (dest : state.getReg .x12 = BitVec.ofNat 64 base)
    (aligned : base % 8 = 0) (bound : base + 32 ≤ 2^64) :
    execInstrBr (capCompressionAnswer state answer) (.SH .x12 .x0 30) =
      (capCompressionAnswer state (padLow answer)).setPC (state.pc+8) := by
  have clear := masked_reply_memory state base answer aligned bound
  change ((writeBits state (state.getReg .x12) answer).setHalfword
      ((writeBits state (state.getReg .x12) answer).getReg .x12 + signExtend12 30)
      0).setPC ((writeBits state (state.getReg .x12) answer).pc + 4) = _
  rw [writeBits_register, dest]
  change (((writeBits state (BitVec.ofNat 64 base) answer).setHalfword
      (BitVec.ofNat 64 base + BitVec.ofNat 64 30) 0).setPC _) = _
  rw [← BitVec.ofNat_add]
  unfold capCompressionAnswer
  rw [dest]
  have rawFrame := write_frame state (BitVec.ofNat 64 base) answer
  have padFrame := write_frame state (BitVec.ofNat 64 base) (padLow answer)
  generalize writeBits state (BitVec.ofNat 64 base) answer = raw at clear rawFrame ⊢
  generalize writeBits state (BitVec.ofNat 64 base) (padLow answer) = padded at clear padFrame ⊢
  cases state
  cases raw
  cases padded
  simp only [MachineState.mk.injEq] at rawFrame padFrame
  simp only [MachineState.setPC, MachineState.setHalfword, MachineState.setMem,
    MachineState.mk.injEq] at clear ⊢
  simp_all [BitVec.add_assoc]

end CommitGolfCandidate.ShortTree
