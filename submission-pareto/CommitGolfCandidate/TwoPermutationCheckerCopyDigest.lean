import CommitGolfCandidate.TwoPermutationCheckerCopy
import CommitGolfCandidate.TwoPermutationSyscall

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64

theorem word_offset (a b : Nat) :
    wordAddress a + BitVec.ofNat 64 (8*b) = wordAddress (a+b) :=
  (wordAddress_add a b).symm

theorem distinct_word_offset (a b i j : Nat) (ha : a+i < 2^61) (hb : b+j < 2^61)
    (apart : a+i ≠ b+j) :
    wordAddress a + BitVec.ofNat 64 (8*i) ≠ wordAddress b + BitVec.ofNat 64 (8*j) := by
  rw [word_offset, word_offset]
  exact fun equal => apart (wordAddress_injective_of_bound ha hb equal)

theorem four_word_store_word (state : MachineState) (src dest : Word) (address : Nat)
    (aligned : dest = wordAddress address) (bounded : address+4 ≤ 2^61) (i : Fin 4) :
    (Opening.fourWordStore state src dest).getMem (dest + BitVec.ofNat 64 (8*i.val)) =
      state.getMem (src + BitVec.ofNat 64 (8*i.val)) := by
  have distinct (i j : Fin 4) (different : i ≠ j) :
      dest + BitVec.ofNat 64 (8*i.val) ≠ dest + BitVec.ofNat 64 (8*j.val) := by
    rw [aligned]
    exact distinct_word_offset address address i.val j.val (by omega) (by omega) (by
      intro equal
      apply different
      apply Fin.ext
      omega)
  have d01 := distinct 0 1 (by decide)
  have d02 := distinct 0 2 (by decide)
  have d03 := distinct 0 3 (by decide)
  have d12 := distinct 1 2 (by decide)
  have d13 := distinct 1 3 (by decide)
  have d23 := distinct 2 3 (by decide)
  change dest + 0#64 ≠ dest + 8#64 at d01
  change dest + 0#64 ≠ dest + 16#64 at d02
  change dest + 0#64 ≠ dest + 24#64 at d03
  change dest + 8#64 ≠ dest + 16#64 at d12
  change dest + 8#64 ≠ dest + 24#64 at d13
  change dest + 16#64 ≠ dest + 24#64 at d23
  simp only [BitVec.add_zero] at d01 d02 d03
  fin_cases i <;>
    simp [Opening.fourWordStore, show BitVec.ofNat 64 (8*0) = 0#64 from rfl,
      show BitVec.ofNat 64 (8*1) = 8#64 from rfl,
      show BitVec.ofNat 64 (8*2) = 16#64 from rfl,
      show BitVec.ofNat 64 (8*3) = 24#64 from rfl,
      d01, d02, d03, d12, d13, d23] <;>
    rfl

/-- Adjacent scratch operands use the same four-word copy as cap frontier nodes.
With aligned disjoint endpoints the byte digest is unchanged by the copy. -/
theorem copied_digest (state : MachineState) (start src dest : Nat) (valid : CopyBlock start)
    (srcReg : state.getReg (copySource start) = wordAddress src)
    (destReg : state.getReg (copyTarget start)+BitVec.ofNat 64 (copyOffset start) = wordAddress dest)
    (srcBound : src+4 ≤ 2^61) (destBound : dest+4 ≤ 2^61)
    (apart : src+4 ≤ dest ∨ dest+4 ≤ src) :
    readBuffer (copied state start) (8*dest) 32 = readBuffer state (8*src) 32 := by
  have separate (i j : Fin 4) : state.getReg (copySource start) + BitVec.ofNat 64 (8*i.val) ≠
      state.getReg (copyTarget start) + BitVec.ofNat 64 (copyOffset start+8*j.val) := by
    rw [srcReg, BitVec.ofNat_add, ← BitVec.add_assoc, destReg]
    exact distinct_word_offset src dest i.val j.val (by omega) (by omega) (by omega)
  refine (read_digest_eq_iff _ _ _ _ (by omega) (by omega)).mpr ?_
  intro i bound
  simp only [← Nat.mul_add]
  have copy := copied_memory state start valid separate
  change (copied state start).mem (wordAddress (dest+i)) = state.getMem (wordAddress (src+i))
  rw [copy, srcReg, destReg, ← word_offset, ← word_offset]
  exact four_word_store_word state (wordAddress src) (wordAddress dest) dest rfl destBound ⟨i, bound⟩

/-- A second digest copy preserves the first half and every unread sibling. -/
theorem copied_digest_outside (state : MachineState) (start src dest read : Nat) (valid : CopyBlock start)
    (srcReg : state.getReg (copySource start) = wordAddress src)
    (destReg : state.getReg (copyTarget start)+BitVec.ofNat 64 (copyOffset start) = wordAddress dest)
    (srcBound : src+4 ≤ 2^61) (destBound : dest+4 ≤ 2^61) (readBound : read+4 ≤ 2^61)
    (apart : src+4 ≤ dest ∨ dest+4 ≤ src) (outside : read+4 ≤ dest ∨ dest+4 ≤ read) :
    readBuffer (copied state start) (8*read) 32 = readBuffer state (8*read) 32 := by
  have separate (i j : Fin 4) : state.getReg (copySource start) + BitVec.ofNat 64 (8*i.val) ≠
      state.getReg (copyTarget start) + BitVec.ofNat 64 (copyOffset start+8*j.val) := by
    rw [srcReg, BitVec.ofNat_add, ← BitVec.add_assoc, destReg]
    exact distinct_word_offset src dest i.val j.val (by omega) (by omega) (by omega)
  refine read_digest_congr _ _ _ (by omega) ?_
  intro i bounded
  simp only [← Nat.mul_add]
  change (copied state start).getMem (wordAddress (read+i)) = state.getMem (wordAddress (read+i))
  apply copied_frame _ _ valid separate
  intro j
  rw [destReg, ← word_offset]
  exact distinct_word_offset read dest i j.val (by omega) (by omega) (by omega)

theorem copied_word_outside (state : MachineState) (start src dest read : Nat) (valid : CopyBlock start)
    (srcReg : state.getReg (copySource start) = wordAddress src)
    (destReg : state.getReg (copyTarget start)+BitVec.ofNat 64 (copyOffset start) = wordAddress dest)
    (srcBound : src+4 ≤ 2^61) (destBound : dest+4 ≤ 2^61) (readBound : read < 2^61)
    (apart : src+4 ≤ dest ∨ dest+4 ≤ src) (outside : read < dest ∨ dest+4 ≤ read) :
    memoryView (copied state start) read = memoryView state read := by
  have separate (i j : Fin 4) : state.getReg (copySource start) + BitVec.ofNat 64 (8*i.val) ≠
      state.getReg (copyTarget start) + BitVec.ofNat 64 (copyOffset start+8*j.val) := by
    rw [srcReg, BitVec.ofNat_add, ← BitVec.add_assoc, destReg]
    exact distinct_word_offset src dest i.val j.val (by omega) (by omega) (by omega)
  apply copied_frame _ _ valid separate
  intro j
  rw [destReg]
  have h := distinct_word_offset read dest 0 j.val (by omega) (by omega) (by omega)
  change wordAddress read + 0#64 ≠ _ at h
  simpa only [BitVec.add_zero] using h

theorem read_word (state : MachineState) (word : Nat) :
    readBuffer state (8*word) 8 = memoryView state word := by
  have sliced := read_buffer_slice state (8*word) 32 0 8 (by decide)
  have extracted := read_digest_word state (8*word) 0 (by omega) (by decide)
  simpa only [Nat.mul_zero, Nat.add_zero, memoryView, wordAddress] using sliced.symm.trans extracted

theorem write_bits_word_outside {bits : Nat} (state : MachineState) (answer : BitVec bits)
    (dest word : Nat) (destBound : 8*dest+(bits+7)/8 ≤ 2^64) (wordBound : word < 2^61)
    (outside : 8*word+8 ≤ 8*dest ∨ 8*dest+(bits+7)/8 ≤ 8*word) :
    memoryView (writeBits state (wordAddress dest) answer) word = memoryView state word := by
  rw [← read_word, ← read_word]
  exact write_bits_read_outside state answer (8*dest) (8*word) 8 destBound (by omega) outside

end TwoPermutationPrototype.Checker
