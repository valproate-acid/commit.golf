import CommitGolfCandidate.Memory
import CommitGolfCandidate.WriteMemory
import CommitGolfCandidate.TwoPermutationMemoryBridge

/-! Trusted syscall selection and little-endian input for the aligned permutation
windows. The digit and out-of-range byte lemmas are reused from the existing candidate. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv OracleComp RiscvZkvm.Rv64
set_option maxRecDepth 4096

def bufferByte (words : Words 25) (index : Nat) : Byte :=
  if h : index / 8 < 25 then extractByte (words ⟨index / 8, h⟩) (index % 8) else 0

def packBuffer (words : Words 25) : BitVec 1600 :=
  BitVec.ofNat 1600 (∑ byte ∈ Finset.range 200, (bufferByte words byte).toNat * 2 ^ (8 * byte))

theorem get_byte_window (state : MachineState) (start : Nat) {byte : Nat} (inside : byte < 200) :
    state.getByte (BitVec.ofNat 64 (8 * start + byte)) = bufferByte (window (memoryView state) start) byte := by
  have split : 8 * start + byte = 8 * (start + byte / 8) + byte % 8 := by omega
  have offset : byte % 8 < 8 := by omega
  have word : byte / 8 < 25 := by omega
  rw [split, CommitGolfCandidate.aligned_byte state (start + byte / 8) (byte % 8) (by omega)]
  simp [bufferByte, word, window, memoryView, wordAddress, Nat.div_eq_of_lt offset, Nat.mod_eq_of_lt offset]

theorem read_permutation_window (state : MachineState) (start : Nat) :
    readBuffer state (8 * start) 200 = packBuffer (window (memoryView state) start) := by
  unfold readBuffer packBuffer
  apply congrArg (BitVec.ofNat 1600)
  apply Finset.sum_congr rfl
  intro byte present
  rw [get_byte_window state start (Finset.mem_range.mp present)]

theorem word_address_value {word : Nat} (bounded : word < 2 ^ 61) : (wordAddress word).toNat = 8 * word := by
  rw [wordAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  omega

theorem oracle_input_permutation (state : MachineState) (src dst : Nat)
    (srcBound : src + 25 ≤ 2 ^ 33) (dstBound : dst + 25 ≤ 2 ^ 33)
    (input : state.getReg .x10 = wordAddress src) (output : state.getReg .x12 = wordAddress dst)
    (size : state.getReg .x11 = 200) (primitive : state.getReg .x13 = 1) :
    oracleInput state = some (.inr (.inl (packBuffer (window (memoryView state) src)))) := by
  have srcValue := word_address_value (word := src) (by omega)
  have dstValue := word_address_value (word := dst) (by omega)
  have fitsSrc : 8 * src + 200 ≤ MEMORY_BYTES := by unfold MEMORY_BYTES; omega
  have fitsDst : 8 * dst + 200 ≤ MEMORY_BYTES := by unfold MEMORY_BYTES; omega
  have kind : (state.getReg .x13).toNat = 1 := by rw [primitive]; rfl
  unfold oracleInput
  dsimp only
  rw [kind]
  simp [input, output, size, srcValue, dstValue, rangeValid,
    fitsSrc, fitsDst, PERMUTATION_WIDTH, read_permutation_window]

theorem execute_permutation_call (image : Image) (fuel : Nat) (state : MachineState) (allowCoins : Bool)
    (src dst : Nat) (srcBound : src + 25 ≤ 2 ^ 33) (dstBound : dst + 25 ≤ 2 ^ 33)
    (input : state.getReg .x10 = wordAddress src) (output : state.getReg .x12 = wordAddress dst)
    (selector : state.getReg .x5 = 0) (size : state.getReg .x11 = 200) (primitive : state.getReg .x13 = 1)
    (fetched : fetch image state = some (.base .ECALL)) :
    execute image (fuel + 1) state allowCoins = (do
      let answer ← World.query (.inr (.inr (.inl (packBuffer (window (memoryView state) src)))))
      let result ← execute image fuel (writeBits state (wordAddress dst) answer) allowCoins
      pure (result.charge 8 1)) := by
  have ready := oracle_input_permutation state src dst srcBound dstBound input output size primitive
  simp only [execute, fetched, selector, ↓reduceIte, ready, output, writeOracleAnswer, oracleCycles, PERMUTATION_CYCLES]

def replyWords (reply : BitVec 1600) : Words 25 := fun i => reply.extractLsb' (64 * i.val) 64

private theorem read_one_word (state : MachineState) (word : Nat) :
    readBuffer state (8 * word) 8 = memoryView state word := by
  have sliced := CommitGolfCandidate.read_buffer_slice state (8 * word) 32 0 8 (by decide)
  have extracted := CommitGolfCandidate.read_digest_word state (8 * word) 0 (by omega) (by decide)
  simpa only [Nat.mul_zero, Nat.add_zero, memoryView, wordAddress] using sliced.symm.trans extracted

theorem permutation_write_memory (state : MachineState) (dst word : Nat) (reply : BitVec 1600)
    (dstBound : dst + 25 ≤ 2 ^ 33) (wordBound : word < 2 ^ 33) :
    memoryView (writeBits state (wordAddress dst) reply) word =
      writeWindow (memoryView state) dst (replyWords reply) word := by
  let written := writeBits state (wordAddress dst) reply
  rw [← read_one_word written]
  by_cases inside : dst ≤ word ∧ word < dst + 25
  · rw [writeWindow, dite_eq_left inside]
    change readBuffer written (8 * word) 8 = reply.extractLsb' (64 * (word - dst)) 64
    rw [show 64 * (word - dst) = 8 * (8 * (word - dst)) by omega]
    apply CommitGolfCandidate.read_serialized_slice written reply (8 * word) (8 * (word - dst)) 8
    intro index limit
    have offset : 8 * (word - dst) + index < 200 := by omega
    have byte := CommitGolfCandidate.write_bits_byte state (wordAddress dst) reply (8 * (word - dst) + index) (by omega) (by decide)
    simpa only [written, wordAddress, ← BitVec.ofNat_add,
      show 8 * dst + (8 * (word - dst) + index) = 8 * word + index by omega] using byte
  · rw [writeWindow, dite_eq_right inside, ← read_one_word state]
    apply congrArg (BitVec.ofNat 64)
    apply Finset.sum_congr rfl
    intro index present
    have indexBound := Finset.mem_range.mp present
    have separate : ∀ offset < 200, BitVec.ofNat 64 (8 * word + index) ≠
        wordAddress dst + BitVec.ofNat 64 offset := by
      intro offset offsetBound equal
      have numeric := congrArg BitVec.toNat equal
      rw [wordAddress, ← BitVec.ofNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 8 * word + index < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 8 * dst + offset < 2 ^ 64)] at numeric
      omega
    rw [CommitGolfCandidate.write_bits_byte_outside state (wordAddress dst) _ reply (by simpa using separate)]

end TwoPermutationPrototype.RV64
