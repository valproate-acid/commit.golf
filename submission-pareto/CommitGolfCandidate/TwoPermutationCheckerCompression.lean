import CommitGolfCandidate.TwoPermutationCheckerLeafRun

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling

attribute [local irreducible] execute readBuffer writeBits

theorem oracle_input_compression (state : MachineState) (src dst : Nat)
    (srcBound : src + 8 ≤ 2 ^ 33) (dstBound : dst + 4 ≤ 2 ^ 33)
    (input : state.getReg .x10 = wordAddress src) (output : state.getReg .x12 = wordAddress dst)
    (size : state.getReg .x11 = 64) (primitive : state.getReg .x13 = 0) :
    oracleInput state = some (.inl (readBuffer state (8*src) 64)) := by
  have srcValue := word_address_value (word := src) (by omega)
  have dstValue := word_address_value (word := dst) (by omega)
  have fitsSrc : 8 * src + 64 ≤ MEMORY_BYTES := by unfold MEMORY_BYTES; omega
  have fitsDst : 8 * dst + 32 ≤ MEMORY_BYTES := by unfold MEMORY_BYTES; omega
  have kind : (state.getReg .x13).toNat = 0 := by rw [primitive]; rfl
  unfold oracleInput
  dsimp only
  rw [kind]
  simp [input, output, size, srcValue, dstValue, rangeValid, fitsSrc, fitsDst,
    COMPRESSION_INPUT_LENGTH, COMPRESSION_OUTPUT_LENGTH]

/-- A compression call uses the exact little-endian byte pair in memory. The
same syscall lemma serves the sixteen lower levels and the eight cap levels. -/
theorem execute_compression_call (fuel : Nat) (state : MachineState) (src dst : Nat)
    (srcBound : src + 8 ≤ 2 ^ 33) (dstBound : dst + 4 ≤ 2 ^ 33)
    (input : state.getReg .x10 = wordAddress src) (output : state.getReg .x12 = wordAddress dst)
    (selector : state.getReg .x5 = 0) (size : state.getReg .x11 = 64) (primitive : state.getReg .x13 = 0)
    (fetched : fetch checkerImage state = some (.base .ECALL)) :
    execute checkerImage (fuel + 1) state false = (do
      let answer ← World.query (.inr (.inl (readBuffer state (8 * src) 64)))
      let result ← execute checkerImage fuel (writeBits state (wordAddress dst) answer) false
      return result.charge 8 1) := by
  have ready := oracle_input_compression state src dst srcBound dstBound input output size primitive
  simp only [execute, fetched, selector, ↓reduceIte, ready, output, writeOracleAnswer, oracleCycles,
    COMPRESSION_CYCLES]

theorem compressed_digest (state : MachineState) (dst : Nat) (answer : BitVec 256) :
    readBuffer (writeBits state (wordAddress dst) answer) (8*dst) 32 = answer := by
  simpa only [wordAddress, Nat.add_zero, Nat.mul_zero, BitVec.extractLsb'_eq_self] using
    write_bits_digest state (8*dst) 0 answer (by decide) (by decide)

theorem path_pair_read (state : MachineState) (src node : Nat) (digest sibling : BitVec 256)
    (low : readBuffer state (8*src) 32 = if node % 2 = 0 then digest else sibling)
    (high : readBuffer state (8*src+32) 32 = if node % 2 = 0 then sibling else digest) :
    readBuffer state (8*src) 64 = pathPair node digest sibling := by
  rw [read_compression_halves state (8*src) (by omega), high, low]
  by_cases parity : node % 2 = 0 <;> simp [pathPair, parity]

end TwoPermutationPrototype.Checker
