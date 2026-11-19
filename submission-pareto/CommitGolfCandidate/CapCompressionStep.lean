import CommitGolfCandidate.CapMarkPassExecution

/-! Generic compression bridge for the cap checker. Input is snapped before
the parent reply is written. The source/destination checks and image fetch
remain explicit, and arbitrary replies preserve finalized marks and ABI bytes. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] readBuffer

def capCompressionInput (state : MachineState) : PublicSpec.Domain :=
  .inl (readBuffer state (state.getReg .x10).toNat 64)

def capCompressionAnswer (state : MachineState) (answer : BitVec 256) : MachineState :=
  writeBits state (state.getReg .x12) answer

/-- One real ECALL pays eight cycles and one public query, on either coin policy. -/
theorem cap_compression_execute (image : Image) (state : MachineState)
    (fetched : fetch image state = some (.base .ECALL))
    (selectors : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (sourceValid : rangeValid (state.getReg .x10) 64 = true)
    (destinationValid : rangeValid (state.getReg .x12) 32 = true)
    (sourceAligned : (state.getReg .x10).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x12).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (1 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (capCompressionInput state))
          let result ← execute image fuel (capCompressionAnswer state answer) allowCoins
          return result.charge 8 1) := by
  have input : oracleInput state = some (capCompressionInput state) := by
    simp [oracleInput, capCompressionInput, selectors.2.2, selectors.2.1,
      COMPRESSION_INPUT_LENGTH, COMPRESSION_OUTPUT_LENGTH, sourceValid, destinationValid]
    refine ⟨⟨sourceAligned, destinationAligned⟩, ?_⟩
    rw [selectors.2.2]
    exact BitVec.setWidth_eq _
  rw [Nat.add_comm 1 fuel, execute, fetched, if_pos selectors.1, input]
  simp [capCompressionAnswer, writeOracleAnswer, selectors.2.2,
    oracleCycles, COMPRESSION_CYCLES, Execution.charge]
  rfl

theorem cap_compression_register (state : MachineState) (answer : BitVec 256)
    (reg : Reg) :
    (capCompressionAnswer state answer).getReg reg = state.getReg reg :=
  writeBits_register state _ answer reg

/-- Adjacent root slots are exactly right ++ left in the fixed compression ABI. -/
theorem cap_compression_halves (state : MachineState) (source : Nat)
    (pointer : state.getReg .x10 = BitVec.ofNat 64 source)
    (bounded : source < 2^64) (aligned : source % 8 = 0) :
    capCompressionInput state =
      .inl (readBuffer state (source + 32) 32 ++ readBuffer state source 32) := by
  unfold capCompressionInput
  rw [pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded,
    read_compression_halves state source aligned]

theorem cap_compression_answer_digest (state : MachineState) (destination : Nat)
    (answer : BitVec 256)
    (pointer : state.getReg .x12 = BitVec.ofNat 64 destination) :
    readBuffer (capCompressionAnswer state answer) destination 32 = answer := by
  unfold capCompressionAnswer
  rw [pointer]
  have written := write_bits_digest state destination 0 answer (by decide) (by decide)
  simpa only [Nat.add_zero, Nat.mul_zero, BitVec.extractLsb'_eq_self] using written

theorem cap_compression_high_bytes (state reference : MachineState)
    (destination : Nat) (answer : BitVec 256)
    (pointer : state.getReg .x12 = BitVec.ofNat 64 destination)
    (low : destination + 32 ≤ 32768) (frame : CapHighBytes state reference) :
    CapHighBytes (capCompressionAnswer state answer) reference := by
  unfold capCompressionAnswer
  rw [pointer]
  exact cap_high_bytes_reply state reference destination answer low frame

/-- A reply wholly below the mark region preserves every finalized mark word. -/
theorem cap_compression_marks (state : MachineState) (destination : Nat)
    (answer : BitVec 256) (node : Nat)
    (pointer : state.getReg .x12 = BitVec.ofNat 64 destination)
    (low : destination + 32 ≤ 28672) (bounded : node < 512) :
    (capCompressionAnswer state answer).getMem (capMarkAddress node) =
      state.getMem (capMarkAddress node) := by
  unfold capCompressionAnswer
  rw [pointer]
  apply writeBits_memory_outside
  intro offset inside equal
  have addressSmall : destination + offset < 28672 := by omega
  have alignedLow :
      (alignToDword (BitVec.ofNat 64 destination + BitVec.ofNat 64 offset)).toNat < 28672 := by
    rw [← BitVec.ofNat_add]
    have masked : (alignToDword (BitVec.ofNat 64 (destination + offset))).toNat ≤
        (BitVec.ofNat 64 (destination + offset)).toNat := by
      simp only [alignToDword, BitVec.toNat_and]
      exact Nat.and_le_left
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : destination + offset < 2^64)] at masked
    omega
  have numeric := congrArg BitVec.toNat equal
  have markNat : (capMarkAddress node).toNat = 28672 + 8 * node := by
    simp only [capMarkAddress, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 28672 + 8 * node < 2^64)]
  rw [markNat] at numeric
  omega

theorem cap_compression_ready (state : MachineState) (destination : Nat)
    (answer : BitVec 256) (marked : Nat → Bool)
    (pointer : state.getReg .x12 = BitVec.ofNat 64 destination)
    (low : destination + 32 ≤ 28672) (ready : CapMarksReady state 256 0 marked) :
    CapMarksReady (capCompressionAnswer state answer) 256 0 marked := by
  intro node positive bounded
  rw [cap_compression_marks state destination answer node pointer low bounded]
  exact ready node positive bounded

end CommitGolfCandidate
