import CommitGolfCandidate.CapInputBytes
import CommitGolfCandidate.WriteMemory

/-! A memory frame for the cap checker's input buffers. Scratch, root slots and
marks lie below 22,528; every ABI input lies above that boundary. This frame
allows loader identities to be transported after stores and oracle replies. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def CapHighBytes (state reference : MachineState) : Prop :=
  ∀ address, 32768 ≤ address → address < 2^64 →
    state.getByte (BitVec.ofNat 64 address) = reference.getByte (BitVec.ofNat 64 address)

theorem cap_high_bytes_refl (state : MachineState) : CapHighBytes state state :=
  fun _ _ _ => rfl

theorem cap_high_bytes_memory (state next reference : MachineState)
    (same : next.mem = state.mem) (frame : CapHighBytes state reference) :
    CapHighBytes next reference := by
  intro address lower upper
  rw [show next.getByte = state.getByte by
    unfold MachineState.getByte MachineState.getMem
    rw [same]]
  exact frame address lower upper

/-- A word store to the low workspace preserves all high input bytes. -/
theorem cap_high_bytes_store (state reference : MachineState) (destination : Nat) (value : Word)
    (low : destination < 32768) (frame : CapHighBytes state reference) :
    CapHighBytes (state.setMem (BitVec.ofNat 64 destination) value) reference := by
  intro address lower upper
  have decomposition : 8 * (address / 8) + address % 8 = address := by omega
  have distinct : BitVec.ofNat 64 (8 * (address / 8)) ≠ BitVec.ofNat 64 destination := by
    intro equal
    have numeric := congrArg BitVec.toNat equal
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 8 * (address / 8) < 2^64),
      Nat.mod_eq_of_lt (by omega : destination < 2^64)] at numeric
    omega
  conv_lhs => rw [← decomposition]
  rw [aligned_byte _ (address / 8) (address % 8) (by omega),
    show 8 * (address / 8) + 8 * ((address % 8) / 8) = 8 * (address / 8) by omega,
    show (address % 8) % 8 = address % 8 by omega,
    MachineState.getMem_setMem_ne distinct]
  have original := aligned_byte state (address / 8) (address % 8) (by omega)
  simp only [Nat.div_eq_of_lt (by omega : address % 8 < 8), Nat.mul_zero,
    Nat.add_zero, Nat.mod_eq_of_lt (by omega : address % 8 < 8), decomposition] at original
  exact original.symm.trans (frame address lower upper)

/-- Every byte of an oracle reply must lie in the low workspace. No assumption
about the reply value or consistency of consecutive replies is required. -/
theorem cap_high_bytes_reply {bits : Nat} (state reference : MachineState)
    (destination : Nat) (answer : BitVec bits)
    (low : destination + (bits+7)/8 ≤ 32768) (frame : CapHighBytes state reference) :
    CapHighBytes (writeBits state (BitVec.ofNat 64 destination) answer) reference := by
  intro address lower upper
  rw [write_bits_byte_outside]
  · exact frame address lower upper
  · intro offset inside equal
    have numeric := congrArg BitVec.toNat equal
    rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt upper,
      Nat.mod_eq_of_lt (by omega : destination + offset < 2^64)] at numeric
    omega

/-- Framed runs can reuse the exact proof-byte loader fact at any later state. -/
theorem cap_framed_proof_byte (input : CheckInput) (state : MachineState) (offset : Nat)
    (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (inside : offset < input.proof.length)
    (frame : CapHighBytes state (capProgram.initialState .check input)) :
    state.getByte (BitVec.ofNat 64 (capProgram.layout.proof + offset)) =
      input.proof[offset]?.getD 0 := by
  rw [frame]
  · exact cap_check_input_proof_byte input offset admitted inside
  · norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    omega
  · have bounded := (cap_check_loader_bounds input admitted).2.2
    omega
end CommitGolfCandidate
