import CommitGolfCandidate.CapPrograms
import CommitGolfCandidate.CapWorkspace

/-! Actual loader facts for the experimental cap images. The images retain the
published layout and empty data; code length may change the unused initial stack
pointer, so no whole-state equality with the old image is assumed. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

abbrev capProgram : Submission := capExperimental LOG_LENGTH

theorem cap_experimental_opening_workspace_zero
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (address : Nat) (bounded : address + 8 ≤ 32768) :
    (capProgram.initialState .opening (trapdoor, positions)).getMem
      (BitVec.ofNat 64 address) = 0 := by
  apply cap_initial_zero_word capProgram .opening _ address (by omega) rfl
  intro buffer member
  simp only [Submission.inputBuffers, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · norm_num [fixedBuffer, capProgram, capExperimental, candidate, layout,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    omega
  · simp only [positionsBuffer]
    norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    omega

theorem cap_experimental_check_workspace_zero (input : CheckInput) (address : Nat)
    (bounded : address + 8 ≤ 32768) :
    (capProgram.initialState .check input).getMem (BitVec.ofNat 64 address) = 0 := by
  apply cap_initial_zero_word capProgram .check input address (by omega) rfl
  intro buffer member
  simp only [Submission.inputBuffers, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · norm_num [fixedBuffer, capProgram, capExperimental, candidate, layout,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    omega
  · simp only [positionsBuffer]
    norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    omega
  · simp only [valuesBuffer]
    norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    omega
  · norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    omega

/-- Both address addition and the minimum-record-length multiplication are
ordinary bounded naturals, not wrapped word comparisons. -/
theorem cap_check_loader_bounds (input : CheckInput)
    (admitted : input.proof.length ≤ capProgram.sizes.proof) :
    capProgram.layout.proof + input.proof.length ≤ MEMORY_BYTES ∧
    544 * input.positions.card < 2^64 ∧
    capProgram.layout.proof + input.proof.length < 2^64 := by
  have cardinal : input.positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ input.positions
  norm_num [capProgram, capExperimental, candidate, sizes, layout, trapdoorBytes,
    openingBytes, LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES, MEMORY_BYTES] at admitted cardinal ⊢
  omega

theorem cap_check_required_length (input : CheckInput) :
    ((capProgram.initialState .check input).getReg .x16 * BitVec.ofNat 64 544).toNat =
      544 * input.positions.card := by
  have cardinal : input.positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ input.positions
  change (BitVec.ofNat 64 input.positions.card * BitVec.ofNat 64 544).toNat = _
  rw [← BitVec.ofNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  · omega
  · norm_num [LENGTH, LOG_LENGTH] at cardinal
    omega

theorem cap_check_proof_end (input : CheckInput)
    (admitted : input.proof.length ≤ capProgram.sizes.proof) :
    ((capProgram.initialState .check input).getReg .x15 +
      (capProgram.initialState .check input).getReg .x17).toNat =
        capProgram.layout.proof + input.proof.length := by
  change (BitVec.ofNat 64 capProgram.layout.proof +
    BitVec.ofNat 64 input.proof.length).toNat = _
  rw [← BitVec.ofNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (cap_check_loader_bounds input admitted).2.2]
end CommitGolfCandidate
