import CommitGolfCandidate.InputMemory

/-! Initialization and address facts for the prospective cap workspace. Fetch
reads image.code independently of memory; the zero proof concerns only embedded
data and actual phase input buffers, not the nominal commitment message range. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def capRootsBase : Nat := 12288
def capMarksBase : Nat := 28672
def capStackBase : Nat := 1024

theorem cap_workspace_ranges :
    capStackBase + 1024 ≤ capRootsBase ∧
    capRootsBase + 512*32 = capMarksBase ∧
    capMarksBase + 512*8 = 32768 ∧
    capRootsBase % 8 = 0 ∧ capMarksBase % 8 = 0 ∧ capStackBase % 8 = 0 := by
  decide

theorem cap_child_parent_separate (node : Nat) (positive : 1 ≤ node) (bounded : node < 256) :
    capRootsBase + 32*node + 32 ≤ capRootsBase + 32*(2*node) ∧
    capRootsBase + 32*(2*node) + 64 ≤ capMarksBase := by
  norm_num [capRootsBase, capMarksBase]
  omega

/-- A zero word follows from the actual loader when all phase input buffers begin
after it and there is no embedded data. The nominal message range is irrelevant. -/
theorem cap_initial_zero_word (candidate : Submission) (program : Program)
    (input : Input candidate.sizes program) (address : Nat)
    (bounded : address < 2^64) (noData : (candidate.image program).data = [])
    (beforeInputs : ∀ buffer ∈ candidate.inputBuffers program input, address + 8 ≤ buffer.address) :
    (candidate.initialState program input).getMem (BitVec.ofNat 64 address) = 0 := by
  rw [initial_input_word candidate program input address bounded]
  have bytes (offset : Nat) (small : offset < 8) :
      inputByte candidate program input (address + offset) = 0 := by
    have noneSelected : (candidate.inputBuffers program input).find?
        (fun buffer => decide (buffer.address ≤ address + offset ∧
          address + offset < buffer.address + buffer.length)) = none := by
      apply List.find?_eq_none.mpr
      intro buffer member
      have lower := beforeInputs buffer member
      simp only [Bool.not_eq_true, decide_eq_false_iff_not]
      omega
    unfold inputByte
    rw [noneSelected]
    simp [noData]
  have zero : (∑ offset ∈ Finset.range 8,
      (inputByte candidate program input (address + offset)).toNat * 2^(8*offset)) = 0 := by
    apply Finset.sum_eq_zero
    intro offset member
    rw [bytes offset (Finset.mem_range.mp member)]
    simp
  rw [zero]
  rfl

/-- The current opening loader initializes the entire proposed workspace to zero.
The eventual cap image must retain empty data and the same input layout. -/
theorem cap_opening_workspace_zero (trapdoor : BitVec (8*submission.sizes.trapdoor))
    (positions : Positions) (address : Nat) (bounded : address + 8 ≤ 32768) :
    (submission.initialState .opening (trapdoor, positions)).getMem (BitVec.ofNat 64 address) = 0 := by
  apply cap_initial_zero_word submission .opening _ address (by omega) rfl
  intro buffer member
  simp only [Submission.inputBuffers, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · norm_num [fixedBuffer, submission, candidate, layout, LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    omega
  · simp only [positionsBuffer]
    norm_num [submission, candidate, layout, trapdoorBytes, LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    omega

theorem cap_check_workspace_zero (input : CheckInput) (address : Nat)
    (bounded : address + 8 ≤ 32768) :
    (submission.initialState .check input).getMem (BitVec.ofNat 64 address) = 0 := by
  apply cap_initial_zero_word submission .check input address (by omega) rfl
  intro buffer member
  simp only [Submission.inputBuffers, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · norm_num [fixedBuffer, submission, candidate, layout, LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    omega
  · simp only [positionsBuffer]
    norm_num [submission, candidate, layout, trapdoorBytes, LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    omega
  · simp only [valuesBuffer]
    norm_num [submission, candidate, layout, trapdoorBytes, LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    omega
  · norm_num [submission, candidate, layout, trapdoorBytes, LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    omega
end CommitGolfCandidate
