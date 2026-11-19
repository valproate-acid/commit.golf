import CommitGolfCandidate.TwoPermutationOpeningBlocks
import CommitGolfCandidate.TwoPermutationOpeningGeometry

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64

theorem word_at (address i : Nat) :
    BitVec.ofNat 64 address + BitVec.ofNat 64 (8 * i) = BitVec.ofNat 64 (address + 8 * i) :=
  (BitVec.ofNat_add address (8 * i)).symm

theorem nat_address_injective {left right : Nat}
    (leftBound : left < 2 ^ 64) (rightBound : right < 2 ^ 64)
    (same : BitVec.ofNat 64 left = BitVec.ofNat 64 right) : left = right := by
  have x := congrArg BitVec.toNat same
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt leftBound,
    Nat.mod_eq_of_lt rightBound] at x
  exact x

theorem aligned_access (address : Nat) (aligned : address % 8 = 0)
    (bounded : address + 8 ≤ MEMORY_BYTES) :
    accessValid (BitVec.ofNat 64 address) 8 = true := by
  have small : address < 2 ^ 64 := by
    unfold MEMORY_BYTES at bounded
    omega
  have natural : (BitVec.ofNat 64 address).toNat = address := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  simp [accessValid, rangeValid, natural, aligned, bounded]

/-- Byte loading uses the same aligned word window as the ordinary LD/SD pairs. -/
theorem copied_buffer (before after : MachineState) (source dest words : Nat)
    (sourceAligned : source % 8 = 0) (destAligned : dest % 8 = 0)
    (small : words ≤ 8)
    (copied : ∀ i < words, after.getMem (BitVec.ofNat 64 (dest + 8 * i)) =
      before.getMem (BitVec.ofNat 64 (source + 8 * i))) :
    readBuffer after dest (8 * words) = readBuffer before source (8 * words) := by
  obtain ⟨src, rfl⟩ : ∃ a, source = 8*a := ⟨source/8, by omega⟩
  obtain ⟨dst, rfl⟩ : ∃ a, dest = 8*a := ⟨dest/8, by omega⟩
  unfold readBuffer
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have bounded := Finset.mem_range.mp hi
  rw [aligned_byte after dst i (by omega), aligned_byte before src i (by omega),
    copied (i / 8) (by omega)]

theorem separated_words (source dest words : Nat)
    (ordered : source + 8 * words ≤ dest)
    (bounded : dest + 8 * words ≤ MEMORY_BYTES) (i j : Fin words) :
    BitVec.ofNat 64 source + BitVec.ofNat 64 (8 * i.val) ≠
      BitVec.ofNat 64 dest + BitVec.ofNat 64 (8 * j.val) := by
  rw [word_at, word_at]
  have hi := i.isLt
  have hj := j.isLt
  unfold MEMORY_BYTES at bounded
  intro same
  have equal := nat_address_injective (by omega) (by omega) same
  omega

/-- The natural address requested by the integer/shift arithmetic in the nonce block. -/
theorem nonce_address (state : MachineState) (index : Nat)
    (base : state.getReg .x22 = BitVec.ofNat 64 nonceBase)
    (value : state.getMem (state.getReg .x8) = BitVec.ofNat 64 index) :
    nonceSource state = BitVec.ofNat 64 (nonceBase + 16 * index) := by
  rw [nonceSource, base, value, BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 nonceBase + BitVec.ofNat 64 index * BitVec.ofNat 64 16 = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm index]

theorem nonce_copies (state : MachineState) (source dest : Nat)
    (src : nonceSource state = BitVec.ofNat 64 source)
    (dst : state.getReg .x21 = BitVec.ofNat 64 dest)
    (sourceAligned : source % 8 = 0) (destAligned : dest % 8 = 0)
    (ordered : source + 16 ≤ dest) (bounded : dest + 16 ≤ MEMORY_BYTES) :
    readBuffer (noncePrefix state 10) dest 16 = readBuffer state source 16 := by
  have disjoint : nonceSource state + 8 ≠ state.getReg .x21 := by
    rw [src, dst]
    simpa using separated_words source dest 2 ordered bounded 1 0
  have adjacent : BitVec.ofNat 64 dest + 8 ≠ BitVec.ofNat 64 dest := by
    intro same
    have eq : BitVec.ofNat 64 (dest + 8) = BitVec.ofNat 64 dest :=
      (word_at dest 1).symm.trans same
    unfold MEMORY_BYTES at bounded
    have := nat_address_injective (by omega) (by omega) eq
    omega
  apply copied_buffer state _ source dest 2 sourceAligned destAligned (by decide)
  intro i hi
  simp only [MachineState.getMem, (nonce_post state disjoint).1, src, dst]
  interval_cases i
  · simpa [MachineState.getMem] using
      (MachineState.getMem_setMem_ne (Ne.symm adjacent) (s := state.setMem
        (BitVec.ofNat 64 dest) _)).trans MachineState.getMem_setMem_eq
  · rw [← word_at dest 1, ← word_at source 1]
    exact MachineState.getMem_setMem_eq

/-- Input memory is immutable after entry, including between adjacent records. -/
def SameOpeningInput (before after : MachineState) : Prop :=
  ∀ address : Nat, trapdoorBase ≤ address → address < proofBase →
    after.getMem (BitVec.ofNat 64 address) = before.getMem (BitVec.ofNat 64 address)

/-- An ordinal record copies the serialized nonce of the sorted ABI position into
its exact proof slot. The state may already contain any earlier records. -/
theorem ordinal_nonce_bytes (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (ordinal : Nat) (bounded : ordinal < positions.card) (state : MachineState)
    (indexPointer : state.getReg .x8 = BitVec.ofNat 64 (indicesBase + 8 * ordinal))
    (noncePointer : state.getReg .x22 = BitVec.ofNat 64 nonceBase)
    (outputPointer : state.getReg .x21 = BitVec.ofNat 64 (recordBase ordinal))
    (input : SameOpeningInput (s.initialState .opening (trapdoor, positions)) state) :
    let index := (positions.sort (· ≤ ·))[ordinal]'(by simpa using bounded)
    readBuffer (noncePrefix state 10) (recordBase ordinal) 16 =
      trapdoor.extractLsb' (8 * (80 * LENGTH + 16 * index.val)) 128 := by
  let index := (positions.sort (· ≤ ·))[ordinal]'(by simpa using bounded)
  change readBuffer (noncePrefix state 10) (recordBase ordinal) 16 =
    trapdoor.extractLsb' (8 * (80 * LENGTH + 16 * index.val)) 128
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  have addressLower : trapdoorBase ≤ indicesBase + 8 * ordinal := by
    unfold indicesBase
    omega
  have addressUpper : indicesBase + 8 * ordinal < proofBase := by
    unfold proofBase
    omega
  have value : state.getMem (state.getReg .x8) = BitVec.ofNat 64 index.val := by
    rw [indexPointer, input _ addressLower addressUpper]
    exact input_index s layout trapdoor positions ordinal bounded
  have ⟨sourceAligned, destAligned, ordered, finish⟩ :=
    ordinal_nonce_geometry index ordinal (by omega)
  rw [nonce_copies state _ _ (nonce_address state index.val noncePointer value)
    outputPointer sourceAligned destAligned ordered finish]
  have stable : readBuffer state (nonceBase + 16 * index.val) 16 =
      readBuffer (s.initialState .opening (trapdoor, positions)) (nonceBase + 16 * index.val) 16 := by
    apply copied_buffer _ _ _ _ 2 sourceAligned sourceAligned (by decide)
    intro j hj
    apply input
    · unfold nonceBase
      omega
    · have indexBound := index.isLt
      rw [← nonces_end_at_indices] at addressUpper
      have before := indices_before_records
      rw [← nonces_end_at_indices] at before
      omega
  rw [stable, input_nonce s layout trapdoor positions index]

end TwoPermutationPrototype.Opening
