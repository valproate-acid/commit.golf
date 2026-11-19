import CommitGolfCandidate.QOpeningCopy

namespace TwoPermutationPrototype.QOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64

theorem four_word_store_bytes (state : MachineState) (source dest : Nat)
    (srcAligned : source % 8 = 0) (dstAligned : dest % 8 = 0)
    (inside : dest + 32 ≤ MEMORY_BYTES) :
    readBuffer (fourWordStore state (BitVec.ofNat 64 source) (BitVec.ofNat 64 dest)) dest 32 =
      readBuffer state source 32 := by
  have distinct {i j : Fin 4} (different : i ≠ j) : BitVec.ofNat 64 dest + BitVec.ofNat 64 (8 * i.val) ≠
      BitVec.ofNat 64 dest + BitVec.ofNat 64 (8 * j.val) := by
    rw [word_at, word_at]
    have hi := i.isLt
    have hj := j.isLt
    unfold MEMORY_BYTES at inside
    intro same
    have := nat_address_injective (by omega) (by omega) same
    apply different
    exact Fin.ext (by omega)
  apply copied_buffer _ _ _ _ 4 srcAligned dstAligned (by decide)
  intro i hi
  rw [← word_at dest i, ← word_at source i]
  interval_cases i
  · have h1 : BitVec.ofNat 64 dest ≠ BitVec.ofNat 64 dest + 8#64 := by
      simpa using distinct (i := 0) (j := 1) (by decide)
    have h2 : BitVec.ofNat 64 dest ≠ BitVec.ofNat 64 dest + 16#64 := by
      simpa using distinct (i := 0) (j := 2) (by decide)
    have h3 : BitVec.ofNat 64 dest ≠ BitVec.ofNat 64 dest + 24#64 := by
      simpa using distinct (i := 0) (j := 3) (by decide)
    simp [fourWordStore, h1, h2, h3]
  · have h2 : BitVec.ofNat 64 dest + 8#64 ≠ BitVec.ofNat 64 dest + 16#64 :=
      distinct (i := 1) (j := 2) (by decide)
    have h3 : BitVec.ofNat 64 dest + 8#64 ≠ BitVec.ofNat 64 dest + 24#64 :=
      distinct (i := 1) (j := 3) (by decide)
    simp [fourWordStore, h2, h3]
  · have h3 : BitVec.ofNat 64 dest + 16#64 ≠ BitVec.ofNat 64 dest + 24#64 :=
      distinct (i := 2) (j := 3) (by decide)
    simp [fourWordStore, h3]
  · simp [fourWordStore]

end TwoPermutationPrototype.QOpening
