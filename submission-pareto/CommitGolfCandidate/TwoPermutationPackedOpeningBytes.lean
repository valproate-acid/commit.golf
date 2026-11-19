import CommitGolfCandidate.TwoPermutationTranscript
import CommitGolfCandidate.InputMemory

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.Sampling

/-- The byte-level interface to a copied field in the machine proof. -/
structure ByteCopy (before after : MachineState) (source target size : Nat) : Prop where
  copied : ∀ i < size,
    after.getByte (BitVec.ofNat 64 (target+i)) = before.getByte (BitVec.ofNat 64 (source+i))
  frame : ∀ address : Word, (∀ i < size, address ≠ BitVec.ofNat 64 (target+i)) →
    after.getByte address = before.getByte address

theorem ByteCopy.read {before after : MachineState} {source target size : Nat}
    (copied : ByteCopy before after source target size) :
    readBuffer after target size = readBuffer before source size := by
  unfold readBuffer
  apply congrArg (BitVec.ofNat (8*size))
  apply Finset.sum_congr rfl
  intro i hi
  rw [copied.copied i (Finset.mem_range.mp hi)]

theorem ByteCopy.read_outside {before after : MachineState} {source target size : Nat}
    (copied : ByteCopy before after source target size) (readStart count : Nat)
    (targetBound : target+size ≤ 2^64) (readBound : readStart+count ≤ 2^64)
    (outside : readStart+count ≤ target ∨ target+size ≤ readStart) :
    readBuffer after readStart count = readBuffer before readStart count := by
  unfold readBuffer
  apply congrArg (BitVec.ofNat (8*count))
  apply Finset.sum_congr rfl
  intro i hi
  have inside := Finset.mem_range.mp hi
  have separate (j : Nat) (bound : j < size) : BitVec.ofNat 64 (readStart+i) ≠ BitVec.ofNat 64 (target+j) := by
    intro same
    have numeric := congrArg BitVec.toNat same
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : readStart+i < 2^64),
      Nat.mod_eq_of_lt (by omega : target+j < 2^64)] at numeric
    omega
  rw [copied.frame _ separate]

theorem ByteCopy.read_low_digest {before after : MachineState} {source target : Nat}
    (copied : ByteCopy before after source target 30) :
    readBuffer after target 30 = (readBuffer before source 32).extractLsb' 0 240 := by
  rw [copied.read]
  simpa only [Nat.mul_zero, Nat.add_zero] using (read_buffer_slice before source 32 0 30 (by decide)).symm

theorem ByteCopy.read_full_digest {before after : MachineState} {source target : Nat}
    (copied : ByteCopy before after source target 32) :
    readBuffer after target 32 = readBuffer before source 32 := copied.read

theorem ByteCopy.digest_byte {before after : MachineState} {source target : Nat} (packed : Bool)
    (copied : ByteCopy before after source target (if packed then 30 else 32)) (i : Nat)
    (inside : i < (proofDigestBytes packed (readBuffer before source 32)).length) :
    after.getByte (BitVec.ofNat 64 (target+i)) =
      (proofDigestBytes packed (readBuffer before source 32))[i] := by
  have valid : i < (if packed then 30 else 32) := by
    rw [proof_digest_length] at inside
    exact inside
  have limit : i < 32 := by cases packed <;> simp_all <;> omega
  rw [copied.copied i valid, ← read_buffer_byte before source 32 i limit]
  cases packed with
  | false =>
    simp only [proofDigestBytes, Bool.false_eq_true, ite_false, digestBytes, List.getElem_ofFn]
  | true =>
    simp only [proofDigestBytes, ite_true, List.getElem_take, digestBytes, List.getElem_ofFn]

theorem ByteCopy.salt_byte {before after : MachineState} {source target : Nat}
    (copied : ByteCopy before after source target 16) (i : Nat) (inside : i < 16) :
    after.getByte (BitVec.ofNat 64 (target+i)) =
      (saltBytes (readBuffer before source 16))[i]'(by simpa [saltBytes] using inside) := by
  rw [copied.copied i inside, ← read_buffer_byte before source 16 i inside]
  simp only [saltBytes, List.getElem_ofFn]

end TwoPermutationPrototype.PackedOpening
