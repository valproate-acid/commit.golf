import CommitGolfCandidate.CapMarkInvariant

/-! Bounded natural addresses and latch arithmetic for occupancy marking.
These facts connect the real shifted-register addresses to the natural heap
indices without weakening the machine's access checks. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem cap_mark_child_pointer (node : Nat) :
    (28672 : Word) + (BitVec.ofNat 64 node <<< 4) = capMarkAddress (2 * node) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 28672 + BitVec.ofNat 64 node * BitVec.ofNat 64 16 = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  unfold capMarkAddress
  congr 1
  omega

theorem cap_mark_right_pointer (node : Nat) :
    capMarkAddress (2 * node) + 8 = capMarkAddress (2 * node + 1) := by
  change BitVec.ofNat 64 (28672 + 8 * (2 * node)) + BitVec.ofNat 64 8 = _
  rw [← BitVec.ofNat_add]
  unfold capMarkAddress
  congr 1

theorem cap_mark_parent_pointer (node : Nat) :
    (28672 : Word) + (BitVec.ofNat 64 node <<< 3) = capMarkAddress node := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 28672 + BitVec.ofNat 64 node * BitVec.ofNat 64 8 = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  unfold capMarkAddress
  congr 1
  omega

theorem cap_mark_decrement (node : Nat) (positive : 0 < node) :
    BitVec.ofNat 64 node + signExtend12 (4095 : BitVec 12) =
      BitVec.ofNat 64 (node - 1) := by
  rw [show signExtend12 (4095 : BitVec 12) = -(1 : Word) by decide]
  have equation : node = node - 1 + 1 := by omega
  conv_lhs => rw [equation]
  rw [BitVec.ofNat_add, BitVec.add_assoc]
  simp

theorem cap_mark_last_iff (node : Nat) (positive : 0 < node) (bounded : node < 256) :
    BitVec.ofNat 64 (node - 1) = 0 ↔ node = 1 := by
  constructor
  · intro equal
    have numeric := congrArg BitVec.toNat equal
    change (node - 1) % 2^64 = 0 at numeric
    rw [Nat.mod_eq_of_lt (by omega : node - 1 < 2^64)] at numeric
    omega
  · intro equal
    subst node
    rfl

theorem cap_mark_back_pc (start : Word) :
    start + 36 + signExtend13 (8156 : BitVec 13) = start := by
  rw [show signExtend13 (8156 : BitVec 13) = -(36 : Word) by decide]
  simp [BitVec.add_assoc]

end CommitGolfCandidate
