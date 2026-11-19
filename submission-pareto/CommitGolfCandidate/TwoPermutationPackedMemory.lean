import CommitGolfCandidate.ProjectedHalfwordMemory

namespace TwoPermutationPrototype.Packed
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 ProjectedHalfword
private theorem ofNat_ne {left right : Nat} (leftBound : left < 2^64) (rightBound : right < 2^64)
    (different : left ≠ right) : (BitVec.ofNat 64 left : Word) ≠ BitVec.ofNat 64 right := by
  intro equal
  apply different
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt leftBound, Nat.mod_eq_of_lt rightBound]
    using congrArg BitVec.toNat equal

private theorem alignedNat (address : Nat) (bound : address < 2^64) (even : address % 2 = 0) :
    (BitVec.ofNat 64 address).toNat % 2 = 0 := by
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] using even

private theorem advance_forward (address : Nat) :
    advance false (BitVec.ofNat 64 address) = BitVec.ofNat 64 (address+2) := by
  rw [BitVec.ofNat_add]
  rfl

private theorem word_succ (base : Nat) :
    BitVec.ofNat 64 (base+1) = BitVec.ofNat 64 base+1 := by
  rw [BitVec.ofNat_add]
  rfl

private theorem storeFrame (state : MachineState) (target : Nat) (query : Word) (value : BitVec 16)
    (bound : target < 2^64) (even : target % 2 = 0)
    (outside : query ≠ BitVec.ofNat 64 target ∧ query ≠ BitVec.ofNat 64 (target+1)) :
    (state.setHalfword (BitVec.ofNat 64 target) value).getByte query = state.getByte query := by
  apply store_outside state _ _ _ (alignedNat target bound even)
  rw [← word_succ]
  exact outside

private theorem storeCopy (state : MachineState) (source target : Nat)
    (sourceBound : source < 2^64) (targetBound : target < 2^64)
    (sourceEven : source % 2 = 0) (targetEven : target % 2 = 0)
    (index : Nat) (inside : index < 2) :
    let next := state.setHalfword (BitVec.ofNat 64 target) (state.getHalfword (BitVec.ofNat 64 source))
    next.getByte (BitVec.ofNat 64 (target+index)) =
      state.getByte (BitVec.ofNat 64 (source+index)) := by
  obtain ⟨lower, upper⟩ := copy_bytes state (BitVec.ofNat 64 source) (BitVec.ofNat 64 target)
    (alignedNat source sourceBound sourceEven) (alignedNat target targetBound targetEven)
  interval_cases index
  · simpa only [Nat.add_zero] using lower
  · rw [word_succ, word_succ]
    exact upper

theorem forward_disjoint_memory (count : Nat) (state : MachineState) (source target : Nat)
    (ordered : source+2*count ≤ target) (sourceBound : source+2*count ≤ 2^64)
    (targetBound : target+2*count ≤ 2^64)
    (sourceEven : source % 2 = 0) (targetEven : target % 2 = 0) :
    let final := copyLoopMemory false count state (BitVec.ofNat 64 source) (BitVec.ofNat 64 target)
    (∀ i < 2*count, final.getByte (BitVec.ofNat 64 (target+i)) =
      state.getByte (BitVec.ofNat 64 (source+i))) ∧
    (∀ query, (∀ i < 2*count, query ≠ BitVec.ofNat 64 (target+i)) →
      final.getByte query = state.getByte query) := by
  induction count generalizing state source target with
  | zero =>
    exact ⟨fun i inside => (by omega : False).elim, fun _ _ => rfl⟩
  | succ count ih =>
    let next := state.setHalfword (BitVec.ofNat 64 target) (state.getHalfword (BitVec.ofNat 64 source))
    simp only [copyLoopMemory, advance_forward]
    obtain ⟨copied, frame⟩ :=
      ih next (source+2) (target+2) (by omega) (by omega) (by omega) (by omega) (by omega)
    constructor
    · intro index inside
      by_cases before : index < 2
      · have outside : ∀ j < 2*count, (BitVec.ofNat 64 (target+index) : Word) ≠
            BitVec.ofNat 64 (target+2+j) := by
          intro j hj
          exact ofNat_ne (by omega) (by omega) (by omega)
        rw [frame _ outside]
        exact storeCopy state source target (by omega) (by omega) sourceEven targetEven index before
      · have nextIndex : index = 2 + (index-2) := by omega
        have matching := copied (index-2) (by omega)
        rw [Nat.add_assoc, Nat.add_assoc, ← nextIndex] at matching
        rw [matching]
        exact storeFrame state target _ _ (by omega) targetEven
          ⟨ofNat_ne (by omega) (by omega) (by omega), ofNat_ne (by omega) (by omega) (by omega)⟩
    · intro query outside
      rw [frame _ (fun i hi => by
        rw [Nat.add_assoc]
        exact outside (2+i) (by omega))]
      exact storeFrame state target _ _ (by omega) targetEven
        ⟨by simpa only [Nat.add_zero] using outside 0 (by omega), outside 1 (by omega)⟩

end TwoPermutationPrototype.Packed
