import CommitGolfCandidate.ProjectedHalfword

namespace CommitGolfCandidate.ProjectedHalfword
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

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

private theorem advance_backward (address : Nat) (positive : 2 ≤ address) :
    advance true (BitVec.ofNat 64 address) = BitVec.ofNat 64 (address-2) := by
  rw [show address = address-2+2 by omega, BitVec.ofNat_add]
  simp only [Nat.add_sub_cancel]
  change BitVec.ofNat 64 (address - 2) + (2:Word) + -2 = _
  simp [BitVec.add_assoc]

theorem cursor_forward (count base : Nat) :
    cursorAt false count (BitVec.ofNat 64 base) = BitVec.ofNat 64 (base+2*count) := by
  induction count generalizing base with
  | zero => simp [cursorAt]
  | succ count ih =>
    rw [cursorAt.eq_2, advance_forward, ih]
    congr 1
    omega

theorem cursor_backward (count base : Nat) (room : 2*count ≤ base) :
    cursorAt true count (BitVec.ofNat 64 base) = BitVec.ofNat 64 (base-2*count) := by
  induction count generalizing base with
  | zero => simp [cursorAt]
  | succ count ih =>
    rw [cursorAt.eq_2, advance_backward _ (by omega), ih (base-2) (by omega)]
    congr 1
    omega

private theorem validHalfword (address : Nat) (window : address+2 ≤ MEMORY_BYTES)
    (even : address % 2 = 0) : accessValid (BitVec.ofNat 64 address) 2 = true := by
  have small : address < 2^64 := by norm_num [MEMORY_BYTES] at window; omega
  simp only [accessValid, rangeValid, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨window, even⟩

theorem forward_ready (entry : Word) (state : MachineState) (source target count : Nat)
    (positive : 0<count) (countBound : count<2^64)
    (pc : state.pc=entry) (counter : state.getReg .x28=BitVec.ofNat 64 count)
    (sourceReg : state.getReg .x23=BitVec.ofNat 64 source)
    (targetReg : state.getReg .x25=BitVec.ofNat 64 target)
    (sourceBound : source+2*count ≤ MEMORY_BYTES) (targetBound : target+2*count ≤ MEMORY_BYTES)
    (sourceEven : source%2=0) (targetEven : target%2=0) :
    CopyReady false entry count state := by
  refine ⟨countBound, counter, fun _ => pc, fun empty => (by omega : False).elim, ?_, ?_⟩
  · intro i inside
    rw [sourceReg, cursor_forward]
    exact validHalfword _ (by omega) (by omega)
  · intro i inside
    rw [targetReg, cursor_forward]
    exact validHalfword _ (by omega) (by omega)

theorem reverse_ready (entry : Word) (state : MachineState) (source target count : Nat)
    (positive : 0<count) (countBound : count<2^64)
    (pc : state.pc=entry) (counter : state.getReg .x28=BitVec.ofNat 64 count)
    (sourceReg : state.getReg .x23=BitVec.ofNat 64 (source+2*(count-1)))
    (targetReg : state.getReg .x25=BitVec.ofNat 64 (target+2*(count-1)))
    (sourceBound : source+2*count ≤ MEMORY_BYTES) (targetBound : target+2*count ≤ MEMORY_BYTES)
    (sourceEven : source%2=0) (targetEven : target%2=0) :
    CopyReady true entry count state := by
  refine ⟨countBound, counter, fun _ => pc, fun empty => (by omega : False).elim, ?_, ?_⟩
  · intro i inside
    rw [sourceReg, cursor_backward _ _ (by omega)]
    exact validHalfword _ (by omega) (by omega)
  · intro i inside
    rw [targetReg, cursor_backward _ _ (by omega)]
    exact validHalfword _ (by omega) (by omega)

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

/-- A low-to-high copy retains the source bytes even if the ranges overlap. -/
theorem forward_memory (count : Nat) (state : MachineState) (source target : Nat)
    (ordered : target ≤ source) (sourceBound : source+2*count ≤ 2^64)
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

def reverseMemory (count : Nat) (state : MachineState) (source target : Nat) : MachineState :=
  copyLoopMemory true count state (BitVec.ofNat 64 (source+2*(count-1)))
    (BitVec.ofNat 64 (target+2*(count-1)))

private theorem reverseMemory_step (count : Nat) (state : MachineState) (source target : Nat) :
    reverseMemory (count+1) state source target =
      reverseMemory count (state.setHalfword (BitVec.ofNat 64 (target+2*count))
        (state.getHalfword (BitVec.ofNat 64 (source+2*count)))) source target := by
  cases count with
  | zero => rfl
  | succ count =>
    unfold reverseMemory
    simp only [copyLoopMemory.eq_2, Nat.add_sub_cancel]
    rw [advance_backward _ (by omega), advance_backward _ (by omega),
      show source+2*(count+1)-2 = source+2*count by omega,
      show target+2*(count+1)-2 = target+2*count by omega]

/-- A high-to-low copy retains the source bytes even if the ranges overlap. -/
theorem backward_memory (count : Nat) (state : MachineState) (source target : Nat)
    (ordered : source ≤ target) (sourceBound : source+2*count ≤ 2^64)
    (targetBound : target+2*count ≤ 2^64)
    (sourceEven : source % 2 = 0) (targetEven : target % 2 = 0) :
    let final := reverseMemory count state source target
    (∀ i < 2*count, final.getByte (BitVec.ofNat 64 (target+i)) =
      state.getByte (BitVec.ofNat 64 (source+i))) ∧
    (∀ query, (∀ i < 2*count, query ≠ BitVec.ofNat 64 (target+i)) →
      final.getByte query = state.getByte query) := by
  induction count generalizing state with
  | zero =>
    exact ⟨fun i inside => (by omega : False).elim, fun _ _ => rfl⟩
  | succ count ih =>
    let next := state.setHalfword (BitVec.ofNat 64 (target+2*count))
      (state.getHalfword (BitVec.ofNat 64 (source+2*count)))
    simp only [reverseMemory_step]
    obtain ⟨copied, frame⟩ := ih next (by omega) (by omega)
    constructor
    · intro index inside
      by_cases earlier : index < 2*count
      · rw [copied index earlier]
        exact storeFrame state (target+2*count) _ _ (by omega) (by omega)
          ⟨ofNat_ne (by omega) (by omega) (by omega), ofNat_ne (by omega) (by omega) (by omega)⟩
      · have outside : ∀ j < 2*count, (BitVec.ofNat 64 (target+index) : Word) ≠
            BitVec.ofNat 64 (target+j) := by
          intro j hj
          exact ofNat_ne (by omega) (by omega) (by omega)
        rw [frame _ outside]
        have matching := storeCopy state (source+2*count) (target+2*count)
          (by omega) (by omega) (by omega) (by omega) (index-2*count) (by omega)
        rw [Nat.add_assoc, Nat.add_assoc, show 2*count+(index-2*count) = index by omega] at matching
        exact matching
    · intro query outside
      rw [frame _ (fun i inside => outside i (by omega))]
      exact storeFrame state (target+2*count) _ _ (by omega) (by omega)
        ⟨outside (2*count) (by omega), by
          rw [Nat.add_assoc]; exact outside (2*count+1) (by omega)⟩

end CommitGolfCandidate.ProjectedHalfword
