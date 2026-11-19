import CommitGolfCandidate.CapMemoryFrame

/-! Natural descending-node invariant for occupancy marks. At residual node j,
every larger tree index is already a finalized 0/1 word. Both children are
therefore available before the parent store; lower nodes remain unconstrained. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def capMarkAddress (node : Nat) : Word := BitVec.ofNat 64 (28672 + 8 * node)
def capMarkWord (marked : Bool) : Word := if marked then 1 else 0

def CapMarksReady (state : MachineState) (leaves remaining : Nat)
    (marked : Nat → Bool) : Prop :=
  ∀ node, remaining < node → node < 2 * leaves →
    state.getMem (capMarkAddress node) = capMarkWord (marked node)

def capMarkWrite (state : MachineState) (node : Nat) : MachineState :=
  state.setMem (capMarkAddress node)
    (state.getMem (capMarkAddress (2 * node)) |||
      state.getMem (capMarkAddress (2 * node + 1)))

theorem cap_mark_word_or (left right : Bool) :
    capMarkWord left ||| capMarkWord right = capMarkWord (left || right) := by
  cases left <;> cases right <;> decide

/-- Both child words are finalized when the current node is positive/internal. -/
theorem cap_marks_children (state : MachineState) (leaves node : Nat)
    (marked : Nat → Bool) (positive : 0 < node) (internal : node < leaves)
    (ready : CapMarksReady state leaves node marked) :
    state.getMem (capMarkAddress (2 * node)) = capMarkWord (marked (2 * node)) ∧
    state.getMem (capMarkAddress (2 * node + 1)) = capMarkWord (marked (2 * node + 1)) :=
  ⟨ready _ (by omega) (by omega), ready _ (by omega) (by omega)⟩

theorem cap_mark_address_injective (leaves : Nat) (bounded : leaves ≤ 256)
    (left right : Nat) (leftBound : left < 2 * leaves) (rightBound : right < 2 * leaves)
    (equal : capMarkAddress left = capMarkAddress right) : left = right := by
  have numeric := congrArg BitVec.toNat equal
  simp only [capMarkAddress, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 28672 + 8 * left < 2^64),
    Nat.mod_eq_of_lt (by omega : 28672 + 8 * right < 2^64)] at numeric
  omega

/-- The store finalizes the current parent and preserves all larger nodes. -/
theorem cap_marks_ready_next (state : MachineState) (leaves node : Nat)
    (marked : Nat → Bool) (bounded : leaves ≤ 256)
    (positive : 0 < node) (internal : node < leaves)
    (equation : marked node = (marked (2 * node) || marked (2 * node + 1)))
    (ready : CapMarksReady state leaves node marked) :
    CapMarksReady (capMarkWrite state node) leaves (node - 1) marked := by
  obtain ⟨left, right⟩ := cap_marks_children state leaves node marked positive internal ready
  intro next lower upper
  by_cases same : next = node
  · subst next
    simp only [capMarkWrite, MachineState.getMem_setMem_eq, left, right,
      cap_mark_word_or, ← equation]
  · have distinct : capMarkAddress next ≠ capMarkAddress node := by
      intro equal
      exact same (cap_mark_address_injective leaves bounded next node upper (by omega) equal)
    rw [capMarkWrite, MachineState.getMem_setMem_ne distinct]
    exact ready next (by omega) upper

/-- The natural parent address is aligned, admitted, and below every ABI input. -/
theorem cap_mark_address_valid (leaves node : Nat) (bounded : leaves ≤ 256)
    (inside : node < 2 * leaves) :
    accessValid (capMarkAddress node) 8 = true ∧
      (capMarkAddress node).toNat < 32768 := by
  have small : 28672 + 8 * node < 32768 := by omega
  have numeric : (capMarkAddress node).toNat = 28672 + 8 * node := by
    simp only [capMarkAddress, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 28672 + 8 * node < 2^64)]
  constructor
  · simp [accessValid, rangeValid, numeric, MEMORY_BYTES]
    omega
  · omega

theorem cap_mark_write_frame (state reference : MachineState) (leaves node : Nat)
    (bounded : leaves ≤ 256) (inside : node < leaves)
    (frame : CapHighBytes state reference) :
    CapHighBytes (capMarkWrite state node) reference := by
  exact cap_high_bytes_store state reference (28672 + 8 * node) _ (by omega) frame

/-- Occupancy stores preserve every collected cap-root word. -/
theorem cap_mark_write_roots (state : MachineState) (leaves node address : Nat)
    (bounded : leaves ≤ 256) (inside : node < leaves)
    (belowMarks : address < 28672) :
    (capMarkWrite state node).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  apply MachineState.getMem_setMem_ne
  intro equal
  have numeric := congrArg BitVec.toNat equal
  simp only [capMarkAddress, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : address < 2^64),
    Nat.mod_eq_of_lt (by omega : 28672 + 8 * node < 2^64)] at numeric
  omega

def capMarkPass (state : MachineState) : Nat → MachineState
  | 0 => state
  | remaining + 1 => capMarkPass (capMarkWrite state (remaining + 1)) remaining

/-- Starting with the leaves initialized, a descending pass finalizes every
positive cap index. This is a memory statement; instruction costs are separate. -/
theorem cap_mark_pass_ready (state : MachineState) (leaves remaining : Nat)
    (marked : Nat → Bool) (bounded : leaves ≤ 256) (internal : remaining < leaves)
    (equation : ∀ node, 0 < node → node < leaves →
      marked node = (marked (2 * node) || marked (2 * node + 1)))
    (ready : CapMarksReady state leaves remaining marked) :
    CapMarksReady (capMarkPass state remaining) leaves 0 marked := by
  induction remaining generalizing state with
  | zero => exact ready
  | succ remaining ih =>
    exact ih (capMarkWrite state (remaining + 1)) (by omega)
      (cap_marks_ready_next state leaves (remaining + 1) marked bounded (by omega)
        internal (equation _ (by omega) internal) ready)

theorem cap_mark_pass_frame (state reference : MachineState) (leaves remaining : Nat)
    (bounded : leaves ≤ 256) (internal : remaining < leaves)
    (frame : CapHighBytes state reference) :
    CapHighBytes (capMarkPass state remaining) reference := by
  induction remaining generalizing state with
  | zero => exact frame
  | succ remaining ih =>
    exact ih (capMarkWrite state (remaining + 1)) (by omega)
      (cap_mark_write_frame state reference leaves (remaining + 1) bounded internal frame)

theorem cap_mark_pass_roots (state : MachineState) (leaves remaining address : Nat)
    (bounded : leaves ≤ 256) (internal : remaining < leaves)
    (belowMarks : address < 28672) :
    (capMarkPass state remaining).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  induction remaining generalizing state with
  | zero => rfl
  | succ remaining ih =>
    exact (ih (capMarkWrite state (remaining + 1)) (by omega)).trans
      (cap_mark_write_roots state leaves (remaining + 1) address bounded internal belowMarks)

end CommitGolfCandidate
