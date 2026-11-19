import CommitGolfCandidate.QOpeningMarkMachine
import CommitGolfCandidate.QOpeningMarks

namespace TwoPermutationPrototype.QOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local irreducible] execute markParentPrefix
set_option maxRecDepth 4096

def machineMarks (state : MachineState) (node : Nat) : Word :=
  state.getMem (BitVec.ofNat 64 (markBase + 8 * node))

def markMachine (state : MachineState) : Nat → MachineState
  | 0 => state
  | remaining + 1 => markMachine (markParentPrefix state 10) remaining

theorem mark_sweep_pc (state : MachineState) (remaining : Nat) (within : remaining < 256)
    (pc : state.pc = 0x10b4)
    (count : state.getReg .x6 = BitVec.ofNat 64 (remaining + 1)) :
    (markParentPrefix state 10).pc = (if remaining = 0 then 0x10dc else 0x10b4) ∧
      (markParentPrefix state 10).getReg .x6 = BitVec.ofNat 64 remaining := by
  have decrease : state.getReg .x6 - 1 = BitVec.ofNat 64 remaining := by
    rw [count]
    change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by decide) (by omega)]
    rw [Nat.add_sub_cancel]
  have zero : BitVec.ofNat 64 remaining = 0#64 ↔ remaining = 0 := by
    constructor
    · intro h
      exact nat_address_injective (left := remaining) (right := 0) (by omega) (by decide) h
    · rintro rfl
      rfl
  exact ⟨by rw [(mark_parent_post state pc).2.2.2, decrease]; simp [zero],
    (mark_parent_post state pc).2.2.1.trans decrease⟩

private theorem mark_cell_access (node : Nat) (bounded : node < 512) :
    accessValid (BitVec.ofNat 64 (markBase + 8 * node)) 8 = true := by
  apply aligned_access
  · unfold markBase
    omega
  · unfold markBase MEMORY_BYTES
    omega

/-- Execute the actual entire descending sweep, accounting for every iteration. -/
theorem execute_mark_sweep (state : MachineState) (remaining fuel : Nat) (allowCoins : Bool)
    (bounded : remaining < 256)
    (pc : state.pc = if remaining = 0 then 0x10dc else 0x10b4)
    (base : state.getReg .x26 = BitVec.ofNat 64 markBase)
    (count : state.getReg .x6 = BitVec.ofNat 64 remaining) :
    execute openingImage (10 * remaining + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (markMachine state remaining) allowCoins
          return result.charge (10 * remaining) 0) := by
  induction remaining generalizing state with
  | zero => simp [markMachine, Execution.charge]
  | succ remaining ih =>
    have headPC : state.pc = 0x10b4 := by simpa using pc
    have ⟨left, right, parent⟩ := mark_addresses state (remaining + 1) base count
    have leftValid : accessValid (childrenAddress state) 8 = true := by
      rw [left]
      exact mark_cell_access _ (by omega)
    have rightValid : accessValid (childrenAddress state + 8#64) 8 = true := by
      rw [right]
      exact mark_cell_access _ (by omega)
    have parentValid : accessValid (parentAddress state) 8 = true := by
      rw [parent]
      exact mark_cell_access _ (by omega)
    have head := execute_mark_parent state headPC (10 * remaining + fuel) allowCoins
      leftValid rightValid parentValid
    have ⟨nextPC, nextCount⟩ := mark_sweep_pc state remaining (by omega) headPC count
    have nextBase := (mark_parent_post state headPC).2.1.trans base
    rw [show 10 * (remaining + 1) + fuel = 10 + (10 * remaining + fuel) by omega, head,
      ih _ (by omega) nextPC nextBase nextCount]
    simp [markMachine, Execution.charge, Nat.add_assoc, Nat.mul_succ, Nat.add_comm 10]

end TwoPermutationPrototype.QOpening
