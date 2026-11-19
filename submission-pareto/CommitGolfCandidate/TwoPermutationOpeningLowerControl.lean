import CommitGolfCandidate.TwoPermutationOpeningSiblingStep
import CommitGolfCandidate.TwoPermutationOpeningFootprint

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] getReg_setReg getReg_setMem

@[local simp] private theorem lower_pc_set (s : MachineState) (pc : Word) :
    (s.setPC pc).pc = pc := rfl

@[local simp] private theorem lower_zero (s : MachineState) : s.getReg .x0 = 0#64 := rfl

theorem sibling_control (state : MachineState) (pc : state.pc = 0x105c) :
    let after := siblingPrefix state 15
    after.getReg .x9 = state.getReg .x9 ∧
    after.getReg .x21 = state.getReg .x21 + 32#64 ∧
    after.getReg .x6 = state.getReg .x6 >>> 1 ∧
    after.getReg .x29 = state.getReg .x29 - 1 ∧
    after.pc = (if state.getReg .x29 - 1 = 0#64 then 0x1098 else 0x105c) := by
  by_cases done : state.getReg .x29 + 18446744073709551615#64 = 0#64 <;>
    simp [siblingPrefix, siblingInstructions, execInstrBr, signExtend12, signExtend13,
      BitVec.sub_eq_add_neg, pc, done]

theorem sibling_address (state : MachineState) (node : Nat)
    (base : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase)
    (value : state.getReg .x6 = BitVec.ofNat 64 node) :
    siblingSource state = BitVec.ofNat 64 (trapdoorBase + 32 * (node ^^^ 1)) := by
  rw [siblingSource, base, value]
  rw [← BitVec.ofNat_xor, BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 trapdoorBase + BitVec.ofNat 64 (node ^^^ 1) * BitVec.ofNat 64 32 = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm (node ^^^ 1)]

/-- State of the lower loop after completing the indicated number of levels. -/
structure LowerControl (state : MachineState) (index : Index) (ordinal level : Nat) : Prop where
  pc : state.pc = if level = 16 then 0x1098 else 0x105c
  heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase
  destination : state.getReg .x21 = BitVec.ofNat 64 (siblingDest ordinal level)
  node : state.getReg .x6 = BitVec.ofNat 64 (lowerNode index level)
  remaining : state.getReg .x29 = BitVec.ofNat 64 (16 - level)

attribute [local irreducible] siblingPrefix execute

theorem lower_control_next (state : MachineState) (index : Index) (ordinal level : Nat)
    (inside : level < 16) (control : LowerControl state index ordinal level) :
    LowerControl (siblingPrefix state 15) index ordinal (level + 1) := by
  have pc : state.pc = 0x105c := by simpa [show level ≠ 16 by omega] using control.pc
  have post := sibling_control state pc
  have counter : state.getReg .x29 - 1 = BitVec.ofNat 64 (16 - (level + 1)) := by
    rw [control.remaining]
    change BitVec.ofNat 64 (16 - level) - BitVec.ofNat 64 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by decide) (by omega)]
    congr 1
  have empty : BitVec.ofNat 64 (16 - (level + 1)) = 0#64 ↔ level + 1 = 16 := by
    constructor
    · intro h
      have eq := nat_address_injective (left := 16 - (level + 1)) (right := 0)
        (by omega) (by decide) h
      omega
    · intro h
      rw [h, Nat.sub_self]
  refine ⟨?_, post.1.trans control.heap, ?_, ?_, post.2.2.2.1.trans counter⟩
  · rw [post.2.2.2.2, counter]
    simp only [empty]
  · rw [post.2.1, control.destination]
    change BitVec.ofNat 64 (siblingDest ordinal level) + BitVec.ofNat 64 32 = _
    rw [← BitVec.ofNat_add]
    unfold siblingDest
    congr 1
  · rw [post.2.2.1, control.node, lower_node_next]
    apply BitVec.eq_of_toNat_eq
    have left : lowerNode index level < 2 ^ 64 :=
      (lower_node_bound _ _).trans (by decide)
    have right : lowerNode index level / 2 < 2 ^ 64 := (Nat.div_le_self _ _).trans_lt left
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt left, Nat.mod_eq_of_lt right]

/-- Every real sibling step on an admitted record has valid heap and output addresses. -/
theorem execute_lower_level (state : MachineState) (index : Index)
    (ordinal level fuel : Nat) (allowCoins : Bool) (ordinalBound : ordinal < LENGTH)
    (inside : level < 16) (control : LowerControl state index ordinal level) :
    execute openingImage (15 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (siblingPrefix state 15) allowCoins
          return result.charge 15 0) := by
  have pc : state.pc = 0x105c := by simpa [show level ≠ 16 by omega] using control.pc
  have src := sibling_address state (lowerNode index level) control.heap control.node
  have ⟨srcAligned, dstAligned, separated, fits⟩ :=
    ordinal_sibling_geometry index ordinal level ordinalBound inside
  apply execute_sibling _ pc
  · intro j
    rw [src, word_at]
    have small := j.isLt
    apply aligned_access _ (by omega) (by omega)
  · intro j
    rw [control.destination, word_at]
    have small := j.isLt
    apply aligned_access _ (by omega) (by omega)

def lowerPathMachine (state : MachineState) : Nat → MachineState
  | 0 => state
  | remaining + 1 => lowerPathMachine (siblingPrefix state 15) remaining

theorem lower_path_control (state : MachineState) (index : Index) (ordinal level remaining : Nat)
    (final : level + remaining = 16) (control : LowerControl state index ordinal level) :
    LowerControl (lowerPathMachine state remaining) index ordinal 16 := by
  induction remaining generalizing state level with
  | zero =>
    have done : level = 16 := by omega
    subst level
    exact control
  | succ remaining ih =>
    apply ih _ (level + 1) (by omega)
    exact lower_control_next state index ordinal level (by omega) control

/-- Starting at the first sibling, the concrete loop executes 240 instructions. -/
theorem execute_lower_path (state : MachineState) (index : Index)
    (ordinal level remaining fuel : Nat) (allowCoins : Bool)
    (ordinalBound : ordinal < LENGTH) (final : level + remaining = 16)
    (control : LowerControl state index ordinal level) :
    execute openingImage (15 * remaining + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (lowerPathMachine state remaining) allowCoins
          return result.charge (15 * remaining) 0) := by
  induction remaining generalizing state level with
  | zero => simp [lowerPathMachine, Execution.charge]
  | succ remaining ih =>
    have one := execute_lower_level state index ordinal level (15 * remaining + fuel)
      allowCoins ordinalBound (by omega) control
    have next := lower_control_next state index ordinal level (by omega) control
    rw [show 15 * (remaining + 1) + fuel = 15 + (15 * remaining + fuel) by omega,
      one, ih _ (level + 1) (by omega) next]
    simp [lowerPathMachine, Execution.charge, Nat.add_assoc, Nat.mul_succ, Nat.add_comm 15]

end TwoPermutationPrototype.Opening
