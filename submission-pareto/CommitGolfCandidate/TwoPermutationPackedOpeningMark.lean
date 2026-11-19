import CommitGolfCandidate.TwoPermutationPackedOpeningImage
import CommitGolfCandidate.TwoPermutationOpeningMarkSweep
import CommitGolfCandidate.TwoPermutationOpeningFootprint

namespace TwoPermutationPrototype.PackedOpening
set_option maxRecDepth 4096
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

open Opening (capMarkInstructions markParentPrefix childrenAddress parentAddress markBase mark_addresses)

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem

@[local simp] private theorem pc_setPC (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

@[local simp] private theorem zero_reg (state : MachineState) : state.getReg .x0 = 0#64 := rfl

private theorem mark_decode (i : Fin 10) :
    (openingImage.code[604 + i.val]?).bind Opening.decodeBase =
      some ((capMarkInstructions.drop 1)[i.val]?.getD .EBREAK) := by
  fin_cases i <;> rfl

private theorem mark_prefix_succ (state : MachineState) (i : Nat) (bounded : i < 10) :
    markParentPrefix state (i+1) =
      execInstrBr (markParentPrefix state i) ((capMarkInstructions.drop 1)[i]?.getD .EBREAK) := by
  have inside : i < (capMarkInstructions.drop 1).length := bounded
  rw [markParentPrefix, markParentPrefix, List.take_succ_eq_append_getElem inside,
    List.foldl_append, List.getElem?_eq_getElem inside]
  rfl

private theorem mark_ordinary (state : MachineState) (i : Fin 10)
    (valid : memoryArgumentsValid state ((capMarkInstructions.drop 1)[i.val]?.getD .EBREAK) = true) :
    ordinaryStep state (.base ((capMarkInstructions.drop 1)[i.val]?.getD .EBREAK)) =
      some (execInstrBr state ((capMarkInstructions.drop 1)[i.val]?.getD .EBREAK)) := by
  fin_cases i <;> simp [capMarkInstructions] at valid ⊢ <;> exact ite_eq_left valid

/-- One iteration of the actual descending cap-parent loop takes ten cycles. -/
theorem execute_mark_parent (state : MachineState) (pc : state.pc = 0x1970) (fuel : Nat)
    (allowCoins : Bool) (left : accessValid (childrenAddress state) 8 = true)
    (right : accessValid (childrenAddress state + 8#64) 8 = true)
    (parent : accessValid (parentAddress state) 8 = true) :
    execute openingImage (10 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (markParentPrefix state 10) allowCoins
          return result.charge 10 0) := by
  apply execute_unit_steps (states := markParentPrefix state)
  intro i bounded
  refine ⟨.base ((capMarkInstructions.drop 1)[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply packed_fetch_base _ (604 + i) _ (by omega) _ (mark_decode ⟨i, bounded⟩)
    interval_cases i <;> simp [markParentPrefix, capMarkInstructions, execInstrBr, pc]
  · rw [mark_prefix_succ state i bounded]
    apply mark_ordinary _ ⟨i, bounded⟩
    simp only [childrenAddress] at left right
    simp only [parentAddress] at parent
    interval_cases i <;>
      simp [memoryArgumentsValid, memAccess, markParentPrefix, capMarkInstructions,
        execInstrBr, signExtend12, left, right, parent]
  · interval_cases i <;> rfl

@[local simp] private theorem mark_mem_setReg (s : MachineState) (r : Reg) (w : Word) :
    (s.setReg r w).mem = s.mem := by cases r <;> rfl

@[local simp] private theorem mark_mem_setPC (s : MachineState) (w : Word) :
    (s.setPC w).mem = s.mem := rfl

@[local simp] private theorem mark_mem_setMem (s : MachineState) (address value : Word) :
    (s.setMem address value).mem =
      fun atAddress => if atAddress = address then value else s.mem atAddress := by
  funext atAddress
  simp [MachineState.setMem]

/-- The parent instruction reads both children, ORs their marks, and changes only
the parent word. Its latch visits the next parent or starts the cap walk. -/
theorem mark_parent_post (state : MachineState) (pc : state.pc = 0x1970) :
    let after := markParentPrefix state 10
    let left := state.getMem (childrenAddress state)
    let right := state.getMem (childrenAddress state + 8#64)
    after.mem = (state.setMem (parentAddress state) (left ||| right)).mem ∧
    after.getReg .x26 = state.getReg .x26 ∧
    after.getReg .x6 = state.getReg .x6 - 1 ∧
    after.pc = if state.getReg .x6 - 1 = 0#64 then 0x1998 else 0x1970 := by
  by_cases done : state.getReg .x6 + 18446744073709551615#64 = 0#64 <;>
    simp [markParentPrefix, capMarkInstructions, execInstrBr, parentAddress, childrenAddress,
      signExtend12, signExtend13, BitVec.sub_eq_add_neg, pc, done]

attribute [local irreducible] execute markParentPrefix
set_option maxRecDepth 4096

theorem mark_sweep_pc (state : MachineState) (remaining : Nat) (within : remaining < 256)
    (pc : state.pc = 0x1970)
    (count : state.getReg .x6 = BitVec.ofNat 64 (remaining + 1)) :
    (markParentPrefix state 10).pc = (if remaining = 0 then 0x1998 else 0x1970) ∧
      (markParentPrefix state 10).getReg .x6 = BitVec.ofNat 64 remaining := by
  have decrease : state.getReg .x6 - 1 = BitVec.ofNat 64 remaining := by
    rw [count]
    change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by decide) (by omega)]
    rw [Nat.add_sub_cancel]
  have zero : BitVec.ofNat 64 remaining = 0#64 ↔ remaining = 0 := by
    constructor
    · intro h
      exact Opening.nat_address_injective (left := remaining) (right := 0) (by omega) (by decide) h
    · rintro rfl
      rfl
  exact ⟨by rw [(mark_parent_post state pc).2.2.2, decrease]; simp [zero],
    (mark_parent_post state pc).2.2.1.trans decrease⟩

private theorem mark_cell_access (node : Nat) (bounded : node < 512) :
    accessValid (BitVec.ofNat 64 (markBase + 8 * node)) 8 = true := by
  apply Opening.aligned_access
  · unfold markBase
    omega
  · unfold markBase MEMORY_BYTES
    omega

/-- Execute the actual entire descending sweep, accounting for every iteration. -/
theorem execute_mark_sweep (state : MachineState) (remaining fuel : Nat) (allowCoins : Bool)
    (bounded : remaining < 256)
    (pc : state.pc = if remaining = 0 then 0x1998 else 0x1970)
    (base : state.getReg .x26 = BitVec.ofNat 64 markBase)
    (count : state.getReg .x6 = BitVec.ofNat 64 remaining) :
    execute openingImage (10 * remaining + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (Opening.markMachine state remaining) allowCoins
          return result.charge (10 * remaining) 0) := by
  induction remaining generalizing state with
  | zero => simp [Opening.markMachine, Execution.charge]
  | succ remaining ih =>
    have headPC : state.pc = 0x1970 := by simpa using pc
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
    simp [Opening.markMachine, Execution.charge, Nat.add_assoc, Nat.mul_succ, Nat.add_comm 10]

end TwoPermutationPrototype.PackedOpening
