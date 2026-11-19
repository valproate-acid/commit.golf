import CommitGolfCandidate.TwoPermutationPackedOpeningCapAdvance
import CommitGolfCandidate.TwoPermutationOpeningCapFlow

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.Sampling
  RiscvZkvm.Rv64 OracleComp

open Opening (CapSpan CapContext markBase aligned_access markWord cap_span_height cap_span_node)

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem

@[local simp] private theorem flow_pc_set (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

@[local simp] private theorem flow_reg_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

private theorem mem_setReg (state : MachineState) (reg : Reg) (value : Word) :
    (state.setReg reg value).mem = state.mem := by cases reg <;> rfl

private theorem mem_setPC (state : MachineState) (pc : Word) :
    (state.setPC pc).mem = state.mem := rfl

attribute [local simp] mem_setReg mem_setPC

private theorem visit_memory (state : MachineState) :
    (cursorVisitPrefix state 4).mem = state.mem := by
  by_cases zero : state.getMem (cursorMarkAddress state) = 0#64 <;>
    simp [cursorMarkAddress] at zero <;>
    simp [cursorVisitPrefix, capWalkInstructions, execInstrBr, signExtend12, zero]

private theorem visit_register (state : MachineState) (r : Reg) (a : r ≠ .x7) (b : r ≠ .x28) :
    (cursorVisitPrefix state 4).getReg r = state.getReg r := by
  by_cases zero : state.getMem (cursorMarkAddress state) = 0#64 <;>
    simp [cursorMarkAddress] at zero <;>
    simp [cursorVisitPrefix, capWalkInstructions, execInstrBr, signExtend12, zero,
      Ne.symm a, Ne.symm b]

theorem cap_mark_address (state : MachineState) (node : Nat)
    (base : state.getReg .x26 = BitVec.ofNat 64 markBase)
    (cursor : state.getReg .x6 = BitVec.ofNat 64 node) :
    cursorMarkAddress state = BitVec.ofNat 64 (markBase + 8 * node) := by
  rw [cursorMarkAddress, base, cursor, BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 markBase + BitVec.ofNat 64 node * BitVec.ofNat 64 8 = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm node]

private theorem mark_word_zero (groups : List Nat) (node height : Nat)
    (span : CapSpan node height) :
    markWord groups node = 0#64 ↔ capIsMarked groups node height = false := by
  rw [markWord, cap_span_height node height span]
  cases capIsMarked groups node height <;> decide

/-- The four-cycle lookup dispatches to exactly the branch in the pure frontier. -/
theorem cap_lookup (state : MachineState) (groups : List Nat) (node height fuel : Nat)
    (allowCoins : Bool) (span : CapSpan node height) (context : CapContext groups state)
    (pc : state.pc = 0x199c) (nodeWord : state.getReg .x6 = BitVec.ofNat 64 node) :
    execute openingImage (4 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (cursorVisitPrefix state 4) allowCoins
          return result.charge 4 0) ∧
    (cursorVisitPrefix state 4).pc = (if capIsMarked groups node height then 0x19ac else 0x19b8) ∧
    (cursorVisitPrefix state 4).getReg .x6 = state.getReg .x6 ∧
    (cursorVisitPrefix state 4).getReg .x21 = state.getReg .x21 ∧
    (cursorVisitPrefix state 4).mem = state.mem ∧
    CapContext groups (cursorVisitPrefix state 4) := by
  have ⟨positive, bounded⟩ := cap_span_node node height span
  have markAddr := cap_mark_address state node context.markBaseWord nodeWord
  have safe : accessValid (cursorMarkAddress state) 8 = true := by
    rw [markAddr]
    apply aligned_access
    · unfold markBase; omega
    · unfold markBase MEMORY_BYTES; omega
  have raw : state.getMem (cursorMarkAddress state) = markWord groups node := by
    rw [markAddr]
    exact context.markValue node positive bounded
  refine ⟨execute_cursor_visit state pc fuel allowCoins safe, ?_,
    visit_register state .x6 (by decide) (by decide),
    visit_register state .x21 (by decide) (by decide), visit_memory state, ?_⟩
  · rw [cursor_visit_pc state pc, raw]
    cases mark : capIsMarked groups node height
    · have empty := (mark_word_zero groups node height span).mpr mark
      simp [empty]
    · have occupied : markWord groups node ≠ 0#64 := by
        intro empty
        have impossible := (mark_word_zero groups node height span).mp empty
        rw [mark] at impossible
        cases impossible
      simp [occupied]
  · apply context.of_preserved
    · intro r member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> exact visit_register state _ (by decide) (by decide)
    · intro target _ _
      exact congrFun (visit_memory state) (BitVec.ofNat 64 (markBase + 8 * target))

end TwoPermutationPrototype.PackedOpening
