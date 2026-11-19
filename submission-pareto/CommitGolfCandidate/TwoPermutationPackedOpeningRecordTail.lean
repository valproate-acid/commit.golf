import CommitGolfCandidate.TwoPermutationPackedOpeningImage
import CommitGolfCandidate.TwoPermutationOpeningRecordTail

namespace TwoPermutationPrototype.PackedOpening
set_option maxRecDepth 4096
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem

@[local simp] theorem tail_pc_setPC (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

@[local simp] theorem tail_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

@[local simp] private theorem mem_setReg (s : MachineState) (r : Reg) (w : Word) :
    (s.setReg r w).mem = s.mem := by cases r <;> rfl

@[local simp] private theorem mem_setPC (s : MachineState) (w : Word) :
    (s.setPC w).mem = s.mem := rfl

@[local simp] private theorem mem_setMem (s : MachineState) (address value : Word) :
    (s.setMem address value).mem =
      fun atAddress => if atAddress = address then value else s.mem atAddress := by
  funext atAddress
  simp [MachineState.setMem]

open Opening (recordMarkAddress)

def recordTailInstructions : List Instr :=
  Opening.recordTailInstructions.take 5 ++ [.BEQ .x18 .x0 8, .JAL .x0 2094796]

def recordTailPrefix (state : MachineState) (count : Nat) : MachineState :=
  (recordTailInstructions.take count).foldl execInstrBr state

private theorem record_tail_decoded (i : Fin 6) :
    (openingImage.code[596 + i.val]?).bind Opening.decodeBase =
      some (recordTailInstructions[i.val]?.getD .EBREAK) := by
  fin_cases i <;> rfl

private theorem record_tail_prefix_succ (state : MachineState) (i : Nat) (bounded : i < 6) :
    recordTailPrefix state (i + 1) =
      execInstrBr (recordTailPrefix state i) (recordTailInstructions[i]?.getD .EBREAK) := by
  have inside : i < recordTailInstructions.length := by change i < 7; omega
  rw [recordTailPrefix, recordTailPrefix, List.take_succ_eq_append_getElem inside,
    List.foldl_append, List.getElem?_eq_getElem inside]
  rfl

private theorem record_tail_ordinary (state : MachineState) (i : Fin 6)
    (valid : memoryArgumentsValid state (recordTailInstructions[i.val]?.getD .EBREAK) = true) :
    ordinaryStep state (.base (recordTailInstructions[i.val]?.getD .EBREAK)) =
      some (execInstrBr state (recordTailInstructions[i.val]?.getD .EBREAK)) := by
  fin_cases i <;> simp [recordTailInstructions, Opening.recordTailInstructions] at valid ⊢ <;> exact ite_eq_left valid

/-- Mark the current cap group, advance the ordinal, and branch if any remain. -/
theorem execute_record_tail (state : MachineState) (pc : state.pc = 0x1950) (fuel : Nat)
    (allowCoins : Bool) (markAccess : accessValid (recordMarkAddress state) 8 = true) :
    execute openingImage (6 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (recordTailPrefix state 6) allowCoins
          return result.charge 6 0) := by
  apply execute_unit_steps (states := recordTailPrefix state)
  intro i bounded
  refine ⟨.base (recordTailInstructions[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply packed_fetch_base _ (596+i) _ (by omega) _ (record_tail_decoded ⟨i, bounded⟩)
    interval_cases i <;> simp [recordTailPrefix, recordTailInstructions, Opening.recordTailInstructions, execInstrBr, pc]
  · rw [record_tail_prefix_succ state i bounded]
    apply record_tail_ordinary _ ⟨i, bounded⟩
    simp only [recordMarkAddress] at markAccess
    interval_cases i <;>
      simp [memoryArgumentsValid, memAccess, recordTailPrefix, recordTailInstructions, Opening.recordTailInstructions,
        execInstrBr, signExtend12, markAccess]
  · interval_cases i <;> rfl

theorem record_tail_post (state : MachineState) (pc : state.pc = 0x1950) :
    let after := recordTailPrefix state 6
    after.mem = (state.setMem (recordMarkAddress state) (state.getReg .x23)).mem ∧
    after.getReg .x8 = state.getReg .x8 + 8#64 ∧
    after.getReg .x18 = state.getReg .x18 - 1 ∧
    after.pc = if state.getReg .x18 - 1 = 0#64 then 0x196c else 0x1968 := by
  by_cases done : state.getReg .x18 + 18446744073709551615#64 = 0#64 <;>
    simp [recordTailPrefix, recordTailInstructions, Opening.recordTailInstructions, execInstrBr, recordMarkAddress, signExtend12,
      signExtend13, BitVec.sub_eq_add_neg, pc, done]

/-- The continuing latch jumps back to the next record after its common prefix. -/
theorem execute_record_continue (state : MachineState) (pc : state.pc = 0x1968)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (1+fuel) state allowCoins =
      (do let result ← execute openingImage fuel (state.setPC 0x1034) allowCoins
          return result.charge 1 0) := by
  have fetched := packed_fetch_base state 602 (.JAL .x0 2094796) (by decide) pc rfl
  have step : ordinaryStep state (.base (.JAL .x0 2094796)) = some (state.setPC 0x1034) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21, pc, MachineState.setReg]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched step]
  rfl

end TwoPermutationPrototype.PackedOpening
