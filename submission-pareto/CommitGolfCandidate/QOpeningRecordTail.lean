import CommitGolfCandidate.QOpeningFootprint

namespace TwoPermutationPrototype.QOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] getReg_setReg getReg_setMem

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

def recordMarkAddress (state : MachineState) : Word :=
  state.getReg .x26 + (state.getReg .x6 <<< 3)

def recordTailPrefix (state : MachineState) (count : Nat) : MachineState :=
  (recordTailInstructions.take count).foldl execInstrBr state

private theorem record_tail_decoded (i : Fin 6) :
    (openingImage.code[38 + i.val]?).bind decodeInstruction =
      some (.base (recordTailInstructions[i.val]?.getD .EBREAK)) := by
  fin_cases i <;> rfl

private theorem record_tail_prefix_succ (state : MachineState) (i : Nat) (bounded : i < 6) :
    recordTailPrefix state (i + 1) =
      execInstrBr (recordTailPrefix state i) (recordTailInstructions[i]?.getD .EBREAK) := by
  have inside : i < recordTailInstructions.length := bounded
  rw [recordTailPrefix, recordTailPrefix, List.take_succ_eq_append_getElem inside,
    List.foldl_append, List.getElem?_eq_getElem inside]
  rfl

private theorem record_tail_ordinary (state : MachineState) (i : Fin 6)
    (valid : memoryArgumentsValid state (recordTailInstructions[i.val]?.getD .EBREAK) = true) :
    ordinaryStep state (.base (recordTailInstructions[i.val]?.getD .EBREAK)) =
      some (execInstrBr state (recordTailInstructions[i.val]?.getD .EBREAK)) := by
  fin_cases i <;> simp [recordTailInstructions] at valid ⊢ <;> exact ite_eq_left valid

/-- Mark the current cap group, advance the ordinal, and branch if any remain. -/
theorem execute_record_tail (state : MachineState) (pc : state.pc = 0x1098) (fuel : Nat)
    (allowCoins : Bool) (markAccess : accessValid (recordMarkAddress state) 8 = true) :
    execute openingImage (6 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (recordTailPrefix state 6) allowCoins
          return result.charge 6 0) := by
  apply execute_unit_steps (states := recordTailPrefix state)
  intro i bounded
  refine ⟨.base (recordTailInstructions[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply opening_fetch _ (38+i) _ (by omega) _ (record_tail_decoded ⟨i, bounded⟩)
    interval_cases i <;> simp [recordTailPrefix, recordTailInstructions, execInstrBr, pc]
  · rw [record_tail_prefix_succ state i bounded]
    apply record_tail_ordinary _ ⟨i, bounded⟩
    simp only [recordMarkAddress] at markAccess
    interval_cases i <;>
      simp [memoryArgumentsValid, memAccess, recordTailPrefix, recordTailInstructions,
        execInstrBr, signExtend12, markAccess]
  · interval_cases i <;> rfl

theorem record_tail_post (state : MachineState) (pc : state.pc = 0x1098) :
    let after := recordTailPrefix state 6
    after.mem = (state.setMem (recordMarkAddress state) (state.getReg .x23)).mem ∧
    after.getReg .x8 = state.getReg .x8 + 8#64 ∧
    after.getReg .x18 = state.getReg .x18 - 1 ∧
    after.pc = if state.getReg .x18 - 1 = 0#64 then 0x10b0 else 0x1034 := by
  by_cases done : state.getReg .x18 + 18446744073709551615#64 = 0#64 <;>
    simp [recordTailPrefix, recordTailInstructions, execInstrBr, recordMarkAddress, signExtend12,
      signExtend13, BitVec.sub_eq_add_neg, pc, done]

theorem record_mark_address (state : MachineState) (group : Nat)
    (base : state.getReg .x26 = BitVec.ofNat 64 markBase)
    (position : state.getReg .x6 = BitVec.ofNat 64 group) :
    recordMarkAddress state = BitVec.ofNat 64 (markBase + 8 * group) := by
  rw [recordMarkAddress, base, position, BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 markBase + BitVec.ofNat 64 group * BitVec.ofNat 64 8 = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm group]

end TwoPermutationPrototype.QOpening
