import CommitGolfCandidate.QOpeningCapImage

namespace TwoPermutationPrototype.QOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] getReg_setReg getReg_setMem

@[local simp] private theorem cursor_pc_setPC (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

@[local simp] private theorem cursor_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

def cursorMarkAddress (state : MachineState) : Word :=
  state.getReg .x26 + (state.getReg .x6 <<< 3)

def cursorVisitPrefix (state : MachineState) (count : Nat) : MachineState :=
  ((capWalkInstructions.drop 1).take count).foldl execInstrBr state

private theorem visit_decode (i : Fin 4) :
    (openingImage.code[56 + i.val]?).bind decodeInstruction =
      some (.base ((capWalkInstructions.drop 1)[i.val]?.getD .EBREAK)) := by
  fin_cases i <;> rfl

private theorem visit_succ (state : MachineState) (i : Nat) (bounded : i < 4) :
    cursorVisitPrefix state (i + 1) =
      execInstrBr (cursorVisitPrefix state i) ((capWalkInstructions.drop 1)[i]?.getD .EBREAK) := by
  have inside : i < (capWalkInstructions.drop 1).length := by
    change i < 26
    omega
  rw [cursorVisitPrefix, cursorVisitPrefix, List.take_succ_eq_append_getElem inside,
    List.foldl_append, List.getElem?_eq_getElem inside]
  rfl

/-- Lookup of the current cap mark and the branch to output or descend. -/
theorem execute_cursor_visit (state : MachineState) (pc : state.pc = 0x10e0)
    (fuel : Nat) (allowCoins : Bool)
    (valid : accessValid (cursorMarkAddress state) 8 = true) :
    execute openingImage (4 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (cursorVisitPrefix state 4) allowCoins
          return result.charge 4 0) := by
  apply execute_unit_steps (states := cursorVisitPrefix state)
  intro i bounded
  refine ⟨.base ((capWalkInstructions.drop 1)[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply opening_fetch _ (56 + i) _ (by omega) _ (visit_decode ⟨i, bounded⟩)
    interval_cases i <;> simp [cursorVisitPrefix, capWalkInstructions, execInstrBr, pc]
  · rw [visit_succ state i bounded]
    simp only [cursorMarkAddress] at valid
    interval_cases i <;>
      simp [ordinaryStep, memoryArgumentsValid, memAccess, cursorVisitPrefix, capWalkInstructions,
        execInstrBr, signExtend12, valid]
  · interval_cases i <;> rfl

theorem cursor_visit_pc (state : MachineState) (pc : state.pc = 0x10e0) :
    (cursorVisitPrefix state 4).pc =
      if state.getMem (cursorMarkAddress state) = 0#64 then 0x10fc else 0x10f0 := by
  by_cases mark : state.getMem (cursorMarkAddress state) = 0#64 <;>
    simp [cursorMarkAddress] at mark ⊢ <;>
    simp [cursorVisitPrefix, capWalkInstructions, execInstrBr, signExtend12, signExtend13, pc, mark]

def cursorKnownPrefix (state : MachineState) (count : Nat) : MachineState :=
  ((capWalkInstructions.drop 5).take count).foldl execInstrBr state

/-- An occupied internal cap node descends to its left child in three cycles. -/
theorem execute_cursor_descend (state : MachineState) (pc : state.pc = 0x10f0)
    (fuel : Nat) (allowCoins : Bool)
    (inside : BitVec.ult (state.getReg .x6) (state.getReg .x27) = true) :
    execute openingImage (3 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (cursorKnownPrefix state 3) allowCoins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := cursorKnownPrefix state)
  intro i bounded
  refine ⟨.base ((capWalkInstructions.drop 5)[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply opening_fetch _ (60 + i) _ (by omega)
    · interval_cases i <;>
        simp [cursorKnownPrefix, capWalkInstructions, execInstrBr, pc, inside]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem cursor_descend_post (state : MachineState) (pc : state.pc = 0x10f0)
    (inside : BitVec.ult (state.getReg .x6) (state.getReg .x27) = true) :
    let next := cursorKnownPrefix state 3
    next.pc = 0x10e0 ∧ next.getReg .x6 = state.getReg .x6 <<< 1 ∧
    next.getReg .x21 = state.getReg .x21 ∧ next.mem = state.mem := by
  simp [MachineState.getReg] at inside
  simp [cursorKnownPrefix, capWalkInstructions, execInstrBr, signExtend21, pc, inside,
    MachineState.setPC, MachineState.setReg, MachineState.getReg]

/-- An occupied cap leaf goes directly to the advance block in one cycle. -/
theorem execute_cursor_prune (state : MachineState) (pc : state.pc = 0x10f0)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (1 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (cursorKnownPrefix state 1) allowCoins
          return result.charge 1 0) := by
  apply execute_unit_steps (states := cursorKnownPrefix state)
  intro i bounded
  have zero : i = 0 := by omega
  subst i
  refine ⟨.base (.BGEU .x6 .x27 56), ?_, rfl, rfl⟩
  exact opening_fetch _ 60 _ (by decide) pc rfl

theorem cursor_prune_post (state : MachineState) (pc : state.pc = 0x10f0)
    (leaf : BitVec.ult (state.getReg .x6) (state.getReg .x27) = false) :
    cursorKnownPrefix state 1 = state.setPC 0x1128 := by
  simp [cursorKnownPrefix, capWalkInstructions, execInstrBr, signExtend13, pc, leaf]

end TwoPermutationPrototype.QOpening
