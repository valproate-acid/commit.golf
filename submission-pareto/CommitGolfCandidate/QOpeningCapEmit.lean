import CommitGolfCandidate.QOpeningCapAdvance
import CommitGolfCandidate.QOpeningCopy

namespace TwoPermutationPrototype.QOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] getReg_setReg getReg_setMem

@[local simp] private theorem emit_pc_set (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

def capSource (state : MachineState) : Word :=
  state.getReg .x25 + (state.getReg .x6 <<< 5)

def capEmitPrefix (state : MachineState) (count : Nat) : MachineState :=
  ((capWalkInstructions.drop 8).take count).foldl execInstrBr state

private theorem emit_get_next (state : MachineState) (i : Nat) (bounded : i < 11) :
    capEmitPrefix state (i+1) =
      execInstrBr (capEmitPrefix state i) ((capWalkInstructions.drop 8)[i]?.getD .EBREAK) := by
  have inside : i < (capWalkInstructions.drop 8).length := by
    change i < 19
    omega
  rw [capEmitPrefix, capEmitPrefix, List.take_succ_eq_append_getElem inside,
    List.foldl_append, List.getElem?_eq_getElem inside]
  rfl

private theorem emit_ordinary (state : MachineState) (i : Fin 11)
    (valid : memoryArgumentsValid state ((capWalkInstructions.drop 8)[i.val]?.getD .EBREAK) = true) :
    ordinaryStep state (.base ((capWalkInstructions.drop 8)[i.val]?.getD .EBREAK)) =
      some (execInstrBr state ((capWalkInstructions.drop 8)[i.val]?.getD .EBREAK)) := by
  fin_cases i <;> simp [capWalkInstructions] at valid ⊢ <;> exact ite_eq_left valid

/-- An unoccupied node copies its stored digest and advances the proof pointer. -/
theorem execute_cap_emit (state : MachineState) (pc : state.pc = 0x10fc)
    (fuel : Nat) (allowCoins : Bool)
    (source : ∀ i : Fin 4, accessValid (capSource state + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (dest : ∀ i : Fin 4, accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * i.val)) 8 = true) :
    execute openingImage (11 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (capEmitPrefix state 11) allowCoins
          return result.charge 11 0) := by
  apply execute_unit_steps (states := capEmitPrefix state)
  intro i bounded
  refine ⟨.base ((capWalkInstructions.drop 8)[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply opening_fetch _ (63 + i) _ (by omega)
    · interval_cases i <;> simp [capEmitPrefix, capWalkInstructions, execInstrBr, pc]
    · interval_cases i <;> rfl
  · rw [emit_get_next state i bounded]
    apply emit_ordinary _ ⟨i, bounded⟩
    have s0 : accessValid (capSource state) 8 = true := by simpa using source 0
    have s1 : accessValid (capSource state + 8#64) 8 = true := source 1
    have s2 : accessValid (capSource state + 16#64) 8 = true := source 2
    have s3 : accessValid (capSource state + 24#64) 8 = true := source 3
    have d0 : accessValid (state.getReg .x21) 8 = true := by simpa using dest 0
    have d1 : accessValid (state.getReg .x21 + 8#64) 8 = true := dest 1
    have d2 : accessValid (state.getReg .x21 + 16#64) 8 = true := dest 2
    have d3 : accessValid (state.getReg .x21 + 24#64) 8 = true := dest 3
    simp only [capSource] at s0 s1 s2 s3
    interval_cases i <;>
      simp [memoryArgumentsValid, memAccess, capEmitPrefix, capWalkInstructions, execInstrBr,
        signExtend12, s0, s1, s2, s3, d0, d1, d2, d3]
  · interval_cases i <;> rfl

private theorem emit_copy_part (state : MachineState) :
    capEmitPrefix state 10 = copyBlock (capEmitPrefix state 2) := by
  unfold capEmitPrefix copyBlock
  rw [show (capWalkInstructions.drop 8).take 10 =
    (capWalkInstructions.drop 8).take 2 ++ copyInstructions by decide, List.foldl_append]

/-- The cap emission and the lower sibling use the same verified four-word copy. -/
theorem cap_emit_memory (state : MachineState)
    (separate : ∀ i j : Fin 4, capSource state + BitVec.ofNat 64 (8 * i.val) ≠
      state.getReg .x21 + BitVec.ofNat 64 (8 * j.val)) :
    (capEmitPrefix state 11).mem = (fourWordStore state (capSource state) (state.getReg .x21)).mem := by
  have source : (capEmitPrefix state 2).getReg .x7 = capSource state := by
    simp [capEmitPrefix, capWalkInstructions, execInstrBr, capSource]
  have dest : (capEmitPrefix state 2).getReg .x21 = state.getReg .x21 := by
    simp [capEmitPrefix, capWalkInstructions, execInstrBr]
  have before : (capEmitPrefix state 2).mem = state.mem := rfl
  have disjoint (i j : Fin 4) :
      (capEmitPrefix state 2).getReg .x7 + BitVec.ofNat 64 (8 * i.val) ≠
        (capEmitPrefix state 2).getReg .x21 + BitVec.ofNat 64 (8 * j.val) := by
    rw [source, dest]
    exact separate i j
  have tweak : (capEmitPrefix state 11).mem = (capEmitPrefix state 10).mem := by
    rw [emit_get_next state 10 (by decide)]
    rfl
  have copied := copy_block_memory (capEmitPrefix state 2) disjoint
  rw [source, dest] at copied
  exact tweak.trans ((congrArg MachineState.mem (emit_copy_part state)).trans
    (copied.trans (four_word_store_mem_congr _ _ _ _ before)))

theorem cap_emit_post (state : MachineState) (pc : state.pc = 0x10fc) :
    let after := capEmitPrefix state 11
    after.pc = 0x1128 ∧ after.getReg .x6 = state.getReg .x6 ∧
      after.getReg .x21 = state.getReg .x21 + 32#64 := by
  simp [capEmitPrefix, capWalkInstructions, execInstrBr, signExtend12, pc]

end TwoPermutationPrototype.QOpening
