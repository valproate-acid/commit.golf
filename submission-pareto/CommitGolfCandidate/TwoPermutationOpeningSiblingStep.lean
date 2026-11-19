import CommitGolfCandidate.TwoPermutationOpeningBlocks

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] getReg_setMem getReg_setReg

set_option maxRecDepth 4096

def siblingSource (state : MachineState) : Word :=
  state.getReg .x9 + ((state.getReg .x6 ^^^ 1#64) <<< 5)

def siblingPrefix (state : MachineState) (count : Nat) : MachineState :=
  (siblingInstructions.take count).foldl execInstrBr state

private theorem siblingPrefix_succ (state : MachineState) (i : Nat) (bounded : i < 15) :
    siblingPrefix state (i + 1) =
      execInstrBr (siblingPrefix state i) (siblingInstructions[i]?.getD .EBREAK) := by
  have existsIndex : i < siblingInstructions.length := bounded
  rw [siblingPrefix, siblingPrefix, List.take_succ_eq_append_getElem existsIndex,
    List.foldl_append, List.getElem?_eq_getElem existsIndex]
  rfl

private theorem sibling_ordinary (state : MachineState) (i : Fin 15)
    (valid : memoryArgumentsValid state (siblingInstructions[i.val]?.getD .EBREAK) = true) :
    ordinaryStep state (.base (siblingInstructions[i.val]?.getD .EBREAK)) =
      some (execInstrBr state (siblingInstructions[i.val]?.getD .EBREAK)) := by
  fin_cases i <;>
    simp [siblingInstructions] at valid ⊢ <;>
    exact ite_eq_left valid

/-- The shipped sibling block is a four-word copy followed by its loop latch. -/
theorem execute_sibling (state : MachineState) (pc : state.pc = 0x105c) (fuel : Nat)
    (allowCoins : Bool) (source : ∀ i : Fin 4,
      accessValid (siblingSource state + BitVec.ofNat 64 (8 * i.val)) 8 = true)
    (destination : ∀ i : Fin 4,
      accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * i.val)) 8 = true) :
    execute openingImage (15 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (siblingPrefix state 15) allowCoins
          return result.charge 15 0) := by
  apply execute_unit_steps (states := siblingPrefix state)
  intro i bounded
  refine ⟨.base (siblingInstructions[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply opening_fetch _ (23 + i) _ (by omega) _ (sibling_decode ⟨i, bounded⟩)
    interval_cases i <;>
      simp [siblingPrefix, siblingInstructions, execInstrBr, MachineState.setPC, pc]
  · rw [siblingPrefix_succ state i bounded]
    apply sibling_ordinary _ ⟨i, bounded⟩
    have src0 : accessValid (siblingSource state) 8 = true := by simpa using source 0
    have src1 : accessValid (siblingSource state + 8#64) 8 = true := source 1
    have src2 : accessValid (siblingSource state + 16#64) 8 = true := source 2
    have src3 : accessValid (siblingSource state + 24#64) 8 = true := source 3
    have dst0 : accessValid (state.getReg .x21) 8 = true := by simpa using destination 0
    have dst1 : accessValid (state.getReg .x21 + 8#64) 8 = true := destination 1
    have dst2 : accessValid (state.getReg .x21 + 16#64) 8 = true := destination 2
    have dst3 : accessValid (state.getReg .x21 + 24#64) 8 = true := destination 3
    simp only [siblingSource] at src0 src1 src2 src3
    interval_cases i <;>
      simp [memoryArgumentsValid, memAccess, siblingPrefix, siblingInstructions, execInstrBr,
        signExtend12, src0, src1, src2, src3, dst0, dst1, dst2, dst3]
  · interval_cases i <;> rfl

end TwoPermutationPrototype.Opening
