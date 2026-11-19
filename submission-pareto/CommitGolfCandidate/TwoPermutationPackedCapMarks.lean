import CommitGolfCandidate.TwoPermutationPackedCapFetch
import CommitGolfCandidate.TwoPermutationOpeningMarkMachine

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 4096
open TwoPermutationPrototype.Opening

attribute [local simp] getReg_setReg getReg_setMem

@[local simp] private theorem pc_setPC (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

@[local simp] private theorem zero_reg (state : MachineState) : state.getReg .x0 = 0#64 := rfl

def markParentPrefix (state : MachineState) (count : Nat) : MachineState :=
  ((capMarkInstructions.drop 1).take count).foldl execInstrBr state

def childrenAddress (state : MachineState) : Word :=
  state.getReg .x26 + (state.getReg .x6 <<< 4)

def parentAddress (state : MachineState) : Word :=
  state.getReg .x26 + (state.getReg .x6 <<< 3)

private theorem mark_decode (i : Fin 10) :
    (packedImage.code[274+i.val]?).bind decodeInstruction =
      some (.base ((capMarkInstructions.drop 1)[i.val]?.getD .EBREAK)) := by
  fin_cases i <;> rfl

theorem mark_prefix_succ (state : MachineState) (i : Nat) (bounded : i < 10) :
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
theorem execute_mark_parent (state : MachineState) (pc : state.pc = 0x1448) (fuel : Nat)
    (left : accessValid (childrenAddress state) 8 = true)
    (right : accessValid (childrenAddress state + 8#64) 8 = true)
    (parent : accessValid (parentAddress state) 8 = true) :
    execute packedImage (10 + fuel) state false =
      (do let result ← execute packedImage fuel (markParentPrefix state 10) false
          return result.charge 10 0) := by
  apply execute_unit_steps (states := markParentPrefix state)
  intro i bounded
  refine ⟨.base ((capMarkInstructions.drop 1)[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_fetch _ (274 + i) _ (by omega) _ (mark_decode ⟨i, bounded⟩)
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
theorem mark_parent_post (state : MachineState) (pc : state.pc = 0x1448) :
    let after := markParentPrefix state 10
    let left := state.getMem (childrenAddress state)
    let right := state.getMem (childrenAddress state + 8#64)
    after.mem = (state.setMem (parentAddress state) (left ||| right)).mem ∧
    after.getReg .x26 = state.getReg .x26 ∧
    after.getReg .x6 = state.getReg .x6 - 1 ∧
    after.pc = if state.getReg .x6 - 1 = 0#64 then 0x1470 else 0x1448 := by
  by_cases done : state.getReg .x6 + 18446744073709551615#64 = 0#64 <;>
    simp [markParentPrefix, capMarkInstructions, execInstrBr, parentAddress, childrenAddress,
      signExtend12, signExtend13, BitVec.sub_eq_add_neg, pc, done]

end TwoPermutationPrototype.Packed.Checker
