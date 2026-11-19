import CommitGolfCandidate.TwoPermutationOpeningSiblingStep
import CommitGolfCandidate.TwoPermutationOpeningCopy

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] getReg_setMem getReg_setReg

set_option maxRecDepth 4096

@[local simp] private theorem mem_setReg (s : MachineState) (r : Reg) (w : Word) :
    (s.setReg r w).mem = s.mem := by cases r <;> rfl

@[local simp] private theorem mem_setPC (s : MachineState) (w : Word) :
    (s.setPC w).mem = s.mem := rfl

@[local simp] private theorem sibling_zero (s : MachineState) : s.getReg .x0 = 0#64 := rfl

private def siblingEnd (state : MachineState) : MachineState :=
  (siblingInstructions.drop 11).foldl execInstrBr state

private theorem split_sibling (state : MachineState) :
    siblingPrefix state 15 = siblingEnd (siblingPrefix state 11) := by
  unfold siblingPrefix siblingEnd
  rw [List.take_of_length_le (by decide : siblingInstructions.length ≤ 15)]
  conv_lhs => rw [← List.take_append_drop 11 siblingInstructions]
  rw [List.foldl_append]

private theorem sibling_end_memory (state : MachineState) :
    (siblingEnd state).mem = state.mem := by
  by_cases done : state.getReg .x29 + 18446744073709551615#64 = 0#64 <;>
    simp [siblingEnd, siblingInstructions, execInstrBr, signExtend12, done]

private theorem sibling_copy_block (state : MachineState) :
    siblingPrefix state 11 = copyBlock (siblingPrefix state 3) := by
  unfold siblingPrefix copyBlock
  rw [show siblingInstructions.take 11 = siblingInstructions.take 3 ++ copyInstructions by decide,
    List.foldl_append]

private theorem sibling_source_pointer (state : MachineState) :
    (siblingPrefix state 3).getReg .x7 = siblingSource state := by
  simp [siblingPrefix, siblingInstructions, execInstrBr, siblingSource, signExtend12]

private theorem sibling_dest_pointer (state : MachineState) :
    (siblingPrefix state 3).getReg .x21 = state.getReg .x21 := by
  simp [siblingPrefix, siblingInstructions, execInstrBr]

private theorem sibling_prepare_memory (state : MachineState) :
    (siblingPrefix state 3).mem = state.mem := rfl

private theorem sibling_pre_latch_memory (state : MachineState)
    (separate : ∀ i j : Fin 4, siblingSource state + BitVec.ofNat 64 (8 * i.val) ≠
      state.getReg .x21 + BitVec.ofNat 64 (8 * j.val)) :
    (siblingPrefix state 11).mem = (fourWordStore state (siblingSource state) (state.getReg .x21)).mem := by
  have disjoint (i j : Fin 4) : (siblingPrefix state 3).getReg .x7 + BitVec.ofNat 64 (8 * i.val) ≠
      (siblingPrefix state 3).getReg .x21 + BitVec.ofNat 64 (8 * j.val) := by
    rw [sibling_source_pointer, sibling_dest_pointer]
    exact separate i j
  rw [sibling_copy_block]
  have copied := copy_block_memory (siblingPrefix state 3) disjoint
  rw [sibling_source_pointer, sibling_dest_pointer] at copied
  exact copied.trans (four_word_store_mem_congr _ _ _ _ (sibling_prepare_memory state))

/-- The lower sibling changes only the four output words and copies their exact
source values. The counter and branch use only registers. -/
theorem sibling_memory (state : MachineState)
    (separate : ∀ i j : Fin 4, siblingSource state + BitVec.ofNat 64 (8 * i.val) ≠
      state.getReg .x21 + BitVec.ofNat 64 (8 * j.val)) :
    (siblingPrefix state 15).mem =
      (fourWordStore state (siblingSource state) (state.getReg .x21)).mem :=
  ((congrArg MachineState.mem (split_sibling state)).trans
    (sibling_end_memory (siblingPrefix state 11))).trans (sibling_pre_latch_memory state separate)

/-- Registers outside the path, destination, counter and temporaries are preserved. -/
theorem sibling_register (state : MachineState) (register : Reg)
    (node : register ≠ .x6) (source : register ≠ .x7) (dest : register ≠ .x21)
    (count : register ≠ .x29) (temp : register ≠ .x31) :
    (siblingPrefix state 15).getReg register = state.getReg register := by
  by_cases done : state.getReg .x29 + 18446744073709551615#64 = 0#64 <;>
    simp [siblingPrefix, siblingInstructions, execInstrBr, signExtend12, done,
      Ne.symm node, Ne.symm source, Ne.symm dest, Ne.symm count, Ne.symm temp]

end TwoPermutationPrototype.Opening
