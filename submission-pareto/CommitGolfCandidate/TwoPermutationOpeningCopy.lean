import CommitGolfCandidate.TwoPermutationOpeningFootprint

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64

attribute [local simp] getReg_setReg getReg_setMem

private theorem mem_set_reg (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).mem = s.mem := by cases r <;> rfl

private theorem mem_set_pc (s : MachineState) (pc : Word) :
    (s.setPC pc).mem = s.mem := rfl

private theorem mem_set_mem (s : MachineState) (address value : Word) :
    (s.setMem address value).mem =
      fun atAddress => if atAddress = address then value else s.mem atAddress := by
  funext address
  simp [MachineState.setMem]

def copyInstructions : List Instr :=
  [.LD .x31 .x7 0, .SD .x21 .x31 0, .LD .x31 .x7 8, .SD .x21 .x31 8,
   .LD .x31 .x7 16, .SD .x21 .x31 16, .LD .x31 .x7 24, .SD .x21 .x31 24]

def copyBlock (state : MachineState) : MachineState :=
  copyInstructions.foldl execInstrBr state

def fourWordStore (state : MachineState) (source dest : Word) : MachineState :=
  ((((state.setMem dest (state.getMem source)).setMem
    (dest + 8#64) (state.getMem (source + 8#64))).setMem
    (dest + 16#64) (state.getMem (source + 16#64))).setMem
    (dest + 24#64) (state.getMem (source + 24#64)))

/-- Shared ordinary load/store body used by both the lower records and the cap. -/
theorem copy_block_memory (state : MachineState)
    (separate : ∀ i j : Fin 4, state.getReg .x7 + BitVec.ofNat 64 (8 * i.val) ≠
      state.getReg .x21 + BitVec.ofNat 64 (8 * j.val)) :
    (copyBlock state).mem = (fourWordStore state (state.getReg .x7) (state.getReg .x21)).mem := by
  have h10 : state.getReg .x7 + 8#64 ≠ state.getReg .x21 := by simpa using separate 1 0
  have h20 : state.getReg .x7 + 16#64 ≠ state.getReg .x21 := by simpa using separate 2 0
  have h21 : state.getReg .x7 + 16#64 ≠ state.getReg .x21 + 8#64 := separate 2 1
  have h30 : state.getReg .x7 + 24#64 ≠ state.getReg .x21 := by simpa using separate 3 0
  have h31 : state.getReg .x7 + 24#64 ≠ state.getReg .x21 + 8#64 := separate 3 1
  have h32 : state.getReg .x7 + 24#64 ≠ state.getReg .x21 + 16#64 := separate 3 2
  simp [copyBlock, copyInstructions, fourWordStore, execInstrBr, signExtend12,
    mem_set_reg, mem_set_pc, mem_set_mem, h10, h20, h21, h30, h31, h32]

theorem copy_register (state : MachineState) (reg : Reg) (temp : reg ≠ .x31) :
    (copyBlock state).getReg reg = state.getReg reg := by
  simp [copyBlock, copyInstructions, execInstrBr, Ne.symm temp]

theorem four_word_store_outside (state : MachineState) (source dest atWord : Word)
    (outside : ∀ i : Fin 4, atWord ≠ dest + BitVec.ofNat 64 (8 * i.val)) :
    (fourWordStore state source dest).getMem atWord = state.getMem atWord := by
  have first : atWord ≠ dest := by simpa using outside 0
  have second : atWord ≠ dest + 8#64 := outside 1
  have third : atWord ≠ dest + 16#64 := outside 2
  have fourth : atWord ≠ dest + 24#64 := outside 3
  simp [fourWordStore, first, second, third, fourth]

theorem four_word_store_mem_congr (before after : MachineState) (source dest : Word)
    (memory : before.mem = after.mem) :
    (fourWordStore before source dest).mem = (fourWordStore after source dest).mem := by
  simp only [fourWordStore, mem_set_mem, MachineState.getMem, memory]

end TwoPermutationPrototype.Opening
