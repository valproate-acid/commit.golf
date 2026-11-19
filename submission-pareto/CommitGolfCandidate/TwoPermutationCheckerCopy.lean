import CommitGolfCandidate.TwoPermutationCheckerImage
import CommitGolfCandidate.TwoPermutationOpeningCopy

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

def copySource (start : Nat) : Reg :=
  if start = 78 ∨ start = 103 ∨ start = 176 then .x21 else .x23
def copyTarget (start : Nat) : Reg :=
  if start = 137 then .x28 else if start = 176 then .x7 else .x24

def copyOffset (start : Nat) : Nat :=
  if start = 86 ∨ start = 103 then 32 else 0

def CopyBlock (start : Nat) : Prop :=
  start = 78 ∨ start = 86 ∨ start = 95 ∨ start = 103 ∨ start = 137 ∨ start = 176

private def copyCode (start : Nat) : List Instr :=
  [.LD .x31 (copySource start) 0, .SD (copyTarget start) .x31 (BitVec.ofNat 12 (copyOffset start)),
   .LD .x31 (copySource start) 8, .SD (copyTarget start) .x31 (BitVec.ofNat 12 (copyOffset start + 8)),
   .LD .x31 (copySource start) 16, .SD (copyTarget start) .x31 (BitVec.ofNat 12 (copyOffset start + 16)),
   .LD .x31 (copySource start) 24, .SD (copyTarget start) .x31 (BitVec.ofNat 12 (copyOffset start + 24))]

private def copyPrefix (state : MachineState) (start count : Nat) : MachineState :=
  ((copyCode start).take count).foldl execInstrBr state

def copied (state : MachineState) (start : Nat) : MachineState :=
  copyPrefix state start 8

private theorem copy_prefix_register (state : MachineState) (start count : Nat)
    (bounded : count ≤ 8) (reg : Reg) (notScratch : reg ≠ .x31) :
    (copyPrefix state start count).getReg reg = state.getReg reg := by
  have memRegister (state : MachineState) (address value : Word) (reg : Reg) :
      (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl
  interval_cases count <;>
    simp only [copyPrefix, copyCode, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, memRegister,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notScratch)]

theorem copied_register (state : MachineState) (start : Nat) (reg : Reg)
    (notScratch : reg ≠ .x31) :
    (copied state start).getReg reg = state.getReg reg :=
  copy_prefix_register state start 8 (by decide) reg notScratch

theorem copied_pc (state : MachineState) (start : Nat) :
    (copied state start).pc = state.pc + 32 := by
  simp [copied, copyPrefix, copyCode, execInstrBr,
    MachineState.setPC, BitVec.add_assoc]

set_option maxHeartbeats 1500000 in
/-- Each copy in the two ordering branches uses eight ordinary instructions.
The same instruction sequence also copies new cap leaves and frontier nodes. -/
theorem execute_copy (state : MachineState) (start : Nat)
    (location : CopyBlock start)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start))
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg (copySource start) + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (targetValid : ∀ word : Fin 4,
      accessValid (state.getReg (copyTarget start) + BitVec.ofNat 64 (copyOffset start+8*word.val)) 8 = true)
    (fuel : Nat) :
    execute checkerImage (8 + fuel) state false =
      (do let result ← execute checkerImage fuel (copied state start) false
          return result.charge 8 0) := by
  apply execute_unit_steps (states := copyPrefix state start)
  intro i hi
  refine ⟨.base (((copyCode start)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply checker_fetch _ (start + i) _ (by rcases location with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    · rcases location with rfl | rfl | rfl | rfl | rfl | rfl <;> interval_cases i <;>
        simp [copyPrefix, copyCode, execInstrBr, pc, MachineState.setPC]
    · rcases location with rfl | rfl | rfl | rfl | rfl | rfl <;> interval_cases i <;> rfl
  · have sourceReg := copy_prefix_register state start i (by omega) (copySource start)
      (by rcases location with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    have targetReg := copy_prefix_register state start i (by omega) (copyTarget start)
      (by rcases location with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have s3 := sourceValid ⟨3, by decide⟩
    have valid : memoryArgumentsValid (copyPrefix state start i)
        (((copyCode start)[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [copyCode, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, sourceReg, targetReg, signExtend12] <;>
        first | exact s0 | exact s1 | exact s2 | exact s3 |
          (rcases location with rfl | rfl | rfl | rfl | rfl | rfl <;>
            first | exact targetValid 0 | exact targetValid 1 | exact targetValid 2 | exact targetValid 3)
    interval_cases i <;>
      simp only [copyCode, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

attribute [local simp] Opening.getReg_setMem Opening.getReg_setReg MachineState.getReg_setPC

@[local simp] private theorem copy_mem_set_reg (s : MachineState) (reg : Reg) (value : Word) :
    (s.setReg reg value).mem = s.mem := by cases reg <;> rfl

@[local simp] private theorem copy_mem_set_pc (s : MachineState) (pc : Word) :
    (s.setPC pc).mem = s.mem := rfl

private theorem copy_mem_set_mem (s : MachineState) (address value : Word) :
    (s.setMem address value).mem =
      fun atWord => if atWord = address then value else s.mem atWord := by
  funext atWord
  simp [MachineState.setMem]

set_option maxHeartbeats 2500000 in
theorem copied_memory (state : MachineState) (start : Nat) (valid : CopyBlock start)
    (separate : ∀ i j : Fin 4, state.getReg (copySource start) + BitVec.ofNat 64 (8*i.val) ≠
      state.getReg (copyTarget start) + BitVec.ofNat 64 (copyOffset start+8*j.val)) :
    (copied state start).mem = (Opening.fourWordStore state (state.getReg (copySource start))
      (state.getReg (copyTarget start)+BitVec.ofNat 64 (copyOffset start))).mem := by
  have h10 := separate 1 0
  have h20 := separate 2 0
  have h21 := separate 2 1
  have h30 := separate 3 0
  have h31 := separate 3 1
  have h32 := separate 3 2
  rcases valid with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [copied, copyPrefix, copyCode, copySource, copyTarget, copyOffset, Opening.fourWordStore,
      execInstrBr, signExtend12, copy_mem_set_mem, MachineState.getMem, BitVec.add_assoc]
       at h10 h20 h21 h30 h31 h32 ⊢ <;>
    simp [h10, h20, h21, h30, h31, h32]

theorem copied_frame (state : MachineState) (start : Nat) (valid : CopyBlock start)
    (separate : ∀ i j : Fin 4, state.getReg (copySource start) + BitVec.ofNat 64 (8*i.val) ≠
      state.getReg (copyTarget start) + BitVec.ofNat 64 (copyOffset start+8*j.val))
    (atWord : Word) (outside : ∀ i : Fin 4,
      atWord ≠ (state.getReg (copyTarget start)+BitVec.ofNat 64 (copyOffset start)) + BitVec.ofNat 64 (8*i.val)) :
    (copied state start).getMem atWord = state.getMem atWord := by
  rw [MachineState.getMem, copied_memory state start valid separate]
  exact Opening.four_word_store_outside _ _ _ _ outside

end TwoPermutationPrototype.Checker
