import CommitGolfCandidate.TwoPermutationPackedCheckerSteps
import CommitGolfCandidate.TwoPermutationCheckerCopyDigest
import CommitGolfCandidate.TwoPermutationCheckerLeafRun

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

private def copyWords : List Instr :=
  [.LD .x31 .x23 0, .SD .x28 .x31 0, .LD .x31 .x23 8, .SD .x28 .x31 8,
   .LD .x31 .x23 16, .SD .x28 .x31 16, .LD .x31 .x23 24, .SD .x28 .x31 24]

private def copyPrefix (s : MachineState) (count : Nat) :=
  (copyWords.take count).foldl execInstrBr s

def copiedGroup (s : MachineState) := copyPrefix s 8

private theorem store_register (s : MachineState) (address value : Word) (r : Reg) :
    (s.setMem address value).getReg r = s.getReg r := by cases r <;> rfl

private theorem copy_keeps (s : MachineState) (count : Nat) (bounded : count ≤ 8)
    (reg : Reg) (notScratch : reg ≠ .x31) :
    (copyPrefix s count).getReg reg = s.getReg reg := by
  interval_cases count <;>
    simp only [copyPrefix,copyWords,List.take,List.foldl,execInstrBr,MachineState.getReg_setPC,
      store_register,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notScratch)]

theorem copied_group_register (s : MachineState) (r : Reg) (other : r ≠ .x31) :
    (copiedGroup s).getReg r = s.getReg r :=
  copy_keeps s 8 (by decide) r other

theorem copied_group_pc (s : MachineState) : (copiedGroup s).pc = s.pc+32 := by
  simp [copiedGroup,copyPrefix,copyWords,execInstrBr,MachineState.setPC,BitVec.add_assoc]

theorem execute_group_copy (s : MachineState) (pc : s.pc = 0x140c)
    (readable : ∀ j : Fin 4, accessValid (s.getReg .x23+BitVec.ofNat 64 (8*j.val)) 8 = true)
    (writable : ∀ j : Fin 4, accessValid (s.getReg .x28+BitVec.ofNat 64 (8*j.val)) 8 = true) :
    GroupHop s (copiedGroup s) 8 := by
  intro fuel
  apply execute_unit_steps (states := copyPrefix s)
  intro i bounded
  have src := copy_keeps s i (by omega) .x23 (by decide)
  have dst := copy_keeps s i (by omega) .x28 (by decide)
  have r0 := readable ⟨0,by decide⟩
  have r1 := readable ⟨1,by decide⟩
  have r2 := readable ⟨2,by decide⟩
  have r3 := readable ⟨3,by decide⟩
  have w0 := writable ⟨0,by decide⟩
  have w1 := writable ⟨1,by decide⟩
  have w2 := writable ⟨2,by decide⟩
  have w3 := writable ⟨3,by decide⟩
  have valid : memoryArgumentsValid (copyPrefix s i) (copyWords[i]?.getD .EBREAK) = true := by
    interval_cases i <;>
      simp only [copyWords,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
        memoryArgumentsValid,memAccess,src,dst] <;>
      first | exact r0 | exact r1 | exact r2 | exact r3 | exact w0 | exact w1 | exact w2 | exact w3
  refine ⟨.base (copyWords[i]?.getD .EBREAK),fetch_at _ (259+i) _ (by omega) ?_ ?_,?_,?_⟩
  · interval_cases i <;> simp [copyPrefix,copyWords,execInstrBr,pc,MachineState.setPC]
  · interval_cases i <;> rfl
  · simp only [ordinaryStep]
    interval_cases i <;> simp only [copyWords,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some] at valid ⊢ <;> rw [ite_eq_left valid] <;> rfl
  · interval_cases i <;> rfl

attribute [local simp] Opening.getReg_setMem Opening.getReg_setReg MachineState.getReg_setPC

@[local simp] private theorem copy_mem_set_reg (s : MachineState) (reg : Reg) (value : Word) :
    (s.setReg reg value).mem = s.mem := by cases reg <;> rfl

@[local simp] private theorem copy_mem_set_pc (s : MachineState) (pc : Word) :
    (s.setPC pc).mem = s.mem := rfl

private theorem mem_store (s : MachineState) (address value : Word) :
    (s.setMem address value).mem = fun word => if word = address then value else s.mem word := by
  funext word
  simp [MachineState.setMem]

theorem copied_group_memory (s : MachineState)
    (separate : ∀ i j : Fin 4, s.getReg .x23+BitVec.ofNat 64 (8*i.val) ≠
      s.getReg .x28+BitVec.ofNat 64 (8*j.val)) :
    (copiedGroup s).mem = (Opening.fourWordStore s (s.getReg .x23) (s.getReg .x28)).mem := by
  have h10 := separate 1 0
  have h20 := separate 2 0
  have h21 := separate 2 1
  have h30 := separate 3 0
  have h31 := separate 3 1
  have h32 := separate 3 2
  simp [copiedGroup,copyPrefix,copyWords,Opening.fourWordStore,execInstrBr,
    signExtend12,mem_store,MachineState.getMem,BitVec.add_assoc] at h10 h20 h21 h30 h31 h32 ⊢
  all_goals simp [h10,h20,h21,h30,h31,h32]

end TwoPermutationPrototype.Packed.Checker
