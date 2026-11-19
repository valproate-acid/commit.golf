import CommitGolfCandidate.TwoPermutationPackedCheckerSteps
import CommitGolfCandidate.TwoPermutationCheckerCopyDigest

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
def ChildSite (start : Nat) : Prop := start=99 ∨ start=108 ∨ start=183 ∨ start=192
def childOffset (start : Nat) := if start=99 ∨ start=183 then 32 else 0

private def copyCode (start : Nat) : List Instr :=
  [.LD .x31 (.x23) 0, .SD (.x24) .x31 (BitVec.ofNat 12 (childOffset start)),
   .LD .x31 (.x23) 8, .SD (.x24) .x31 (BitVec.ofNat 12 (childOffset start + 8)),
   .LD .x31 (.x23) 16, .SD (.x24) .x31 (BitVec.ofNat 12 (childOffset start + 16)),
   .LD .x31 (.x23) 24, .SD (.x24) .x31 (BitVec.ofNat 12 (childOffset start + 24))]

private def copyPrefix (state : MachineState) (start count : Nat) : MachineState :=
  ((copyCode start).take count).foldl execInstrBr state

def childCopied (state : MachineState) (start : Nat) : MachineState :=
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

theorem childCopied_register (state : MachineState) (start : Nat) (reg : Reg)
    (notScratch : reg ≠ .x31) :
    (childCopied state start).getReg reg = state.getReg reg :=
  copy_prefix_register state start 8 (by decide) reg notScratch

theorem childCopied_pc (state : MachineState) (start : Nat) :
    (childCopied state start).pc = state.pc + 32 := by
  simp [childCopied, copyPrefix, copyCode, execInstrBr,
    MachineState.setPC, BitVec.add_assoc]

set_option maxHeartbeats 1500000 in
/-- Each copy in the two ordering branches uses eight ordinary instructions.
The same instruction sequence also copies new cap leaves and frontier nodes. -/
theorem execute_child_copy (state : MachineState) (start : Nat)
    (location : ChildSite start)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start))
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg (.x23) + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (targetValid : ∀ word : Fin 4,
      accessValid (state.getReg (.x24) + BitVec.ofNat 64 (childOffset start+8*word.val)) 8 = true)
    (fuel : Nat) :
    execute packedImage (8 + fuel) state false =
      (do let result ← execute packedImage fuel (childCopied state start) false
          return result.charge 8 0) := by
  apply execute_unit_steps (states := copyPrefix state start)
  intro i hi
  refine ⟨.base (((copyCode start)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetch_at _ (start + i) _ (by rcases location with rfl | rfl | rfl | rfl <;> omega)
    · rcases location with rfl | rfl | rfl | rfl <;> interval_cases i <;>
        simp [copyPrefix, copyCode, execInstrBr, pc, MachineState.setPC]
    · rcases location with rfl | rfl | rfl | rfl <;> interval_cases i <;> rfl
  · have sourceReg := copy_prefix_register state start i (by omega) (.x23)
      (by rcases location with rfl | rfl | rfl | rfl <;> decide)
    have targetReg := copy_prefix_register state start i (by omega) (.x24)
      (by rcases location with rfl | rfl | rfl | rfl <;> decide)
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
          (rcases location with rfl | rfl | rfl | rfl <;>
            first | exact targetValid 0 | exact targetValid 1 | exact targetValid 2 | exact targetValid 3)
    interval_cases i <;>
      simp only [copyCode, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl


theorem child_as_old (s : MachineState) (start : Nat) (site : ChildSite start) :
    childCopied s start = TwoPermutationPrototype.Checker.copied s (if childOffset start=32 then 86 else 95) := by
  rcases site with rfl | rfl | rfl | rfl <;> rfl

end TwoPermutationPrototype.Packed.Checker
