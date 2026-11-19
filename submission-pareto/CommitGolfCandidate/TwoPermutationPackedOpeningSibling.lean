import CommitGolfCandidate.TwoPermutationPackedOpeningImage
import CommitGolfCandidate.TwoPermutationPackedOpeningSchedule

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

@[local simp] private theorem mem_set_register (state : MachineState) (reg : Reg) (word : Word) :
    (state.setReg reg word).mem = state.mem := by cases reg <;> rfl

@[local simp] private theorem mem_set_pc (state : MachineState) (pc : Word) :
    (state.setPC pc).mem = state.mem := rfl

attribute [local simp] MachineState.getReg_setPC Opening.getReg_setReg

@[local simp] private theorem pc_set (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

def siblingSite (level : Fin 16) : CopySite :=
  if h : level.val = 0 then .firstSibling else .sibling ⟨level.val-1, by omega⟩

def siblingStart (level : Fin 16) : Nat := (siblingSite level).start-3
def siblingEnd (level : Fin 16) : Nat := (siblingSite level).start+2*(siblingSite level).halfwords

theorem sibling_width_exact (level : Fin 16) :
    2*(siblingSite level).halfwords = siblingWidth level.val := by
  by_cases first : level.val = 0 <;> simp [siblingSite, CopySite.halfwords, siblingWidth, first]

theorem sibling_copy_start (level : Fin 16) : siblingStart level+3 = (siblingSite level).start := by
  unfold siblingStart siblingSite
  split <;> simp [CopySite.start] <;> omega

theorem sibling_next (level : Fin 16) (later : level.val+1 < 16) :
    siblingEnd level+2 = siblingStart ⟨level.val+1, later⟩ := by
  have positive : level.val+1 ≠ 0 := by omega
  by_cases first : level.val = 0
  · simp [siblingStart, siblingEnd, siblingSite, CopySite.start, CopySite.halfwords, first]
  · simp [siblingStart, siblingEnd, siblingSite, CopySite.start, CopySite.halfwords, first]
    omega

theorem first_sibling_start : siblingStart 0 = 34 := rfl
theorem last_sibling_end : siblingEnd 15+2 = 596 := rfl

def headCode : List Instr :=
  [.XORI .x7 .x6 1, .SLLI .x7 .x7 5, .ADD .x7 .x9 .x7]

def tailCode (level : Fin 16) : List Instr :=
  [.ADDI .x21 .x21 (BitVec.ofNat 12 (siblingWidth level.val)), .SRLI .x6 .x6 1]

def headPrefix (state : MachineState) (count : Nat) : MachineState :=
  (headCode.take count).foldl execInstrBr state

def tailPrefix (state : MachineState) (level : Fin 16) (count : Nat) : MachineState :=
  ((tailCode level).take count).foldl execInstrBr state

set_option maxRecDepth 4096 in
private theorem head_decode :
    ∀ (level : Fin 16) (i : Fin 3),
      (openingImage.code[siblingStart level+i.val]?).bind Opening.decodeBase =
        some (headCode[i.val]?.getD .EBREAK) := by decide

set_option maxRecDepth 4096 in
private theorem tail_decode :
    ∀ (level : Fin 16) (i : Fin 2),
      (openingImage.code[siblingEnd level+i.val]?).bind Opening.decodeBase =
        some ((tailCode level)[i.val]?.getD .EBREAK) := by decide

private theorem head_range : ∀ level : Fin 16, siblingStart level+3 ≤ 667 := by decide
private theorem tail_range : ∀ level : Fin 16, siblingEnd level+2 ≤ 667 := by decide

theorem execute_sibling_head (state : MachineState) (level : Fin 16)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*siblingStart level)) (fuel : Nat) (coins : Bool) :
    execute openingImage (3+fuel) state coins =
      (do let result ← execute openingImage fuel (headPrefix state 3) coins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := headPrefix state)
  intro i inside
  refine ⟨.base (headCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply packed_fetch_base _ (siblingStart level+i) _ (by have := head_range level; omega)
    · have offset : BitVec.ofNat 64 (4096+4*siblingStart level) + BitVec.ofNat 64 (4*i) =
          BitVec.ofNat 64 (4096+4*(siblingStart level+i)) := by rw [← BitVec.ofNat_add]; congr 1; omega
      rw [← offset]
      interval_cases i <;> simp [headPrefix, headCode, execInstrBr, pc, BitVec.add_assoc]
    · exact head_decode level ⟨i,inside⟩
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem execute_sibling_tail (state : MachineState) (level : Fin 16)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*siblingEnd level)) (fuel : Nat) (coins : Bool) :
    execute openingImage (2+fuel) state coins =
      (do let result ← execute openingImage fuel (tailPrefix state level 2) coins
          return result.charge 2 0) := by
  apply execute_unit_steps (states := tailPrefix state level)
  intro i inside
  refine ⟨.base ((tailCode level)[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply packed_fetch_base _ (siblingEnd level+i) _ (by have := tail_range level; omega)
    · have offset : BitVec.ofNat 64 (4096+4*siblingEnd level) + BitVec.ofNat 64 (4*i) =
          BitVec.ofNat 64 (4096+4*(siblingEnd level+i)) := by rw [← BitVec.ofNat_add]; congr 1; omega
      rw [← offset]
      interval_cases i <;> simp [tailPrefix, tailCode, execInstrBr, pc, BitVec.add_assoc]
    · exact tail_decode level ⟨i,inside⟩
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem sibling_head_post (state : MachineState) :
    let next := headPrefix state 3
    next.pc = state.pc+12#64 ∧ next.mem = state.mem ∧
      next.getReg .x7 = state.getReg .x9+((state.getReg .x6 ^^^ 1#64) <<< 5) ∧
      ∀ reg, reg ≠ .x7 → next.getReg reg = state.getReg reg := by
  simp [headPrefix, headCode, execInstrBr, signExtend12, BitVec.add_assoc]
  intro reg distinct
  simp [Ne.symm distinct]

theorem sibling_tail_post (state : MachineState) (level : Fin 16) :
    let next := tailPrefix state level 2
    next.pc = state.pc+8#64 ∧ next.mem = state.mem ∧
      next.getReg .x21 = state.getReg .x21 + BitVec.ofNat 64 (siblingWidth level.val) ∧
      next.getReg .x6 = state.getReg .x6 >>> 1 ∧
      ∀ reg, reg ≠ .x21 → reg ≠ .x6 → next.getReg reg = state.getReg reg := by
  by_cases first : level.val = 0 <;>
    simp [tailPrefix, tailCode, execInstrBr, siblingWidth, first, signExtend12, BitVec.add_assoc] <;>
    intro reg a b <;> simp [Ne.symm a, Ne.symm b]

end TwoPermutationPrototype.PackedOpening
