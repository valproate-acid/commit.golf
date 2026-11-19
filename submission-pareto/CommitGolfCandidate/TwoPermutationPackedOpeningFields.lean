import CommitGolfCandidate.TwoPermutationPackedOpeningImage
import CommitGolfCandidate.TwoPermutationOpeningBlocks

namespace TwoPermutationPrototype.PackedOpening
set_option maxRecDepth 4096
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

@[local simp] private theorem mem_set_register (state : MachineState) (reg : Reg) (word : Word) :
    (state.setReg reg word).mem = state.mem := by cases reg <;> rfl

@[local simp] private theorem mem_set_pc (state : MachineState) (pc : Word) :
    (state.setPC pc).mem = state.mem := rfl

attribute [local simp] Opening.getReg_setReg MachineState.getReg_setPC

@[local simp] private theorem pc_set (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

def nonceSetupCode : List Instr := [.LD .x6 .x8 0, .SLLI .x7 .x6 4, .ADD .x7 .x22 .x7]

def nonceAdvanceCode : List Instr := [.ADDI .x21 .x21 16, .ADD .x6 .x6 .x19]

def capSourceCode : List Instr := [.SLLI .x7 .x6 5, .ADD .x7 .x25 .x7]

def capAdvanceCode : List Instr := [.ADDI .x21 .x21 30]

private def execPrefix (code : List Instr) (state : MachineState) (count : Nat) : MachineState :=
  (code.take count).foldl execInstrBr state

def nonceSetup (state : MachineState) := execPrefix nonceSetupCode state 3

def nonceAdvance (state : MachineState) := execPrefix nonceAdvanceCode state 2

def capSource (state : MachineState) := execPrefix capSourceCode state 2

def capAdvance (state : MachineState) := execPrefix capAdvanceCode state 1

theorem execute_nonce_setup (state : MachineState) (pc : state.pc = 0x1034)
    (readable : accessValid (state.getReg .x8) 8 = true) (fuel : Nat) (coins : Bool) :
    execute openingImage (3+fuel) state coins =
      (do let result ← execute openingImage fuel (nonceSetup state) coins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := execPrefix nonceSetupCode state)
  intro i inside
  refine ⟨.base (nonceSetupCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply packed_fetch_base _ (13+i) _ (by omega)
    · interval_cases i <;> simp [execPrefix, nonceSetupCode, execInstrBr, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;>
      simp [execPrefix, nonceSetupCode, ordinaryStep, memoryArgumentsValid, memAccess, signExtend12, readable] <;> rfl
  · interval_cases i <;> rfl

theorem execute_nonce_advance (state : MachineState) (pc : state.pc = 0x1080) (fuel : Nat) (coins : Bool) :
    execute openingImage (2+fuel) state coins =
      (do let result ← execute openingImage fuel (nonceAdvance state) coins
          return result.charge 2 0) := by
  apply execute_unit_steps (states := execPrefix nonceAdvanceCode state)
  intro i inside
  refine ⟨.base (nonceAdvanceCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply packed_fetch_base _ (32+i) _ (by omega)
    · interval_cases i <;> simp [execPrefix, nonceAdvanceCode, execInstrBr, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem execute_cap_source (state : MachineState) (pc : state.pc = 0x19b8) (fuel : Nat) (coins : Bool) :
    execute openingImage (2+fuel) state coins =
      (do let result ← execute openingImage fuel (capSource state) coins
          return result.charge 2 0) := by
  apply execute_unit_steps (states := execPrefix capSourceCode state)
  intro i inside
  refine ⟨.base (capSourceCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply packed_fetch_base _ (622+i) _ (by omega)
    · interval_cases i <;> simp [execPrefix, capSourceCode, execInstrBr, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem execute_cap_advance (state : MachineState) (pc : state.pc = 0x1a38) (fuel : Nat) (coins : Bool) :
    execute openingImage (1+fuel) state coins =
      (do let result ← execute openingImage fuel (capAdvance state) coins
          return result.charge 1 0) := by
  have fetched := packed_fetch_base state 654 (.ADDI .x21 .x21 30) (by decide) pc rfl
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched (show ordinaryStep state _ = _ from rfl)]
  rfl

theorem nonce_setup_post (state : MachineState) :
    let next := nonceSetup state
    next.pc = state.pc+12#64 ∧ next.mem = state.mem ∧
      next.getReg .x7 = Opening.nonceSource state ∧ next.getReg .x6 = state.getMem (state.getReg .x8) ∧
      ∀ r, r ≠ .x6 → r ≠ .x7 → next.getReg r = state.getReg r := by
  simp [nonceSetup, execPrefix, nonceSetupCode, execInstrBr, signExtend12, Opening.nonceSource, BitVec.add_assoc]
  intro r a b
  simp [Ne.symm a, Ne.symm b]

theorem nonce_advance_post (state : MachineState) :
    let next := nonceAdvance state
    next.pc = state.pc+8#64 ∧ next.mem = state.mem ∧
      next.getReg .x21 = state.getReg .x21+16#64 ∧ next.getReg .x6 = state.getReg .x6+state.getReg .x19 ∧
      ∀ r, r ≠ .x21 → r ≠ .x6 → next.getReg r = state.getReg r := by
  simp [nonceAdvance, execPrefix, nonceAdvanceCode, execInstrBr, signExtend12, BitVec.add_assoc]
  intro r a b
  simp [Ne.symm a, Ne.symm b]

theorem cap_source_post (state : MachineState) :
    let next := capSource state
    next.pc = state.pc+8#64 ∧ next.mem = state.mem ∧
      next.getReg .x7 = state.getReg .x25+(state.getReg .x6 <<< 5) ∧
      ∀ r, r ≠ .x7 → next.getReg r = state.getReg r := by
  simp [capSource, execPrefix, capSourceCode, execInstrBr, BitVec.add_assoc]
  intro r a
  simp [Ne.symm a]

theorem cap_advance_post (state : MachineState) :
    let next := capAdvance state
    next.pc = state.pc+4#64 ∧ next.mem = state.mem ∧
      next.getReg .x21 = state.getReg .x21+30#64 ∧
      ∀ r, r ≠ .x21 → next.getReg r = state.getReg r := by
  simp [capAdvance, execPrefix, capAdvanceCode, execInstrBr, signExtend12]
  intro r a
  simp [Ne.symm a]

end TwoPermutationPrototype.PackedOpening
