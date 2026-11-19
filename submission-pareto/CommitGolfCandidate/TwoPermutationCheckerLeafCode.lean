import CommitGolfCandidate.TwoPermutationCheckerImage
import CommitGolfCandidate.TwoPermutationSyscall
import CommitGolfCandidate.TwoPermutationOpeningBlocks

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem

@[local simp] private theorem leaf_reg_set_pc (s : MachineState) (pc : Word) (reg : Reg) :
    (s.setPC pc).getReg reg = s.getReg reg := rfl

@[local simp] private theorem leaf_pc_set (s : MachineState) (pc : Word) :
    (s.setPC pc).pc = pc := rfl

def firstPreamble : List Instr :=
  [.SD .x10 .x28 0, .SD .x10 .x0 8, .SD .x10 .x0 16,
   .LD .x31 .x21 0, .SD .x10 .x31 24, .LD .x31 .x21 8, .SD .x10 .x31 32,
   .ADDI .x12 .x10 0]

def secondPreamble : List Instr :=
  [.ADDI .x10 .x10 96, .ADDI .x31 .x28 96, .SD .x10 .x31 0, .ADDI .x12 .x23 0]

def firstPrefix (state : MachineState) (count : Nat) : MachineState :=
  (firstPreamble.take count).foldl execInstrBr state

def secondPrefix (state : MachineState) (count : Nat) : MachineState :=
  (secondPreamble.take count).foldl execInstrBr state

theorem execute_first_prefix (state : MachineState) (pc : state.pc = 0x10e4) (fuel : Nat)
    (first : accessValid (state.getReg .x10) 8 = true)
    (next : accessValid (state.getReg .x10 + 8#64) 8 = true)
    (third : accessValid (state.getReg .x10 + 16#64) 8 = true)
    (fourth : accessValid (state.getReg .x10 + 24#64) 8 = true)
    (fifth : accessValid (state.getReg .x10 + 32#64) 8 = true)
    (nonce : accessValid (state.getReg .x21) 8 = true)
    (nonceTail : accessValid (state.getReg .x21 + 8#64) 8 = true) :
    execute checkerImage (8 + fuel) state false =
      (do let result ← execute checkerImage fuel (firstPrefix state 8) false
          return result.charge 8 0) := by
  apply execute_unit_steps (states := firstPrefix state)
  intro i bounded
  refine ⟨.base (firstPreamble[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply checker_fetch _ (57+i) _ (by omega)
    · interval_cases i <;> simp [firstPrefix, firstPreamble, execInstrBr, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;>
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, signExtend12,
        firstPrefix, firstPreamble, first, next, third, fourth, fifth, nonce, nonceTail] <;> assumption
  · interval_cases i <;> rfl

theorem execute_second_prefix (state : MachineState) (pc : state.pc = 0x1108) (fuel : Nat)
    (store : accessValid (state.getReg .x10 + 96#64) 8 = true) :
    execute checkerImage (4 + fuel) state false =
      (do let result ← execute checkerImage fuel (secondPrefix state 4) false
          return result.charge 4 0) := by
  apply execute_unit_steps (states := secondPrefix state)
  intro i bounded
  refine ⟨.base (secondPreamble[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply checker_fetch _ (66+i) _ (by omega)
    · interval_cases i <;> simp [secondPrefix, secondPreamble, execInstrBr, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;>
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, signExtend12,
        secondPrefix, secondPreamble, store] <;> assumption
  · interval_cases i <;> rfl

theorem checker_first_ecall (state : MachineState) (pc : state.pc = 0x1104) :
    fetch checkerImage state = some (.base .ECALL) :=
  checker_fetch state 65 .ECALL (by decide) pc rfl

theorem checker_second_ecall (state : MachineState) (pc : state.pc = 0x1118) :
    fetch checkerImage state = some (.base .ECALL) :=
  checker_fetch state 70 .ECALL (by decide) pc rfl

def checkerNonce (state : MachineState) : Words 2 := fun i =>
  if i.val = 0 then state.getMem (state.getReg .x21) else state.getMem (state.getReg .x21+8#64)

def firstHeaderMemory (state : MachineState) : MachineState :=
  let src := state.getReg .x10
  let nonce := checkerNonce state
  let tagged := state.setMem src (state.getReg .x28)
  let cleared := (tagged.setMem (src+8#64) 0).setMem (src+16#64) 0
  let salted := cleared.setMem (src+24#64) (nonce 0)
  salted.setMem (src+32#64) (nonce 1)

theorem first_prefix_post (state : MachineState)
    (disjoint : ∀ (i : Fin 2) (j : Fin 5), state.getReg .x21 + BitVec.ofNat 64 (8*i.val) ≠
      state.getReg .x10 + BitVec.ofNat 64 (8*j.val)) :
    let after := firstPrefix state 8
    after.mem = (firstHeaderMemory state).mem ∧ after.getReg .x10 = state.getReg .x10 ∧
    after.getReg .x12 = state.getReg .x10 ∧ after.pc = state.pc + 32 ∧
    after.getReg .x5 = state.getReg .x5 ∧ after.getReg .x11 = state.getReg .x11 ∧
    after.getReg .x13 = state.getReg .x13 := by
  have d0 : state.getReg .x21 ≠ state.getReg .x10 := by simpa using disjoint 0 0
  have d8 : state.getReg .x21 ≠ state.getReg .x10+8#64 := by simpa using disjoint 0 1
  have d16 : state.getReg .x21 ≠ state.getReg .x10+16#64 := by simpa using disjoint 0 2
  have e0 : state.getReg .x21+8#64 ≠ state.getReg .x10 := by simpa using disjoint 1 0
  have e8 : state.getReg .x21+8#64 ≠ state.getReg .x10+8#64 := disjoint 1 1
  have e16 : state.getReg .x21+8#64 ≠ state.getReg .x10+16#64 := disjoint 1 2
  have e24 : state.getReg .x21+8#64 ≠ state.getReg .x10+24#64 := disjoint 1 3
  simp [MachineState.getReg] at d0 d8 d16 e0 e8 e16 e24
  simp [firstPrefix, firstPreamble, firstHeaderMemory, checkerNonce, execInstrBr, signExtend12,
    MachineState.setPC, MachineState.setMem, MachineState.getMem, MachineState.getReg, MachineState.setReg,
    d0, d8, d16, e0, e8, e16, e24, show state.getReg .x0 = 0#64 from rfl, BitVec.add_assoc]
  <;> rfl

theorem second_prefix_post (state : MachineState) :
    let after := secondPrefix state 4
    let src := state.getReg .x10 + 96#64
    after.mem = (state.setMem src (state.getReg .x28+96#64)).mem ∧
    after.getReg .x10 = src ∧ after.getReg .x12 = state.getReg .x23 ∧ after.pc = state.pc + 16 ∧
    after.getReg .x5 = state.getReg .x5 ∧ after.getReg .x11 = state.getReg .x11 ∧
    after.getReg .x13 = state.getReg .x13 := by
  simp [secondPrefix, secondPreamble, execInstrBr, signExtend12, MachineState.setPC, MachineState.setMem,
    MachineState.getReg, MachineState.setReg, BitVec.add_assoc]
  <;> rfl

theorem first_prefix_register (state : MachineState) (reg : Reg)
    (a : reg ≠ .x12) (b : reg ≠ .x31) :
    (firstPrefix state 8).getReg reg = state.getReg reg := by
  simp [firstPrefix, firstPreamble, execInstrBr, Ne.symm a, Ne.symm b]

theorem second_prefix_register (state : MachineState) (reg : Reg)
    (a : reg ≠ .x10) (b : reg ≠ .x12) (c : reg ≠ .x31) :
    (secondPrefix state 4).getReg reg = state.getReg reg := by
  simp [secondPrefix, secondPreamble, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c]

end TwoPermutationPrototype.Checker
