import CommitGolfCandidate.TwoPermutationCheckerLeafRun

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64

attribute [local simp] Opening.getReg_setMem Opening.getReg_setReg MachineState.getReg_setPC

@[local simp] private theorem setup_pc_set (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

private theorem word_shift (value : Nat) :
    (BitVec.ofNat 64 value <<< 8) = BitVec.ofNat 64 (256*value) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 value * BitVec.ofNat 64 256 = _
  rw [← BitVec.ofNat_mul, Nat.mul_comm value]

def beginRecordCode : List Instr :=
  [.LD .x6 .x8 0, .SLLI .x28 .x6 8, .ADD .x28 .x3 .x28, .ADDI .x10 .x19 0,
   .ADDI .x11 .x0 200, .ADDI .x13 .x0 1]

def beginRecord (state : MachineState) (count : Nat) : MachineState :=
  (beginRecordCode.take count).foldl execInstrBr state

theorem execute_record_setup (state : MachineState) (pc : state.pc = 0x10cc) (fuel : Nat)
    (index : accessValid (state.getReg .x8) 8 = true) :
    execute checkerImage (6+fuel) state false =
      (do let result ← execute checkerImage fuel (beginRecord state 6) false
          return result.charge 6 0) := by
  apply execute_unit_steps (states := beginRecord state)
  intro i bounded
  refine ⟨.base (beginRecordCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply checker_fetch _ (51+i) _ (by omega)
    · interval_cases i <;> simp [beginRecord, beginRecordCode, execInstrBr, MachineState.setPC, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> simp [ordinaryStep, memoryArgumentsValid, memAccess, beginRecord,
      beginRecordCode, signExtend12, index] <;> assumption
  · interval_cases i <;> rfl

theorem record_setup_post (state : MachineState) :
    let next := beginRecord state 6
    next.getReg .x6 = state.getMem (state.getReg .x8) ∧
    next.getReg .x28 = state.getReg .x3 + (state.getMem (state.getReg .x8) <<< 8) ∧
    next.getReg .x10 = state.getReg .x19 ∧
    next.getReg .x11 = 200 ∧ next.getReg .x13 = 1 ∧ next.pc = state.pc+24 := by
  simp [beginRecord, beginRecordCode, execInstrBr, signExtend12, BitVec.add_assoc]
  <;> rfl

theorem record_setup_register (state : MachineState) (reg : Reg)
    (noIndex : reg ≠ .x6) (noTag : reg ≠ .x28) (noInput : reg ≠ .x10)
    (noSize : reg ≠ .x11) (noKind : reg ≠ .x13) :
    (beginRecord state 6).getReg reg = state.getReg reg := by
  simp [beginRecord, beginRecordCode, execInstrBr,
    Ne.symm noIndex, Ne.symm noTag, Ne.symm noInput, Ne.symm noSize, Ne.symm noKind]

theorem record_setup_mem (state : MachineState) : (beginRecord state 6).mem = state.mem := by
  rfl

theorem record_setup_ready (state : MachineState) (src nonce : Nat) (index : Index)
    (pc : state.pc = 0x10cc) (ordinal : state.getMem (state.getReg .x8) = BitVec.ofNat 64 index.val)
    (tagBase : state.getReg .x3 = 4056#64) (source : state.getReg .x19 = wordAddress src)
    (proof : state.getReg .x21 = wordAddress nonce) (dest : state.getReg .x23 = wordAddress 1536)
    (selector : state.getReg .x5 = 0) (separate : src+37 ≤ nonce) (bound : nonce+2 ≤ 2^33) :
    LeafReady (beginRecord state 6) src nonce index := by
  obtain ⟨_, tag, input, size, kind, endPC⟩ := record_setup_post state
  have reg (r : Reg) (h6 : r ≠ .x6) (h28 : r ≠ .x28) (h10 : r ≠ .x10) (h11 : r ≠ .x11)
      (h13 : r ≠ .x13) : (beginRecord state 6).getReg r = state.getReg r :=
    record_setup_register state r h6 h28 h10 h11 h13
  refine ⟨?_, input.trans source, ?_, ?_, ?_, ?_, size, kind, separate, bound⟩
  · rw [endPC, pc]; rfl
  · rw [reg _ (by decide) (by decide) (by decide) (by decide) (by decide), proof]
  · rw [reg _ (by decide) (by decide) (by decide) (by decide) (by decide), dest]
  · rw [tag, tagBase, ordinal, word_shift, firstTag]
    change BitVec.ofNat 64 4056 + BitVec.ofNat 64 (256*index.val) = _
    rw [← BitVec.ofNat_add]
  · rw [reg _ (by decide) (by decide) (by decide) (by decide) (by decide), selector]

def beginLowerCode : List Instr :=
  [.ADDI .x21 .x21 16, .ADD .x6 .x6 .x20, .ADDI .x11 .x0 64, .ADDI .x13 .x0 0, .ADDI .x29 .x0 16]

def beginLower (state : MachineState) (count : Nat) : MachineState :=
  (beginLowerCode.take count).foldl execInstrBr state

theorem execute_lower_setup (state : MachineState) (pc : state.pc = 0x111c) (fuel : Nat) :
    execute checkerImage (5+fuel) state false =
      (do let result ← execute checkerImage fuel (beginLower state 5) false
          return result.charge 5 0) := by
  apply execute_unit_steps (states := beginLower state)
  intro i bounded
  refine ⟨.base (beginLowerCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply checker_fetch _ (71+i) _ (by omega)
    · interval_cases i <;> simp [beginLower, beginLowerCode, execInstrBr, MachineState.setPC, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem lower_setup_post (state : MachineState) :
    let next := beginLower state 5
    next.getReg .x21 = state.getReg .x21+16 ∧
    next.getReg .x6 = state.getReg .x6+state.getReg .x20 ∧
    next.getReg .x11 = 64 ∧ next.getReg .x13 = 0 ∧
    next.getReg .x29 = 16 ∧ next.pc = state.pc+20 := by
  simp [beginLower, beginLowerCode, execInstrBr, signExtend12, BitVec.add_assoc]
  <;> rfl

theorem lower_setup_register (state : MachineState) (reg : Reg)
    (noPointer : reg ≠ .x21) (noNode : reg ≠ .x6) (noSize : reg ≠ .x11)
    (noKind : reg ≠ .x13) (noCounter : reg ≠ .x29) :
    (beginLower state 5).getReg reg = state.getReg reg := by
  simp [beginLower, beginLowerCode, execInstrBr,
    Ne.symm noPointer, Ne.symm noNode, Ne.symm noSize, Ne.symm noKind, Ne.symm noCounter]

theorem lower_setup_mem (state : MachineState) : (beginLower state 5).mem = state.mem := by
  rfl

end TwoPermutationPrototype.Checker
