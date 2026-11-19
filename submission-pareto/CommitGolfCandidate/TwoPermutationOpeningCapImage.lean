import CommitGolfCandidate.TwoPermutationOpeningBlocks

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

def capMarkInstructions : List Instr :=
  [.ADDI .x6 .x0 255,
   .SLLI .x7 .x6 4, .ADD .x7 .x26 .x7, .LD .x28 .x7 0, .LD .x29 .x7 8,
   .OR .x28 .x28 .x29, .SLLI .x7 .x6 3, .ADD .x7 .x26 .x7, .SD .x7 .x28 0,
   .ADDI .x6 .x6 4095, .BNE .x6 .x0 8156]

def capWalkInstructions : List Instr :=
  [.ADDI .x6 .x0 1,
   .SLLI .x7 .x6 3, .ADD .x7 .x26 .x7, .LD .x28 .x7 0, .BEQ .x28 .x0 16,
   .BGEU .x6 .x27 56, .SLLI .x6 .x6 1, .JAL .x0 2097128,
   .SLLI .x7 .x6 5, .ADD .x7 .x25 .x7,
   .LD .x31 .x7 0, .SD .x21 .x31 0, .LD .x31 .x7 8, .SD .x21 .x31 8,
   .LD .x31 .x7 16, .SD .x21 .x31 16, .LD .x31 .x7 24, .SD .x21 .x31 24,
   .ADDI .x21 .x21 32,
   .ADDI .x7 .x0 1, .BEQ .x6 .x7 28, .ANDI .x7 .x6 1, .BEQ .x7 .x0 12,
   .SRLI .x6 .x6 1, .JAL .x0 2097132, .ADDI .x6 .x6 1, .JAL .x0 2097052]

def exitInstructions : List Instr :=
  [.SUB .x11 .x21 .x20, .ADDI .x5 .x0 1, .ADDI .x10 .x0 0, .ECALL]

theorem cap_suffix_decoded :
    ((openingImage.code.drop 44).map decodeBase) =
      ((capMarkInstructions ++ capWalkInstructions ++ exitInstructions).map some) := by
  decide

attribute [local simp] getReg_setReg getReg_setMem

def exitPrefix (state : MachineState) (count : Nat) : MachineState :=
  (exitInstructions.take count).foldl execInstrBr state

/-- The common return block returns the final proof pointer minus its start. -/
theorem execute_exit (state : MachineState) (pc : state.pc = 0x1148) (fuel : Nat)
    (allowCoins : Bool) :
    execute openingImage (4 + fuel) state allowCoins =
      pure ⟨.success, exitPrefix state 3, 4, 0⟩ := by
  have ranPrefix : execute openingImage (3 + (fuel + 1)) state allowCoins =
      (do let result ← execute openingImage (fuel + 1) (exitPrefix state 3) allowCoins
          return result.charge 3 0) := by
    apply execute_unit_steps (states := exitPrefix state)
    intro i bounded
    refine ⟨.base ((exitInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply opening_fetch _ (82 + i) _ (by omega)
      · interval_cases i <;> simp [exitPrefix, exitInstructions, execInstrBr, MachineState.setPC, pc]
      · interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have halted : fetch openingImage (exitPrefix state 3) = some (.base .ECALL) := by
    apply opening_fetch _ 85 _ (by decide)
    · simp [exitPrefix, exitInstructions, execInstrBr, MachineState.setPC, pc]
    · rfl
  have haltFlag : (exitPrefix state 3).getReg .x5 = 1 := by
    simp [exitPrefix, exitInstructions, execInstrBr, signExtend12,
      show state.getReg .x0 = 0 from rfl]
  have successFlag : (exitPrefix state 3).getReg .x10 = 0 := by
    simp [exitPrefix, exitInstructions, execInstrBr, signExtend12,
      show state.getReg .x0 = 0 from rfl]
  rw [show 4 + fuel = 3 + (fuel + 1) by omega, ranPrefix]
  simp [execute, halted, haltFlag, successFlag, Execution.charge]

theorem exit_register (state : MachineState) :
    (exitPrefix state 3).getReg .x11 = state.getReg .x21 - state.getReg .x20 := by
  simp [exitPrefix, exitInstructions, execInstrBr]

theorem exit_memory (state : MachineState) : (exitPrefix state 3).mem = state.mem := rfl

/-- The cap occupancy array begins zero in the trusted ABI before any record. -/
theorem initial_mark_word (s : Submission) (layout : OpeningLayout s)
    (image : s.image .opening = openingImage) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) (node : Nat) (bounded : node < 512) :
    (s.initialState .opening (trapdoor, positions)).getMem
      (BitVec.ofNat 64 (markBase + 8 * node)) = 0 := by
  erw [initial_input_word s .opening (trapdoor, positions) _ (by
    unfold markBase
    omega)]
  have zero (j : Nat) (hj : j < 8) :
      inputByte s .opening (trapdoor, positions) (markBase + 8 * node + j) = 0 := by
    have before : ¬trapdoorBase ≤ markBase + 8 * node + j := by
      norm_num [markBase, trapdoorBase, LENGTH, LOG_LENGTH]
      omega
    have beforeIndices : ¬indicesBase ≤ markBase + 8 * node + j := by
      unfold indicesBase
      omega
    have beforeData : ¬dataBase openingImage ≤ markBase + 8 * node + j := by
      norm_num [dataBase, MEMORY_BYTES, openingImage, markBase]
      omega
    simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, positionsBuffer,
      layout.trapdoor, layout.indices, before, beforeIndices, false_and, decide_false,
      List.find?_nil, image, beforeData, ite_false]
  have total : (∑ j ∈ Finset.range 8,
      (inputByte s .opening (trapdoor, positions) (markBase + 8 * node + j)).toNat *
        2 ^ (8 * j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [zero j (Finset.mem_range.mp hj)]
    simp
  rw [total]
  rfl

end TwoPermutationPrototype.Opening
