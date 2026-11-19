import CommitGolfCandidate.TwoPermutationOpeningImage

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

theorem getReg_setMem (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl

theorem getReg_setReg (state : MachineState) (rd rs : Reg) (value : Word) :
    (state.setReg rd value).getReg rs =
      if rd = rs ∧ rd ≠ .x0 then value else state.getReg rs := by
  by_cases same : rd = rs
  · subst rs
    by_cases zero : rd = .x0
    · subst rd
      rfl
    · simp [zero, MachineState.getReg_setReg_eq]
  · simp [same, MachineState.getReg_setReg_ne]

private theorem offset0 : signExtend12 0 = 0 := by decide
private theorem offset8 : signExtend12 8 = 8 := by decide
private theorem offset16 : signExtend12 16 = 16 := by decide
private theorem offset24 : signExtend12 24 = 24 := by decide
private theorem offset32 : signExtend12 32 = 32 := by decide
private theorem offset1 : signExtend12 1 = 1 := by decide
private theorem offsetNeg1 : signExtend12 4095 = -1 := by decide

attribute [local simp] getReg_setMem getReg_setReg offset0 offset8 offset16 offset24
  offset32 offset1 offsetNeg1

def nonceSource (state : MachineState) : Word :=
  state.getReg .x22 + (state.getMem (state.getReg .x8) <<< 4)

def noncePrefix (state : MachineState) (count : Nat) : MachineState :=
  (nonceInstructions.take count).foldl execInstrBr state

/-- The ordinal index load, nonce copy, and lower-path initialization consume ten
one-cycle instructions in the concrete opening image. -/
theorem execute_nonce (state : MachineState) (pc : state.pc = 0x1034) (fuel : Nat)
    (allowCoins : Bool) (indexAccess : accessValid (state.getReg .x8) 8 = true)
    (sourceFirst : accessValid (nonceSource state) 8 = true)
    (sourceSecond : accessValid (nonceSource state + 8) 8 = true)
    (destinationFirst : accessValid (state.getReg .x21) 8 = true)
    (destinationSecond : accessValid (state.getReg .x21 + 8) 8 = true) :
    execute openingImage (10 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (noncePrefix state 10) allowCoins
          return result.charge 10 0) := by
  apply execute_unit_steps (states := noncePrefix state)
  intro i bounded
  refine ⟨.base (nonceInstructions[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply opening_fetch _ (13 + i) _ (by omega) _ (nonce_decode ⟨i, bounded⟩)
    interval_cases i <;>
      simp [noncePrefix, nonceInstructions, execInstrBr, MachineState.setPC, pc]
  · interval_cases i <;>
      simp [ordinaryStep, memoryArgumentsValid, memAccess, noncePrefix, nonceInstructions,
        execInstrBr, signExtend12] <;>
      assumption
  · interval_cases i <;> rfl

/-- The two stores copy the nonce words and touch no other word. The path starts
at the full heap leaf and the first digest is written immediately after the nonce. -/
theorem nonce_post (state : MachineState)
    (separate : nonceSource state + 8 ≠ state.getReg .x21) :
    let after := noncePrefix state 10
    let source := nonceSource state
    let dest := state.getReg .x21
    after.mem = ((state.setMem dest (state.getMem source)).setMem
      (dest + 8) (state.getMem (source + 8))).mem ∧
    after.getReg .x21 = dest + 16 ∧
    after.getReg .x6 = state.getMem (state.getReg .x8) + state.getReg .x19 ∧
    after.getReg .x29 = 16 ∧ after.pc = state.pc + 40 := by
  have second : state.getReg .x22 + (state.getMem (state.getReg .x8) <<< 4) + 8 ≠
      state.getReg .x21 := separate
  simp [noncePrefix, nonceInstructions, execInstrBr, nonceSource, signExtend12,
    MachineState.setMem, MachineState.setReg, MachineState.setPC, MachineState.getMem,
    MachineState.getReg, BitVec.add_assoc] at second ⊢
  simp [second]

/-- Reads after the nonce block agree with the incoming state off the two stores. -/
theorem nonce_frame (state : MachineState) (address : Word)
    (separate : nonceSource state + 8 ≠ state.getReg .x21)
    (outsideFirst : address ≠ state.getReg .x21)
    (outsideSecond : address ≠ state.getReg .x21 + 8) :
    (noncePrefix state 10).getMem address = state.getMem address := by
  simp only [MachineState.getMem, (nonce_post state separate).1]
  exact (MachineState.getMem_setMem_ne outsideSecond).trans
    (MachineState.getMem_setMem_ne outsideFirst)

end TwoPermutationPrototype.Opening
