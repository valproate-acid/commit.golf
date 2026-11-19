import CommitGolfCandidate.TwoPermutationCheckerCompression

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64

attribute [local simp] MachineState.getReg_setPC Opening.getReg_setReg

@[local simp] private theorem pc_after (state : MachineState) (pc : Word) : (state.setPC pc).pc = pc := rfl
@[local simp] private theorem reg_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

def capMarkAddress (state : MachineState) : Word := state.getReg .x26 + (state.getReg .x6 <<< 3)
def capMarkedWord (state : MachineState) : Word := state.getMem (capMarkAddress state)

def capLookupCode : List Instr :=
  [.SLLI .x7 .x6 3, .ADD .x7 .x26 .x7, .LD .x28 .x7 0]

def capLookupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capLookupCode.take count).foldl execInstrBr state

theorem execute_cap_lookup_prefix (state : MachineState) (pc : state.pc = 0x1294) (fuel : Nat)
    (markRead : accessValid (capMarkAddress state) 8 = true) :
    execute checkerImage (3+fuel) state false =
      (do let next ← execute checkerImage fuel (capLookupPrefix state 3) false
          return next.charge 3 0) := by
  have access : accessValid (state.getReg .x26+(state.getReg .x6 <<< 3)) 8 = true := markRead
  apply execute_unit_steps (states := capLookupPrefix state)
  intro i bound
  refine ⟨.base (capLookupCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply checker_fetch _ (165+i) _ (by omega)
    · interval_cases i <;> simp [capLookupPrefix, capLookupCode, execInstrBr, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;>
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
        capLookupPrefix, capLookupCode, access]
  · interval_cases i <;> rfl

theorem cap_lookup_prefix_mark (state : MachineState) :
    (capLookupPrefix state 3).getReg .x28 = capMarkedWord state := by
  simp [capLookupPrefix, capLookupCode, capMarkedWord, capMarkAddress, execInstrBr, signExtend12]

theorem cap_lookup_prefix_register (state : MachineState) (reg : Reg)
    (heap : reg ≠ .x7) (mark : reg ≠ .x28) :
    (capLookupPrefix state 3).getReg reg = state.getReg reg := by
  simp [capLookupPrefix, capLookupCode, execInstrBr, Ne.symm heap, Ne.symm mark]

def capLookup (state : MachineState) : MachineState :=
  let checked := capLookupPrefix state 3
  if capMarkedWord state = 0#64 then
    checked.setPC 0x12b0
  else if state.getReg .x27 ≤ state.getReg .x6 then
    checked.setPC 0x12e4
  else
    (checked.setReg .x6 (state.getReg .x6 <<< 1)).setPC 0x1294

def capLookupSteps (state : MachineState) : Nat :=
  if capMarkedWord state = 0#64 then 4 else if state.getReg .x27 ≤ state.getReg .x6 then 5 else 7

/-- DFS lookup branches to the frontier read, the marked-leaf return, or the
left child. The mark array is read once and no scratch memory is changed. -/
theorem execute_cap_lookup (state : MachineState) (pc : state.pc = 0x1294) (fuel : Nat)
    (markRead : accessValid (capMarkAddress state) 8 = true) :
    execute checkerImage (capLookupSteps state+fuel) state false =
      (do let next ← execute checkerImage fuel (capLookup state) false
          return next.charge (capLookupSteps state) 0) := by
  let checked := capLookupPrefix state 3
  have checkedPC : checked.pc = 0x12a0 := by
    simp [checked, capLookupPrefix, capLookupCode, execInstrBr, pc]
  have first : fetch checkerImage checked = some (.base (.BEQ .x28 .x0 16)) :=
    checker_fetch checked 168 _ (by decide) checkedPC rfl
  by_cases unmarked : capMarkedWord state = 0#64
  · have yes : ordinaryStep checked (.base (.BEQ .x28 .x0 16)) = some (checked.setPC 0x12b0) := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, checkedPC,
        show checked.getReg .x28 = capMarkedWord state from cap_lookup_prefix_mark state, unmarked]
    rw [capLookup, capLookupSteps, ite_eq_left unmarked, ite_eq_left unmarked,
      show 4+fuel = 3+(fuel+1) by omega, execute_cap_lookup_prefix _ pc _ markRead,
      execute_ordinary_step _ _ _ _ _ _ first yes]
    simp [Execution.charge, instructionCycles, checked, ← Nat.add_assoc]
  · let branched := checked.setPC 0x12a4
    have no : ordinaryStep checked (.base (.BEQ .x28 .x0 16)) = some branched := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, checkedPC, branched,
        show checked.getReg .x28 = capMarkedWord state from cap_lookup_prefix_mark state, unmarked]
    have second : fetch checkerImage branched = some (.base (.BGEU .x6 .x27 64)) :=
      checker_fetch branched 169 _ (by decide) rfl rfl
    have r6 : branched.getReg .x6 = state.getReg .x6 := cap_lookup_prefix_register state .x6 (by decide) (by decide)
    have r27 : branched.getReg .x27 = state.getReg .x27 := cap_lookup_prefix_register state .x27 (by decide) (by decide)
    by_cases leaf : state.getReg .x27 ≤ state.getReg .x6
    · have leafBit : (branched.getReg .x6).ult (branched.getReg .x27) = false := by
        rw [r6, r27]
        exact decide_eq_false (Nat.not_lt.mpr leaf)
      have yes : ordinaryStep branched (.base (.BGEU .x6 .x27 64)) = some (checked.setPC 0x12e4) := by
        simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
          leafBit, show branched.pc = 0x12a4 from rfl]
        rfl
      rw [capLookup, capLookupSteps, ite_eq_right unmarked, ite_eq_right unmarked,
        ite_eq_left leaf, ite_eq_left leaf, show 5+fuel = 3+((fuel+1)+1) by omega,
        execute_cap_lookup_prefix _ pc _ markRead,
        execute_ordinary_step _ _ _ _ _ _ first no, execute_ordinary_step _ _ _ _ _ _ second yes]
      simp [Execution.charge, instructionCycles, checked, ← Nat.add_assoc]
    · let beforeShift := checked.setPC 0x12a8
      let shifted := (checked.setReg .x6 (state.getReg .x6 <<< 1)).setPC 0x12ac
      have branchBit : (branched.getReg .x6).ult (branched.getReg .x27) = true := by
        rw [r6, r27]
        exact decide_eq_true (Nat.lt_of_not_ge leaf)
      have notLeaf : ordinaryStep branched (.base (.BGEU .x6 .x27 64)) = some beforeShift := by
        simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
          branchBit, show branched.pc = 0x12a4 from rfl]
        rfl
      have fShift : fetch checkerImage beforeShift = some (.base (.SLLI .x6 .x6 1)) :=
        checker_fetch beforeShift 170 _ (by decide) rfl rfl
      have sShift : ordinaryStep beforeShift (.base (.SLLI .x6 .x6 1)) = some shifted := by
        simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, beforeShift, shifted,
          show checked.getReg .x6 = state.getReg .x6 from r6]
        rfl
      have fJump : fetch checkerImage shifted = some (.base (.JAL .x0 2097128)) :=
        checker_fetch shifted 171 _ (by decide) rfl rfl
      have sJump : ordinaryStep shifted (.base (.JAL .x0 2097128)) =
          some ((checked.setReg .x6 (state.getReg .x6 <<< 1)).setPC 0x1294) := by
        simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21, shifted, MachineState.setReg]
        rfl
      rw [capLookup, capLookupSteps, ite_eq_right unmarked, ite_eq_right unmarked,
        ite_eq_right leaf, ite_eq_right leaf, show 7+fuel = 3+((((fuel+1)+1)+1)+1) by omega,
        execute_cap_lookup_prefix _ pc _ markRead,
        execute_ordinary_step _ _ _ _ _ _ first no, execute_ordinary_step _ _ _ _ _ _ second notLeaf,
        execute_ordinary_step _ _ _ _ _ _ fShift sShift, execute_ordinary_step _ _ _ _ _ _ fJump sJump]
      simp [Execution.charge, instructionCycles, checked, ← Nat.add_assoc]

theorem cap_lookup_mark_address (state : MachineState) (node : Nat)
    (nodeReg : state.getReg .x6 = BitVec.ofNat 64 node) (markReg : state.getReg .x26 = 4096#64) :
    capMarkAddress state = wordAddress (512+node) := by
  rw [capMarkAddress, nodeReg, markReg, BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 4096 + BitVec.ofNat 64 node * BitVec.ofNat 64 8 = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, wordAddress]
  congr 1
  omega

theorem cap_lookup_post (state : MachineState) :
    let next := capLookup state
    let unmarked := capMarkedWord state = 0#64
    let leaf := state.getReg .x27 ≤ state.getReg .x6
    next.pc = (if unmarked then 0x12b0 else if leaf then 0x12e4 else 0x1294) ∧
    next.getReg .x6 = (if unmarked ∨ leaf then state.getReg .x6 else state.getReg .x6 <<< 1) ∧
    next.mem = state.mem := by
  have old := cap_lookup_prefix_register state .x6 (by decide) (by decide)
  dsimp only
  by_cases mark : capMarkedWord state = 0#64
  · simp [capLookup, mark, old]
    rfl
  · by_cases leaf : state.getReg .x27 ≤ state.getReg .x6
    · simp [capLookup, mark, leaf, old]
      rfl
    · simp [capLookup, mark, leaf, old]
      rfl

theorem cap_lookup_register (state : MachineState) (reg : Reg) (node : reg ≠ .x6)
    (address : reg ≠ .x7) (mark : reg ≠ .x28) :
    (capLookup state).getReg reg = state.getReg reg := by
  unfold capLookup
  split
  · exact cap_lookup_prefix_register state reg address mark
  · split
    · exact cap_lookup_prefix_register state reg address mark
    · simp [Ne.symm node, cap_lookup_prefix_register state reg address mark]

end TwoPermutationPrototype.Checker
