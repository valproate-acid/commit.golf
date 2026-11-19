import CommitGolfCandidate.TwoPermutationCheckerCopy
import CommitGolfCandidate.TwoPermutationCheckerCompression
import CommitGolfCandidate.TwoPermutationCheckerRecordSetup

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp OracleSpec
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling

def lowerBranch (state : MachineState) : MachineState :=
  (state.setReg .x7 (state.getReg .x6 &&& 1)).setPC
    (if state.getReg .x6 &&& 1 = 0 then 0x117c else 0x1138)

theorem execute_lower_branch (state : MachineState) (pc : state.pc = 0x1130)
    (fuel : Nat) :
    execute checkerImage (2 + fuel) state false =
      (do let result ← execute checkerImage fuel (lowerBranch state) false
          return result.charge 2 0) := by
  let next := (state.setReg .x7 (state.getReg .x6 &&& 1)).setPC 0x1134
  have f0 : fetch checkerImage state = some (.base (.ANDI .x7 .x6 1)) := by
    apply checker_fetch _ 76 _ (by decide) pc; rfl
  have f1 : fetch checkerImage next = some (.base (.BEQ .x7 .x0 72)) := by
    apply checker_fetch _ 77 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ANDI .x7 .x6 1)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, next, pc]
  have s1 : ordinaryStep next (.base (.BEQ .x7 .x0 72)) = some (lowerBranch state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      next, lowerBranch, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 2 fuel]
  simp only [execute, f0, s0, f1, s1, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

private theorem execute_lower_jump (state : MachineState) (pc : state.pc = 0x1178)
    (fuel : Nat) :
    execute checkerImage (1 + fuel) state false =
      (do let result ← execute checkerImage fuel (state.setPC 0x11bc) false
          return result.charge 1 0) := by
  have fetched : fetch checkerImage state = some (.base (.JAL .x0 68)) := by
    apply checker_fetch _ 94 _ (by decide) pc; rfl
  have stepped : ordinaryStep state (.base (.JAL .x0 68)) = some (state.setPC 0x11bc) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21,
      MachineState.setReg, pc]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

def lowerNext (state : MachineState) : MachineState :=
  (((state.setReg .x21 (state.getReg .x21 + 32)).setReg .x6 (state.getReg .x6 >>> 1)).setReg
    .x29 (state.getReg .x29 - 1)).setPC (if state.getReg .x29 - 1 = 0 then 0x11d8 else 0x1130)

theorem execute_lower_next (state : MachineState) (pc : state.pc = 0x11c8)
    (fuel : Nat) :
    execute checkerImage (4 + fuel) state false =
      (do let result ← execute checkerImage fuel (lowerNext state) false
          return result.charge 4 0) := by
  let advanced := (state.setReg .x21 (state.getReg .x21 + 32)).setPC 0x11cc
  let shifted := (advanced.setReg .x6 (state.getReg .x6 >>> 1)).setPC 0x11d0
  let next := (shifted.setReg .x29 (state.getReg .x29 - 1)).setPC 0x11d4
  have f0 : fetch checkerImage state = some (.base (.ADDI .x21 .x21 32)) := by
    apply checker_fetch _ 114 _ (by decide) pc; rfl
  have f1 : fetch checkerImage advanced = some (.base (.SRLI .x6 .x6 1)) := by
    apply checker_fetch _ 115 _ (by decide) rfl; rfl
  have f2 : fetch checkerImage shifted = some (.base (.ADDI .x29 .x29 4095)) := by
    apply checker_fetch _ 116 _ (by decide) rfl; rfl
  have f3 : fetch checkerImage next = some (.base (.BNE .x29 .x0 8028)) := by
    apply checker_fetch _ 117 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x21 .x21 32)) = some advanced := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, advanced, pc]
  have s1 : ordinaryStep advanced (.base (.SRLI .x6 .x6 1)) = some shifted := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, advanced, shifted,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have s2 : ordinaryStep shifted (.base (.ADDI .x29 .x29 4095)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, advanced, shifted, next,
      MachineState.getReg, MachineState.setReg, MachineState.setPC, BitVec.sub_eq_add_neg]
  have s3 : ordinaryStep next (.base (.BNE .x29 .x0 8028)) = some (lowerNext state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      advanced, shifted, next, lowerNext, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 4 fuel]
  simp only [execute, f0, s0, f1, s1, f2, s2, f3, s3, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

def lowerPrepare (state : MachineState) : MachineState :=
  if state.getReg .x6 &&& 1 = 0 then
    copied (copied (lowerBranch state) 95) 103
  else
    (copied (copied (lowerBranch state) 78) 86).setPC 0x11bc

def lowerPreparationSteps (state : MachineState) : Nat := if state.getReg .x6 &&& 1 = 0 then 18 else 19

structure LowerReady (state : MachineState) (node proof : Nat) where
  pc : state.pc = 0x1130
  nodeReg : state.getReg .x6 = BitVec.ofNat 64 node
  proofReg : state.getReg .x21 = wordAddress proof
  digestReg : state.getReg .x23 = wordAddress 1536
  pairReg : state.getReg .x24 = wordAddress 1568
  selector : state.getReg .x5 = 0
  size : state.getReg .x11 = 64
  primitive : state.getReg .x13 = 0
  proofAbove : 4096 ≤ proof
  proofBound : proof + 4 ≤ 2^33

theorem lower_branch_register (state : MachineState) (reg : Reg) (notScratch : reg ≠ .x7) :
    (lowerBranch state).getReg reg = state.getReg reg := by
  simp only [lowerBranch, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notScratch)]

theorem lower_prepared_pc (state : MachineState) : (lowerPrepare state).pc = 0x11bc := by
  unfold lowerPrepare
  split
  · rw [copied_pc, copied_pc]
    change (if state.getReg .x6 &&& 1 = 0 then 0x117c else 0x1138) + 32 + 32 = 0x11bc
    simp_all
  · rfl

theorem lower_prepared_register (state : MachineState) (reg : Reg)
    (notTemp : reg ≠ .x31) (notScratch : reg ≠ .x7) :
    (lowerPrepare state).getReg reg = state.getReg reg := by
  unfold lowerPrepare
  split <;> simp [copied_register _ _ _ notTemp, lower_branch_register _ _ notScratch,
    MachineState.getReg_setPC]

private theorem branch_copied_register (state : MachineState) (start : Nat) (reg : Reg)
    (notTemp : reg ≠ .x31) (notScratch : reg ≠ .x7) :
    (copied (lowerBranch state) start).getReg reg = state.getReg reg :=
  (copied_register _ _ _ notTemp).trans (lower_branch_register _ _ notScratch)

private theorem access_word_offset (word offset : Nat) (bounded : word + offset < 2^33) :
    accessValid (wordAddress word + BitVec.ofNat 64 (8*offset)) 8 = true := by
  change accessValid (wordAddress word + wordAddress offset) 8 = true
  rw [← wordAddress_add]
  exact aligned_access _ bounded

private theorem proof_access {state : MachineState} {node proof : Nat}
    (ready : LowerReady state node proof) (i : Fin 4) (m : MachineState)
    (r : m.getReg .x21 = state.getReg .x21) :
    accessValid (m.getReg .x21 + BitVec.ofNat 64 (8*i.val)) 8 = true := by
  rw [r, ready.proofReg]
  exact access_word_offset _ _ (by have := ready.proofBound; omega)

private theorem digest_access {state : MachineState} {node proof : Nat}
    (ready : LowerReady state node proof) (i : Fin 4) (m : MachineState)
    (r : m.getReg .x23 = state.getReg .x23) :
    accessValid (m.getReg .x23 + BitVec.ofNat 64 (8*i.val)) 8 = true := by
  rw [r, ready.digestReg]
  exact access_word_offset _ _ (by omega)

private theorem pair_access {state : MachineState} {node proof : Nat}
    (ready : LowerReady state node proof) (i : Fin 4) (m : MachineState) (half : Nat)
    (bounded : half ≤ 4) (r : m.getReg .x24 = state.getReg .x24) :
    accessValid (m.getReg .x24 + BitVec.ofNat 64 (8*half+8*i.val)) 8 = true := by
  rw [r, ready.pairReg, ← Nat.mul_add]
  exact access_word_offset _ _ (by omega)

theorem execute_lower_prepare {state : MachineState} {node proof : Nat}
    (ready : LowerReady state node proof) (fuel : Nat) :
    execute checkerImage (lowerPreparationSteps state+fuel) state false =
      (do let result ← execute checkerImage fuel (lowerPrepare state) false
          return result.charge (lowerPreparationSteps state) 0) := by
  let branch := lowerBranch state
  by_cases even : state.getReg .x6 &&& 1 = 0
  · have pc₀ : branch.pc = 0x117c := if_pos even
    let middle := copied branch 95
    have pc₁ : middle.pc = 0x119c := by rw [copied_pc, pc₀]; rfl
    have first := execute_copy branch 95 (by unfold CopyBlock; decide) pc₀
      (fun i => digest_access ready i branch (lower_branch_register _ _ (by decide)))
      (fun i => pair_access ready i branch 0 (by decide) (lower_branch_register _ _ (by decide))) (8+fuel)
    have next := execute_copy middle 103 (by unfold CopyBlock; decide) pc₁
      (fun i => proof_access ready i middle (branch_copied_register _ _ _ (by decide) (by decide)))
      (fun i => pair_access ready i middle 4 (by decide) (branch_copied_register _ _ _ (by decide) (by decide))) fuel
    simp only [lowerPreparationSteps, lowerPrepare, even, if_true]
    rw [show 18+fuel = 2+(8+(8+fuel)) by omega, execute_lower_branch _ ready.pc, first, next]
    simp [Execution.charge, branch, middle, ← Nat.add_assoc]
  · have pc₀ : branch.pc = 0x1138 := if_neg even
    let middle := copied branch 78
    have pc₁ : middle.pc = 0x1158 := by rw [copied_pc, pc₀]; rfl
    have pc₂ : (copied middle 86).pc = 0x1178 := by rw [copied_pc, pc₁]; rfl
    have first := execute_copy branch 78 (by unfold CopyBlock; decide) pc₀
      (fun i => proof_access ready i branch (lower_branch_register _ _ (by decide)))
      (fun i => pair_access ready i branch 0 (by decide) (lower_branch_register _ _ (by decide))) (8+(1+fuel))
    have next := execute_copy middle 86 (by unfold CopyBlock; decide) pc₁
      (fun i => digest_access ready i middle (branch_copied_register _ _ _ (by decide) (by decide)))
      (fun i => pair_access ready i middle 4 (by decide) (branch_copied_register _ _ _ (by decide) (by decide))) (1+fuel)
    simp only [lowerPreparationSteps, lowerPrepare, even, if_false]
    rw [show 19+fuel = 2+(8+(8+(1+fuel))) by omega, execute_lower_branch _ ready.pc,
      first, next, execute_lower_jump _ pc₂]
    simp [Execution.charge, branch, middle, ← Nat.add_assoc]

def lowerCompressionState (state : MachineState) : MachineState :=
  ((state.setReg .x10 (state.getReg .x24)).setReg .x12 (state.getReg .x23)).setPC 0x11c4

theorem execute_lower_compression_setup (state : MachineState) (pc : state.pc = 0x11bc) (fuel : Nat) :
    execute checkerImage (2+fuel) state false =
      (do let result ← execute checkerImage fuel (lowerCompressionState state) false
          return result.charge 2 0) := by
  let middle := (state.setReg .x10 (state.getReg .x24)).setPC 0x11c0
  have f₀ : fetch checkerImage state = some (.base (.ADDI .x10 .x24 0)) :=
    checker_fetch state 111 _ (by decide) pc rfl
  have f₁ : fetch checkerImage middle = some (.base (.ADDI .x12 .x23 0)) :=
    checker_fetch middle 112 _ (by decide) rfl rfl
  have s₀ : ordinaryStep state (.base (.ADDI .x10 .x24 0)) = some middle := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, middle, pc]
  have s₁ : ordinaryStep middle (.base (.ADDI .x12 .x23 0)) = some (lowerCompressionState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, middle,
      lowerCompressionState, MachineState.getReg_setPC, Opening.getReg_setReg]
    rfl
  rw [Nat.add_comm 2 fuel]
  simp only [execute, f₀, f₁, s₀, s₁, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

attribute [local irreducible] execute readBuffer writeBits

def lowerReply (state : MachineState) (answer : BitVec 256) : MachineState :=
  lowerNext (writeBits (lowerCompressionState (lowerPrepare state)) (wordAddress 1536) answer)

def lowerQuery (state : MachineState) : OracleComp World MachineState := do
  let answer ← World.query (.inr (.inl (readBuffer (lowerCompressionState (lowerPrepare state)) 12544 64)))
  return lowerReply state answer

theorem execute_lower_level {state : MachineState} {node proof : Nat}
    (ready : LowerReady state node proof) (fuel : Nat) :
    execute checkerImage (lowerPreparationSteps state+7+fuel) state false =
      (do let next ← lowerQuery state
          let result ← execute checkerImage fuel next false
          return result.charge (lowerPreparationSteps state+14) 1) := by
  let setup := lowerPrepare state
  let atCall := lowerCompressionState setup
  have control (reg : Reg) (notIn : reg ≠ .x10) (notOut : reg ≠ .x12)
      (notTemp : reg ≠ .x31) (notScratch : reg ≠ .x7) :
      atCall.getReg reg = state.getReg reg := by
    simp [atCall, lowerCompressionState, MachineState.getReg_setPC, Opening.getReg_setReg,
      Ne.symm notIn, Ne.symm notOut, lower_prepared_register _ _ notTemp notScratch, setup]
  have source : atCall.getReg .x10 = wordAddress 1568 := by
    simpa [atCall, lowerCompressionState, MachineState.getReg_setPC, Opening.getReg_setReg, setup] using
      (lower_prepared_register state .x24 (by decide) (by decide)).trans ready.pairReg
  have dest : atCall.getReg .x12 = wordAddress 1536 := by
    simpa [atCall, lowerCompressionState, MachineState.getReg_setPC, Opening.getReg_setReg, setup] using
      (lower_prepared_register state .x23 (by decide) (by decide)).trans ready.digestReg
  have fetched : fetch checkerImage atCall = some (.base .ECALL) :=
    checker_fetch atCall 113 _ (by decide) rfl rfl
  have call := execute_compression_call (4+fuel) atCall 1568 1536 (by decide) (by decide)
    source dest
    ((control _ (by decide) (by decide) (by decide) (by decide)).trans ready.selector)
    ((control _ (by decide) (by decide) (by decide) (by decide)).trans ready.size)
    ((control _ (by decide) (by decide) (by decide) (by decide)).trans ready.primitive)
    fetched
  rw [show lowerPreparationSteps state+7+fuel = lowerPreparationSteps state+(2+((4+fuel)+1)) by omega,
    execute_lower_prepare ready, execute_lower_compression_setup _ (lower_prepared_pc state)]
  change (do
    let result ← (do
      let inner ← execute checkerImage (4+fuel+1) atCall false
      return inner.charge 2 0)
    return result.charge (lowerPreparationSteps state) 0) = _
  rw [call]
  simp only [lowerQuery, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro reply _
  change BitVec 256 at reply
  have afterPC : (writeBits atCall (wordAddress 1536) reply).pc = 0x11c8 := by
    unfold writeBits
    change atCall.pc + 4 = _
    rfl
  erw [execute_lower_next _ afterPC]
  simp [lowerReply, atCall, setup, Execution.charge, ← Nat.add_assoc, Nat.add_comm]

end TwoPermutationPrototype.Checker
