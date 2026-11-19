import CommitGolfCandidate.TwoPermutationCheckerCapHash

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64

attribute [local simp] MachineState.getReg_setPC Opening.getReg_setReg
@[local simp] private theorem pc_after (state : MachineState) (pc : Word) : (state.setPC pc).pc = pc := rfl

def frontierCode : List Instr :=
  [.SLLI .x7 .x6 5, .ADD .x7 .x25 .x7, .ADDI .x28 .x21 32, .BLTU .x22 .x28 172]

def frontierPrefix (state : MachineState) (count : Nat) : MachineState :=
  (frontierCode.take count).foldl execInstrBr state

theorem execute_frontier_prefix (state : MachineState) (pc : state.pc = 0x12b0) (fuel : Nat) :
    execute checkerImage (4+fuel) state false =
      (do let next ← execute checkerImage fuel (frontierPrefix state 4) false
          return next.charge 4 0) := by
  apply execute_unit_steps (states := frontierPrefix state)
  intro i bounded
  refine ⟨.base (frontierCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply checker_fetch _ (172+i) _ (by omega)
    · interval_cases i <;> simp [frontierPrefix, frontierCode, execInstrBr, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem frontier_prefix_post (state : MachineState) (pc : state.pc = 0x12b0) :
    let next := frontierPrefix state 4
    next.pc = (if state.getReg .x22 < state.getReg .x21+32#64 then 0x1368 else 0x12c0) ∧
    next.getReg .x7 = state.getReg .x25+(state.getReg .x6 <<< 5) ∧
    next.getReg .x28 = state.getReg .x21+32#64 ∧ next.mem = state.mem := by
  by_cases short : state.getReg .x22 < state.getReg .x21+32#64
  · have branch : (state.getReg .x22).ult (state.getReg .x21+32#64) = true := decide_eq_true short
    simp [frontierPrefix, frontierCode, execInstrBr, signExtend12, signExtend13, pc, short, branch]
    rfl
  · have branch : (state.getReg .x22).ult (state.getReg .x21+32#64) = false := decide_eq_false short
    simp [frontierPrefix, frontierCode, execInstrBr, signExtend12, signExtend13, pc, short, branch]
    rfl

theorem frontier_prefix_register (state : MachineState) (r : Reg) (dest : r ≠ .x7) (endPtr : r ≠ .x28) :
    (frontierPrefix state 4).getReg r = state.getReg r := by
  by_cases short : (state.getReg .x22).ult (state.getReg .x21+32#64)
  · simp [frontierPrefix, frontierCode, execInstrBr, signExtend12, Ne.symm dest, Ne.symm endPtr, short]
  · simp [frontierPrefix, frontierCode, execInstrBr, signExtend12, Ne.symm dest, Ne.symm endPtr, short]

def frontierFinish (state : MachineState) :=
  (state.setReg .x21 (state.getReg .x21+32#64)).setPC 0x12e4

theorem execute_frontier_finish (state : MachineState) (pc : state.pc = 0x12e0) (fuel : Nat) :
    execute checkerImage (1+fuel) state false =
      (do let result ← execute checkerImage fuel (frontierFinish state) false
          return result.charge 1 0) := by
  have fetched := checker_fetch state 184 (.ADDI .x21 .x21 32) (by decide) pc rfl
  have stepped : ordinaryStep state (.base (.ADDI .x21 .x21 32)) = some (frontierFinish state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, frontierFinish, pc]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

structure FrontierReady (state : MachineState) (node proof : Nat) where
  pc : state.pc = 0x12b0
  nodeReg : state.getReg .x6 = BitVec.ofNat 64 node
  capReg : state.getReg .x25 = 16384#64
  proofReg : state.getReg .x21 = wordAddress proof
  below : node < 512
  above : 4096 ≤ proof
  room : proof+4 ≤ 2^33

def frontierRead (state : MachineState) := frontierFinish (copied (frontierPrefix state 4) 176)

theorem frontier_copy_regs {state : MachineState} {node proof : Nat}
    (ready : FrontierReady state node proof) :
    let prepared := frontierPrefix state 4
    prepared.getReg .x21 = wordAddress proof ∧
    prepared.getReg .x7 = wordAddress (2048+4*node) := by
  refine ⟨(frontier_prefix_register state _ (by decide) (by decide)).trans ready.proofReg, ?_⟩
  obtain ⟨_, dst, _, _⟩ := frontier_prefix_post state ready.pc
  rw [dst, ready.capReg, ready.nodeReg, BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 16384 + BitVec.ofNat 64 node * BitVec.ofNat 64 32 = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, wordAddress]
  congr 1
  omega

theorem execute_frontier_read {state : MachineState} {node proof : Nat}
    (ready : FrontierReady state node proof) (fuel : Nat)
    (fits : ¬ state.getReg .x22 < state.getReg .x21+32#64) :
    execute checkerImage (13+fuel) state false =
      (do let next ← execute checkerImage fuel (frontierRead state) false
          return next.charge 13 0) := by
  let prepared := frontierPrefix state 4
  have pc : prepared.pc = 0x12c0 := by
    change (frontierPrefix state 4).pc = _
    rw [(frontier_prefix_post state ready.pc).1, ite_eq_right fits]
  obtain ⟨input, output⟩ := frontier_copy_regs ready
  have src (i : Fin 4) :
      accessValid (prepared.getReg (copySource 176)+BitVec.ofNat 64 (8*i.val)) 8 = true := by
    change accessValid (prepared.getReg .x21+BitVec.ofNat 64 (8*i.val)) 8 = true
    rw [input, word_offset]
    exact aligned_access _ (by have := ready.room; omega)
  have dst (i : Fin 4) :
      accessValid (prepared.getReg (copyTarget 176)+BitVec.ofNat 64 (copyOffset 176+8*i.val)) 8 = true := by
    rw [show copyOffset 176 = 0 from rfl, Nat.zero_add]
    change accessValid (prepared.getReg .x7+BitVec.ofNat 64 (8*i.val)) 8 = true
    rw [output, word_offset]
    exact aligned_access _ (by have := ready.below; omega)
  have nextPC : (copied prepared 176).pc = 0x12e0 := by rw [copied_pc, pc]; rfl
  rw [show 13+fuel = 4+(8+(1+fuel)) by omega, execute_frontier_prefix _ ready.pc,
    execute_copy prepared 176 (by unfold CopyBlock; decide) pc src dst, execute_frontier_finish _ nextPC]
  simp [frontierRead, Execution.charge, ← Nat.add_assoc]
  <;> rfl

theorem frontier_digest {state : MachineState} {node proof : Nat}
    (ready : FrontierReady state node proof) :
    capRootAt (frontierRead state) node = readBuffer state (8*proof) 32 := by
  have src := (frontier_copy_regs ready).1
  have dst := (frontier_copy_regs ready).2
  have room := ready.room
  have above := ready.above
  have below := ready.below
  change readBuffer (frontierRead state) (8*(2048+4*node)) 32 = _
  have saved : readBuffer (frontierRead state) (8*(2048+4*node)) 32 =
      readBuffer (copied (frontierPrefix state 4) 176) (8*(2048+4*node)) 32 :=
    read_digest_congr _ _ _ (by omega) (fun _ _ => rfl)
  rw [saved]
  rw [copied_digest _ 176 proof (2048+4*node) (by unfold CopyBlock; decide) src
    (by simpa [copyOffset, copyTarget, show BitVec.ofNat 64 0 = 0#64 from rfl] using dst)
    (by omega) (by omega) (Or.inr (by omega))]
  apply read_digest_congr _ _ _ (by omega)
  intro i _
  exact congrFun (frontier_prefix_post state ready.pc).2.2.2 _

end TwoPermutationPrototype.Checker
