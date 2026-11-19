import CommitGolfCandidate.QuadOpeningRecord

/-! The whole penta opening run: setup, all records, exit. -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open QOpening (OpeningLayout trapdoorBase proofBase nonceBase indicesBase)

attribute [local simp] QOpening.getReg_setReg MachineState.getReg_setPC

@[local simp] private theorem reg_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

structure OpeningABI (s : Submission) extends OpeningLayout s where
  image : s.image .opening = openingImage
  capacity : PENTA_PROOF_CAPACITY ≤ s.sizes.proof
  fuel : 17179934720 ≤ s.steps .opening

def proofLength (positions : Positions) : Nat := 1424*positions.card

def scheduledSteps (positions : Positions) : Nat :=
  if positions.card = 0 then 6 else 15+517*positions.card

def scheduledCycles (positions : Positions) : Nat :=
  if positions.card = 0 then 6 else 15+583*positions.card

structure OpenPhysical (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (result : Execution) : Prop where
  success : result.exit = .success
  length : (result.state.getReg .x11).toNat = proofLength positions
  noCalls : result.oracleCalls = 0
  cycles : result.cycles = scheduledCycles positions
  output : Inv (s.initialState .opening (trapdoor, positions)) result.state (wordSource positions)
    (178*positions.card)

theorem beq_shape (state : MachineState) (r₁ r₂ : Reg) (imm : BitVec 13) :
    execInstrBr state (.BEQ r₁ r₂ imm) =
      state.setPC (if state.getReg r₁ == state.getReg r₂ then state.pc + signExtend13 imm else state.pc + 4) := by
  simp only [execInstrBr]
  split <;> rfl

set_option maxRecDepth 100000 in
theorem setup_codes :
    CodeAt 0 [.ADDI .x21 .x15 0] ∧ program[1]? = some (.BEQ .x16 .x0 612) ∧
    CodeAt 2 [.ADDI .x8 .x13 0, .ADDI .x9 .x12 0, .ADDI .x18 .x16 0, .LUI .x22 442369, .ADD .x22 .x9 .x22,
      .ADDI .x19 .x0 5, .ADDI .x23 .x0 368, .LUI .x26 1, .ADDI .x26 .x26 636] ∧
    CodeAt 154 [.SUB .x11 .x21 .x15, .ADDI .x5 .x0 1, .ADDI .x10 .x0 0] ∧ program[157]? = some .ECALL := by
  decide +kernel

def setupHead (state : MachineState) : MachineState :=
  ([.ADDI .x21 .x15 0] : List Instr).foldl execInstrBr state

def setupBranch (state : MachineState) : MachineState :=
  execInstrBr (setupHead state) (.BEQ .x16 .x0 612)

def setupRun (state : MachineState) : MachineState :=
  ([.ADDI .x8 .x13 0, .ADDI .x9 .x12 0, .ADDI .x18 .x16 0, .LUI .x22 442369, .ADD .x22 .x9 .x22,
    .ADDI .x19 .x0 5, .ADDI .x23 .x0 368, .LUI .x26 1, .ADDI .x26 .x26 636] : List Instr).foldl execInstrBr (setupBranch state)

def exitRun (state : MachineState) : MachineState :=
  ([.SUB .x11 .x21 .x15, .ADDI .x5 .x0 1, .ADDI .x10 .x0 0] : List Instr).foldl execInstrBr state

theorem execute_exit (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*154)) (fuel : Nat)
    (coins : Bool) :
    execute openingImage (4+fuel) state coins = pure ⟨.success, exitRun state, 4, 0⟩ := by
  obtain ⟨_, _, _, c₄, c₅⟩ := setup_codes
  have pure₀ : ([.SUB .x11 .x21 .x15, .ADDI .x5 .x0 1, .ADDI .x10 .x0 0] : List Instr).all pureOp = true := rfl
  have run : Runs state (exitRun state) 3 3 :=
    (runs_pure _ 154 state c₄ pc pure₀).cast rfl (by simp [cost, instructionCycles])
  have pc₃ : (exitRun state).pc = BitVec.ofNat 64 (4096+4*157) := by
    rw [exitRun, pure_pc _ _ pure₀, pc, pc_offset]; rfl
  have halted := fetch_program (exitRun state) 157 .ECALL c₅ pc₃
  have haltFlag : (exitRun state).getReg .x5 = 1 := by simp [exitRun, execInstrBr, signExtend12]
  have successFlag : (exitRun state).getReg .x10 = 0 := by simp [exitRun, execInstrBr, signExtend12]
  rw [show 4+fuel = 3+(fuel+1) by omega, run (fuel+1) coins]
  simp [execute, halted, haltFlag, successFlag, Execution.charge]

theorem exit_length (state : MachineState) :
    (exitRun state).getReg .x11 = state.getReg .x21 - state.getReg .x15 := by
  simp [exitRun, execInstrBr]

theorem exit_memory (state : MachineState) : (exitRun state).mem = state.mem :=
  pure_mem _ _ rfl

theorem initial_registers (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) :
    let init := s.initialState .opening (trapdoor, positions)
    init.pc = BitVec.ofNat 64 4096 ∧ init.getReg .x12 = BitVec.ofNat 64 trapdoorBase ∧
      init.getReg .x13 = BitVec.ofNat 64 indicesBase ∧ init.getReg .x15 = BitVec.ofNat 64 proofBase ∧
      init.getReg .x16 = BitVec.ofNat 64 positions.card :=
  ⟨rfl, congrArg (BitVec.ofNat 64) layout.trapdoor, congrArg (BitVec.ofNat 64) layout.indices,
    congrArg (BitVec.ofNat 64) layout.proof, rfl⟩

theorem setup_head (state : MachineState) (pc : state.pc = BitVec.ofNat 64 4096) :
    Runs state (setupHead state) 1 1 ∧ (setupHead state).pc = BitVec.ofNat 64 (4096+4*1) ∧
      (setupHead state).mem = state.mem ∧ (setupHead state).getReg .x15 = state.getReg .x15 ∧
      (setupHead state).getReg .x21 = state.getReg .x15 ∧
      ∀ r, r ≠ .x15 → r ≠ .x21 → (setupHead state).getReg r = state.getReg r := by
  obtain ⟨c₁, _, _, _, _⟩ := setup_codes
  have pure₀ : ([.ADDI .x21 .x15 0] : List Instr).all pureOp = true := rfl
  refine ⟨runs_pure _ 0 state c₁ pc pure₀, ?_, pure_mem _ _ pure₀, ?_, ?_, ?_⟩
  · rw [setupHead, pure_pc _ _ pure₀, pc]; rfl
  · simp [setupHead, execInstrBr, signExtend12]
  · simp [setupHead, execInstrBr, signExtend12]
  · intro r a b
    simp [setupHead, execInstrBr, Ne.symm a, Ne.symm b]

theorem setup_branch (state : MachineState) (pc : (setupHead state).pc = BitVec.ofNat 64 (4096+4*1)) :
    Runs (setupHead state) (setupBranch state) 1 1 ∧
      (setupBranch state).pc = (if (setupHead state).getReg .x16 = 0#64 then BitVec.ofNat 64 (4096+4*154)
        else BitVec.ofNat 64 (4096+4*2)) ∧
      (setupBranch state).mem = (setupHead state).mem ∧
      ∀ r, (setupBranch state).getReg r = (setupHead state).getReg r := by
  obtain ⟨_, c₂, _, _, _⟩ := setup_codes
  have shape := beq_shape (setupHead state) .x16 .x0 612
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro fuel coins
    rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ (fetch_program _ 1 _ c₂ pc) rfl]
    rfl
  · rw [setupBranch, shape, set_pc_pc, pc, reg_zero]
    by_cases zero : (setupHead state).getReg .x16 = 0#64
    · simp [zero] <;> decide
    · simp [zero] <;> decide
  · rw [setupBranch, shape]; rfl
  · intro r
    rw [setupBranch, shape, MachineState.getReg_setPC]

theorem lui_salts : ((BitVec.ofNat 20 442369).zeroExtend 32 <<< 12).signExtend 64 = BitVec.ofNat 64 1811943424 := by
  decide

theorem setup_ready (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (nonempty : positions.card ≠ 0) :
    let init := s.initialState .opening (trapdoor, positions)
    Runs init (setupRun init) 11 11 ∧ RecordAt init (setupRun init) positions 0 := by
  intro init
  obtain ⟨pc₀, trap, indices, proof, count⟩ := initial_registers s layout trapdoor positions
  obtain ⟨_, _, c₃, _, _⟩ := setup_codes
  obtain ⟨run₁, pc₁, mem₁, x15, x21, keep₁⟩ := setup_head init pc₀
  obtain ⟨run₂, pc₂, mem₂, keep₂⟩ := setup_branch init pc₁
  have card := card_le positions
  have hL : LENGTH = 16777216 := rfl
  have nonzero : (setupHead init).getReg .x16 ≠ 0#64 := by
    rw [keep₁ .x16 (by decide) (by decide), count]
    intro same
    have := QOpening.nat_address_injective (by omega) (by decide) same
    omega
  have pc₂' : (setupBranch init).pc = BitVec.ofNat 64 (4096+4*2) := by rw [pc₂, if_neg nonzero]
  have pure₃ : ([.ADDI .x8 .x13 0, .ADDI .x9 .x12 0, .ADDI .x18 .x16 0, .LUI .x22 442369, .ADD .x22 .x9 .x22,
    .ADDI .x19 .x0 5, .ADDI .x23 .x0 368, .LUI .x26 1, .ADDI .x26 .x26 636] : List Instr).all pureOp = true := rfl
  have run₃ := runs_pure _ 2 (setupBranch init) c₃ pc₂' pure₃
  have reg (r : Reg) : (setupBranch init).getReg r = (setupHead init).getReg r := keep₂ r
  have base (r : Reg) (a : r ≠ .x15) (b : r ≠ .x21) : (setupBranch init).getReg r = init.getReg r :=
    (keep₂ r).trans (keep₁ r a b)
  refine ⟨(run₁.trans (run₂.trans run₃)).cast rfl rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [setupRun, pure_pc _ _ pure₃, pc₂', pc_offset, if_neg (Ne.symm nonempty)]; rfl
  · simp [setupRun, execInstrBr, signExtend12]
    rw [base .x13 (by decide) (by decide), indices]
  · simp [setupRun, execInstrBr, signExtend12]
    rw [base .x12 (by decide) (by decide), trap]
  · simp [setupRun, execInstrBr, signExtend12]
    rw [base .x16 (by decide) (by decide), count]
  · simp [setupRun, execInstrBr, signExtend12]
  · simp [setupRun, execInstrBr, signExtend12]
    rw [reg .x15, x15, proof]
  · simp [setupRun, execInstrBr, signExtend12]
    rw [reg .x21, x21, proof]
  · simp [setupRun, execInstrBr, signExtend12, lui_salts]
    rw [base .x12 (by decide) (by decide), trap, ← BitVec.ofNat_add]
    rfl
  · simp [setupRun, execInstrBr, signExtend12]
  · simp [setupRun, execInstrBr, signExtend12]
    decide
  · refine ⟨fun a _ _ => ?_, fun u h => by omega⟩
    have same : (setupRun init).mem = init.mem := by
      rw [setupRun, pure_mem _ _ pure₃, mem₂, mem₁]
    simp only [MachineState.getMem, same]

theorem nonempty_bound (positions : Positions) :
    BitVec.ofNat 64 (proofBase+8*(178*positions.card)) - BitVec.ofNat 64 proofBase =
      BitVec.ofNat 64 (proofLength positions) := by
  have card := card_le positions
  have hL : LENGTH = 16777216 := rfl
  have : proofBase = 10804535392 := rfl
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, word_lt _ (by omega), word_lt _ (by omega), word_lt _ (by unfold proofLength; omega)]
  unfold proofLength
  omega

theorem opening_physical (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) :
    ∃ result : Execution, s.run .opening (trapdoor, positions) = pure result ∧
      OpenPhysical s trapdoor positions result := by
  let init := s.initialState .opening (trapdoor, positions)
  have card := card_le positions
  have hL : LENGTH = 16777216 := rfl
  have budget : scheduledSteps positions ≤ s.steps .opening := by
    refine le_trans ?_ abi.fuel
    unfold scheduledSteps
    split <;> omega
  obtain ⟨pc₀, trap, indices, proof, count⟩ := initial_registers s abi.toOpeningLayout trapdoor positions
  by_cases empty : positions.card = 0
  · obtain ⟨run₁, pc₁, mem₁, x15, x21, keep₁⟩ := setup_head init pc₀
    obtain ⟨run₂, pc₂, mem₂, keep₂⟩ := setup_branch init pc₁
    have zero : (setupHead init).getReg .x16 = 0#64 := by
      rw [keep₁ .x16 (by decide) (by decide), count, empty]
    have pc₂' : (setupBranch init).pc = BitVec.ofNat 64 (4096+4*154) := by rw [pc₂, if_pos zero]
    let result : Execution := ⟨.success, exitRun (setupBranch init), 6, 0⟩
    refine ⟨result, ?_, ⟨rfl, ?_, rfl, by simp [result, scheduledCycles, empty], ?_⟩⟩
    · change execute (s.image .opening) (s.steps .opening) init true = pure result
      rw [abi.image, show s.steps .opening = 2+(4+(s.steps .opening-6)) by
        simp [scheduledSteps, empty] at budget; omega, (run₁.trans run₂) (4+(s.steps .opening-6)) true,
        execute_exit _ pc₂']
      simp [result, Execution.charge]
    · show ((exitRun (setupBranch init)).getReg .x11).toNat = _
      rw [exit_length, keep₂, keep₂, x15, x21]
      simp [proofLength, empty]
    · refine ⟨fun a _ _ => ?_, fun u h => by simp [empty] at h⟩
      have same : (exitRun (setupBranch init)).mem = init.mem := by
        rw [exit_memory, mem₂, mem₁]
      exact congrFun same _
  · obtain ⟨run₁, ready⟩ := setup_ready s abi.toOpeningLayout trapdoor positions empty
    obtain ⟨run₂, done⟩ := records_run s abi.toOpeningLayout trapdoor positions positions.card 0
      (setupRun init) (by omega) ready
    let final := recordsRun positions.card (setupRun init)
    have pcFinal : final.pc = BitVec.ofNat 64 (4096+4*154) := by simpa using done.pc
    let result : Execution := ⟨.success, exitRun final, scheduledCycles positions, 0⟩
    refine ⟨result, ?_, ⟨rfl, ?_, rfl, rfl, ?_⟩⟩
    · change execute (s.image .opening) (s.steps .opening) init true = pure result
      have steps : s.steps .opening = (11+517*positions.card)+(4+(s.steps .opening-scheduledSteps positions)) := by
        simp [scheduledSteps, empty] at budget ⊢; omega
      rw [abi.image, steps, (run₁.trans run₂) _ true, execute_exit _ pcFinal]
      simp [result, Execution.charge, scheduledCycles, empty]
      omega
    · show ((exitRun final).getReg .x11).toNat = _
      rw [exit_length, done.dest, done.begin, nonempty_bound, word_lt _ (by unfold proofLength; omega)]
    · exact done.inv.of_mem (exit_memory final)

theorem opening_success (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (result : Execution) (physical : OpenPhysical s trapdoor positions result) :
    s.openingSucceeded result = true := by
  have card := card_le positions
  have bytes : (result.state.getReg .x11).toNat ≤ s.sizes.proof := by
    rw [physical.length]
    refine le_trans ?_ abi.capacity
    unfold proofLength PENTA_PROOF_CAPACITY
    omega
  simp [Submission.openingSucceeded, physical.success, bytes]

theorem opening_scored_limits (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (result : Execution) (physical : OpenPhysical s trapdoor positions result)
    (count : positions.card = BATCH) :
    result.cycles ≤ 74639 ∧ (result.state.getReg .x11).toNat ≤ 182272 := by
  have size : positions.card = 128 := count
  rw [physical.cycles, physical.length]
  simp [scheduledCycles, proofLength, size]

end TwoPermutationPrototype.QuadOpening
