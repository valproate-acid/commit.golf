import CommitGolfCandidate.CapMarkLoopFrame

/-! Two real entry instructions initialize leaves-1 and bypass the descending
body for a one-leaf cap. This includes the zero-body case without charging a
terminal iteration or weakening the positive natural bound on the cap size. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capMarkHeaderSet (leavesReg : Reg) (state : MachineState) : MachineState :=
  execInstrBr state (.ADDI .x20 leavesReg 4095)

def capMarkHeaderState (leavesReg : Reg) (state : MachineState) : MachineState :=
  execInstrBr (capMarkHeaderSet leavesReg state) (.BEQ .x20 .x0 44)

attribute [local irreducible] capMarkHeaderState capMarkHeaderSet

private theorem header_charge (result : Execution) :
    (result.charge 1 0).charge 1 0 = result.charge 2 0 := by
  simp only [Execution.charge, Nat.zero_add, ← Nat.add_assoc]

def CapMarkHeaderFetched (image : Image) (leavesReg : Reg) (entry : Word) : Prop :=
  ∀ state : MachineState, state.pc = entry →
    fetch image state = some (.base (.ADDI .x20 leavesReg 4095)) ∧
    fetch image (capMarkHeaderSet leavesReg state) = some (.base (.BEQ .x20 .x0 44))

theorem cap_mark_header_execute (image : Image) (leavesReg : Reg) (entry : Word)
    (fetched : CapMarkHeaderFetched image leavesReg entry)
    (state : MachineState) (pc : state.pc = entry)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (2 + fuel) state allowCoins =
      (do let result ← execute image fuel (capMarkHeaderState leavesReg state) allowCoins
          return result.charge 2 0) := by
  obtain ⟨first, second⟩ := fetched state pc
  have firstStep : ordinaryStep state (.base (.ADDI .x20 leavesReg 4095)) =
      some (capMarkHeaderSet leavesReg state) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, ite_true, capMarkHeaderSet]
  have secondStep : ordinaryStep (capMarkHeaderSet leavesReg state)
      (.base (.BEQ .x20 .x0 44)) = some (capMarkHeaderState leavesReg state) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, ite_true, capMarkHeaderState]
  rw [show 2 + fuel = (fuel + 1) + 1 by omega,
    execute_ordinary_step image _ state _ (fuel + 1) allowCoins first firstStep,
    execute_ordinary_step image _ _ _ fuel allowCoins second secondStep]
  simp only [instructionCycles, bind_assoc, pure_bind, header_charge]

theorem cap_mark_header_register (leavesReg : Reg) (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x20) :
    (capMarkHeaderState leavesReg state).getReg reg = state.getReg reg := by
  have branch (current : MachineState) :
      (execInstrBr current (.BEQ .x20 .x0 (44 : BitVec 13))).getReg reg =
        current.getReg reg := by
    simp only [execInstrBr]
    split <;> exact MachineState.getReg_setPC
  rw [capMarkHeaderState, branch]
  simp only [capMarkHeaderSet, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside)]

theorem cap_mark_header_memory (leavesReg : Reg) (state : MachineState) :
    (capMarkHeaderState leavesReg state).mem = state.mem := by
  have branch (current : MachineState) :
      (execInstrBr current (.BEQ .x20 .x0 (44 : BitVec 13))).mem = current.mem := by
    simp only [execInstrBr]
    split <;> simp only [MachineState.setPC]
  rw [capMarkHeaderState, branch]
  simp only [capMarkHeaderSet, execInstrBr, MachineState.setPC, MachineState.setReg]

theorem cap_mark_header_counter (leavesReg : Reg) (state : MachineState) (leaves : Nat)
    (count : state.getReg leavesReg = BitVec.ofNat 64 leaves) (positive : 0 < leaves) :
    (capMarkHeaderState leavesReg state).getReg .x20 = BitVec.ofNat 64 (leaves - 1) := by
  have branch (current : MachineState) :
      (execInstrBr current (.BEQ .x20 .x0 (44 : BitVec 13))).getReg .x20 =
        current.getReg .x20 := by
    simp only [execInstrBr]
    split <;> exact MachineState.getReg_setPC
  rw [capMarkHeaderState, branch]
  simp (disch := decide) only [capMarkHeaderSet, execInstrBr,
    MachineState.getReg_setPC, MachineState.getReg_setReg_eq, count]
  exact cap_mark_decrement leaves positive

theorem cap_mark_header_pc (leavesReg : Reg) (state : MachineState) (entry : Word)
    (leaves : Nat) (pc : state.pc = entry)
    (count : state.getReg leavesReg = BitVec.ofNat 64 leaves)
    (positive : 0 < leaves) (bounded : leaves ≤ 256) :
    (capMarkHeaderState leavesReg state).pc =
      if leaves = 1 then (entry + 8) + 40 else entry + 8 := by
  have setCounter : (capMarkHeaderSet leavesReg state).getReg .x20 =
      BitVec.ofNat 64 (leaves - 1) := by
    simp (disch := decide) only [capMarkHeaderSet, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, count]
    exact cap_mark_decrement leaves positive
  have setPC : (capMarkHeaderSet leavesReg state).pc = entry + 4 := by
    simpa only [capMarkHeaderSet, execInstrBr, MachineState.setPC] using
      congrArg (fun value : Word => value + 4) pc
  rw [capMarkHeaderState]
  simp only [execInstrBr, setCounter, setPC]
  have zero : (capMarkHeaderSet leavesReg state).getReg .x0 = 0 := rfl
  rw [zero]
  by_cases last : leaves = 1
  · subst leaves
    simp only [Nat.sub_self, show BitVec.ofNat 64 0 = (0 : Word) by rfl,
      beq_self_eq_true, ite_true, MachineState.setPC]
    rw [show signExtend13 (44 : BitVec 13) = (44 : Word) by decide]
    simp only [BitVec.add_assoc]
    rfl
  · have nonzero : BitVec.ofNat 64 (leaves - 1) ≠ 0 := by
      intro equal
      have numeric := congrArg BitVec.toNat equal
      change (leaves - 1) % 2^64 = 0 at numeric
      rw [Nat.mod_eq_of_lt (by omega : leaves - 1 < 2^64)] at numeric
      omega
    have test : (BitVec.ofNat 64 (leaves - 1) == (0 : Word)) = false :=
      beq_eq_false_iff_ne.mpr nonzero
    simp only [test, Bool.false_eq_true, ite_false, MachineState.setPC, last,
      BitVec.add_assoc]
    rfl

/-- Leaf occupancy is unchanged by the header; the body receives the exact
natural counter, address base and conditional entry PC. -/
theorem cap_mark_header_ready (marks leavesReg : Reg) (state : MachineState)
    (entry : Word) (leaves : Nat) (marked : Nat → Bool)
    (selected : CapMarksRegister marks) (base : state.getReg marks = 28672)
    (count : state.getReg leavesReg = BitVec.ofNat 64 leaves) (pc : state.pc = entry)
    (positive : 0 < leaves) (bounded : leaves ≤ 256)
    (ready : CapMarksReady state leaves (leaves - 1) marked) :
    CapMarkLoopReady marks (entry + 8) (capMarkHeaderState leavesReg state)
      leaves (leaves - 1) marked := by
  refine ⟨?_, cap_mark_header_counter leavesReg state leaves count positive, ?_, ?_⟩
  · rw [cap_mark_header_register leavesReg state marks
      (cap_marks_register_outside marks selected).2.2.1]
    exact base
  · have result := cap_mark_header_pc leavesReg state entry leaves pc count positive bounded
    simpa only [cap_mark_one_iff leaves positive] using result
  · exact cap_marks_ready_memory state (capMarkHeaderState leavesReg state)
      leaves (leaves - 1) marked (cap_mark_header_memory leavesReg state) ready

end CommitGolfCandidate
