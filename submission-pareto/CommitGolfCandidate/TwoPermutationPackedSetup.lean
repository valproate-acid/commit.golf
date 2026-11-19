import CommitGolfCandidate.TwoPermutationPackedLeafFetch

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute packedWideCommitImage

def packed_wideFinishReady (state : MachineState) : MachineState :=
  execInstrBr (execInstrBr state (.SLLI .x7 .x13 11)) (.ADDI .x10 .x10 40)

def packed_wideReadyState (state : MachineState) {bits : Nat} (coins : BitVec bits) : MachineState :=
  packed_wideFinishReady (readyState state coins)

private def packed_wideFinishOps : List Instr :=
  readyInstructions ++ [.SLLI .x7 .x13 11,.ADDI .x10 .x10 40]

private def packed_wideReadyPrefix (state : MachineState) (i : Nat) : MachineState :=
  (packed_wideFinishOps.take i).foldl execInstrBr state

private theorem packed_wide_initial_run (state : MachineState) (atEntry : state.pc=4096) (fuel : Nat) :
    execute packedWideCommitImage (11+fuel) state true =
      (do let out ← execute packedWideCommitImage fuel (initialPrefix state 11) true
          return out.charge 11 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := initialPrefix state)
  intro i inside
  refine ⟨.base ((initialInstructions[i]?).getD .EBREAK),?_,?_,?_⟩
  · have pc : (initialPrefix state i).pc=BitVec.ofNat 64 (4096+4*i) := by
      interval_cases i <;>
        simp only [initialPrefix,initialInstructions,List.take,List.foldl,execInstrBr,MachineState.setPC,atEntry] <;> rfl
    have fetched := packed_wide_fetch_initial ⟨i,by omega⟩ (initialPrefix state i) pc
    interval_cases i <;> exact fetched
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

private theorem packed_wide_draw_run (state : MachineState) (pc : state.pc=4140) (r : SetupRegisters state)
    (fuel : Nat) :
    execute packedWideCommitImage (1+fuel) state true =
      (do let answer ← liftM ($ᵗ BitVec (8*(state.getReg .x11).toNat) : ProbComp (BitVec (8*(state.getReg .x11).toNat)))
          let out ← execute packedWideCommitImage fuel (writeBits state (wordAddress (leafSalt 0)) answer) true
          return out.charge 33554433 0) := by
  have fetched : fetch packedWideCommitImage state=some (.base .ECALL) :=
    packed_wide_fetch_initial ⟨11,by decide⟩ state pc
  have valid : randomArgumentsValid state=true := by rw [randomArgumentsValid,r.target,r.size]; decide
  have cost : 1+((state.getReg .x11).toNat+7)/8=33554433 := by rw [r.size]; rfl
  rw [Nat.add_comm 1 fuel,execute,fetched]
  simp only [r.selector,valid,r.target,cost]
  rfl

private theorem packed_wide_ready_run (state : MachineState) (atReady : state.pc=4144) (fuel : Nat) :
    execute packedWideCommitImage (6+fuel) state true =
      (do let out ← execute packedWideCommitImage fuel (packed_wideFinishReady (readyPrefix state 4)) true
          return out.charge 6 0) := by
  have endState : packed_wideReadyPrefix state 6 = packed_wideFinishReady (readyPrefix state 4) := rfl
  rw [←endState]
  apply CommitGolfCandidate.execute_unit_steps (states := packed_wideReadyPrefix state)
  intro i inside
  refine ⟨.base ((packed_wideFinishOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have pc : (packed_wideReadyPrefix state i).pc=BitVec.ofNat 64 (4096+4*(12+i)) := by
      interval_cases i <;>
        simp only [packed_wideReadyPrefix,packed_wideFinishOps,readyInstructions,List.cons_append,List.nil_append,List.take,List.foldl,
          execInstrBr,MachineState.setPC,atReady] <;> rfl
    have fetched := packed_wide_fetch_initial ⟨12+i,by omega⟩ (packed_wideReadyPrefix state i) pc
    interval_cases i <;> exact fetched
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem packed_execute_wide_setup (state : MachineState) (entry : CommitEntry state) (fuel : Nat) :
    execute packedWideCommitImage (18+fuel) state true =
      (do let answer ← liftM ($ᵗ BitVec (8*((initialPrefix state 11).getReg .x11).toNat) :
            ProbComp (BitVec (8*((initialPrefix state 11).getReg .x11).toNat)))
          let out ← execute packedWideCommitImage fuel (packed_wideReadyState state answer) true
          return out.charge 33554450 0) := by
  rw [show 18+fuel=11+(1+(6+fuel)) by omega,packed_wide_initial_run state entry.pc,
    packed_wide_draw_run _ (setup_pc state entry.pc) (setup_registers state entry)]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro answer _
  have pc : (writeBits (initialPrefix state 11) (wordAddress (leafSalt 0)) answer).pc=4144 := by
    rw [written_pc,setup_pc state entry.pc]
    rfl
  rw [packed_wide_ready_run _ pc]
  simp [Execution.charge,←Nat.add_assoc,packed_wideReadyState,readyState]

private theorem packed_wide_finish_register (state : MachineState) (reg : Reg)
    (kept : reg ∉ [Reg.x7,.x10]) :
    (packed_wideFinishReady state).getReg reg=state.getReg reg := by
  cases reg <;> first | rfl | simp at kept

theorem packed_wide_ready_state_register (state : MachineState) {bits : Nat} (coins : BitVec bits) (reg : Reg)
    (kept : reg ∉ [Reg.x7,.x10]) :
    (packed_wideReadyState state coins).getReg reg=(readyState state coins).getReg reg :=
  packed_wide_finish_register (readyState state coins) reg kept

private theorem packed_wide_finish_memory (state : MachineState) :
    (packed_wideFinishReady state).mem=state.mem := rfl

theorem packed_wide_ready_state_memory (state : MachineState) {bits : Nat} (coins : BitVec bits) :
    (packed_wideReadyState state coins).mem=(readyState state coins).mem :=
  packed_wide_finish_memory (readyState state coins)

theorem packed_wide_ready_source (state : MachineState) {bits : Nat} (coins : BitVec bits) :
    (packed_wideReadyState state coins).getReg .x10=(readyState state coins).getReg .x10+40 := rfl

theorem packed_wide_ready_state_entry (state : MachineState) (entry : CommitEntry state)
    {bits : Nat} (coins : BitVec bits) :
    (packed_wideReadyState state coins).pc=4168 ∧ (packed_wideReadyState state coins).getReg .x7=2048 := by
  have old := (post_random_regs state entry coins).1.pc
  constructor
  · change (readyState state coins).pc+4+4=_
    rw [old]
    rfl
  · change ((readyState state coins).getReg .x13 <<< (11 : Nat)) = _
    rw [(post_random_regs state entry coins).1.primitive]
    rfl

theorem packed_execute_wide_parent_setup (state : MachineState) (atSetup : state.pc=184784) (fuel : Nat) :
    execute packedWideCommitImage (5+fuel) state true =
      (do let out ← execute packedWideCommitImage fuel (parentSetup state 5) true
          return out.charge 5 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := parentSetup state)
  intro i inside
  refine ⟨.base ((parentSetupOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have pc : (parentSetup state i).pc=BitVec.ofNat 64 (4096+4*(45172+i)) := by
      interval_cases i <;>
        simp only [parentSetup,parentSetupOps,List.take,List.foldl,execInstrBr,MachineState.setPC,atSetup] <;> rfl
    exact packed_wide_fetch_parent_setup ⟨i,inside⟩ (parentSetup state i) pc
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem packed_wide_parent_setup_ready (state : MachineState) (atSetup : state.pc=184784)
    (selector : state.getReg .x5=0) (heap : state.getReg .x9=4294971424)
    (stride : state.getReg .x19=536870912)
    (stop : state.getReg .x21=wordAddress (leafDest (2^24))) :
    ParentRegs (parentSetup state 5) (2^24-1) ∧ (parentSetup state 5).pc=184804 ∧
      (parentSetup state 5).getReg .x8=state.getReg .x8 := by
  refine ⟨⟨?_,?_,selector,rfl,rfl,heap⟩,?_,rfl⟩
  · change state.getReg .x21+signExtend12 4032=_
    rw [stop]
    rfl
  · change state.getReg .x21-state.getReg .x19+signExtend12 4064=_
    rw [stop,stride]
    rfl
  · change state.pc+4+4+4+4+4=_
    rw [atSetup]
    rfl

end TwoPermutationPrototype.RV64
