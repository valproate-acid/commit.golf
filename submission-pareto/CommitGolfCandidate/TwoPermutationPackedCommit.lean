import CommitGolfCandidate.TwoPermutationPackedSetup

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8192
set_option maxHeartbeats 1700000
attribute [local irreducible] execute packed_wideReadyState parentSetup rootPrefix

structure PackedLeavesFinished (state : MachineState) : Prop where
  pc : state.pc=184784
  selector : state.getReg .x5=0
  heap : state.getReg .x9=4294971424
  stride : state.getReg .x19=536870912
  stop : state.getReg .x21=wordAddress (leafDest (2^24))
  output : state.getReg .x8=4294971392

structure PackedLeafExecution where
  trace : MachineState → OracleComp World MachineState
  executes : ∀ (initial : MachineState), CommitEntry initial → ∀ {bits : Nat}
    (coins : BitVec bits) (fuel : Nat),
      execute packedWideCommitImage (184950783+fuel) (packed_wideReadyState initial coins) true =
        (do let leaves ← trace (packed_wideReadyState initial coins)
            let out ← execute packedWideCommitImage fuel leaves true
            return out.charge 419831807 33554432)
  finished : ∀ (initial : MachineState), CommitEntry initial → ∀ {bits : Nat}
    (coins : BitVec bits) (out : MachineState),
      out ∈ support (trace (packed_wideReadyState initial coins)) → PackedLeavesFinished out

def packed_wideCommitBody (leaf : PackedLeafExecution) (initial : MachineState) {bits : Nat}
    (coins : BitVec bits) : OracleComp World MachineState := do
  let leaves ← leaf.trace (packed_wideReadyState initial coins)
  let parents ← packedParentGroups 184804 46995 357 (parentSetup leaves 5)
  return rootPrefix parents 10

theorem packed_wide_commit_after_draw (leaf : PackedLeafExecution) (initial : MachineState)
    (entry : CommitEntry initial) {bits : Nat} (coins : BitVec bits) (fuel : Nat) :
    execute packedWideCommitImage (252060372+fuel) (packed_wideReadyState initial coins) true =
      (do let result ← packed_wideCommitBody leaf initial coins
          return ⟨.success,result,604381901,50331647⟩) := by
  rw [show 252060372+fuel=184950783+(5+(67109573+(11+fuel))) by omega,
    leaf.executes initial entry coins]
  simp only [packed_wideCommitBody,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro leaves reached
  have fin := leaf.finished initial entry coins leaves reached
  have regs := packed_wide_parent_setup_ready leaves fin.pc fin.selector fin.heap fin.stride fin.stop
  rw [packed_execute_wide_parent_setup leaves fin.pc,packed_parent_phase _ _ regs.1 regs.2.1]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro parents reached
  obtain ⟨terms,pc,out⟩ := packed_parent_phase_post _ regs.1 regs.2.1 reached
  rw [execute_packed_root parents pc terms.heap (out.trans (regs.2.2.trans fin.output))]
  simp only [bind_assoc,pure_bind,Execution.charge]

def packed_wideCommitTrace (leaf : PackedLeafExecution) (initial : MachineState) :
    OracleComp World Execution := do
  let coins ← liftM ($ᵗ BitVec (8*((initialPrefix initial 11).getReg .x11).toNat) :
    ProbComp (BitVec (8*((initialPrefix initial 11).getReg .x11).toNat)))
  let state ← packed_wideCommitBody leaf initial coins
  return ⟨.success,state,637936351,50331647⟩

theorem packed_wide_commit_execution (leaf : PackedLeafExecution) (initial : MachineState)
    (entry : CommitEntry initial) (fuel : Nat) :
    execute packedWideCommitImage (252060390+fuel) initial true=packed_wideCommitTrace leaf initial := by
  rw [show 252060390+fuel=18+(252060372+fuel) by omega,packed_execute_wide_setup initial entry]
  simp only [packed_wideCommitTrace,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro coins _
  rw [packed_wide_commit_after_draw leaf initial entry coins]
  simp only [bind_assoc,pure_bind,Execution.charge]

theorem packed_submission_wide_commit_run (leaf : PackedLeafExecution) (program : Submission)
    (image : program.image .commit=packedWideCommitImage) (enough : 252060390≤program.steps .commit)
    (message : Message) (entry : CommitEntry (program.initialState .commit message)) :
    program.run .commit message=packed_wideCommitTrace leaf (program.initialState .commit message) := by
  change execute (program.image .commit) (program.steps .commit)
    (program.initialState .commit message) true=_
  rw [image,show program.steps .commit=252060390+(program.steps .commit-252060390) by omega]
  exact packed_wide_commit_execution leaf _ entry _

end TwoPermutationPrototype.RV64
