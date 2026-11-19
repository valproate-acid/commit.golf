import CommitGolfCandidate.TwoPermutationRoot
import CommitGolfCandidate.TwoPermutationInputWords

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 32768
set_option maxHeartbeats 1500000
attribute [local irreducible] execute writeBits parentAfter parentsTrace parentBatches leavesTrace

theorem parents_out_register (rem count : Nat) (s : MachineState) {out : MachineState}
    (hit : out ∈ support (parentsTrace rem count s)) : out.getReg .x8=s.getReg .x8 := by
  induction count generalizing s with
  | zero => simp only [parentsTrace,support_pure,Set.mem_singleton_iff] at hit;rw [hit]
  | succ k ih =>
    simp only [parentsTrace,mem_support_bind_iff] at hit
    obtain ⟨reply,_,reach⟩ := hit
    apply (ih _ reach).trans
    unfold parentAfter
    change (parentWritten s (rem+(k+1)) reply).getReg .x8=_
    exact CommitGolfCandidate.writeBits_register s _ reply .x8

theorem parent_batch_out_register (rem : Nat) (s : MachineState) {out : MachineState}
    (hit : out ∈ support (parentBatch rem s)) : out.getReg .x8=s.getReg .x8 := by
  simp only [parentBatch,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨body,reached,rfl⟩ := hit
  exact parents_out_register rem 128 s (out := body) reached

theorem all_parent_post (cnt : Nat) (s : MachineState) (r : ParentRegs s (128*cnt))
    (pc : s.pc=parentNextPC (128*cnt)) {out : MachineState} (hit : out ∈ support (parentBatches cnt s)) :
    ParentRegs out 0 ∧ out.pc=8216 ∧ out.getReg .x8=s.getReg .x8 := by
  induction cnt generalizing s with
  | zero =>
    simp only [parentBatches,support_pure,Set.mem_singleton_iff] at hit
    subst out; exact ⟨r,pc,rfl⟩
  | succ k ih =>
    simp only [parentBatches,mem_support_bind_iff] at hit
    obtain ⟨mid,step,reached⟩ := hit
    rw [Nat.mul_succ] at r pc
    have here : s.pc=6676 := by rw [pc,parentNextPC,if_neg (by omega)]
    obtain ⟨regs,next⟩ := parent_batch_post (128*k) s r here step
    obtain ⟨rend,epc,x8⟩ := ih mid regs next reached
    exact ⟨rend,epc,x8.trans (parent_batch_out_register _ _ step)⟩

theorem full_parents_post (s : MachineState) (r : ParentRegs s (2^24-1)) (pc : s.pc=5152)
    {out : MachineState} (hit : out ∈ support (fullParents s)) :
    ParentRegs out 0 ∧ out.pc=8216 ∧ out.getReg .x8=s.getReg .x8 := by
  simp only [fullParents,mem_support_bind_iff] at hit
  obtain ⟨mid,first,tail⟩ := hit
  have body := parents_post (128*131071) 127 0 s r pc first
  obtain ⟨endReg,last,x8⟩ := all_parent_post 131071 mid body.1 body.2 tail
  exact ⟨endReg,last,x8.trans (parents_out_register _ _ _ first)⟩

def commitBody (s : MachineState) {bits : Nat} (packed : BitVec bits) : OracleComp World MachineState := do
  let leaves ← leavesTrace (2^20) 0 (readyState s packed)
  let parents ← fullParents (parentSetup leaves 5)
  return rootPrefix parents 10

attribute [local irreducible] fullParents parentSetup rootPrefix readyState

theorem all_after_draw (s : MachineState) (entry : CommitEntry s) {bits : Nat} (packed : BitVec bits) (fuel : Nat) :
    execute commitImage (305266700+fuel) (readyState s packed) true =
      (do let state ← commitBody s packed
          return ⟨.success,state,657588229,50331647⟩) := by
  obtain ⟨r,stop,_⟩ := post_random_regs s entry packed
  rw [show 305266700+fuel=254803968+(5+(50462716+(11+fuel))) by omega,
      production_leaf_execution _ r stop]
  simp only [commitBody,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro leaves reached
  obtain ⟨pc,regs,start,out⟩ := after_leaves_parent_ready s entry packed reached
  rw [execute_parent_setup leaves pc,entire_parent_phase _ _ regs start]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro parents reached
  obtain ⟨p,endpc,result⟩ := full_parents_post _ regs start reached
  rw [execute_root parents endpc p.heap (result.trans out)]
  simp only [bind_assoc,pure_bind,Execution.charge]

attribute [local irreducible] commitBody

def commitTrace (s : MachineState) : OracleComp World Execution := do
  let packed ← liftM ($ᵗ BitVec (8*((initialPrefix s 11).getReg .x11).toNat) :
    ProbComp (BitVec (8*((initialPrefix s 11).getReg .x11).toNat)))
  let state ← commitBody s packed
  return ⟨.success,state,691142677,50331647⟩

theorem full_commit_execution (s : MachineState) (entry : CommitEntry s) (fuel : Nat) :
    execute commitImage (305266716+fuel) s true=commitTrace s := by
  rw [show 305266716+fuel=16+(305266700+fuel) by omega,execute_setup s entry]
  simp only [commitTrace,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro packed _
  rw [all_after_draw s entry packed]
  simp only [bind_assoc,pure_bind,Execution.charge]

theorem submission_commit_run (candidate : Submission) (abi : CommitABI candidate) (msg : Message) :
    candidate.run .commit msg=commitTrace (candidate.initialState .commit msg) := by
  change execute (candidate.image .commit) (candidate.steps .commit) _ true=_
  rw [abi.code,show candidate.steps .commit=305266716+(candidate.steps .commit-305266716) by have := abi.fuel;omega]
  exact full_commit_execution _ (abi_commit_entry candidate abi msg) _

end TwoPermutationPrototype.RV64
