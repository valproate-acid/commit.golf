import CommitGolfCandidate.TwoPermutationCounted
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate (checkEvaluation check_evaluation_pure check_evaluation_bind check_evaluation_public
  oracle_run_public oracle_run_pure oracle_run_bind oracle_run_coins fixedOracleRun)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def packedOutput (s : MachineState) (oracle : Oracle) {bits : Nat} (packed : BitVec bits) : Execution :=
  ⟨.success,(checkEvaluation oracle (commitBody s packed)).1,691142677,50331647⟩

attribute [local irreducible] commitBody checkEvaluation

private theorem counted_draw {bits : Nat} (oracle : Oracle) (body : BitVec bits → OracleComp World MachineState)
    (f : MachineState → Execution) (calls : Nat) (law : ∀ p, RunPublic oracle (body p) calls) :
    oracle.run (do
      let p ← (liftM ($ᵗ BitVec bits : ProbComp (BitVec bits)) : OracleComp World (BitVec bits))
      let state ← body p
      return f state) =
      (do let packed ← $ᵗ BitVec bits
          return (f (checkEvaluation oracle (body packed)).1,calls)) := by
  rw [CommitGolfCandidate.oracle_run_coins_bind]
  apply bind_congr_of_forall_mem_support
  intro packed _
  rw [oracle_run_bind,show oracle.run (body packed)=_ from law packed,pure_bind]
  simp only [oracle_run_pure,pure_bind,Nat.add_zero]

theorem counted_commit_trace (oracle : Oracle) (s : MachineState) :
    oracle.run (commitTrace s) =
      (do let packed ← $ᵗ BitVec (8*((initialPrefix s 11).getReg .x11).toNat)
          return (packedOutput s oracle packed,50331647)) := by
  exact counted_draw oracle (fun p => commitBody s p) (fun st => ⟨.success,st,691142677,50331647⟩)
    50331647 (counted_commit_body oracle s)

theorem commit_machine_resources (candidate : Submission) (abi : CommitABI candidate) (msg : Message)
    {res : Execution} (hit : res ∈ support (candidate.run .commit msg)) :
    res.exit=.success ∧ res.cycles=691142677 ∧ res.oracleCalls=50331647 := by
  rw [submission_commit_run candidate abi msg] at hit
  simp only [commitTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨_,_,_,_,rfl⟩ := hit
  exact ⟨rfl,rfl,rfl⟩

end TwoPermutationPrototype.RV64
