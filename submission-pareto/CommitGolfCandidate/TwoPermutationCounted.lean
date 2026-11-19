import CommitGolfCandidate.TwoPermutationCommitRun
import CommitGolfCandidate.CountingCoins

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate (checkEvaluation check_evaluation_pure check_evaluation_bind check_evaluation_public
  oracle_run_public oracle_run_pure oracle_run_bind oracle_run_coins fixedOracleRun)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def RunPublic (oracle : Oracle) {α : Type} (p : OracleComp World α) (calls : Nat) : Prop :=
  oracle.run p=pure ((checkEvaluation oracle p).1,calls)

theorem run_pure_public (oracle : Oracle) {α : Type} (a : α) : RunPublic oracle (pure a) 0 := by
  simp [RunPublic,oracle_run_pure,check_evaluation_pure]

theorem run_query_public (oracle : Oracle) (q : PublicSpec.Domain) :
    RunPublic oracle (liftM (World.query (.inr q)) : OracleComp World (PublicSpec.Range q)) 1 := by
  simp [RunPublic,oracle_run_public,check_evaluation_public]

theorem run_bind_public (oracle : Oracle) {α β : Type} (p : OracleComp World α) (f : α → OracleComp World β)
    (k l : Nat) (left : RunPublic oracle p k) (right : ∀ a, RunPublic oracle (f a) l) :
    RunPublic oracle (p >>= f) (k+l) := by
  unfold RunPublic at *
  rw [oracle_run_bind,left,pure_bind]
  dsimp only
  rw [right,pure_bind,check_evaluation_bind]

theorem counted_leaf (oracle : Oracle) (s : MachineState) (g u : Nat) : RunPublic oracle (slotTrace s g u) 2 := by
  unfold slotTrace leafTrace
  apply run_bind_public _ _ _ 1 1 (run_query_public ..)
  intro a
  apply run_bind_public _ _ _ 1 0 (run_query_public ..)
  intro b
  exact run_pure_public ..

theorem counted_group (oracle : Oracle) (s : MachineState) (g cnt u : Nat) :
    RunPublic oracle (groupTrace g cnt u s) (2*cnt) := by
  induction cnt generalizing s u with
  | zero => exact run_pure_public ..
  | succ k ih =>
    rw [show 2*(k+1)=2+2*k by omega]
    exact run_bind_public _ _ _ 2 _ (counted_leaf ..) (fun _ => ih _ _)

theorem counted_batch (oracle : Oracle) (s : MachineState) (g : Nat) :
    RunPublic oracle (batchTrace g s) 32 :=
  run_bind_public _ _ _ (2*16) 0 (counted_group ..) (fun _ => run_pure_public ..)

theorem counted_leaves (oracle : Oracle) (s : MachineState) (cnt g : Nat) :
    RunPublic oracle (leavesTrace cnt g s) (32*cnt) := by
  induction cnt generalizing s g with
  | zero => exact run_pure_public ..
  | succ k ih =>
    rw [show 32*(k+1)=32+32*k by omega]
    exact run_bind_public _ _ _ 32 _ (counted_batch ..) (fun _ => ih _ _)

theorem counted_parents (oracle : Oracle) (s : MachineState) (rem cnt : Nat) :
    RunPublic oracle (parentsTrace rem cnt s) cnt := by
  induction cnt generalizing s with
  | zero => exact run_pure_public ..
  | succ k ih =>
    rw [parentsTrace]
    simpa only [Nat.add_comm 1 k] using
      (run_bind_public oracle (liftM (World.query (.inr (.inl (parentInput s (rem+(k+1)))))) : OracleComp World (BitVec 256))
        (fun answer => parentsTrace rem k (parentAfter s (rem+(k+1)) answer)) 1 k (run_query_public ..) (fun _ => ih _))

theorem counted_parent_batch (oracle : Oracle) (s : MachineState) (rem : Nat) :
    RunPublic oracle (parentBatch rem s) 128 :=
  run_bind_public _ _ _ 128 0 (counted_parents ..) (fun _ => run_pure_public ..)

theorem counted_parent_batches (oracle : Oracle) (s : MachineState) (cnt : Nat) :
    RunPublic oracle (parentBatches cnt s) (128*cnt) := by
  induction cnt generalizing s with
  | zero => exact run_pure_public ..
  | succ k ih =>
    rw [show 128*(k+1)=128+128*k by omega]
    exact run_bind_public _ _ _ 128 _ (counted_parent_batch ..) (fun _ => ih _)

theorem counted_full_parents (oracle : Oracle) (s : MachineState) :
    RunPublic oracle (fullParents s) 16777215 :=
  run_bind_public _ _ _ 127 (128*131071) (counted_parents ..) (fun _ => counted_parent_batches ..)

attribute [local irreducible] leavesTrace fullParents parentBatches parentsTrace

theorem counted_commit_body (oracle : Oracle) (s : MachineState) {bits : Nat} (packed : BitVec bits) :
    RunPublic oracle (commitBody s packed) 50331647 := by
  unfold commitBody
  apply run_bind_public _ _ _ (32*2^20) 16777215 (counted_leaves ..)
  intro leaves
  exact run_bind_public _ _ _ 16777215 0 (counted_full_parents ..) (fun _ => run_pure_public ..)


end TwoPermutationPrototype.RV64
