import CommitGolfCandidate.QuadCommitLeafSpill
import CommitGolfCandidate.TwoPermutationPackedMeaning
import CommitGolfCandidate.QuadCommitLeafLatch

namespace TwoPermutationPrototype.Quad.Commit.Leaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64
open CommitGolfCandidate (checkEvaluation check_evaluation_bind check_evaluation_pure check_evaluation_support splitBlocks)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] checkEvaluation leavesTrace fullParents rootPrefix parentSetup readyState

theorem same_mem_prefix (oracle : Oracle) (before : Memory) (s t : MachineState) (pos : Nat) (h : t.mem=s.mem)
    (prev : PinnedLeafPrefix oracle before s pos) : PinnedLeafPrefix oracle before t pos := by
  have mem : memoryView t=memoryView s := by funext word;change t.mem _=s.mem _;rw [h]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i hi;rw [mem];exact prev.digests i hi
  · intro i lo hi;rw [mem];exact prev.messages i lo hi
  · intro i hi;rw [mem];exact prev.salts i hi
  · intro g hg;rw [mem];exact prev.zeros g hg
  · intro k h a b c;rw [mem];exact prev.upper k h a b c

theorem prefix_unit (oracle : Oracle) (before : Memory) (s : MachineState) (g u : Nat)
    (bound : g<4097) (inside : u<4096) (r : Regs s g u) (prev : PinnedLeafPrefix oracle before s (4095*g+u)) :
    PinnedLeafPrefix oracle before (checkEvaluation oracle (unitTrace s g u)).1 (4095*g+u+1) := by
  have eq : (posSlot u).val=u := Nat.mod_eq_of_lt inside
  have start : PinnedLeafPrefix oracle before s (4095*g+(posSlot u).val) := by rw [eq];exact prev
  have ru : Regs s g (posSlot u).val := by rw [eq];exact r
  have raw := production_prefix_step oracle before s g (posSlot u) bound ru start
  simp only [eq] at raw
  simp only [unitTrace,check_evaluation_bind,check_evaluation_pure]
  exact same_mem_prefix _ _ _ _ _ (rebase_mem _ u) raw

theorem prefix_group (oracle : Oracle) (before : Memory) (s : MachineState) (g cnt u : Nat)
    (bound : g<4097) (inside : u+cnt≤4096) (r : Regs s g u) (prev : PinnedLeafPrefix oracle before s (4095*g+u)) :
    PinnedLeafPrefix oracle before (checkEvaluation oracle (group g cnt u s)).1 (4095*g+u+cnt) := by
  induction cnt generalizing s u with
  | zero => simpa only [group,check_evaluation_pure,Nat.add_zero] using prev
  | succ k ih =>
    simp only [group,check_evaluation_bind]
    have next := prefix_unit oracle before s g u bound (by omega) r prev
    have regs := unit_post s g u bound (by omega) r (check_evaluation_support oracle (unitTrace s g u))
    rw [show 4095*g+u+(k+1)=4095*g+(u+1)+k by omega]
    exact ih _ (u+1) (by omega) regs (by simpa only [←Nat.add_assoc] using next)

theorem prefix_batch (oracle : Oracle) (before : Memory) (s : MachineState) (g : Nat) (bound : g<4097)
    (r : Regs s g 1) (prev : PinnedLeafPrefix oracle before s (4095*g+1)) :
    PinnedLeafPrefix oracle before (checkEvaluation oracle (batch g s)).1 (4095*(g+1)+1) := by
  have carry (p : OracleComp World MachineState) (pc : Word) (cnt : Nat)
      (h : PinnedLeafPrefix oracle before (checkEvaluation oracle p).1 cnt) :
      PinnedLeafPrefix oracle before (checkEvaluation oracle (p >>= fun z => pure (z.setPC pc))).1 cnt := by
    simp only [check_evaluation_bind,check_evaluation_pure]
    exact same_mem_prefix _ _ (checkEvaluation oracle p).1 _ _ rfl h
  unfold batch
  apply carry
  rw [show 4095*(g+1)+1=4095*g+1+4095 by omega]
  exact prefix_group oracle before s g 4095 1 bound (by decide) r prev

theorem prefix_groups (oracle : Oracle) (before : Memory) (s : MachineState) (cnt g : Nat)
    (limit : g+cnt=4097) (r : 0<cnt → Regs s g 1) (prev : PinnedLeafPrefix oracle before s (4095*g+1)) :
    PinnedLeafPrefix oracle before (checkEvaluation oracle (groups cnt g s)).1 (4095*(g+cnt)+1) := by
  induction cnt generalizing s g with
  | zero => simpa only [groups,check_evaluation_pure,Nat.add_zero] using prev
  | succ k ih =>
    simp only [groups,check_evaluation_bind]
    have valid := r (by omega)
    have next := prefix_batch oracle before s g (by omega) valid prev
    have endReg := (batch_post s g (by omega) valid (check_evaluation_support oracle (batch g s))).1
    rw [show g+(k+1)=g+1+k by omega]
    exact ih _ (g+1) (by omega) (fun more => endReg (by omega)) next

theorem counted_raw (oracle : Oracle) (s : MachineState) (u : Fin 4096) (start i dst : Nat) :
    RunPublic oracle (leafTrace s u start i dst) 2 := by
  unfold leafTrace
  apply run_bind_public _ _ _ 1 1 (run_query_public ..)
  intro a
  apply run_bind_public _ _ _ 1 0 (run_query_public ..)
  intro b;exact run_pure_public ..

theorem counted_unit (oracle : Oracle) (s : MachineState) (g u : Nat) : RunPublic oracle (unitTrace s g u) 2 :=
  run_bind_public _ _ _ 2 0 (counted_raw ..) (fun _ => run_pure_public ..)

theorem counted_group (oracle : Oracle) (s : MachineState) (g cnt u : Nat) : RunPublic oracle (group g cnt u s) (2*cnt) := by
  induction cnt generalizing s u with
  | zero => exact run_pure_public ..
  | succ k ih =>
    rw [show 2*(k+1)=2+2*k by omega]
    exact run_bind_public _ _ _ 2 _ (counted_unit ..) (fun _ => ih _ _)

theorem counted_batch (oracle : Oracle) (s : MachineState) (g : Nat) : RunPublic oracle (batch g s) 8190 :=
  run_bind_public _ _ _ (2*4095) 0 (counted_group ..) (fun _ => run_pure_public ..)

theorem counted_groups (oracle : Oracle) (s : MachineState) (cnt g : Nat) : RunPublic oracle (groups cnt g s) (8190*cnt) := by
  induction cnt generalizing s g with
  | zero => exact run_pure_public ..
  | succ k ih =>
    rw [show 8190*(k+1)=8190+8190*k by omega]
    exact run_bind_public _ _ _ 8190 _ (counted_batch ..) (fun _ => ih _ _)


end TwoPermutationPrototype.Quad.Commit.Leaves
