import CommitGolfCandidate.CapMarkEffect
import CommitGolfCandidate.CapMarkMemoryEffect
import CommitGolfCandidate.CapMarkLoopReady
import CommitGolfCandidate.CapCountedLoop

/-! Actual descending occupancy loop. Every positive residual node pays one
checked ten-instruction iteration. Zero residual stops at the branch fallthrough;
entry/header instructions are accounted for separately. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capMarkPrefix

def capMarkLoopRun (marks : Reg) : Nat → MachineState → MachineState :=
  capCountedRun (fun state => capMarkPrefix marks state 10)

theorem cap_mark_loop_run_zero (marks : Reg) (state : MachineState) :
    capMarkLoopRun marks 0 state = state :=
  capCountedRun.eq_1 _ _

theorem cap_mark_loop_run_succ (marks : Reg) (remaining : Nat) (state : MachineState) :
    capMarkLoopRun marks (remaining + 1) state =
      capMarkLoopRun marks remaining (capMarkPrefix marks state 10) :=
  capCountedRun.eq_2 _ state remaining

theorem cap_mark_loop_next (marks : Reg) (start : Word) (state : MachineState)
    (leaves node : Nat) (marked : Nat → Bool)
    (selected : CapMarksRegister marks) (bounded : leaves ≤ 256)
    (positive : 0 < node) (internal : node < leaves)
    (equation : marked node = (marked (2 * node) || marked (2 * node + 1)))
    (invariant : CapMarkLoopReady marks start state leaves node marked) :
    CapMarkLoopReady marks start (capMarkPrefix marks state 10)
      leaves (node - 1) marked := by
  apply cap_mark_ready_transport marks start state (capMarkPrefix marks state 10)
    leaves node marked bounded positive internal equation invariant.ready
  · exact (cap_mark_prefix_register marks state 10 (by decide) marks
      (cap_marks_register_outside marks selected)).trans invariant.base
  · exact cap_mark_counter marks state node invariant.index positive
  · have pc : state.pc = start :=
      invariant.pc.trans (ite_eq_right (Nat.ne_of_gt positive))
    exact cap_mark_latch_pc marks state start node pc invariant.index positive
      (Nat.lt_of_lt_of_le internal bounded)
  · exact cap_mark_memory_effect marks state node selected invariant.base invariant.index

/-- The natural residual bound and the machine projections travel together. -/
private theorem cap_mark_loop_transport (marks : Reg) (start : Word)
    (leaves : Nat) (marked : Nat → Bool)
    (selected : CapMarksRegister marks) (bounded : leaves ≤ 256)
    (equations : ∀ node, 0 < node → node < leaves →
      marked node = (marked (2 * node) || marked (2 * node + 1)))
    (remaining : Nat) (state : MachineState)
    (valid : remaining + 1 < leaves ∧
      CapMarkLoopReady marks start state leaves (remaining + 1) marked) :
    remaining < leaves ∧ CapMarkLoopReady marks start
      (capMarkPrefix marks state 10) leaves remaining marked := by
  have positive : 0 < remaining + 1 := Nat.zero_lt_succ remaining
  exact ⟨Nat.lt_trans (Nat.lt_succ_self remaining) valid.1,
    cap_mark_loop_next marks start state leaves (remaining + 1) marked selected bounded
      positive valid.1 (equations _ positive valid.1) valid.2⟩

private theorem cap_mark_loop_checked (image : Image) (marks : Reg) (start : Word)
    (fetched : CapMarkFetched image marks start) (selected : CapMarksRegister marks)
    (leaves : Nat) (marked : Nat → Bool) (bounded : leaves ≤ 256)
    (count : Nat) (current : MachineState)
    (valid : count + 1 < leaves ∧
      CapMarkLoopReady marks start current leaves (count + 1) marked)
    (extra : Nat) (coins : Bool) :
    execute image (10 + extra) current coins =
      (do let result ← execute image extra (capMarkPrefix marks current 10) coins
          return result.charge 10 0) := by
  have pc : current.pc = start :=
    valid.2.pc.trans (ite_eq_right (Nat.ne_of_gt (Nat.zero_lt_succ count)))
  obtain ⟨left, right, parent, _⟩ := cap_mark_access marks current leaves (count + 1)
    selected valid.2.base valid.2.index bounded valid.1
  exact cap_mark_execute image marks start fetched current pc left right parent extra coins

/-- No oracle calls occur in the pass. Fetches and accesses are tied to each
actual prefix state, and the fuel count is exactly ten times the residual. -/
theorem cap_mark_loop_execute (image : Image) (marks : Reg) (start : Word)
    (fetched : CapMarkFetched image marks start) (selected : CapMarksRegister marks)
    (leaves remaining : Nat) (marked : Nat → Bool)
    (bounded : leaves ≤ 256) (internal : remaining < leaves)
    (equations : ∀ node, 0 < node → node < leaves →
      marked node = (marked (2 * node) || marked (2 * node + 1)))
    (state : MachineState)
    (invariant : CapMarkLoopReady marks start state leaves remaining marked)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (10 * remaining + fuel) state allowCoins =
      (do let result ← execute image fuel (capMarkLoopRun marks remaining state) allowCoins
          return result.charge (10 * remaining) 0) := by
  exact cap_counted_run_execute image 10 (fun current => capMarkPrefix marks current 10)
    (fun count current => count < leaves ∧ CapMarkLoopReady marks start current leaves count marked)
    (cap_mark_loop_transport marks start leaves marked selected bounded equations)
    (cap_mark_loop_checked image marks start fetched selected leaves marked bounded)
    remaining state ⟨internal, invariant⟩ fuel allowCoins

theorem cap_mark_loop_finished (marks : Reg) (start : Word)
    (leaves remaining : Nat) (marked : Nat → Bool)
    (selected : CapMarksRegister marks) (bounded : leaves ≤ 256)
    (internal : remaining < leaves)
    (equations : ∀ node, 0 < node → node < leaves →
      marked node = (marked (2 * node) || marked (2 * node + 1)))
    (state : MachineState)
    (invariant : CapMarkLoopReady marks start state leaves remaining marked) :
    CapMarkLoopReady marks start (capMarkLoopRun marks remaining state) leaves 0 marked := by
  exact (cap_counted_run_ready (fun current => capMarkPrefix marks current 10)
    (fun count current => count < leaves ∧ CapMarkLoopReady marks start current leaves count marked)
    (cap_mark_loop_transport marks start leaves marked selected bounded equations)
    remaining state ⟨internal, invariant⟩).2

end CommitGolfCandidate
