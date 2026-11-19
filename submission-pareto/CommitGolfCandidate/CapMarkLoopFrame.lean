import CommitGolfCandidate.CapMarkLoop

/-! Memory refinement and ABI frames for the actual occupancy pass. The pure
pass is used only as a memory projection; its unchanged registers and PC are
not substituted for the actual execution state. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capMarkPrefix capMarkLoopRun capCountedRun

theorem cap_mark_loop_register (marks : Reg) (remaining : Nat)
    (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x20 ∧ reg ≠ .x23 ∧ reg ≠ .x30) :
    (capMarkLoopRun marks remaining state).getReg reg = state.getReg reg := by
  induction remaining generalizing state with
  | zero => rw [cap_mark_loop_run_zero]
  | succ remaining ih =>
      rw [cap_mark_loop_run_succ]
      exact (ih _).trans (cap_mark_prefix_register marks state 10 (by decide) reg outside)

private theorem write_memory_congr (state reference : MachineState) (node : Nat)
    (equal : state.mem = reference.mem) :
    (capMarkWrite state node).mem = (capMarkWrite reference node).mem := by
  simp only [capMarkWrite, MachineState.setMem, MachineState.getMem, equal]

theorem cap_mark_pass_memory_congr (state reference : MachineState) (remaining : Nat)
    (equal : state.mem = reference.mem) :
    (capMarkPass state remaining).mem = (capMarkPass reference remaining).mem := by
  induction remaining generalizing state reference with
  | zero => exact equal
  | succ remaining ih =>
      exact ih _ _ (write_memory_congr state reference (remaining + 1) equal)

theorem cap_mark_loop_memory (marks : Reg) (start : Word)
    (leaves remaining : Nat) (marked : Nat → Bool)
    (selected : CapMarksRegister marks) (bounded : leaves ≤ 256)
    (internal : remaining < leaves)
    (equations : ∀ node, 0 < node → node < leaves →
      marked node = (marked (2 * node) || marked (2 * node + 1)))
    (state : MachineState)
    (invariant : CapMarkLoopReady marks start state leaves remaining marked) :
    (capMarkLoopRun marks remaining state).mem = (capMarkPass state remaining).mem := by
  induction remaining generalizing state with
  | zero => rw [cap_mark_loop_run_zero, capMarkPass]
  | succ remaining ih =>
      rw [cap_mark_loop_run_succ, capMarkPass]
      have positive := Nat.zero_lt_succ remaining
      have residual := Nat.lt_trans (Nat.lt_succ_self remaining) internal
      have next := cap_mark_loop_next marks start state leaves (remaining + 1) marked selected
        bounded positive internal (equations _ positive internal) invariant
      exact (ih residual _ next).trans
        (cap_mark_pass_memory_congr (capMarkPrefix marks state 10)
          (capMarkWrite state (remaining + 1)) remaining
          (cap_mark_memory_effect marks state (remaining + 1)
            selected invariant.base invariant.index))

theorem cap_mark_loop_frame (marks : Reg) (start : Word)
    (leaves remaining : Nat) (marked : Nat → Bool)
    (selected : CapMarksRegister marks) (bounded : leaves ≤ 256)
    (internal : remaining < leaves)
    (equations : ∀ node, 0 < node → node < leaves →
      marked node = (marked (2 * node) || marked (2 * node + 1)))
    (state reference : MachineState)
    (invariant : CapMarkLoopReady marks start state leaves remaining marked)
    (frame : CapHighBytes state reference) :
    CapHighBytes (capMarkLoopRun marks remaining state) reference := by
  exact cap_high_bytes_memory (capMarkPass state remaining) _ reference
    (cap_mark_loop_memory marks start leaves remaining marked selected bounded internal
      equations state invariant)
    (cap_mark_pass_frame state reference leaves remaining bounded internal frame)

theorem cap_mark_loop_roots (marks : Reg) (start : Word)
    (leaves remaining : Nat) (marked : Nat → Bool)
    (selected : CapMarksRegister marks) (bounded : leaves ≤ 256)
    (internal : remaining < leaves)
    (equations : ∀ node, 0 < node → node < leaves →
      marked node = (marked (2 * node) || marked (2 * node + 1)))
    (state : MachineState)
    (invariant : CapMarkLoopReady marks start state leaves remaining marked)
    (address : Nat) (belowMarks : address < 28672) :
    (capMarkLoopRun marks remaining state).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  exact (congrFun
    (cap_mark_loop_memory marks start leaves remaining marked selected bounded internal
      equations state invariant) (BitVec.ofNat 64 address)).trans
    (cap_mark_pass_roots state leaves remaining address bounded internal belowMarks)

end CommitGolfCandidate
