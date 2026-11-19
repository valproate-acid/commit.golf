import CommitGolfCandidate.CapMarkInvariant

/-! Projection-only transport for the occupancy-loop invariant. The next state
is abstract here: this lemma does not expand any instruction prefix. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

structure CapMarkLoopReady (marks : Reg) (start : Word) (state : MachineState)
    (leaves remaining : Nat) (marked : Nat → Bool) : Prop where
  base : state.getReg marks = 28672
  index : state.getReg .x20 = BitVec.ofNat 64 remaining
  pc : state.pc = if remaining = 0 then start + 40 else start
  ready : CapMarksReady state leaves remaining marked

theorem cap_marks_ready_memory (state next : MachineState)
    (leaves remaining : Nat) (marked : Nat → Bool)
    (memory : next.mem = state.mem)
    (ready : CapMarksReady state leaves remaining marked) :
    CapMarksReady next leaves remaining marked := by
  intro node lower upper
  exact (congrFun memory (capMarkAddress node)).trans (ready node lower upper)

theorem cap_mark_one_iff (leaves : Nat) (positive : 0 < leaves) :
    (leaves - 1 = 0) ↔ leaves = 1 := by omega

theorem cap_mark_ready_transport (marks : Reg) (start : Word)
    (state next : MachineState) (leaves node : Nat) (marked : Nat → Bool)
    (bounded : leaves ≤ 256) (positive : 0 < node) (internal : node < leaves)
    (equation : marked node = (marked (2 * node) || marked (2 * node + 1)))
    (ready : CapMarksReady state leaves node marked)
    (base : next.getReg marks = 28672)
    (index : next.getReg .x20 = BitVec.ofNat 64 (node - 1))
    (pc : next.pc = if node = 1 then start + 40 else start)
    (memory : next.mem = (capMarkWrite state node).mem) :
    CapMarkLoopReady marks start next leaves (node - 1) marked := by
  refine ⟨base, index, ?_, ?_⟩
  · have boundary : (node - 1 = 0) ↔ node = 1 := by omega
    simpa only [boundary] using pc
  · have finalized := cap_marks_ready_next state leaves node marked bounded positive
      internal equation ready
    intro other lower upper
    exact (congrFun memory (capMarkAddress other)).trans (finalized other lower upper)

end CommitGolfCandidate
