import CommitGolfCandidate.TwoPermutationGroupLatch

/-! Exact execution of the production commitment's entire leaf phase. Every
group includes its two cursor updates and the fetched heap-end branch. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
attribute [local irreducible] execute

def batchTrace (g : Nat) (s : MachineState) : OracleComp World MachineState := do
  let done ← groupTrace g 16 0 s
  return afterGroup done g

theorem execute_leaf_batch (g fuel : Nat) (s : MachineState) (bound : g < 2^20)
    (regs : GroupRegs s g 0) (stop : s.getReg .x21 = wordAddress (leafDest (2^24))) (coins : Bool) :
    execute commitImage (243+fuel) s coins =
      (do let next ← batchTrace g s
          let result ← execute commitImage fuel next coins
          return result.charge 467 32) := by
  rw [show 243+fuel=15*16+(3+fuel) by omega,
    execute_group_segment g 16 0 s bound (by decide) regs]
  simp only [batchTrace,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro done reached
  have r := group_trace_regs g 16 0 s bound (by decide) regs reached
  have last := (group_preserved_reg g 16 0 s .x21 (by decide) (by decide) (by decide) reached).trans stop
  rw [group_latch_run done g fuel bound r last]
  simp [Execution.charge,bind_assoc,←Nat.add_assoc] <;> rfl

theorem batch_next (g : Nat) (s : MachineState) (bound : g < 2^20) (regs : GroupRegs s g 0)
    (stop : s.getReg .x21 = wordAddress (leafDest (2^24))) {done : MachineState}
    (hit : done ∈ support (batchTrace g s)) :
    (g+1 < 2^20 → GroupRegs done (g+1) 0) ∧
    done.getReg .x21 = wordAddress (leafDest (2^24)) ∧ done.pc = nextPC g := by
  simp only [batchTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨middle,reached,rfl⟩ := hit
  have body := group_trace_regs g 16 0 s bound (by decide) regs reached
  have last := (group_preserved_reg g 16 0 s .x21 (by decide) (by decide) (by decide) reached).trans stop
  exact ⟨fun more => group_latch_next middle g more body,last,rfl⟩

def leavesTrace : Nat → Nat → MachineState → OracleComp World MachineState
  | 0, _, s => pure s
  | n+1, g, s => do
    let middle ← batchTrace g s
    leavesTrace n (g+1) middle

theorem execute_leaf_batches (groups g : Nat) (s : MachineState) (limit : g+groups ≤ 2^20)
    (regs : 0<groups → GroupRegs s g 0) (stop : s.getReg .x21 = wordAddress (leafDest (2^24)))
    (fuel : Nat) (coins : Bool) :
    execute commitImage (243*groups+fuel) s coins =
      (do let done ← leavesTrace groups g s
          let result ← execute commitImage fuel done coins
          return result.charge (467*groups) (32*groups)) := by
  induction groups generalizing g s with
  | zero => simp [leavesTrace,Execution.charge]
  | succ n ih =>
    have valid := regs (by omega)
    rw [show 243*(n+1)+fuel=243+(243*n+fuel) by omega,
      execute_leaf_batch g _ s (by omega) valid stop]
    simp only [leavesTrace,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro mid reached
    obtain ⟨next,ending,_⟩ := batch_next g s (by omega) valid stop reached
    rw [ih (g+1) mid (by omega) (fun more => next (by omega)) ending]
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem production_leaf_execution (s : MachineState) (regs : GroupRegs s 0 0)
    (stop : s.getReg .x21 = wordAddress (leafDest (2^24))) (fuel : Nat) :
    execute commitImage (254803968+fuel) s true =
      (do let done ← leavesTrace (2^20) 0 s
          let result ← execute commitImage fuel done true
          return result.charge 489684992 33554432) :=
  execute_leaf_batches (2^20) 0 s (by decide) (fun _ => regs) stop fuel true

end TwoPermutationPrototype.RV64
