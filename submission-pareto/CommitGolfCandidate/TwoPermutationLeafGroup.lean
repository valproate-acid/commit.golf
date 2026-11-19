import CommitGolfCandidate.TwoPermutationLeafAdvance

/-! Compose the 16 concrete leaf sequences in one group, preserving their
state-dependent queries and exact machine cost for every reply sequence. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
attribute [local irreducible] execute leafTrace

def slotTrace (s : MachineState) (g u : Nat) : OracleComp World MachineState :=
  let i := 16*g+u
  leafTrace s (groupSlot u) (leafStart i) i (leafDest i)

def groupTrace (g : Nat) : Nat → Nat → MachineState → OracleComp World MachineState
  | 0, _, s => pure s
  | k+1, u, s => do
    let next ← slotTrace s g u
    groupTrace g k (u+1) next

theorem single_slot (s : MachineState) (g u fuel : Nat) (bound : g < 2^20) (hu : u < 16)
    (regs : GroupRegs s g u) (coins : Bool) :
    execute commitImage (15+fuel) s coins =
      (do let next ← slotTrace s g u
          let result ← execute commitImage fuel next coins
          return result.charge 29 2) := by
  have prod := group_prod_regs regs hu
  have ready := production_leaf_ready s g (groupSlot u) bound prod
  have run := execute_two_permutation_leaf _ _ _ _ _ _ fuel ready prod.pc coins
  have same : (groupSlot u).val=u := Nat.mod_eq_of_lt hu
  simpa only [same,slotTrace] using run

theorem execute_group_segment (g count u : Nat) (s : MachineState) (bound : g < 2^20)
    (inside : u+count ≤ 16) (regs : GroupRegs s g u) (fuel : Nat) (coins : Bool) :
    execute commitImage (15*count+fuel) s coins =
      (do let finished ← groupTrace g count u s
          let result ← execute commitImage fuel finished coins
          return result.charge (29*count) (2*count)) := by
  induction count generalizing u s with
  | zero => simp [groupTrace, Execution.charge]
  | succ k ih =>
    rw [show 15*(k+1)+fuel = 15+(15*k+fuel) by omega,
      single_slot s g u _ bound (by omega) regs coins]
    simp only [groupTrace,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next hit
    rw [ih (u+1) next (by omega) (trace_advance_regs bound (by omega) regs hit)]
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem group_trace_regs (g count u : Nat) (s : MachineState) (bound : g < 2^20)
    (inside : u+count ≤ 16) (regs : GroupRegs s g u) {done : MachineState}
    (hit : done ∈ support (groupTrace g count u s)) : GroupRegs done g (u+count) := by
  induction count generalizing u s with
  | zero =>
    simp only [groupTrace,support_pure,Set.mem_singleton_iff] at hit
    simpa [hit] using regs
  | succ k ih =>
    simp only [groupTrace,mem_support_bind_iff] at hit
    obtain ⟨next,step,tail⟩ := hit
    rw [show u+(k+1)=u+1+k by omega]
    exact ih (u+1) next (by omega) (trace_advance_regs bound (by omega) regs step) tail

end TwoPermutationPrototype.RV64
