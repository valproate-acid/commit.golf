import CommitGolfCandidate.QuadCommitLeafRebase

namespace TwoPermutationPrototype.Quad.Commit.Leaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] execute image

def posSlot (u : Nat) : Fin 4096 := ⟨u%4096,Nat.mod_lt _ (by decide)⟩
def unitTrace (s : MachineState) (g u : Nat) : OracleComp World MachineState := do
  let i := 4095*g+u
  let raw ← leafTrace s (posSlot u) (leafStart i) i (leafDest i)
  return rebased raw u

def group (g : Nat) : Nat → Nat → MachineState → OracleComp World MachineState
  | 0,_,s => pure s
  | k+1,u,s => do
    let mid ← unitTrace s g u
    group g k (u+1) mid

def progress (cost u : Nat) := cost*u+u/45+(u+128)/256+(if 4096≤u then 1 else 0)
def span (cost u k : Nat) := progress cost (u+k)-progress cost u

theorem span_step (cost u k : Nat) (inside : u+(k+1)≤4096) :
    span cost u (k+1) = cost + extra u + span cost (u+1) k := by
  have mono (a b : Nat) (h : a≤b) : progress cost a≤progress cost b := by
    have mul := Nat.mul_le_mul_left cost h
    unfold progress
    split <;> split <;> omega
  have a := mono u (u+1) (by omega)
  have b := mono (u+1) (u+1+k) (by omega)
  have inc : progress cost (u+1)=progress cost u+cost+extra u := by
    have count := extra_count u (by omega)
    unfold progress
    rw [Nat.mul_succ]
    by_cases last : u+1=4096
    · rw [if_pos (by omega),if_neg (by omega)]
      rw [if_pos last] at count
      omega
    · rw [if_neg (by omega),if_neg (by omega)]
      rw [if_neg last] at count
      omega
  unfold span
  rw [show u+(k+1)=u+1+k by omega]
  omega

theorem raw_post (s : MachineState) (g : Nat) (u : Fin 4096) (bound : g<4097) (r : Regs s g u.val)
    {raw : MachineState} (reach : raw ∈ support (leafTrace s u (leafStart (idx g u)) (idx g u) (leafDest (idx g u)))) :
    RawRegs raw g u := by
  simp only [leafTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reach
  obtain ⟨a,_,b,_,rfl⟩ := reach
  exact post_slot s g u bound r a b

theorem unit_run (s : MachineState) (g u fuel : Nat) (bound : g<4097) (hu : u<4096) (r : Regs s g u) :
    execute image (11+extra u+fuel) s true =
      (do let next ← unitTrace s g u
          let result ← execute image fuel next true
          return result.charge (25+extra u) 2) := by
  let slot := posSlot u
  have eq : slot.val=u := Nat.mod_eq_of_lt hu
  have ru : Regs s g slot.val := by rw [eq];exact r
  have ready := ready_slot s g slot bound ru
  rw [show 11+extra u+fuel=11+(extra u+fuel) by omega,execute_two_permutation_leaf _ _ _ _ _ _ _ ready ru.pc]
  simp only [unitTrace,bind_assoc,pure_bind]
  simp only [idx,eq]
  apply bind_congr_of_forall_mem_support
  intro raw hit
  have h : RawRegs raw g slot := raw_post s g slot bound ru (by simpa only [idx,eq] using hit)
  have reb := rebase_run raw slot h.pc fuel
  rw [eq] at reb
  rw [reb]
  simp [Execution.charge,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem unit_post (s : MachineState) (g u : Nat) (bound : g<4097) (hu : u<4096) (r : Regs s g u)
    {next : MachineState} (hit : next ∈ support (unitTrace s g u)) : Regs next g (u+1) := by
  simp only [unitTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨raw,step,rfl⟩ := hit
  have eq : (posSlot u).val=u := Nat.mod_eq_of_lt hu
  have hold := raw_post s g (posSlot u) bound (by simpa only [eq] using r) (by simpa only [idx,eq] using step)
  simpa only [eq] using rebase_regs raw g (posSlot u) hold

theorem group_run (s : MachineState) (g cnt u fuel : Nat) (bound : g<4097) (inside : u+cnt≤4096) (r : Regs s g u) :
    execute image (span 11 u cnt+fuel) s true =
      (do let next ← group g cnt u s
          let result ← execute image fuel next true
          return result.charge (span 25 u cnt) (2*cnt)) := by
  induction cnt generalizing s u with
  | zero => simp [group,span,Execution.charge]
  | succ k ih =>
    rw [span_step 11 u k inside,span_step 25 u k inside,Nat.add_assoc (11+extra u),unit_run s g u _ bound (by omega) r]
    simp only [group,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    rw [ih next (u+1) (by omega) (unit_post s g u bound (by omega) r reached)]
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem group_post (s : MachineState) (g cnt u : Nat) (bound : g<4097) (inside : u+cnt≤4096) (r : Regs s g u)
    {next : MachineState} (hit : next ∈ support (group g cnt u s)) : Regs next g (u+cnt) := by
  induction cnt generalizing s u with
  | zero => simp only [group,support_pure,Set.mem_singleton_iff] at hit;rw [hit];exact r
  | succ k ih =>
    simp only [group,mem_support_bind_iff] at hit
    obtain ⟨mid,step,reach⟩ := hit
    rw [show u+(k+1)=u+1+k by omega]
    exact ih mid (u+1) (by omega) (unit_post s g u bound (by omega) r step) reach

theorem rebased_dest (s : MachineState) (u : Nat) : (rebased s u).getReg .x12=s.getReg .x12 := by
  unfold rebased; split <;> split <;> split <;> rfl

theorem unit_dest (s : MachineState) (g u : Nat) (bound : g<4097) (hu : u<4096) (r : Regs s g u)
    {next : MachineState} (hit : next ∈ support (unitTrace s g u)) :
    next.getReg .x12=wordAddress (leafDest (4095*g+u)) := by
  simp only [unitTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨raw,step,rfl⟩ := hit
  have eq : (posSlot u).val=u := Nat.mod_eq_of_lt hu
  have hold := raw_post s g (posSlot u) bound (by simpa only [eq] using r) (by simpa only [idx,eq] using step)
  rw [rebased_dest,hold.dest]
  simp only [idx,eq]

theorem group_dest (s : MachineState) (g cnt u : Nat) (bound : g<4097) (inside : u+(cnt+1)≤4096) (r : Regs s g u)
    {next : MachineState} (hit : next ∈ support (group g (cnt+1) u s)) :
    next.getReg .x12=wordAddress (leafDest (4095*g+(u+cnt))) := by
  induction cnt generalizing s u with
  | zero =>
    simp only [group,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
    obtain ⟨mid,step,rfl⟩ := hit
    simpa using unit_dest s g u bound (by omega) r step
  | succ k ih =>
    rw [group,mem_support_bind_iff] at hit
    obtain ⟨mid,step,reach⟩ := hit
    have := ih mid (u+1) (by omega) (unit_post s g u bound (by omega) r step) reach
    rw [this]
    congr 3
    omega

def SavedReg (reg : Reg) := reg ∈ [Reg.x5,.x8,.x9,.x11,.x13,.x19,.x21]

theorem rebased_saved (s : MachineState) (u : Nat) (reg : Reg) (safe : SavedReg reg) :
    (rebased s u).getReg reg=s.getReg reg := by
  simp only [SavedReg,List.mem_cons,List.not_mem_nil,or_false] at safe
  rcases safe with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold rebased <;> split <;> split <;> split <;> rfl

theorem unit_saved (s : MachineState) (g u : Nat) (reg : Reg) (safe : SavedReg reg)
    {next : MachineState} (hit : next ∈ support (unitTrace s g u)) : next.getReg reg=s.getReg reg := by
  simp only [unitTrace,leafTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨raw,⟨a,_,b,_,rfl⟩,rfl⟩ := hit
  rw [rebased_saved _ _ _ safe]
  apply finished_reg_frame
  all_goals simp only [SavedReg,List.mem_cons,List.not_mem_nil,or_false] at safe
  all_goals rcases safe with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem group_saved (s : MachineState) (g cnt u : Nat) (reg : Reg) (safe : SavedReg reg)
    {next : MachineState} (hit : next ∈ support (group g cnt u s)) : next.getReg reg=s.getReg reg := by
  induction cnt generalizing u s with
  | zero => simp only [group,support_pure,Set.mem_singleton_iff] at hit;rw [hit]
  | succ k ih =>
    simp only [group,mem_support_bind_iff] at hit
    obtain ⟨mid,step,reach⟩ := hit
    exact (ih mid (u+1) reach).trans (unit_saved s g u reg safe step)

end TwoPermutationPrototype.Quad.Commit.Leaves
