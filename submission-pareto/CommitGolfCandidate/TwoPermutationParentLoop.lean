import CommitGolfCandidate.TwoPermutationParentFetch

/-! Exact execution of the 127-parent prefix and each 128-parent batch. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute parentAfter

def parentsTrace (remaining : Nat) : Nat → MachineState → OracleComp World MachineState
  | 0, s => pure s
  | k+1, s => do
    let answer ← (liftM (World.query (.inr (.inl (parentInput s (remaining+(k+1)))))) : OracleComp World (BitVec 256))
    parentsTrace remaining k (parentAfter s (remaining+(k+1)) answer)

theorem parents_segment (rem count slot fuel : Nat) (s : MachineState)
    (bound : rem+count < 2^24) (inside : slot+count ≤ 255)
    (r : ParentRegs s (rem+count)) (pc : s.pc=parentPC slot) :
    execute commitImage (3*count+fuel) s true =
      (do let mid ← parentsTrace rem count s
          let result ← execute commitImage fuel mid true
          return result.charge (10*count) count) := by
  induction count generalizing slot s with
  | zero => simp [parentsTrace,Execution.charge]
  | succ k ih =>
    rw [show 3*(k+1)+fuel=3+(3*k+fuel) by omega,parent_triple s _ _ _ pc bound r (parent_fetched slot (by omega))]
    simp only [parentsTrace,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro answer _
    have r' := next_parent_regs s (rem+k) answer (by simpa only [Nat.add_assoc] using r)
    have pc' := (parent_pc s (rem+(k+1)) answer).trans ((congrArg (·+12) pc).trans (parent_pc_next slot))
    rw [ih (slot+1) _ (by omega) (by omega) (by simpa only [Nat.add_assoc] using r') pc']
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem parents_post (rem count slot : Nat) (s : MachineState)
    (r : ParentRegs s (rem+count)) (pc : s.pc=parentPC slot)
    {out : MachineState} (hit : out ∈ support (parentsTrace rem count s)) :
    ParentRegs out rem ∧ out.pc=parentPC (slot+count) := by
  induction count generalizing slot s with
  | zero =>
    simp only [parentsTrace,support_pure,Set.mem_singleton_iff] at hit
    subst out; exact ⟨r,pc⟩
  | succ k ih =>
    simp only [parentsTrace,mem_support_bind_iff] at hit
    obtain ⟨answer,_,reach⟩ := hit
    have r' := next_parent_regs s (rem+k) answer (by simpa only [Nat.add_assoc] using r)
    have pc' := (parent_pc s (rem+(k+1)) answer).trans ((congrArg (·+12) pc).trans (parent_pc_next slot))
    rw [show slot+(k+1)=slot+1+k by omega]
    exact ih (slot+1) _ (by simpa only [Nat.add_assoc] using r') pc' reach

def parentNextPC (rem : Nat) : Word := if rem=0 then 8216 else 6676

theorem parent_latch (rem fuel : Nat) (s : MachineState) (limit : rem<2^24)
    (r : ParentRegs s rem) (pc : s.pc=8212) :
    execute commitImage (1+fuel) s true =
      (do let result ← execute commitImage fuel (s.setPC (parentNextPC rem)) true
          return result.charge 1 0) := by
  have equal : s.getReg .x12=s.getReg .x9 ↔ rem=0 := by
    rw [r.target,r.heap]
    constructor
    · intro same
      have h := wordAddress_injective_of_bound (a := treeWord rem) (b := treeWord 0)
        (by unfold treeWord;omega) (by decide) same
      unfold treeWord at h;omega
    · rintro rfl;rfl
  have fetched : fetch commitImage s=some (.base (.BNE .x12 .x9 6656)) := by rw [fetch,pc];rfl
  have step : ordinaryStep s (.base (.BNE .x12 .x9 6656))=some (s.setPC (parentNextPC rem)) := by
    change some (if s.getReg .x12 != s.getReg .x9 then s.setPC (s.pc+signExtend13 6656) else s.setPC (s.pc+4)) = _
    simp only [bne_iff_ne,pc,parentNextPC]
    by_cases last : rem=0
    · rw [if_neg (not_not_intro (equal.mpr last)),if_pos last];rfl
    · rw [if_pos (fun h => last (equal.mp h)),if_neg last];rfl
  rw [Nat.add_comm 1 fuel,CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ fetched step]; rfl

def parentBatch (rem : Nat) (s : MachineState) : OracleComp World MachineState := do
  let body ← parentsTrace rem 128 s
  return body.setPC (parentNextPC rem)

theorem parent_batch (rem fuel : Nat) (s : MachineState) (bound : rem+128<2^24)
    (r : ParentRegs s (rem+128)) (pc : s.pc=6676) :
    execute commitImage (385+fuel) s true =
      (do let mid ← parentBatch rem s
          let result ← execute commitImage fuel mid true
          return result.charge 1281 128) := by
  rw [show 385+fuel=3*128+(1+fuel) by omega,parents_segment rem 128 127 _ s bound (by decide) r pc]
  simp only [parentBatch,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro body reached
  obtain ⟨regs,ending⟩ := parents_post rem 128 127 s r pc reached
  rw [parent_latch rem fuel body (by omega) regs ending]
  simp [Execution.charge,←Nat.add_assoc]

theorem parent_batch_post (rem : Nat) (s : MachineState) (r : ParentRegs s (rem+128)) (pc : s.pc=6676)
    {out : MachineState} (hit : out ∈ support (parentBatch rem s)) :
    ParentRegs out rem ∧ out.pc=parentNextPC rem := by
  simp only [parentBatch,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨body,reach,rfl⟩ := hit
  obtain ⟨regs,_⟩ := parents_post rem 128 127 s r pc reach
  exact ⟨⟨regs.source,regs.target,regs.selector,regs.size,regs.primitive,regs.heap⟩,rfl⟩

def parentBatches : Nat → MachineState → OracleComp World MachineState
  | 0, s => pure s
  | k+1, s => do
    let next ← parentBatch (128*k) s
    parentBatches k next

theorem parent_batches (groups fuel : Nat) (s : MachineState) (bound : 128*groups<2^24)
    (r : ParentRegs s (128*groups)) (pc : 0<groups → s.pc=6676) :
    execute commitImage (385*groups+fuel) s true =
      (do let out ← parentBatches groups s
          let result ← execute commitImage fuel out true
          return result.charge (1281*groups) (128*groups)) := by
  induction groups generalizing s with
  | zero => simp [parentBatches,Execution.charge]
  | succ k ih =>
    rw [Nat.mul_succ] at r bound
    rw [show 385*(k+1)+fuel=385+(385*k+fuel) by omega,parent_batch (128*k) _ s bound r (pc (by omega))]
    simp only [parentBatches,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    obtain ⟨regs,back⟩ := parent_batch_post _ s r (pc (by omega)) reached
    rw [ih next (by omega) regs (fun positive => by rw [back,parentNextPC,if_neg (by omega)])]
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

def fullParents (s : MachineState) : OracleComp World MachineState := do
  let first ← parentsTrace (128*131071) 127 s
  parentBatches 131071 first

theorem entire_parent_phase (s : MachineState) (fuel : Nat)
    (r : ParentRegs s (2^24-1)) (pc : s.pc=5152) :
    execute commitImage (50462716+fuel) s true =
      (do let out ← fullParents s
          let result ← execute commitImage fuel out true
          return result.charge 167903221 16777215) := by
  rw [show 50462716+fuel=3*127+(385*131071+fuel) by omega,
    parents_segment (128*131071) 127 0 _ s (by decide) (by decide) r pc]
  simp only [fullParents,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro first reached
  obtain ⟨regs,back⟩ := parents_post (128*131071) 127 0 s r pc reached
  rw [parent_batches 131071 fuel first (by decide) regs (fun _ => back)]
  simp [Execution.charge,←Nat.add_assoc]

end TwoPermutationPrototype.RV64
