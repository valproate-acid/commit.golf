import CommitGolfCandidate.TwoPermutationPackedLeafGroups
import CommitGolfCandidate.TwoPermutationPackedCommit

namespace TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute packedWideCommitImage

def latchPC (g : Nat) : Word := if g+1=2^12 then 184784 else 4168
def latchCost (g : Nat) := if g+1=2^12 then 1 else 2

theorem latch_run (s : MachineState) (g fuel : Nat) (bound : g<2^12) (r : Regs s g 4096)
    (stop : s.getReg .x21=wordAddress (leafDest (2^24))) :
    execute packedWideCommitImage (latchCost g+fuel) s true =
      (do let y ← execute packedWideCommitImage fuel (s.setPC (latchPC g)) true
          return y.charge (latchCost g) 0) := by
  have here : s.pc=184776 := r.pc
  have eq : s.getReg .x20=s.getReg .x21 ↔ g+1=2^12 := by
    rw [r.heap,stop]
    constructor
    · intro h
      have j := wordAddress_injective_of_bound (a := heapBase g 4096) (b := leafDest (2^24))
        (by unfold heapBase leafDest;omega) (by decide) h
      unfold heapBase leafDest at j;omega
    · intro h
      apply congrArg wordAddress
      unfold heapBase leafDest
      omega
  by_cases last : g+1=2^12
  · have step : ordinaryStep s (.base (.BEQ .x20 .x21 8))=some (s.setPC 184784) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,here,eq.mpr last,signExtend13]
    rw [latchCost,if_pos last,latchPC,if_pos last,Nat.add_comm 1 fuel,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (packed_wide_fetch_leaf_branch s here) step];rfl
  · let middle := s.setPC 184780
    have diff : s.getReg .x20≠s.getReg .x21 := fun h => last (eq.mp h)
    have step : ordinaryStep s (.base (.BEQ .x20 .x21 8))=some middle := by
      simp [middle,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,here,diff]
    have jump : ordinaryStep middle (.base (.JAL .x0 1916540))=some (s.setPC 4168) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,middle,MachineState.setReg,MachineState.setPC]
      rfl
    rw [latchCost,if_neg last,latchPC,if_neg last,show 2+fuel=(fuel+1)+1 by omega,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (packed_wide_fetch_leaf_branch s here) step,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (packed_wide_fetch_leaf_loop middle rfl) jump]
    simp [instructionCycles,Execution.charge,←Nat.add_assoc]

theorem latch_next (s : MachineState) (g : Nat) (more : g+1<2^12) (r : Regs s g 4096) :
    Regs (s.setPC (latchPC g)) (g+1) 0 := by
  have source : 4096*(g+1)+0=4096*g+4096 := by omega
  refine ⟨?_,?_,?_,r.stride,r.selector,r.size,r.primitive,?_⟩
  · change s.getReg .x10=wordAddress (leafStart _+5);rw [source];exact r.source
  · change s.getReg .x20=wordAddress (heapBase _ _);rw [r.heap];unfold heapBase;rw [show 4096*g+64*(4096/64)=4096*(g+1)+64*(0/64) by omega]
  · change s.getReg .x22=wordAddress (nonceBase _ _);rw [r.salts];unfold nonceBase;rw [show 4096*g+128*(4096/128)=4096*(g+1)+128*(0/128) by omega]
  · change latchPC g=_;rw [latchPC,if_neg (by omega)];rfl

def batch (g : Nat) (s : MachineState) : OracleComp World MachineState := do
  let body ← group g 4096 0 s
  return body.setPC (latchPC g)

theorem batch_run (s : MachineState) (g fuel : Nat) (bound : g<2^12) (r : Regs s g 0)
    (stop : s.getReg .x21=wordAddress (leafDest (2^24))) :
    execute packedWideCommitImage (45152+latchCost g+fuel) s true =
      (do let next ← batch g s
          let result ← execute packedWideCommitImage fuel next true
          return result.charge (102496+latchCost g) 8192) := by
  rw [show 45152+latchCost g+fuel=span 11 0 4096+(latchCost g+fuel) by change 45152+_+_=45152+(_+_);omega,
    group_run s g 4096 0 _ bound (by decide) r]
  simp only [batch,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro body reached
  have regs := group_post s g 4096 0 bound (by decide) r reached
  have endReg := (group_saved s g 4096 0 .x21 (by simp [SavedReg]) reached).trans stop
  rw [latch_run body g fuel bound regs endReg]
  simp [span,progress,Execution.charge,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem batch_post (s : MachineState) (g : Nat) (bound : g<2^12) (r : Regs s g 0)
    {next : MachineState} (hit : next ∈ support (batch g s)) :
    (g+1<2^12 → Regs next (g+1) 0) ∧ next.pc=latchPC g ∧
    ∀ reg, SavedReg reg → next.getReg reg=s.getReg reg := by
  simp only [batch,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨body,reach,rfl⟩ := hit
  refine ⟨fun more => latch_next body g more (group_post s g 4096 0 bound (by decide) r reach),rfl,?_⟩
  intro reg safe
  exact group_saved s g 4096 0 reg safe (next := body) reach

def groups : Nat → Nat → MachineState → OracleComp World MachineState
  | 0,_,s => pure s
  | k+1,g,s => do
    let mid ← batch g s
    groups k (g+1) mid

theorem groups_run (s : MachineState) (cnt g fuel : Nat) (limit : g+cnt=2^12)
    (r : 0<cnt → Regs s g 0) (stop : s.getReg .x21=wordAddress (leafDest (2^24))) :
    execute packedWideCommitImage ((45154*cnt-1)+fuel) s true =
      (do let next ← groups cnt g s
          let result ← execute packedWideCommitImage fuel next true
          return result.charge (102498*cnt-1) (8192*cnt)) := by
  induction cnt generalizing g s with
  | zero => simp [groups,Execution.charge]
  | succ k ih =>
    have last : (45154*(k+1)-1)=45152+latchCost g+(45154*k-1) ∧
        (102498*(k+1)-1)=102496+latchCost g+(102498*k-1) := by
      unfold latchCost;split <;> constructor <;> omega
    have valid := r (by omega)
    rw [last.1,Nat.add_assoc (45152+latchCost g),batch_run s g _ (by omega) valid stop]
    simp only [groups,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    obtain ⟨regs,_,keep⟩ := batch_post s g (by omega) valid reached
    rw [ih next (g+1) (by omega) (fun more => regs (by omega)) ((keep .x21 (by simp [SavedReg])).trans stop), last.2]
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem groups_post (s : MachineState) (cnt g : Nat) (limit : g+cnt=2^12)
    (r : Regs s g 0) (positive : 0<cnt) {out : MachineState} (hit : out ∈ support (groups cnt g s)) :
    out.pc=184784 ∧ ∀ reg, SavedReg reg → out.getReg reg=s.getReg reg := by
  induction cnt generalizing g s with
  | zero => omega
  | succ k ih =>
    simp only [groups,mem_support_bind_iff] at hit
    obtain ⟨mid,step,reach⟩ := hit
    obtain ⟨regs,pc,keep⟩ := batch_post s g (by omega) r step
    cases k with
    | zero =>
      simp only [groups,support_pure,Set.mem_singleton_iff] at reach;subst out
      exact ⟨by rw [pc,latchPC,if_pos (by omega)],keep⟩
    | succ k =>
      obtain ⟨finish,rest⟩ := ih mid (g+1) (by omega) (regs (by omega)) (by omega) reach
      exact ⟨finish,fun reg h => (rest reg h).trans (keep reg h)⟩

theorem entry_regs (s : MachineState) (entry : CommitEntry s) {bits : Nat} (coins : BitVec bits) :
    Regs (packed_wideReadyState s coins) 0 0 ∧ (packed_wideReadyState s coins).getReg .x21=wordAddress (leafDest (2^24)) := by
  obtain ⟨base,stop,_⟩ := post_random_regs s entry coins
  obtain ⟨pc,stride⟩ := packed_wide_ready_state_entry s entry coins
  have save := packed_wide_ready_state_register s coins
  exact ⟨⟨by rw [packed_wide_ready_source,base.source];rfl,(save .x20 (by decide)).trans base.heap,
    (save .x22 (by decide)).trans base.salts,stride,(save .x5 (by decide)).trans base.selector,
    (save .x11 (by decide)).trans base.size,(save .x13 (by decide)).trans base.primitive,pc⟩,
    (save .x21 (by decide)).trans stop⟩

def executableLeaves : PackedLeafExecution where
  trace := groups (2^12) 0
  executes s entry _ coins fuel := groups_run _ (2^12) 0 fuel (by decide) (fun _ => (entry_regs s entry coins).1)
    (entry_regs s entry coins).2
  finished s entry _ coins out hit := by
    obtain ⟨pc,keep⟩ := groups_post _ (2^12) 0 (by decide) (entry_regs s entry coins).1 (by decide) hit
    obtain ⟨g,stop,x8,x9,x19⟩ := post_random_regs s entry coins
    have held (reg : Reg) (safe : SavedReg reg) (diff : reg ∉ [Reg.x7,.x10]) :=
      (keep reg safe).trans (packed_wide_ready_state_register s coins reg diff)
    exact ⟨pc,(held .x5 (by simp [SavedReg]) (by decide)).trans g.selector,
      (held .x9 (by simp [SavedReg]) (by decide)).trans x9,(held .x19 (by simp [SavedReg]) (by decide)).trans x19,
      (held .x21 (by simp [SavedReg]) (by decide)).trans stop,(held .x8 (by simp [SavedReg]) (by decide)).trans x8⟩

end TwoPermutationPrototype.RV64.PackedLeaves
