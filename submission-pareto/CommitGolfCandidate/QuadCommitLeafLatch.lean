import CommitGolfCandidate.QuadCommitLeafGroups
import CommitGolfCandidate.QuadCommitFetch

namespace TwoPermutationPrototype.Quad.Commit.Leaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute image

def latchPC (g : Nat) : Word := if g+1=4097 then 184900 else 4216
def latchCost (g : Nat) := if g+1=4097 then 1 else 2

theorem latch_run (s : MachineState) (g fuel : Nat) (bound : g<4097) (r : Regs s g 4096)
    (stop : s.getReg .x8=wordAddress (leafStart (2^24)+5)) :
    execute image (latchCost g+fuel) s true =
      (do let y ← execute image fuel (s.setPC (latchPC g)) true
          return y.charge (latchCost g) 0) := by
  have here : s.pc=184828 := by rw [r.pc,leaf_body_end];rfl
  have eq : s.getReg .x10=s.getReg .x8 ↔ g+1=4097 := by
    rw [r.source,stop]
    constructor
    · intro h
      have j := wordAddress_injective_of_bound
        (a := leafStart (4095*g+4096)+5) (b := leafStart (2^24)+5)
        (by unfold leafStart;omega) (by decide) h
      unfold leafStart at j
      omega
    · intro h
      apply congrArg wordAddress
      congr 2
      omega
  by_cases last : g+1=4097
  · have step : ordinaryStep s (.base (.BEQ .x10 .x8 72))=some (s.setPC 184900) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,here,eq.mpr last,signExtend13]
    rw [latchCost,if_pos last,latchPC,if_pos last,Nat.add_comm 1 fuel,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_leaf_latch s here) step];rfl
  · let middle := s.setPC 184832
    have diff : s.getReg .x10≠s.getReg .x8 := fun h => last (eq.mp h)
    have step : ordinaryStep s (.base (.BEQ .x10 .x8 72))=some middle := by
      simp [middle,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,here,diff]
    have jump : ordinaryStep middle (.base (.JAL .x0 1916536))=some (s.setPC 4216) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,middle,MachineState.setReg,MachineState.setPC]
      rfl
    rw [latchCost,if_neg last,latchPC,if_neg last,show 2+fuel=(fuel+1)+1 by omega,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_leaf_latch s here) step,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_leaf_jump middle rfl) jump]
    simp [instructionCycles,Execution.charge,←Nat.add_assoc]

theorem latch_next (s : MachineState) (g : Nat) (more : g+1<4097) (r : Regs s g 4096) :
    Regs (s.setPC (latchPC g)) (g+1) 1 := by
  have source : 4095*(g+1)+1=4095*g+4096 := by omega
  refine ⟨?_,?_,?_,r.stride,r.selector,r.size,r.primitive,?_⟩
  · change s.getReg .x10=wordAddress (leafStart _+5);rw [source];exact r.source
  · change s.getReg .x20=wordAddress (heapBase _ _)
    rw [r.heap]
    apply congrArg wordAddress
    unfold heapBase windowWord
    rw [show 4095*g+45*(4096/45)=4095*(g+1)+45*(1/45) by omega]
  · change s.getReg .x22=wordAddress (nonceBase _ _);rw [r.salts]
    apply congrArg wordAddress
    unfold nonceBase
    rw [if_pos rfl,if_neg (by omega),show 4095*g+4095=4095*(g+1)+256*((1+128)/256) by omega]
  · change latchPC g=_;rw [latchPC,if_neg (by omega)];rfl

/-- One pass of the loop: leaves 1 .. 4095 of the unrolled body, then the latch. -/
def batch (g : Nat) (s : MachineState) : OracleComp World MachineState := do
  let body ← group g 4095 1 s
  return body.setPC (latchPC g)

theorem batch_run (s : MachineState) (g fuel : Nat) (bound : g<4097) (r : Regs s g 1)
    (stop : s.getReg .x8=wordAddress (leafStart (2^24)+5)) :
    execute image (45153+latchCost g+fuel) s true =
      (do let next ← batch g s
          let result ← execute image fuel next true
          return result.charge (102483+latchCost g) 8190) := by
  rw [show 45153+latchCost g+fuel=span 11 1 4095+(latchCost g+fuel) by change 45153+_+_=45153+(_+_);omega,
    group_run s g 4095 1 _ bound (by decide) r]
  simp only [batch,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro body reached
  have regs := group_post s g 4095 1 bound (by decide) r reached
  have endReg := (group_saved s g 4095 1 .x8 (by simp [SavedReg]) reached).trans stop
  rw [latch_run body g fuel bound regs endReg]
  simp [span,progress,Execution.charge,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem batch_post (s : MachineState) (g : Nat) (bound : g<4097) (r : Regs s g 1)
    {next : MachineState} (hit : next ∈ support (batch g s)) :
    (g+1<4097 → Regs next (g+1) 1) ∧ next.pc=latchPC g ∧
    (g+1=4097 → next.getReg .x12=wordAddress (leafDest (4095*g+4095))) ∧
    ∀ reg, SavedReg reg → next.getReg reg=s.getReg reg := by
  simp only [batch,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨body,reach,rfl⟩ := hit
  have regs := group_post s g 4095 1 bound (by decide) r reach
  refine ⟨fun more => latch_next body g more regs,rfl,fun _ => ?_,?_⟩
  · change body.getReg .x12=_
    simpa using group_dest s g 4094 1 bound (by decide) r reach
  · intro reg safe
    exact group_saved s g 4095 1 reg safe (next := body) reach

def groups : Nat → Nat → MachineState → OracleComp World MachineState
  | 0,_,s => pure s
  | k+1,g,s => do
    let mid ← batch g s
    groups k (g+1) mid

theorem groups_run (s : MachineState) (cnt g fuel : Nat) (limit : g+cnt=4097)
    (r : 0<cnt → Regs s g 1) (stop : s.getReg .x8=wordAddress (leafStart (2^24)+5)) :
    execute image ((45155*cnt-1)+fuel) s true =
      (do let next ← groups cnt g s
          let result ← execute image fuel next true
          return result.charge (102485*cnt-1) (8190*cnt)) := by
  induction cnt generalizing g s with
  | zero => simp [groups,Execution.charge]
  | succ k ih =>
    have last : (45155*(k+1)-1)=45153+latchCost g+(45155*k-1) ∧
        (102485*(k+1)-1)=102483+latchCost g+(102485*k-1) := by
      unfold latchCost;split <;> constructor <;> omega
    have valid := r (by omega)
    rw [last.1,Nat.add_assoc (45153+latchCost g),batch_run s g _ (by omega) valid stop]
    simp only [groups,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    obtain ⟨regs,_,_,keep⟩ := batch_post s g (by omega) valid reached
    rw [ih next (g+1) (by omega) (fun more => regs (by omega)) ((keep .x8 (by simp [SavedReg])).trans stop), last.2]
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem groups_post (s : MachineState) (cnt g : Nat) (limit : g+cnt=4097)
    (r : Regs s g 1) (positive : 0<cnt) {out : MachineState} (hit : out ∈ support (groups cnt g s)) :
    out.pc=184900 ∧ out.getReg .x12=wordAddress (leafDest (2^24-1)) ∧
      ∀ reg, SavedReg reg → out.getReg reg=s.getReg reg := by
  induction cnt generalizing g s with
  | zero => omega
  | succ k ih =>
    simp only [groups,mem_support_bind_iff] at hit
    obtain ⟨mid,step,reach⟩ := hit
    obtain ⟨regs,pc,final,keep⟩ := batch_post s g (by omega) r step
    cases k with
    | zero =>
      simp only [groups,support_pure,Set.mem_singleton_iff] at reach;subst out
      refine ⟨by rw [pc,latchPC,if_pos (by omega)],?_,keep⟩
      rw [final (by omega)]
      congr 2
      omega
    | succ k =>
      obtain ⟨finish,dest,rest⟩ := ih mid (g+1) (by omega) (regs (by omega)) (by omega) reach
      exact ⟨finish,dest,fun reg h => (rest reg h).trans (keep reg h)⟩


end TwoPermutationPrototype.Quad.Commit.Leaves
