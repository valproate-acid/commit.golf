import CommitGolfCandidate.TwoPermutationParentLoop

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute

def StableLeafReg (reg : Reg) := reg ∈ [Reg.x5,.x8,.x9,.x19,.x21]

theorem batch_keeps_register (g : Nat) (s : MachineState) (reg : Reg) (stable : StableLeafReg reg)
    {done : MachineState} (hit : done ∈ support (batchTrace g s)) : done.getReg reg=s.getReg reg := by
  simp only [batchTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨body,reached,rfl⟩ := hit
  simp only [StableLeafReg,List.mem_cons,List.not_mem_nil,or_false] at stable
  rcases stable with rfl|rfl|rfl|rfl|rfl
  · exact group_preserved_reg g 16 0 s .x5 (by decide) (by decide) (by decide) (done := body) reached
  · exact group_preserved_reg g 16 0 s .x8 (by decide) (by decide) (by decide) (done := body) reached
  · exact group_preserved_reg g 16 0 s .x9 (by decide) (by decide) (by decide) (done := body) reached
  · exact group_preserved_reg g 16 0 s .x19 (by decide) (by decide) (by decide) (done := body) reached
  · exact group_preserved_reg g 16 0 s .x21 (by decide) (by decide) (by decide) (done := body) reached

theorem leaves_keep_register (g cnt : Nat) (s : MachineState) (reg : Reg) (stable : StableLeafReg reg)
    {done : MachineState} (hit : done ∈ support (leavesTrace cnt g s)) : done.getReg reg=s.getReg reg := by
  induction cnt generalizing s g with
  | zero => simp only [leavesTrace,support_pure,Set.mem_singleton_iff] at hit;rw [hit]
  | succ k ih =>
    simp only [leavesTrace,mem_support_bind_iff] at hit
    obtain ⟨mid,step,tail⟩ := hit
    exact (ih (g+1) mid tail).trans (batch_keeps_register g s reg stable step)

theorem leaves_end_pc (g cnt : Nat) (s : MachineState) (endAt : g+cnt=2^20)
    (start : GroupRegs s g 0) (stop : s.getReg .x21=wordAddress (leafDest (2^24)))
    (more : 0<cnt) {done : MachineState} (reach : done ∈ support (leavesTrace cnt g s)) :
    done.pc=5132 := by
  induction cnt generalizing s g with
  | zero => omega
  | succ k ih =>
    simp only [leavesTrace,mem_support_bind_iff] at reach
    obtain ⟨mid,step,tail⟩ := reach
    obtain ⟨regs,regEnd,pc⟩ := batch_next g s (by omega) start stop step
    cases k with
    | zero =>
      simp only [leavesTrace,support_pure,Set.mem_singleton_iff] at tail
      rw [tail,pc,nextPC,if_pos (by omega)]
    | succ j => exact ih (g+1) mid (by omega) (regs (by omega)) regEnd (by omega) tail

def parentSetupOps : List Instr := [.ADDI .x10 .x21 4032,.SUB .x12 .x21 .x19,.ADDI .x12 .x12 4064,
  .ADDI .x11 .x0 64,.ADDI .x13 .x0 0]

def parentSetup (s : MachineState) (i : Nat) := (parentSetupOps.take i).foldl execInstrBr s

theorem execute_parent_setup (s : MachineState) (pc : s.pc=5132) (fuel : Nat) :
    execute commitImage (5+fuel) s true =
      (do let result ← execute commitImage fuel (parentSetup s 5) true
          return result.charge 5 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := parentSetup s)
  intro i inside
  refine ⟨.base ((parentSetupOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · interval_cases i <;> simp only [parentSetup,parentSetupOps,List.take,List.foldl,execInstrBr,MachineState.setPC,fetch,pc] <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem parent_setup_regs (s : MachineState) (pc : s.pc=5132)
    (sel : s.getReg .x5=0) (heap : s.getReg .x9=4294971424) (stride : s.getReg .x19=536870912)
    (stop : s.getReg .x21=wordAddress (leafDest (2^24))) :
    ParentRegs (parentSetup s 5) (2^24-1) ∧ (parentSetup s 5).pc=5152 := by
  refine ⟨⟨?_,?_,sel,rfl,rfl,heap⟩,?_⟩
  · change s.getReg .x21+signExtend12 4032=_;rw [stop];rfl
  · change s.getReg .x21-s.getReg .x19+signExtend12 4064=_;rw [stop,stride];rfl
  · change s.pc+4+4+4+4+4=_;rw [pc];rfl

theorem after_leaves_parent_ready (s : MachineState) (entry : CommitEntry s) {bits : Nat} (packed : BitVec bits)
    {done : MachineState} (reach : done ∈ support (leavesTrace (2^20) 0 (readyState s packed))) :
    done.pc=5132 ∧ ParentRegs (parentSetup done 5) (2^24-1) ∧ (parentSetup done 5).pc=5152 ∧
      (parentSetup done 5).getReg .x8=4294971392 := by
  obtain ⟨g,stop,out,heap,stride⟩ := post_random_regs s entry packed
  have pc := leaves_end_pc 0 (2^20) _ (by decide) g stop (by decide) reach
  have hold (reg : Reg) (stable : StableLeafReg reg) := leaves_keep_register 0 (2^20) _ reg stable reach
  have p := parent_setup_regs done pc ((hold .x5 (by simp [StableLeafReg])).trans g.selector)
    ((hold .x9 (by simp [StableLeafReg])).trans heap) ((hold .x19 (by simp [StableLeafReg])).trans stride)
    ((hold .x21 (by simp [StableLeafReg])).trans stop)
  exact ⟨pc,p.1,p.2,(hold .x8 (by simp [StableLeafReg])).trans out⟩

end TwoPermutationPrototype.RV64
