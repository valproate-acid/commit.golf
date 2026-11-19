import CommitGolfCandidate.TwoPermutationProductionLeaf

/-! Register and instruction-position invariants across consecutive leaves of
one unrolled group. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private theorem reg_store (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r = s.getReg r := by cases r <;> rfl

private theorem first_reg_frame (s : MachineState) (slot : Fin 16) (reg : Reg)
    (out : Reg.x12 ≠ reg) (tmp : Reg.x31 ≠ reg) :
    (preparedA s slot).getReg reg = s.getReg reg := by
  simp only [preparedA,firstInstructions,List.foldl_cons,List.foldl_nil,execInstrBr,
    MachineState.getReg_setPC,reg_store,MachineState.getReg_setReg_ne _ _ _ _ out,
    MachineState.getReg_setReg_ne _ _ _ _ tmp]

theorem finished_reg_frame (s : MachineState) (slot : Fin 16) (start dst : Nat)
    (a b : BitVec 1600) (reg : Reg) (src : Reg.x10 ≠ reg) (out : Reg.x12 ≠ reg) (tmp : Reg.x31 ≠ reg) :
    (finishedLeaf s slot start dst a b).getReg reg = s.getReg reg := by
  simp only [finishedLeaf,repliedB,preparedB,secondInstructions,List.foldl_cons,List.foldl_nil,
    execInstrBr,MachineState.getReg_setPC,reg_store,MachineState.getReg_setReg_ne _ _ _ _ src,
    MachineState.getReg_setReg_ne _ _ _ _ out,MachineState.getReg_setReg_ne _ _ _ _ tmp,
    CommitGolfCandidate.writeBits_register,repliedA,first_reg_frame s slot reg out tmp]

def groupPC (u : Nat) : Word := BitVec.ofNat 64 (4160 + 60*u)
def groupSlot (u : Nat) : Fin 16 := ⟨u%16,Nat.mod_lt _ (by decide)⟩

structure GroupRegs (s : MachineState) (g u : Nat) : Prop where
  source : s.getReg .x10 = wordAddress (leafStart (16*g+u))
  heap : s.getReg .x20 = wordAddress (leafDest (16*g))
  salts : s.getReg .x22 = wordAddress (leafSalt (16*g))
  selector : s.getReg .x5 = 0
  size : s.getReg .x11 = 200
  primitive : s.getReg .x13 = 1
  pc : s.pc = groupPC u

theorem group_prod_regs {s : MachineState} {g u : Nat} (r : GroupRegs s g u) (hu : u < 16) :
    ProductionRegs s g (groupSlot u) := by
  have same : (groupSlot u).val = u := Nat.mod_eq_of_lt hu
  refine ⟨?_,r.heap,r.salts,r.selector,r.size,r.primitive,?_⟩
  · rw [same];exact r.source
  · simpa only [groupPC,leafPC,same,Nat.mul_zero,Nat.add_zero] using r.pc

theorem leaf_advance_regs {s : MachineState} {g u : Nat} (bound : g < 2^20) (hu : u < 16)
    (r : GroupRegs s g u) (a b : BitVec 1600) :
    let i := 16*g+u
    GroupRegs (finishedLeaf s (groupSlot u) (leafStart i) (leafDest i) a b) g (u+1) := by
  let slot := groupSlot u
  let i := 16*g+u
  let start := leafStart i
  let dst := leafDest i
  have same : slot.val = u := Nat.mod_eq_of_lt hu
  have prod := group_prod_regs r hu
  have ready := production_leaf_ready _ _ slot bound prod
  rw [same] at ready
  have prev := after_a_control _ _ _ _ _ _ ready prod.pc a
  have src := after_a_input_cursor _ _ _ _ _ _ ready a
  let p := repliedA s slot start a
  have second := second_execution p slot
  have x : (preparedB s slot start a).getReg .x10 = wordAddress start + 96 := second.2.1.trans (congrArg (· + 96) src)
  have pc : (preparedB s slot start a).pc = leafPC slot 13 := by
    change ((secondInstructions slot).foldl execInstrBr p).pc = _
    rw [second.2.2.2.2.2.2,show p.pc=leafPC slot 9 from prev.2.2.2.2]
    exact leaf_pc_add slot 9 4
  have hold := finished_reg_frame s slot start dst a b
  refine ⟨?_,(hold .x20 (by decide) (by decide) (by decide)).trans r.heap,
    (hold .x22 (by decide) (by decide) (by decide)).trans r.salts,
    (hold .x5 (by decide) (by decide) (by decide)).trans r.selector,
    (hold .x11 (by decide) (by decide) (by decide)).trans r.size,
    (hold .x13 (by decide) (by decide) (by decide)).trans r.primitive,?_⟩
  · change (repliedB s slot start dst a b).getReg .x10 + 160 = _
    rw [repliedB, CommitGolfCandidate.writeBits_register,x,BitVec.add_assoc]
    change wordAddress (leafStart i) + wordAddress 32 = _
    rw [← wordAddress_add];congr 1 <;> dsimp [i,leafStart] <;> omega
  · change (preparedB s slot start a).pc + 4 + 4 = _
    rw [pc,BitVec.add_assoc]
    change leafPC slot 13 + BitVec.ofNat 64 (4*2) = _
    rw [leaf_pc_add,leafPC,groupPC,same]
    congr 1 <;> omega

theorem trace_advance_regs {s : MachineState} {g u : Nat} (bound : g < 2^20) (hu : u < 16)
    (r : GroupRegs s g u) {done : MachineState}
    (hit : done ∈ support (leafTrace s (groupSlot u) (leafStart (16*g+u)) (16*g+u) (leafDest (16*g+u)))) :
    GroupRegs done g (u+1) := by
  simp only [leafTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨a,_,b,_,rfl⟩ := hit
  exact leaf_advance_regs bound hu r a b

end TwoPermutationPrototype.RV64
