import CommitGolfCandidate.TwoPermutationPackedGroupCode

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
attribute [local simp] Opening.getReg_setMem Opening.getReg_setReg MachineState.getReg_setPC
@[local simp] private theorem setpc (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl
@[local simp] private theorem setpc_mem (s : MachineState) (pc : Word) : (s.setPC pc).mem=s.mem := rfl
@[local simp] private theorem setreg_mem (s : MachineState) (r : Reg) (x : Word) : (s.setReg r x).mem=s.mem := by cases r <;> rfl
@[local simp] private theorem zero_register (s : MachineState) : s.getReg .x0=0#64 := rfl

def GroupSaved (reg : Reg) : Prop :=
  reg ∉ ([.x7,.x8,.x18,.x19,.x28,.x29,.x30,.x31] : List Reg)

def sameGroupWord (s : MachineState) (i : Fin 4) : Prop :=
  s.getMem (s.getReg .x28+BitVec.ofNat 64 (8*i.val)) =
    s.getMem (s.getReg .x23+BitVec.ofNat 64 (8*i.val))
instance (s : MachineState) (i : Fin 4) : Decidable (sameGroupWord s i) := inferInstanceAs (Decidable (_=_))

private theorem group_beq_pc (s : MachineState) (a b : Reg) (d : BitVec 13) :
    (execInstrBr s (.BEQ a b d)).pc = if s.getReg a=s.getReg b then s.pc+signExtend13 d else s.pc+4 := by
  simp only [execInstrBr,beq_iff_eq]
  split <;> rfl

theorem group_bne_pc (s : MachineState) (a b : Reg) (d : BitVec 13) :
    (execInstrBr s (.BNE a b d)).pc = if s.getReg a=s.getReg b then s.pc+4 else s.pc+signExtend13 d := by
  simp only [execInstrBr,bne_iff_ne]
  by_cases eq : s.getReg a=s.getReg b <;> simp [eq]

private theorem group_beq_reg (s : MachineState) (a b r : Reg) (d : BitVec 13) :
    (execInstrBr s (.BEQ a b d)).getReg r=s.getReg r := by simp only [execInstrBr]; split <;> rfl

theorem group_bne_reg (s : MachineState) (a b r : Reg) (d : BitVec 13) :
    (execInstrBr s (.BNE a b d)).getReg r=s.getReg r := by simp only [execInstrBr]; split <;> rfl

private theorem group_beq_mem (s : MachineState) (a b : Reg) (d : BitVec 13) :
    (execInstrBr s (.BEQ a b d)).mem=s.mem := by simp only [execInstrBr]; split <;> rfl

theorem group_bne_mem (s : MachineState) (a b : Reg) (d : BitVec 13) :
    (execInstrBr s (.BNE a b d)).mem=s.mem := by simp only [execInstrBr]; split <;> rfl

private theorem getMem_pc (s : MachineState) (p a : Word) : (s.setPC p).getMem a=s.getMem a := rfl
private theorem getMem_reg (s : MachineState) (r : Reg) (v a : Word) : (s.setReg r v).getMem a=s.getMem a := by cases r <;> rfl
attribute [local simp] getMem_pc getMem_reg

set_option maxHeartbeats 1600000 in
theorem group_setup_view (s : MachineState) (pc : s.pc=0x13c0) :
    let t := GroupBlock.setup.done s
    t.pc=(if s.getMem (groupMarkAddress s)=0 then 0x140c else 0x13d8) ∧
    t.getReg .x7=groupMarkAddress s ∧ t.getReg .x28=groupRootAddress s ∧ t.mem=s.mem ∧
    ∀ r : Reg, r ≠ .x7 → r ≠ .x28 → r ≠ .x29 → t.getReg r=s.getReg r := by
  dsimp only
  simp only [GroupBlock.done,GroupBlock.words,List.foldl_cons,List.foldl_nil,
    group_beq_pc,group_beq_reg,group_beq_mem]
  simp [execInstrBr,signExtend12,signExtend13,groupMarkAddress,groupRootAddress,pc]
  constructor
  · rfl
  intro r m p t
  simp [Ne.symm m,Ne.symm p,Ne.symm t]

theorem group_compare_view (s : MachineState) (i : Fin 4)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*(246+3*i.val))) :
    let t := (GroupBlock.compare i).done s
    t.pc=(if sameGroupWord s i then BitVec.ofNat 64 (4096+4*(249+3*i.val)) else 0x15b0) ∧
      t.mem=s.mem ∧ ∀ r : Reg, r≠.x29 → r≠.x30 → t.getReg r=s.getReg r := by
  dsimp only
  simp only [GroupBlock.done,GroupBlock.words,List.foldl_cons,List.foldl_nil,
    group_bne_pc,group_bne_reg,group_bne_mem]
  fin_cases i <;> simp [sameGroupWord,execInstrBr,signExtend12,signExtend13,pc]
  all_goals first | exact ⟨rfl, by intro r m p; simp [Ne.symm m,Ne.symm p]⟩ | (intro r m p; simp [Ne.symm m,Ne.symm p])

theorem group_duplicate_view (s : MachineState) (pc : s.pc=0x1408) :
    let t := GroupBlock.duplicate.done s
    t.pc=0x1434 ∧ t.mem=s.mem ∧ ∀ r, t.getReg r=s.getReg r := by
  simp [GroupBlock.done,GroupBlock.words,execInstrBr,pc,signExtend21]

theorem group_mark_view (s : MachineState) (pc : s.pc=0x142c) :
    let t := GroupBlock.mark.done s
    t.pc=0x1434 ∧ t.mem=(s.setMem (s.getReg .x7) 1).mem ∧
      ∀ r : Reg, r≠.x29 → t.getReg r=s.getReg r := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · simp [GroupBlock.done,GroupBlock.words,execInstrBr,pc]
  · simp [GroupBlock.done,GroupBlock.words,execInstrBr,signExtend12,MachineState.setMem]
  · intro r kept
    simp [GroupBlock.done,GroupBlock.words,execInstrBr,Ne.symm kept]

end TwoPermutationPrototype.Packed.Checker
