import CommitGolfCandidate.TwoPermutationPackedGroupView
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
attribute [local simp] Opening.getReg_setReg MachineState.getReg_setPC
private theorem latch_word (s : MachineState) (reg : Reg) (imm : BitVec 12) (nz : reg≠.x0) :
    (execInstrBr s (.ADDI reg reg imm)).getReg reg=s.getReg reg+signExtend12 imm := by
  simp [execInstrBr,nz]
private theorem latch_keep (s : MachineState) (reg other : Reg) (imm : BitVec 12) (ne : other≠reg) :
    (execInstrBr s (.ADDI reg reg imm)).getReg other=s.getReg other := by
  simp [execInstrBr,Ne.symm ne]
private theorem latch_mem (s : MachineState) (reg : Reg) (imm : BitVec 12) :
    (execInstrBr s (.ADDI reg reg imm)).mem=s.mem := by cases reg <;> rfl
private theorem latch_pc (s : MachineState) (reg : Reg) (imm : BitVec 12) :
    (execInstrBr s (.ADDI reg reg imm)).pc=s.pc+4 := rfl

section
attribute [local irreducible] execInstrBr

private def lA (s : MachineState) := execInstrBr s (.ADDI .x8 .x8 8)
private def lB (s : MachineState) := execInstrBr (lA s) (.ADDI .x19 .x19 256)
private def lC (s : MachineState) := execInstrBr (lB s) (.ADDI .x18 .x18 4095)
private def lD (s : MachineState) := execInstrBr (lC s) (.BNE .x18 .x0 7192)

private theorem ldec (s : MachineState) (remaining : Nat) (counter : s.getReg .x18=BitVec.ofNat 64 (remaining+1)) : (lC s).getReg .x18=BitVec.ofNat 64 remaining := by
  let a := lA s
  let b := lB s
  let c := lC s
  let d := lD s
  have dec : c.getReg .x18=BitVec.ofNat 64 remaining := by
    rw [show c.getReg .x18 = b.getReg .x18 + signExtend12 4095 from latch_word _ _ _ (by decide),
      show b.getReg .x18=a.getReg .x18 from latch_keep _ _ _ _ (by decide),
      show a.getReg .x18=s.getReg .x18 from latch_keep _ _ _ _ (by decide),
      counter,BitVec.ofNat_add]
    change BitVec.ofNat 64 remaining+1+(-1:Word)=BitVec.ofNat 64 remaining
    simp [BitVec.add_assoc]
  exact dec

private theorem latch_branch_control (middle : MachineState) (n : Nat)
    (pc : middle.pc=5184) (count : middle.getReg .x18=BitVec.ofNat 64 n) (small : n<2^64) :
    (execInstrBr middle (.BNE .x18 .x0 7192)).pc=(if n=0 then 5188 else 4184) := by
  have fall : (5184 : Word)+4=5188 := by decide
  have back : (5184 : Word)+signExtend13 7192=4184 := by decide
  rw [group_bne_pc,pc,fall,back,count,show middle.getReg .x0=0#64 by rfl]
  by_cases zero : n=0
  · subst n
    rfl
  · have nonzero : BitVec.ofNat 64 n≠0#64 := by
      intro eq
      apply zero
      have numeric := congrArg BitVec.toNat eq
      change n%2^64=0 at numeric
      rwa [Nat.mod_eq_of_lt small] at numeric
    simp only [if_neg nonzero,if_neg zero]

private theorem lpc (s : MachineState) (pc : s.pc=0x1434) (remaining : Nat) (counter : s.getReg .x18=BitVec.ofNat 64 (remaining+1)) (small : remaining<2^64) :
    (lD s).pc=(if remaining=0 then 0x1444 else 0x1058) := by
  apply latch_branch_control (lC s) remaining _ (ldec s remaining counter) small
  rw [lC,latch_pc,lB,latch_pc,lA,latch_pc,pc]
  decide

private theorem l8 (s : MachineState) : (lD s).getReg .x8=s.getReg .x8+8 := by
  let a := lA s
  let b := lB s
  let c := lC s
  let d := lD s
  change d.getReg _=_
  rw [show d.getReg .x8=c.getReg .x8 from group_bne_reg _ _ _ _ _,
    show c.getReg .x8=b.getReg .x8 from latch_keep _ _ _ _ (by decide),
    show b.getReg .x8=a.getReg .x8 from latch_keep _ _ _ _ (by decide),
    show a.getReg .x8=s.getReg .x8+signExtend12 8 from latch_word _ _ _ (by decide)]
  rfl

private theorem l19 (s : MachineState) : (lD s).getReg .x19=s.getReg .x19+256 := by
  let a := lA s
  let b := lB s
  let c := lC s
  let d := lD s
  change d.getReg _=_
  rw [show d.getReg .x19=c.getReg .x19 from group_bne_reg _ _ _ _ _,
    show c.getReg .x19=b.getReg .x19 from latch_keep _ _ _ _ (by decide),
    show b.getReg .x19=a.getReg .x19+signExtend12 256 from latch_word _ _ _ (by decide),
    show a.getReg .x19=s.getReg .x19 from latch_keep _ _ _ _ (by decide)]
  rfl


private theorem latch_abstract_fold {α : Type} (step : α → Instr → α) (s : α) :
    GroupBlock.latch.words.foldl step s =
      step (step (step (step s (.ADDI .x8 .x8 8)) (.ADDI .x19 .x19 256)) (.ADDI .x18 .x18 4095))
        (.BNE .x18 .x0 7192) := rfl

private theorem latch_done_eq (s : MachineState) : GroupBlock.latch.done s = lD s :=
  latch_abstract_fold execInstrBr s

private theorem latch_done_pc (s : MachineState) (pc : s.pc=0x1434) (remaining : Nat)
    (counter : s.getReg .x18=BitVec.ofNat 64 (remaining+1)) (small : remaining<2^64) :
    (GroupBlock.latch.done s).pc=(if remaining=0 then 0x1444 else 0x1058) :=
  (congrArg MachineState.pc (latch_done_eq s)).trans (lpc s pc remaining counter small)

private theorem latch_done_8 (s : MachineState) :
    (GroupBlock.latch.done s).getReg .x8 = s.getReg .x8+8 :=
  (congrArg (fun (t : MachineState) => t.getReg .x8) (latch_done_eq s)).trans (l8 s)

private theorem latch_done_19 (s : MachineState) :
    (GroupBlock.latch.done s).getReg .x19 = s.getReg .x19+256 :=
  (congrArg (fun (t : MachineState) => t.getReg .x19) (latch_done_eq s)).trans (l19 s)

private theorem latch_done_18 (s : MachineState) (remaining : Nat)
    (counter : s.getReg .x18=BitVec.ofNat 64 (remaining+1)) :
    (GroupBlock.latch.done s).getReg .x18 = BitVec.ofNat 64 remaining :=
  (congrArg (fun (t : MachineState) => t.getReg .x18) (latch_done_eq s)).trans
    ((group_bne_reg (lC s) .x18 .x0 .x18 7192).trans (ldec s remaining counter))

private theorem latch_done_mem (s : MachineState) : (GroupBlock.latch.done s).mem = s.mem :=
  (congrArg MachineState.mem (latch_done_eq s)).trans
    ((group_bne_mem (lC s) .x18 .x0 7192).trans
      ((latch_mem (lB s) .x18 4095).trans ((latch_mem (lA s) .x19 256).trans (latch_mem s .x8 8))))

private theorem latch_done_reg (s : MachineState) (r : Reg)
    (r8 : r≠.x8) (r19 : r≠.x19) (r18 : r≠.x18) :
    (GroupBlock.latch.done s).getReg r = s.getReg r :=
  (congrArg (fun (t : MachineState) => t.getReg r) (latch_done_eq s)).trans
    ((group_bne_reg (lC s) .x18 .x0 r 7192).trans
      ((latch_keep (lB s) .x18 r 4095 r18).trans
        ((latch_keep (lA s) .x19 r 256 r19).trans (latch_keep s .x8 r 8 r8))))

theorem group_latch_view (s : MachineState) (pc : s.pc=0x1434) (remaining : Nat)
    (counter : s.getReg .x18=BitVec.ofNat 64 (remaining+1)) (small : remaining<2^64) :
    let t := GroupBlock.latch.done s
    t.pc=(if remaining=0 then 0x1444 else 0x1058) ∧
      t.getReg .x8=s.getReg .x8+8 ∧ t.getReg .x19=s.getReg .x19+256 ∧
      t.getReg .x18=BitVec.ofNat 64 remaining ∧ t.mem=s.mem ∧
      ∀ r : Reg, r≠.x8 → r≠.x19 → r≠.x18 → t.getReg r=s.getReg r :=
  ⟨latch_done_pc s pc remaining counter small, latch_done_8 s, latch_done_19 s, latch_done_18 s remaining counter,
    latch_done_mem s, latch_done_reg s⟩

end
end TwoPermutationPrototype.Packed.Checker
