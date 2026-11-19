import CommitGolfCandidate.QuadCheckPentaCopy
import CommitGolfCandidate.QuadCheckerExit

/-! The straight-line glue of a penta record: the jump from the leaf into the
block (words 58, 59, 367, 368), the branch-free commitment comparison
(words 443-457), the rejecting branch (458), the jump to the record latch (459)
and the unchanged latch (269-272). -/
namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

attribute [local irreducible] execute
attribute [local simp] Opening.getReg_setMem MachineState.getReg_setPC

@[local simp] private theorem code_zero (s : MachineState) : s.getReg .x0=0#64 := rfl
@[local simp] private theorem set_x0 (s : MachineState) (v : Word) : s.setReg .x0 v=s := rfl

/-! ### Entry -/

def entryCode : List Instr :=
  [.ADDI .x21 .x21 16, .JAL .x0 1232, .ADDI .x10 .x24 256, .ADDI .x29 .x0 11]

def entryPrefix (s : MachineState) (n : Nat) : MachineState := (entryCode.take n).foldl execInstrBr s

def entryState (s : MachineState) : MachineState := entryPrefix s 4

private def entryWord (i : Nat) : Nat := if i<2 then 58+i else 365+i

theorem execute_entry (s : MachineState) (pc : s.pc=0x10e8) : GroupHop s (entryState s) 4 := by
  intro fuel
  apply execute_unit_steps (states := entryPrefix s)
  intro i bounded
  refine ⟨.base (entryCode[i]?.getD .EBREAK),?_,?_,?_⟩
  · apply fetch_at _ (entryWord i) _ (by unfold entryWord; split <;> omega)
    · interval_cases i <;> simp [entryPrefix,entryCode,entryWord,execInstrBr,signExtend21,pc] <;> rfl
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem entry_post (s : MachineState) (pc : s.pc=0x10e8) (pair : s.getReg .x24=wordAddress 1568) :
    let t := entryState s
    t.pc=BitVec.ofNat 64 (4096+4*369) ∧ t.getReg .x21=s.getReg .x21+16 ∧ t.getReg .x10=wordAddress 1600 ∧
      t.getReg .x29=BitVec.ofNat 64 11 ∧
      (∀ r, r≠.x10 → r≠.x21 → r≠.x29 → t.getReg r=s.getReg r) ∧ t.mem=s.mem := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simp [entryState,entryPrefix,entryCode,execInstrBr,signExtend21,pc]; try rfl
  · simp [entryState,entryPrefix,entryCode,execInstrBr,signExtend12,MachineState.getReg_setReg_ne]; try rfl
  · simp [entryState,entryPrefix,entryCode,execInstrBr,signExtend12,MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq,pair]; try rfl
  · simp [entryState,entryPrefix,entryCode,execInstrBr,signExtend12,MachineState.getReg_setReg_eq]; try rfl
  · intro r a b c
    simp [entryState,entryPrefix,entryCode,execInstrBr,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm a),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm b),MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm c)]
  · simp only [entryState,entryPrefix,entryCode,List.take,List.foldl,execInstrBr]; rfl

/-! ### Comparison -/

def compareCode : List Instr :=
  [.LD .x29 .x23 0, .LD .x30 .x9 0, .XOR .x31 .x29 .x30,
   .LD .x29 .x23 8, .LD .x30 .x9 8, .XOR .x29 .x29 .x30, .OR .x31 .x31 .x29,
   .LD .x29 .x23 16, .LD .x30 .x9 16, .XOR .x29 .x29 .x30, .OR .x31 .x31 .x29,
   .LD .x29 .x23 24, .LD .x30 .x9 24, .XOR .x29 .x29 .x30, .OR .x31 .x31 .x29]

def comparePrefix (s : MachineState) (n : Nat) : MachineState := (compareCode.take n).foldl execInstrBr s

def compareState (s : MachineState) : MachineState := comparePrefix s 15

theorem compare_prefix_reg (s : MachineState) (n : Nat) (bound : n≤15) (r : Reg)
    (a : r≠.x29) (b : r≠.x30) (c : r≠.x31) : (comparePrefix s n).getReg r=s.getReg r := by
  interval_cases n <;>
    simp [comparePrefix,compareCode,execInstrBr,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm a),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm b),MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm c)]

theorem compare_prefix_pc (s : MachineState) (n : Nat) (bound : n≤15) :
    (comparePrefix s n).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  interval_cases n <;>
    simp [comparePrefix,compareCode,execInstrBr,MachineState.setPC,MachineState.setReg,BitVec.add_assoc] <;> rfl

theorem compare_state_pc (s : MachineState) : (compareState s).pc=s.pc+BitVec.ofNat 64 (4*15) :=
  compare_prefix_pc s 15 (by decide)

theorem compare_state_reg (s : MachineState) (r : Reg) (a : r≠.x29) (b : r≠.x30) (c : r≠.x31) :
    (compareState s).getReg r=s.getReg r :=
  compare_prefix_reg s 15 (by decide) r a b c

theorem execute_compare (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (4096+4*443))
    (digest : s.getReg .x23=wordAddress 1536) (root : s.getReg .x9=wordAddress 536871424) :
    GroupHop s (compareState s) 15 := by
  intro fuel
  apply execute_unit_steps (states := comparePrefix s)
  intro i bounded
  refine ⟨.base (compareCode[i]?.getD .EBREAK),?_,?_,?_⟩
  · apply fetch_at _ (443+i) _ (by omega)
    · rw [compare_prefix_pc s i (by omega),pc,←BitVec.ofNat_add]; congr 1; omega
    · interval_cases i <;> rfl
  · have d := compare_prefix_reg s i (by omega) .x23 (by decide) (by decide) (by decide)
    have c := compare_prefix_reg s i (by omega) .x9 (by decide) (by decide) (by decide)
    have next : comparePrefix s (i+1)=execInstrBr (comparePrefix s i) (compareCode[i]?.getD .EBREAK) := by
      interval_cases i <;> rfl
    rw [next]
    interval_cases i
    · apply step_ld; rw [d,digest,se_0,word_offset_add]; exact word_access _ (by omega)
    · apply step_ld; rw [c,root,se_0,word_offset_add]; exact word_access _ (by omega)
    · rfl
    · apply step_ld; rw [d,digest,se_8,word_offset_add]; exact word_access _ (by omega)
    · apply step_ld; rw [c,root,se_8,word_offset_add]; exact word_access _ (by omega)
    · rfl
    · rfl
    · apply step_ld; rw [d,digest,se_16,word_offset_add]; exact word_access _ (by omega)
    · apply step_ld; rw [c,root,se_16,word_offset_add]; exact word_access _ (by omega)
    · rfl
    · rfl
    · apply step_ld; rw [d,digest,se_24,word_offset_add]; exact word_access _ (by omega)
    · apply step_ld; rw [c,root,se_24,word_offset_add]; exact word_access _ (by omega)
    · rfl
    · rfl
  · interval_cases i <;> rfl

theorem xor_or_zero (a0 b0 a1 b1 a2 b2 a3 b3 : Word) :
    ((((a0 ^^^ b0) ||| (a1 ^^^ b1)) ||| (a2 ^^^ b2)) ||| (a3 ^^^ b3))=0#64 ↔
      a0=b0 ∧ a1=b1 ∧ a2=b2 ∧ a3=b3 := by
  simp only [BitVec.or_eq_zero_iff,BitVec.xor_eq_zero_iff,and_assoc]

theorem compare_post (s : MachineState) (digest : s.getReg .x23=wordAddress 1536)
    (root : s.getReg .x9=wordAddress 536871424) :
    let t := compareState s
    (t.getReg .x31=0#64 ↔ readBuffer s 12288 32=readBuffer s (8*536871424) 32) ∧ t.mem=s.mem := by
  have raw : (compareState s).getReg .x31=
      ((((s.getMem (s.getReg .x23+signExtend12 0) ^^^ s.getMem (s.getReg .x9+signExtend12 0)) |||
        (s.getMem (s.getReg .x23+signExtend12 8) ^^^ s.getMem (s.getReg .x9+signExtend12 8))) |||
        (s.getMem (s.getReg .x23+signExtend12 16) ^^^ s.getMem (s.getReg .x9+signExtend12 16))) |||
        (s.getMem (s.getReg .x23+signExtend12 24) ^^^ s.getMem (s.getReg .x9+signExtend12 24))) := by
    simp [compareState,comparePrefix,compareCode,execInstrBr,MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq]
  have value : (compareState s).getReg .x31=
      ((((s.getMem (wordAddress 1536) ^^^ s.getMem (wordAddress 536871424)) |||
        (s.getMem (wordAddress 1537) ^^^ s.getMem (wordAddress 536871425))) |||
        (s.getMem (wordAddress 1538) ^^^ s.getMem (wordAddress 536871426))) |||
        (s.getMem (wordAddress 1539) ^^^ s.getMem (wordAddress 536871427))) := by
    rw [raw,digest,root,se_0,se_8,se_16,se_24,word_offset_add,word_offset_add,word_offset_add,word_offset_add,
      word_offset_add,word_offset_add,word_offset_add,word_offset_add]
  refine ⟨?_,?_⟩
  · rw [value,xor_or_zero]
    rw [read_digest_eq_iff _ _ _ _ (by decide) (by decide)]
    constructor
    · rintro ⟨e0,e1,e2,e3⟩ word bound
      interval_cases word
      · exact e0
      · exact e1
      · exact e2
      · exact e3
    · intro all
      exact ⟨all 0 (by decide),all 1 (by decide),all 2 (by decide),all 3 (by decide)⟩
  · simp only [compareState,comparePrefix,compareCode,List.take,List.foldl,execInstrBr]; rfl

/-! ### Branch, jump and latch -/

theorem bne_458 : BitVec.ofNat 64 (4096+4*458)+signExtend13 (7816 : BitVec 13)=0x15b0 := by decide
theorem jal_459 : BitVec.ofNat 64 (4096+4*459)+signExtend21 (2096392 : BitVec 21)=BitVec.ofNat 64 (4096+4*269) := by
  decide
theorem pc_458_next : BitVec.ofNat 64 (4096+4*458)+4=BitVec.ofNat 64 (4096+4*459) := by decide
theorem bne_272 : BitVec.ofNat 64 (4096+4*272)+signExtend13 (7192 : BitVec 13)=0x1058 := by decide

def branchState (s : MachineState) : MachineState := execInstrBr s (.BNE .x31 .x0 7816)

theorem execute_branch (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (4096+4*458)) :
    GroupHop s (branchState s) 1 :=
  hop_one_unit (fetch_at _ 458 _ (by decide) pc rfl) rfl rfl

theorem set_pc_pc (s : MachineState) (v : Word) : (s.setPC v).pc=v := rfl
theorem set_pc_mem (s : MachineState) (v : Word) : (s.setPC v).mem=s.mem := rfl

theorem branch_shape (s : MachineState) :
    branchState s=if (s.getReg .x31 != 0#64)=true then s.setPC (s.pc+signExtend13 7816) else s.setPC (s.pc+4) := rfl

theorem branch_fall (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (4096+4*458)) (zero : s.getReg .x31=0#64) :
    (branchState s).pc=BitVec.ofNat 64 (4096+4*459) := by
  rw [branch_shape,zero,if_neg (by decide),set_pc_pc,pc]
  exact pc_458_next

theorem branch_taken (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (4096+4*458)) (nonzero : s.getReg .x31≠0#64) :
    (branchState s).pc=0x15b0 := by
  have ne : (s.getReg .x31 != 0#64)=true := bne_iff_ne.mpr nonzero
  rw [branch_shape,if_pos ne,set_pc_pc,pc]
  exact bne_458

theorem branch_reg (s : MachineState) (r : Reg) : (branchState s).getReg r=s.getReg r := by
  rw [branch_shape]; split <;> exact MachineState.getReg_setPC

theorem branch_mem (s : MachineState) : (branchState s).mem=s.mem := by
  rw [branch_shape]; split <;> exact set_pc_mem _ _

def latchJump (s : MachineState) : MachineState := execInstrBr s (.JAL .x0 2096392)
def latchA (s : MachineState) : MachineState := execInstrBr (latchJump s) (.ADDI .x8 .x8 8)
def latchB (s : MachineState) : MachineState := execInstrBr (latchA s) (.ADDI .x19 .x19 256)
def latchU (s : MachineState) : MachineState := execInstrBr (latchB s) (.ADDI .x18 .x18 4095)
def latchState (s : MachineState) : MachineState := execInstrBr (latchU s) (.BNE .x18 .x0 7192)

/-! Generic single-instruction facts (no concrete values, so they are cheap). -/

theorem addi_pc (t : MachineState) (rd rs : Reg) (imm : BitVec 12) :
    (execInstrBr t (.ADDI rd rs imm)).pc=t.pc+4 := by
  simp only [execInstrBr]; exact set_pc_pc _ _

theorem addi_mem (t : MachineState) (rd rs : Reg) (imm : BitVec 12) :
    (execInstrBr t (.ADDI rd rs imm)).mem=t.mem := by
  simp only [execInstrBr]; cases rd <;> rfl

theorem addi_same (t : MachineState) (rd rs : Reg) (imm : BitVec 12) (h : rd≠.x0) :
    (execInstrBr t (.ADDI rd rs imm)).getReg rd=t.getReg rs+signExtend12 imm := by
  simp only [execInstrBr,MachineState.getReg_setPC]; exact MachineState.getReg_setReg_eq h

theorem addi_other (t : MachineState) (rd rs : Reg) (imm : BitVec 12) (r : Reg) (h : rd≠r) :
    (execInstrBr t (.ADDI rd rs imm)).getReg r=t.getReg r := by
  simp only [execInstrBr,MachineState.getReg_setPC]; exact MachineState.getReg_setReg_ne _ _ _ _ h

theorem jal0_pc (t : MachineState) (off : BitVec 21) :
    (execInstrBr t (.JAL .x0 off)).pc=t.pc+signExtend21 off := by
  simp only [execInstrBr]; exact set_pc_pc _ _

theorem jal0_reg (t : MachineState) (off : BitVec 21) (r : Reg) :
    (execInstrBr t (.JAL .x0 off)).getReg r=t.getReg r := by
  simp only [execInstrBr]; exact MachineState.getReg_setPC

theorem jal0_mem (t : MachineState) (off : BitVec 21) :
    (execInstrBr t (.JAL .x0 off)).mem=t.mem := by
  simp only [execInstrBr]; exact set_pc_mem _ _

theorem pc_269_next : BitVec.ofNat 64 (4096+4*269)+4=BitVec.ofNat 64 (4096+4*270) := by decide
theorem pc_270_next : BitVec.ofNat 64 (4096+4*270)+4=BitVec.ofNat 64 (4096+4*271) := by decide
theorem pc_271_next : BitVec.ofNat 64 (4096+4*271)+4=BitVec.ofNat 64 (4096+4*272) := by decide
theorem pc_272_next : BitVec.ofNat 64 (4096+4*272)+4=0x1444 := by decide

theorem latch_pcs (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (4096+4*459)) :
    (latchJump s).pc=BitVec.ofNat 64 (4096+4*269) ∧ (latchA s).pc=BitVec.ofNat 64 (4096+4*270) ∧
      (latchB s).pc=BitVec.ofNat 64 (4096+4*271) ∧ (latchU s).pc=BitVec.ofNat 64 (4096+4*272) := by
  have p1 : (latchJump s).pc=BitVec.ofNat 64 (4096+4*269) := by
    unfold latchJump; rw [jal0_pc,pc]; exact jal_459
  have p2 : (latchA s).pc=BitVec.ofNat 64 (4096+4*270) := by
    unfold latchA; rw [addi_pc,p1]; exact pc_269_next
  have p3 : (latchB s).pc=BitVec.ofNat 64 (4096+4*271) := by
    unfold latchB; rw [addi_pc,p2]; exact pc_270_next
  have p4 : (latchU s).pc=BitVec.ofNat 64 (4096+4*272) := by
    unfold latchU; rw [addi_pc,p3]; exact pc_271_next
  exact ⟨p1,p2,p3,p4⟩

theorem execute_latch (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (4096+4*459)) :
    GroupHop s (latchState s) 5 := by
  obtain ⟨p1,p2,p3,p4⟩ := latch_pcs s pc
  have h0 : GroupHop s (latchJump s) 1 := hop_one_unit (fetch_at _ 459 _ (by decide) pc rfl) rfl rfl
  have h1 : GroupHop (latchJump s) (latchA s) 1 := hop_one_unit (fetch_at _ 269 _ (by decide) p1 rfl) rfl rfl
  have h2 : GroupHop (latchA s) (latchB s) 1 := hop_one_unit (fetch_at _ 270 _ (by decide) p2 rfl) rfl rfl
  have h3 : GroupHop (latchB s) (latchU s) 1 := hop_one_unit (fetch_at _ 271 _ (by decide) p3 rfl) rfl rfl
  have h4 : GroupHop (latchU s) (latchState s) 1 := hop_one_unit (fetch_at _ 272 _ (by decide) p4 rfl) rfl rfl
  exact (((h0.thenDo h1).thenDo h2).thenDo h3).thenDo h4

theorem latch_post (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (4096+4*459)) (left : Nat)
    (positive : 0<left) (small : left<2^64) (remaining : s.getReg .x18=BitVec.ofNat 64 left) :
    let t := latchState s
    t.pc=(if left=1 then 0x1444 else 0x1058) ∧ t.getReg .x18=BitVec.ofNat 64 (left-1) ∧
      t.getReg .x8=s.getReg .x8+8 ∧ t.getReg .x19=s.getReg .x19+256 ∧
      (∀ r, r≠.x8 → r≠.x18 → r≠.x19 → t.getReg r=s.getReg r) ∧ t.mem=s.mem := by
  let u := latchU s
  have whole : latchState s=execInstrBr u (.BNE .x18 .x0 7192) := rfl
  have upc : u.pc=BitVec.ofNat 64 (4096+4*272) := (latch_pcs s pc).2.2.2
  have u18 : u.getReg .x18=BitVec.ofNat 64 (left-1) := by
    change (execInstrBr (execInstrBr (execInstrBr (execInstrBr s (.JAL .x0 2096392)) (.ADDI .x8 .x8 8)) (.ADDI .x19 .x19 256)) (.ADDI .x18 .x18 4095)).getReg .x18=_
    rw [addi_same _ _ _ _ (by decide),addi_other _ _ _ _ _ (by decide),addi_other _ _ _ _ _ (by decide),
      jal0_reg,remaining,show signExtend12 (4095 : BitVec 12)=BitVec.ofNat 64 (2^64-1) from rfl,←BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  have u8 : u.getReg .x8=s.getReg .x8+8 := by
    change (execInstrBr (execInstrBr (execInstrBr (execInstrBr s (.JAL .x0 2096392)) (.ADDI .x8 .x8 8)) (.ADDI .x19 .x19 256)) (.ADDI .x18 .x18 4095)).getReg .x8=_
    rw [addi_other _ _ _ _ _ (by decide),addi_other _ _ _ _ _ (by decide),addi_same _ _ _ _ (by decide),
      jal0_reg,show signExtend12 (8 : BitVec 12)=8 from rfl]
  have u19 : u.getReg .x19=s.getReg .x19+256 := by
    change (execInstrBr (execInstrBr (execInstrBr (execInstrBr s (.JAL .x0 2096392)) (.ADDI .x8 .x8 8)) (.ADDI .x19 .x19 256)) (.ADDI .x18 .x18 4095)).getReg .x19=_
    rw [addi_other _ _ _ _ _ (by decide),addi_same _ _ _ _ (by decide),addi_other _ _ _ _ _ (by decide),
      jal0_reg,show signExtend12 (256 : BitVec 12)=256 from rfl]
  have ureg (r : Reg) (ka : r≠.x8) (kb : r≠.x18) (kc : r≠.x19) : u.getReg r=s.getReg r := by
    change (execInstrBr (execInstrBr (execInstrBr (execInstrBr s (.JAL .x0 2096392)) (.ADDI .x8 .x8 8)) (.ADDI .x19 .x19 256)) (.ADDI .x18 .x18 4095)).getReg r=_
    rw [addi_other _ _ _ _ _ (Ne.symm kb),addi_other _ _ _ _ _ (Ne.symm kc),addi_other _ _ _ _ _ (Ne.symm ka),
      jal0_reg]
  have umem : u.mem=s.mem := by
    change (execInstrBr (execInstrBr (execInstrBr (execInstrBr s (.JAL .x0 2096392)) (.ADDI .x8 .x8 8)) (.ADDI .x19 .x19 256)) (.ADDI .x18 .x18 4095)).mem=_
    rw [addi_mem,addi_mem,addi_mem,jal0_mem]
  have shape : latchState s=if (u.getReg .x18 != 0#64)=true then u.setPC (u.pc+signExtend13 7192)
      else u.setPC (u.pc+4) := whole
  have breg (r : Reg) : (latchState s).getReg r=u.getReg r := by
    rw [shape]; split <;> exact MachineState.getReg_setPC
  refine ⟨?_,(breg _).trans u18,(breg _).trans u8,(breg _).trans u19,fun r ka kb kc => (breg r).trans (ureg r ka kb kc),?_⟩
  · rw [shape,u18]
    by_cases one : left=1
    · subst one
      rw [if_neg (by decide),set_pc_pc,upc,if_pos rfl]
      exact pc_272_next
    · have ne : BitVec.ofNat 64 (left-1)≠0#64 := by
        intro eq
        have := congrArg BitVec.toNat eq
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at this
        simp at this; omega
      rw [if_pos (bne_iff_ne.mpr ne),set_pc_pc,upc,if_neg one]
      exact bne_272
  · rw [shape]; split <;> exact (set_pc_mem _ _).trans umem

end TwoPermutationPrototype.Quad.Checker
