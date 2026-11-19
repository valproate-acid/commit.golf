import CommitGolfCandidate.QuadCheckerSteps
import CommitGolfCandidate.TwoPermutationOpeningBlocks
import CommitGolfCandidate.TwoPermutationMemoryBridge

/-! Generic single steps and the aligned four-word copy used by the penta block:
`LD x31, 8m(src); SD x31, 40+8m(x28)` for `m = 0 … 3`. -/
namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

attribute [local irreducible] execute

/-- One ordinary instruction with its own cycle cost (DIVU/REMU cost four). -/
theorem hop_instr (s t : MachineState) (i : Instr) (f : fetch packedImage s=some (.base i))
    (step : ordinaryStep s (.base i)=some t) : Hop s t 1 (instructionCycles (.base i)) := by
  intro fuel
  rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ f step]

theorem hop_one_unit {s t : MachineState} {i : Instr} (f : fetch packedImage s=some (.base i))
    (step : ordinaryStep s (.base i)=some t) (cost : instructionCycles (.base i)=1) : GroupHop s t 1 := by
  have h := hop_instr s t i f step
  rw [cost] at h
  exact h

theorem word_access (word : Nat) (bounded : word < 2^33) :
    accessValid (wordAddress word) 8 = true := by
  have small : 8*word < 2^64 := by omega
  simp only [accessValid, rangeValid, wordAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
    MEMORY_BYTES, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem step_ld (t : MachineState) (rd rs : Reg) (off : BitVec 12)
    (valid : accessValid (t.getReg rs + signExtend12 off) 8 = true) :
    ordinaryStep t (.base (.LD rd rs off))=some (execInstrBr t (.LD rd rs off)) := by
  simp [ordinaryStep, memoryArgumentsValid, memAccess, valid]

theorem step_sd (t : MachineState) (rs1 rs2 : Reg) (off : BitVec 12)
    (valid : accessValid (t.getReg rs1 + signExtend12 off) 8 = true) :
    ordinaryStep t (.base (.SD rs1 rs2 off))=some (execInstrBr t (.SD rs1 rs2 off)) := by
  simp [ordinaryStep, memoryArgumentsValid, memAccess, valid]

theorem word_offset_add (a m : Nat) : wordAddress a + BitVec.ofNat 64 (8*m) = wordAddress (a+m) :=
  (wordAddress_add a m).symm

theorem memory_view_set_reg (s : MachineState) (r : Reg) (v : Word) :
    memoryView (s.setReg r v) = memoryView s := by
  funext w; cases r <;> rfl

theorem memory_view_set_pc (s : MachineState) (p : Word) :
    memoryView (s.setPC p) = memoryView s := rfl

theorem se_0 : signExtend12 (0 : BitVec 12)=BitVec.ofNat 64 (8*0) := by decide
theorem se_8 : signExtend12 (8 : BitVec 12)=BitVec.ofNat 64 (8*1) := by decide
theorem se_16 : signExtend12 (16 : BitVec 12)=BitVec.ofNat 64 (8*2) := by decide
theorem se_24 : signExtend12 (24 : BitVec 12)=BitVec.ofNat 64 (8*3) := by decide
theorem se_32 : signExtend12 (32 : BitVec 12)=BitVec.ofNat 64 (8*4) := by decide
theorem se_40 : signExtend12 (40 : BitVec 12)=BitVec.ofNat 64 (8*5) := by decide
theorem se_48 : signExtend12 (48 : BitVec 12)=BitVec.ofNat 64 (8*6) := by decide
theorem se_56 : signExtend12 (56 : BitVec 12)=BitVec.ofNat 64 (8*7) := by decide
theorem se_64 : signExtend12 (64 : BitVec 12)=BitVec.ofNat 64 (8*8) := by decide

/-- One load/store pair through `x31`. -/
def movePair (s : MachineState) (src : Reg) (o1 o2 : BitVec 12) : MachineState :=
  execInstrBr (execInstrBr s (.LD .x31 src o1)) (.SD .x28 .x31 o2)

theorem move_pair_reg (s : MachineState) (src : Reg) (o1 o2 : BitVec 12) (r : Reg) (keep : r≠.x31) :
    (movePair s src o1 o2).getReg r=s.getReg r := by
  simp [movePair, execInstrBr, Opening.getReg_setMem, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm keep)]

theorem move_pair_pc (s : MachineState) (src : Reg) (o1 o2 : BitVec 12) :
    (movePair s src o1 o2).pc=s.pc+8 := by
  simp only [movePair, execInstrBr, MachineState.setPC, MachineState.setMem, MachineState.setReg]
  cases src <;> simp [BitVec.add_assoc]

theorem move_pair_memory (s : MachineState) (src : Reg) (o1 o2 : BitVec 12) (a b : Nat)
    (keep : src≠.x31) (hs : s.getReg src+signExtend12 o1=wordAddress a)
    (hd : s.getReg .x28+signExtend12 o2=wordAddress b) (ab : b<2^61) (w : Nat) (wb : w<2^61) :
    memoryView (movePair s src o1 o2) w=writeWord (memoryView s) b (memoryView s a) w := by
  have r28 : ((s.setReg .x31 (s.getMem (s.getReg src+signExtend12 o1))).setPC (s.pc+4)).getReg .x28=s.getReg .x28 := by
    simp [MachineState.getReg_setReg_ne]
  have r31 : ((s.setReg .x31 (s.getMem (s.getReg src+signExtend12 o1))).setPC (s.pc+4)).getReg .x31=
      s.getMem (wordAddress a) := by
    simp [MachineState.getReg_setReg_eq, hs]
  have shape : movePair s src o1 o2=
      ((((s.setReg .x31 (s.getMem (s.getReg src+signExtend12 o1))).setPC (s.pc+4)).setMem
        (wordAddress b) (s.getMem (wordAddress a))).setPC (s.pc+4+4)) := by
    unfold movePair
    simp only [execInstrBr]
    rw [r28, hd, r31]
    rfl
  rw [shape, memory_view_set_pc, memory_at_store ab wb, memory_view_set_pc, memory_view_set_reg]
  rfl

/-- Four aligned words from `src` to `x28 + 40`. -/
def copyFourCode (src : Reg) : List Instr :=
  [.LD .x31 src 0, .SD .x28 .x31 40, .LD .x31 src 8, .SD .x28 .x31 48,
   .LD .x31 src 16, .SD .x28 .x31 56, .LD .x31 src 24, .SD .x28 .x31 64]

def copyFourPrefix (s : MachineState) (src : Reg) (n : Nat) : MachineState :=
  ((copyFourCode src).take n).foldl execInstrBr s

def copyFour (s : MachineState) (src : Reg) : MachineState := copyFourPrefix s src 8

theorem copy_four_split (s : MachineState) (src : Reg) :
    copyFour s src=movePair (movePair (movePair (movePair s src 0 40) src 8 48) src 16 56) src 24 64 := rfl

theorem copy_four_prefix_reg (s : MachineState) (src : Reg) (n : Nat) (bound : n≤8) (r : Reg) (keep : r≠.x31) :
    (copyFourPrefix s src n).getReg r=s.getReg r := by
  interval_cases n <;>
    simp [copyFourPrefix, copyFourCode, execInstrBr, Opening.getReg_setMem,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm keep)]

theorem copy_four_prefix_pc (s : MachineState) (src : Reg) (n : Nat) (bound : n≤8) :
    (copyFourPrefix s src n).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  interval_cases n <;>
    (simp only [copyFourPrefix, copyFourCode, List.take, List.foldl, execInstrBr, MachineState.setPC,
      MachineState.setMem, MachineState.setReg]; cases src <;> simp [BitVec.add_assoc]) <;> rfl

theorem copy_four_reg (s : MachineState) (src : Reg) (r : Reg) (keep : r≠.x31) :
    (copyFour s src).getReg r=s.getReg r :=
  copy_four_prefix_reg s src 8 (by decide) r keep

theorem copy_four_pc (s : MachineState) (src : Reg) : (copyFour s src).pc=s.pc+32 :=
  copy_four_prefix_pc s src 8 (by decide)

/-- The copied words land at `d+5 … d+8`; everything else is framed. -/
theorem copy_four_memory (s : MachineState) (src : Reg) (a d : Nat) (keep : src≠.x31) (keep28 : src≠.x28)
    (hs : s.getReg src=wordAddress a) (hd : s.getReg .x28=wordAddress d)
    (ab : a+4≤2^61) (db : d+9≤2^61) (apart : a+4≤d+5 ∨ d+9≤a) (w : Nat) (wb : w<2^61) :
    memoryView (copyFour s src) w=
      if d+5≤w ∧ w<d+9 then memoryView s (a+(w-(d+5))) else memoryView s w := by
  let s1 := movePair s src 0 40
  let s2 := movePair s1 src 8 48
  let s3 := movePair s2 src 16 56
  have reg1 (r : Reg) (k : r≠.x31) : s1.getReg r=s.getReg r := move_pair_reg _ _ _ _ r k
  have reg2 (r : Reg) (k : r≠.x31) : s2.getReg r=s.getReg r := (move_pair_reg _ _ _ _ r k).trans (reg1 r k)
  have reg3 (r : Reg) (k : r≠.x31) : s3.getReg r=s.getReg r := (move_pair_reg _ _ _ _ r k).trans (reg2 r k)
  have h1 (v : Nat) (vb : v<2^61) : memoryView s1 v=writeWord (memoryView s) (d+5) (memoryView s (a+0)) v :=
    move_pair_memory s src 0 40 (a+0) (d+5) keep (by rw [hs,se_0,word_offset_add]) (by rw [hd,se_40,word_offset_add])
      (by omega) v vb
  have h2 (v : Nat) (vb : v<2^61) : memoryView s2 v=writeWord (memoryView s1) (d+6) (memoryView s1 (a+1)) v :=
    move_pair_memory s1 src 8 48 (a+1) (d+6) keep (by rw [reg1 _ keep,hs,se_8,word_offset_add])
      (by rw [reg1 _ (by decide),hd,se_48,word_offset_add]) (by omega) v vb
  have h3 (v : Nat) (vb : v<2^61) : memoryView s3 v=writeWord (memoryView s2) (d+7) (memoryView s2 (a+2)) v :=
    move_pair_memory s2 src 16 56 (a+2) (d+7) keep (by rw [reg2 _ keep,hs,se_16,word_offset_add])
      (by rw [reg2 _ (by decide),hd,se_56,word_offset_add]) (by omega) v vb
  have h4 (v : Nat) (vb : v<2^61) : memoryView (copyFour s src) v=writeWord (memoryView s3) (d+8) (memoryView s3 (a+3)) v :=
    move_pair_memory s3 src 24 64 (a+3) (d+8) keep (by rw [reg3 _ keep,hs,se_24,word_offset_add])
      (by rw [reg3 _ (by decide),hd,se_64,word_offset_add]) (by omega) v vb
  have m1 (v : Nat) (vb : v<2^61) : memoryView s1 v=if v=d+5 then memoryView s a else memoryView s v := by
    rw [h1 v vb]; rfl
  have m2 (v : Nat) (vb : v<2^61) : memoryView s2 v=if v=d+6 then memoryView s (a+1) else memoryView s1 v := by
    rw [h2 v vb, m1 (a+1) (by omega), if_neg (by omega)]; rfl
  have m3 (v : Nat) (vb : v<2^61) : memoryView s3 v=if v=d+7 then memoryView s (a+2) else memoryView s2 v := by
    rw [h3 v vb, m2 (a+2) (by omega), if_neg (by omega), m1 (a+2) (by omega), if_neg (by omega)]; rfl
  have m4 : memoryView (copyFour s src) w=if w=d+8 then memoryView s (a+3) else memoryView s3 w := by
    rw [h4 w wb, m3 (a+3) (by omega), if_neg (by omega), m2 (a+3) (by omega), if_neg (by omega),
      m1 (a+3) (by omega), if_neg (by omega)]; rfl
  rw [m4, m3 w wb, m2 w wb, m1 w wb]
  split_ifs <;> first | omega | (congr 1; omega) | rfl

theorem execute_copy_four (s : MachineState) (src : Reg) (start a d : Nat)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*start)) (room : start+8≤456)
    (code : ∀ i < 8, (packedImage.code[start+i]?).bind decodeInstruction =
      some (.base ((copyFourCode src)[i]?.getD .EBREAK)))
    (keep : src≠.x31) (hs : s.getReg src=wordAddress a) (hd : s.getReg .x28=wordAddress d)
    (ab : a+4≤2^33) (db : d+9≤2^33) : GroupHop s (copyFour s src) 8 := by
  intro fuel
  apply execute_unit_steps (states := copyFourPrefix s src)
  intro i bounded
  refine ⟨.base ((copyFourCode src)[i]?.getD .EBREAK),?_,?_,?_⟩
  · apply fetch_at _ (start+i) _ (by omega) _ (code i bounded)
    rw [copy_four_prefix_pc s src i (by omega),pc]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
    omega
  · have srcReg := copy_four_prefix_reg s src i (by omega) src keep
    have dstReg := copy_four_prefix_reg s src i (by omega) .x28 (by decide)
    have next : copyFourPrefix s src (i+1)=execInstrBr (copyFourPrefix s src i) ((copyFourCode src)[i]?.getD .EBREAK) := by
      interval_cases i <;> rfl
    rw [next]
    interval_cases i
    · apply step_ld; rw [srcReg,hs,se_0,word_offset_add]; exact word_access _ (by omega)
    · apply step_sd; rw [dstReg,hd,se_40,word_offset_add]; exact word_access _ (by omega)
    · apply step_ld; rw [srcReg,hs,se_8,word_offset_add]; exact word_access _ (by omega)
    · apply step_sd; rw [dstReg,hd,se_48,word_offset_add]; exact word_access _ (by omega)
    · apply step_ld; rw [srcReg,hs,se_16,word_offset_add]; exact word_access _ (by omega)
    · apply step_sd; rw [dstReg,hd,se_56,word_offset_add]; exact word_access _ (by omega)
    · apply step_ld; rw [srcReg,hs,se_24,word_offset_add]; exact word_access _ (by omega)
    · apply step_sd; rw [dstReg,hd,se_64,word_offset_add]; exact word_access _ (by omega)
  · interval_cases i <;> rfl

end TwoPermutationPrototype.Quad.Checker
