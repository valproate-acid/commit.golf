import CommitGolfCandidate.QuadCheckPentaCopy

/-! The straight-line parts of one penta level (words 369-439): the slot
computation with the zero prefix, the opened-digest copy, and the four rotated
sibling copies. Every phase is an exact fold of the image's instructions. -/
namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

attribute [local irreducible] execute
attribute [local simp] Opening.getReg_setMem MachineState.getReg_setPC

@[local simp] private theorem phase_zero (s : MachineState) : s.getReg .x0=0#64 := rfl

/-- `execute_unit_steps` with a per-instruction cycle cost. -/
theorem execute_cost_steps (image : Image) (count fuel : Nat)
    (states : Nat → MachineState) (cost : Nat → Nat) (allowCoins : Bool)
    (trace : ∀ i < count, ∃ instruction,
      fetch image (states i) = some instruction ∧
      ordinaryStep (states i) instruction = some (states (i + 1)) ∧
      instructionCycles instruction = cost i) :
    execute image (count + fuel) (states 0) allowCoins =
      (do let result ← execute image fuel (states count) allowCoins
          return result.charge (∑ i ∈ Finset.range count, cost i) 0) := by
  induction count generalizing states cost with
  | zero => simp [Execution.charge]
  | succ count ih =>
    obtain ⟨instruction, fetched, stepped, costed⟩ := trace 0 (by omega)
    rw [Nat.succ_add, execute_ordinary_step image instruction _ _ _ _ fetched stepped, costed]
    have tail := ih (fun i => states (i + 1)) (fun i => cost (i+1)) (by
      intro i hi
      exact trace (i + 1) (by omega))
    simp only [tail, bind_assoc, pure_bind]
    simp only [Execution.charge, Finset.sum_range_succ', Nat.zero_add]
    congr 1
    funext result
    congr 2
    omega

theorem ofNat_remu (n k : Nat) (bound : n<2^64) (small : k<2^64) (positive : 0<k) :
    rv64_remu (BitVec.ofNat 64 n) (BitVec.ofNat 64 k)=BitVec.ofNat 64 (n%k) := by
  have ne : (BitVec.ofNat 64 k == 0#64)=false := by
    apply beq_false_of_ne
    intro eq
    have := congrArg BitVec.toNat eq
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at this
    simp at this; omega
  unfold rv64_remu
  rw [ne]
  apply BitVec.eq_of_toNat_eq
  simp only [Bool.false_eq_true, ite_false, BitVec.toNat_umod, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt small]
  exact (Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ positive) (by omega))).symm

theorem ofNat_divu (n k : Nat) (bound : n<2^64) (small : k<2^64) (positive : 0<k) :
    rv64_divu (BitVec.ofNat 64 n) (BitVec.ofNat 64 k)=BitVec.ofNat 64 (n/k) := by
  have ne : (BitVec.ofNat 64 k == 0#64)=false := by
    apply beq_false_of_ne
    intro eq
    have := congrArg BitVec.toNat eq
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at this
    simp at this; omega
  unfold rv64_divu
  rw [ne]
  apply BitVec.eq_of_toNat_eq
  simp only [Bool.false_eq_true, ite_false, BitVec.toNat_udiv, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt small]
  exact (Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) bound)).symm

theorem slot_address (q : Nat) (small : q<5) :
    wordAddress 1600+(BitVec.ofNat 64 q <<< (5 : Nat))=wordAddress (1600+4*q) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add,BitVec.toNat_shiftLeft]
  simp only [wordAddress,BitVec.toNat_ofNat]
  rw [Nat.shiftLeft_eq]
  omega

/-! ### Phase A: slot, quotient, zero prefix -/

def phaseACode : List Instr :=
  [.ADDI .x30 .x0 5, .REMU .x7 .x6 .x30, .DIVU .x6 .x6 .x30,
   .SD .x10 .x0 0, .SD .x10 .x0 8, .SD .x10 .x0 16, .SD .x10 .x0 24, .SD .x10 .x0 32,
   .SLLI .x28 .x7 5, .ADD .x28 .x10 .x28]

def phaseAPrefix (s : MachineState) (n : Nat) : MachineState := (phaseACode.take n).foldl execInstrBr s

def phaseA (s : MachineState) : MachineState := phaseAPrefix s 10

def phaseACost (i : Nat) : Nat := if i=1 ∨ i=2 then 4 else 1

theorem phase_a_prefix_x10 (s : MachineState) (n : Nat) (bound : n≤10) :
    (phaseAPrefix s n).getReg .x10=s.getReg .x10 := by
  interval_cases n <;>
    simp [phaseAPrefix, phaseACode, execInstrBr, MachineState.getReg_setReg_ne]

theorem phase_a_prefix_pc (s : MachineState) (n : Nat) (bound : n≤10) :
    (phaseAPrefix s n).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  interval_cases n <;>
    simp [phaseAPrefix, phaseACode, execInstrBr, MachineState.setPC, MachineState.setMem,
      MachineState.setReg, BitVec.add_assoc] <;> rfl

theorem execute_phase_a (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (4096+4*369))
    (base : s.getReg .x10=wordAddress 1600) : Hop s (phaseA s) 10 16 := by
  intro fuel
  have run := execute_cost_steps packedImage 10 fuel (phaseAPrefix s) phaseACost false (by
    intro i bounded
    refine ⟨.base (phaseACode[i]?.getD .EBREAK),?_,?_,?_⟩
    · apply fetch_at _ (369+i) _ (by omega)
      · rw [phase_a_prefix_pc s i (by omega),pc]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
        omega
      · interval_cases i <;> rfl
    · have reg := phase_a_prefix_x10 s i (by omega)
      have next : phaseAPrefix s (i+1)=execInstrBr (phaseAPrefix s i) (phaseACode[i]?.getD .EBREAK) := by
        interval_cases i <;> rfl
      rw [next]
      interval_cases i
      · rfl
      · rfl
      · rfl
      · apply step_sd; rw [reg,base,se_0,word_offset_add]; exact word_access _ (by omega)
      · apply step_sd; rw [reg,base,se_8,word_offset_add]; exact word_access _ (by omega)
      · apply step_sd; rw [reg,base,se_16,word_offset_add]; exact word_access _ (by omega)
      · apply step_sd; rw [reg,base,se_24,word_offset_add]; exact word_access _ (by omega)
      · apply step_sd; rw [reg,base,se_32,word_offset_add]; exact word_access _ (by omega)
      · rfl
      · rfl
    · interval_cases i <;> rfl)
  have sum : ∑ i ∈ Finset.range 10, phaseACost i=16 := by simp [Finset.sum_range_succ, phaseACost]
  rw [sum] at run
  exact run

private theorem zero_store (t : MachineState) (off : BitVec 12) (b : Nat) (bb : b<2^61)
    (addr : t.getReg .x10+signExtend12 off=wordAddress b) (w : Nat) (wb : w<2^61) :
    memoryView (execInstrBr t (.SD .x10 .x0 off)) w=writeWord (memoryView t) b 0 w := by
  have shape : execInstrBr t (.SD .x10 .x0 off)=(t.setMem (wordAddress b) 0#64).setPC (t.pc+4) := by
    simp only [execInstrBr]
    rw [addr]
    rfl
  rw [shape,memory_view_set_pc,memory_at_store bb wb]
  rfl

structure PhaseAFacts (s t : MachineState) (n : Nat) : Prop where
  pc : t.pc=s.pc+40
  slot : t.getReg .x7=BitVec.ofNat 64 (n%5)
  node : t.getReg .x6=BitVec.ofNat 64 (n/5)
  five : t.getReg .x30=5
  target : t.getReg .x28=wordAddress (1600+4*(n%5))
  saved : ∀ r, r≠.x6 → r≠.x7 → r≠.x28 → r≠.x30 → t.getReg r=s.getReg r
  memory : ∀ w<2^61, memoryView t w=if 1600≤w ∧ w<1605 then 0 else memoryView s w

theorem phase_a_facts (s : MachineState) (n : Nat) (bound : n<2^64)
    (node : s.getReg .x6=BitVec.ofNat 64 n) (base : s.getReg .x10=wordAddress 1600) :
    PhaseAFacts s (phaseA s) n := by
  let t3 := phaseAPrefix s 3
  have r3 (r : Reg) (a : r≠.x6) (b : r≠.x7) (c : r≠.x30) : t3.getReg r=s.getReg r := by
    simp [t3, phaseAPrefix, phaseACode, execInstrBr, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm a),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm b), MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm c)]
  have t30 : t3.getReg .x30=5 := by
    simp [t3, phaseAPrefix, phaseACode, execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
      signExtend12]
  have t7 : t3.getReg .x7=BitVec.ofNat 64 (n%5) := by
    simp [t3, phaseAPrefix, phaseACode, execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
      signExtend12, node]
    exact ofNat_remu n 5 bound (by decide) (by decide)
  have t6 : t3.getReg .x6=BitVec.ofNat 64 (n/5) := by
    simp [t3, phaseAPrefix, phaseACode, execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
      signExtend12, node]
    exact ofNat_divu n 5 bound (by decide) (by decide)
  have tm : t3.mem=s.mem := by
    simp only [t3, phaseAPrefix, phaseACode, List.take, List.foldl, execInstrBr]
    rfl
  have t10 : t3.getReg .x10=wordAddress 1600 := (r3 .x10 (by decide) (by decide) (by decide)).trans base
  let z1 := execInstrBr t3 (.SD .x10 .x0 0)
  let z2 := execInstrBr z1 (.SD .x10 .x0 8)
  let z3 := execInstrBr z2 (.SD .x10 .x0 16)
  let z4 := execInstrBr z3 (.SD .x10 .x0 24)
  let z5 := execInstrBr z4 (.SD .x10 .x0 32)
  have zr1 (r : Reg) : z1.getReg r=t3.getReg r := by simp [z1, execInstrBr]
  have zr2 (r : Reg) : z2.getReg r=t3.getReg r := by simp [z2, execInstrBr, zr1]
  have zr3 (r : Reg) : z3.getReg r=t3.getReg r := by simp [z3, execInstrBr, zr2]
  have zr4 (r : Reg) : z4.getReg r=t3.getReg r := by simp [z4, execInstrBr, zr3]
  have zr5 (r : Reg) : z5.getReg r=t3.getReg r := by simp [z5, execInstrBr, zr4]
  have m1 (w : Nat) (wb : w<2^61) : memoryView z1 w=writeWord (memoryView t3) 1600 0 w :=
    zero_store t3 0 1600 (by decide) (by rw [t10,se_0,word_offset_add]) w wb
  have m2 (w : Nat) (wb : w<2^61) : memoryView z2 w=writeWord (memoryView z1) 1601 0 w :=
    zero_store z1 8 1601 (by decide) (by rw [zr1,t10,se_8,word_offset_add]) w wb
  have m3 (w : Nat) (wb : w<2^61) : memoryView z3 w=writeWord (memoryView z2) 1602 0 w :=
    zero_store z2 16 1602 (by decide) (by rw [zr2,t10,se_16,word_offset_add]) w wb
  have m4 (w : Nat) (wb : w<2^61) : memoryView z4 w=writeWord (memoryView z3) 1603 0 w :=
    zero_store z3 24 1603 (by decide) (by rw [zr3,t10,se_24,word_offset_add]) w wb
  have m5 (w : Nat) (wb : w<2^61) : memoryView z5 w=writeWord (memoryView z4) 1604 0 w :=
    zero_store z4 32 1604 (by decide) (by rw [zr4,t10,se_32,word_offset_add]) w wb
  let t9 := execInstrBr z5 (.SLLI .x28 .x7 5)
  have whole : phaseA s=execInstrBr t9 (.ADD .x28 .x10 .x28) := rfl
  have r9 (r : Reg) (k : r≠.x28) : t9.getReg r=t3.getReg r := by
    simp [t9, execInstrBr, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm k), zr5]
  have fin (r : Reg) (k : r≠.x28) : (phaseA s).getReg r=t3.getReg r := by
    rw [whole]; simp [execInstrBr, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm k), r9 r k]
  have fmem : (phaseA s).mem=z5.mem := by
    rw [whole]; simp only [t9, execInstrBr]; rfl
  have slotSmall : n%5<5 := Nat.mod_lt _ (by decide)
  refine ⟨?_,(fin .x7 (by decide)).trans t7,(fin .x6 (by decide)).trans t6,(fin .x30 (by decide)).trans t30,
    ?_,?_,?_⟩
  · exact (phase_a_prefix_pc s 10 (by decide)).trans rfl
  · rw [whole]
    simp only [execInstrBr,MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide),r9 .x10 (by decide),t10]
    have shift : t9.getReg .x28=BitVec.ofNat 64 (n%5) <<< (5 : Nat) := by
      simp [t9, execInstrBr, MachineState.getReg_setReg_eq, zr5, t7]
    rw [shift]
    exact slot_address _ slotSmall
  · intro r a b c d
    exact (fin r c).trans (r3 r a b d)
  · intro w wb
    have view : memoryView (phaseA s) w=memoryView z5 w := by
      simp only [memoryView,MachineState.getMem,fmem]
    have origin : memoryView t3 w=memoryView s w := by
      simp only [memoryView,MachineState.getMem,tm]
    rw [view,m5 w wb]
    simp only [writeWord]
    rw [m4 w wb]
    simp only [writeWord]
    rw [m3 w wb]
    simp only [writeWord]
    rw [m2 w wb]
    simp only [writeWord]
    rw [m1 w wb]
    simp only [writeWord,origin]
    split_ifs <;> first | rfl | omega

/-! ### One rotated sibling: slot `(q+1)%5`, four words from the proof, cursor +32 -/

def siblingHeadCode : List Instr :=
  [.ADDI .x7 .x7 1, .REMU .x7 .x7 .x30, .SLLI .x28 .x7 5, .ADD .x28 .x10 .x28]

def siblingHeadPrefix (s : MachineState) (n : Nat) : MachineState := (siblingHeadCode.take n).foldl execInstrBr s

def siblingStep (s : MachineState) : MachineState :=
  execInstrBr (copyFour (siblingHeadPrefix s 4) .x21) (.ADDI .x21 .x21 32)

theorem sibling_head_prefix_pc (s : MachineState) (n : Nat) (bound : n≤4) :
    (siblingHeadPrefix s n).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  interval_cases n <;>
    simp [siblingHeadPrefix, siblingHeadCode, execInstrBr, MachineState.setPC, MachineState.setReg,
      BitVec.add_assoc] <;> rfl

theorem execute_sibling_step (s : MachineState) (start a : Nat)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*start)) (room : start+13≤456)
    (code : ∀ i < 13, (packedImage.code[start+i]?).bind decodeInstruction =
      some (.base ((siblingHeadCode++copyFourCode .x21++[.ADDI .x21 .x21 32])[i]?.getD .EBREAK)))
    (src : s.getReg .x21=wordAddress a) (base : s.getReg .x10=wordAddress 1600)
    (q : Nat) (slot : s.getReg .x7=BitVec.ofNat 64 q) (small : q<5) (five : s.getReg .x30=5)
    (ab : a+4≤2^33) : Hop s (siblingStep s) 13 16 := by
  let h := siblingHeadPrefix s 4
  have head : Hop s h 4 7 := by
    intro fuel
    have run := execute_cost_steps packedImage 4 fuel (siblingHeadPrefix s) (fun i => if i=1 then 4 else 1) false (by
      intro i bounded
      refine ⟨.base (siblingHeadCode[i]?.getD .EBREAK),?_,?_,?_⟩
      · apply fetch_at _ (start+i) _ (by omega)
        · rw [sibling_head_prefix_pc s i (by omega),pc]
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
          omega
        · have c := code i (by omega)
          interval_cases i <;> exact c
      · interval_cases i <;> rfl
      · interval_cases i <;> rfl)
    have sum : ∑ i ∈ Finset.range 4, (fun i => if i=1 then 4 else 1) i=7 := by simp [Finset.sum_range_succ]
    rw [sum] at run
    exact run
  have hreg (r : Reg) (k1 : r≠.x7) (k2 : r≠.x28) : h.getReg r=s.getReg r := by
    simp [h, siblingHeadPrefix, siblingHeadCode, execInstrBr, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm k1),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm k2)]
  have h7 : h.getReg .x7=BitVec.ofNat 64 ((q+1)%5) := by
    have raw : h.getReg .x7=rv64_remu (s.getReg .x7+signExtend12 1) (s.getReg .x30) := by
      simp [h, siblingHeadPrefix, siblingHeadCode, execInstrBr, MachineState.getReg_setReg_ne,
        MachineState.getReg_setReg_eq]
    rw [raw,slot,five,show signExtend12 (1 : BitVec 12)=BitVec.ofNat 64 1 by decide,←BitVec.ofNat_add]
    exact ofNat_remu (q+1) 5 (by omega) (by decide) (by decide)
  have h28 : h.getReg .x28=wordAddress (1600+4*((q+1)%5)) := by
    have raw : h.getReg .x28=h.getReg .x10+(h.getReg .x7 <<< (5 : Nat)) := by
      simp [h, siblingHeadPrefix, siblingHeadCode, execInstrBr, MachineState.getReg_setReg_ne,
        MachineState.getReg_setReg_eq]
    rw [raw,h7,hreg .x10 (by decide) (by decide),base]
    exact slot_address _ (Nat.mod_lt _ (by decide))
  have hpc : h.pc=BitVec.ofNat 64 (4096+4*(start+4)) := by
    rw [sibling_head_prefix_pc s 4 (by decide),pc,←BitVec.ofNat_add]
    congr 1
  have copy : GroupHop h (copyFour h .x21) 8 :=
    execute_copy_four h .x21 (start+4) a (1600+4*((q+1)%5)) hpc (by omega)
      (by intro i bi; have c := code (4+i) (by omega); rw [show start+(4+i)=start+4+i by omega] at c
          interval_cases i <;> exact c)
      (by decide) ((hreg .x21 (by decide) (by decide)).trans src) h28 ab (by omega)
  have last : GroupHop (copyFour h .x21) (siblingStep s) 1 := by
    apply hop_one_unit
    · apply fetch_at _ (start+12) _ (by omega)
      · rw [copy_four_pc,hpc,show (32 : Word)=BitVec.ofNat 64 32 from rfl,←BitVec.ofNat_add]
        congr 1
      · exact code 12 (by omega)
    · rfl
    · rfl
  exact (head.thenDo copy).thenDo last

end TwoPermutationPrototype.Quad.Checker
