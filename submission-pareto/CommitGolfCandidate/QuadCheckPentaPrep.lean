import CommitGolfCandidate.QuadCheckPentaPhase

/-! The prepared 200-byte penta workspace of one level (words 369-439): five zero
words, the opened digest in slot `r = n % 5`, and the four proof siblings in slots
`r+1, …, r+4 (mod 5)`. -/
namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

attribute [local irreducible] execute copyFour
attribute [local simp] Opening.getReg_setMem MachineState.getReg_setPC

structure SiblingFacts (s t : MachineState) (q a : Nat) : Prop where
  pc : t.pc=s.pc+52
  slot : t.getReg .x7=BitVec.ofNat 64 ((q+1)%5)
  cursor : t.getReg .x21=wordAddress (a+4)
  saved : ∀ r, r≠.x7 → r≠.x21 → r≠.x28 → r≠.x31 → t.getReg r=s.getReg r
  memory : ∀ w<2^61, memoryView t w=
    if 1605+4*((q+1)%5)≤w ∧ w<1609+4*((q+1)%5) then memoryView s (a+(w-(1605+4*((q+1)%5))))
    else memoryView s w

theorem sibling_facts (s : MachineState) (a q : Nat) (src : s.getReg .x21=wordAddress a)
    (base : s.getReg .x10=wordAddress 1600) (slot : s.getReg .x7=BitVec.ofNat 64 q) (small : q<5)
    (five : s.getReg .x30=5) (far : 1625≤a) (ab : a+4≤2^33) : SiblingFacts s (siblingStep s) q a := by
  let h := siblingHeadPrefix s 4
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
  have hmem : h.mem=s.mem := by
    simp only [h, siblingHeadPrefix, siblingHeadCode, List.take, List.foldl, execInstrBr]
    rfl
  let c := copyFour h .x21
  have creg (r : Reg) (k : r≠.x31) : c.getReg r=h.getReg r := copy_four_reg h .x21 r k
  have whole : siblingStep s=execInstrBr c (.ADDI .x21 .x21 32) := rfl
  have slotSmall : (q+1)%5<5 := Nat.mod_lt _ (by decide)
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [whole]
    simp only [execInstrBr,MachineState.setPC,MachineState.setReg]
    rw [show c.pc=h.pc+32 from copy_four_pc h .x21, sibling_head_prefix_pc s 4 (by decide)]
    simp only [BitVec.add_assoc]
    rfl
  · rw [whole]
    simp [execInstrBr, MachineState.getReg_setReg_ne, creg .x7 (by decide), h7]
  · rw [whole]
    simp only [execInstrBr,MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide),creg .x21 (by decide),hreg .x21 (by decide) (by decide),src,
      show signExtend12 (32 : BitVec 12)=BitVec.ofNat 64 (8*4) by decide,word_offset_add]
  · intro r a7 a21 a28 a31
    rw [whole]
    simp only [execInstrBr,MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm a21),creg r a31,hreg r a7 a28]
  · intro w wb
    have last : memoryView (siblingStep s) w=memoryView c w := by
      rw [whole]; simp only [execInstrBr]; rw [memory_view_set_pc,memory_view_set_reg]
    have copied := copy_four_memory h .x21 a (1600+4*((q+1)%5)) (by decide) (by decide)
      ((hreg .x21 (by decide) (by decide)).trans src) h28 (by omega) (by omega) (by omega) w wb
    have same (v : Nat) : memoryView h v=memoryView s v := by
      simp only [memoryView,MachineState.getMem,hmem]
    rw [last,copied,same,same]
    split_ifs <;> first | rfl | (congr 1; omega)

/-! ### The whole preparation -/

def levelPrep (s : MachineState) : MachineState :=
  execInstrBr (siblingStep (siblingStep (siblingStep (siblingStep (copyFour (phaseA s) .x23)))))
    (.ADDI .x12 .x23 0)

/-- Expected workspace contents after preparation. -/
def levelWord (mem : Memory) (r p w : Nat) : Word :=
  if 1600≤w ∧ w<1605 then 0
  else if 1605≤w ∧ w<1625 then
    (if (w-1605)/4=r then mem (1536+(w-1605)%4) else mem (p+4*(((w-1605)/4+4-r)%5)+(w-1605)%4))
  else mem w

structure LevelPrepFacts (s t : MachineState) (n p : Nat) : Prop where
  pc : t.pc=s.pc+284
  node : t.getReg .x6=BitVec.ofNat 64 (n/5)
  cursor : t.getReg .x21=wordAddress (p+16)
  output : t.getReg .x12=wordAddress 1536
  saved : ∀ r, r≠.x6 → r≠.x7 → r≠.x12 → r≠.x21 → r≠.x28 → r≠.x30 → r≠.x31 → t.getReg r=s.getReg r
  memory : ∀ w<2^61, memoryView t w=levelWord (memoryView s) (n%5) p w
  run : Hop s t 71 89

private theorem pc_offset (a b c : Nat) (h : a+b=c) :
    BitVec.ofNat 64 a+BitVec.ofNat 64 b=BitVec.ofNat 64 c := by
  rw [←BitVec.ofNat_add,h]

theorem level_prep_facts (s : MachineState) (n p : Nat) (bound : n<2^64)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*369))
    (node : s.getReg .x6=BitVec.ofNat 64 n) (base : s.getReg .x10=wordAddress 1600)
    (digest : s.getReg .x23=wordAddress 1536) (src : s.getReg .x21=wordAddress p)
    (far : 1625≤p) (pb : p+16≤2^33) : LevelPrepFacts s (levelPrep s) n p := by
  let a := phaseA s
  have A := phase_a_facts s n bound node base
  let b := copyFour a .x23
  have breg (r : Reg) (k : r≠.x31) : b.getReg r=a.getReg r := copy_four_reg a .x23 r k
  have areg (r : Reg) (k6 : r≠.x6) (k7 : r≠.x7) (k28 : r≠.x28) (k30 : r≠.x30) : a.getReg r=s.getReg r :=
    A.saved r k6 k7 k28 k30
  have rSmall : n%5<5 := Nat.mod_lt _ (by decide)
  have bmem (w : Nat) (wb : w<2^61) : memoryView b w=
      if 1605+4*(n%5)≤w ∧ w<1609+4*(n%5) then memoryView s (1536+(w-(1605+4*(n%5))))
      else if 1600≤w ∧ w<1605 then 0 else memoryView s w := by
    have copied := copy_four_memory a .x23 1536 (1600+4*(n%5)) (by decide) (by decide)
      ((areg .x23 (by decide) (by decide) (by decide) (by decide)).trans digest) A.target
      (by omega) (by omega) (by omega) w wb
    rw [show 1600+4*(n%5)+5=1605+4*(n%5) by omega,show 1600+4*(n%5)+9=1609+4*(n%5) by omega] at copied
    rw [copied]
    split_ifs with h1 h2
    · rw [A.memory _ (by omega),if_neg (by omega)]
    · rw [A.memory _ wb,if_pos h2]
    · rw [A.memory _ wb,if_neg h2]
  -- registers into the sibling chain
  have b7 : b.getReg .x7=BitVec.ofNat 64 (n%5) := (breg .x7 (by decide)).trans A.slot
  have b10 : b.getReg .x10=wordAddress 1600 :=
    (breg .x10 (by decide)).trans ((areg .x10 (by decide) (by decide) (by decide) (by decide)).trans base)
  have b21 : b.getReg .x21=wordAddress p :=
    (breg .x21 (by decide)).trans ((areg .x21 (by decide) (by decide) (by decide) (by decide)).trans src)
  have b30 : b.getReg .x30=5 := (breg .x30 (by decide)).trans A.five
  let c1 := siblingStep b
  have C1 := sibling_facts b p (n%5) b21 b10 b7 rSmall b30 far (by omega)
  let c2 := siblingStep c1
  have C2 := sibling_facts c1 (p+4) ((n%5+1)%5) C1.cursor
    ((C1.saved .x10 (by decide) (by decide) (by decide) (by decide)).trans b10) C1.slot (Nat.mod_lt _ (by decide))
    ((C1.saved .x30 (by decide) (by decide) (by decide) (by decide)).trans b30) (by omega) (by omega)
  let c3 := siblingStep c2
  have C3 := sibling_facts c2 (p+4+4) (((n%5+1)%5+1)%5) C2.cursor
    ((C2.saved .x10 (by decide) (by decide) (by decide) (by decide)).trans
      ((C1.saved .x10 (by decide) (by decide) (by decide) (by decide)).trans b10)) C2.slot (Nat.mod_lt _ (by decide))
    ((C2.saved .x30 (by decide) (by decide) (by decide) (by decide)).trans
      ((C1.saved .x30 (by decide) (by decide) (by decide) (by decide)).trans b30)) (by omega) (by omega)
  let c4 := siblingStep c3
  have C4 := sibling_facts c3 (p+4+4+4) ((((n%5+1)%5+1)%5+1)%5) C3.cursor
    ((C3.saved .x10 (by decide) (by decide) (by decide) (by decide)).trans
      ((C2.saved .x10 (by decide) (by decide) (by decide) (by decide)).trans
        ((C1.saved .x10 (by decide) (by decide) (by decide) (by decide)).trans b10))) C3.slot (Nat.mod_lt _ (by decide))
    ((C3.saved .x30 (by decide) (by decide) (by decide) (by decide)).trans
      ((C2.saved .x30 (by decide) (by decide) (by decide) (by decide)).trans
        ((C1.saved .x30 (by decide) (by decide) (by decide) (by decide)).trans b30))) (by omega) (by omega)
  have whole : levelPrep s=execInstrBr c4 (.ADDI .x12 .x23 0) := rfl
  have csaved (r : Reg) (k7 : r≠.x7) (k21 : r≠.x21) (k28 : r≠.x28) (k31 : r≠.x31) : c4.getReg r=b.getReg r :=
    (C4.saved r k7 k21 k28 k31).trans ((C3.saved r k7 k21 k28 k31).trans
      ((C2.saved r k7 k21 k28 k31).trans (C1.saved r k7 k21 k28 k31)))
  have fsaved (r : Reg) (k12 : r≠.x12) : (levelPrep s).getReg r=c4.getReg r := by
    rw [whole]; simp [execInstrBr, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm k12)]
  have pcA : a.pc=BitVec.ofNat 64 (4096+4*379) := by
    rw [A.pc,pc]; exact pc_offset _ _ _ rfl
  have pcB : b.pc=BitVec.ofNat 64 (4096+4*387) := by
    rw [show b.pc=a.pc+32 from copy_four_pc a .x23,pcA]; exact pc_offset _ _ _ rfl
  have pc1 : c1.pc=BitVec.ofNat 64 (4096+4*400) := by rw [C1.pc,pcB]; exact pc_offset _ _ _ rfl
  have pc2 : c2.pc=BitVec.ofNat 64 (4096+4*413) := by rw [C2.pc,pc1]; exact pc_offset _ _ _ rfl
  have pc3 : c3.pc=BitVec.ofNat 64 (4096+4*426) := by rw [C3.pc,pc2]; exact pc_offset _ _ _ rfl
  have pc4 : c4.pc=BitVec.ofNat 64 (4096+4*439) := by rw [C4.pc,pc3]; exact pc_offset _ _ _ rfl
  have runA : Hop s a 10 16 := execute_phase_a s pc base
  have runB : GroupHop a b 8 := execute_copy_four a .x23 379 1536 (1600+4*(n%5)) pcA (by decide)
    (by intro i hi; interval_cases i <;> rfl) (by decide)
    ((areg .x23 (by decide) (by decide) (by decide) (by decide)).trans digest) A.target (by decide) (by omega)
  have run1 : Hop b c1 13 16 := execute_sibling_step b 387 p pcB (by decide)
    (by intro i hi; interval_cases i <;> rfl) b21 b10 (n%5) b7 rSmall b30 (by omega)
  have run2 : Hop c1 c2 13 16 := execute_sibling_step c1 400 (p+4) pc1 (by decide)
    (by intro i hi; interval_cases i <;> rfl) C1.cursor
    ((C1.saved .x10 (by decide) (by decide) (by decide) (by decide)).trans b10) _ C1.slot (Nat.mod_lt _ (by decide))
    ((C1.saved .x30 (by decide) (by decide) (by decide) (by decide)).trans b30) (by omega)
  have run3 : Hop c2 c3 13 16 := execute_sibling_step c2 413 (p+4+4) pc2 (by decide)
    (by intro i hi; interval_cases i <;> rfl) C2.cursor
    ((C2.saved .x10 (by decide) (by decide) (by decide) (by decide)).trans
      ((C1.saved .x10 (by decide) (by decide) (by decide) (by decide)).trans b10)) _ C2.slot (Nat.mod_lt _ (by decide))
    ((C2.saved .x30 (by decide) (by decide) (by decide) (by decide)).trans
      ((C1.saved .x30 (by decide) (by decide) (by decide) (by decide)).trans b30)) (by omega)
  have run4 : Hop c3 c4 13 16 := execute_sibling_step c3 426 (p+4+4+4) pc3 (by decide)
    (by intro i hi; interval_cases i <;> rfl) C3.cursor
    ((C3.saved .x10 (by decide) (by decide) (by decide) (by decide)).trans
      ((C2.saved .x10 (by decide) (by decide) (by decide) (by decide)).trans
        ((C1.saved .x10 (by decide) (by decide) (by decide) (by decide)).trans b10))) _ C3.slot (Nat.mod_lt _ (by decide))
    ((C3.saved .x30 (by decide) (by decide) (by decide) (by decide)).trans
      ((C2.saved .x30 (by decide) (by decide) (by decide) (by decide)).trans
        ((C1.saved .x30 (by decide) (by decide) (by decide) (by decide)).trans b30))) (by omega)
  have runE : GroupHop c4 (levelPrep s) 1 := by
    rw [whole]
    exact hop_one_unit (fetch_at _ 439 _ (by decide) pc4 rfl) rfl rfl
  refine ⟨?_,?_,?_,?_,?_,?_,(((((runA.thenDo runB).thenDo run1).thenDo run2).thenDo run3).thenDo run4).thenDo runE⟩
  · rw [whole]
    simp only [execInstrBr,MachineState.setPC,MachineState.setReg]
    rw [C4.pc,C3.pc,C2.pc,C1.pc,show b.pc=a.pc+32 from copy_four_pc a .x23,A.pc]
    simp only [BitVec.add_assoc]
    rfl
  · rw [fsaved .x6 (by decide),csaved .x6 (by decide) (by decide) (by decide) (by decide),breg .x6 (by decide)]
    exact A.node
  · rw [fsaved .x21 (by decide),C4.cursor]
  · rw [whole]
    simp only [execInstrBr,MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide),csaved .x23 (by decide) (by decide) (by decide) (by decide),
      breg .x23 (by decide),areg .x23 (by decide) (by decide) (by decide) (by decide),digest,se_0]
    rfl
  · intro r k6 k7 k12 k21 k28 k30 k31
    rw [fsaved r k12,csaved r k7 k21 k28 k31,breg r k31]
    exact areg r k6 k7 k28 k30
  · intro w wb
    have last : memoryView (levelPrep s) w=memoryView c4 w := by
      rw [whole]; simp only [execInstrBr]; rw [memory_view_set_pc,memory_view_set_reg]
    -- words at or above the proof are never written by the chain
    have high3 (v : Nat) (vb : v<2^61) (above : 1625≤v) : memoryView c3 v=memoryView s v := by
      rw [C3.memory v vb,if_neg (by omega),C2.memory v vb,if_neg (by omega),C1.memory v vb,if_neg (by omega),
        bmem v vb,if_neg (by omega),if_neg (by omega)]
    have high2 (v : Nat) (vb : v<2^61) (above : 1625≤v) : memoryView c2 v=memoryView s v := by
      rw [C2.memory v vb,if_neg (by omega),C1.memory v vb,if_neg (by omega),
        bmem v vb,if_neg (by omega),if_neg (by omega)]
    have high1 (v : Nat) (vb : v<2^61) (above : 1625≤v) : memoryView c1 v=memoryView s v := by
      rw [C1.memory v vb,if_neg (by omega),bmem v vb,if_neg (by omega),if_neg (by omega)]
    have highb (v : Nat) (vb : v<2^61) (above : 1625≤v) : memoryView b v=memoryView s v := by
      rw [bmem v vb,if_neg (by omega),if_neg (by omega)]
    rw [last,C4.memory w wb]
    split_ifs with g4
    · rw [high3 _ (by omega) (by omega)]
      unfold levelWord
      split_ifs <;> first | rfl | omega | (congr 1; omega)
    rw [C3.memory w wb]
    split_ifs with g3
    · rw [high2 _ (by omega) (by omega)]
      unfold levelWord
      split_ifs <;> first | rfl | omega | (congr 1; omega)
    rw [C2.memory w wb]
    split_ifs with g2
    · rw [high1 _ (by omega) (by omega)]
      unfold levelWord
      split_ifs <;> first | rfl | omega | (congr 1; omega)
    rw [C1.memory w wb]
    split_ifs with g1
    · rw [highb _ (by omega) (by omega)]
      unfold levelWord
      split_ifs <;> first | rfl | omega | (congr 1; omega)
    rw [bmem w wb]
    unfold levelWord
    split_ifs <;> first | rfl | omega | (congr 1; omega)

end TwoPermutationPrototype.Quad.Checker
