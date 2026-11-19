import CommitGolfCandidate.TwoPermutationPackedGroupView

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
attribute [local irreducible] execute packedImage

theorem GroupBlock.hop (block : GroupBlock) (s : MachineState)
    (here : s.pc=BitVec.ofNat 64 (4096+4*block.start)) (valid : block.Valid s) :
    GroupHop s (block.done s) block.words.length :=
  group_block_execute block s here valid

private def nextWord (left : Nat) : Fin 4 := ⟨(3-left)%4,Nat.mod_lt _ (by decide)⟩

def compareGroup : Nat → MachineState → MachineState × Nat
  | 0,s => (GroupBlock.duplicate.done s,1)
  | left+1,s =>
    let i := nextWord left
    let t := (GroupBlock.compare i).done s
    if sameGroupWord s i then
      let result := compareGroup left t
      (result.1,3+result.2)
    else (t,3)

def GroupReadable (s : MachineState) :=
  ∀ i : Fin 4, (GroupBlock.compare i).Valid s

/-- The comparison has no writes. A mismatch exits on the first unequal
stored word; reaching the record latch authenticates all four words. -/
theorem compare_group_run (s : MachineState) (left : Nat) (bounded : left≤4)
    (here : s.pc=BitVec.ofNat 64 (4096+4*(258-3*left)))
    (readable : GroupReadable s) :
    let result := compareGroup left s
    GroupHop s result.1 result.2 ∧ result.2≤3*left+1 ∧ result.1.mem=s.mem ∧
      (∀ r : Reg, r≠.x29 → r≠.x30 → result.1.getReg r=s.getReg r) ∧
      result.1.pc=if ∀ i : Fin 4, 4-left≤ i.val → sameGroupWord s i then 0x1434 else 0x15b0 := by
  classical
  induction left generalizing s with
  | zero =>
    have pc : s.pc=0x1408 := here
    have good : ∀ i : Fin 4, 4-0≤ i.val → sameGroupWord s i := by intro i hi;omega
    obtain ⟨after,mem,regs⟩ := group_duplicate_view s pc
    simp only [compareGroup]
    exact ⟨GroupBlock.hop .duplicate s pc trivial,by decide,mem,fun r _ _ => regs r,
      by simpa only [if_pos good] using after⟩
  | succ left ih =>
    let i := nextWord left
    let t := (GroupBlock.compare i).done s
    have val : i.val=3-left := by
      change (3-left)%4=3-left
      apply Nat.mod_eq_of_lt
      omega
    have site : s.pc=BitVec.ofNat 64 (4096+4*(246+3*i.val)) := by rw [val,here];congr 1;omega
    have hop : GroupHop s t 3 := (GroupBlock.compare i).hop s site (readable i)
    obtain ⟨pc,memory,regs⟩ := group_compare_view s i site
    have equival (j : Fin 4) : sameGroupWord t j ↔ sameGroupWord s j := by
      simp only [sameGroupWord,regs _ (by decide : Reg.x28≠.x29) (by decide : Reg.x28≠.x30),
        regs _ (by decide : Reg.x23≠.x29) (by decide : Reg.x23≠.x30),MachineState.getMem,memory,t]
    have validT : GroupReadable t := by
      intro j
      change accessValid (t.getReg .x28+_) 8=true ∧ accessValid (t.getReg .x23+_) 8=true
      rw [regs _ (by decide) (by decide),regs _ (by decide) (by decide)]
      exact readable j
    by_cases matchWord : sameGroupWord s i
    · have pc' : t.pc=BitVec.ofNat 64 (4096+4*(258-3*left)) := by
        rw [show t.pc=_ from pc,if_pos matchWord,val]
        congr 1
        omega
      obtain ⟨run,cost,mem,kept,exit⟩ := ih t (by omega) pc' validT
      have allWords : (∀ j : Fin 4, 4-left≤ j.val → sameGroupWord t j) ↔
          (∀ j : Fin 4, 4-(left+1)≤ j.val → sameGroupWord s j) := by
        constructor
        · intro later j hj
          by_cases eq : j=i
          · simpa only [eq] using matchWord
          · have apart : j.val ≠ i.val := fun h => eq (Fin.ext h)
            exact (equival j).mp (later j (by omega))
        · intro all j hj
          exact (equival j).mpr (all j (by omega))
      simp only [compareGroup,show sameGroupWord s (nextWord left) from matchWord,↓reduceIte]
      exact ⟨hop.thenDo run,by change 3+(compareGroup left t).2≤_; omega,mem.trans memory,
        fun r a b => (kept r a b).trans (regs r a b),by simpa only [allWords] using exit⟩
    · have bad : ¬∀ j : Fin 4, 4-(left+1)≤ j.val → sameGroupWord s j :=
        fun h => matchWord (h i (by omega))
      simp only [compareGroup,show ¬sameGroupWord s (nextWord left) from matchWord,↓reduceIte]
      exact ⟨hop,by omega,memory,regs,by simpa only [if_neg matchWord,if_neg bad] using pc⟩

end TwoPermutationPrototype.Packed.Checker
