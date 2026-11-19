import CommitGolfCandidate.QuadCommitPentaLayouts
import CommitGolfCandidate.TwoPermutationRoot

/-! The fixed pieces around the level passes: clearing the ragged slots of the last level-0
group, the root node (written at trapdoor offset 32, the old heap node 1) and the unchanged root
copy and HALT. -/
namespace TwoPermutationPrototype.Quad.Commit.Penta
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
attribute [local irreducible] leafCode nodeCode decodeInstruction execute writeBits

private theorem leaf_zero_table : ∀ t : Fin 16,
    (leafZeroWords[t.val]?).bind decodeInstruction = some (.base (.SD .x12 .x0 (BitVec.ofNat 12 (32+8*t.val)))) := by
  unfold decodeInstruction;decide +kernel

theorem leaf_zero_segment : ZeroSegment 45201 32 16 := by
  intro t ht
  have at' := code_segment_at (setupWords ++ leafCode ++ leafLatchWords) leafZeroWords
    (levelsCode ++ rootSetupWords ++ rootWords) (by unfold image;simp only [List.append_assoc]) t ht
  rw [show (setupWords ++ leafCode ++ leafLatchWords).length=45201 by
    simp only [List.length_append,Leaves.leaf_code_word_count];rfl] at at'
  rw [at']
  exact leaf_zero_table ⟨t,ht⟩

theorem levels_code_length : levelsCode.length=191316 := by
  unfold levelsCode
  simp only [List.length_append,level_code_length_1,level_code_length_2,level_code_length_3,level_code_length_4,
    level_code_length_5,level_code_length_6,level_code_length_7,level_code_length_8,level_code_length_9,
    level_code_length_10]

def rootHead : List (BitVec 32) := setupWords ++ leafCode ++ leafLatchWords ++ leafZeroWords ++ levelsCode

theorem root_head_length : rootHead.length=236533 := by
  unfold rootHead
  simp only [List.length_append,Leaves.leaf_code_word_count,levels_code_length]
  rfl

def rootNodeOps : List Instr :=
  [.LUI .x10 376848,.ADDI .x10 .x10 4056,.ADD .x10 .x9 .x10,.ADDI .x12 .x9 32]

private theorem root_setup_table : ∀ i : Fin 5,
    (rootSetupWords[i.val]?).bind decodeInstruction = some (.base (((rootNodeOps++[.ECALL])[i.val]?).getD .EBREAK)) := by
  unfold decodeInstruction;decide +kernel

theorem fetch_root_setup (i : Nat) (hi : i<5) (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (4096+4*(236533+i))) :
    fetch image s=some (.base (((rootNodeOps++[.ECALL])[i]?).getD .EBREAK)) := by
  apply fetch_code_index s (236533+i) (by omega) pc
  have at' := code_segment_at rootHead rootSetupWords rootWords
    (by unfold image rootHead;simp only [List.append_assoc]) i hi
  rw [root_head_length] at at'
  rw [at']
  exact root_setup_table ⟨i,hi⟩

def rootNode (s : MachineState) (i : Nat) := (rootNodeOps.take i).foldl execInstrBr s

theorem root_node_regs (s : MachineState) (x9 : s.getReg .x9=4294971424) :
    (rootNode s 4).getReg .x10=wordAddress (pentaGroupWord 10 0) ∧
    (rootNode s 4).getReg .x12=wordAddress (heapWord 1) := by
  refine ⟨?_,?_⟩ <;>
  dsimp [rootNode,rootNodeOps,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg] <;>
  simp only [show s.regs .x9=4294971424 from x9] <;> rfl

theorem root_node_keep (s : MachineState) (reg : Reg) (h10 : reg≠.x10) (h12 : reg≠.x12) :
    (rootNode s 4).getReg reg=s.getReg reg := by
  simp only [rootNode,rootNodeOps,List.take,List.foldl,execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h10),MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h12)]

theorem root_node_mem (s : MachineState) : (rootNode s 4).mem=s.mem := rfl

theorem execute_root_node (s : MachineState) (pc : s.pc=950228) (x9 : s.getReg .x9=4294971424)
    (x5 : s.getReg .x5=0) (x11 : s.getReg .x11=200) (x13 : s.getReg .x13=1) (fuel : Nat) :
    execute image (5+fuel) s true =
      (do let reply ← World.query (.inr (.inr (.inl (packBuffer (window (memoryView s) (pentaGroupWord 10 0))))))
          let out ← execute image fuel (writeBits (rootNode s 4) (wordAddress (heapWord 1)) reply) true
          return out.charge 12 1) := by
  have setup : execute image (4+(1+fuel)) s true =
      (do let out ← execute image (1+fuel) (rootNode s 4) true
          return out.charge 4 0) := by
    apply CommitGolfCandidate.execute_unit_steps (states := rootNode s)
    intro i hi
    refine ⟨.base ((rootNodeOps[i]?).getD .EBREAK),?_,?_,?_⟩
    · have here : (rootNode s i).pc=BitVec.ofNat 64 (4096+4*(236533+i)) := by
        interval_cases i <;> simp only [rootNode,rootNodeOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
      have f := fetch_root_setup i (by omega) _ here
      interval_cases i <;> exact f
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  obtain ⟨src,dst⟩ := root_node_regs s x9
  have callPC : (rootNode s 4).pc=BitVec.ofNat 64 (4096+4*(236533+4)) := by
    simp only [rootNode,rootNodeOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc];rfl
  have call := execute_permutation_call image fuel (rootNode s 4) true (pentaGroupWord 10 0) (heapWord 1)
    (by decide) (by decide) src dst ((root_node_keep s .x5 (by decide) (by decide)).trans x5)
    ((root_node_keep s .x11 (by decide) (by decide)).trans x11)
    ((root_node_keep s .x13 (by decide) (by decide)).trans x13) (fetch_root_setup 4 (by decide) _ callPC)
  have view : window (memoryView (rootNode s 4)) (pentaGroupWord 10 0) = (window (memoryView s) (pentaGroupWord 10 0) : Words 25) := by
    funext t;exact congrFun (root_node_mem s) _
  rw [view] at call
  rw [show 5+fuel=4+(fuel+1) by omega,Nat.add_comm fuel 1,setup,Nat.add_comm 1 fuel,call]
  simp only [bind_assoc,pure_bind]
  apply bind_congr;intro a
  apply bind_congr;intro r
  simp only [Execution.charge]
  congr 2 <;> omega

/-! ### Root copy and HALT (the root node sits at trapdoor offset 32) -/

private theorem root_decoded (i : Fin 11) :
    (rootWords[i.val]?).bind decodeInstruction=some (.base (((rootOps++[.ECALL])[i.val]?).getD .EBREAK)) := by
  revert i;decide +kernel

theorem fetch_root (s : MachineState) (i : Nat) (inside : i<11)
    (pc : s.pc=BitVec.ofNat 64 (950248+4*i)) :
    fetch image s=some (.base (((rootOps++[.ECALL])[i]?).getD .EBREAK)) := by
  apply fetch_code_index s (236538+i) (by omega) (by rw [pc];congr 1 <;> omega)
  have atIndex := code_segment_at (rootHead++rootSetupWords) rootWords []
    (by unfold image rootHead;simp only [List.append_assoc,List.append_nil]) i
    (Nat.lt_of_lt_of_le inside (by decide))
  rw [List.length_append,root_head_length] at atIndex
  change image.code[236538+i]?=_ at atIndex
  rw [atIndex];exact root_decoded ⟨i,inside⟩

private theorem root_access (s : MachineState) (heap : s.getReg .x9=4294971424)
    (out : s.getReg .x8=4294971392) (i : Nat) (hi : i<10) :
    memoryArgumentsValid (rootPrefix s i) ((rootOps[i]?).getD .EBREAK) = true := by
  interval_cases i
  · change accessValid (s.getReg .x9+32) 8=true;rw [heap];decide
  · change accessValid (s.getReg .x8+0) 8=true;rw [out];decide
  · change accessValid (s.getReg .x9+40) 8=true;rw [heap];decide
  · change accessValid (s.getReg .x8+8) 8=true;rw [out];decide
  · change accessValid (s.getReg .x9+48) 8=true;rw [heap];decide
  · change accessValid (s.getReg .x8+16) 8=true;rw [out];decide
  · change accessValid (s.getReg .x9+56) 8=true;rw [heap];decide
  · change accessValid (s.getReg .x8+24) 8=true;rw [out];decide
  · rfl
  · rfl

theorem execute_root (state : MachineState) (pc : state.pc=950248)
    (heap : state.getReg .x9=4294971424) (out : state.getReg .x8=4294971392) (fuel : Nat) :
    execute image (11+fuel) state true = pure ⟨.success,rootPrefix state 10,11,0⟩ := by
  have prefixPC (i : Nat) (inside : i<11) :
      (rootPrefix state i).pc=BitVec.ofNat 64 (950248+4*i) := by
    interval_cases i <;>
      simp only [rootPrefix,rootOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
  have run (left : Nat) :
      execute image (10+left) state true =
        (do let result ← execute image left (rootPrefix state 10) true
            return result.charge 10 0) := by
    apply CommitGolfCandidate.execute_unit_steps (states := rootPrefix state)
    intro i inside
    refine ⟨.base ((rootOps[i]?).getD .EBREAK),?_,?_,?_⟩
    · have fetched := fetch_root (rootPrefix state i) i (by omega) (prefixPC i (by omega))
      interval_cases i <;> exact fetched
    · have access := root_access state heap out i inside
      interval_cases i <;>
        simp only [rootOps,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at access ⊢ <;>
        simp only [ordinaryStep,access,↓reduceIte] <;> rfl
    · interval_cases i <;> rfl
  have fetched : fetch image (rootPrefix state 10)=some (.base .ECALL) :=
    fetch_root (rootPrefix state 10) 10 (by decide) (prefixPC 10 (by decide))
  have halt : (rootPrefix state 10).getReg .x5=1 := rfl
  have success : (rootPrefix state 10).getReg .x10=0 := rfl
  rw [show 11+fuel=10+(fuel+1) by omega,run,execute,fetched]
  simp only [halt,success]
  rfl

end TwoPermutationPrototype.Quad.Commit.Penta
