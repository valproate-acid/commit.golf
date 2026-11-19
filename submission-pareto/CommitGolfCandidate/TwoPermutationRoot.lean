import CommitGolfCandidate.TwoPermutationParentEntry
import CommitGolfCandidate.CopyRefinement

/-! Root copy and HALT of the actual commitment. The four loads/stores use
the ABI commitment buffer, which is disjoint from the full trapdoor. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute

def rootOps : List Instr :=
  [.LD .x31 .x9 32,.SD .x8 .x31 0,.LD .x31 .x9 40,.SD .x8 .x31 8,
   .LD .x31 .x9 48,.SD .x8 .x31 16,.LD .x31 .x9 56,.SD .x8 .x31 24,
   .ADDI .x5 .x0 1,.ADDI .x10 .x0 0]

def rootPrefix (s : MachineState) (i : Nat) := (rootOps.take i).foldl execInstrBr s

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

theorem execute_root (s : MachineState) (pc : s.pc=8216) (heap : s.getReg .x9=4294971424)
    (out : s.getReg .x8=4294971392) (fuel : Nat) :
    execute commitImage (11+fuel) s true = pure ⟨.success,rootPrefix s 10,11,0⟩ := by
  have body (left : Nat) :
      execute commitImage (10+left) s true =
        (do let result ← execute commitImage left (rootPrefix s 10) true
            return result.charge 10 0) := by
    apply execute_unit_steps (states := rootPrefix s)
    intro i inside
    refine ⟨.base ((rootOps[i]?).getD .EBREAK),?_,?_,?_⟩
    · interval_cases i <;> simp only [rootPrefix,rootOps,List.take,List.foldl,execInstrBr,MachineState.setPC,fetch,pc] <;> rfl
    · have access := root_access s heap out i inside
      interval_cases i <;>
        simp only [rootOps,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at access ⊢ <;>
        simp only [ordinaryStep,access,↓reduceIte] <;> rfl
    · interval_cases i <;> rfl
  have endpc : (rootPrefix s 10).pc=8256 := by
    change s.pc+4+4+4+4+4+4+4+4+4+4=_
    rw [pc];rfl
  have fetched : fetch commitImage (rootPrefix s 10)=some (.base .ECALL) := by rw [fetch,endpc];rfl
  have halt : (rootPrefix s 10).getReg .x5=1 := rfl
  have success : (rootPrefix s 10).getReg .x10=0 := rfl
  rw [show 11+fuel=10+(fuel+1) by omega,body,execute,fetched]
  simp only [halt,success];rfl

private def oldCopyBase (s : MachineState) := (s.setReg .x23 (s.getReg .x9+32)).setReg .x25 (s.getReg .x8)

theorem root_copy_memory (s : MachineState) :
    (rootPrefix s 10).mem = (openingCopyState (oldCopyBase s)).mem := by
  rw [opening_copy_expansion]
  simp [rootPrefix,rootOps,oldCopyBase,List.foldl,execInstrBr,signExtend12,MachineState.getReg,
    MachineState.setReg,MachineState.setPC,MachineState.setMem,MachineState.getMem,BitVec.add_assoc]

theorem root_copy_output (s : MachineState) (heap : s.getReg .x9=4294971424) (out : s.getReg .x8=4294971392) :
    readBuffer (rootPrefix s 10) 4294971392 32=nodeDigest s 1 := by
  rw [read_buffer_memory_congr _ _ (root_copy_memory s),opening_copy_digest _ (8*treeWord 1) 4294971392]
  · rfl
  · change s.getReg .x9+32=_;rw [heap];rfl
  · exact out
  all_goals decide

theorem root_copy_trap_word (s : MachineState) (out : s.getReg .x8=4294971392)
    (word : Nat) (above : 4294971424 ≤ 8*word) (inside : word < 2^33) :
    memoryView (rootPrefix s 10) word=memoryView s word := by
  change (rootPrefix s 10).mem _ = s.mem _
  rw [root_copy_memory]
  apply opening_copy_memory_outside
  intro j
  change wordAddress word ≠ s.getReg .x8+BitVec.ofNat 64 (8*j.val)
  rw [out]
  intro same
  have e := congrArg BitVec.toNat same
  have w := word_address_value (word := word) (by omega)
  change (wordAddress word).toNat=(BitVec.ofNat 64 4294971392+BitVec.ofNat 64 (8*j.val)).toNat at e
  rw [w,←BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := j.isLt;omega)] at e
  have := j.isLt;omega

end TwoPermutationPrototype.RV64
