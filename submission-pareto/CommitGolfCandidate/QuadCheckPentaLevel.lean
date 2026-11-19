import CommitGolfCandidate.QuadCheckPentaPrep
import CommitGolfCandidate.QuadCheckPentaInput
import CommitGolfCandidate.TwoPermutationPentaSpec
import CommitGolfCandidate.TwoPermutationSyscall
import CommitGolfCandidate.TwoPermutationCheckerReplay
import CommitGolfCandidate.TwoPermutationCheckerLowerRun
import CommitGolfCandidate.TwoPermutationHeapInvariant

/-! One complete penta level (words 369-442): preparation, the permutation call
on the actual 200-byte workspace (exactly `pentaInput` of the five slots), and
the level latch. -/
namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (check_recorded_bind check_recorded_map)
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

/-- Slot `t` of the prepared workspace: the opened digest at `r = n % 5`, the
`((t+4-r) % 5)`-th proof sibling elsewhere. -/
def prepChild (s : MachineState) (r p : Nat) (t : Fin 5) : BitVec 256 :=
  if t.val=r then readBuffer s 12288 32 else readBuffer s (8*p+32*((t.val+4-r)%5)) 32

theorem level_prep_children (s : MachineState) (n p : Nat) (facts : LevelPrepFacts s (levelPrep s) n p)
    (pb : p+16≤2^33) : levelChildren (levelPrep s)=prepChild s (n%5) p := by
  funext t
  have tb := t.isLt
  unfold levelChildren prepChild
  split
  · rename_i same
    apply (read_digest_eq_iff _ _ _ _ (by omega) (by decide)).mpr
    intro m mb
    have w := facts.memory (1605+4*t.val+m) (by omega)
    unfold levelWord at w
    rw [if_neg (by omega),if_pos (by omega),if_pos (by omega)] at w
    have e1 : BitVec.ofNat 64 (12840+32*t.val+8*m)=wordAddress (1605+4*t.val+m) := by
      unfold wordAddress; congr 1; omega
    have e2 : BitVec.ofNat 64 (12288+8*m)=wordAddress (1536+m) := by
      unfold wordAddress; congr 1; omega
    rw [e1,e2]
    refine w.trans ?_
    change memoryView s _=memoryView s _
    congr 1; omega
  · rename_i other
    apply (read_digest_eq_iff _ _ _ _ (by omega) (by omega)).mpr
    intro m mb
    have w := facts.memory (1605+4*t.val+m) (by omega)
    unfold levelWord at w
    rw [if_neg (by omega),if_pos (by omega),if_neg (by omega)] at w
    have e1 : BitVec.ofNat 64 (12840+32*t.val+8*m)=wordAddress (1605+4*t.val+m) := by
      unfold wordAddress; congr 1; omega
    have e2 : BitVec.ofNat 64 (8*p+32*((t.val+4-n%5)%5)+8*m)=wordAddress (p+4*((t.val+4-n%5)%5)+m) := by
      unfold wordAddress; congr 1; omega
    rw [e1,e2]
    refine w.trans ?_
    change memoryView s _=memoryView s _
    congr 1; omega

theorem level_prep_input (s : MachineState) (n p : Nat) (facts : LevelPrepFacts s (levelPrep s) n p)
    (pb : p+16≤2^33) :
    packBuffer (window (memoryView (levelPrep s)) 1600)=pentaInput (prepChild s (n%5) p) := by
  rw [workspace_penta_input,level_prep_children s n p facts pb]
  intro i ib
  have w := facts.memory (1600+i) (by omega)
  unfold levelWord at w
  rw [if_pos (by omega)] at w
  exact w

/-! ### Call and latch -/

def levelLatch (t : MachineState) : MachineState :=
  execInstrBr (execInstrBr t (.ADDI .x29 .x29 4095)) (.BNE .x29 .x0 7900)

def levelReply (s : MachineState) (answer : Block) : MachineState :=
  levelLatch (writeBits (levelPrep s) (wordAddress 1536) answer)

def levelInput (s : MachineState) : Block := packBuffer (window (memoryView (levelPrep s)) 1600)

/-- The full level as a program with one public query. -/
def levelCall (s : MachineState) : OracleComp World MachineState := do
  let answer ← World.query (.inr (.inr (.inl (levelInput s))))
  return levelReply s answer

attribute [local irreducible] execute writeBits levelPrep

theorem level_latch_post (t : MachineState) (pc : t.pc=BitVec.ofNat 64 (4096+4*441)) (left : Nat)
    (positive : 0<left) (small : left≤11) (counter : t.getReg .x29=BitVec.ofNat 64 left) :
    (levelLatch t).pc=(if left=1 then BitVec.ofNat 64 (4096+4*443) else BitVec.ofNat 64 (4096+4*369)) ∧
    (levelLatch t).getReg .x29=BitVec.ofNat 64 (left-1) ∧
    (∀ r, r≠.x29 → (levelLatch t).getReg r=t.getReg r) ∧ (levelLatch t).mem=t.mem := by
  have dec : t.getReg .x29+signExtend12 (4095 : BitVec 12)=BitVec.ofNat 64 (left-1) := by
    rw [counter,show signExtend12 (4095 : BitVec 12)=BitVec.ofNat 64 (2^64-1) from rfl,←BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  let u := execInstrBr t (.ADDI .x29 .x29 4095)
  have u29 : u.getReg .x29=BitVec.ofNat 64 (left-1) := by
    simp only [u,execInstrBr,MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide),dec]
  have upc : u.pc=BitVec.ofNat 64 (4096+4*442) := by
    simp only [u,execInstrBr,MachineState.setPC,MachineState.setReg,pc]; rfl
  have ureg (r : Reg) (k : r≠.x29) : u.getReg r=t.getReg r := by
    simp only [u,execInstrBr,MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm k)
  have whole : levelLatch t=execInstrBr u (.BNE .x29 .x0 7900) := rfl
  have zero : u.getReg .x0=0#64 := rfl
  refine ⟨?_,?_,?_,?_⟩
  · rw [whole]
    simp only [execInstrBr,u29,zero]
    by_cases one : left=1
    · subst one
      rw [if_pos rfl]
      simp only [show (BitVec.ofNat 64 (1-1) != 0#64)=false from rfl,Bool.false_eq_true,ite_false,
        MachineState.setPC,upc]
      rfl
    · rw [if_neg one]
      have ne : BitVec.ofNat 64 (left-1)≠0#64 := by
        intro eq
        have := congrArg BitVec.toNat eq
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at this
        simp at this; omega
      simp only [bne_iff_ne,ne_eq,ne,not_false_eq_true,ite_true,MachineState.setPC,upc]
      rfl
  · rw [whole]; simp only [execInstrBr]; split <;> simpa only [MachineState.getReg_setPC] using u29
  · intro r k
    rw [whole]; simp only [execInstrBr]; split <;> simpa only [MachineState.getReg_setPC] using ureg r k
  · rw [whole]; simp only [execInstrBr]; split <;> rfl

theorem execute_level_latch (t : MachineState) (pc : t.pc=BitVec.ofNat 64 (4096+4*441)) :
    GroupHop t (levelLatch t) 2 := by
  let u := execInstrBr t (.ADDI .x29 .x29 4095)
  have upc : u.pc=BitVec.ofNat 64 (4096+4*442) := by
    simp only [u,execInstrBr,MachineState.setPC,MachineState.setReg,pc]; rfl
  have first : GroupHop t u 1 := hop_one_unit (fetch_at _ 441 _ (by decide) pc rfl) rfl rfl
  have last : GroupHop u (levelLatch t) 1 := hop_one_unit (fetch_at _ 442 _ (by decide) upc rfl) rfl rfl
  exact first.thenDo last

structure LevelReady (s : MachineState) (n p left : Nat) : Prop where
  pc : s.pc=BitVec.ofNat 64 (4096+4*369)
  node : s.getReg .x6=BitVec.ofNat 64 n
  bound : n<2^64
  base : s.getReg .x10=wordAddress 1600
  digest : s.getReg .x23=wordAddress 1536
  cursor : s.getReg .x21=wordAddress p
  far : 1625≤p
  room : p+16≤2^33
  selector : s.getReg .x5=0
  size : s.getReg .x11=200
  primitive : s.getReg .x13=1
  counter : s.getReg .x29=BitVec.ofNat 64 left
  positive : 0<left
  small : left≤11

theorem level_prep_ready (s : MachineState) (n p left : Nat) (ready : LevelReady s n p left) :
    LevelPrepFacts s (levelPrep s) n p :=
  level_prep_facts s n p ready.bound ready.pc ready.node ready.base ready.digest ready.cursor ready.far ready.room

theorem execute_level (s : MachineState) (n p left : Nat) (ready : LevelReady s n p left) (fuel : Nat) :
    execute packedImage (74+fuel) s false = do
      let next ← levelCall s
      let result ← execute packedImage fuel next false
      return result.charge 99 1 := by
  have facts := level_prep_ready s n p left ready
  let t := levelPrep s
  have keep (r : Reg) (k6 : r≠.x6) (k7 : r≠.x7) (k12 : r≠.x12) (k21 : r≠.x21) (k28 : r≠.x28) (k30 : r≠.x30)
      (k31 : r≠.x31) : t.getReg r=s.getReg r := facts.saved r k6 k7 k12 k21 k28 k30 k31
  have tpc : t.pc=BitVec.ofNat 64 (4096+4*440) := by
    rw [facts.pc,ready.pc]; rfl
  have fetched := fetch_at t 440 .ECALL (by decide) tpc rfl
  have call := execute_permutation_call packedImage (2+fuel) t false 1600 1536 (by decide) (by decide)
    ((keep .x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.base)
    facts.output
    ((keep .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.selector)
    ((keep .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.size)
    ((keep .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.primitive)
    fetched
  rw [show 74+fuel=71+(2+fuel+1) by omega,facts.run,call]
  simp only [levelCall,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro answer _
  have replied : (writeBits t (wordAddress 1536) answer).pc=BitVec.ofNat 64 (4096+4*441) := by
    unfold writeBits
    change t.pc+4=_
    rw [tpc]; rfl
  rw [execute_level_latch _ replied]
  simp only [bind_assoc,pure_bind,Execution.charge,Nat.zero_add,←Nat.add_assoc]
  rfl

theorem level_call_rows (oracle : Oracle) (s : MachineState) :
    checkEvaluation oracle (recordRows (levelCall s))=
      ((levelReply s (oracle.permutation (levelInput s)),
        [.permutation (levelInput s) (oracle.permutation (levelInput s))]),1) := by
  simp only [levelCall,record_rows_query,check_evaluation_public_bind,check_evaluation_map,
    record_rows_pure,check_evaluation_pure]
  rfl

end TwoPermutationPrototype.Quad.Checker
