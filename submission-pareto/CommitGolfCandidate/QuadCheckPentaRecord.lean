import CommitGolfCandidate.QuadCheckPentaLoop
import CommitGolfCandidate.QuadCheckPentaRecordCode
import CommitGolfCandidate.QuadRecordLeafBlock
import CommitGolfCandidate.QuadRecordLeafMeaning

/-! One complete penta record: setup, nonce stage and pinned leaf (unchanged
8d2a211 code), the entry into the penta block, eleven levels, the commitment
comparison, and either the rejecting exit or the record latch. -/
namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Quad (PentaPath PentaOpening pentaSlot)
open TwoPermutationPrototype.Quad.RecordLeaf
open TwoPermutationPrototype.Checker (beginRecord honestIndex check_recorded_bind check_recorded_map
  aligned_digest_frame)
open TwoPermutationPrototype.Packed (copy_field_execute)
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem penta_index_count (i : Nat) (inside : i<LENGTH) : ∀ k, i/5^k<pentaCount k := by
  intro k
  induction k with
  | zero => simpa [pentaCount] using inside
  | succ k ih =>
    rw [pentaCount,pow_succ,←Nat.div_div_eq_div_mul]
    omega

theorem penta_index_root (i : Nat) (inside : i<LENGTH) : i/5^11=0 := by
  apply Nat.div_eq_of_lt
  change i<16777216 at inside
  change i<48828125
  omega

/-- The record's first sibling word (eight-aligned, right after the salt). -/
def siblingWord (ordinal : Nat) : Nat := 1350566926+178*ordinal

theorem sibling_word_bytes (ordinal : Nat) : 8*siblingWord ordinal=checkProofByte ordinal+16 := by
  unfold siblingWord checkProofByte; omega

structure RecordOutcome where
  state : MachineState
  steps : Nat
  cycles : Nat
  rows : List PublicRow
  accepted : Bool

noncomputable def recordOutcome (oracle : Oracle) (ordinal : Nat) (index : Index) (s : MachineState) :
    RecordOutcome := by
  classical
  let raw := rawLeaf oracle ordinal index s
  let e := entryState raw.1
  let levels := levelsRun oracle 11 e
  let branch := branchState (compareState levels.1)
  exact if (compareState levels.1).getReg .x31=0#64 then
      ⟨latchState branch,875,1164,raw.2++levels.2,true⟩
    else ⟨branch,870,1159,raw.2++levels.2,false⟩

structure RecordFacts (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (before : MachineState) (out : RecordOutcome) : Prop where
  steps : out.steps≤2048
  run : ∀ fuel,
    let tail := checkEvaluation oracle (recordRows (execute packedImage fuel out.state false))
    checkEvaluation oracle (recordRows (execute packedImage (out.steps+fuel) before false)) =
      ((tail.1.1.charge out.cycles 13,out.rows++tail.1.2),13+tail.2)
  rejected : out.accepted=false → out.state.pc=0x15b0
  cursor : out.accepted=true → RecordCursor input (ordinal+1) out.state
  frame : out.accepted=true → RecordInputFrame input (ordinal+1) out.state
  opening : out.accepted=true →
    let index := honestIndex input.positions ordinal present
    PentaOpening oracle index.val (input.values index) input.commitment out.rows
  honest : ∀ message salts, input=honestCheckInput oracle message input.positions salts → out.accepted=true

attribute [local irreducible] execute readBuffer checkEvaluation recordRows levelsRun entryState compareState
  branchState latchState

private theorem nonce_stage_run (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (s : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal s) (fuel : Nat) :
    execute packedImage (16+fuel) (beginRecord s 6) false =
      (do let result ← execute packedImage fuel (staged s) false; return result.charge 16 0) :=
  copy_field_execute (fieldCode .nonce) _ _ _ (stage_ready input ordinal h s fits cursor) fuel false

theorem raw_digest_rows (oracle : Oracle) (ordinal : Nat) (index : Index) (s : MachineState) :
    let message := window (memoryView (staged s)) (checkSourceWord ordinal+5)
    let nonce := checkerNonce (staged s)
    let a := pinnedFirstRow oracle.permutation message
    let b := pinnedSecondRow oracle.permutation index nonce a.2 message
    (rawLeaf oracle ordinal index s).2=[.permutation a.1 a.2,.permutation b.1 b.2] ∧
      readBuffer (rawLeaf oracle ordinal index s).1 12288 32=outputDigest b.2 := by
  unfold rawLeaf
  rw [checker_leaf_rows]
  exact ⟨rfl,checker_leaf_digest _ _ _ _⟩

private theorem saved_cases (r : Reg) (keep : r≠.x6 ∧ r≠.x7 ∧ r≠.x8 ∧ r≠.x10 ∧ r≠.x11 ∧ r≠.x12 ∧ r≠.x13 ∧
    r≠.x18 ∧ r≠.x19 ∧ r≠.x21 ∧ r≠.x28 ∧ r≠.x29 ∧ r≠.x30 ∧ r≠.x31) : True := trivial

theorem record_facts (oracle : Oracle) (input : CheckInput) (ordinal : Nat) (present : ordinal < input.positions.card)
    (s : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal s)
    (framed : RecordInputFrame input ordinal s) :
    RecordFacts oracle input ordinal present s
      (recordOutcome oracle ordinal (honestIndex input.positions ordinal present).val s) := by
  let item := honestIndex input.positions ordinal present
  let idx := item.val
  let query := leafQueries (staged s) (checkSourceWord ordinal) idx
  let raw := rawLeaf oracle ordinal idx s
  let e := entryState raw.1
  let levels := levelsRun oracle 11 e
  let cmp := compareState levels.1
  let branch := branchState cmp
  have card := checker_positions_bound input
  have indexBound : idx.val<16777216 := idx.isLt
  have geometry := quad_record_geometry input ordinal present fits
  obtain ⟨rawPc,rawNode,rawKept,rawFrame⟩ := raw_view oracle input ordinal present s fits cursor framed
  have readyLeaf := leaf_ready input ordinal present s fits cursor framed
  have rawSize : raw.1.getReg .x11=200 ∧ raw.1.getReg .x13=1 := by
    dsimp only [raw]
    unfold rawLeaf
    rw [checker_leaf_rows]
    exact ⟨(checker_leaf_preserved_register _ _ _ _ .x11 (by decide) (by decide) (by decide)).trans readyLeaf.size,
      (checker_leaf_preserved_register _ _ _ _ .x13 (by decide) (by decide) (by decide)).trans readyLeaf.primitive⟩
  have rawKeep (r : Reg) (a : r≠.x6) (b : r≠.x28) (c : r≠.x10) (d : r≠.x11) (f : r≠.x13) (g : r≠.x12)
      (h : r≠.x31) : raw.1.getReg r=s.getReg r := rawKept r a b c d f g h
  have entry := entry_post raw.1 rawPc (by
    rw [rawKeep .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),cursor.pair])
  obtain ⟨ePc0,e210,e100,e290,eKeep0,eMem0⟩ := entry
  have ePc : e.pc=BitVec.ofNat 64 (4096+4*369) := ePc0
  have e21 : e.getReg .x21=raw.1.getReg .x21+16 := e210
  have e10 : e.getReg .x10=wordAddress 1600 := e100
  have e29 : e.getReg .x29=BitVec.ofNat 64 11 := e290
  have eKeep (r : Reg) (a : r≠.x10) (b : r≠.x21) (c : r≠.x29) : e.getReg r=raw.1.getReg r := eKeep0 r a b c
  have eMem : e.mem=raw.1.mem := eMem0
  -- the loop
  let P0 := siblingWord ordinal
  have P0bytes := sibling_word_bytes ordinal
  have far : 1625≤P0 := by unfold P0 siblingWord; omega
  have room : P0+16*11≤2^33 := by unfold P0 siblingWord; omega
  have readyLoop : LevelReady e (idx.val/5^0) (P0+16*0) 11 := by
    have k (r : Reg) (a : r≠.x10) (b : r≠.x21) (c : r≠.x29) (d : r≠.x6) (f : r≠.x28) (g : r≠.x11)
        (h : r≠.x13) (i : r≠.x12) (j : r≠.x31) : e.getReg r=s.getReg r :=
      (eKeep r a b c).trans (rawKeep r d f a g h i j)
    refine ⟨ePc,?_,by simp; omega,e10,?_,?_,by omega,by omega,?_,?_,?_,e29,by decide,le_rfl⟩
    · rw [eKeep .x6 (by decide) (by decide) (by decide),rawNode,pow_zero,Nat.div_one]
    · rw [k .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide),cursor.digest]
    · rw [e21,rawKeep .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        cursor.proof]
      unfold wordAddress
      rw [show (16 : Word)=BitVec.ofNat 64 16 from rfl,←BitVec.ofNat_add,
        show checkProofByte ordinal+16=8*(P0+16*0) by unfold P0 siblingWord checkProofByte; omega]
    · rw [k .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide),cursor.selector]
    · rw [eKeep .x11 (by decide) (by decide) (by decide)]; exact rawSize.1
    · rw [eKeep .x13 (by decide) (by decide) (by decide)]; exact rawSize.2
  have loop := loop_facts oracle idx.val P0 (by omega) far room 11 0 e (by decide) (fun _ => readyLoop)
    (fun h => absurd h (by decide))
  have lvPc : levels.1.pc=BitVec.ofNat 64 (4096+4*443) := loop.pc (by decide)
  have lvKeep (r : Reg) (a : r≠.x6) (b : r≠.x7) (c : r≠.x12) (d : r≠.x21) (f : r≠.x28) (g : r≠.x29)
      (h : r≠.x30) (i : r≠.x31) (j : r≠.x10) (l : r≠.x11) (m : r≠.x13) : levels.1.getReg r=s.getReg r :=
    (loop.saved r a b c d f g h i).trans ((eKeep r j d g).trans (rawKeep r a f j l m c i))
  have lv23 : levels.1.getReg .x23=wordAddress 1536 :=
    (lvKeep .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans cursor.digest
  have lv9 : levels.1.getReg .x9=wordAddress 536871424 :=
    (lvKeep .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans (cursor.commitment.trans rfl)
  have cmpPost := compare_post levels.1 lv23 lv9
  have cmpPc : cmp.pc=BitVec.ofNat 64 (4096+4*458) := by
    refine (compare_state_pc levels.1).trans ?_
    rw [lvPc,←BitVec.ofNat_add]
  have cmpKeep (r : Reg) (a : r≠.x29) (b : r≠.x30) (c : r≠.x31) : cmp.getReg r=levels.1.getReg r :=
    compare_state_reg levels.1 r a b c
  -- memory frames back to the record start
  have viewEq (a b : MachineState) (same : a.mem=b.mem) (w : Nat) : memoryView a w=memoryView b w := by
    simp only [memoryView,MachineState.getMem,same]
  have backFrame (w : Nat) (wb : w<2^33) (out1 : w<checkSourceWord ordinal ∨ checkSourceWord ordinal+26≤w)
      (out2 : 1625≤w) : memoryView levels.1 w=memoryView s w :=
    (loop.frame w wb (by omega) (by omega)).trans ((viewEq _ _ eMem w).trans (rawFrame w wb out1 (by omega)))
  have commitmentWords : readBuffer levels.1 (8*536871424) 32=input.commitment := by
    refine (aligned_digest_frame s levels.1 536871424 (fun offset bounded =>
      backFrame _ (by omega) (Or.inl (by unfold checkSourceWord; omega)) (by omega))).trans ?_
    exact record_input_root input ordinal s framed
  -- the trace
  have meaning := raw_digest_rows oracle ordinal idx s
  have values := staged_entry_words input ordinal present s fits cursor framed
  dsimp only at meaning
  rw [values] at meaning
  have startDigest : readBuffer e 12288 32=outputDigest
      (pinnedSecondRow oracle.permutation idx (checkerNonce (staged s))
        (pinnedFirstRow oracle.permutation (entryWords (input.values item))).2 (entryWords (input.values item))).2 :=
    (read_buffer_memory_congr _ _ eMem _ _).trans meaning.2
  have outcomeAccept (yes : cmp.getReg .x31=0#64) :
      recordOutcome oracle ordinal idx s=⟨latchState branch,875,1164,raw.2++levels.2,true⟩ := by
    unfold recordOutcome; rw [if_pos yes]
  have outcomeReject (no : ¬cmp.getReg .x31=0#64) :
      recordOutcome oracle ordinal idx s=⟨branch,870,1159,raw.2++levels.2,false⟩ := by
    unfold recordOutcome; rw [if_neg no]
  -- the honest climb
  have honestRoot (message : Message) (salts : CompleteSaltTape)
      (canonical : input=honestCheckInput oracle message input.positions salts) :
      readBuffer levels.1 12288 32=input.commitment := by
    let leaves := Honest.honestLeaves oracle message salts
    let penta := Honest.honestPenta oracle
    have loaded : RecordInputFrame (honestCheckInput oracle message input.positions salts) ordinal s :=
      Eq.mp (congrArg (fun data => RecordInputFrame data ordinal s) canonical) framed
    have digest := meaning.2
    rw [staged_honest_nonce_words oracle input ordinal present s fits cursor framed message salts canonical,
      canonical_entry_value oracle input message salts item canonical] at digest
    have leafDigest : readBuffer e 12288 32=pentaNode penta leaves 0 (idx.val/5^0) := by
      apply (read_buffer_memory_congr _ _ eMem _ _).trans
      refine digest.trans ((honest_row_digest oracle message salts idx).trans ?_)
      simp only [pow_zero,Nat.div_one,pentaNode,dif_pos idx.isLt]
      rfl
    have climb : ∀ lvl, 0≤lvl → lvl<0+11 →
        (oracle.permutation (pentaInput (loopChild e idx.val P0 lvl (pentaNode penta leaves lvl (idx.val/5^lvl))))).extractLsb' 0 256=
          pentaNode penta leaves (lvl+1) (idx.val/5^(lvl+1)) := by
      intro lvl _ deep
      let m := idx.val/5^(lvl+1)
      have hm : m=idx.val/5^(lvl+1) := rfl
      have split : idx.val/5^lvl=5*m+idx.val/5^lvl%5 := by
        have := Nat.div_add_mod (idx.val/5^lvl) 5
        rw [Nat.div_div_eq_div_mul,←pow_succ] at this
        omega
      have children : loopChild e idx.val P0 lvl (pentaNode penta leaves lvl (idx.val/5^lvl))=pentaGroup penta leaves lvl m := by
        funext t
        unfold loopChild pentaGroup
        split
        · rename_i same
          rw [split,same]
        · rename_i other
          have j4 : (t.val+4-idx.val/5^lvl%5)%5<4 := by
            have := t.isLt; have := Nat.mod_lt (idx.val/5^lvl) (show 0<5 by decide); omega
          have frame : readBuffer e (8*(P0+16*lvl)+32*((t.val+4-idx.val/5^lvl%5)%5)) 32=
              readBuffer s (checkProofByte ordinal+(16+128*lvl+32*((t.val+4-idx.val/5^lvl%5)%5))) 32 := by
            rw [show 8*(P0+16*lvl)+32*((t.val+4-idx.val/5^lvl%5)%5)=
              8*(P0+16*lvl+4*((t.val+4-idx.val/5^lvl%5)%5)) by omega,
              show checkProofByte ordinal+(16+128*lvl+32*((t.val+4-idx.val/5^lvl%5)%5))=
              8*(P0+16*lvl+4*((t.val+4-idx.val/5^lvl%5)%5)) by omega]
            apply aligned_digest_frame s e
            intro offset bounded
            exact (viewEq _ _ eMem _).trans (rawFrame _ (by omega)
              (Or.inr (by unfold checkSourceWord P0 siblingWord at *; omega)) (by unfold P0 siblingWord at *; omega))
          have sib : readBuffer s (checkProofByte ordinal+(16+128*lvl+32*((t.val+4-idx.val/5^lvl%5)%5))) 32=
              pentaNode penta leaves lvl (pentaNeighbour idx lvl ((t.val+4-idx.val/5^lvl%5)%5)) :=
            quad_record_sibling oracle message input.positions salts ordinal lvl _ present deep j4 s loaded
          rw [frame,sib]
          unfold pentaNeighbour pentaRot
          congr 1
          dsimp only [Fin.val_mk]
          have := t.isLt; have := Nat.mod_lt (idx.val/5^lvl) (show 0<5 by decide)
          rw [hm]
          omega
      rw [children]
      have count := penta_index_count idx.val idx.isLt (lvl+1)
      rw [penta_node_succ penta leaves lvl m count]
      rfl
    have final : readBuffer levels.1 12288 32=pentaNode penta leaves (0+11) (idx.val/5^(0+11)) :=
      loop.honest (pentaNode penta leaves) climb leafDigest
    refine final.trans ?_
    rw [show 0+11=11 from rfl,penta_index_root idx.val idx.isLt,canonical]
    rfl
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · by_cases yes : cmp.getReg .x31=0#64
    · rw [outcomeAccept yes]; show 875≤2048; decide
    · rw [outcomeReject yes]; show 870≤2048; decide
  · intro fuel
    have access : accessValid (s.getReg .x8) 8=true := by
      rw [cursor.index]; apply word_access; unfold checkIndexWord; omega
    have counted : (checkEvaluation oracle (recordRows query)).2=2 := by
      dsimp only [query]; rw [checker_leaf_rows]
    have entryPC := cursor.pc.trans (ite_eq_right (by omega))
    have common : ∀ more,
        checkEvaluation oracle (recordRows (execute packedImage (36+4+74*11+15+1+more) s false))=
          let tail := checkEvaluation oracle (recordRows (execute packedImage more branch false))
          ((tail.1.1.charge 1159 13,(raw.2++levels.2)++tail.1.2),13+tail.2) := by
      intro more
      rw [show 36+4+74*11+15+1+more=6+(16+(14+(4+(74*11+(15+(1+more)))))) by omega,
        execute_record_setup s entryPC _ access]
      simp only [bind_pure_comp,check_recorded_map]
      rw [nonce_stage_run input ordinal present s fits cursor]
      simp only [bind_pure_comp,check_recorded_map]
      rw [execute_checker_leaf (leaf_ready input ordinal present s fits cursor framed),check_recorded_bind]
      simp only [bind_pure_comp,check_recorded_map]
      erw [execute_entry raw.1 rawPc]
      simp only [bind_pure_comp,check_recorded_map]
      erw [loop.run]
      erw [execute_compare levels.1 lvPc lv23 lv9]
      simp only [bind_pure_comp,check_recorded_map]
      erw [execute_branch cmp cmpPc]
      simp only [bind_pure_comp,check_recorded_map]
      rw [counted]
      simp only [Execution.charge,←Nat.add_assoc,Nat.reduceAdd,Nat.zero_add,Nat.add_zero,List.append_assoc]
      try rfl
    by_cases yes : cmp.getReg .x31=0#64
    · rw [outcomeAccept yes]
      have bpc : branch.pc=BitVec.ofNat 64 (4096+4*459) := branch_fall cmp cmpPc yes
      dsimp only
      rw [show 875+fuel=36+4+74*11+15+1+(5+fuel) by omega,common]
      dsimp only
      erw [execute_latch branch bpc]
      simp only [bind_pure_comp,check_recorded_map,Execution.charge,List.append_assoc,←Nat.add_assoc]
      try rfl
    · rw [outcomeReject yes]
      dsimp only
      rw [show 870+fuel=36+4+74*11+15+1+fuel by omega,common]
  · intro rejected
    by_cases yes : cmp.getReg .x31=0#64
    · rw [outcomeAccept yes] at rejected; cases rejected
    · rw [outcomeReject yes]
      exact branch_taken cmp cmpPc yes
  · intro accepted
    by_cases yes : cmp.getReg .x31=0#64
    swap
    · rw [outcomeReject yes] at accepted; cases accepted
    rw [outcomeAccept yes]
    have bpc : branch.pc=BitVec.ofNat 64 (4096+4*459) := branch_fall cmp cmpPc yes
    have bKeep (r : Reg) (a : r≠.x6) (b : r≠.x7) (c : r≠.x12) (d : r≠.x21) (f : r≠.x28) (g : r≠.x29)
        (h : r≠.x30) (i : r≠.x31) (j : r≠.x10) (l : r≠.x11) (m : r≠.x13) : branch.getReg r=s.getReg r :=
      (branch_reg cmp r).trans ((cmpKeep r g h i).trans (lvKeep r a b c d f g h i j l m))
    have rem : branch.getReg .x18=BitVec.ofNat 64 (input.positions.card-ordinal) :=
      (bKeep .x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)).trans cursor.remaining
    have L := latch_post branch bpc (input.positions.card-ordinal) (by omega) (by omega) rem
    obtain ⟨lpc,l18,l8,l19,lKeep,_⟩ := L
    have keepAll (r : Reg) (a : r≠.x6) (b : r≠.x7) (c : r≠.x12) (d : r≠.x21) (f : r≠.x28) (g : r≠.x29)
        (h : r≠.x30) (i : r≠.x31) (j : r≠.x10) (l : r≠.x11) (m : r≠.x13) (n : r≠.x8) (o : r≠.x18) (p : r≠.x19) :
        (latchState branch).getReg r=s.getReg r :=
      (lKeep r n o p).trans (bKeep r a b c d f g h i j l m)
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [lpc]
      by_cases last : ordinal+1=input.positions.card
      · rw [if_pos (by omega),if_pos last]
      · rw [if_neg (by omega),if_neg last]
    · rw [l8,bKeep .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide),cursor.index]
      unfold wordAddress checkIndexWord
      rw [show (8 : Word)=BitVec.ofNat 64 8 from rfl,←BitVec.ofNat_add]
      congr 1
    · rw [l19,bKeep .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide),cursor.value]
      unfold wordAddress checkSourceWord
      rw [show (256 : Word)=BitVec.ofNat 64 256 from rfl,←BitVec.ofNat_add]
      congr 1
    · rw [lKeep .x21 (by decide) (by decide) (by decide),branch_reg,cmpKeep .x21 (by decide) (by decide) (by decide),
        loop.cursor]
      unfold wordAddress
      congr 1
      unfold P0 siblingWord checkProofByte; omega
    · rw [l18,show input.positions.card-ordinal-1=input.positions.card-(ordinal+1) by omega]
    all_goals first
      | exact (keepAll _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.tag
      | exact (keepAll _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.commitment
      | exact (keepAll _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.challengeLength
      | exact (keepAll _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.proofEnd
      | exact (keepAll _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.digest
      | exact (keepAll _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.pair
      | exact (keepAll _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.capRoots
      | exact (keepAll _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.marks
      | exact (keepAll _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.capCount
      | exact (keepAll _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.selector
      | exact (keepAll _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.nonceScratch
  · intro accepted
    by_cases yes : cmp.getReg .x31=0#64
    swap
    · rw [outcomeReject yes] at accepted; cases accepted
    rw [outcomeAccept yes]
    have bpc : branch.pc=BitVec.ofNat 64 (4096+4*459) := branch_fall cmp cmpPc yes
    have rem : branch.getReg .x18=BitVec.ofNat 64 (input.positions.card-ordinal) := by
      rw [branch_reg,cmpKeep .x18 (by decide) (by decide) (by decide)]
      exact (lvKeep .x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)).trans cursor.remaining
    have lmem := (latch_post branch bpc (input.positions.card-ordinal) (by omega) (by omega) rem).2.2.2.2.2
    apply record_input_frame_step input ordinal s _ framed
    intro w wb used
    obtain ⟨out1,out2⟩ := record_input_address_after input ordinal w used
    rw [viewEq _ _ lmem,viewEq _ _ (branch_mem cmp),viewEq _ _ cmpPost.2]
    exact backFrame w wb out1 out2
  · intro accepted
    by_cases yes : cmp.getReg .x31=0#64
    swap
    · rw [outcomeReject yes] at accepted; cases accepted
    rw [outcomeAccept yes]
    have equalRoot := (cmpPost.1.mp yes).trans commitmentWords
    have path := loop.path
    rw [startDigest,equalRoot] at path
    refine ⟨⟨checkerNonce (staged s),?_,?_,path.mono (fun _ h => List.mem_append_right _ h)⟩⟩
    · apply List.mem_append_left
      rw [show raw.2=_ from meaning.1]
      exact List.mem_cons_self
    · apply List.mem_append_left
      rw [show raw.2=_ from meaning.1]
      exact List.mem_cons_of_mem _ List.mem_cons_self
  · intro message salts canonical
    have equal : cmp.getReg .x31=0#64 :=
      cmpPost.1.mpr ((honestRoot message salts canonical).trans commitmentWords.symm)
    rw [outcomeAccept equal]

end TwoPermutationPrototype.Quad.Checker
