import CommitGolfCandidate.QuadCheckPentaLevel
import CommitGolfCandidate.QuadBindingPaths
import CommitGolfCandidate.TwoPermutationHonestLower

/-! The eleven-level penta loop: exact run, recorded D5 path, frame, and the
honest climb from the opened leaf to the root. -/
namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Quad (PentaPath pentaSlot)
open TwoPermutationPrototype.Checker (check_recorded_bind check_recorded_map aligned_digest_frame)
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

attribute [local irreducible] execute writeBits levelPrep checkEvaluation recordRows

/-- Workspace frame of one level: only the reply window and the workspace change. -/
def LevelFrame (before after : MachineState) : Prop :=
  ∀ w<2^33, (w<1536 ∨ 1561≤w) → (w<1600 ∨ 1625≤w) → memoryView after w=memoryView before w

theorem memory_view_congr (a b : MachineState) (same : a.mem=b.mem) (v : Nat) :
    memoryView a v=memoryView b v := by
  simp only [memoryView,MachineState.getMem,same]

structure LevelReplyFacts (s t : MachineState) (n p left : Nat) (answer : Block) : Prop where
  pc : t.pc=(if left=1 then BitVec.ofNat 64 (4096+4*443) else BitVec.ofNat 64 (4096+4*369))
  node : t.getReg .x6=BitVec.ofNat 64 (n/5)
  cursor : t.getReg .x21=wordAddress (p+16)
  counter : t.getReg .x29=BitVec.ofNat 64 (left-1)
  saved : ∀ r, r≠.x6 → r≠.x7 → r≠.x12 → r≠.x21 → r≠.x28 → r≠.x29 → r≠.x30 → r≠.x31 → t.getReg r=s.getReg r
  digest : readBuffer t 12288 32=answer.extractLsb' 0 256
  frame : LevelFrame s t

theorem level_reply_facts (s : MachineState) (n p left : Nat) (ready : LevelReady s n p left) (answer : Block) :
    LevelReplyFacts s (levelReply s answer) n p left answer := by
  have facts := level_prep_ready s n p left ready
  let t := levelPrep s
  let w := writeBits t (wordAddress 1536) answer
  have tpc : t.pc=BitVec.ofNat 64 (4096+4*440) := by rw [facts.pc,ready.pc]; rfl
  have wpc : w.pc=BitVec.ofNat 64 (4096+4*441) := by
    unfold w writeBits; change t.pc+4=_; rw [tpc]; rfl
  have wreg (r : Reg) : w.getReg r=t.getReg r := writeBits_register _ _ _ r
  have w29 : w.getReg .x29=BitVec.ofNat 64 left :=
    (wreg _).trans ((facts.saved .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans ready.counter)
  have latch := level_latch_post w wpc left ready.positive ready.small w29
  have lreg (r : Reg) (k : r≠.x29) : (levelReply s answer).getReg r=t.getReg r := (latch.2.2.1 r k).trans (wreg r)
  have lmem : (levelReply s answer).mem=w.mem := latch.2.2.2
  refine ⟨latch.1,(lreg .x6 (by decide)).trans facts.node,(lreg .x21 (by decide)).trans facts.cursor,latch.2.1,?_,?_,?_⟩
  · intro r a b c d e f g h
    exact (lreg r f).trans (facts.saved r a b c d e g h)
  · rw [read_buffer_memory_congr _ _ lmem]
    change readBuffer (writeBits t (BitVec.ofNat 64 12288) answer) (12288+0) 32=answer.extractLsb' (8*0) 256
    exact write_bits_digest t 12288 0 answer (by decide) (by decide)
  · intro v vb outsideReply outsideWork
    rw [memory_view_congr _ _ lmem v]
    change BitVec 1600 at answer
    change memoryView (writeBits t (wordAddress 1536) answer) v=_
    rw [permutation_write_memory _ 1536 v answer (by decide) vb,writeWindow,
      dite_eq_right (by omega : ¬(1536≤v ∧ v<1536+25))]
    have m := facts.memory v (by omega)
    unfold levelWord at m
    rw [if_neg (by omega),if_neg (by omega)] at m
    exact m

attribute [local irreducible] levelReply levelLatch

/-- Children of level `lvl` as read from the loop-start state. -/
def loopChild (s : MachineState) (i P0 lvl : Nat) (d : BitVec 256) : Fin 5 → BitVec 256 :=
  fun t => if t.val=i/5^lvl%5 then d
    else readBuffer s (8*(P0+16*lvl)+32*((t.val+4-i/5^lvl%5)%5)) 32

noncomputable def levelsRun (oracle : Oracle) : Nat → MachineState → MachineState × List PublicRow
  | 0, s => (s, [])
  | k+1, s =>
    let input := levelInput s
    let answer := oracle.permutation input
    let rest := levelsRun oracle k (levelReply s answer)
    (rest.1, PublicRow.permutation input answer :: rest.2)

structure LoopFacts (oracle : Oracle) (s : MachineState) (i P0 k left : Nat) : Prop where
  run : ∀ fuel,
    let tail := checkEvaluation oracle (recordRows (execute packedImage fuel (levelsRun oracle left s).1 false))
    checkEvaluation oracle (recordRows (execute packedImage (74*left+fuel) s false)) =
      ((tail.1.1.charge (99*left) left,(levelsRun oracle left s).2++tail.1.2),left+tail.2)
  pc : 0<left → (levelsRun oracle left s).1.pc=BitVec.ofNat 64 (4096+4*443)
  cursor : (levelsRun oracle left s).1.getReg .x21=wordAddress (P0+16*(k+left))
  saved : ∀ r, r≠.x6 → r≠.x7 → r≠.x12 → r≠.x21 → r≠.x28 → r≠.x29 → r≠.x30 → r≠.x31 →
    (levelsRun oracle left s).1.getReg r=s.getReg r
  frame : LevelFrame s (levelsRun oracle left s).1
  path : PentaPath (levelsRun oracle left s).2 i k left (readBuffer s 12288 32)
    (readBuffer (levelsRun oracle left s).1 12288 32)
  honest : ∀ node : Nat → Nat → BitVec 256,
    (∀ lvl, k≤lvl → lvl<k+left →
      (oracle.permutation (pentaInput (loopChild s i P0 lvl (node lvl (i/5^lvl))))).extractLsb' 0 256=
        node (lvl+1) (i/5^(lvl+1))) →
    readBuffer s 12288 32=node k (i/5^k) →
    readBuffer (levelsRun oracle left s).1 12288 32=node (k+left) (i/5^(k+left))

theorem charge_charge (r : Execution) (a b c d : Nat) :
    (r.charge a b).charge c d=r.charge (c+a) (d+b) := by
  simp only [Execution.charge,Nat.add_assoc]

private theorem frame_trans {a b c : MachineState} (first : LevelFrame a b) (second : LevelFrame b c) :
    LevelFrame a c := fun w wb x y => (second w wb x y).trans (first w wb x y)

private theorem proof_read_frame (before after : MachineState) (frame : LevelFrame before after) (word : Nat)
    (far : 1625≤word) (room : word+4≤2^33) :
    readBuffer after (8*word) 32=readBuffer before (8*word) 32 :=
  aligned_digest_frame before after word (fun offset _ => frame _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)))

theorem loop_facts (oracle : Oracle) (i P0 : Nat) (ib : i<2^64) (far : 1625≤P0) (room : P0+16*11≤2^33) :
    ∀ left k s, k+left=11 → (0<left → LevelReady s (i/5^k) (P0+16*k) left) →
      (left=0 → s.getReg .x21=wordAddress (P0+16*k)) → LoopFacts oracle s i P0 k left := by
  intro left
  induction left with
  | zero =>
    intro k s total _ cur
    refine ⟨?_,fun h => absurd h (by decide),?_,fun _ _ _ _ _ _ _ _ _ => rfl,fun _ _ _ _ => rfl,.done k _,?_⟩
    · intro fuel
      simp [levelsRun,Execution.charge]
    · simpa [levelsRun] using cur rfl
    · intro node _ start
      simpa [levelsRun] using start
  | succ left ih =>
    intro k s total readyOf _
    have ready := readyOf (by omega)
    let answer := oracle.permutation (levelInput s)
    have R0 := level_reply_facts s (i/5^k) (P0+16*k) (left+1) ready answer
    obtain ⟨t,tdef⟩ : ∃ t, levelReply s answer=t := ⟨_,rfl⟩
    have R : LevelReplyFacts s t (i/5^k) (P0+16*k) (left+1) answer := tdef ▸ R0
    have nextNode : i/5^k/5=i/5^(k+1) := by rw [Nat.div_div_eq_div_mul,pow_succ]
    have tail := ih (k+1) t (by omega)
      (by
        intro positive
        have keep (r : Reg) (a : r≠.x6) (b : r≠.x7) (c : r≠.x12) (d : r≠.x21) (e : r≠.x28) (f : r≠.x29)
            (g : r≠.x30) (h : r≠.x31) : t.getReg r=s.getReg r := R.saved r a b c d e f g h
        refine ⟨?_,?_,lt_of_le_of_lt (Nat.div_le_self _ _) ib,?_,?_,?_,by omega,by omega,?_,?_,?_,?_,positive,by omega⟩
        · exact R.pc.trans (if_neg (by omega))
        · rw [R.node,nextNode]
        · exact (keep .x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide)).trans ready.base
        · exact (keep .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide)).trans ready.digest
        · rw [R.cursor,show P0+16*k+16=P0+16*(k+1) by omega]
        · exact (keep .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide)).trans ready.selector
        · exact (keep .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide)).trans ready.size
        · exact (keep .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide)).trans ready.primitive
        · rw [R.counter,Nat.add_sub_cancel])
      (by intro zero; rw [R.cursor,show P0+16*k+16=P0+16*(k+1) by omega])
    have facts := level_prep_ready s _ _ _ ready
    have input : levelInput s=pentaInput (prepChild s (i/5^k%5) (P0+16*k)) :=
      level_prep_input s _ _ facts ready.room
    have unfoldRun : levelsRun oracle (left+1) s=
        ((levelsRun oracle left t).1,PublicRow.permutation (levelInput s) answer::(levelsRun oracle left t).2) := by
      rw [←tdef]; rfl
    -- children read from the loop-start state
    have childNow (d : BitVec 256) (dig : readBuffer s 12288 32=d) :
        prepChild s (i/5^k%5) (P0+16*k)=loopChild s i P0 k d := by
      funext c
      unfold prepChild loopChild
      split
      · exact dig
      · rfl
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · intro fuel
      rw [unfoldRun]
      dsimp only
      rw [show 74*(left+1)+fuel=74+(74*left+fuel) by omega,execute_level s _ _ _ ready,check_recorded_bind,
        level_call_rows]
      simp only [bind_pure_comp,check_recorded_map]
      rw [tdef,tail.run]
      simp only [charge_charge,List.cons_append,List.nil_append]
      refine Prod.ext (Prod.ext ?_ rfl) ?_
      · rw [show 99+99*left=99*(left+1) by omega,show 1+left=left+1 by omega]
      · simp only; omega
    · intro _
      rw [unfoldRun]
      by_cases more : 0<left
      · exact tail.pc more
      · have zero : left=0 := by omega
        subst zero
        change t.pc=_
        rw [R.pc,if_pos rfl]
    · rw [unfoldRun]
      dsimp only
      rw [tail.cursor,show P0+16*(k+1+left)=P0+16*(k+(left+1)) by omega]
    · intro r a b c d e f g h
      rw [unfoldRun]
      exact (tail.saved r a b c d e f g h).trans (R.saved r a b c d e f g h)
    · rw [unfoldRun]
      exact frame_trans R.frame tail.frame
    · rw [unfoldRun]
      dsimp only
      refine .step k left _ _ (prepChild s (i/5^k%5) (P0+16*k)) answer ?_ ?_ ?_
      · unfold prepChild pentaSlot
        simp only [ite_true]
      · rw [←input]
        exact List.mem_cons_self
      · rw [←R.digest]
        exact tail.path.mono (fun _ hit => List.mem_cons_of_mem _ hit)
    · intro node climb start
      rw [unfoldRun]
      dsimp only
      have nowClimb := climb k le_rfl (by omega)
      rw [←childNow _ start,←input] at nowClimb
      have nextStart : readBuffer t 12288 32=node (k+1) (i/5^(k+1)) := R.digest.trans nowClimb
      have later := tail.honest node (by
        intro lvl lo hi
        have c := climb lvl (by omega) (by omega)
        have same : loopChild t i P0 lvl (node lvl (i/5^lvl))=loopChild s i P0 lvl (node lvl (i/5^lvl)) := by
          funext c'
          unfold loopChild
          split
          · rfl
          · rw [show 8*(P0+16*lvl)+32*((c'.val+4-i/5^lvl%5)%5)=8*(P0+16*lvl+4*((c'.val+4-i/5^lvl%5)%5)) by omega]
            exact proof_read_frame s t R.frame _ (by omega) (by omega)
        rw [same]
        exact c) nextStart
      rw [later,show k+1+left=k+(left+1) by omega]

end TwoPermutationPrototype.Quad.Checker
