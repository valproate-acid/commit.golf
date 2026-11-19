import CommitGolfCandidate.QuadCommitPentaLevel
import CommitGolfCandidate.TwoPermutationHeapInvariant

/-! Memory meaning of the level passes. `Tree s nodes salts L` says that the salts, the zero
prefixes of all groups of levels `0 … 10` and every slot (in range or ragged) of levels below `L`
are in place. A level pass for level `k+1` writes only its own slots, so it keeps the tree below
and adds level `k+1`. -/
namespace TwoPermutationPrototype.Quad.Commit.Penta
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open CommitGolfCandidate (checkEvaluation check_evaluation_bind check_evaluation_pure read_buffer_memory_congr
  write_bits_digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] writeBits checkEvaluation

/-! ### The node input -/

theorem penta_input_zero_word (c : Fin 5 → BitVec 256) (k : Fin 5) :
    (pentaInput c).extractLsb' (64*k.val) 64=0 := by
  change ((((((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) ++ (0#320))).extractLsb' (64*k.val) 64=0
  rw [BitVec.extractLsb'_append_eq_of_add_le (by have := k.isLt;omega : 64*k.val+64≤320)]
  simp

theorem penta_input_digest_word (c : Fin 5 → BitVec 256) (slot : Fin 5) (k : Fin 4) :
    (pentaInput c).extractLsb' (64*(5+4*slot.val+k.val)) 64 = (c slot).extractLsb' (64*k.val) 64 := by
  change ((((((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) ++ (0#320))).extractLsb' (64*(5+4*slot.val+k.val)) 64 =
    (c slot).extractLsb' (64*k.val) 64
  have hk := k.isLt
  fin_cases slot <;> apply BitVec.eq_of_getLsbD_eq <;> intro bit hbit
  all_goals simp only [BitVec.getLsbD_extractLsb',BitVec.getLsbD_append]
  all_goals simp only [show decide (bit<64)=true by exact decide_eq_true hbit,Bool.true_and]
  all_goals split_ifs <;> first | omega | (congr 1 <;> omega)

theorem penta_buffer_eq (s : MachineState) (k g : Nat) (c : Fin 5 → BitVec 256)
    (zeros : ∀ t : Fin 5, memoryView s (pentaGroupWord k g+t.val)=0)
    (children : ∀ (slot : Fin 5) (w : Fin 4), memoryView s (pentaSlotWord k (5*g+slot.val)+w.val)=
      (c slot).extractLsb' (64*w.val) 64) :
    readBuffer s (8*pentaGroupWord k g) 200=pentaInput c := by
  apply aligned_buffer_eq s _ 200 (by decide)
  intro w hw
  by_cases low : w<5
  · rw [zeros ⟨w,low⟩]
    exact (penta_input_zero_word c ⟨w,low⟩).symm
  · let slot : Fin 5 := ⟨(w-5)/4,by omega⟩
    let word : Fin 4 := ⟨(w-5)%4,Nat.mod_lt _ (by decide)⟩
    have offset : 5+4*slot.val+word.val=w := by dsimp [slot,word];omega
    have address : pentaGroupWord k g+w=pentaSlotWord k (5*g+slot.val)+word.val := by
      unfold pentaSlotWord pentaGroupWord
      have hslot := slot.isLt
      omega
    rw [address,children]
    have slice := penta_input_digest_word c slot word
    rw [offset] at slice
    exact slice.symm

theorem buffer_digest_words (s : MachineState) (w : Nat) (d : BitVec 256)
    (read : readBuffer s (8*w) 32=d) (k : Fin 4) :
    memoryView s (w+k.val)=d.extractLsb' (64*k.val) 64 := by
  rw [←RV64.read_word]
  have slice := CommitGolfCandidate.read_buffer_slice s (8*w) 32 (8*k.val) 8 (by have := k.isLt;omega)
  rw [read] at slice
  rw [show 8*(w+k.val)=8*w+8*k.val by omega,←slice,←Nat.mul_assoc]

/-! ### The invariant -/

structure Tree (s : MachineState) (nodes : Nat → Nat → BitVec 256) (salts : CompleteSaltTape) (L : Nat) : Prop where
  nonce : ∀ (i : Index) (t : Fin 2), memoryView s (saltWord i.val+t.val)=(salts i).extractLsb' (64*t.val) 64
  zeros : ∀ k g, k≤10 → g<pentaCount (k+1) → ∀ t : Fin 5, memoryView s (pentaGroupWord k g+t.val)=0
  node : ∀ k j, k<L → j<5*pentaCount (k+1) → ∀ t : Fin 4,
    memoryView s (pentaSlotWord k j+t.val)=(nodes k j).extractLsb' (64*t.val) 64

structure Partial (s : MachineState) (nodes : Nat → Nat → BitVec 256) (salts : CompleteSaltTape) (k j : Nat) : Prop
    extends Tree s nodes salts (k+1) where
  done : ∀ i, i<j → ∀ t : Fin 4,
    memoryView s (pentaSlotWord (k+1) i+t.val)=(nodes (k+1) i).extractLsb' (64*t.val) 64

theorem count_step (k : Nat) : pentaCount (k+1)=(pentaCount k+4)/5 := rfl

theorem tree_same_mem (s u : MachineState) (nodes : Nat → Nat → BitVec 256) (salts : CompleteSaltTape) (L : Nat)
    (r : Tree s nodes salts L) (h : u.mem=s.mem) : Tree u nodes salts L := by
  have view : memoryView u=memoryView s := by funext w;change u.mem _=s.mem _;rw [h]
  exact ⟨by rw [view];exact r.nonce,by rw [view];exact r.zeros,by rw [view];exact r.node⟩

theorem partial_same_mem (s u : MachineState) (nodes : Nat → Nat → BitVec 256) (salts : CompleteSaltTape) (k j : Nat)
    (r : Partial s nodes salts k j) (h : u.mem=s.mem) : Partial u nodes salts k j := by
  have view : memoryView u=memoryView s := by funext w;change u.mem _=s.mem _;rw [h]
  exact ⟨tree_same_mem s u nodes salts (k+1) r.toTree h,by rw [view];exact r.done⟩

private theorem count_table : ∀ l : Fin 11, pentaCount (l.val+1)<2^24 := by decide

theorem count_lt (l : Nat) (hl : l≤10) : pentaCount (l+1)<2^24 := count_table ⟨l,by omega⟩

theorem salt_top (i : Index) : saltWord i.val+2≤2^33 := by
  have : i.val<16777216 := i.isLt
  unfold saltWord
  omega

theorem group_top (l g : Nat) (hl : l≤10) (hg : g<pentaCount (l+1)) : pentaGroupWord l g+46≤2^33 := by
  have := count_lt l hl
  exact group_room l g (by omega)

/-- A write that only touches level-`k+1` words from slot `j` on keeps the partial level. -/
theorem partial_frame (s u : MachineState) (nodes : Nat → Nat → BitVec 256) (salts : CompleteSaltTape)
    (k j : Nat) (hk : k≤9) (inside : j<pentaCount (k+1)) (r : Partial s nodes salts k j)
    (frame : ∀ w, w<pentaSlotWord (k+1) j ∨ pentaSlotWord (k+1) j+25≤w → w<2^33 →
      memoryView u w=memoryView s w) :
    Partial u nodes salts k j := by
  have groupInside : j/5<pentaCount (k+2) := by rw [count_step (k+1)];omega
  have writeEnd := slot_write_end (k+1) j
  have writeStart := slot_after_zero_prefix (k+1) j
  have e : pentaGroupWord (k+1) (j/5+1)=pentaGroupWord (k+1) (j/5)+46 := by unfold pentaGroupWord;omega
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · intro i t
    have below := group_below_salts (k+1) (j/5) (by omega) groupInside i.val
    have top := salt_top i
    have := t.isLt
    rw [frame _ (Or.inr (by omega)) (by omega)]
    exact r.nonce i t
  · intro l g hl hg t
    have room := group_top l g hl hg
    have := t.isLt
    have away : pentaGroupWord l g+t.val<pentaSlotWord (k+1) j ∨
        pentaSlotWord (k+1) j+25≤pentaGroupWord l g+t.val := by
      by_cases same : l=k+1
      · subst same
        rcases slot_zero_prefix_separate (k+1) j g with h|h
        · right;omega
        · left;omega
      · by_cases lower : l<k+1
        · have := level_order l (k+1) g lower (by omega) hg (j/5)
          left;omega
        · have := level_order (k+1) l (j/5) (by omega) (by omega) groupInside g
          right;omega
    rw [frame _ away (by omega)]
    exact r.zeros l g hl hg t
  · intro l i hl hi t
    have := t.isLt
    have groupI : i/5<pentaCount (l+1) := by omega
    have order := level_order l (k+1) (i/5) (by omega) (by omega) groupI (j/5)
    have slotEnd := slot_write_end l i
    have room := group_top l (i/5) (by omega) groupI
    have e : pentaGroupWord l (i/5+1)=pentaGroupWord l (i/5)+46 := by unfold pentaGroupWord;omega
    rw [frame _ (Or.inl (by omega)) (by omega)]
    exact r.node l i hl hi t
  · intro i hi t
    have := t.isLt
    have sep := slot_separate (k+1) i j hi
    have room := slot_room (k+1) j (by have := count_lt k (by omega);omega)
    rw [frame _ (Or.inl (by omega)) (by omega)]
    exact r.done i hi t

/-- Node values: in-range nodes are the node function of their group, the others are zero. -/
structure Values (oracle : Oracle) (nodes : Nat → Nat → BitVec 256) : Prop where
  value : ∀ k j, j<pentaCount (k+1) →
    nodes (k+1) j=pentaFunction oracle.permutation (fun t => nodes k (5*j+t.val))
  ragged : ∀ k j, pentaCount k≤ j → nodes k j=0

theorem node_input (s : MachineState) (nodes : Nat → Nat → BitVec 256) (salts : CompleteSaltTape) (k j : Nat)
    (hk : k≤10) (inside : j<pentaCount (k+1)) (r : Tree s nodes salts (k+1)) :
    readBuffer s (8*pentaGroupWord k j) 200=pentaInput (fun t => nodes k (5*j+t.val)) := by
  apply penta_buffer_eq s k j _ (r.zeros k j (by omega) inside)
  intro slot w
  exact r.node k (5*j+slot.val) (by omega) (by have := slot.isLt;omega) w

theorem content_step (oracle : Oracle) (s : MachineState) (nodes : Nat → Nat → BitVec 256) (salts : CompleteSaltTape)
    (v : Values oracle nodes) (k j : Nat) (hk : k≤9) (inside : j<pentaCount (k+1))
    (r : Partial s nodes salts k j) :
    Partial (after k s j (oracle.permutation (packBuffer (window (memoryView s) (pentaGroupWord k j)))))
      nodes salts k (j+1) := by
  let reply := oracle.permutation (packBuffer (window (memoryView s) (pentaGroupWord k j)))
  have countBound : pentaCount (k+1)<2^24 := by
    have table : ∀ l : Fin 10, pentaCount (l.val+1)<2^24 := by decide
    exact table ⟨k,by omega⟩
  have mem : (after k s j reply).mem=(writeBits s (wordAddress (pentaSlotWord (k+1) j)) reply).mem := by unfold after;rfl
  have view : ∀ w, w<2^33 → memoryView (after k s j reply) w =
      writeWindow (memoryView s) (pentaSlotWord (k+1) j) (replyWords reply) w := by
    intro w hw
    rw [show memoryView (after k s j reply) w=memoryView (writeBits s (wordAddress (pentaSlotWord (k+1) j)) reply) w by
      change (after k s j reply).mem _=_;rw [mem];rfl]
    exact permutation_write_memory s _ w reply (slot_room (k+1) j (by omega)) hw
  have kept := partial_frame s (after k s j reply) nodes salts k j hk inside r (by
    intro w away hw
    rw [view w hw]
    unfold writeWindow
    rw [dif_neg (by omega)])
  refine ⟨kept.toTree,?_⟩
  intro i hi t
  by_cases same : i=j
  · subst i
    have written := write_bits_digest (bits := 1600) s (8*pentaSlotWord (k+1) j) 0 reply (by decide) (by decide)
    simp only [Nat.mul_zero,Nat.add_zero] at written
    have buffer : readBuffer (after k s j reply) (8*pentaSlotWord (k+1) j) 32=nodes (k+1) j := by
      rw [read_buffer_memory_congr _ _ mem]
      apply written.trans
      rw [v.value k j inside]
      unfold reply pentaFunction
      rw [←read_permutation_window,node_input s nodes salts k j (by omega) inside r.toTree]
      rfl
    exact buffer_digest_words _ _ _ buffer t
  · exact kept.done i (by omega) t

theorem sequence_content (oracle : Oracle) (s : MachineState) (nodes : Nat → Nat → BitVec 256) (salts : CompleteSaltTape)
    (v : Values oracle nodes) (k count j : Nat) (hk : k≤9) (limit : j+count≤pentaCount (k+1))
    (r : Partial s nodes salts k j) :
    Partial (checkEvaluation oracle (trace k count j s)).1 nodes salts k (j+count) := by
  induction count generalizing s j with
  | zero => simpa only [trace,check_evaluation_pure,Nat.add_zero] using r
  | succ c ih =>
    rw [trace,check_evaluation_bind]
    have evaluated : checkEvaluation oracle (liftM
        (World.query (.inr (.inr (.inl (packBuffer (window (memoryView s) (pentaGroupWord k j))))))) :
        OracleComp World (BitVec 1600)) =
      (oracle.permutation (packBuffer (window (memoryView s) (pentaGroupWord k j))),1) :=
      CommitGolfCandidate.check_evaluation_public oracle _
    rw [evaluated]
    have step := content_step oracle s nodes salts v k j hk (by omega) r
    have tail := ih _ (j+1) (by omega) step
    rwa [show j+1+c=j+(c+1) by omega] at tail

theorem loops_content (oracle : Oracle) (s : MachineState) (nodes : Nat → Nat → BitVec 256) (salts : CompleteSaltTape)
    (v : Values oracle nodes) (k B S cnt j : Nat) (hk : k≤9) (limit : j+S*cnt≤pentaCount (k+1))
    (r : Partial s nodes salts k j) :
    Partial (checkEvaluation oracle (loops k B S cnt j s)).1 nodes salts k (j+S*cnt) := by
  induction cnt generalizing s j with
  | zero => simpa only [loops,check_evaluation_pure,Nat.mul_zero,Nat.add_zero] using r
  | succ c ih =>
    rw [loops,check_evaluation_bind]
    have body := sequence_content oracle s nodes salts v k S j hk (by rw [Nat.mul_succ] at limit;omega) r
    let mid := (checkEvaluation oracle (trace k S j s)).1
    have next := partial_same_mem mid (mid.setPC (nextPC B S c)) nodes salts k (j+S) body rfl
    have tail := ih _ (j+S) (by rw [Nat.mul_succ] at limit;omega) next
    rwa [show j+S+S*c=j+S*(c+1) by rw [Nat.mul_succ];omega] at tail

/-- Clearing the ragged slots completes level `k+1`. -/
theorem zero_content (oracle : Oracle) (s : MachineState) (nodes : Nat → Nat → BitVec 256) (salts : CompleteSaltTape)
    (v : Values oracle nodes) (k z : Nat) (hk : k≤9) (r : Partial s nodes salts k (pentaCount (k+1)))
    (x12 : s.getReg .x12=wordAddress (pentaSlotWord (k+1) (pentaCount (k+1))))
    (ragged : z=4*(5*pentaCount (k+2)-pentaCount (k+1))) (small : 8*z<2048) :
    Tree (zeroed s 0 z z) nodes salts (k+2) := by
  have countBound := count_lt k (by omega)
  have upper : pentaCount (k+2)=(pentaCount (k+1)+4)/5 := count_step (k+1)
  have same2 : pentaCount (k+1+1)=pentaCount (k+2) := rfl
  by_cases none : z=0
  · subst none
    have full : 5*pentaCount (k+2)=pentaCount (k+1) := by omega
    refine ⟨r.nonce,r.zeros,?_⟩
    intro l i hl hi t
    by_cases same : l=k+1
    · subst same;exact r.done i (by omega) t
    · exact r.node l i (by omega) hi t
  have notFull : pentaCount (k+1)%5≠0 := by omega
  let c := pentaCount (k+1)
  let b := pentaCount (k+2)
  have lastGroup : b=c/5+1 := by omega
  let W := pentaSlotWord (k+1) c
  have slotLow : W<2^31 := by
    have := base_word_le (k+1)
    unfold W pentaSlotWord pentaGroupWord
    omega
  have view : ∀ w, w<2^33 → memoryView (zeroed s 0 z z) w = if W≤w ∧ w<W+z then 0 else memoryView s w := by
    intro w hw
    have := zeroed_memory s 0 z z W le_rfl x12 (by decide) (by omega) (by omega) w hw
    simpa using this
  have outside : ∀ w, w<W ∨ W+z≤w → w<2^33 → memoryView (zeroed s 0 z z) w=memoryView s w := by
    intro w away hw
    rw [view w hw,if_neg (by omega)]
  have startW : W=pentaGroupWord (k+1) (c/5)+5+4*(c%5) := rfl
  have endW : W+z=pentaGroupWord (k+1) (c/5)+25 := by
    rw [startW,ragged];omega
  have lastBound : c/5<pentaCount (k+2) := by omega
  refine ⟨?_,?_,?_⟩
  · intro i t
    have below := group_below_salts (k+1) (c/5) (by omega) lastBound i.val
    have top := salt_top i
    have := t.isLt
    rw [outside _ (Or.inr (by omega)) (by omega)]
    exact r.nonce i t
  · intro l g hl hg t
    have := t.isLt
    have room := group_top l g hl hg
    have away : pentaGroupWord l g+t.val<W ∨ W+z≤pentaGroupWord l g+t.val := by
      by_cases same : l=k+1
      · subst same
        left
        have : g≤c/5 := by omega
        rw [startW]
        unfold pentaGroupWord
        omega
      · by_cases lower : l<k+1
        · have := level_order l (k+1) g lower (by omega) hg (c/5)
          left;omega
        · have := level_order (k+1) l (c/5) (by omega) (by omega) lastBound g
          right;omega
    rw [outside _ away (by omega)]
    exact r.zeros l g hl hg t
  · intro l i hl hi t
    have := t.isLt
    by_cases same : l=k+1
    · subst same
      by_cases real : i<c
      · have sep := slot_separate (k+1) i c real
        rw [outside _ (Or.inl (by omega)) (by omega)]
        exact r.done i real t
      · have inRegion : W≤pentaSlotWord (k+1) i+t.val ∧ pentaSlotWord (k+1) i+t.val<W+z := by
          have same5 : i/5=c/5 := by omega
          rw [endW,startW]
          unfold pentaSlotWord
          rw [same5]
          omega
        rw [view _ (by omega),if_pos inRegion,v.ragged (k+1) i (by omega)]
        simp
    · have lower : l<k+1 := by omega
      have groupI : i/5<pentaCount (l+1) := by omega
      have order := level_order l (k+1) (i/5) lower (by omega) groupI (c/5)
      have slotEnd := slot_write_end l i
      have room := group_top l (i/5) (by omega) groupI
      have e : pentaGroupWord l (i/5+1)=pentaGroupWord l (i/5)+46 := by unfold pentaGroupWord;omega
      rw [outside _ (Or.inl (by omega)) (by omega)]
      exact r.node l i (by omega) hi t

end TwoPermutationPrototype.Quad.Commit.Penta
