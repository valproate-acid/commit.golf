import CommitGolfCandidate.QuadCommitInput
import CommitGolfCandidate.QuadCommitFetch

/-! Generic execution of a penta level pass: node `j` reads level-`k` group `j` and writes its
200-byte reply at the level-`k+1` slot of `j`; the destination advances 32 bytes, or 240 after
slot 4. Straight-line node segments, a looped segment with a `beq x12, x21` latch, and the
`sd x0` stores that clear ragged slots. -/
namespace TwoPermutationPrototype.Quad.Commit.Penta
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] image leafCode levelsCode execute writeBits

def stride (t : Nat) : BitVec 12 := if t = 4 then 240 else 32
def nodeInstr (t part : Nat) : Instr :=
  if part=0 then .ECALL else if part=1 then .ADDI .x10 .x10 368 else .ADDI .x12 .x12 (stride t)

theorem node_decoded : ∀ t : Fin 5, ∀ part : Fin 3,
    ((nodeWords t.val)[part.val]?).bind decodeInstruction = some (.base (nodeInstr t.val part.val)) := by
  decide +kernel

theorem node_code_length (n : Nat) : (nodeCode n).length = 3*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold nodeCode at *
    rw [List.range_succ,List.flatMap_append,List.length_append,ih]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,nodeWords,List.length_cons,List.length_nil]
    omega

theorem node_code_at (n p part : Nat) (hp : p<n) (hpart : part<3) :
    (nodeCode n)[3*p+part]? = (nodeWords (p%5))[part]? := by
  induction n with
  | zero => omega
  | succ n ih =>
    unfold nodeCode at *
    rw [List.range_succ,List.flatMap_append]
    by_cases last : p=n
    · subst p
      rw [List.getElem?_append_right (by have := node_code_length n;unfold nodeCode at this;omega)]
      have := node_code_length n
      unfold nodeCode at this
      rw [this,show 3*n+part-3*n=part by omega]
      try simp
    · rw [List.getElem?_append_left (by have := node_code_length n;unfold nodeCode at this;omega)]
      exact ih (by omega)

/-- `n` nodes of code at word index `B` of the image. -/
def NodeSegment (B n : Nat) : Prop :=
  ∀ p part, p<n → part<3 →
    (image.code[B+3*p+part]?).bind decodeInstruction = some (.base (nodeInstr (p%5) part))

theorem node_segment (head tail : List (BitVec 32)) (n : Nat)
    (code : image.code=head++nodeCode n++tail) : NodeSegment head.length n := by
  intro p part hp hpart
  have at' := code_segment_at head (nodeCode n) tail code (3*p+part) (by rw [node_code_length];omega)
  rw [show head.length+3*p+part=head.length+(3*p+part) by omega,at',node_code_at n p part hp hpart]
  exact node_decoded ⟨p%5,Nat.mod_lt _ (by decide)⟩ ⟨part,hpart⟩

def nodePC (B p part : Nat) : Word := BitVec.ofNat 64 (4096+4*(B+3*p+part))

theorem fetch_node {B n : Nat} (seg : NodeSegment B n) (room : B+3*n<2^30) (p part : Nat)
    (hp : p<n) (hpart : part<3) (s : MachineState) (pc : s.pc=nodePC B p part) :
    fetch image s=some (.base (nodeInstr (p%5) part)) :=
  fetch_code_index s (B+3*p+part) (by omega) pc _ (seg p part hp hpart)

/-! ### Registers and one node -/

structure Regs (k : Nat) (s : MachineState) (j : Nat) : Prop where
  source : s.getReg .x10=wordAddress (pentaGroupWord k j)
  target : s.getReg .x12=wordAddress (pentaSlotWord (k+1) j)
  selector : s.getReg .x5=0
  size : s.getReg .x11=200
  primitive : s.getReg .x13=1

theorem regs_setPC (k : Nat) (s : MachineState) (j : Nat) (pc : Word) (r : Regs k s j) : Regs k (s.setPC pc) j :=
  ⟨r.source,r.target,r.selector,r.size,r.primitive⟩

def after (k : Nat) (s : MachineState) (j : Nat) (reply : BitVec 1600) :=
  execInstrBr (execInstrBr (writeBits s (wordAddress (pentaSlotWord (k+1) j)) reply)
    (.ADDI .x10 .x10 368)) (.ADDI .x12 .x12 (stride (j%5)))

def trace (k : Nat) : Nat → Nat → MachineState → OracleComp World MachineState
  | 0,_,s => pure s
  | n+1,j,s => do
    let reply ← (liftM (World.query (.inr (.inr (.inl (packBuffer (window (memoryView s) (pentaGroupWord k j))))))) : OracleComp World (BitVec 1600))
    trace k n (j+1) (after k s j reply)

theorem after_pc (k : Nat) (s : MachineState) (j : Nat) (reply : BitVec 1600) :
    (after k s j reply).pc=s.pc+12 := by
  change (writeBits s _ reply).pc+4+4=_
  rw [written_pc,BitVec.add_assoc,BitVec.add_assoc]
  rfl

theorem after_reg (k : Nat) (s : MachineState) (j : Nat) (reply : BitVec 1600) (reg : Reg)
    (source : .x10≠reg) (target : .x12≠reg) :
    (after k s j reply).getReg reg=s.getReg reg := by
  simp only [after,execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ source,MachineState.getReg_setReg_ne _ _ _ _ target,
    CommitGolfCandidate.writeBits_register]

theorem stride_advance (k j : Nat) :
    wordAddress (pentaSlotWord (k+1) j)+signExtend12 (stride (j%5))=wordAddress (pentaSlotWord (k+1) (j+1)) := by
  have adv := slot_advance (k+1) j
  by_cases last : j%5=4
  · rw [stride,if_pos last,show signExtend12 (240 : BitVec 12)=BitVec.ofNat 64 240 by rfl,
      wordAddress,←BitVec.ofNat_add]
    rw [if_pos last] at adv
    congr 1
    omega
  · rw [stride,if_neg last,show signExtend12 (32 : BitVec 12)=BitVec.ofNat 64 32 by rfl,
      wordAddress,←BitVec.ofNat_add]
    rw [if_neg last] at adv
    congr 1
    omega

theorem after_regs (k : Nat) (s : MachineState) (j : Nat) (reply : BitVec 1600) (r : Regs k s j) :
    Regs k (after k s j reply) (j+1) := by
  refine ⟨?_,?_,(after_reg k s j reply .x5 (by decide) (by decide)).trans r.selector,
    (after_reg k s j reply .x11 (by decide) (by decide)).trans r.size,
    (after_reg k s j reply .x13 (by decide) (by decide)).trans r.primitive⟩
  · change (writeBits s _ reply).getReg .x10+signExtend12 368=_
    rw [CommitGolfCandidate.writeBits_register,r.source]
    change wordAddress (pentaGroupWord k j)+BitVec.ofNat 64 368=_
    rw [wordAddress,←BitVec.ofNat_add]
    congr 1 <;> (try unfold pentaGroupWord) <;> omega
  · change (writeBits s _ reply).getReg .x12+signExtend12 (stride (j%5))=_
    rw [CommitGolfCandidate.writeBits_register,r.target]
    exact stride_advance k j

theorem base_word_le (k : Nat) : pentaBaseWord k ≤ 192947195 := by
  unfold pentaBaseWord
  split <;> omega

theorem group_room (k j : Nat) (bound : j<2^24) : pentaGroupWord k j+46 ≤ 2^33 := by
  have := base_word_le k
  unfold pentaGroupWord
  omega

theorem slot_room (k j : Nat) (bound : j<2^24) : pentaSlotWord k j+25 ≤ 2^33 := by
  have := base_word_le k
  unfold pentaSlotWord pentaGroupWord
  omega

private theorem one_run {B n : Nat} (seg : NodeSegment B n) (room : B+3*n<2^30)
    (k : Nat) (s : MachineState) (j p fuel : Nat) (bound : j<2^24) (hp : p<n)
    (phase : p%5=j%5) (r : Regs k s j) (pc : s.pc=nodePC B p 0) :
    execute image (3+fuel) s true =
      (do let reply ← (liftM (World.query (.inr (.inr (.inl (packBuffer (window (memoryView s) (pentaGroupWord k j))))))) : OracleComp World (BitVec 1600))
          let out ← execute image fuel (after k s j reply) true
          return out.charge 10 1) := by
  have fetched := fetch_node seg room p 0 hp (by decide) s pc
  rw [show 3+fuel=(fuel+2)+1 by omega,
    execute_permutation_call image (fuel+2) s true (pentaGroupWord k j) (pentaSlotWord (k+1) j)
      (by have := group_room k j bound;omega) (slot_room (k+1) j bound) r.source r.target r.selector r.size r.primitive
      (by simpa [nodeInstr] using fetched)]
  apply bind_congr_of_forall_mem_support
  intro reply _
  let written := writeBits s (wordAddress (pentaSlotWord (k+1) j)) reply
  let moved := execInstrBr written (.ADDI .x10 .x10 368)
  have writtenPC : written.pc=nodePC B p 1 := by
    dsimp only [written]
    rw [written_pc,pc]
    unfold nodePC
    change BitVec.ofNat 64 _+BitVec.ofNat 64 4=_
    rw [←BitVec.ofNat_add];congr 1 <;> omega
  have movedPC : moved.pc=nodePC B p 2 := by
    change written.pc+BitVec.ofNat 64 4=_
    rw [writtenPC];unfold nodePC;rw [←BitVec.ofNat_add];congr 1 <;> omega
  have f1 := fetch_node seg room p 1 hp (by decide) written writtenPC
  have f2 := fetch_node seg room p 2 hp (by decide) moved movedPC
  simp only [nodeInstr,phase] at f1 f2
  rw [CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ f1
    (show ordinaryStep written (.base (.ADDI .x10 .x10 368))=some moved from rfl),
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ f2
    (show ordinaryStep moved (.base (.ADDI .x12 .x12 (stride (j%5))))=some (after k s j reply) from rfl)]
  simp [instructionCycles,Execution.charge,←Nat.add_assoc]

private theorem next_pc (B p : Nat) (s : MachineState) (pc : s.pc=nodePC B p 0) :
    s.pc+12=nodePC B (p+1) 0 := by
  rw [pc];unfold nodePC
  change BitVec.ofNat 64 _+BitVec.ofNat 64 12=_
  rw [←BitVec.ofNat_add];congr 1 <;> omega

theorem sequence_run {B n : Nat} (seg : NodeSegment B n) (room : B+3*n<2^30)
    (k : Nat) (s : MachineState) (count j p fuel : Nat) (bound : j+count≤2^24)
    (inside : p+count≤n) (phase : p%5=j%5) (r : Regs k s j) (pc : s.pc=nodePC B p 0) :
    execute image (3*count+fuel) s true =
      (do let mid ← trace k count j s
          let out ← execute image fuel mid true
          return out.charge (10*count) count) := by
  induction count generalizing s j p with
  | zero => simp [trace,Execution.charge]
  | succ c ih =>
    rw [show 3*(c+1)+fuel=3+(3*c+fuel) by omega,
      one_run seg room k s j p _ (by omega) (by omega) phase r pc]
    simp only [trace,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro reply _
    have nextPC : (after k s j reply).pc=nodePC B (p+1) 0 := by
      rw [after_pc];exact next_pc B p s pc
    rw [ih _ (j+1) (p+1) (by omega) (by omega) (by omega) (after_regs k s j reply r) nextPC]
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem sequence_post (B : Nat) (k : Nat) (s : MachineState) (count j p : Nat) (r : Regs k s j)
    (pc : s.pc=nodePC B p 0) {out : MachineState} (hit : out ∈ support (trace k count j s)) :
    Regs k out (j+count) ∧ out.pc=nodePC B (p+count) 0 ∧
      ∀ reg, .x10≠reg → .x12≠reg → out.getReg reg=s.getReg reg := by
  induction count generalizing s j p with
  | zero =>
    simp only [trace,support_pure,Set.mem_singleton_iff] at hit;subst out
    exact ⟨by simpa using r,by simpa using pc,fun _ _ _ => rfl⟩
  | succ c ih =>
    simp only [trace,mem_support_bind_iff] at hit
    obtain ⟨reply,_,tail⟩ := hit
    have nextPC : (after k s j reply).pc=nodePC B (p+1) 0 := by
      rw [after_pc];exact next_pc B p s pc
    obtain ⟨rs,here,keep⟩ := ih _ (j+1) (p+1) (after_regs k s j reply r) nextPC tail
    refine ⟨by simpa only [Nat.add_assoc,Nat.add_comm 1 c] using rs,by simpa only [Nat.add_assoc,Nat.add_comm 1 c] using here,?_⟩
    intro reg a b;exact (keep reg a b).trans (after_reg k s j reply reg a b)

theorem counted_trace (oracle : Oracle) (k : Nat) (s : MachineState) (count j : Nat) :
    RunPublic oracle (trace k count j s) count := by
  induction count generalizing s j with
  | zero =>
    simp only [trace]
    exact run_pure_public ..
  | succ c ih =>
    rw [trace,show c+1=1+c by omega]
    exact run_bind_public _ _ _ 1 c (run_query_public ..) (fun _ => ih _ _)

/-! ### The looped segment -/

/-- The latch after a body of `S` nodes at word index `B`: `beq x12, x21, 8` then `jal` back. -/
structure Latch (B S : Nat) where
  back : BitVec 21
  target : nodePC B S 0+4+signExtend21 back=nodePC B 0 0
  branch : ∀ s : MachineState, s.pc=nodePC B S 0 → fetch image s=some (.base (.BEQ .x12 .x21 8))
  jump : ∀ s : MachineState, s.pc=nodePC B S 0+4 → fetch image s=some (.base (.JAL .x0 back))

def exitPC (B S : Nat) : Word := nodePC B S 0+8
/-- After an iteration with `n` iterations still to run. -/
def nextPC (B S n : Nat) : Word := if n=0 then exitPC B S else nodePC B 0 0
def latchCost (n : Nat) : Nat := if n=0 then 1 else 2

/-- `n` iterations of the body starting at node `j`. -/
def loops (k B S : Nat) : Nat → Nat → MachineState → OracleComp World MachineState
  | 0,_,s => pure s
  | n+1,j,s => do
    let body ← trace k S j s
    loops k B S n (j+S) (body.setPC (nextPC B S n))

private theorem slot_injective (k a b : Nat) (ha : a%5=0) (hb : b%5=0) (ba : a<2^24) (bb : b<2^24)
    (same : wordAddress (pentaSlotWord k a)=wordAddress (pentaSlotWord k b)) : a=b := by
  have room := slot_room k a ba
  have room' := slot_room k b bb
  have := wordAddress_injective_of_bound (by omega) (by omega) same
  unfold pentaSlotWord pentaGroupWord at this
  omega

theorem latch_run {B S : Nat} (latch : Latch B S) (k : Nat) (s : MachineState) (j stop n fuel : Nat)
    (aligned : j%5=0) (stopAligned : stop%5=0) (bound : j<2^24) (stopBound : stop<2^24)
    (iff : j=stop ↔ n=0) (r : Regs k s j)
    (pc : s.pc=nodePC B S 0) (x21 : s.getReg .x21=wordAddress (pentaSlotWord (k+1) stop)) :
    execute image (latchCost n+fuel) s true =
      (do let out ← execute image fuel (s.setPC (nextPC B S n)) true
          return out.charge (latchCost n) 0) := by
  have equal : s.getReg .x12=s.getReg .x21 ↔ n=0 := by
    rw [r.target,x21,←iff]
    constructor
    · intro h;exact slot_injective (k+1) j stop aligned stopAligned bound stopBound h
    · rintro rfl;rfl
  by_cases last : n=0
  · have step : ordinaryStep s (.base (.BEQ .x12 .x21 8))=some (s.setPC (exitPC B S)) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,equal.mpr last,signExtend13,exitPC]
    rw [latchCost,nextPC,if_pos last,if_pos last,Nat.add_comm 1 fuel,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (latch.branch s pc) step];rfl
  · let mid := s.setPC (nodePC B S 0+4)
    have diff : s.getReg .x12≠s.getReg .x21 := fun h => last (equal.mp h)
    have step : ordinaryStep s (.base (.BEQ .x12 .x21 8))=some mid := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,diff,mid]
    have jump : ordinaryStep mid (.base (.JAL .x0 latch.back))=some (s.setPC (nodePC B 0 0)) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,mid,MachineState.setReg,MachineState.setPC]
      exact latch.target
    rw [latchCost,nextPC,if_neg last,if_neg last,show 2+fuel=(fuel+1)+1 by omega,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (latch.branch s pc) step,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (latch.jump mid rfl) jump]
    simp [instructionCycles,Execution.charge,←Nat.add_assoc]

/-- Steps and cycles of `cnt` iterations, as sums (no subtraction). -/
def loopSteps (S cnt : Nat) : Nat := if cnt=0 then 0 else (3*S+2)*cnt-1
def loopCycles (S cnt : Nat) : Nat := if cnt=0 then 0 else (10*S+2)*cnt-1

private theorem loop_steps_succ (S c : Nat) :
    loopSteps S (c+1)=3*S+(latchCost c+loopSteps S c) ∧
    loopCycles S (c+1)=10*S+(latchCost c+loopCycles S c) := by
  unfold loopSteps loopCycles latchCost
  rcases c with _|c
  · simp
  · simp only [Nat.succ_ne_zero,ite_false]
    constructor <;> rw [Nat.mul_succ,Nat.mul_succ] <;> omega

theorem loops_run {B S : Nat} (seg : NodeSegment B S) (room : B+3*S<2^30) (latch : Latch B S)
    (k : Nat) (positive : 0<S) (multiple : S%5=0) (s : MachineState) (cnt j fuel : Nat)
    (aligned : j%5=0) (fits : j+S*cnt<2^24) (r : Regs k s j) (pc : 0<cnt → s.pc=nodePC B 0 0)
    (x21 : s.getReg .x21=wordAddress (pentaSlotWord (k+1) (j+S*cnt))) :
    execute image (loopSteps S cnt+fuel) s true =
      (do let next ← loops k B S cnt j s
          let out ← execute image fuel next true
          return out.charge (loopCycles S cnt) (S*cnt)) := by
  induction cnt generalizing s j with
  | zero => simp [loops,loopSteps,loopCycles,Execution.charge]
  | succ c ih =>
    have sizes := loop_steps_succ S c
    have fits' : j+S+S*c<2^24 := by rw [Nat.mul_succ] at fits;omega
    rw [sizes.1,Nat.add_assoc,sequence_run seg room k s S j 0 _ (by omega) (by omega)
      (by omega) r (pc (by omega))]
    simp only [loops,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro body reached
    obtain ⟨rs,here,keep⟩ := sequence_post B k s S j 0 r (pc (by omega)) reached
    have x21' : body.getReg .x21=wordAddress (pentaSlotWord (k+1) (j+S*(c+1))) :=
      (keep .x21 (by decide) (by decide)).trans x21
    have iff : j+S=j+S*(c+1) ↔ c=0 := by
      constructor
      · intro e
        rcases c with _|c
        · rfl
        · rw [Nat.mul_succ,Nat.mul_succ] at e;omega
      · rintro rfl;simp
    have mulAligned : (S*(c+1))%5=0 := by rw [Nat.mul_mod,multiple];simp
    rw [Nat.add_assoc (latchCost c),latch_run latch k body (j+S) (j+S*(c+1)) c _ (by omega) (by omega)
      (by omega) (by omega) iff rs (by simpa using here) x21']
    simp only [bind_assoc,pure_bind]
    let next := body.setPC (nextPC B S c)
    have regs : Regs k next (j+S) := regs_setPC k body (j+S) _ rs
    have again (positive : 0<c) : next.pc=nodePC B 0 0 := by
      dsimp only [next,MachineState.setPC]
      rw [nextPC,if_neg (by omega)]
    rw [ih next (j+S) (by omega) (by omega) regs again
      (by change body.getReg .x21=_;rw [x21',show j+S*(c+1)=j+S+S*c by rw [Nat.mul_succ];omega])]
    simp only [bind_assoc,pure_bind]
    apply bind_congr
    intro result
    simp only [Execution.charge]
    rw [sizes.2]
    congr 1
    funext x
    congr 2 <;> (try rw [Nat.mul_succ]) <;> omega

theorem loops_post (B : Nat) (k S : Nat) (s : MachineState) (cnt j : Nat) (r : Regs k s j)
    (pc : 0<cnt → s.pc=nodePC B 0 0) {out : MachineState} (hit : out ∈ support (loops k B S cnt j s)) :
    Regs k out (j+S*cnt) ∧ (0<cnt → out.pc=exitPC B S) ∧
      ∀ reg, .x10≠reg → .x12≠reg → out.getReg reg=s.getReg reg := by
  induction cnt generalizing s j with
  | zero =>
    simp only [loops,support_pure,Set.mem_singleton_iff] at hit;subst out
    exact ⟨by simpa using r,by omega,fun _ _ _ => rfl⟩
  | succ c ih =>
    simp only [loops,mem_support_bind_iff] at hit
    obtain ⟨body,reach,tail⟩ := hit
    obtain ⟨rs,here,keep⟩ := sequence_post B k s S j 0 r (pc (by omega)) reach
    let next := body.setPC (nextPC B S c)
    have regs : Regs k next (j+S) := regs_setPC k body (j+S) _ rs
    have again (positive : 0<c) : next.pc=nodePC B 0 0 := by
      dsimp only [next,MachineState.setPC]
      rw [nextPC,if_neg (by omega)]
    obtain ⟨done,finish,rest⟩ := ih next (j+S) regs again tail
    refine ⟨?_,fun _ => ?_,fun reg a b => (rest reg a b).trans (keep reg a b)⟩
    · have e : j+S+S*c=j+S*(c+1) := by rw [Nat.mul_succ];omega
      rw [←e];exact done
    · cases c with
      | zero =>
        simp only [loops,support_pure,Set.mem_singleton_iff] at tail
        rw [tail];change nextPC B S 0=exitPC B S
        rw [nextPC,if_pos rfl]
      | succ c => exact finish (by omega)

theorem counted_loops (oracle : Oracle) (k B S : Nat) (s : MachineState) (cnt j : Nat) :
    RunPublic oracle (loops k B S cnt j s) (S*cnt) := by
  induction cnt generalizing s j with
  | zero =>
    simp only [loops,Nat.mul_zero]
    exact run_pure_public ..
  | succ c ih =>
    rw [loops,show S*(c+1)=S+S*c by rw [Nat.mul_succ];omega]
    exact run_bind_public _ _ _ S _ (counted_trace ..) (fun _ => ih _ _)

/-! ### Clearing ragged slots -/

def zeroOps (offset count : Nat) : List Instr :=
  (List.range count).map (fun t => .SD .x12 .x0 (BitVec.ofNat 12 (offset+8*t)))

def zeroed (s : MachineState) (offset count i : Nat) := ((zeroOps offset count).take i).foldl execInstrBr s

/-- `count` stores `sd x0, offset+8t(x12)` at word index `Z`. -/
def ZeroSegment (Z offset count : Nat) : Prop :=
  ∀ t, t<count → (image.code[Z+t]?).bind decodeInstruction =
    some (.base (.SD .x12 .x0 (BitVec.ofNat 12 (offset+8*t))))

theorem sext_small (x : Nat) (small : x<2048) : signExtend12 (BitVec.ofNat 12 x)=BitVec.ofNat 64 x := by
  unfold signExtend12
  rw [BitVec.signExtend_eq_setWidth_of_msb_false (by
      rw [BitVec.msb_eq_false_iff_two_mul_lt,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)];omega),
    BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by omega)]

theorem zeroed_step (s : MachineState) (offset count i : Nat) (hi : i<count) :
    zeroed s offset count (i+1) = execInstrBr (zeroed s offset count i) (.SD .x12 .x0 (BitVec.ofNat 12 (offset+8*i))) := by
  unfold zeroed
  rw [List.take_succ,List.foldl_append]
  have : (zeroOps offset count)[i]? = some (.SD .x12 .x0 (BitVec.ofNat 12 (offset+8*i))) := by
    simp [zeroOps,hi]
  rw [this]
  rfl

theorem zeroed_reg (s : MachineState) (offset count i : Nat) (hi : i≤count) (reg : Reg) :
    (zeroed s offset count i).getReg reg=s.getReg reg := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [zeroed_step s offset count i (by omega)]
    change (((zeroed s offset count i).setMem _ _).setPC _).getReg reg = _
    rw [MachineState.getReg_setPC]
    have keep : ∀ (t : MachineState) (a v : Word), (t.setMem a v).getReg reg=t.getReg reg := by
      intro t a v;cases reg <;> rfl
    rw [keep]
    exact ih (by omega)

theorem zeroed_pc (s : MachineState) (offset count i : Nat) (hi : i≤count) :
    (zeroed s offset count i).pc=s.pc+BitVec.ofNat 64 (4*i) := by
  induction i with
  | zero => simp [zeroed]
  | succ i ih =>
    rw [zeroed_step s offset count i (by omega)]
    change (zeroed s offset count i).pc+BitVec.ofNat 64 4=_
    rw [ih (by omega),BitVec.add_assoc,←BitVec.ofNat_add]
    congr 2

theorem zeroed_memory (s : MachineState) (offset count i W : Nat) (hi : i≤count)
    (base : s.getReg .x12=wordAddress W) (aligned : offset%8=0) (small : offset+8*count<2048)
    (room : W+offset/8+count<2^33) (w : Nat) (hw : w<2^33) :
    memoryView (zeroed s offset count i) w =
      if W+offset/8≤w ∧ w<W+offset/8+i then 0 else memoryView s w := by
  induction i with
  | zero => simp [zeroed]
  | succ i ih =>
    rw [zeroed_step s offset count i (by omega)]
    change memoryView (((zeroed s offset count i).setMem _ ((zeroed s offset count i).getReg .x0)).setPC _) w=_
    have addr : (zeroed s offset count i).getReg .x12+signExtend12 (BitVec.ofNat 12 (offset+8*i)) =
        wordAddress (W+offset/8+i) := by
      rw [zeroed_reg s offset count i (by omega),base]
      have : signExtend12 (BitVec.ofNat 12 (offset+8*i))=BitVec.ofNat 64 (offset+8*i) :=
        sext_small _ (by omega)
      rw [this,wordAddress,←BitVec.ofNat_add]
      congr 1
      omega
    rw [addr]
    change memoryView ((zeroed s offset count i).setMem (wordAddress (W+offset/8+i)) 0) w=_
    rw [memory_at_store (by omega) (by omega)]
    unfold writeWord
    by_cases same : w=W+offset/8+i
    · rw [if_pos same,if_pos (by omega)]
    · rw [if_neg same,ih (by omega)]
      by_cases inside : W+offset/8≤w ∧ w<W+offset/8+i
      · rw [if_pos inside,if_pos (by omega)]
      · rw [if_neg inside,if_neg (by omega)]

theorem zero_run (Z offset count : Nat) (seg : ZeroSegment Z offset count) (room : Z+count<2^30)
    (s : MachineState) (W : Nat) (pc : s.pc=BitVec.ofNat 64 (4096+4*Z))
    (base : s.getReg .x12=wordAddress W) (aligned : offset%8=0) (small : offset+8*count<2048)
    (fits : W+offset/8+count<2^33) (fuel : Nat) :
    execute image (count+fuel) s true =
      (do let out ← execute image fuel (zeroed s offset count count) true
          return out.charge count 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := zeroed s offset count)
  intro i hi
  refine ⟨.base (.SD .x12 .x0 (BitVec.ofNat 12 (offset+8*i))),?_,?_,rfl⟩
  · apply fetch_code_index _ (Z+i) (by omega) _ _ (seg i hi)
    rw [zeroed_pc s offset count i (by omega),pc,←BitVec.ofNat_add]
    congr 1
    omega
  · rw [zeroed_step s offset count i hi]
    simp only [ordinaryStep]
    rw [if_pos]
    change accessValid ((zeroed s offset count i).getReg .x12+signExtend12 (BitVec.ofNat 12 (offset+8*i))) 8=true
    rw [zeroed_reg s offset count i (by omega),base]
    have : signExtend12 (BitVec.ofNat 12 (offset+8*i))=BitVec.ofNat 64 (offset+8*i) :=
      sext_small _ (by omega)
    rw [this,wordAddress,←BitVec.ofNat_add]
    simp only [accessValid,rangeValid,BitVec.toNat_ofNat,MEMORY_BYTES,Bool.and_eq_true,decide_eq_true_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

end TwoPermutationPrototype.Quad.Commit.Penta
