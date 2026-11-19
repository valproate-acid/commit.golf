import CommitGolfCandidate.QuadCommitPentaPass

/-! One level pass of the penta commit image (output level `k+1`), described by its code layout:
nine setup instructions (x10 := level-`k` group 0, x12 := level-`k+1` slot 0, x21 := the slot after
the looped part), `q` iterations of an `S`-node body with its latch, an `r`-node tail and `z`
stores clearing the ragged slots of the last level-`k+1` group. -/
namespace TwoPermutationPrototype.Quad.Commit.Penta
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] image leafCode levelsCode execute writeBits

structure Layout (k : Nat) where
  W : Nat
  ops : List Instr
  S : Nat
  q : Nat
  r : Nat
  z : Nat
  T : Nat
  tailIndex : T=W+9+(if q=0 then 0 else 3*S+2)
  fetchSetup : ∀ i, i<9 → (image.code[W+i]?).bind decodeInstruction = some (.base ((ops[i]?).getD .EBREAK))
  alu : ∀ i, i<9 → ∀ s : MachineState,
    ordinaryStep s (.base ((ops[i]?).getD .EBREAK)) = some (execInstrBr s ((ops[i]?).getD .EBREAK)) ∧
    instructionCycles (.base ((ops[i]?).getD .EBREAK)) = 1
  steps : ∀ i, i<9 → ∀ s : MachineState,
    ((ops.take (i+1)).foldl execInstrBr s) = execInstrBr ((ops.take i).foldl execInstrBr s) ((ops[i]?).getD .EBREAK)
  setup : ∀ s : MachineState, s.getReg .x9=4294971424 →
    (ops.foldl execInstrBr s).getReg .x10=wordAddress (pentaGroupWord k 0) ∧
    (ops.foldl execInstrBr s).getReg .x12=wordAddress (pentaSlotWord (k+1) 0) ∧
    (ops.foldl execInstrBr s).getReg .x21=wordAddress (pentaSlotWord (k+1) (S*q))
  keep : ∀ s : MachineState, ∀ reg, reg≠.x10 → reg≠.x12 → reg≠.x21 →
    (ops.foldl execInstrBr s).getReg reg=s.getReg reg
  pcs : ∀ s : MachineState, ∀ i, i≤9 → ((ops.take i).foldl execInstrBr s).pc=s.pc+BitVec.ofNat 64 (4*i)
  mem : ∀ s : MachineState, (ops.foldl execInstrBr s).mem=s.mem
  full : ops.take 9=ops
  body : 0<q → NodeSegment (W+9) S
  latch : 0<q → Latch (W+9) S
  tail : NodeSegment T r
  zero : ZeroSegment (T+3*r) 0 z
  count : S*q+r=pentaCount (k+1)
  ragged : z=4*(5*pentaCount (k+2)-pentaCount (k+1))
  shape : 0<q → 0<S ∧ S%5=0
  room : T+3*r+z<2^30
  small : 8*z<2048
  level : k≤9

def setupState {k : Nat} (L : Layout k) (s : MachineState) := L.ops.foldl execInstrBr s

/-- The level pass after the setup. -/
def levelTrace {k : Nat} (L : Layout k) (s : MachineState) : OracleComp World MachineState := do
  let a ← loops k (L.W+9) L.S L.q 0 (setupState L s)
  let b ← trace k L.r (L.S*L.q) a
  return zeroed b 0 L.z L.z

def levelSteps {k : Nat} (L : Layout k) : Nat := 9+(loopSteps L.S L.q+(3*L.r+L.z))
def levelCycles {k : Nat} (L : Layout k) : Nat := 9+(loopCycles L.S L.q+(10*L.r+L.z))
def endPC {k : Nat} (L : Layout k) : Word := BitVec.ofNat 64 (4096+4*(L.T+3*L.r+L.z))

theorem setup_run {k : Nat} (L : Layout k) (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (4096+4*L.W))
    (fuel : Nat) :
    execute image (9+fuel) s true =
      (do let out ← execute image fuel (setupState L s) true
          return out.charge 9 0) := by
  have room := L.room
  have tailIdx := L.tailIndex
  have final : setupState L s=(L.ops.take 9).foldl execInstrBr s := by rw [L.full];rfl
  rw [final]
  apply CommitGolfCandidate.execute_unit_steps (states := fun i => (L.ops.take i).foldl execInstrBr s)
  intro i hi
  refine ⟨.base ((L.ops[i]?).getD .EBREAK),?_,?_,(L.alu i hi s).2⟩
  · apply fetch_code_index _ (L.W+i) (by split at tailIdx <;> omega) _ _ (L.fetchSetup i hi)
    rw [L.pcs s i (by omega),pc,←BitVec.ofNat_add]
    congr 1
    omega
  · rw [L.steps i hi s]
    exact (L.alu i hi _).1

theorem setup_pc {k : Nat} (L : Layout k) (s : MachineState) : (setupState L s).pc=s.pc+BitVec.ofNat 64 36 := by
  have := L.pcs s 9 le_rfl
  rw [L.full] at this
  exact this

theorem setup_regs {k : Nat} (L : Layout k) (s : MachineState) (x9 : s.getReg .x9=4294971424)
    (x5 : s.getReg .x5=0) (x11 : s.getReg .x11=200) (x13 : s.getReg .x13=1) :
    Regs k (setupState L s) 0 ∧ (setupState L s).getReg .x21=wordAddress (pentaSlotWord (k+1) (L.S*L.q)) := by
  obtain ⟨a,b,c⟩ := L.setup s x9
  exact ⟨⟨a,b,(L.keep s .x5 (by decide) (by decide) (by decide)).trans x5,
    (L.keep s .x11 (by decide) (by decide) (by decide)).trans x11,
    (L.keep s .x13 (by decide) (by decide) (by decide)).trans x13⟩,c⟩

theorem loops_any {k : Nat} (L : Layout k) (t : MachineState) (regs : Regs k t 0)
    (pc : t.pc=nodePC (L.W+9) 0 0) (x21 : t.getReg .x21=wordAddress (pentaSlotWord (k+1) (L.S*L.q))) (fuel : Nat) :
    execute image (loopSteps L.S L.q+fuel) t true =
      (do let a ← loops k (L.W+9) L.S L.q 0 t
          let out ← execute image fuel a true
          return out.charge (loopCycles L.S L.q) (L.S*L.q)) := by
  by_cases none : L.q=0
  · simp [none,loops,loopSteps,loopCycles,Execution.charge]
  · have positive := L.shape (by omega)
    have room := L.room
    have tailIdx := L.tailIndex
    rw [if_neg none] at tailIdx
    have count := L.count
    have hk := L.level
    have countBound : pentaCount (k+1)<2^24 := by
      have table : ∀ k : Fin 10, pentaCount (k.val+1)<2^24 := by decide
      exact table ⟨k,by omega⟩
    exact loops_run (L.body (by omega)) (by omega) (L.latch (by omega)) k positive.1 positive.2 t L.q 0 fuel
      (by decide) (by omega) regs (fun _ => pc) (by simpa using x21)

theorem loops_any_post {k : Nat} (L : Layout k) (t : MachineState) (regs : Regs k t 0)
    (pc : t.pc=nodePC (L.W+9) 0 0) {a : MachineState} (hit : a ∈ support (loops k (L.W+9) L.S L.q 0 t)) :
    Regs k a (L.S*L.q) ∧ a.pc=nodePC L.T 0 0 ∧ ∀ reg, .x10≠reg → .x12≠reg → a.getReg reg=t.getReg reg := by
  have tailIdx := L.tailIndex
  obtain ⟨rs,finish,keep⟩ := loops_post (L.W+9) k L.S t L.q 0 regs (fun _ => pc) hit
  refine ⟨by simpa [Nat.mul_comm] using rs,?_,keep⟩
  by_cases none : L.q=0
  · have : a=t := by simpa [none,loops] using hit
    subst this
    rw [pc,tailIdx,if_pos none]
    try rfl
  · rw [finish (by omega),tailIdx,if_neg none]
    unfold exitPC nodePC
    change BitVec.ofNat 64 _+BitVec.ofNat 64 8=_
    rw [←BitVec.ofNat_add]
    congr 1 <;> omega

theorem level_run {k : Nat} (L : Layout k) (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (4096+4*L.W))
    (x9 : s.getReg .x9=4294971424) (x5 : s.getReg .x5=0) (x11 : s.getReg .x11=200) (x13 : s.getReg .x13=1)
    (fuel : Nat) :
    execute image (levelSteps L+fuel) s true =
      (do let out ← levelTrace L s
          let result ← execute image fuel out true
          return result.charge (levelCycles L) (pentaCount (k+1))) := by
  have room := L.room
  have tailIdx := L.tailIndex
  have count := L.count
  have hk := L.level
  have small := L.small
  have countBound : pentaCount (k+1)<2^24 := by
    have table : ∀ k : Fin 10, pentaCount (k.val+1)<2^24 := by decide
    exact table ⟨k,by omega⟩
  obtain ⟨regs,x21⟩ := setup_regs L s x9 x5 x11 x13
  have startPC : (setupState L s).pc=nodePC (L.W+9) 0 0 := by
    rw [setup_pc,pc];unfold nodePC;rw [←BitVec.ofNat_add];congr 1 <;> omega
  unfold levelSteps
  rw [show 9+(loopSteps L.S L.q+(3*L.r+L.z))+fuel=9+(loopSteps L.S L.q+(3*L.r+(L.z+fuel))) by omega,
    setup_run L s pc,loops_any L _ regs startPC x21]
  simp only [levelTrace,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a reachA
  obtain ⟨ra,pa,_⟩ := loops_any_post L _ regs startPC reachA
  have phase : 0%5=(L.S*L.q)%5 := by
    by_cases none : L.q=0
    · simp [none]
    · have := (L.shape (by omega)).2
      rw [Nat.mul_mod,this];simp
  rw [sequence_run L.tail (by omega) k a L.r (L.S*L.q) 0 _ (by omega) (by omega) phase ra pa]
  simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro b reachB
  obtain ⟨rb,pb,_⟩ := sequence_post L.T k a L.r (L.S*L.q) 0 ra pa reachB
  have target : b.getReg .x12=wordAddress (pentaSlotWord (k+1) (pentaCount (k+1))) := by
    rw [rb.target,show L.S*L.q+L.r=pentaCount (k+1) by omega]
  have slotFit : pentaSlotWord (k+1) (pentaCount (k+1))<2^31 := by
    have := base_word_le (k+1)
    unfold pentaSlotWord pentaGroupWord
    omega
  rw [zero_run (L.T+3*L.r) 0 L.z L.zero (by omega) b _ (by rw [pb];unfold nodePC;congr 1 <;> omega)
    target (by decide) (by omega) (by omega)]
  simp only [bind_assoc,pure_bind]
  apply bind_congr
  intro result
  simp only [levelCycles,Execution.charge]
  congr 2 <;> omega

theorem level_post {k : Nat} (L : Layout k) (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (4096+4*L.W))
    (x9 : s.getReg .x9=4294971424) (x5 : s.getReg .x5=0) (x11 : s.getReg .x11=200) (x13 : s.getReg .x13=1)
    {out : MachineState} (hit : out ∈ support (levelTrace L s)) :
    out.pc=endPC L ∧ ∀ reg, reg≠.x10 → reg≠.x12 → reg≠.x21 → out.getReg reg=s.getReg reg := by
  obtain ⟨regs,x21⟩ := setup_regs L s x9 x5 x11 x13
  have startPC : (setupState L s).pc=nodePC (L.W+9) 0 0 := by
    rw [setup_pc,pc];unfold nodePC;rw [←BitVec.ofNat_add];congr 1 <;> omega
  simp only [levelTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨a,reachA,b,reachB,rfl⟩ := hit
  obtain ⟨ra,pa,ka⟩ := loops_any_post L _ regs startPC reachA
  obtain ⟨rb,pb,kb⟩ := sequence_post L.T k a L.r (L.S*L.q) 0 ra pa reachB
  constructor
  · rw [zeroed_pc b 0 L.z L.z le_rfl,pb]
    unfold endPC nodePC
    rw [←BitVec.ofNat_add]
    congr 1
    omega
  · intro reg h10 h12 h21
    rw [zeroed_reg b 0 L.z L.z le_rfl,kb reg (Ne.symm h10) (Ne.symm h12),ka reg (Ne.symm h10) (Ne.symm h12)]
    exact L.keep s reg h10 h12 h21

theorem counted_level {k : Nat} (L : Layout k) (oracle : Oracle) (s : MachineState) :
    RunPublic oracle (levelTrace L s) (pentaCount (k+1)) := by
  unfold levelTrace
  rw [←L.count]
  apply run_bind_public _ _ _ (L.S*L.q) L.r (by simpa [Nat.mul_comm] using counted_loops oracle k (L.W+9) L.S _ L.q 0)
  intro a
  apply run_bind_public _ _ _ L.r 0 (counted_trace ..)
  intro b
  exact run_pure_public ..

/-! ### The standard level setup: three `lui; addi; add x9` pairs -/

def setupOps (a1 : BitVec 20) (a2 : BitVec 12) (b1 : BitVec 20) (b2 : BitVec 12) (c1 : BitVec 20) (c2 : BitVec 12) :
    List Instr :=
  [.LUI .x10 a1,.ADDI .x10 .x10 a2,.ADD .x10 .x9 .x10,
   .LUI .x12 b1,.ADDI .x12 .x12 b2,.ADD .x12 .x9 .x12,
   .LUI .x21 c1,.ADDI .x21 .x21 c2,.ADD .x21 .x9 .x21]

theorem setup_alu (a1 a2 b1 b2 c1 c2) (i : Nat) (hi : i<9) (s : MachineState) :
    ordinaryStep s (.base (((setupOps a1 a2 b1 b2 c1 c2)[i]?).getD .EBREAK)) =
      some (execInstrBr s (((setupOps a1 a2 b1 b2 c1 c2)[i]?).getD .EBREAK)) ∧
    instructionCycles (.base (((setupOps a1 a2 b1 b2 c1 c2)[i]?).getD .EBREAK)) = 1 := by
  interval_cases i <;> exact ⟨rfl,rfl⟩

theorem setup_steps (ops : List Instr) (i : Nat) (hi : i<ops.length) (s : MachineState) :
    ((ops.take (i+1)).foldl execInstrBr s) = execInstrBr ((ops.take i).foldl execInstrBr s) ((ops[i]?).getD .EBREAK) := by
  rw [List.take_add_one,List.foldl_append]
  rw [List.getElem?_eq_getElem hi]
  rfl

theorem setup_pcs (a1 a2 b1 b2 c1 c2) (s : MachineState) (i : Nat) (hi : i≤9) :
    (((setupOps a1 a2 b1 b2 c1 c2).take i).foldl execInstrBr s).pc=s.pc+BitVec.ofNat 64 (4*i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [setup_steps _ i (by simp [setupOps];omega)]
    have bound : i<9 := by omega
    have step : ∀ t : MachineState, (execInstrBr t (((setupOps a1 a2 b1 b2 c1 c2)[i]?).getD .EBREAK)).pc=t.pc+4 := by
      intro t;interval_cases i <;> rfl
    rw [step,ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 _+BitVec.ofNat 64 4=_
    rw [←BitVec.ofNat_add]
    congr 1 <;> omega

theorem setup_keep (a1 a2 b1 b2 c1 c2) (s : MachineState) (reg : Reg)
    (h10 : reg≠.x10) (h12 : reg≠.x12) (h21 : reg≠.x21) :
    ((setupOps a1 a2 b1 b2 c1 c2).foldl execInstrBr s).getReg reg=s.getReg reg := by
  simp only [setupOps,List.foldl_cons,List.foldl_nil,execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h10),MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h12),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h21)]

theorem setup_mem (a1 a2 b1 b2 c1 c2) (s : MachineState) :
    ((setupOps a1 a2 b1 b2 c1 c2).foldl execInstrBr s).mem=s.mem := rfl

theorem setup_full (a1 a2 b1 b2 c1 c2) : (setupOps a1 a2 b1 b2 c1 c2).take 9=setupOps a1 a2 b1 b2 c1 c2 := rfl

end TwoPermutationPrototype.Quad.Commit.Penta
