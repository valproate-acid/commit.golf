import CommitGolfCandidate.TwoPermutationParentLoop

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute

structure PackedParentWordsAt (image : Image) (pc : Word) : Prop where
  call : ∀ s : MachineState, s.pc=pc → fetch image s=some (.base .ECALL)
  mask : ∀ s : MachineState, s.pc=pc+4 → fetch image s=some (.base (.SH .x12 .x0 30))
  source : ∀ s : MachineState, s.pc=pc+8 →
    fetch image s=some (.base (.ADDI .x10 .x10 4032))
  target : ∀ s : MachineState, s.pc=pc+12 →
    fetch image s=some (.base (.ADDI .x12 .x12 4064))

def packedParentMask (s : MachineState) (n : Nat) (answer : BitVec 256) :=
  execInstrBr (parentWritten s n answer) (.SH .x12 .x0 30)

def packedParentAfter (s : MachineState) (n : Nat) (answer : BitVec 256) :=
  execInstrBr (execInstrBr (packedParentMask s n answer) (.ADDI .x10 .x10 4032)) (.ADDI .x12 .x12 4064)

def packedParentsTrace (remaining : Nat) : Nat → MachineState → OracleComp World MachineState
  | 0, state => pure state
  | count+1, state => do
    let answer ← (liftM (World.query (.inr (.inl (parentInput state (remaining+(count+1)))))) : OracleComp World (BitVec 256))
    packedParentsTrace remaining count (packedParentAfter state (remaining+(count+1)) answer)

theorem packed_parent_pc (state : MachineState) (n : Nat) (answer : BitVec 256) :
    (packedParentAfter state n answer).pc=state.pc+16 := by
  change (parentWritten state n answer).pc+4+4+4=state.pc+16
  rw [parentWritten,written_pc,BitVec.add_assoc,BitVec.add_assoc,BitVec.add_assoc]
  rfl

private theorem register_after_halfword (state : MachineState) (address : Word)
    (word : BitVec 16) (reg : Reg) :
    (state.setHalfword address word).getReg reg=state.getReg reg := by
  unfold MachineState.setHalfword
  rfl

private theorem register_after_mask_instruction (state : MachineState) (reg : Reg) :
    (execInstrBr state (.SH .x12 .x0 30)).getReg reg=state.getReg reg := by
  simp only [execInstrBr,MachineState.getReg_setPC,register_after_halfword]

private theorem mask_register (state : MachineState) (n : Nat) (answer : BitVec 256) (reg : Reg) :
    (packedParentMask state n answer).getReg reg=(parentWritten state n answer).getReg reg :=
  register_after_mask_instruction (parentWritten state n answer) reg

attribute [local irreducible] parentWritten packedParentMask

theorem packed_parent_keeps_register (state : MachineState) (n : Nat) (answer : BitVec 256) (reg : Reg)
    (keptSource : .x10≠reg) (keptTarget : .x12≠reg) :
    (packedParentAfter state n answer).getReg reg=state.getReg reg := by
  simp only [packedParentAfter,execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ keptSource,MachineState.getReg_setReg_ne _ _ _ _ keptTarget]
  rw [mask_register,parentWritten,CommitGolfCandidate.writeBits_register]

theorem packed_next_parent_regs (state : MachineState) (n : Nat) (answer : BitVec 256)
    (regs : ParentRegs state (n+1)) : ParentRegs (packedParentAfter state (n+1) answer) n := by
  have next := next_parent_regs state n answer regs
  constructor
  · change (packedParentMask state (n+1) answer).getReg .x10 + signExtend12 4032 = _
    rw [mask_register]
    exact next.source
  · change (packedParentMask state (n+1) answer).getReg .x12 + signExtend12 4064 = _
    rw [mask_register]
    exact next.target
  · exact (packed_parent_keeps_register state _ answer .x5 (by decide) (by decide)).trans regs.selector
  · exact (packed_parent_keeps_register state _ answer .x11 (by decide) (by decide)).trans regs.size
  · exact (packed_parent_keeps_register state _ answer .x13 (by decide) (by decide)).trans regs.primitive
  · exact (packed_parent_keeps_register state _ answer .x9 (by decide) (by decide)).trans regs.heap

private theorem parent_call_at (image : Image) (s : MachineState) (n fuel : Nat)
    (bound : n < 2^24) (regs : ParentRegs s n)
    (fetched : fetch image s=some (.base .ECALL)) :
    execute image (fuel+1) s true =
      (do let answer ← (liftM (World.query (.inr (.inl (parentInput s n)))) : OracleComp World (BitVec 256))
          let result ← execute image fuel (parentWritten s n answer) true
          return result.charge 8 1) := by
  have source := word_address_value (word := treeWord (2*n)) (by unfold treeWord; omega)
  have target := word_address_value (word := treeWord n) (by unfold treeWord; omega)
  have inputRange : 8*treeWord (2*n)+64 ≤ MEMORY_BYTES := by unfold treeWord MEMORY_BYTES; omega
  have outputRange : 8*treeWord n+32 ≤ MEMORY_BYTES := by unfold treeWord MEMORY_BYTES; omega
  have query : oracleInput s=some (.inl (parentInput s n)) := by
    have kind : (s.getReg .x13).toNat=0 := by rw [regs.primitive]; rfl
    unfold oracleInput
    dsimp only
    rw [kind]
    simp [regs.source,regs.target,regs.size,COMPRESSION_INPUT_LENGTH,COMPRESSION_OUTPUT_LENGTH,
      rangeValid,source,target,inputRange,outputRange,parentInput]
  simp [execute,fetched,regs.selector,query,writeOracleAnswer,regs.target,parentWritten,
    oracleCycles,COMPRESSION_CYCLES]
  rfl

private theorem packed_parent_step (image : Image) (s : MachineState) (n fuel : Nat) (pc : Word)
    (here : s.pc=pc) (bound : n<2^24) (regs : ParentRegs s n)
    (fetched : PackedParentWordsAt image pc) :
    execute image (4+fuel) s true =
      (do let answer ← (liftM (World.query (.inr (.inl (parentInput s n)))) : OracleComp World (BitVec 256))
          let result ← execute image fuel (packedParentAfter s n answer) true
          return result.charge 11 1) := by
  rw [show 4+fuel=(fuel+3)+1 by omega,parent_call_at image s n _ bound regs (fetched.call s here)]
  apply bind_congr_of_forall_mem_support
  intro answer _
  let first := parentWritten s n answer
  let masked := packedParentMask s n answer
  let moved := execInstrBr masked (.ADDI .x10 .x10 4032)
  have firstPC : first.pc=pc+4 := by simp only [first,parentWritten,written_pc,here]
  have maskPC : masked.pc=pc+8 := by
    unfold masked packedParentMask
    change first.pc+4=_
    rw [firstPC,BitVec.add_assoc]
    rfl
  have movedPC : moved.pc=pc+12 := by
    change masked.pc+4=_
    rw [maskPC,BitVec.add_assoc]
    rfl
  have target : first.getReg .x12=wordAddress (treeWord n) := by
    unfold first parentWritten
    rw [CommitGolfCandidate.writeBits_register,regs.target]
  have address : first.getReg .x12 + signExtend12 30 = BitVec.ofNat 64 (8*treeWord n+30) := by
    rw [target]
    change BitVec.ofNat 64 (8*treeWord n)+BitVec.ofNat 64 30=_
    rw [←BitVec.ofNat_add]
  have limit : 8*treeWord n+32 ≤ MEMORY_BYTES := by unfold MEMORY_BYTES treeWord; omega
  have address64 : 8*treeWord n+30<2^64 := by unfold MEMORY_BYTES at limit; omega
  have valid : accessValid (BitVec.ofNat 64 (8*treeWord n+30)) 2=true := by
    have nat : (BitVec.ofNat 64 (8*treeWord n+30)).toNat=8*treeWord n+30 := by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt address64]
    simp only [accessValid,rangeValid,nat,Bool.and_eq_true,decide_eq_true_eq]
    constructor <;> omega
  have clear : ordinaryStep first (.base (.SH .x12 .x0 30))=some masked := by
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,address,valid,↓reduceIte]
    unfold masked packedParentMask
    rfl
  rw [CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetched.mask first firstPC) clear,
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetched.source masked maskPC)
      (show ordinaryStep masked _=some moved from rfl),
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetched.target moved movedPC)
      (show ordinaryStep moved _=some (packedParentAfter s n answer) from rfl)]
  simp [instructionCycles,Execution.charge,←Nat.add_assoc]

def packedParentPC (base : Word) (slot : Nat) : Word := base+BitVec.ofNat 64 (16*slot)

private theorem packed_parent_pc_succ (base : Word) (slot : Nat) :
    packedParentPC base slot+16=packedParentPC base (slot+1) := by
  change base+BitVec.ofNat 64 (16*slot)+BitVec.ofNat 64 16 =
    base+BitVec.ofNat 64 (16*(slot+1))
  rw [BitVec.add_assoc,←BitVec.ofNat_add]
  rw [show 16*slot+16=16*(slot+1) by omega]

theorem packed_parent_segment (image : Image) (base : Word) (span : Nat)
    (fetches : ∀ i < span, PackedParentWordsAt image (packedParentPC base i))
    (remaining count slot fuel : Nat) (s : MachineState)
    (bound : remaining+count<2^24) (inside : slot+count≤span)
    (regs : ParentRegs s (remaining+count)) (pc : s.pc=packedParentPC base slot) :
    execute image (4*count+fuel) s true =
      (do let mid ← packedParentsTrace remaining count s
          let result ← execute image fuel mid true
          return result.charge (11*count) count) := by
  induction count generalizing slot s with
  | zero => simp [packedParentsTrace,Execution.charge]
  | succ count ih =>
    rw [show 4*(count+1)+fuel=4+(4*count+fuel) by omega,
      packed_parent_step image s _ _ _ pc bound regs (fetches slot (by omega))]
    simp only [packedParentsTrace,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro answer _
    have next := packed_next_parent_regs s (remaining+count) answer (by simpa only [Nat.add_assoc] using regs)
    have atNext := (packed_parent_pc s (remaining+(count+1)) answer).trans
      ((congrArg (·+16) pc).trans (packed_parent_pc_succ base slot))
    rw [ih (slot+1) _ (by omega) (by omega) (by simpa only [Nat.add_assoc] using next) atNext]
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem packed_parent_segment_post (base : Word) (remaining count slot : Nat)
    (s : MachineState) (regs : ParentRegs s (remaining+count)) (pc : s.pc=packedParentPC base slot)
    {out : MachineState} (reached : out ∈ support (packedParentsTrace remaining count s)) :
    ParentRegs out remaining ∧ out.pc=packedParentPC base (slot+count) := by
  induction count generalizing slot s with
  | zero =>
    simp only [packedParentsTrace,support_pure,Set.mem_singleton_iff] at reached
    subst out
    exact ⟨regs,pc⟩
  | succ count ih =>
    simp only [packedParentsTrace,mem_support_bind_iff] at reached
    obtain ⟨answer,_,tail⟩ := reached
    have next := packed_next_parent_regs s (remaining+count) answer (by simpa only [Nat.add_assoc] using regs)
    have atNext := (packed_parent_pc s (remaining+(count+1)) answer).trans
      ((congrArg (·+16) pc).trans (packed_parent_pc_succ base slot))
    rw [show slot+(count+1)=slot+1+count by omega]
    exact ih (slot+1) _ (by simpa only [Nat.add_assoc] using next) atNext tail

end TwoPermutationPrototype.RV64
