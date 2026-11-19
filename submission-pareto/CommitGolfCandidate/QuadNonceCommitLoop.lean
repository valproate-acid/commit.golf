import CommitGolfCandidate.QuadCommitExecution
import CommitGolfCandidate.TwoPermutationCommitSetup

/-! NonceChain generator of the quad commit image (31727a8's loop, retargeted).
Words 236549..237420: x12 := x22, x7 := x22 + 0x10002000, then 1525248 forward permutation
calls (288 per latch), then x10 := x18, x12 := x9 and a jump back to word 18. -/
namespace TwoPermutationPrototype.Quad.Commit.Chain
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ### The permutation syscall -/

def chainPermInput (s : MachineState) : BitVec PERMUTATION_WIDTH := readBuffer s (s.getReg .x10).toNat 200
def chainPermReply (s : MachineState) (y : BitVec PERMUTATION_WIDTH) := writeBits s (s.getReg .x12) y

/-- Selector, width and primitive of the forward permutation call. -/
def ChainPermReady (state : MachineState) : Prop :=
  state.getReg .x5 = 0 ∧ state.getReg .x11 = 200 ∧ state.getReg .x13 = 1

theorem chain_read_width (state : MachineState) (address kind : Nat) (one : kind = 1) :
    BitVec.setWidth 1600 (readBuffer state address
      (((if kind = 0 then 512 else 1600) + 7) / 8)) =
      readBuffer state address 200 := by
  subst one
  exact BitVec.setWidth_eq _

theorem chain_oracle_input (state : MachineState) (ready : ChainPermReady state)
    (sourceAligned : (state.getReg .x10).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x12).toNat % 8 = 0)
    (sourceBound : (state.getReg .x10).toNat + 200 ≤ MEMORY_BYTES)
    (destinationBound : (state.getReg .x12).toNat + 200 ≤ MEMORY_BYTES) :
    oracleInput state = some (.inr (.inl (chainPermInput state))) := by
  rcases ready with ⟨_, width, kind⟩
  have kindNat : (state.getReg .x13).toNat = 1 := by rw [kind]; rfl
  have widthNat : (state.getReg .x11).toNat = 200 := by rw [width]; rfl
  simp [oracleInput, kindNat, widthNat, rangeValid, sourceAligned, destinationAligned,
    sourceBound, destinationBound, PERMUTATION_WIDTH, COMPRESSION_INPUT_LENGTH, chainPermInput]
  exact chain_read_width state _ _ kindNat

/-- One forward permutation syscall: eight cycles, one query, any 1600-bit reply. -/
theorem chain_perm_call (image : Image) (state : MachineState) (fuel : Nat) (allowCoins : Bool)
    (fetched : fetch image state = some (.base .ECALL))
    (ready : ChainPermReady state)
    (sourceAligned : (state.getReg .x10).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x12).toNat % 8 = 0)
    (sourceBound : (state.getReg .x10).toNat + 200 ≤ MEMORY_BYTES)
    (destinationBound : (state.getReg .x12).toNat + 200 ≤ MEMORY_BYTES) :
    execute image (1 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inr (.inl (chainPermInput state))))
          let result ← execute image fuel (chainPermReply state answer) allowCoins
          return result.charge 8 1) := by
  rw [Nat.add_comm 1 fuel, execute, fetched, if_pos ready.1,
    chain_oracle_input state ready sourceAligned destinationAligned sourceBound destinationBound]
  rfl

/-! ### Fetching the generator and the patched setup words -/

def genOps : List Instr :=
  [.ADDI .x12 .x22 0,.LUI .x7 65538,.ADDI .x7 .x7 0,.ADD .x7 .x7 .x22] ++
  (List.replicate 288 [.ECALL,.ADDI .x10 .x10 176,.ADDI .x12 .x12 176]).flatten ++
  [.BLTU .x12 .x7 4736,.ADDI .x10 .x18 0,.ADDI .x12 .x9 0,.JAL .x0 1147544]

/-- Words 0..18 of the NonceChain image. -/
def nonceSetupOps : List Instr :=
  [.ADDI .x8 .x11 0,.ADDI .x9 .x12 0,.ADDI .x18 .x10 0,
   .LUI .x20 1,.ADDI .x20 .x20 1536,.ADD .x20 .x9 .x20,
   .LUI .x22 442369,.ADDI .x22 .x22 0,.ADD .x22 .x9 .x22,
   .ADDI .x5 .x0 2,.ADDI .x10 .x22 (-176),.ADDI .x11 .x0 24,.ADDI .x11 .x11 0,
   .ECALL,
   .ADDI .x5 .x0 0,.ADDI .x11 .x0 200,.ADDI .x13 .x0 1,.JAL .x0 946128,.SLLI .x7 .x13 12]

private theorem gen_decoded : ∀ j : Fin 872,
    (genWords[j.val]?).bind decodeInstruction = some (.base ((genOps[j.val]?).getD .EBREAK)) := by
  decide +kernel

private theorem nonce_setup_decoded : ∀ i : Fin 19,
    (setupWords[i.val]?).bind decodeInstruction = some (.base ((nonceSetupOps[i.val]?).getD .EBREAK)) := by
  decide +kernel

/-- The 11 root copy/HALT words preceding the generator inside `rootWords`. -/
def rootCoreWords : List (BitVec 32) :=
  [0x0204bf83, 0x01f43023, 0x0284bf83, 0x01f43423, 0x0304bf83, 0x01f43823, 0x0384bf83, 0x01f43c23, 0x00100293, 0x00000513, 0x00000073]

def genPrefix := Penta.rootHead++rootSetupWords++rootCoreWords

theorem gen_prefix_length : genPrefix.length=236549 := by
  unfold genPrefix
  simp only [List.length_append]
  rw [Penta.root_head_length]
  rfl

attribute [local irreducible] image leafCode levelsCode decodeInstruction

theorem fetch_gen (j : Nat) (inside : j<872) (s : MachineState)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*(236549+j))) :
    fetch image s=some (.base ((genOps[j]?).getD .EBREAK)) := by
  apply fetch_code_index s (236549+j) (by omega) pc
  have atIndex := code_segment_at genPrefix genWords []
    (by unfold image genPrefix Penta.rootHead rootWords rootCoreWords;simp only [List.append_assoc,List.append_nil]) j
    (Nat.lt_of_lt_of_le inside (by decide))
  rw [gen_prefix_length] at atIndex
  rw [atIndex]
  exact gen_decoded ⟨j,inside⟩

theorem fetch_nonce_setup (i : Nat) (inside : i<19) (s : MachineState)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*i)) :
    fetch image s=some (.base ((nonceSetupOps[i]?).getD .EBREAK)) := by
  apply fetch_code_index s i (by omega) pc
  have word := code_segment_at [] setupWords
    (leafCode++leafLatchWords++leafZeroWords++levelsCode++rootSetupWords++rootWords)
    (by unfold image;simp only [List.nil_append,List.append_assoc]) i inside
  simp only [List.length_nil,Nat.zero_add] at word
  rw [word]
  exact nonce_setup_decoded ⟨i,inside⟩

/-! ### The loop -/

abbrev nonceChainBase : Nat := 6106914848
abbrev nonceChainCount : Nat := 1525248
def nonceChainDest (j : Nat) := nonceChainBase + 176*j
def nonceChainSource (j : Nat) := (nonceChainBase - 176) + 176*j
def nonceChainPC (j : Nat) := if j = nonceChainCount then 953768 else 950308 + 12*(j%288)
def nonceChainSteps (j : Nat) := 3*j + j/288
def nonceChainCycles (j : Nat) := 10*j + j/288

def chainAdvance (s : MachineState) (j : Nat) (y : BitVec 1600) : MachineState :=
  let after := writeBits s (s.getReg .x12) y
  let inc := execInstrBr (execInstrBr after (.ADDI .x10 .x10 176)) (.ADDI .x12 .x12 176)
  inc.setPC (BitVec.ofNat 64 (nonceChainPC (j+1)))

def chainRun (j : Nat) (s : MachineState) : Nat → OracleComp World MachineState
  | 0 => pure s
  | n+1 => do
    let y ← World.query (.inr (.inr (.inl (chainPermInput s))))
    chainRun (j+1) (chainAdvance s j y) n

structure NonceChainFrame (s : MachineState) (j : Nat) : Prop where
  pc : s.pc = BitVec.ofNat 64 (nonceChainPC j)
  ready : ChainPermReady s
  input : s.getReg .x10 = BitVec.ofNat 64 (nonceChainSource j)
  output : s.getReg .x12 = BitVec.ofNat 64 (nonceChainDest j)
  limit : s.getReg .x7 = BitVec.ofNat 64 (nonceChainDest nonceChainCount)

theorem chain_advance_register (s : MachineState) (j : Nat) (y : BitVec 1600) (r : Reg)
    (ha : r ≠ .x10) (hb : r ≠ .x12) : (chainAdvance s j y).getReg r = s.getReg r := by
  simp only [chainAdvance,execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ ha.symm,
    MachineState.getReg_setReg_ne _ _ _ _ hb.symm,writeBits_register]

theorem chain_advance_frame (s : MachineState) (j : Nat) (y : BitVec 1600)
    (h : NonceChainFrame s j) : NonceChainFrame (chainAdvance s j y) (j+1) := by
  have keep (r : Reg) (ha : r ≠ .x10 := by decide) (hb : r ≠ .x12 := by decide) :=
    chain_advance_register s j y r ha hb
  refine ⟨rfl, ⟨(keep .x5).trans h.ready.1, (keep .x11).trans h.ready.2.1,
    (keep .x13).trans h.ready.2.2⟩, ?_, ?_, (keep .x7).trans h.limit⟩
  · change _ + 176#64 = _
    rw [writeBits_register,h.input]
    unfold nonceChainSource
    rw [show nonceChainBase-176+176*(j+1) = nonceChainBase-176+176*j+176 by omega]
    simp only [BitVec.ofNat_add]
  · change _ + 176#64 = _
    change (writeBits s (s.getReg .x12) y).getReg .x12 + 176#64 = _
    rw [writeBits_register,h.output]
    unfold nonceChainDest
    rw [show nonceChainBase+176*(j+1) = nonceChainBase+176*j+176 by omega]
    simp only [BitVec.ofNat_add]

private def triple (k : Nat) : Instr :=
  if k=0 then .ECALL else if k=1 then .ADDI .x10 .x10 176 else .ADDI .x12 .x12 176

private theorem triple_ops : ∀ u : Fin 288, ∀ k : Fin 3,
    (genOps[4+3*u.val+k.val]?).getD .EBREAK = triple k.val := by decide +kernel

theorem nonce_chain_triple (j k : Nat) (hj : j < 288) (hk : k < 3) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (950308+12*j+4*k)) :
    fetch image s = some (.base (triple k)) := by
  have fetched := fetch_gen (4+3*j+k) (by omega) s (by rw [pc];congr 1;omega)
  rw [fetched]
  exact congrArg (fun i => some (Instruction.base i)) (triple_ops ⟨j,hj⟩ ⟨k,hk⟩)

theorem nonce_chain_latch (s : MachineState) (pc : s.pc=953764) :
    fetch image s=some (.base (.BLTU .x12 .x7 4736)) :=
  fetch_gen 868 (by decide) s pc

def nonceIncrements (s : MachineState) := execInstrBr
  (execInstrBr s (.ADDI .x10 .x10 176)) (.ADDI .x12 .x12 176)

theorem nonce_increments_execute (j : Nat) (hj : j < 288) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (950308+12*j+4)) (fuel : Nat) :
    execute image (2+fuel) s true =
      (do let r ← execute image fuel (nonceIncrements s) true
          return r.charge 2 0) := by
  let mid := execInstrBr s (.ADDI .x10 .x10 176)
  have first := nonce_chain_triple j 1 hj (by decide) s pc
  have mp : mid.pc = BitVec.ofNat 64 (950308+12*j+4*2) := by
    change s.pc+4=_
    rw [pc,show 950308+12*j+4*2 = (950308+12*j+4)+4 by omega]
    simp only [BitVec.ofNat_add]
    rfl
  have second := nonce_chain_triple j 2 hj (by decide) mid mp
  rw [show 2+fuel = (fuel+1)+1 by omega,
    execute_ordinary_step _ _ _ mid _ _ first rfl,
    execute_ordinary_step _ _ _ (nonceIncrements s) _ _ second rfl]
  simp only [bind_assoc,pure_bind]
  apply bind_congr
  intro r
  simp [Execution.charge,instructionCycles,triple] <;> omega

theorem nonce_latch_pc (s : MachineState) (j : Nat) (endGroup : j%288=287)
    (hj : j < nonceChainCount) (pc : s.pc=953764)
    (output : s.getReg .x12 = BitVec.ofNat 64 (nonceChainDest (j+1)))
    (limit : s.getReg .x7 = BitVec.ofNat 64 (nonceChainDest nonceChainCount)) :
    execInstrBr s (.BLTU .x12 .x7 4736) = s.setPC (BitVec.ofNat 64 (nonceChainPC (j+1))) := by
  have comp : (s.getReg .x12).ult (s.getReg .x7) = decide (j+1<nonceChainCount) := by
    rw [output,limit]
    simp only [BitVec.ult, BitVec.toNat_ofNat,nonceChainDest]
    rw [Nat.mod_eq_of_lt (by dsimp [nonceChainBase,nonceChainCount] at *; omega),
      Nat.mod_eq_of_lt (by decide)]
    simp only [Nat.add_lt_add_iff_left,Nat.mul_lt_mul_left (by decide : 0<176)]
  simp only [execInstrBr,comp,pc,nonceChainPC]
  by_cases last : j+1=nonceChainCount
  · simp [last] <;> rfl
  · have take : j+1<nonceChainCount := by omega
    have slot : (j+1)%288 = 0 := by omega
    simp [take,last,slot] <;> rfl

theorem nonce_reply_pc (s : MachineState) (y : BitVec PERMUTATION_WIDTH) :
    (chainPermReply s y).pc = s.pc + 4 := rfl

theorem nonce_increments_pc (s : MachineState) : (nonceIncrements s).pc = s.pc+4+4 := rfl

theorem chain_advance_eq (s : MachineState) (j : Nat) (y : BitVec PERMUTATION_WIDTH) :
    chainAdvance s j y = (nonceIncrements (chainPermReply s y)).setPC (BitVec.ofNat 64 (nonceChainPC (j+1))) := rfl

end TwoPermutationPrototype.Quad.Commit.Chain
