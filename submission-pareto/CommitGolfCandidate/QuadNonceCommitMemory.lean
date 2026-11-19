import CommitGolfCandidate.QuadNonceCommitSetup
import CommitGolfCandidate.QuadCommitInput
import CommitGolfCandidate.NonceChainLayout

/-! Memory of the NonceChain generator in the quad layout. The next permutation input is the
whole previous reply; the 176 low bytes of each reply are the eleven salts of its block and
survive all later replies. Messages and the nine zero words of every group cell are untouched. -/
namespace TwoPermutationPrototype.Quad.Commit.Chain
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open CommitGolfCandidate.Permutation.NonceChain (Key Word1600 actualNonces orbit seedState)
set_option maxRecDepth 14000
set_option maxHeartbeats 400000
set_option exponentiation.threshold 2048

private theorem seed_mem (s : MachineState) : (seedSetup s).mem=s.mem := rfl
private theorem written_mem (s : MachineState) (k : Key) :
    (chainInitial s k).mem=(seedWritten s k).mem := rfl

theorem chain_read_zero (state : MachineState) (address count : Nat)
    (zero : ∀ i < count, state.getByte (BitVec.ofNat 64 (address+i)) = 0) :
    (readBuffer state address count).toNat = 0 := by
  unfold readBuffer
  rw [Finset.sum_eq_zero (fun i hi => by simp [zero i (Finset.mem_range.mp hi)])]
  simp

/-- A buffer is its low part plus the shifted high part. -/
theorem chain_read_append (state : MachineState) (address left right total middle : Nat)
    (size : left+right = total) (next : address+left = middle) :
    (readBuffer state address total).toNat =
      (readBuffer state address left).toNat +
        2^(8*left) * (readBuffer state middle right).toNat := by
  subst size
  subst next
  have low : (readBuffer state address (left+right)).extractLsb' (8*0) (8*left) =
      readBuffer state address left := by
    have slice := read_buffer_slice state address (left+right) 0 left (by omega)
    rwa [Nat.add_zero] at slice
  have high := read_buffer_slice state address (left+right) left right (by omega)
  have lowNat := congrArg BitVec.toNat low
  have highNat := congrArg BitVec.toNat high
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.mul_zero, Nat.pow_zero,
    Nat.div_one] at lowNat highNat
  have bound : (readBuffer state address (left+right)).toNat < 2^(8*left) * 2^(8*right) := by
    have limit := (readBuffer state address (left+right)).isLt
    have power : 2^(8*(left+right)) = 2^(8*left) * 2^(8*right) := by
      rw [Nat.mul_add, Nat.pow_add]
    exact lt_of_lt_of_eq limit power
  rw [← lowNat, ← highNat, Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul bound)]
  exact (Nat.mod_add_div _ _).symm

private theorem extract_self {w : Nat} (v : BitVec w) : v.extractLsb' 0 w = v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_zero,Nat.mod_eq_of_lt v.isLt]

private theorem read_written {w : Nat} (s : MachineState) (a : Nat) (v : BitVec w)
    (off cnt : Nat) (size : off+cnt ≤ (w+7)/8) (bound : (w+7)/8 ≤ 2^64) :
    readBuffer (writeBits s (BitVec.ofNat 64 a) v) (a+off) cnt =
      v.extractLsb' (8*off) (8*cnt) := by
  apply read_serialized_slice
  intro j hj
  simpa only [BitVec.ofNat_add,Nat.add_assoc,BitVec.add_assoc] using
    write_bits_byte s (BitVec.ofNat 64 a) v (off+j) (by omega) bound

/-- Every used group's zero prefix lies below the seed block. -/
theorem zeros_below_seed (k g : Nat) (hk : k ≤ 10) (hg : g < pentaCount (k+1)) (t : Fin 5) :
    8*(pentaGroupWord k g+t.val)+8 ≤ nonceChainSource 0 := by
  have := level_order k 11 g (by omega) le_rfl hg 1
  have := levels_below_salts
  have := t.isLt
  unfold saltWord at *
  unfold nonceChainSource nonceChainBase
  omega

/-- Group words lie above the message block. -/
theorem zeros_above_message (k g : Nat) (hk : k ≤ 10) (t : Nat) :
    4096+16777216*256 ≤ 8*(pentaGroupWord k g+t) := by
  have := trapdoor_below_levels k g (by omega)
  omega

structure ChainMemory (π : Perm) (k : Key) (m : Message) (j : Nat) (s : MachineState) : Prop where
  input : readBuffer s (nonceChainSource j) 200 = orbit π (seedState k) j
  message : ∀ i : Index, readBuffer s (4096+256*i.val) 256 = m i
  nonce : ∀ i : Index, i.val/11 < j → readBuffer s (nonceChainBase+16*i.val) 16 = actualNonces π k i
  zeros : ∀ k g, k ≤ 10 → g < pentaCount (k+1) → ∀ t : Fin 5,
    readBuffer s (8*(pentaGroupWord k g+t.val)) 8 = 0

attribute [local irreducible] readBuffer writeBits actualNonces chainAdvance

private theorem advance_mem (s : MachineState) (j : Nat) (y : Word1600) :
    (chainAdvance s j y).mem = (writeBits s (s.getReg .x12) y).mem := by unfold chainAdvance;rfl

theorem chain_step_memory (π : Perm) (k : Key) (m : Message) (s : MachineState) (j : Nat)
    (bound : j < nonceChainCount) (frame : NonceChainFrame s j) (old : ChainMemory π k m j s) :
    ChainMemory π k m (j+1) (chainAdvance s j (π (chainPermInput s))) := by
  have src : (s.getReg .x10).toNat = nonceChainSource j := by
    rw [frame.input,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by
      dsimp [nonceChainCount] at bound; unfold nonceChainSource nonceChainBase;omega)]
  have input : chainPermInput s = orbit π (seedState k) j := by
    unfold chainPermInput
    rw [src]
    exact old.input
  let answer : BitVec 1600 := π (chainPermInput s)
  have val : answer = orbit π (seedState k) (j+1) := congrArg π input
  have space : nonceChainDest j+200 ≤ 2^64 := by
    dsimp [nonceChainCount] at bound; unfold nonceChainDest nonceChainBase;omega
  have mem : (chainAdvance s j answer).mem = (writeBits s (BitVec.ofNat 64 (nonceChainDest j)) answer).mem :=
    (advance_mem s j answer).trans (congrArg (fun a => (writeBits s a answer).mem) frame.output)
  constructor
  · have addr : nonceChainSource (j+1) = nonceChainDest j := by
      unfold nonceChainSource nonceChainDest nonceChainBase;omega
    rw [read_buffer_memory_congr _ _ mem,addr,← val]
    have readAll : readBuffer (writeBits s (BitVec.ofNat 64 (nonceChainDest j)) answer)
        (nonceChainDest j) 200 = answer.extractLsb' 0 1600 :=
      read_written s (nonceChainDest j) answer 0 200 (by decide) (by decide)
    exact readAll.trans (extract_self answer)
  · intro i
    have length : i.val < 16777216 := i.isLt
    rw [read_buffer_memory_congr _ _ mem,write_bits_read_outside _ answer _ _ _ space (by omega)
      (Or.inl (by unfold nonceChainDest nonceChainBase;omega))]
    exact old.message i
  · intro i inside
    have length : i.val < 16777216 := i.isLt
    rw [read_buffer_memory_congr _ _ mem]
    by_cases earlier : i.val/11 < j
    · rw [write_bits_read_outside _ answer _ _ _ space (by unfold nonceChainBase;omega)
        (Or.inl (by unfold nonceChainDest;omega))]
      exact old.nonce i earlier
    · have thisBlock : i.val/11=j := by omega
      have addr : nonceChainBase+16*i.val = nonceChainDest j+16*(i.val%11) := by
        unfold nonceChainDest;omega
      rw [addr,read_written s _ answer (16*(i.val%11)) 16 (by omega) (by decide),val]
      unfold actualNonces
      change _ = (orbit π (seedState k) (i.val/11+1)).extractLsb' (128*(i.val%11)) 128
      rw [thisBlock,show 8*(16*(i.val%11))=128*(i.val%11) by omega]
      rfl
  · intro l g hl hg z
    have below := zeros_below_seed l g hl hg z
    rw [read_buffer_memory_congr _ _ mem,write_bits_read_outside _ answer _ _ _ space
      (by unfold nonceChainSource nonceChainBase at below;omega)
      (Or.inl (by unfold nonceChainSource nonceChainDest nonceChainBase at *;omega))]
    exact old.zeros l g hl hg z

def evalChain (π : Perm) (j : Nat) (s : MachineState) : Nat → MachineState
  | 0 => s
  | n+1 => evalChain π (j+1) (chainAdvance s j (π (chainPermInput s))) n

theorem chain_fixed_run (o : Oracle) (j n : Nat) (s : MachineState) :
    o.run (chainRun j s n) = pure (evalChain o.permutation j s n,n) := by
  induction n generalizing j s with
  | zero => exact oracle_run_pure o s
  | succ n ih =>
    rw [chainRun,oracle_run_public_bind,ih]
    simp [evalChain,Oracle.answer,Nat.add_comm] <;> rfl

theorem chain_memory_run (π : Perm) (k : Key) (m : Message) (j n : Nat) (s : MachineState)
    (space : j+n ≤ nonceChainCount) (frame : NonceChainFrame s j) (saved : Saved s)
    (old : ChainMemory π k m j s) :
    let last := evalChain π j s n
    ChainMemory π k m (j+n) last ∧ Saved last ∧ NonceChainFrame last (j+n) := by
  induction n generalizing j s with
  | zero => simpa [evalChain] using And.intro old (And.intro saved frame)
  | succ n ih =>
    have next := ih (j+1) _ (by omega)
      (chain_advance_frame s j _ frame) (advance_saved s j _ saved)
      (chain_step_memory π k m s j (by omega) frame old)
    simpa only [evalChain,show j+(n+1)=(j+1)+n by omega] using next

attribute [local irreducible] chainInitial seedSetup seedWritten nonceChainPC Submission.initialState evalChain chainRun

/-- An initial-state byte outside the message buffer is zero (the commit image has no data). -/
theorem initial_zero_byte (candidate : Submission) (abi : ABI candidate) (m : Message) (address : Nat)
    (outside : 4096+16777216*256 ≤ address) (bound : address < 2^64) :
    (candidate.initialState .commit m).getByte (BitVec.ofNat 64 address) = 0 := by
  have empty : (candidate.image .commit).data=[] := by rw [abi.code];unfold image;rfl
  rw [initial_input_byte candidate .commit m _ bound]
  have away : ¬ (candidate.layout.message ≤ address ∧
      address < candidate.layout.message+LENGTH*(LEAF_SIZE/8)) := by
    rw [abi.message];change ¬ (4096≤_ ∧ _<4096+16777216*256);omega
  simp only [inputByte,Submission.inputBuffers,List.find?_cons,messageBuffer,away,decide_false,List.find?_nil]
  split <;> simp [empty]

theorem initial_memory (o : Oracle) (candidate : Submission) (abi : ABI candidate) (m : Message) (k : Key) :
    ChainMemory o.permutation k m 0 (chainInitial (candidate.initialState .commit m) k) := by
  let init := candidate.initialState .commit m
  let a := nonceChainSource 0
  let seed := seedSetup init
  let seeded := writeBits seed (BitVec.ofNat 64 a) k
  let initial := chainInitial init k
  have mem : initial.mem = seeded.mem := by
    simpa only [seedWritten] using written_mem init k
  have head : readBuffer seeded a 24 = k := by
    simpa only [Nat.add_zero,Nat.mul_zero,extract_self] using read_written seed a k 0 24 (by decide) (by decide)
  have high : (readBuffer seeded (a+24) 176).toNat = 0 := by
    rw [show readBuffer seeded (a+24) 176 = readBuffer seed (a+24) 176 from
      write_bits_read_outside seed k a _ _ (by decide) (by decide) (Or.inr (by decide))]
    rw [read_buffer_memory_congr seed init (seed_mem init)]
    apply chain_read_zero
    intro j hj
    exact initial_zero_byte candidate abi m _ (by dsimp [a,nonceChainSource,nonceChainBase];omega)
      (by dsimp [a,nonceChainSource,nonceChainBase];omega)
  refine ⟨?_,?_,fun _ h => (Nat.not_lt_zero _ h).elim,?_⟩
  · rw [read_buffer_memory_congr _ _ mem]
    apply BitVec.eq_of_toNat_eq
    rw [chain_read_append seeded a 24 176 200 (a+24) rfl rfl,head,high,Nat.mul_zero,Nat.add_zero]
    exact (Nat.mod_eq_of_lt (lt_trans k.isLt (by decide : 2^192<2^1600))).symm
  · intro i
    have limit : i.val<16777216 := i.isLt
    rw [read_buffer_memory_congr _ _ mem,show seeded=writeBits seed (BitVec.ofNat 64 a) k from rfl,
      write_bits_read_outside seed k a _ 256 (by decide) (by omega)
        (Or.inl (by dsimp [a,nonceChainSource,nonceChainBase];omega)),read_buffer_memory_congr seed init (seed_mem init)]
    have value := read_serialized_slice init (m i) (4096+256*i.val) 0 256 (fun j hj => by
      simpa only [Nat.zero_add] using abi_message_byte candidate abi m i j hj)
    exact value.trans (extract_self _)
  · intro l g hl hg z
    have below := zeros_below_seed l g hl hg z
    have above := zeros_above_message l g hl z.val
    rw [read_buffer_memory_congr _ _ mem,show seeded=writeBits seed (BitVec.ofNat 64 a) k from rfl,
      write_bits_read_outside seed k a _ 8 (by decide) (by unfold nonceChainSource nonceChainBase at below;omega)
        (Or.inl (by dsimp [a];exact below)),
      read_buffer_memory_congr seed init (seed_mem init)]
    apply BitVec.eq_of_toNat_eq
    rw [chain_read_zero init _ 8 (fun j hj => initial_zero_byte candidate abi m _
      (by omega) (by unfold nonceChainSource nonceChainBase at below;omega))]
    rfl

def chainFinalReady (π : Perm) (initial : MachineState) (k : Key) :=
  chainFinish (evalChain π 0 (chainInitial initial k) nonceChainCount)

private theorem finish_mem (s : MachineState) : (chainFinish s).mem=s.mem := rfl

/-- The leaf-entry state after the generator: registers, message windows, chain salts, zeros. -/
theorem final_content (o : Oracle) (candidate : Submission) (abi : ABI candidate) (m : Message) (k : Key) :
    let ready := chainFinalReady o.permutation (candidate.initialState .commit m) k
    ReadyRegs ready ∧
    (∀ i : Index, window (memoryView ready) (leafStart i.val+5) = messageWords m i) ∧
    (∀ i : Index, window (memoryView ready) (Leaves.leafSalt i.val) = saltWords (actualNonces o.permutation k i)) ∧
    (∀ k g, k ≤ 10 → g < pentaCount (k+1) → ∀ z : Fin 5,
      memoryView ready (pentaGroupWord k g+z.val)=0) := by
  let init := candidate.initialState .commit m
  let last := evalChain o.permutation 0 (chainInitial init k) nonceChainCount
  have started := initial_frame init (abi_entry candidate abi m) k
  have contents : ChainMemory o.permutation k m nonceChainCount last ∧ Saved last ∧ NonceChainFrame last nonceChainCount :=
    chain_memory_run o.permutation k m 0 nonceChainCount _ (by decide) started.1 started.2
      (initial_memory o candidate abi m k)
  refine ⟨finish_regs last contents.2.2 contents.2.1,?_,?_,?_⟩
  · intro i; funext h
    change memoryView (chainFinish last) (leafStart i.val+5+h.val)=_
    rw [←read_word,read_buffer_memory_congr _ _ (finish_mem last)]
    have part := read_buffer_slice last (4096+256*i.val) 256 (8*h.val) 8 (by have := h.isLt;omega)
    rw [contents.1.message i] at part
    rw [show 8*(leafStart i.val+5+h.val)=4096+256*i.val+8*h.val by unfold leafStart;omega,←part]
    change (m i).extractLsb' (8*(8*h.val)) 64 = (m i).extractLsb' (64*h.val) 64
    rw [←Nat.mul_assoc]
  · intro i; funext h
    change memoryView (chainFinish last) (Leaves.leafSalt i.val+h.val)=_
    rw [←read_word,read_buffer_memory_congr _ _ (finish_mem last)]
    have part := read_buffer_slice last (nonceChainBase+16*i.val) 16 (8*h.val) 8 (by have := h.isLt;omega)
    rw [contents.1.nonce i (by have : i.val<16777216 := i.isLt;change i.val/11<1525248;omega)] at part
    rw [show 8*(Leaves.leafSalt i.val+h.val)=nonceChainBase+16*i.val+8*h.val by
      unfold Leaves.leafSalt saltWord nonceChainBase;omega,←part]
    change (actualNonces o.permutation k i).extractLsb' (8*(8*h.val)) 64 = _
    rw [←Nat.mul_assoc]
    rfl
  · intro l g hl hg z
    change memoryView (chainFinish last) (pentaGroupWord l g+z.val)=0
    rw [←read_word,read_buffer_memory_congr _ _ (finish_mem last)]
    exact contents.1.zeros l g hl hg z

end TwoPermutationPrototype.Quad.Commit.Chain
