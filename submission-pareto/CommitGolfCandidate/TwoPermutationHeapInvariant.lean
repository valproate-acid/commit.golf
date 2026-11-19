import CommitGolfCandidate.TwoPermutationCommitRun

/-! During the descending parent pass, all higher complete nodes agree with a
fixed reference tree. Every nonce survives the full pass and root copy. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (read_buffer_slice read_buffer_memory_congr checkEvaluation check_evaluation_bind
  check_evaluation_pure check_evaluation_public_bind write_bits_read_outside write_bits_digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] writeBits checkEvaluation leavesTrace parentsTrace parentBatches readBuffer
  finalReply fullLeafDigests readyState fullParents parentBatch

theorem aligned_buffer_eq (state : MachineState) (start bytes : Nat) (aligned : bytes%8=0)
    (expected : BitVec (8*bytes))
    (words : ∀ k < bytes/8, memoryView state (start+k)=expected.extractLsb' (64*k) 64) :
    readBuffer state (8*start) bytes=expected := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  let k := bit/64
  have bound : k<bytes/8 := by dsimp [k];omega
  have chunk := read_buffer_slice state (8*start) bytes (8*k) 8 (by omega)
  rw [show 8*start+8*k=8*(start+k) by omega,read_word,words k bound] at chunk
  have bits := congrArg (fun w : BitVec 64 => w.getLsbD (bit%64)) chunk
  have numeric : 64*k+bit%64=bit := by dsimp [k];omega
  simpa only [←Nat.mul_assoc, Nat.reduceMul, BitVec.getLsbD_extractLsb',show bit%64<64 by omega,
    decide_true,Bool.true_and,numeric] using bits

def nonceBuffer (state : MachineState) (i : Nat) := readBuffer state (8*leafSalt i) 16

structure ParentContent (s : MachineState) (heap : Nat → BitVec 256) (salts : Index → BitVec 128) (remaining : Nat) : Prop where
  nodes : ∀ n, remaining<n → n<2*LENGTH → nodeDigest s n=heap n
  nonces : ∀ i : Index, nonceBuffer s i.val=salts i

theorem low_digest_word (reply : BitVec 1600) (i : Fin 4) :
    lowDigest (replyWords reply) i = (outputDigest reply).extractLsb' (64*i.val) 64 := by
  exact (BitVec.extractLsb'_extractLsb'_of_le (x := reply) (start := 64*i.val) (len := 64) (len' := 256) (by have := i.isLt;omega)).symm

theorem parent_content_of_leaf_prefix (oracle : Oracle) (before : Memory) (leaves : MachineState)
    (heap : Nat → BitVec 256) (salts : Index → BitVec 128) (inv : LeafPrefix oracle before leaves (2^24))
    (leaf : ∀ i : Index, heap (LENGTH+i.val)=outputDigest (finalReply oracle before i.val))
    (original_salts : ∀ i : Index, (window before (leafSalt i.val) : Words 2)=saltWords (salts i)) :
    ParentContent (parentSetup leaves 5) heap salts (2^24-1) := by
  constructor
  · intro n lo hi
    have valid : n-LENGTH<LENGTH := by omega
    let i : Index := ⟨n-LENGTH,valid⟩
    have idx : n=LENGTH+i.val := by change n=LENGTH+(n-LENGTH);change 2^24-1<n at lo; have e : LENGTH=2^24:=rfl;omega
    rw [idx,leaf i]
    unfold nodeDigest
    rw [read_buffer_memory_congr _ leaves (show (parentSetup leaves 5).mem=leaves.mem from rfl)]
    have addr : treeWord (LENGTH+i.val)=leafDest i.val := by change 516+32*2^24+4*(2^24+i.val)=_;unfold leafDest;omega
    rw [addr]
    apply aligned_buffer_eq leaves _ 32 (by decide)
    intro k hk
    have value := congrFun (inv.digests i.val i.isLt) (⟨k,hk⟩ : Fin 4)
    change memoryView leaves (leafDest i.val+k)=_ at value
    rw [value]
    exact low_digest_word _ (⟨k,hk⟩ : Fin 4)
  · intro i
    unfold nonceBuffer
    rw [read_buffer_memory_congr _ leaves (show (parentSetup leaves 5).mem=leaves.mem from rfl)]
    apply aligned_buffer_eq leaves _ 16 (by decide)
    intro k hk
    have v := (inv.salts i.val i.isLt).trans (original_salts i)
    exact congrFun v (⟨k,hk⟩ : Fin 2)


theorem initialize_parent_content (candidate : Submission) (abi : CommitABI candidate) (oracle : Oracle)
    (msg : Message) (packed : BitVec (128*LENGTH)) (heap : Nat → BitVec 256)
    (leaf : ∀ i : Index, heap (LENGTH+i.val)=fullLeafDigests (BiPermutation.equiv Block oracle.permutation)
      msg (CommitGolfCandidate.splitBlocks 128 LENGTH packed) i) :
    let s := candidate.initialState .commit msg
    let salts := CommitGolfCandidate.splitBlocks 128 LENGTH packed
    let leaves := (checkEvaluation oracle (leavesTrace (2^20) 0 (readyState s packed))).1
    ParentContent (parentSetup leaves 5) heap salts (2^24-1) := by
  let s := candidate.initialState .commit msg
  let ready := readyState s packed
  obtain ⟨g,stop,_⟩ := post_random_regs s (abi_commit_entry candidate abi msg) packed
  exact parent_content_of_leaf_prefix oracle (memoryView ready) _ heap _ (production_leaf_outputs oracle ready g stop)
    (fun i => (leaf i).trans (ready_leaf_digest candidate abi oracle msg packed i).symm)
    (ready_salts s packed)

end TwoPermutationPrototype.RV64
