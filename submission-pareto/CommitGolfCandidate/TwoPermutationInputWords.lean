import CommitGolfCandidate.TwoPermutationCommitSetup
import CommitGolfCandidate.TwoPermutationHidingEager

/-! The checked private draw and ABI loader supply the exact public 2048-bit
message and private 128-bit nonce used by each canonical pair of permutation rows. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (read_buffer_memory_congr read_buffer_slice read_digest_word read_serialized_slice
  splitBlocks initial_input_byte inputByte write_bits_byte write_bits_read_outside)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] writeBits

structure CommitABI (s : Submission) : Prop where
  code : s.image .commit = commitImage
  message : s.layout.message = 4096
  output : s.layout.commitment = 4294971392
  trapdoor : s.layout.trapdoor = 4294971424
  size : s.sizes.trapdoor = 96*LENGTH
  fuel : 305266716 ≤ s.steps .commit

theorem abi_commit_entry (s : Submission) (abi : CommitABI s) (msg : Message) :
    CommitEntry (s.initialState .commit msg) := by
  refine ⟨rfl,?_,?_,?_⟩
  · change BitVec.ofNat 64 s.layout.message=_;rw [abi.message];rfl
  · change BitVec.ofNat 64 s.layout.commitment=_;rw [abi.output];rfl
  · change BitVec.ofNat 64 s.layout.trapdoor=_;rw [abi.trapdoor];rfl

theorem abi_message_byte (s : Submission) (abi : CommitABI s) (msg : Message) (i : Index) (j : Nat) (hj : j<256) :
    (s.initialState .commit msg).getByte (BitVec.ofNat 64 (4096+256*i.val+j)) = (msg i).extractLsb' (8*j) 8 := by
  have n : i.val<2^24 := i.isLt
  rw [initial_input_byte s .commit msg _ (by omega)]
  have selected : 4096 ≤ 4096+256*i.val+j ∧ 4096+256*i.val+j < 4096+LENGTH*(LEAF_SIZE/8) := by
    change _ ∧ _ < 4096+16777216*256;omega
  simp only [inputByte,Submission.inputBuffers,List.find?_cons,messageBuffer,abi.message,
    selected,and_self,decide_true]
  have quotient : (4096+256*i.val+j-4096)/(LEAF_SIZE/8)=i.val := by change _/256=_;omega
  have remainder : (4096+256*i.val+j-4096)%(LEAF_SIZE/8)=j := by change _%256=_;omega
  simp only [quotient,remainder,i.isLt,dite_true]

theorem read_word (s : MachineState) (w : Nat) : readBuffer s (8*w) 8=memoryView s w := by
  have slice := read_buffer_slice s (8*w) 32 0 8 (by decide)
  have extract := read_digest_word s (8*w) 0 (by omega) (by decide)
  simpa only [Nat.mul_zero,Nat.add_zero,memoryView,wordAddress] using slice.symm.trans extract

theorem ready_memory (s : MachineState) {bits : Nat} (packed : BitVec bits) :
    (readyState s packed).mem = (writeBits s (wordAddress (leafSalt 0)) packed).mem :=
  CommitGolfCandidate.write_bits_memory_congr (initialPrefix s 11) s _ packed rfl

theorem ready_messages (candidate : Submission) (abi : CommitABI candidate) (msg : Message)
    (packed : BitVec (128*LENGTH)) (i : Index) :
    window (memoryView (readyState (candidate.initialState .commit msg) packed)) (leafStart i.val+5) =
      messageWords msg i := by
  let init := candidate.initialState .commit msg
  let ready := readyState init packed
  funext k
  change memoryView ready (leafStart i.val+5+k.val)=_
  rw [←read_word,read_buffer_memory_congr _ _ (ready_memory init packed)]
  have hi : i.val<2^24 := i.isLt
  have hk := k.isLt
  have sep := write_bits_read_outside init packed (8*leafSalt 0) (8*(leafStart i.val+5+k.val)) 8
    (by change 5637148704+268435456≤2^64;decide) (by unfold leafStart;omega)
    (by left;unfold leafStart leafSalt;omega)
  rw [wordAddress,sep]
  have slice := read_serialized_slice init (msg i) (8*(leafStart i.val+5+k.val)) (8*k.val) 8 (by
    intro j hj
    rw [show 8*(leafStart i.val+5+k.val)+j=4096+256*i.val+(8*k.val+j) by unfold leafStart;omega]
    exact abi_message_byte candidate abi msg i (8*k.val+j) (by omega))
  simpa only [messageWords,←Nat.mul_assoc] using slice

theorem ready_salts (s : MachineState) (packed : BitVec (128*LENGTH)) (i : Index) :
    window (memoryView (readyState s packed)) (leafSalt i.val) = saltWords (splitBlocks 128 LENGTH packed i) := by
  funext k
  change memoryView (readyState s packed) (leafSalt i.val+k.val)=_
  rw [←read_word,read_buffer_memory_congr _ _ (ready_memory s packed)]
  let offset := 16*i.val+8*k.val
  have iBound : i.val<16777216 := i.isLt
  have kBound := k.isLt
  have bound : (128*LENGTH+7)/8 ≤ 2^64 := by decide
  have slice := read_serialized_slice (writeBits s (wordAddress (leafSalt 0)) packed) packed
    (8*(leafSalt i.val+k.val)) offset 8 (by
      intro j hj
      have inside : offset+j < (128*LENGTH+7)/8 := by change offset+j < 268435456;dsimp [offset];omega
      have byte := write_bits_byte s (wordAddress (leafSalt 0)) packed (offset+j) inside bound
      simpa only [wordAddress,←BitVec.ofNat_add,
        show 8*leafSalt 0+(offset+j)=8*(leafSalt i.val+k.val)+j by dsimp [offset,leafSalt];omega] using byte)
  rw [slice]
  apply BitVec.eq_of_getLsbD_eq
  intro bit within
  have small : 64*k.val+bit < 128 := by omega
  have eq : 8*offset+bit=128*i.val+(64*k.val+bit) := by dsimp [offset];omega
  simp [saltWords,splitBlocks,within,small,eq,←Nat.add_assoc]

theorem ready_leaf_digest (candidate : Submission) (abi : CommitABI candidate) (oracle : Oracle)
    (msg : Message) (packed : BitVec (128*LENGTH)) (i : Index) :
    outputDigest (finalReply oracle (memoryView (readyState (candidate.initialState .commit msg) packed)) i.val) =
      fullLeafDigests (BiPermutation.equiv Block oracle.permutation) msg (splitBlocks 128 LENGTH packed) i := by
  unfold finalReply
  rw [ready_messages candidate abi msg packed i,ready_salts _ packed i]
  rfl

end TwoPermutationPrototype.RV64
