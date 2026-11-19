import CommitGolfCandidate.QuadCommitSetup
import CommitGolfCandidate.QuadCommitLeafMeaning
import CommitGolfCandidate.TwoPermutationPackedLeafInput

namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64
open CommitGolfCandidate (read_buffer_memory_congr read_serialized_slice splitBlocks initial_input_byte inputByte write_bits_byte write_bits_read_outside)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] writeBits image leafCode levelsCode

structure ABI (s : Submission) : Prop where
  code : s.image .commit=image
  message : s.layout.message=4096
  output : s.layout.commitment=4294971392
  heap : s.layout.trapdoor=4294971424

theorem abi (opening checker : Image) : ABI (submission opening checker) := ⟨rfl,rfl,rfl,rfl⟩

theorem abi_entry (s : Submission) (abi : ABI s) (msg : Message) : CommitEntry (s.initialState .commit msg) := by
  refine ⟨rfl,?_,?_,?_⟩
  · change BitVec.ofNat 64 s.layout.message=_;rw [abi.message];rfl
  · change BitVec.ofNat 64 s.layout.commitment=_;rw [abi.output];rfl
  · change BitVec.ofNat 64 s.layout.trapdoor=_;rw [abi.heap];rfl

theorem abi_message_byte (s : Submission) (abi : ABI s) (msg : Message) (i : Index) (j : Nat) (hj : j<256) :
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

/-- The pinned leaf digest read from any memory holding the message and salt windows. -/
theorem windows_pinned_leaf (oracle : Oracle) (before : Memory) (msg : Message) (salts : CompleteSaltTape)
    (messages : ∀ i : Index, window before (leafStart i.val+5) = messageWords msg i)
    (nonces : ∀ i : Index, window before (Leaves.leafSalt i.val) = saltWords (salts i)) (i : Index) :
    outputDigest (Leaves.pinnedFinalReply oracle before i.val) = quadPublicLeaves oracle msg salts i := by
  rw [Leaves.pinnedFinalReply,messages i,nonces i]
  simp only [quadPublicLeaves,pinnedFullLeafDigests,pinnedLeafDigest,pinnedFirstRow,pinnedSecondRow,Leaves.pinned_typed_words]
  rfl

end TwoPermutationPrototype.Quad.Commit
