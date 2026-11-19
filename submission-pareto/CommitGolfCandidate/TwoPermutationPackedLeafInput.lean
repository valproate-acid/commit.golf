import CommitGolfCandidate.TwoPermutationPackedMeaning

namespace TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
open CommitGolfCandidate (initial_input_byte inputByte read_buffer_memory_congr read_serialized_slice write_bits_read_outside)
theorem wide_message_byte (s : Submission) (messageBase : s.layout.message=4096) (msg : Message) (i : Index) (j : Nat) (hj : j<256) :
    (s.initialState .commit msg).getByte (BitVec.ofNat 64 (4096+256*i.val+j)) = (msg i).extractLsb' (8*j) 8 := by
  have n : i.val<2^24 := i.isLt
  rw [initial_input_byte s .commit msg _ (by omega)]
  have selected : 4096 ≤ 4096+256*i.val+j ∧ 4096+256*i.val+j < 4096+LENGTH*(LEAF_SIZE/8) := by
    change _ ∧ _ < 4096+16777216*256;omega
  simp only [inputByte,Submission.inputBuffers,List.find?_cons,messageBuffer,messageBase,
    selected,and_self,decide_true]
  have quotient : (4096+256*i.val+j-4096)/(LEAF_SIZE/8)=i.val := by change _/256=_;omega
  have remainder : (4096+256*i.val+j-4096)%(LEAF_SIZE/8)=j := by change _%256=_;omega
  simp only [quotient,remainder,i.isLt,dite_true]

theorem wide_ready_messages (candidate : Submission) (messageBase : candidate.layout.message=4096) (msg : Message)
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
    exact wide_message_byte candidate messageBase msg i (8*k.val+j) (by omega))
  simpa only [messageWords,←Nat.mul_assoc] using slice


end TwoPermutationPrototype.RV64.PackedLeaves
