import CommitGolfCandidate.TwoPermutationParentContent
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (read_buffer_slice read_buffer_memory_congr checkEvaluation check_evaluation_bind
  check_evaluation_pure check_evaluation_public_bind write_bits_read_outside write_bits_digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] writeBits checkEvaluation leavesTrace parentsTrace parentBatches readBuffer
  finalReply fullLeafDigests readyState fullParents parentBatch

theorem parent_sequence_content (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128) (rem cnt : Nat) (inside : rem+cnt<LENGTH)
    (tree : ∀ j, 0<j → j<LENGTH → heap j=oracle.compression (heap (2*j+1) ++ heap (2*j)))
    (prior : ParentContent s heap salts (rem+cnt)) :
    ParentContent (checkEvaluation oracle (parentsTrace rem cnt s)).1 heap salts rem := by
  induction cnt generalizing s with
  | zero => simpa only [parentsTrace,check_evaluation_pure,Nat.add_zero] using prior
  | succ k ih =>
    rw [parentsTrace,check_evaluation_bind]
    have query : checkEvaluation oracle (liftM (World.query (.inr (.inl (parentInput s (rem+(k+1)))))) : OracleComp World (BitVec 256)) = (oracle.compression (parentInput s (rem+(k+1))),1) := CommitGolfCandidate.check_evaluation_public oracle _
    rw [query]
    apply ih _ (by omega)
    apply parent_content_step oracle _ _ _ (rem+k) (by omega) tree
    exact prior

end TwoPermutationPrototype.RV64
