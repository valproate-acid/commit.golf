import CommitGolfCandidate.TwoPermutationParentBatchesContent
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (read_buffer_slice read_buffer_memory_congr checkEvaluation check_evaluation_bind
  check_evaluation_pure check_evaluation_public_bind write_bits_read_outside write_bits_digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] writeBits checkEvaluation leavesTrace parentsTrace parentBatches readBuffer
  finalReply fullLeafDigests readyState fullParents parentBatch

theorem all_parents_content (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128)
    (tree : ∀ j, 0<j → j<LENGTH → heap j=oracle.compression (heap (2*j+1) ++ heap (2*j)))
    (prior : ParentContent s heap salts (2^24-1)) :
    ParentContent (checkEvaluation oracle (fullParents s)).1 heap salts 0 := by
  have compose {p : OracleComp World MachineState} {f : MachineState → OracleComp World MachineState}
      (ok : ParentContent (checkEvaluation oracle (f (checkEvaluation oracle p).1)).1 heap salts 0) :
      ParentContent (checkEvaluation oracle (p >>= f)).1 heap salts 0 := by
    rw [check_evaluation_bind];exact ok
  unfold fullParents
  exact compose (p := parentsTrace (128*131071) 127 s) (f := parentBatches 131071)
    (parent_batches_content oracle _ heap salts 131071 (by decide) tree
      (parent_sequence_content oracle s heap salts (128*131071) 127 (by decide) tree prior))

end TwoPermutationPrototype.RV64
