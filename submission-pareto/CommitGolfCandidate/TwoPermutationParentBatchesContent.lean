import CommitGolfCandidate.TwoPermutationParentContentLoop
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (read_buffer_slice read_buffer_memory_congr checkEvaluation check_evaluation_bind
  check_evaluation_pure check_evaluation_public_bind write_bits_read_outside write_bits_digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] writeBits checkEvaluation leavesTrace parentsTrace parentBatches readBuffer
  finalReply fullLeafDigests readyState fullParents parentBatch

theorem content_bound (oracle : Oracle) (p : OracleComp World MachineState) (f : MachineState → OracleComp World MachineState)
    (heap : Nat → BitVec 256) (salts : Index → BitVec 128) (count : Nat)
    (ok : ParentContent (checkEvaluation oracle (f (checkEvaluation oracle p).1)).1 heap salts count) :
    ParentContent (checkEvaluation oracle (p >>= f)).1 heap salts count := by rw [check_evaluation_bind];exact ok

theorem content_setpc (s : MachineState) (pc : Word) (heap : Nat → BitVec 256) (salts : Index → BitVec 128)
    (count : Nat) (prev : ParentContent s heap salts count) : ParentContent (s.setPC pc) heap salts count := by
  constructor
  · intro n lo hi
    rw [nodeDigest,read_buffer_memory_congr _ s (show (s.setPC pc).mem=s.mem from rfl)]
    exact prev.nodes n lo hi
  · intro i
    rw [nonceBuffer,read_buffer_memory_congr _ s (show (s.setPC pc).mem=s.mem from rfl)]
    exact prev.nonces i

theorem content_latched (oracle : Oracle) (p : OracleComp World MachineState) (pc : Word)
    (heap : Nat → BitVec 256) (salts : Index → BitVec 128) (count : Nat)
    (ok : ParentContent (checkEvaluation oracle p).1 heap salts count) :
    ParentContent (checkEvaluation oracle (p >>= fun s => pure (s.setPC pc))).1 heap salts count := by
  rw [check_evaluation_bind];simp only [check_evaluation_pure]
  exact content_setpc _ _ _ _ _ ok

theorem parent_batches_content (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128) (groups : Nat) (inside : 128*groups<LENGTH)
    (tree : ∀ j, 0<j → j<LENGTH → heap j=oracle.compression (heap (2*j+1) ++ heap (2*j)))
    (prior : ParentContent s heap salts (128*groups)) :
    ParentContent (checkEvaluation oracle (parentBatches groups s)).1 heap salts 0 := by
  induction groups generalizing s with
  | zero => simpa only [parentBatches,check_evaluation_pure,Nat.mul_zero] using prior
  | succ k ih =>
    rw [Nat.mul_succ] at inside prior
    have body := parent_sequence_content oracle s heap salts (128*k) 128 inside tree prior
    have step := content_latched oracle (parentsTrace (128*k) 128 s) (parentNextPC (128*k)) heap salts (128*k) body
    unfold parentBatches
    apply content_bound oracle (parentBatch (128*k) s) (parentBatches k) heap salts 0
    apply ih _ (by omega)
    unfold parentBatch
    exact step

end TwoPermutationPrototype.RV64
