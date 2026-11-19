import CommitGolfCandidate.TwoPermutationHeapInvariant
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (read_buffer_slice read_buffer_memory_congr checkEvaluation check_evaluation_bind
  check_evaluation_pure check_evaluation_public_bind write_bits_read_outside write_bits_digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] writeBits checkEvaluation leavesTrace parentsTrace parentBatches readBuffer
  finalReply fullLeafDigests readyState fullParents parentBatch

theorem parent_content_step (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128) (n : Nat) (inside : n+1<LENGTH)
    (tree : ∀ j, 0<j → j<LENGTH → heap j=oracle.compression (heap (2*j+1) ++ heap (2*j)))
    (prior : ParentContent s heap salts (n+1)) :
    ParentContent (parentAfter s (n+1) (oracle.compression (parentInput s (n+1)))) heap salts n := by
  let cur := n+1
  let reply : BitVec 256 := oracle.compression (parentInput s cur)
  have intBound : n+1<2^24 := inside
  have writeRange : 8*treeWord cur+32 ≤ 2^64 := by dsimp [treeWord,cur];omega
  constructor
  · intro j larger small
    unfold nodeDigest
    rw [read_buffer_memory_congr _ (parentWritten s cur reply)
      (show (parentAfter s cur reply).mem=(parentWritten s cur reply).mem from rfl)]
    by_cases last : j=cur
    · subst j
      have written := write_bits_digest (bits := 256) s (8*treeWord cur) 0 reply (by decide) (by decide)
      simp only [Nat.add_zero,Nat.mul_zero,BitVec.extractLsb'_eq_self] at written
      apply written.trans
      unfold reply
      rw [child_pair,prior.nodes (2*cur+1) (by dsimp [cur];omega) (by dsimp [cur];omega),
        prior.nodes (2*cur) (by dsimp [cur];omega) (by dsimp [cur];omega),tree cur (by dsimp [cur];omega) inside]
    · have diff : cur<j := by dsimp [cur] at *;omega
      apply Eq.trans _ (prior.nodes j diff small)
      apply write_bits_read_outside (bits := 256) s reply (8*treeWord cur) (8*treeWord j) 32 writeRange
      · change j<2*2^24 at small;unfold treeWord;omega
      · right;unfold treeWord;omega
  · intro i
    apply Eq.trans _ (prior.nonces i)
    unfold nonceBuffer
    rw [read_buffer_memory_congr _ (parentWritten s cur reply)
      (show (parentAfter s cur reply).mem=(parentWritten s cur reply).mem from rfl)]
    apply write_bits_read_outside (bits := 256) s reply (8*treeWord cur) (8*leafSalt i.val) 16 writeRange
    · have small : i.val<2^24 := i.isLt;unfold leafSalt;omega
    · right;dsimp [treeWord,leafSalt,cur];omega

end TwoPermutationPrototype.RV64
