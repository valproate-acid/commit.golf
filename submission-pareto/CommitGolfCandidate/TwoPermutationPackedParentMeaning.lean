import CommitGolfCandidate.TwoPermutationPackedParentMask
import CommitGolfCandidate.TwoPermutationPackedParentControl
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (read_buffer_slice read_buffer_memory_congr checkEvaluation check_evaluation_bind
  check_evaluation_pure check_evaluation_public_bind write_bits_read_outside write_bits_digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] writeBits checkEvaluation leavesTrace parentsTrace parentBatches readBuffer
  finalReply fullLeafDigests readyState fullParents parentBatch

theorem packed_parent_content_step (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128) (n : Nat) (inside : n+1<LENGTH)
    (tree : ∀ j, 0<j → j<LENGTH → heap j=projectReply (oracle.compression (heap (2*j+1) ++ heap (2*j))))
    (prior : ParentContent s heap salts (n+1)) (regs : ParentRegs s (n+1)) :
    ParentContent (packedParentAfter s (n+1) (oracle.compression (parentInput s (n+1)))) heap salts n := by
  let cur := n+1
  let raw : BitVec 256 := oracle.compression (parentInput s cur)
  let reply := projectReply raw
  have memory : (packedParentAfter s cur raw).mem=(parentWritten s cur reply).mem :=
    packed_parent_memory s cur raw regs inside
  have intBound : n+1<2^24 := inside
  have writeRange : 8*treeWord cur+32 ≤ 2^64 := by dsimp [treeWord,cur];omega
  constructor
  · intro j larger small
    unfold nodeDigest
    rw [read_buffer_memory_congr _ (parentWritten s cur reply)
      memory]
    by_cases last : j=cur
    · subst j
      have written := write_bits_digest (bits := 256) s (8*treeWord cur) 0 reply (by decide) (by decide)
      simp only [Nat.add_zero,Nat.mul_zero,BitVec.extractLsb'_eq_self] at written
      apply written.trans
      unfold reply raw
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
      memory]
    apply write_bits_read_outside (bits := 256) s reply (8*treeWord cur) (8*leafSalt i.val) 16 writeRange
    · have small : i.val<2^24 := i.isLt;unfold leafSalt;omega
    · right;dsimp [treeWord,leafSalt,cur];omega

theorem packed_sequence_semantics (oracle : Oracle) (state : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128) (remaining count : Nat) (inside : remaining+count<LENGTH)
    (tree : ∀ node, 0<node → node<LENGTH →
      heap node=projectReply (oracle.compression (heap (2*node+1) ++ heap (2*node))))
    (prior : ParentContent state heap salts (remaining+count))
    (regs : ParentRegs state (remaining+count)) :
    let result := (checkEvaluation oracle (packedParentsTrace remaining count state)).1
    ParentContent result heap salts remaining ∧ ParentRegs result remaining := by
  induction count generalizing state with
  | zero =>
    simpa only [packedParentsTrace,check_evaluation_pure,Nat.add_zero] using And.intro prior regs
  | succ count ih =>
    rw [packedParentsTrace,check_evaluation_bind]
    have evaluated : checkEvaluation oracle (liftM
        (World.query (.inr (.inl (parentInput state (remaining+(count+1)))))) : OracleComp World (BitVec 256)) =
          (oracle.compression (parentInput state (remaining+(count+1))),1) :=
      CommitGolfCandidate.check_evaluation_public oracle _
    rw [evaluated]
    apply ih _ (by omega)
    · exact packed_parent_content_step oracle state heap salts (remaining+count) (by omega) tree prior regs
    · exact packed_next_parent_regs state (remaining+count) _ regs

theorem packed_parent_content (oracle : Oracle) (base : Word) (span groups : Nat)
    (state : MachineState) (heap : Nat → BitVec 256) (salts : Index → BitVec 128)
    (inside : span*groups < LENGTH)
    (tree : ∀ node, 0 < node → node < LENGTH →
      heap node=projectReply (oracle.compression (heap (2*node+1) ++ heap (2*node))))
    (prior : ParentContent state heap salts (span*groups)) (regs : ParentRegs state (span*groups)) :
    ParentContent (checkEvaluation oracle (packedParentGroups base span groups state)).1 heap salts 0 := by
  induction groups generalizing state with
  | zero => simpa only [packedParentGroups,check_evaluation_pure,Nat.mul_zero] using prior
  | succ groups ih =>
    rw [Nat.mul_succ] at inside prior regs
    have body := packed_sequence_semantics oracle state heap salts (span*groups) span inside tree prior regs
    rw [packedParentGroups,check_evaluation_bind]
    apply ih _ (by omega)
    · exact content_setpc _ _ heap salts (span*groups) body.1
    · exact ⟨body.2.source,body.2.target,body.2.selector,body.2.size,body.2.primitive,body.2.heap⟩

theorem counted_packed_parents (oracle : Oracle) (state : MachineState) (remaining count : Nat) :
    RunPublic oracle (packedParentsTrace remaining count state) count := by
  induction count generalizing state with
  | zero => exact run_pure_public oracle state
  | succ count ih =>
    rw [packedParentsTrace]
    simpa only [Nat.add_comm 1 count] using
      (run_bind_public oracle (liftM (World.query (.inr (.inl (parentInput state (remaining+(count+1)))))) :
        OracleComp World (BitVec 256))
        (fun answer => packedParentsTrace remaining count (packedParentAfter state (remaining+(count+1)) answer))
        1 count (run_query_public ..) (fun _ => ih _))

theorem counted_packed_groups (oracle : Oracle) (base : Word) (span groups : Nat)
    (state : MachineState) :
    RunPublic oracle (packedParentGroups base span groups state) (span*groups) := by
  induction groups generalizing state with
  | zero => exact run_pure_public oracle state
  | succ groups ih =>
    rw [packedParentGroups, show span*(groups+1)=span+span*groups by rw [Nat.mul_succ,Nat.add_comm]]
    exact run_bind_public oracle _ _ span (span*groups) (counted_packed_parents ..) (fun out => ih _)

end TwoPermutationPrototype.RV64
