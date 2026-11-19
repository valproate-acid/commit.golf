import CommitGolfCandidate.TwoPermutationPinnedWindows
import CommitGolfCandidate.QuadCommitLeafProduction
import CommitGolfCandidate.TaggedPinnedModel
import CommitGolfCandidate.TwoPermutationHeapInvariant

namespace TwoPermutationPrototype.Quad.Commit.Leaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolfCandidate (read_buffer_memory_congr)
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000

def pinnedFinalReply (oracle : Oracle) (mem : Memory) (i : Nat) : BitVec 1600 :=
  let msg := window mem (leafStart i+5)
  let salt := window mem (leafSalt i)
  let a := oracle.permutation (packBuffer (rawPrefix msg))
  oracle.permutation (packBuffer (pinnedWords (secondTag i) salt (replyWords a) msg))

structure PinnedLeafPrefix (oracle : Oracle) (before : Memory) (s : MachineState) (count : Nat) : Prop where
  digests : ∀ i < count, (window (memoryView s) (leafDest i) : Words 4) =
    lowDigest (replyWords (pinnedFinalReply oracle before i))
  messages : ∀ i, count ≤ i → i < 2^24 → (window (memoryView s) (leafStart i+5) : Words 32) =
    window before (leafStart i+5)
  salts : ∀ i < 2^24, (window (memoryView s) (leafSalt i) : Words 2) = window before (leafSalt i)

  zeros : ∀ g < 3355444, (window (memoryView s) (groupWord g) : Words 5) = window before (groupWord g)
  upper : ∀ k g, 0 < k → k ≤ 10 → g < pentaCount (k+1) →
    (window (memoryView s) (pentaGroupWord k g) : Words 5) = window before (pentaGroupWord k g)

theorem empty_pinned_leaf_prefix (oracle : Oracle) (s : MachineState) : PinnedLeafPrefix oracle (memoryView s) s 0 :=
  ⟨fun _ impossible => False.elim (by omega),fun _ _ _ => rfl, fun _ _ => rfl,fun _ _ => rfl,fun _ _ _ _ _ => rfl⟩



end TwoPermutationPrototype.Quad.Commit.Leaves
