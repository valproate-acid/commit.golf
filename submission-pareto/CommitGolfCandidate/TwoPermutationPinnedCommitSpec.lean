import CommitGolfCandidate.TwoPermutationPinnedWindows
import CommitGolfCandidate.TaggedPinnedModel
import CommitGolfCandidate.TwoPermutationHeapInvariant

namespace TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
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

theorem empty_pinned_leaf_prefix (oracle : Oracle) (s : MachineState) : PinnedLeafPrefix oracle (memoryView s) s 0 :=
  ⟨fun _ impossible => False.elim (by omega),fun _ _ _ => rfl, fun _ _ => rfl⟩


theorem pinned_parent_content_of_leaf_prefix (oracle : Oracle) (before : Memory) (leaves : MachineState)
    (heap : Nat → BitVec 256) (salts : Index → BitVec 128) (inv : PinnedLeafPrefix oracle before leaves (2^24))
    (leaf : ∀ i : Index, heap (LENGTH+i.val)=outputDigest (pinnedFinalReply oracle before i.val))
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

end TwoPermutationPrototype.RV64.PackedLeaves
