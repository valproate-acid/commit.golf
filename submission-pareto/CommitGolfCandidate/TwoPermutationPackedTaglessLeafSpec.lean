import CommitGolfCandidate.TwoPermutationTaglessBinding
import CommitGolfCandidate.TwoPermutationHeapInvariant

namespace TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (read_buffer_memory_congr)
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000

/-- With the store at `start+12` removed, all thirteen remaining first-reply words reach the second call. -/
theorem tagless_second_window (mem : Memory) (start index : Nat) (nonce : Words 2) (reply : Words 25) :
    window (writeWindow (writeWindow mem start (header index nonce)) start reply) (start+12) =
      taglessSecondInput reply (window mem (start+5)) := by
  funext i
  by_cases inReply : i.val < 13
  · have inside : start ≤ start+12+i.val ∧ start+12+i.val < start+25 := by omega
    have offset : start+12+i.val-start=i.val+12 := by omega
    simp [window,writeWindow,taglessSecondInput,inReply,inside,offset]
  · have afterReply : ¬(start≤start+12+i.val ∧ start+12+i.val<start+25) := by omega
    have afterHeader : ¬(start≤start+12+i.val ∧ start+12+i.val<start+5) := by omega
    have offset : start+12+i.val=start+5+(i.val+7) := by omega
    simp [window,writeWindow,taglessSecondInput,inReply,afterReply,afterHeader,←offset]

def taglessLeafWrites (mem : Memory) (nonce : Words 2) (start index dst : Nat) (a b : BitVec 1600) : Memory :=
  writeWindow (writeWindow (writeWindow mem start (header index nonce)) start (replyWords a)) dst (replyWords b)

theorem tagless_leaf_digest_words (mem : Memory) (n : Words 2) (start index dst : Nat) (a b : BitVec 1600) :
    window (taglessLeafWrites mem n start index dst a b) dst = lowDigest (replyWords b) := by
  funext i
  have inside : dst ≤ dst + i.val ∧ dst+i.val < dst+25 := by have := i.isLt;omega
  simp [taglessLeafWrites,window,writeWindow,lowDigest,inside]

theorem tagless_leaf_word_outside (mem : Memory) (n : Words 2) (start index dst word : Nat) (a b : BitVec 1600)
    (sourceOut : word < start ∨ start+25 ≤ word) (heapOut : word < dst ∨ dst+25 ≤ word) :
    taglessLeafWrites mem n start index dst a b word = mem word := by
  have d : ¬ (dst ≤ word ∧ word < dst+25) := by omega
  have m : ¬ (start ≤ word ∧ word < start+25) := by omega
  have h : ¬ (start ≤ word ∧ word < start+5) := by omega
  have t : word ≠ start+12 := by omega
  simp [taglessLeafWrites,writeWindow,writeWord,d,m,h,t]


def taglessFinalReply (oracle : Oracle) (mem : Memory) (i : Nat) : BitVec 1600 :=
  let msg := window mem (leafStart i+5)
  let salt := window mem (leafSalt i)
  let a := oracle.permutation (packBuffer (firstInput i salt msg))
  oracle.permutation (packBuffer (taglessSecondInput (replyWords a) msg))

structure TaglessLeafPrefix (oracle : Oracle) (before : Memory) (s : MachineState) (count : Nat) : Prop where
  digests : ∀ i < count, (window (memoryView s) (leafDest i) : Words 4) =
    lowDigest (replyWords (taglessFinalReply oracle before i))
  messages : ∀ i, count ≤ i → i < 2^24 → (window (memoryView s) (leafStart i+5) : Words 32) =
    window before (leafStart i+5)
  salts : ∀ i < 2^24, (window (memoryView s) (leafSalt i) : Words 2) = window before (leafSalt i)

theorem empty_tagless_leaf_prefix (oracle : Oracle) (s : MachineState) : TaglessLeafPrefix oracle (memoryView s) s 0 :=
  ⟨fun _ impossible => False.elim (by omega),fun _ _ _ => rfl, fun _ _ => rfl⟩


theorem tagless_parent_content_of_leaf_prefix (oracle : Oracle) (before : Memory) (leaves : MachineState)
    (heap : Nat → BitVec 256) (salts : Index → BitVec 128) (inv : TaglessLeafPrefix oracle before leaves (2^24))
    (leaf : ∀ i : Index, heap (LENGTH+i.val)=outputDigest (taglessFinalReply oracle before i.val))
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
