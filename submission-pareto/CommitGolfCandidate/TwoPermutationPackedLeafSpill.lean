import CommitGolfCandidate.TwoPermutationPackedLeafGroups
import CommitGolfCandidate.TwoPermutationLeafInvariant
import CommitGolfCandidate.TwoPermutationPinnedCommitSpec

namespace TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
open CommitGolfCandidate (checkEvaluation)
theorem production_leaf_spill (s : MachineState) (g : Nat) (slot : Fin 4096) (bound : g < 2^12)
    (r : Regs s g slot.val) (a b : BitVec 1600) :
    let i := 4096*g+slot.val
    let mem := memoryView (finishedLeaf s slot (leafStart i) (leafDest i) a b)
    (window mem (leafDest i) = lowDigest (replyWords b)) ∧
    (∀ (j : Nat), j < i → ∀ k < 4, mem (leafDest j+k) = memoryView s (leafDest j+k)) ∧
    (∀ (j : Nat), i < j → j < 2^24 → ∀ k < 32, mem (leafStart j+5+k) = memoryView s (leafStart j+5+k)) ∧
    (∀ (j : Nat), j < 2^24 → ∀ k < 2, mem (leafSalt j+k) = memoryView s (leafSalt j+k)) ∧
    (∀ (j : Nat), i+7 ≤ j → j < 2^24 → ∀ k < 4, mem (leafDest j+k) = memoryView s (leafDest j+k)) := by
  dsimp only
  let i := 4096*g+slot.val
  have n : i < 2^24 := by dsimp [i]; have := slot.isLt; omega
  have ready := ready_slot s g slot bound r
  change LeafReady s slot (leafStart i) i (leafDest i) _ at ready
  have same := fun word (limit : word < 2^33) =>
    finished_leaf_memory _ _ _ _ _ _ word ready a b limit
  constructor
  · funext k
    change memoryView (finishedLeaf s slot (leafStart i) (leafDest i) a b) (leafDest i+k.val) = _
    rw [same _ (by unfold leafDest; have := k.isLt; omega)]
    exact congrFun (pinned_digest_words (memoryView s) (secondTag i) (nonceWords s slot) (leafStart i) (leafDest i) a b) k
  · have frame (word : Nat) (limit : word < 2^33)
        (src : word < leafStart i+1 ∨ leafStart i+26 ≤ word)
        (out : word < leafDest i ∨ leafDest i+25 ≤ word) :
        memoryView (finishedLeaf s slot (leafStart i) (leafDest i) a b) word = memoryView s word :=
      (same word limit).trans (pinned_word_outside _ _ _ _ _ _ _ _ src out)
    refine ⟨?_,?_,?_,?_⟩
    · intro j hj k hk
      apply frame <;> simp only [leafStart,leafDest] <;> omega
    · intro j hj limit k hk
      apply frame <;> simp only [leafStart,leafDest] <;> omega
    · intro j hj k hk
      apply frame <;> simp only [leafStart,leafDest,leafSalt] <;> omega
    · intro j hj limit k hk
      apply frame <;> simp only [leafStart,leafDest] <;> omega

private theorem pinned_tag_matches (i : Index) : pinnedPositionTag i=secondTag i.val := by
  unfold pinnedPositionTag secondTag firstTag
  change BitVec.ofNat 64 (4152 + 256*i.val) = BitVec.ofNat 64 (4056+256*i.val)+BitVec.ofNat 64 96
  rw [←BitVec.ofNat_add]
  congr 1 <;> omega

theorem pinned_typed_words (i : Index) (n : Words 2) (r : Words 25) (m : Words 32) :
    pinnedSecondInput i n r m = pinnedWords (secondTag i.val) n r m := by
  unfold pinnedSecondInput pinnedWords
  rw [pinned_tag_matches]

theorem production_fixed_leaf (oracle : Oracle) (s : MachineState) (g : Nat) (slot : Fin 4096)
    (bound : g < 2^12) (r : Regs s g slot.val) :
    let idx : Index := ⟨4096*g+slot.val,by unfold LENGTH LOG_LENGTH;have := slot.isLt;omega⟩
    let message := window (memoryView s) (leafStart idx.val+5)
    let first := pinnedFirstRow oracle.permutation message
    let second := pinnedSecondRow oracle.permutation idx (nonceWords s slot) first.2 message
    CommitGolfCandidate.checkEvaluation oracle (leafTrace s slot (leafStart idx.val) idx.val (leafDest idx.val)) =
      (finishedLeaf s slot (leafStart idx.val) (leafDest idx.val) first.2 second.2,2) := by
  dsimp only
  simp only [leafTrace,CommitGolfCandidate.check_evaluation_public_bind,CommitGolfCandidate.check_evaluation_pure]
  simp only [pinnedFirstRow,pinnedSecondRow,pinned_typed_words]
  rfl

theorem nonce_memory_window (s : MachineState) (g : Nat) (slot : Fin 4096) (r : Regs s g slot.val) :
    nonceWords s slot = window (memoryView s) (leafSalt (4096*g+slot.val)) := by
  funext k
  fin_cases k <;> simp only [nonceWords,window,memoryView,r.salts] <;> dsimp <;>
    congr 1 <;> simp only [wordAddress,← BitVec.ofNat_add] <;> congr 1 <;> simp only [nonceBase,leafSalt] <;> omega

theorem production_prefix_step (oracle : Oracle) (before : Memory) (s : MachineState) (g : Nat) (u : Fin 4096)
    (bound : g < 2^12) (r : Regs s g u.val) (inv : PinnedLeafPrefix oracle before s (4096*g+u.val)) :
    let i := 4096*g+u.val
    let next := (checkEvaluation oracle (leafTrace s u (leafStart i) i (leafDest i))).1
    PinnedLeafPrefix oracle before next (i+1) := by
  let i := 4096*g+u.val
  have inside : i < 2^24 := by dsimp [i]; have := u.isLt; omega
  let idx : Index := ⟨i, by exact inside⟩
  let msg := (window (memoryView s) (leafStart i+5) : Words 32)
  let a := (pinnedFirstRow oracle.permutation msg).2
  let b := (pinnedSecondRow oracle.permutation idx (nonceWords s u) a msg).2
  have response : b = pinnedFinalReply oracle before i := by
    dsimp only [b,a,pinnedSecondRow,pinnedFirstRow]
    rw [pinned_typed_words]
    change oracle.permutation (packBuffer (pinnedWords (secondTag i) (nonceWords s u) (replyWords (oracle.permutation (packBuffer (rawPrefix msg)))) msg)) = _
    rw [nonce_memory_window s g u r, inv.salts i inside]
    dsimp only [msg]
    rw [inv.messages i (by omega) inside]
    rfl
  have step := production_fixed_leaf oracle s g u bound r
  have spill := production_leaf_spill s g u bound r a b
  change checkEvaluation oracle (leafTrace s u (leafStart i) i (leafDest i)) =
    (finishedLeaf s u (leafStart i) (leafDest i) a b,2) at step
  dsimp only
  rw [step]
  refine ⟨?_,?_,?_⟩
  · intro j hj
    by_cases last : j = i
    · subst j
      exact spill.1.trans (congrArg (fun x => lowDigest (replyWords x)) response)
    · have h : j < i := by change j < i+1 at hj; omega
      apply Eq.trans _ (inv.digests j h)
      funext k
      exact spill.2.1 j h k.val k.isLt
  · intro j later limit
    apply Eq.trans _ (inv.messages j (by change i+1 ≤ j at later; omega) limit)
    funext k
    exact spill.2.2.1 j (by change i+1 ≤ j at later; omega) limit k.val k.isLt
  · intro j limit
    apply Eq.trans _ (inv.salts j limit)
    funext k
    exact spill.2.2.2.1 j limit k.val k.isLt


end TwoPermutationPrototype.RV64.PackedLeaves
