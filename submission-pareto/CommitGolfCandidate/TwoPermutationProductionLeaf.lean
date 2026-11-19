import CommitGolfCandidate.TwoPermutationLeafRun
import CommitGolfCandidate.TwoPermutationBindingLeaf
import CommitGolfCandidate.CheckEvaluation

/-! Actual source, heap and nonce locations for the production 2^24-leaf
commitment. The source scratch ends before any later message. Increasing heap
slots keep every completed digest and the nonce area outside each new spill. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

def leafStart (i : Nat) := 507 + 32*i
def leafDest (i : Nat) := 516 + 36 * 2^24 + 4*i
def leafSalt (i : Nat) := 516 + 42 * 2^24 + 2*i

structure ProductionRegs (s : MachineState) (group : Nat) (slot : Fin 16) : Prop where
  source : s.getReg .x10 = wordAddress (leafStart (16*group+slot.val))
  heap : s.getReg .x20 = wordAddress (leafDest (16*group))
  salts : s.getReg .x22 = wordAddress (leafSalt (16*group))
  selector : s.getReg .x5 = 0
  size : s.getReg .x11 = 200
  primitive : s.getReg .x13 = 1
  pc : s.pc = leafPC slot 0

theorem production_leaf_ready (s : MachineState) (g : Nat) (slot : Fin 16) (bound : g < 2^20)
    (r : ProductionRegs s g slot) :
    LeafReady s slot (leafStart (16*g+slot.val)) (16*g+slot.val) (leafDest (16*g+slot.val))
      (leafSalt (16*g)) := by
  have u := slot.isLt
  refine ⟨r.source,?_,r.salts,?_,?_,?_,?_,?_,r.selector,r.size,r.primitive⟩
  · rw [r.heap,wordAddress,wordAddress,← BitVec.ofNat_add]
    congr 1; unfold leafDest; omega
  · rw [commit_tag_address,wordAddress];congr 1;unfold leafStart;omega
  all_goals simp only [leafStart,leafDest,leafSalt] <;> omega

theorem production_leaf_spill (s : MachineState) (g : Nat) (slot : Fin 16) (bound : g < 2^20)
    (r : ProductionRegs s g slot) (a b : BitVec 1600) :
    let i := 16*g+slot.val
    let mem := memoryView (finishedLeaf s slot (leafStart i) (leafDest i) a b)
    (window mem (leafDest i) = lowDigest (replyWords b)) ∧
    (∀ (j : Nat), j < i → ∀ k < 4, mem (leafDest j+k) = memoryView s (leafDest j+k)) ∧
    (∀ (j : Nat), i < j → j < 2^24 → ∀ k < 32, mem (leafStart j+5+k) = memoryView s (leafStart j+5+k)) ∧
    (∀ (j : Nat), j < 2^24 → ∀ k < 2, mem (leafSalt j+k) = memoryView s (leafSalt j+k)) ∧
    (∀ (j : Nat), i+7 ≤ j → j < 2^24 → ∀ k < 4, mem (leafDest j+k) = memoryView s (leafDest j+k)) := by
  dsimp only
  let i := 16*g+slot.val
  have n : i < 2^24 := by dsimp [i]; have := slot.isLt; omega
  have ready := production_leaf_ready s g slot bound r
  have same := fun word (limit : word < 2^33) =>
    finished_leaf_memory _ _ _ _ _ _ word ready a b limit
  constructor
  · funext k
    change memoryView (finishedLeaf s slot (leafStart i) (leafDest i) a b) (leafDest i+k.val) = _
    rw [same _ (by unfold leafDest; have := k.isLt; omega)]
    exact congrFun (leaf_digest_words (memoryView s) (nonceWords s slot) (leafStart i) i (leafDest i) a b) k
  · have frame (word : Nat) (limit : word < 2^33)
        (src : word < leafStart i ∨ leafStart i+25 ≤ word)
        (out : word < leafDest i ∨ leafDest i+25 ≤ word) :
        memoryView (finishedLeaf s slot (leafStart i) (leafDest i) a b) word = memoryView s word :=
      (same word limit).trans (leaf_word_outside _ _ _ _ _ _ _ _ src out)
    refine ⟨?_,?_,?_,?_⟩
    · intro j hj k hk
      apply frame <;> simp only [leafStart,leafDest] <;> omega
    · intro j hj limit k hk
      apply frame <;> simp only [leafStart,leafDest] <;> omega
    · intro j hj k hk
      apply frame <;> simp only [leafStart,leafDest,leafSalt] <;> omega
    · intro j hj limit k hk
      apply frame <;> simp only [leafStart,leafDest] <;> omega

theorem production_fixed_leaf (oracle : Oracle) (s : MachineState) (g : Nat) (slot : Fin 16)
    (bound : g < 2^20) (r : ProductionRegs s g slot) :
    let idx : Index := ⟨16*g+slot.val,by unfold LENGTH LOG_LENGTH;have := slot.isLt;omega⟩
    let message := window (memoryView s) (leafStart idx.val+5)
    let first := firstRow oracle.permutation idx (nonceWords s slot) message
    let second := secondRow oracle.permutation idx message first.2
    CommitGolfCandidate.checkEvaluation oracle (leafTrace s slot (leafStart idx.val) idx.val (leafDest idx.val)) =
      (finishedLeaf s slot (leafStart idx.val) (leafDest idx.val) first.2 second.2,2) := by
  dsimp only
  simp only [leafTrace,CommitGolfCandidate.check_evaluation_public_bind,CommitGolfCandidate.check_evaluation_pure]
  rfl

end TwoPermutationPrototype.RV64
