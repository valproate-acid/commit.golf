import CommitGolfCandidate.TwoPermutationBindingLeaf

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp MeasureTheory
open TwoPermutationPrototype.RV64

/-- The second window starts at byte 96 and keeps words 12 through 24 of the first reply. -/
def taglessSecondInput (firstReply : Words 25) (message : Words 32) : Words 25 := fun i =>
  if h : i.val < 13 then firstReply ⟨i.val+12, by omega⟩
  else message ⟨i.val+7, by omega⟩

private theorem matching_slices {leftWidth rightWidth : Nat}
    (left : BitVec leftWidth) (right : BitVec rightWidth) (leftOffset rightOffset words : Nat)
    (same : ∀ j < words, left.extractLsb' (64 * (leftOffset + j)) 64 =
      right.extractLsb' (64 * (rightOffset + j)) 64) :
    left.extractLsb' (64 * leftOffset) (64 * words) =
      right.extractLsb' (64 * rightOffset) (64 * words) := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  have eq := congrArg (fun chunk : BitVec 64 => chunk.getLsbD (bit % 64)) (same (bit / 64) (by omega))
  have lhs : 64 * (leftOffset + bit / 64) + bit % 64 = 64 * leftOffset + bit := by omega
  have rhs : 64 * (rightOffset + bit / 64) + bit % 64 = 64 * rightOffset + bit := by omega
  simpa [show bit % 64 < 64 by omega, inside, lhs, rhs] using eq

theorem tagless_second_join (firstReply : Block) (message : Words 32) :
    outputSuffix firstReply =
      inputMiddle (packBuffer (taglessSecondInput (replyWords firstReply) message)) := by
  apply matching_slices _ _ 13 1 12
  intro word inside
  let i : Fin 25 := ⟨1 + word, by omega⟩
  change _ = (packBuffer _).extractLsb' (64 * i.val) 64
  rw [packed_word]
  have below : 1 + word < 13 := by omega
  simp [taglessSecondInput, replyWords, i, below, show 1 + word + 12 = 13 + word by omega]
  rfl

theorem tagless_second_random_slice (firstReply : Block) (message : Words 32) :
    (packBuffer (taglessSecondInput (replyWords firstReply) message)).extractLsb' 0 832 =
      firstReply.extractLsb' 768 832 := by
  symm
  apply matching_slices _ _ 12 0 13
  intro word inside
  simp only [Nat.zero_add]
  let i : Fin 25 := ⟨word, by omega⟩
  change _ = (packBuffer _).extractLsb' (64 * i.val) 64
  rw [packed_word]
  simp [taglessSecondInput, replyWords, i, inside, Nat.add_comm]
  rfl

def taglessMessageTail (message : Words 32) : BitVec 768 :=
  (packBuffer (taglessSecondInput (fun _ => 0) message)).extractLsb' 832 768

theorem tagless_second_tail (firstReply : Block) (message : Words 32) :
    (packBuffer (taglessSecondInput (replyWords firstReply) message)).extractLsb' 832 768 =
      taglessMessageTail message := by
  apply matching_slices _ _ 13 13 12
  intro word inside
  let i : Fin 25 := ⟨13 + word, by omega⟩
  change (packBuffer _).extractLsb' (64 * i.val) 64 =
    (packBuffer _).extractLsb' (64 * i.val) 64
  rw [packed_word, packed_word]
  have last : ¬ i.val < 13 := by simp [i]
  simp [taglessSecondInput, last]

def taglessSecondRow (perm : Block → Block) (message : Words 32) (firstReply : Block) : Row :=
  let input := packBuffer (taglessSecondInput (replyWords firstReply) message)
  (input, perm input)

theorem tagless_replayed_leaf_binding {history : History} (safe : SafeHistory history)
    (perm : Block → Block) (index : Index) (nonce₀ nonce₁ : Words 2) (message₀ message₁ : Words 32) :
    let a₀ := firstRow perm index nonce₀ message₀
    let a₁ := firstRow perm index nonce₁ message₁
    let b₀ := taglessSecondRow perm message₀ a₀.2
    let b₁ := taglessSecondRow perm message₁ a₁.2
    a₀ ∈ history.map Prod.snd → a₁ ∈ history.map Prod.snd →
    b₀ ∈ history.map Prod.snd → b₁ ∈ history.map Prod.snd →
    outputDigest b₀.2 = outputDigest b₁.2 → message₀ = message₁ := by
  dsimp only
  intro first₀ first₁ second₀ second₁ digest
  obtain ⟨equalA, equalB⟩ := safe.two_round_collision_impossible first₀ first₁ second₀ second₁
    (packed_first_domain index nonce₀ message₀) (packed_first_domain index nonce₁ message₁)
    (tagless_second_join _ message₀) (tagless_second_join _ message₁) digest
  have sameA := congrArg (fun row : Row => row.1) equalA
  change packBuffer (firstInput index.val nonce₀ message₀) =
    packBuffer (firstInput index.val nonce₁ message₁) at sameA
  have inputsA := packBuffer_injective sameA
  have sameB := congrArg (fun row : Row => row.1) equalB
  change packBuffer (taglessSecondInput (replyWords (firstRow perm index nonce₀ message₀).2) message₀) =
    packBuffer (taglessSecondInput (replyWords (firstRow perm index nonce₁ message₁).2) message₁) at sameB
  have inputsB := packBuffer_injective sameB
  funext position
  by_cases head : position.val < 20
  · have word := congrFun inputsA (⟨position.val + 5, by omega⟩ : Fin 25)
    have noHeader : ¬ position.val + 5 < 5 := by omega
    simpa [firstInput, noHeader] using word
  · have word := congrFun inputsB (⟨position.val - 7, by omega⟩ : Fin 25)
    have noSuffix : ¬ position.val - 7 < 13 := by omega
    have offset : position.val - 7 + 7 = position.val := by omega
    simpa [taglessSecondInput, noSuffix, offset] using word

def HasTaglessReplayedLeafCollision (cache : Cache) : Prop :=
  ∃ (perm : Block → Block) (index : Index) (nonce₀ nonce₁ : Words 2) (message₀ message₁ : Words 32),
    let a₀ := firstRow perm index nonce₀ message₀
    let a₁ := firstRow perm index nonce₁ message₁
    let b₀ := taglessSecondRow perm message₀ a₀.2
    let b₁ := taglessSecondRow perm message₁ a₁.2
    a₀ ∈ cache.entries ∧ a₁ ∈ cache.entries ∧ b₀ ∈ cache.entries ∧ b₁ ∈ cache.entries ∧
      outputDigest b₀.2 = outputDigest b₁.2 ∧ message₀ ≠ message₁

theorem tagless_replayed_leaf_collision_le {α : Type} (compress : Compression) (program : OracleComp World α)
    (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31)
    (bounded : QueryBounded program calls) :
    Pr{let result ← lazyRun compress program (PermutationCache.empty Block)}[
      HasTaglessReplayedLeafCollision result.2] ≤ (q : ENNReal) / 2 ^ 122 := by
  apply unsafe_result_with_replay compress program (fun result => HasTaglessReplayedLeafCollision result.2)
    _ q calls positive small withReplay bounded
  intro _ cache history same safe collision
  obtain ⟨perm, index, nonce₀, nonce₁, message₀, message₁, first₀, first₁, second₀, second₁, digest, conflict⟩ :=
    collision
  rw [same] at first₀ first₁ second₀ second₁
  exact conflict (tagless_replayed_leaf_binding safe perm index nonce₀ nonce₁ message₀ message₁
    first₀ first₁ second₀ second₁ digest)

end TwoPermutationPrototype.Sampling
