import CommitGolfCandidate.TwoPermutationBindingHistory
import CommitGolfCandidate.TwoPermutationSyscall

/-! Connect the real syscall's input encoding with the binding history's three
bit projections. The final lemma is phrased in terms of rows recorded by replay. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

private def packedState (words : Words 25) : MachineState :=
  { initialMachine with mem := fun addr =>
      if h : addr.toNat / 8 < 25 then words ⟨addr.toNat / 8, h⟩ else 0 }

private theorem packedState_word (words : Words 25) (i : Fin 25) :
    (packedState words).getMem (wordAddress i.val) = words i := by
  rw [MachineState.getMem, packedState]
  dsimp only
  rw [word_address_value (by have := i.isLt; omega)]
  simp [i.isLt]

private theorem packedState_window (words : Words 25) : window (memoryView (packedState words)) 0 = words := by
  funext i
  simpa [window, memoryView] using packedState_word words i

theorem packed_word (words : Words 25) (i : Fin 25) :
    (packBuffer words).extractLsb' (64 * i.val) 64 = words i := by
  have initial : readBuffer (packedState words) 0 200 = packBuffer words := by
    simpa only [Nat.mul_zero, packedState_window] using read_permutation_window (packedState words) 0
  have slice := CommitGolfCandidate.read_buffer_slice (packedState words) 0 200 (8 * i.val) 8 (by have := i.isLt; omega)
  have word := CommitGolfCandidate.read_digest_word (packedState words) (8 * i.val) 0 (by omega) (by decide)
  have wordSlice := CommitGolfCandidate.read_buffer_slice (packedState words) (8 * i.val) 32 0 8 (by decide)
  have address : 8 * (8 * i.val) = 64 * i.val := by omega
  simp only [initial, address, Nat.zero_add] at slice
  simp only [Nat.mul_zero, Nat.add_zero] at word wordSlice
  exact slice.trans (wordSlice.symm.trans (word.trans (packedState_word words i)))

theorem packBuffer_injective : Function.Injective packBuffer := by
  intro left right same
  funext i
  rw [← packed_word left i, ← packed_word right i, same]

private theorem slices_eq_of_words {leftWidth rightWidth : Nat}
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

theorem packed_first_domain (index : Index) (nonce : Words 2) (message : Words 32) :
    packBuffer (firstInput index.val nonce message) ∈ firstDomain := by
  apply domain_of_header _ index
  let expected : BitVec 192 := (0#128) ++ firstTag index.val
  have equal := slices_eq_of_words (packBuffer (firstInput index.val nonce message)) expected 0 0 3 (by
    intro j bound
    have word := packed_word (firstInput index.val nonce message) ⟨j, by omega⟩
    rw [Nat.zero_add, word]
    interval_cases j
    · change firstTag index.val = ((0#128) ++ firstTag index.val).extractLsb' 0 64
      exact BitVec.extractLsb'_append_eq_right.symm
    · rw [BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 64)]
      simp [firstInput, header]
    · rw [BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 128)]
      simp [firstInput, header])
  change (packBuffer (firstInput index.val nonce message)).extractLsb' (64 * 0) (64 * 3) = expected
  apply equal.trans
  change expected.extractLsb' 0 192 = expected
  simp

theorem packed_second_join (index : Index) (firstReply : Block) (message : Words 32) :
    outputSuffix firstReply =
      inputMiddle (packBuffer (secondInput index.val (replyWords firstReply) message)) := by
  apply slices_eq_of_words _ _ 13 1 12
  intro word inside
  let i : Fin 25 := ⟨1 + word, by omega⟩
  have packed := packed_word (secondInput index.val (replyWords firstReply) message) i
  change _ = (packBuffer _).extractLsb' (64 * i.val) 64
  rw [packed]
  have below : 1 + word < 13 := by omega
  simp [secondInput, replyWords, i, below, show 1 + word + 12 = 13 + word by omega]
  rfl

def firstRow (perm : Block → Block) (index : Index) (nonce : Words 2) (message : Words 32) : Row :=
  let input := packBuffer (firstInput index.val nonce message)
  (input, perm input)

def secondRow (perm : Block → Block) (index : Index) (message : Words 32) (firstReply : Block) : Row :=
  let input := packBuffer (secondInput index.val (replyWords firstReply) message)
  (input, perm input)

theorem replayed_leaf_digest_binding {history : History} (safe : SafeHistory history)
    (perm : Block → Block) (index : Index) (nonce₀ nonce₁ : Words 2) (message₀ message₁ : Words 32) :
    let a₀ := firstRow perm index nonce₀ message₀
    let a₁ := firstRow perm index nonce₁ message₁
    let b₀ := secondRow perm index message₀ a₀.2
    let b₁ := secondRow perm index message₁ a₁.2
    a₀ ∈ history.map Prod.snd → a₁ ∈ history.map Prod.snd →
    b₀ ∈ history.map Prod.snd → b₁ ∈ history.map Prod.snd →
    outputDigest b₀.2 = outputDigest b₁.2 → message₀ = message₁ := by
  dsimp only
  intro first₀ first₁ second₀ second₁ digest
  obtain ⟨equalA, equalB⟩ := safe.two_round_collision_impossible first₀ first₁ second₀ second₁
    (packed_first_domain index nonce₀ message₀) (packed_first_domain index nonce₁ message₁)
    (packed_second_join index _ message₀) (packed_second_join index _ message₁) digest
  have firstEqual := congrArg (fun row : Row => row.1) equalA
  change packBuffer (firstInput index.val nonce₀ message₀) =
    packBuffer (firstInput index.val nonce₁ message₁) at firstEqual
  have inputsA := packBuffer_injective firstEqual
  have secondEqual := congrArg (fun row : Row => row.1) equalB
  change packBuffer (secondInput index.val (replyWords (firstRow perm index nonce₀ message₀).2) message₀) =
    packBuffer (secondInput index.val (replyWords (firstRow perm index nonce₁ message₁).2) message₁) at secondEqual
  have inputsB := packBuffer_injective secondEqual
  funext position
  by_cases head : position.val < 20
  · have word := congrFun inputsA (⟨position.val + 5, by omega⟩ : Fin 25)
    have noHeader : ¬ position.val + 5 < 5 := by omega
    simpa [firstInput, noHeader] using word
  · have word := congrFun inputsB (⟨position.val - 7, by omega⟩ : Fin 25)
    have noTag : position.val - 7 ≠ 0 := by omega
    have noSuffix : ¬ position.val - 7 < 13 := by omega
    have offset : position.val - 7 + 7 = position.val := by omega
    simpa [secondInput, noTag, noSuffix, offset] using word


def HasReplayedLeafCollision (cache : Cache) : Prop :=
  ∃ (perm : Block → Block) (index : Index) (nonce₀ nonce₁ : Words 2) (message₀ message₁ : Words 32),
    let a₀ := firstRow perm index nonce₀ message₀
    let a₁ := firstRow perm index nonce₁ message₁
    let b₀ := secondRow perm index message₀ a₀.2
    let b₁ := secondRow perm index message₁ a₁.2
    a₀ ∈ cache.entries ∧ a₁ ∈ cache.entries ∧ b₀ ∈ cache.entries ∧ b₁ ∈ cache.entries ∧
      outputDigest b₀.2 = outputDigest b₁.2 ∧ message₀ ≠ message₁

open MeasureTheory in
/-- The probability of a conflicting pair of same-position leaves whose four
oracle rows are present after a bounded adaptive replay. -/
theorem replayed_leaf_collision_le {α : Type} (compress : Compression) (program : OracleComp World α)
    (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31)
    (bounded : QueryBounded program calls) :
    Pr{let result ← lazyRun compress program (PermutationCache.empty Block)}[
      HasReplayedLeafCollision result.2] ≤ (q : ENNReal) / 2 ^ 122 := by
  apply unsafe_result_with_replay compress program (fun result => HasReplayedLeafCollision result.2)
    _ q calls positive small withReplay bounded
  intro _ cache history same safe collision
  obtain ⟨perm, index, nonce₀, nonce₁, message₀, message₁, first₀, first₁, second₀, second₁, digest, conflict⟩ :=
    collision
  rw [same] at first₀ first₁ second₀ second₁
  exact conflict (replayed_leaf_digest_binding safe perm index nonce₀ nonce₁ message₀ message₁
    first₀ first₁ second₀ second₁ digest)

end TwoPermutationPrototype.Sampling
