import CommitGolfCandidate.TwoPermutationHidingEager

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp MeasureTheory TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

def pinnedPositionTag (index : Index) : BitVec 64 :=
  BitVec.ofNat 64 (4152 + 256 * index.val)

def pinnedFirstInput (message : Words 32) : Words 25 :=
  fun i => message ⟨i.val, by omega⟩

def pinnedSecondInput (index : Index) (nonce : Words 2) (firstReply : Words 25)
    (message : Words 32) : Words 25 := fun i =>
  if i.val = 0 then pinnedPositionTag index
  else if h : i.val < 3 then nonce ⟨i.val - 1, by omega⟩
  else if h : i.val < 14 then firstReply ⟨i.val + 11, by omega⟩
  else message ⟨i.val + 7, by omega⟩

def pinnedFirstRow (perm : Block → Block) (message : Words 32) : Row :=
  let address := packBuffer (pinnedFirstInput message)
  (address, perm address)

def pinnedSecondRow (perm : Block → Block) (index : Index) (nonce : Words 2) (firstReply : Block)
    (message : Words 32) : Row :=
  let address := packBuffer (pinnedSecondInput index nonce (replyWords firstReply) message)
  (address, perm address)

def pinnedLeafDigest (perm : Block → Block) (index : Index) (nonce : Words 2)
    (message : Words 32) : BitVec 256 :=
  outputDigest (pinnedSecondRow perm index nonce (pinnedFirstRow perm message).2 message).2

def pinnedFullLeafDigests (p : BiPermutation Block) (message : Message) (salts : CompleteSaltTape) : DigestTape :=
  fun i => pinnedLeafDigest p.forward i (saltWords (salts i)) (messageWords message i)

theorem pinned_position_tag_injective : Function.Injective pinnedPositionTag := by
  intro i j same
  have left : 4152 + 256 * i.val < 2^64 := by
    have range : i.val < 2^24 := i.isLt
    omega
  have right : 4152 + 256 * j.val < 2^64 := by
    have range : j.val < 2^24 := j.isLt
    omega
  have raw := congrArg BitVec.toNat same
  simp only [pinnedPositionTag, BitVec.toNat_ofNat, Nat.mod_eq_of_lt left, Nat.mod_eq_of_lt right] at raw
  exact Fin.ext (by omega)

theorem pinned_second_tag (index : Index) (nonce : Words 2) (reply : Block) (message : Words 32) :
    (packBuffer (pinnedSecondInput index nonce (replyWords reply) message)).extractLsb' 0 64 =
      pinnedPositionTag index := by
  have first := packed_word (pinnedSecondInput index nonce (replyWords reply) message) (0 : Fin 25)
  simpa only [pinnedSecondInput, Fin.val_zero, Nat.mul_zero, ite_true] using first

theorem pinned_second_input_nonce_injective (index : Index) (reply : Block) (message : Words 32) :
    Function.Injective (fun nonce : Words 2 => packBuffer (pinnedSecondInput index nonce (replyWords reply) message)) := by
  intro first second same
  have words := packBuffer_injective same
  funext i
  let slot : Fin 25 := ⟨i.val + 1, by omega⟩
  have sameWord := congrFun words slot
  have nonzero : i.val + 1 ≠ 0 := by omega
  have below : i.val + 1 < 3 := by omega
  simpa only [slot, pinnedSecondInput, nonzero, ite_false, below, dite_true,
    Nat.add_sub_cancel, Fin.eta] using sameWord

theorem pinned_second_input_distinct_indices (i j : Index) (r s : Words 2)
    (reply reply' : Block) (message message' : Words 32)
    (same : packBuffer (pinnedSecondInput i r (replyWords reply) message) =
      packBuffer (pinnedSecondInput j s (replyWords reply') message')) : i = j := by
  have tag := congrArg (fun word : Block => word.extractLsb' 0 64) same
  exact pinned_position_tag_injective
    ((pinned_second_tag i r reply message).symm.trans (tag.trans (pinned_second_tag j s reply' message')))

theorem pinned_chaining_preserved (index : Index) (nonce : Words 2) (tail : BitVec 1344)
    (low₀ low₁ : BitVec 256) (message : Words 32) :
    pinnedSecondInput index nonce (replyWords (tail ++ low₀)) message =
      pinnedSecondInput index nonce (replyWords (tail ++ low₁)) message := by
  funext i
  unfold pinnedSecondInput
  split
  · rfl
  split
  · rfl
  split
  · let start := 64 * (i.val + 11)
    change (tail ++ low₀).extractLsb' start 64 = (tail ++ low₁).extractLsb' start 64
    have inTail : 256 ≤ start := by dsimp [start]; omega
    exact (BitVec.extractLsb'_append_eq_of_le inTail).trans
      (BitVec.extractLsb'_append_eq_of_le inTail).symm
  · rfl

end TwoPermutationPrototype.Sampling
