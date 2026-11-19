import CommitGolfCandidate.TaggedPinnedBitLayout
import CommitGolfCandidate.S3Leaf
import CommitGolfCandidate.TwoPermutationCheckerPaths

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.RV64
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

def pinnedPeerSalt (index : Index) (salt : BitVec 128) : BitVec 256 :=
  (0#64) ++ (salt ++ pinnedPositionTag index)

private theorem append_nat {a b : Nat} (high : BitVec a) (low : BitVec b) :
    (high ++ low).toNat = high.toNat * 2^b + low.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt low.isLt, Nat.shiftLeft_eq]

private theorem add_backwards (salt reply value : Nat) : value + (reply + salt) = salt + reply + value := by
  omega

theorem pinned_first_peer (index : Index) (value : Entry) :
    packBuffer (pinnedFirstInput (entryWords value)) = s3First value := by
  have layout := pinned_pack_first_input (fun _ => value) index
  change packBuffer (pinnedFirstInput (entryWords value)) = value.extractLsb' 0 1600 at layout
  rw [layout]
  apply BitVec.eq_of_toNat_eq
  simp [s3First, PERMUTATION_WIDTH, BitVec.extractLsb', BitVec.toNat_setWidth]

private theorem top_toNat (high low : Nat) (x : BitVec (high+low)) :
    (x.extractLsb' low high).toNat = x.toNat / 2^low := by
  have fits : x.toNat / 2^low < 2^high := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
    rw [← Nat.pow_add]
    exact x.isLt
  simp only [BitVec.extractLsb', BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]

private theorem padded_nat {w h : Nat} (x : BitVec w) :
    ((0#h) ++ x).toNat % 2^w = x.toNat := by
  rw [append_nat]
  simp only [BitVec.toNat_zero,zero_mul,zero_add,Nat.mod_eq_of_lt x.isLt]

private theorem from_own_nat {w : Nat} (x : BitVec w) : BitVec.ofNat w x.toNat = x := by
  apply BitVec.eq_of_toNat_eq
  exact Nat.mod_eq_of_lt x.isLt

private theorem three_windows {h m l : Nat} (high : BitVec h) (mid : BitVec m) (low : BitVec l) :
    high ++ (mid ++ low) = BitVec.ofNat (h+(m+l))
      (low.toNat+mid.toNat*2^l+high.toNat*2^(m+l)) := by
  refine (from_own_nat (high ++ (mid ++ low))).symm.trans ?_
  apply congrArg (BitVec.ofNat _)
  rw [append_nat,append_nat]
  exact add_backwards _ _ _

private theorem assembled_second (value : BitVec 2048) (reply : BitVec 1600) (salt : BitVec 192) :
    value.extractLsb' 1344 704 ++ (reply.extractLsb' 896 704 ++ salt) =
      s3Second ((0#64) ++ salt) reply value := by
  refine (three_windows (value.extractLsb' 1344 704) (reply.extractLsb' 896 704) salt).trans ?_
  unfold s3Second
  apply congrArg (BitVec.ofNat 1600)
  rw [top_toNat 704 1344 value,top_toNat 704 896 reply,padded_nat,show (704 : Nat) + 192 = 896 by decide]
  rfl

theorem pinned_second_peer (index : Index) (value : Entry) (salt : BitVec 128) (reply : Block) :
    packBuffer (pinnedSecondInput index (saltWords salt) (replyWords reply) (entryWords value)) =
      s3Second (pinnedPeerSalt index salt) reply value :=
  (pinned_pack_second_input (fun _ => value) index reply salt).trans
    (assembled_second value reply (salt ++ pinnedPositionTag index))

theorem pinned_leaf_peer (p : Perm) (index : Index) (value : Entry) (salt : BitVec 128) :
    pinnedLeafDigest p index (saltWords salt) (entryWords value) = s3LeafDigest p (pinnedPeerSalt index salt) value := by
  unfold pinnedLeafDigest pinnedFirstRow pinnedSecondRow s3LeafDigest
  dsimp only
  rw [pinned_second_peer, pinned_first_peer index]
  rfl

end TwoPermutationPrototype.Sampling
