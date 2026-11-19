import CommitGolfCandidate.S3Leaf
import CommitGolfCandidate.CompressionSampling

/-! Oracle programs that evaluate the stage-3 leaf hash, used only in security proofs:
the replay of claimed leaves and the event that two replayed leaves collide. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec

/-- Two forward permutation queries; the digest is computed from the replies. -/
def s3HashLeaf (salt : BitVec 256) (value : Entry) : OracleComp World (BitVec 256) := do
  let first ← (liftM (World.query (.inr (.inr (.inl (s3First value))))) :
    OracleComp World (BitVec PERMUTATION_WIDTH))
  let second ← (liftM (World.query (.inr (.inr (.inl (s3Second salt first value))))) :
    OracleComp World (BitVec PERMUTATION_WIDTH))
  return BitVec.ofNat 256 second.toNat

theorem s3_hash_leaf_run (oracle : Oracle) (salt : BitVec 256) (value : Entry) :
    oracle.run (s3HashLeaf salt value) = pure (s3LeafDigest oracle.permutation salt value, 2) := by
  unfold s3HashLeaf
  erw [oracle_run_public_bind oracle (.inr (.inl (s3First value)))]
  erw [oracle_run_public_bind oracle]
  simp only [oracle_run_pure, pure_bind]
  rfl

theorem s3_hash_leaf_bound (salt : BitVec 256) (value : Entry) :
    IsTotalQueryBound (s3HashLeaf salt value) 2 := by
  unfold s3HashLeaf
  erw [isTotalQueryBound_query_bind_iff]
  refine ⟨by simp, fun first => ?_⟩
  erw [isTotalQueryBound_query_bind_iff]
  exact ⟨by simp, fun second => trivial⟩

/-- Replayed leaves: ((salt, value), digest). -/
abbrev LeafReplies := List ((BitVec 256 × Entry) × BitVec 256)

/-- Two replayed leaves with different values and one digest (salts are free). -/
def LeafCollision (replies : LeafReplies) : Prop :=
  ∃ a ∈ replies, ∃ b ∈ replies, a.1.2 ≠ b.1.2 ∧ a.2 = b.2

def probeLeaves : List (BitVec 256 × Entry) → OracleComp World LeafReplies
  | [] => pure []
  | item :: rest => do
      let digest ← s3HashLeaf item.1 item.2
      let replies ← probeLeaves rest
      return (item, digest) :: replies

theorem probe_leaves_run (oracle : Oracle) (items : List (BitVec 256 × Entry)) :
    oracle.run (probeLeaves items) =
      pure (items.map fun item => (item, s3LeafDigest oracle.permutation item.1 item.2),
        2 * items.length) := by
  induction items with
  | nil => exact oracle_run_pure _ _
  | cons item rest ih =>
    simp only [probeLeaves]
    rw [oracle_run_bind, s3_hash_leaf_run]
    simp only [pure_bind]
    rw [oracle_run_bind, ih]
    simp only [pure_bind, oracle_run_pure, List.map_cons, List.length_cons]
    congr 2
    omega

theorem probe_leaves_bound (items : List (BitVec 256 × Entry)) :
    IsTotalQueryBound (probeLeaves items) (2 * items.length) := by
  induction items with
  | nil => trivial
  | cons item rest ih =>
    simp only [probeLeaves]
    have total : 2 * (item :: rest).length = 2 + (2 * rest.length + 0) := by
      simp only [List.length_cons]; omega
    rw [total]
    apply isTotalQueryBound_bind (s3_hash_leaf_bound _ _)
    intro digest
    apply isTotalQueryBound_bind ih
    intro replies
    trivial

/-- Run a first stage that outputs the leaves to replay, then replay at most `extra` of them. -/
def s3LeafSearch (first : OracleComp World (Option (List (BitVec 256 × Entry)))) (extra : Nat) :
    OracleComp World LeafReplies :=
  first >>= fun outcome =>
    match outcome with
    | none => pure []
    | some items => probeLeaves (items.take extra)

end CommitGolfCandidate
