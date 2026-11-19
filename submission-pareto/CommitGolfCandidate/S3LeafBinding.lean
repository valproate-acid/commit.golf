import CommitGolfCandidate.S3LeafGame
import CommitGolfCandidate.S3LeafProbe
import CommitGolfCandidate.S3PermBridge

/-!
# Leaf binding of the stage-3 leaf hash, in the contract's oracle world

Glue between the lazy-permutation collision bound (`s3_collision_prob_le`, S3LeafGame.lean) and
the eager experiment of the contract (`perm_sampling_prob`, S3PermBridge.lean): for every fixed
compression function and a uniformly sampled permutation with forward and inverse queries, a
first stage with at most `budget` public queries followed by the replay of at most `extra` leaves
produces two replayed leaves with different values and one digest with probability at most
`(budget + 2 extra)^2 / 2^256 + budget / 2^127`.
-/

set_option exponentiation.threshold 2100

namespace CommitGolfCandidate.Permutation.Strat

variable {S : Type} {α β γ : Type}

theorem bind_assoc (st : Strat S α) (f : α → Strat S β) (g : β → Strat S γ) :
    (st.bind f).bind g = st.bind fun a => (f a).bind g := by
  induction st with
  | done a => rfl
  | fwd x k ih => simp only [Strat.bind, ih]
  | inv y k ih => simp only [Strat.bind, ih]
  | rand n k ih => simp only [Strat.bind, ih]

end CommitGolfCandidate.Permutation.Strat

namespace CommitGolfCandidate

open CommitGolf OracleComp OracleSpec
open CommitGolfCandidate.Permutation

/-- The pinned two-call input of a leaf `(salt, value)`: leaf bytes 0..200 (the first window), the
24 nonce bytes, leaf bytes 200..256. The top 8 bytes of the salt are ignored. -/
def s3Input (leaf : BitVec 256 × Entry) : S3LeafInput :=
  (BitVec.ofNat 1600 leaf.2.toNat, BitVec.ofNat 192 leaf.1.toNat,
    BitVec.ofNat 448 (leaf.2.toNat / 2 ^ 1600))

theorem s3_entry_lt (value : Entry) : value.toNat < 2 ^ 2048 := value.isLt

/-- The first window, with literal widths. -/
theorem s3_first_core (value : BitVec 2048) :
    (BitVec.ofNat 1600 (value.toNat % 2 ^ 1600) : S3State) =
      s3PinCall.enc1 (BitVec.ofNat 1600 value.toNat) := by
  simp only [s3PinCall, BitVec.toNat_ofNat]

/-- The second window, with literal widths: leaf bytes 168..256 are the pinned part of the first
window followed by leaf bytes 200..256. -/
theorem s3_second_core (salt : BitVec 256) (reply : S3State) (value : BitVec 2048) :
    (BitVec.ofNat 1600 (salt.toNat % 2 ^ 192 + reply.toNat / 2 ^ 896 * 2 ^ 192 +
        value.toNat / 2 ^ 1344 * 2 ^ 896) : S3State) =
      s3PinCall.enc2 (BitVec.ofNat 192 salt.toNat, s3PinCall.chop reply,
        s3PinCall.pin (s3PinCall.enc1 (BitVec.ofNat 1600 value.toNat)),
        BitVec.ofNat 448 (value.toNat / 2 ^ 1600)) := by
  have hreply : reply.toNat < 2 ^ 1600 := reply.isLt
  have hvalue : value.toNat < 2 ^ 2048 := value.isLt
  simp only [s3PinCall, BitVec.toNat_ofNat]
  congr 1
  omega

theorem s3_first_eq (leaf : BitVec 256 × Entry) :
    s3First leaf.2 = s3PinCall.enc1 (s3Input leaf).1 :=
  s3_first_core leaf.2

theorem s3_second_eq (leaf : BitVec 256 × Entry) (reply : S3State) :
    s3Second leaf.1 reply leaf.2 =
      s3PinCall.enc2 ((s3Input leaf).2.1, s3PinCall.chop reply,
        s3PinCall.pin (s3PinCall.enc1 (s3Input leaf).1), (s3Input leaf).2.2) :=
  s3_second_core leaf.1 reply leaf.2

theorem s3_trunc_eq (reply : S3State) :
    s3PinCall.trunc reply = BitVec.ofNat 256 reply.toNat := rfl

/-- The digest is the pinned two-call hash of the leaf input. -/
theorem s3_leaf_digest_eq (permutation : Perm) (leaf : BitVec 256 × Entry) :
    s3LeafDigest permutation leaf.1 leaf.2 =
      s3PinCall.trunc (permutation (s3PinCall.enc2 ((s3Input leaf).2.1,
        s3PinCall.chop (permutation (s3PinCall.enc1 (s3Input leaf).1)),
        s3PinCall.pin (s3PinCall.enc1 (s3Input leaf).1), (s3Input leaf).2.2))) := by
  have h1 := s3_first_eq leaf
  have h2 := s3_second_eq leaf (permutation (s3PinCall.enc1 (s3Input leaf).1))
  unfold s3LeafDigest
  rw [h1, h2]
  rfl

/-- Different leaf values give different two-call inputs, whatever the salts. -/
theorem s3_input_ne {leaf leaf' : BitVec 256 × Entry} (h : leaf.2 ≠ leaf'.2) :
    s3Input leaf ≠ s3Input leaf' := by
  intro heq
  apply h
  have hvalue := s3_entry_lt leaf.2
  have hvalue' := s3_entry_lt leaf'.2
  have h1 := congrArg (fun p => p.1.toNat) heq
  have h2 := congrArg (fun p => p.2.2.toNat) heq
  simp only [s3Input, BitVec.toNat_ofNat] at h1 h2
  apply BitVec.eq_of_toNat_eq
  omega

/-- The leaf hash program is the pinned two-call evaluation strategy. -/
theorem to_strat_hash_leaf (compression : Compression) (salt : BitVec 256) (value : Entry) :
    toStrat compression (s3HashLeaf salt value) = s3PinCall.eval (s3Input (salt, value)) := by
  have raw : toStrat compression (s3HashLeaf salt value) =
      Strat.fwd (s3First value) fun first =>
        Strat.fwd (s3Second salt first value) fun second =>
          Strat.done (BitVec.ofNat 256 second.toNat) := by
    unfold s3HashLeaf
    erw [to_strat_permute]
    rfl
  have inner : ∀ first : S3State,
      (Strat.fwd (s3Second salt first value) fun second =>
        Strat.done (BitVec.ofNat 256 second.toNat) : Strat S3State (BitVec 256)) =
      Strat.fwd (s3PinCall.enc2 ((s3Input (salt, value)).2.1, s3PinCall.chop first,
        s3PinCall.pin (s3PinCall.enc1 (s3Input (salt, value)).1), (s3Input (salt, value)).2.2))
        fun second => Strat.done (s3PinCall.trunc second) :=
    fun first => congrArg (fun input : S3State => Strat.fwd input fun second =>
      Strat.done (s3PinCall.trunc second)) (s3_second_eq (salt, value) first)
  exact raw.trans (congrArg₂ Strat.fwd (s3_first_eq (salt, value)) (funext inner))

/-- The replay program is the list evaluation strategy. -/
theorem to_strat_probe_leaves (compression : Compression) (items : List (BitVec 256 × Entry)) :
    toStrat compression (probeLeaves items) = s3EvalList s3Input items := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [probeLeaves, s3EvalList]
    rw [to_strat_bind, to_strat_hash_leaf]
    congr 1
    funext digest
    rw [to_strat_bind, ih]
    rfl

theorem s3_bound_of_real (budget extra : Nat) :
    ENNReal.ofReal (((budget : ℝ) + 2 * extra) ^ 2 / 2 ^ 256 + (budget : ℝ) / 2 ^ 127) =
      ((budget : ENNReal) + 2 * extra) ^ 2 / 2 ^ 256 + (budget : ENNReal) / 2 ^ 127 := by
  have hcast : (budget : ℝ) + 2 * extra = ((budget + 2 * extra : ℕ) : ℝ) := by push_cast; ring
  have h256 : ENNReal.ofReal ((2 : ℝ) ^ 256) = 2 ^ 256 := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    norm_num
  have h127 : ENNReal.ofReal ((2 : ℝ) ^ 127) = 2 ^ 127 := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    norm_num
  rw [hcast, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_div_of_pos (by positivity),
    ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
    h256, h127]
  push_cast
  rfl

/-- **Leaf binding.** Any fixed compression function, uniform permutation, inverse queries
allowed. The unary term `budget / 2^127` is charged to the first stage only; the replay makes
forward queries. -/
theorem s3_leaf_collision_bound (compression : Compression)
    (first : OracleComp World (Option (List (BitVec 256 × Entry)))) (budget extra : Nat)
    (bounded : PublicQueryBound first budget) (small : budget ≤ 2 ^ 120) (short : extra ≤ 2 ^ 26) :
    prEvent (LeafCollision <$> (($ᵗ Perm) >>= fun permutation =>
        fixedOracleRun ⟨compression, permutation⟩ (s3LeafSearch first extra))) ≤
      ((budget : ENNReal) + 2 * extra) ^ 2 / 2 ^ 256 + (budget : ENNReal) / 2 ^ 127 := by
  rw [perm_sampling_prob, ← s3_bound_of_real]
  apply ENNReal.ofReal_le_ofReal
  let adversary : Strat S3State (List (BitVec 256 × Entry)) :=
    (toStrat compression first).bind fun outcome => Strat.done (outcome.getD [])
  have adversaryBound : adversary.QB budget :=
    (Strat.QB.bind (to_strat_QB compression bounded)
      fun outcome => Strat.QB.done (outcome.getD []) 0).mono (by omega)
  have search : toStrat compression (s3LeafSearch first extra) =
      adversary.bind fun items => s3EvalList s3Input (items.take extra) := by
    unfold s3LeafSearch
    refine (to_strat_bind compression first _).trans ?_
    refine Eq.trans ?_ (Strat.bind_assoc (toStrat compression first)
      (fun outcome => Strat.done (outcome.getD []))
      (fun items => s3EvalList s3Input (items.take extra))).symm
    refine congrArg (Strat.bind (toStrat compression first)) (funext fun outcome => ?_)
    cases outcome with
    | none =>
      have empty : s3EvalList s3Input (List.take extra ([] : List (BitVec 256 × Entry))) =
          Strat.done [] := by rw [List.take_nil]; rfl
      exact empty.symm
    | some items => exact to_strat_probe_leaves compression (items.take extra)
  rw [search]
  refine le_trans ?_ (s3_collision_prob_le s3Input adversary budget extra adversaryBound small short)
  refine Strat.exp_mono (fun replies _ => ind_mono ?_) _ _
  rintro ⟨a, ha, b, hb, hne, heq⟩
  exact ⟨a, ha, b, hb, s3_input_ne hne, heq⟩

end CommitGolfCandidate
