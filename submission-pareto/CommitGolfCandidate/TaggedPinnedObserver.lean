import CommitGolfCandidate.TaggedPinnedModel
import CommitGolfCandidate.TaggedPinnedTailCoupling

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp MeasureTheory TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

def pinnedPrivateSecond (i : Index) (reply : Block) (message : Words 32) (salt : BitVec 128) : Block :=
  packBuffer (pinnedSecondInput i (saltWords salt) (replyWords reply) message)

private theorem pinned_salt_words_injective : Function.Injective saltWords := by
  intro left right same
  have low := congrFun same (0 : Fin 2)
  have high := congrFun same (1 : Fin 2)
  change left.extractLsb' 0 64 = right.extractLsb' 0 64 at low
  change left.extractLsb' 64 64 = right.extractLsb' 64 64 at high
  have reconstruct (value : BitVec 128) :
      value.extractLsb' 64 64 ++ value.extractLsb' 0 64 = value :=
    BitVec.extractLsb'_append_extractLsb'
  calc
    left = _ := (reconstruct left).symm
    _ = right.extractLsb' 64 64 ++ right.extractLsb' 0 64 := by rw [low, high]
    _ = right := reconstruct right

theorem pinned_fixed_salt_guess_le (i : Index) (reply : Block) (message : Words 32) (guess : Block) :
    Pr{let salt ← $ᵗ BitVec 128}[pinnedPrivateSecond i reply message salt = guess] ≤
      (1 : ENNReal)/2^128 := by
  let : MeasurableSpace (BitVec 128) := ⊤
  let event : Set (BitVec 128) := {salt | pinnedPrivateSecond i reply message salt = guess}
  have unique : Function.Injective (pinnedPrivateSecond i reply message) :=
    (pinned_second_input_nonce_injective i reply message).comp pinned_salt_words_injective
  have size : event.encard ≤ (1 : ℕ∞) := by
    by_cases hit : ∃ salt, pinnedPrivateSecond i reply message salt = guess
    · obtain ⟨key, fits⟩ := hit
      have subset : event ⊆ {key} := fun salt equal => Set.mem_singleton_iff.mpr (unique (equal.trans fits.symm))
      exact (Set.encard_mono subset).trans (by simp)
    · have empty : event = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun salt equal => hit ⟨salt, equal⟩)
      simp [empty]
  rw [prEvent_eq_evalDist_of_discrete]
  simpa only [Nat.cast_one, Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat] using
    SampleableType.evalDist_uniformSample_le_of_encard_le event 1 size

noncomputable local instance pinnedObserverFunctionSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

section Tape
variable {I : Type} [Fintype I] [DecidableEq I]

theorem pinned_fixed_address_hit_le (position : I → Index) (different : Function.Injective position)
    (reply : I → Block) (message : I → Words 32) (guess : Block) :
    Pr{let nonce ← $ᵗ (I → BitVec 128)}[∃ i, pinnedPrivateSecond (position i) (reply i) (message i) (nonce i) = guess] ≤
      (1 : ENNReal)/2^128 := by
  classical
  let event (i : I) (nonce : I → BitVec 128) := pinnedPrivateSecond (position i) (reply i) (message i) (nonce i) = guess
  let selected (i : I) := pinnedPositionTag (position i) = guess.extractLsb' 0 64
  have implied (i : I) (nonce : I → BitVec 128) (hit : event i nonce) : selected i :=
    (pinned_second_tag (position i) (saltWords (nonce i)) (reply i) (message i)).symm.trans
      (congrArg (fun address : Block => address.extractLsb' 0 64) hit)
  by_cases someTag : ∃ i, selected i
  · obtain ⟨j, chosen⟩ := someTag
    refine (prEvent_mono ($ᵗ (I → BitVec 128)) (p := fun nonce => ∃ i, event i nonce)
      (q := event j) ?_).trans ?_
    · rintro nonce ⟨i, hit⟩
      have same := different (pinned_position_tag_injective ((implied i nonce hit).trans chosen.symm))
      exact same ▸ hit
    · have sampler := (uniform_tape_coordinate j (fun salt : BitVec 128 => pure salt)).prEvent_eq
        (fun salt => pinnedPrivateSecond (position j) (reply j) (message j) salt = guess)
      rw [bind_pure_comp, prEvent_map, bind_pure] at sampler
      exact sampler.le.trans (pinned_fixed_salt_guess_le (position j) (reply j) (message j) guess)
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ (fun nonce _ ⟨i, hit⟩ => someTag ⟨i, implied i nonce hit⟩)]
    exact zero_le

theorem pinned_known_address_hit_le (position : I → Index) (different : Function.Injective position)
    (reply : I → Block) (message : I → Words 32) (known : List Block) :
    Pr{let nonce ← $ᵗ (I → BitVec 128)}[∃ address ∈ known, ∃ i,
      pinnedPrivateSecond (position i) (reply i) (message i) (nonce i) = address] ≤
      (known.length : ENNReal)/2^128 := by
  simpa only [mul_one_div] using prEvent_list_le known ($ᵗ (I → BitVec 128))
    (fun guess nonce => ∃ i, pinnedPrivateSecond (position i) (reply i) (message i) (nonce i) = guess)
    (1/2^128) (fun guess _ => pinned_fixed_address_hit_le position different reply message guess)

/-- Inverse detection of a changed latent row must name its unique upper tail.
The guessed tail nominates at most one address and hence at most one site. -/
theorem pinned_reused_output_hit_le (position : I → Index) (different : Function.Injective position)
    (reply : I → Block) (message : I → Words 32)
    (latent : Block → Option (BitVec 1344))
    (unique : ∀ a b hi, latent a = some hi → latent b = some hi → a = b)
    (digest : I → BitVec 256) (guess : Block) :
    Pr{let nonce ← $ᵗ (I → BitVec 128)}[∃ i,
      (latent (pinnedPrivateSecond (position i) (reply i) (message i) (nonce i))).map
        (fun hi => (hi ++ digest i : Block)) = some guess] ≤ (1 : ENNReal)/2^128 := by
  classical
  let event (nonce : I → BitVec 128) := ∃ i,
    (latent (pinnedPrivateSecond (position i) (reply i) (message i) (nonce i))).map
      (fun hi => (hi ++ digest i : Block)) = some guess
  have tailHit (nonce : I → BitVec 128) : event nonce → ∃ i,
      latent (pinnedPrivateSecond (position i) (reply i) (message i) (nonce i)) =
        some (pinnedOutputTail guess) := by
    rintro ⟨i, found⟩
    let address := pinnedPrivateSecond (position i) (reply i) (message i) (nonce i)
    change (latent address).map (fun hi => (hi ++ digest i : Block)) = some guess at found
    cases eq : latent address with
    | none => simp [eq] at found
    | some hi =>
      have foundEq : (some (hi ++ digest i) : Option Block) = some guess := by
        rw [eq] at found
        exact found
      have output : (hi ++ digest i : Block) = guess := Option.some.inj foundEq
      have split : pinnedOutputTail (hi ++ digest i) = hi := BitVec.extractLsb'_append_eq_left
      exact ⟨i, eq.trans (congrArg Option.some (split.symm.trans (congrArg pinnedOutputTail output)))⟩
  by_cases present : ∃ address, latent address = some (pinnedOutputTail guess)
  · obtain ⟨address, known⟩ := present
    refine (prEvent_mono ($ᵗ (I → BitVec 128)) (p := event)
      (q := fun nonce => ∃ i, pinnedPrivateSecond (position i) (reply i) (message i) (nonce i) = address)
      ?_).trans (pinned_fixed_address_hit_le position different reply message address)
    intro nonce hit
    obtain ⟨i, found⟩ := tailHit nonce hit
    exact ⟨i, unique _ _ _ found known⟩
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ (fun nonce _ hit => by
          obtain ⟨i, found⟩ := tailHit nonce hit
          exact present ⟨_, found⟩)]
    exact zero_le

end Tape
end TwoPermutationPrototype.Sampling
