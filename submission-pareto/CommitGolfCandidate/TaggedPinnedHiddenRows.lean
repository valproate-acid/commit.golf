import CommitGolfCandidate.TaggedPinnedAdaptiveObserver
import CommitGolfCandidate.TaggedPinnedFreshGuess
import CommitGolfCandidate.TaggedPinnedHiddenWrites

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2048

noncomputable local instance pinnedHiddenRowsSampler {I α : Type} [Fintype I] [Fintype α] [Nonempty α] :
    SampleableType (I → α) := by
  classical
  exact SampleableType.ofFintype _

noncomputable def pinnedAddedUpper {base : Cache} (cache : PinnedHighCache base) (address : Block) :
    Option (BitVec 1344) := by
  classical
  exact if found : ∃ row ∈ cache.added, row.input = address then some (Classical.choose found).upper else none

theorem pinned_added_upper_read {base : Cache} (cache : PinnedHighCache base) {slot : Nat}
    (valid : cache.Valid slot) (row : PinnedHighRow) (found : row ∈ cache.added) :
    pinnedAddedUpper cache row.input = some row.upper := by
  classical
  have known : ∃ before ∈ cache.added, before.input = row.input := ⟨row, found, rfl⟩
  unfold pinnedAddedUpper
  rw [dite_eq_left known]
  have witness := Classical.choose_spec known
  exact congrArg (fun row : PinnedHighRow => some row.upper)
    (pinned_unique_mapped_key PinnedHighRow.input valid.inputUnique witness.1 found witness.2)

theorem pinned_added_upper_injective {base : Cache} (cache : PinnedHighCache base) {slot : Nat}
    (valid : cache.Valid slot) (a b : Block) (tail : BitVec 1344)
    (left : pinnedAddedUpper cache a = some tail) (right : pinnedAddedUpper cache b = some tail) : a = b := by
  classical
  unfold pinnedAddedUpper at left right
  split at left
  · rename_i foundA
    split at right
    · rename_i foundB
      have wA := Classical.choose_spec foundA
      have wB := Classical.choose_spec foundB
      have eq := pinned_unique_mapped_key PinnedHighRow.upper valid.tailUnique wA.1 wB.1
        ((Option.some.inj left).trans (Option.some.inj right).symm)
      exact wA.2.symm.trans ((congrArg PinnedHighRow.input eq).trans wB.2)
    · cases right
  · cases left

section Finite
variable {I : Type} [Fintype I]

noncomputable def pinnedNonceAddresses (position : I → Index) (first : I → Block)
    (message : I → Words 32) (nonce : I → BitVec 128) : List Block :=
  Finset.univ.toList.map (fun i => pinnedPrivateSecond (position i) (first i) (message i) (nonce i))

theorem pinned_nonce_addresses_length (position : I → Index) (first : I → Block)
    (message : I → Words 32) (nonce : I → BitVec 128) :
    (pinnedNonceAddresses position first message nonce).length = Fintype.card I := by
  simp only [pinnedNonceAddresses, List.length_map, Finset.length_toList, Finset.card_univ]

noncomputable def samplePinnedHiddenRows {base : Cache} (cache : PinnedHighCache base) (slot : Nat)
    (position : I → Index) (first : I → Block) (message : I → Words 32)
    (digests : I → BitVec 256) : ProbComp (List Row) := by
  classical
  exact do
    let nonce ← $ᵗ (I → BitVec 128)
    let addresses := pinnedNonceAddresses position first message nonce
    if ∀ input ∈ addresses, UnusedInput base.entries input then
      let final ← runPinnedHigh cache slot [] (pinnedConstantPlans addresses)
      pure (Finset.univ.toList.map (fun i =>
        let input := pinnedPrivateSecond (position i) (first i) (message i) (nonce i)
        (input, pinnedCachedUpper final.2.zero input ++ digests i)))
    else pure []

theorem pinned_hidden_rows_hit_le [DecidableEq I] {base : Cache} (cache : PinnedHighCache base) (slot : Nat)
    (valid : cache.Valid slot) (position : I → Index) (distinct : Function.Injective position)
    (first : I → Block) (message : I → Words 32) (digests : I → BitVec 256)
    (room : cache.zero.entries.length + Fintype.card I ≤ 2^121) (query : Row) :
    Pr{let rows ← samplePinnedHiddenRows cache slot position first message digests}[rowHits rows query = true] ≤
      (1 : ENNReal)/2^128 + 1/2^128 + (Fintype.card I : ENNReal)/2^1343 := by
  classical
  let b (nonce : I → BitVec 128) (i : I) := pinnedPrivateSecond (position i) (first i) (message i) (nonce i)
  let firstHit (nonce : I → BitVec 128) := ∃ i, b nonce i = query.1
  let oldHit (nonce : I → BitVec 128) := ∃ i,
    (pinnedAddedUpper cache (b nonce i)).map (fun upper => (upper ++ digests i : Block)) = some query.2
  let hit (nonce : I → BitVec 128) := firstHit nonce ∨ oldHit nonce
  let observe (nonce : I → BitVec 128) : ProbComp (List Row) := do
    let addresses := pinnedNonceAddresses position first message nonce
    if ∀ input ∈ addresses, UnusedInput base.entries input then
      let final ← runPinnedHigh cache slot [] (pinnedConstantPlans addresses)
      pure (Finset.univ.toList.map (fun i =>
        let input := b nonce i
        (input, pinnedCachedUpper final.2.zero input ++ digests i)))
    else pure []
  have oldBound : Pr{let nonce ← $ᵗ (I → BitVec 128)}[hit nonce] ≤
      (1 : ENNReal)/2^128 + 1/2^128 :=
    (prEvent_or_le _ firstHit oldHit).trans (add_le_add
      (pinned_fixed_address_hit_le position distinct first message query.1)
      (pinned_reused_output_hit_le position distinct first message (pinnedAddedUpper cache)
        (pinned_added_upper_injective cache valid) digests query.2))
  have after (nonce : I → BitVec 128) (_ : nonce ∈ support ($ᵗ (I → BitVec 128))) (safe : ¬ hit nonce) :
      Pr{let rows ← observe nonce}[rowHits rows query = true] ≤ (Fintype.card I : ENNReal)/2^1343 := by
    let addresses := pinnedNonceAddresses position first message nonce
    let plans := pinnedConstantPlans addresses
    let run := runPinnedHigh cache slot [] plans
    let made (final : List (BitVec 1344) × PinnedHighCache base) : List Row :=
      Finset.univ.toList.map (fun i =>
        let input := b nonce i
        (input, pinnedCachedUpper final.2.zero input ++ digests i))
    have shape : observe nonce = (if ∀ input ∈ addresses, UnusedInput base.entries input then
      run >>= fun final => pure (made final) else pure []) := rfl
    by_cases new : ∀ input ∈ addresses, UnusedInput base.entries input
    · rw [shape, ite_eq_left new, bind_pure_comp, prEvent_map]
      have size : plans.length = Fintype.card I := by
        simp only [plans, pinnedConstantPlans, List.length_map, addresses, pinned_nonce_addresses_length]
      have enough : cache.zero.entries.length + plans.length ≤ 2^121 := size ▸ room
      have tailBound := pinned_high_new_tail_le cache slot [] plans enough (pinnedOutputTail query.2)
      have returnBound : Pr{let final ← run}[cache.NewTail final.2 (pinnedOutputTail query.2)] ≤
          (Fintype.card I : ENNReal)/2^1343 := by
        simpa only [size, run] using tailBound
      refine (prEvent_mono_of_support run (p := fun final => rowHits (made final) query = true)
        (q := fun final => cache.NewTail final.2 (pinnedOutputTail query.2)) ?_).trans returnBound
      intro final reached detected
      simp only [made, rowHits, List.any_eq_true, List.mem_map, Finset.mem_toList, Finset.mem_univ,
        true_and, decide_eq_true_eq] at detected
      obtain ⟨_, ⟨i, rfl⟩, input | output⟩ := detected
      · exact (safe (Or.inl ⟨i, input.symm⟩)).elim
      · have here : b nonce i ∈ addresses := List.mem_map.mpr ⟨i, by simp, rfl⟩
        have fact := pinned_high_const_support cache slot [] addresses valid
          (by simpa only [addresses, pinned_nonce_addresses_length] using room) final reached
        obtain ⟨stored, appears, equal⟩ := pinned_row_from_covers final.2 (b nonce i)
          (fact.2.2.2 (b nonce i) here) (new _ here)
        have top := pinned_high_cached_upper_of_row final.2 stored appears
        rw [equal] at top
        have bytes : (stored.upper ++ digests i : Block) = query.2 :=
          (congrArg (fun head : BitVec 1344 => (head ++ digests i : Block)) top).symm.trans output.symm
        by_cases wasStored : stored ∈ cache.added
        · have initial := pinned_added_upper_read cache valid stored wasStored
          rw [equal] at initial
          exact (safe (Or.inr ⟨i, by
            rw [initial]; exact congrArg some bytes⟩)).elim
        · have replyTail : pinnedOutputTail (stored.upper ++ digests i) = stored.upper :=
            BitVec.extractLsb'_append_eq_left
          exact ⟨stored, appears, wasStored, replyTail.symm.trans (congrArg pinnedOutputTail bytes)⟩
    · rw [shape, ite_eq_right new]
      simp [rowHits]
  exact (prEvent_bind_le_prEvent_add_of_support ($ᵗ (I → BitVec 128)) observe hit
    (fun rows => rowHits rows query = true) after).trans (add_le_add oldBound le_rfl)

end Finite

end TwoPermutationPrototype.Sampling
