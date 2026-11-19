import CommitGolfCandidate.TaggedPinnedHiddenRows
import CommitGolfCandidate.TaggedPinnedConditionalSwap

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 750000
set_option exponentiation.threshold 2048

private noncomputable def pinnedEnumeration (I : Type) [Fintype I] :
    Fin (Finset.univ : Finset I).toList.length ≃ I := by
  classical
  exact List.Nodup.getEquivOfForallMemList _ (Finset.nodup_toList _) (fun i => by simp)

noncomputable def pinnedNonceOrder {I : Type} [Fintype I] (position : I → Index) (first : I → Block)
    (message : I → Words 32) (nonce : I → BitVec 128) :
    Fin (pinnedNonceAddresses position first message nonce).length ≃ I :=
  (finCongr (by simp only [pinnedNonceAddresses, List.length_map])).trans (pinnedEnumeration I)

theorem pinned_nonce_address_at {I : Type} [Fintype I] (position : I → Index) (first : I → Block)
    (message : I → Words 32) (nonce : I → BitVec 128)
    (i : Fin (pinnedNonceAddresses position first message nonce).length) :
    let pos := pinnedNonceOrder position first message nonce i
    (pinnedNonceAddresses position first message nonce)[i] =
      pinnedPrivateSecond (position pos) (first pos) (message pos) (nonce pos) := by
  let all : List I := (Finset.univ : Finset I).toList
  let toBlock (j : I) := pinnedPrivateSecond (position j) (first j) (message j) (nonce j)
  have inputFits : i.val < (all.map toBlock).length := i.isLt
  have indexFits : i.val < all.length := by simpa only [List.length_map] using inputFits
  change (all.map toBlock)[i.val]'inputFits = toBlock (all[i.val]'indexFits)
  exact List.getElem_map toBlock

theorem pinned_nonce_addresses_nodup {I : Type} [Fintype I] (position : I → Index) (unique : Function.Injective position)
    (first : I → Block) (message : I → Words 32) (nonce : I → BitVec 128) :
    (pinnedNonceAddresses position first message nonce).Nodup := by
  apply (Finset.nodup_toList _).map
  intro i j eq
  exact unique (pinned_second_input_distinct_indices _ _ _ _ _ _ _ _ eq)

theorem pinned_nonce_program_rows_match {I : Type} [Fintype I] (position : I → Index)
    (unique : Function.Injective position) (first : I → Block) (message : I → Words 32) (nonce : I → BitVec 128)
    (digest : I → BitVec 256) (high : Block → BitVec 1344) :
    let addresses := pinnedNonceAddresses position first message nonce
    let order := pinnedNonceOrder position first message nonce
    addresses.map (fun input =>
      (input, (high input ++ pinnedDigestByAddress addresses (fun i => digest (order i)) input : Block))) =
    (Finset.univ : Finset I).toList.map (fun i =>
      let input := pinnedPrivateSecond (position i) (first i) (message i) (nonce i)
      (input, (high input ++ digest i : Block))) := by
  dsimp only
  change (((Finset.univ : Finset I).toList.map (fun i =>
    pinnedPrivateSecond (position i) (first i) (message i) (nonce i))).map _) = _
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  have mapped : ∃ j : Fin (pinnedNonceAddresses position first message nonce).length,
      pinnedNonceOrder position first message nonce j = i :=
    (pinnedNonceOrder position first message nonce).surjective i
  obtain ⟨j, located⟩ := mapped
  have value := pinned_nonce_address_at position first message nonce j
  dsimp only at value
  rw [located] at value
  have read := pinned_digest_by_address_get (pinnedNonceAddresses position first message nonce)
    (pinned_nonce_addresses_nodup position unique first message nonce)
    (fun k => digest (pinnedNonceOrder position first message nonce k)) j
  simp only [located, value] at read
  exact Prod.ext rfl (congrArg (fun low : BitVec 256 =>
    (high (pinnedPrivateSecond (position i) (first i) (message i) (nonce i)) ++ low : Block)) read)

theorem pinned_low_function_order {I J Output : Type} [Fintype I] [Fintype J]
    (order : I ≃ J) (next : (I → BitVec 256) → ProbComp Output) :
    (samplePinnedLowFn I >>= next) =ᵈ
      (samplePinnedLowFn J >>= fun full => next (fun i => full (order i))) := by
  let : SampleableType (I → BitVec 256) := @pinnedLowFunctionSampler I inferInstance
  let : SampleableType (J → BitVec 256) := @pinnedLowFunctionSampler J inferInstance
  let equiv : (I → BitVec 256) ≃ (J → BitVec 256) := Equiv.arrowCongr order (Equiv.refl _)
  exact uniform_transport_bind (transportOfEquiv equiv) next

end TwoPermutationPrototype.Sampling
