import CommitGolfCandidate.TaggedPinnedObserver
import CommitGolfCandidate.TaggedPinnedHighRun

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp TwoPermutationPrototype.RV64
set_option maxRecDepth 8192

def pinnedFirstAddress (message : Message) (index : Index) : Block :=
  packBuffer (pinnedFirstInput (messageWords message index))

def pinnedSecondFromHigh (index : Index) (message : Message) (nonce : BitVec 128)
    (upper : BitVec 1344) : Block :=
  pinnedPrivateSecond index (upper ++ (0 : BitVec 256)) (messageWords message index) nonce

theorem pinned_address_from_first_high (index : Index) (message : Message) (nonce : BitVec 128)
    (reply : Block) :
    pinnedPrivateSecond index reply (messageWords message index) nonce =
      pinnedSecondFromHigh index message nonce (pinnedOutputTail reply) := by
  have whole : pinnedOutputTail reply ++ pinnedOutputDigest reply = reply :=
    BitVec.extractLsb'_append_extractLsb'
  have same := congrArg packBuffer (pinned_chaining_preserved index (saltWords nonce)
    (pinnedOutputTail reply) (pinnedOutputDigest reply) 0 (messageWords message index))
  have chain := same
  change pinnedPrivateSecond index (pinnedOutputTail reply ++ pinnedOutputDigest reply)
      (messageWords message index) nonce =
      pinnedSecondFromHigh index message nonce (pinnedOutputTail reply) at chain
  exact (congrArg (fun first => pinnedPrivateSecond index first (messageWords message index) nonce) whole).symm.trans chain

def pinnedFirstAddresses (left right : Message) : List Block :=
  (List.finRange LENGTH).map (pinnedFirstAddress left) ++
    (List.finRange LENGTH).map (pinnedFirstAddress right)

theorem pinned_first_addresses_length (left right : Message) :
    (pinnedFirstAddresses left right).length = 2 * LENGTH := by
  simp [pinnedFirstAddresses, two_mul]

theorem pinned_first_address_mem (left right : Message) (which : Bool) (i : Index) :
    pinnedFirstAddress (if which then right else left) i ∈ pinnedFirstAddresses left right := by
  cases which <;> simp [pinnedFirstAddresses]

def pinnedPublicAddress (message : Message) (upper : Block → BitVec 1344) (index : Index)
    (nonce : BitVec 128) : Block :=
  pinnedSecondFromHigh index message nonce (upper (pinnedFirstAddress message index))

theorem pinned_public_addresses_site (m m' : Message) (hi hi' : Block → BitVec 1344)
    (i j : Index) (nonce nonce' : BitVec 128)
    (same : pinnedPublicAddress m hi i nonce = pinnedPublicAddress m' hi' j nonce') :
    i = j :=
  pinned_second_input_distinct_indices i j (saltWords nonce) (saltWords nonce')
    (hi (pinnedFirstAddress m i) ++ (0 : BitVec 256)) (hi' (pinnedFirstAddress m' j) ++ (0 : BitVec 256))
    (messageWords m i) (messageWords m' j) same

noncomputable def pinnedOpenedAddresses (positions : Positions) (message : Message) (upper : Block → BitVec 1344)
    (salts : OpenedSalts positions) : List Block :=
  positions.toList.map (fun i => pinnedPublicAddress message upper i (publicOpenedSalts salts i))

theorem pinned_opened_addresses_length (positions : Positions) (message : Message)
    (upper : Block → BitVec 1344) (salts : OpenedSalts positions) :
    (pinnedOpenedAddresses positions message upper salts).length = positions.card := by
  simp [pinnedOpenedAddresses]

theorem pinned_opened_addresses_agree (positions : Positions) (left right : Message)
    (upper : Block → BitVec 1344) (salts : OpenedSalts positions)
    (agree : ∀ i ∈ positions, left i = right i) :
    pinnedOpenedAddresses positions left upper salts = pinnedOpenedAddresses positions right upper salts := by
  unfold pinnedOpenedAddresses
  apply List.map_congr_left
  intro i included
  have words : messageWords left i = messageWords right i :=
    congrArg (fun entry : Entry => fun word : Fin 32 => entry.extractLsb' (64 * word.val) 64)
      (agree i (Finset.mem_toList.mp included))
  simp only [pinnedPublicAddress, pinnedSecondFromHigh, pinnedFirstAddress, words]

theorem pinned_hidden_from_opened {positions : Positions} (message openedMessage : Message)
    (upper : Block → BitVec 1344) (salts : OpenedSalts positions)
    (i : Index) (hidden : i ∉ positions) (nonce : BitVec 128) :
    pinnedPublicAddress message upper i nonce ∉ pinnedOpenedAddresses positions openedMessage upper salts := by
  intro seen
  obtain ⟨j, present, same⟩ := List.mem_map.mp seen
  have equal := pinned_public_addresses_site _ _ _ _ _ _ _ _ same
  exact hidden (equal ▸ Finset.mem_toList.mp present)

theorem pinned_leaf_digest_from_high (p : BiPermutation Block) (message : Message)
    (salts : CompleteSaltTape) (upper : Block → BitVec 1344) (i : Index)
    (agree : upper (pinnedFirstAddress message i) = pinnedOutputTail (p.forward (pinnedFirstAddress message i))) :
    pinnedFullLeafDigests p message salts i =
      outputDigest (p.forward (pinnedPublicAddress message upper i (salts i))) := by
  let first := p.forward (pinnedFirstAddress message i)
  have formula := pinned_address_from_first_high i message (salts i) first
  exact congrArg (fun addr => outputDigest (p.forward addr))
    (formula.trans (congrArg (pinnedSecondFromHigh i message (salts i)) agree.symm))

def pinnedConstantPlans (addresses : List Block) : List PinnedHighPlan :=
  addresses.map (fun address _ => address)

theorem pinned_constant_plans_run {α : Type} (p : BiPermutation Block) (answers : List Block)
    (addresses : List Block) (next : List Block → BiPermutation Block → ProbComp α) :
    runPlanned next p answers ((pinnedConstantPlans addresses).map pinnedLiftPlan) =
      next ((addresses.map p.forward).reverse ++ answers) p := by
  induction addresses generalizing answers with
  | nil => rfl
  | cons address rest ih =>
    simp only [pinnedConstantPlans, List.map_cons, pinnedLiftPlan, runPlanned]
    exact (ih (p.forward address :: answers)).trans (by simp [List.reverse_cons, List.append_assoc])

end TwoPermutationPrototype.Sampling
