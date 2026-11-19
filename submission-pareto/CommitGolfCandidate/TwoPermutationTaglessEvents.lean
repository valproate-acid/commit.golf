import CommitGolfCandidate.TwoPermutationTaglessBinding
import CommitGolfCandidate.TwoPermutationHidingTape

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp MeasureTheory
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2048

def taglessSecondBlock (reply : Block) (tail : BitVec 768) : Block :=
  tail ++ reply.extractLsb' 768 832

theorem tagless_second_block_exact (reply : Block) (message : Words 32) :
    RV64.packBuffer (taglessSecondInput (RV64.replyWords reply) message) =
      taglessSecondBlock reply (taglessMessageTail message) := by
  unfold taglessSecondBlock
  rw [← tagless_second_random_slice reply message, ← tagless_second_tail reply message]
  exact (BitVec.extractLsb'_append_extractLsb' (w := 768) (len := 832)
    (x := RV64.packBuffer (taglessSecondInput (RV64.replyWords reply) message))).symm

private theorem unif_slice {low width high : Nat} (total : high+width+low = 1600)
    (word : BitVec width) :
    Pr{let reply ← $ᵗ Block}[reply.extractLsb' low width = word] ≤ (1 : ENNReal)/2^width := by
  let : MeasurableSpace Block := ⊤
  have bound := slice_fiber_size total word
  have probability := SampleableType.evalDist_uniformSample_le_of_encard_le _ _ bound
  rw [prEvent_eq_evalDist_of_discrete]
  refine probability.trans_eq ?_
  rw [Fintype.card_bitVec]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [show (2 : ENNReal)^1600 = 2^width * 2^(high+low) from by rw [← pow_add]; congr 1; omega]
  simpa only [one_mul] using
    ENNReal.mul_div_mul_right (c := (2 : ENNReal)^(high+low)) 1 (2^width) (by positivity) (by finiteness)

theorem tagless_proposal_address_hit (tail : BitVec 768) (guess : Block) :
    Pr{let reply ← $ᵗ Block}[taglessSecondBlock reply tail = guess] ≤ (1 : ENNReal)/2^832 := by
  refine (prEvent_mono _ (p := fun reply => taglessSecondBlock reply tail = guess)
    (q := fun reply => reply.extractLsb' 768 832 = guess.extractLsb' 0 832) ?_).trans
      (unif_slice (low := 768) (high := 0) (by decide) _)
  intro reply same
  have low : (taglessSecondBlock reply tail).extractLsb' 0 832 = reply.extractLsb' 768 832 := by
    change (tail ++ reply.extractLsb' 768 832).extractLsb' 0 832 = _
    exact BitVec.extractLsb'_append_eq_right
  exact low.symm.trans (congrArg (fun input : Block => input.extractLsb' 0 832) same)

theorem tagless_proposal_repeated_address (tail : BitVec 768) (known : List Block) :
    Pr{let reply ← $ᵗ Block}[∃ address ∈ known, taglessSecondBlock reply tail = address] ≤
      (known.length : ENNReal)/2^832 := by
  simpa only [mul_one_div] using
    prEvent_list_le known ($ᵗ Block) (fun address reply => taglessSecondBlock reply tail = address)
      (1/2^832) (fun address _ => tagless_proposal_address_hit tail address)

private theorem tagless_first_header (reply : Block) (tail : BitVec 768)
    (yes : taglessSecondBlock reply tail ∈ firstDomain) :
    ∃ i : Index, reply.extractLsb' 768 192 = (0#128) ++ firstTag i.val := by
  have inside : ∃ input, firstDomainBlock input = taglessSecondBlock reply tail := yes
  obtain ⟨⟨i, upper⟩, same⟩ := inside
  have low := congrArg (fun w : Block => w.extractLsb' 0 192) same
  have header :
      (firstDomainBlock (i, upper)).extractLsb' 0 192 = (0#128) ++ firstTag i.val := by
    unfold firstDomainBlock
    rw [BitVec.append_assoc]
    exact BitVec.extractLsb'_append_eq_right
  have slice :
      (taglessSecondBlock reply tail).extractLsb' 0 192 = reply.extractLsb' 768 192 := by
    change (tail ++ reply.extractLsb' 768 832).extractLsb' 0 192 = _
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0+192 ≤ 832)]
    apply BitVec.eq_of_getLsbD_eq
    intro j jBound
    have jRoom : j < 832 := by omega
    simp [jRoom, jBound]
  exact ⟨i, slice.symm.trans (low.symm.trans header)⟩

private theorem prEvent_index_le {α : Type} (sample : ProbComp α) (event : Index → α → Prop)
    (cost : ENNReal) (each : ∀ i, Pr{let answer ← sample}[event i answer] ≤ cost) :
    Pr{let answer ← sample}[∃ i, event i answer] ≤ 2^24*cost := by
  classical
  let all : List Index := Finset.univ.toList
  have bound := prEvent_list_le all sample event cost (fun i _ => each i)
  have size : all.length = 2^24 := by
    rw [show all.length = Fintype.card Index by simp only [all, Finset.length_toList, Finset.card_univ]]
    exact Fintype.card_fin _
  rw [size] at bound
  simpa only [all, Finset.mem_toList, Finset.mem_univ, true_and, Nat.cast_pow, Nat.cast_ofNat]
    using bound

private theorem mul_pow_margin (width : Nat) (enough : 24 ≤ width) :
    (2 : ENNReal)^24 * (1/2^width) = 1/2^(width-24) := by
  rw [mul_one_div, show width = (width-24)+24 by omega, pow_add]
  have factor := ENNReal.mul_div_mul_right (c := (2 : ENNReal)^24)
    1 (2^(width-24)) (by positivity) (by finiteness)
  simpa only [one_mul, Nat.add_sub_cancel] using factor

theorem tagless_proposal_first_domain_le (tail : BitVec 768) :
    Pr{let reply ← $ᵗ Block}[taglessSecondBlock reply tail ∈ firstDomain] ≤
      (1 : ENNReal)/2^168 := by
  refine (prEvent_mono _ (p := fun reply => taglessSecondBlock reply tail ∈ firstDomain)
    (q := fun reply => ∃ i : Index, reply.extractLsb' 768 192 = (0#128) ++ firstTag i.val)
    (fun reply yes => tagless_first_header reply tail yes)).trans ?_
  apply (prEvent_index_le _ _ ((1 : ENNReal)/2^192) fun i =>
    unif_slice (low := 768) (high := 640) (by decide) ((0#128) ++ firstTag i.val)).trans_eq
  exact mul_pow_margin 192 (by decide)

/-- The opened-stage guard works after every adaptive history in range, using
the actual uniform sampler from the remaining permutation outputs. -/
theorem tagless_fresh_forward_first_domain_le (cache : Cache) (input : Block)
    (fresh : UnusedInput cache.entries input) (room : cache.entries.length ≤ 2^121)
    (tail : BitVec 768) :
    Pr{let answer ← @uniformSample _ (cache.forwardSampler input fresh)}[
      taglessSecondBlock answer.val tail ∈ firstDomain] ≤ (1 : ENNReal)/2^167 := by
  let sample : ProbComp (RemainingOutputs cache.entries) := @uniformSample _ (cache.forwardSampler input fresh)
  refine (prEvent_mono sample (p := fun answer => taglessSecondBlock answer.val tail ∈ firstDomain)
    (q := fun answer => ∃ i : Index, answer.val.extractLsb' 768 192 = (0#128) ++ firstTag i.val)
    (fun answer yes => tagless_first_header answer.val tail yes)).trans ?_
  apply (prEvent_index_le sample _ ((1 : ENNReal)/2^191) fun i =>
    fresh_forward_slice_le cache input fresh (low := 768) (width := 192) (high := 640)
      (by decide) (by decide) room ((0#128) ++ firstTag i.val)).trans_eq
  exact mul_pow_margin 191 (by decide)

section FirstInputs

noncomputable local instance {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem tagless_first_tape_address_hit (indices : ι → Index) (distinct : Function.Injective indices)
    (messages : Index → Words 32) (guess : Block) :
    Pr{let salts ← $ᵗ (ι → BitVec 128)}[
      ∃ i, hiddenFirstInput (indices i) (messages (indices i)) (salts i) = guess] ≤
      (1 : ENNReal)/2^128 := by
  classical
  let selected (i : ι) := firstTag (indices i).val = guess.extractLsb' 0 64
  have hit_select (i : ι) (salts : ι → BitVec 128)
      (hit : hiddenFirstInput (indices i) (messages (indices i)) (salts i) = guess) : selected i := by
    exact (hidden_first_tag (indices i) (messages (indices i)) (salts i)).symm.trans
      (congrArg (fun address : Block => address.extractLsb' 0 64) hit)
  by_cases hasTag : ∃ i, selected i
  · obtain ⟨j, selectedJ⟩ := hasTag
    refine (prEvent_mono ($ᵗ (ι → BitVec 128))
      (p := fun salts => ∃ i, hiddenFirstInput (indices i) (messages (indices i)) (salts i) = guess)
      (q := fun salts => hiddenFirstInput (indices j) (messages (indices j)) (salts j) = guess) ?_).trans ?_
    · rintro salts ⟨i, hit⟩
      have same := distinct (hidden_first_tag_indices ((hit_select i salts hit).trans selectedJ.symm))
      exact same ▸ hit
    · have coord := (uniform_tape_coordinate j (fun salt : BitVec 128 => pure salt)).prEvent_eq
        (fun salt => hiddenFirstInput (indices j) (messages (indices j)) salt = guess)
      rw [bind_pure_comp, prEvent_map, bind_pure] at coord
      exact coord.le.trans (public_guess_first_input_le (indices j) (messages (indices j)) guess)
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ (fun salts _ ⟨i, hit⟩ =>
      hasTag ⟨i, hit_select i salts hit⟩)]
    exact zero_le

/-- Salt guesses are charged once per cached address, even for all opened or all hidden indices. -/
theorem tagless_first_tape_cache_hit (indices : ι → Index) (distinct : Function.Injective indices)
    (messages : Index → Words 32) (known : List Block) :
    Pr{let salts ← $ᵗ (ι → BitVec 128)}[∃ address ∈ known, ∃ i,
      hiddenFirstInput (indices i) (messages (indices i)) (salts i) = address] ≤
      (known.length : ENNReal)/2^128 := by
  simpa only [mul_one_div] using
    prEvent_list_le known ($ᵗ (ι → BitVec 128))
      (fun address salts => ∃ i, hiddenFirstInput (indices i) (messages (indices i)) (salts i) = address)
      (1/2^128) (fun address _ => tagless_first_tape_address_hit indices distinct messages address)

end FirstInputs

end TwoPermutationPrototype.Sampling
