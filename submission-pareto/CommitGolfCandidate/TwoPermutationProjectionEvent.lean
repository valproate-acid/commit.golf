import CommitGolfCandidate.TwoPermutationInverseEvent

/-! Finite-slice bounds for either direction of the lazy permutation. Earlier
query replies and the choice of the next query may be fully adaptive. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp MeasureTheory
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem remaining_output_count {α : Type} [Fintype α] [DecidableEq α] (table : List (α × α))
    [Fintype (RemainingOutputs table)] :
    Fintype.card α - table.length ≤ Fintype.card (RemainingOutputs table) := by
  classical
  let : Fintype (RemainingInputs (flipTable table)) := Fintype.ofFinite _
  let eqv : RemainingOutputs table ≃ RemainingInputs (flipTable table) :=
    Equiv.subtypeEquivRight fun address => by
      constructor
      · intro fresh row present
        obtain ⟨original, inTable, rfl⟩ := List.mem_map.mp present
        exact fresh original inTable
      · intro fresh row present
        exact fresh row.swap (List.mem_map_of_mem present)
  rw [Fintype.card_congr eqv]
  simpa only [flipTable, List.length_map] using remaining_input_count (α := α) (flipTable table)

theorem forward_fresh_event_le {α : Type} [Fintype α] [DecidableEq α]
    (cache : PermutationCache α) (input : α) (fresh : UnusedInput cache.entries input)
    (bad : Set α) (size : Nat) (bound : bad.encard ≤ (size : ℕ∞)) :
    Pr{let answer ← @uniformSample _ (cache.forwardSampler input fresh)}[answer.val ∈ bad] ≤
      (size : ENNReal) / (Fintype.card α - cache.entries.length : Nat) := by
  let : MeasurableSpace (RemainingOutputs cache.entries) := ⊤
  let : Fintype (RemainingOutputs cache.entries) := Fintype.ofFinite _
  let : SampleableType (RemainingOutputs cache.entries) := cache.forwardSampler input fresh
  let event : Set (RemainingOutputs cache.entries) := {answer | answer.val ∈ bad}
  have smaller : event.encard ≤ bad.encard :=
    Set.encard_le_encard_of_injOn (f := Subtype.val) (fun _ present => present) Subtype.val_injective.injOn
  have probability := SampleableType.evalDist_uniformSample_le_of_encard_le event size (smaller.trans bound)
  rw [prEvent_eq_evalDist_of_discrete]
  refine probability.trans (ENNReal.div_le_div le_rfl ?_)
  exact_mod_cast remaining_output_count (α := α) cache.entries

private def fillSlice {low width high : Nat} (total : high + width + low = 1600)
    (target : BitVec width) (rest : BitVec high × BitVec low) : BitVec 1600 :=
  ((rest.1 ++ target) ++ rest.2).cast total

theorem slice_fiber_size {low width high : Nat} (total : high + width + low = 1600)
    (target : BitVec width) :
    {b : BitVec 1600 | b.extractLsb' low width = target}.encard ≤ ((2 ^ (high + low) : Nat) : ℕ∞) := by
  have subset : {b : BitVec 1600 | b.extractLsb' low width = target} ⊆ Set.range (fillSlice total target) := by
    intro block matched
    refine ⟨(block.extractLsb' (width + low) high, block.extractLsb' 0 low), ?_⟩
    change block.extractLsb' low width = target at matched
    unfold fillSlice
    rw [← matched, BitVec.append_assoc]
    have part : block.extractLsb' low width ++ block.extractLsb' 0 low =
        block.extractLsb' 0 (width + low) :=
      BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega)
    rw [part, BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega)]
    apply BitVec.eq_of_getLsbD_eq
    intro i inside
    have fits : i < high + (width + low) := by omega
    simp [fits]
  apply (Set.encard_mono subset).trans
  rw [← Set.image_univ]
  refine (Set.encard_image_le _ _).trans_eq ?_
  rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_prod]
  simp only [Fintype.card_bitVec, ← Nat.pow_add]

private theorem slice_divisor {low width high : Nat} (total : high + width + low = 1600)
    (positive : 1 ≤ width) (cache : Cache) (room : cache.entries.length ≤ 2 ^ 121) :
    ((2 ^ (high + low) : Nat) : ENNReal) / (Fintype.card Block - cache.entries.length : Nat) ≤
      (1 : ENNReal) / 2 ^ (width - 1) := by
  have universeSize : Fintype.card Block = 2 ^ 1600 := Fintype.card_bitVec 1600
  rw [universeSize]
  have remaining : 2 ^ 1599 ≤ (2 ^ 1600 : Nat) - cache.entries.length := by omega
  apply (ENNReal.div_le_div (le_refl _) (show (2 ^ 1599 : ENNReal) ≤
    ((2 ^ 1600 : Nat) - cache.entries.length : Nat) by exact_mod_cast remaining)).trans_eq
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have exponent : 1599 = width - 1 + (high + low) := by omega
  have factor : (2 : ENNReal) ^ 1599 = 2 ^ (width - 1) * 2 ^ (high + low) :=
    (congrArg (fun n : Nat => (2 : ENNReal) ^ n) exponent).trans (pow_add _ _ _)
  rw [factor]
  simpa only [one_mul] using ENNReal.mul_div_mul_right (c := (2 : ENNReal) ^ (high + low))
    1 (2 ^ (width - 1)) (by positivity) (by finiteness)

theorem fresh_forward_slice_le (cache : Cache) (input : Block) (fresh : UnusedInput cache.entries input)
    {low width high : Nat} (total : high + width + low = 1600) (positive : 1 ≤ width)
    (room : cache.entries.length ≤ 2 ^ 121) (target : BitVec width) :
    Pr{let answer ← @uniformSample _ (cache.forwardSampler input fresh)}[answer.val.extractLsb' low width = target] ≤
      (1 : ENNReal) / 2 ^ (width - 1) := by
  have sampled := forward_fresh_event_le cache input fresh {b | b.extractLsb' low width = target}
    (2 ^ (high + low)) (slice_fiber_size total target)
  exact sampled.trans (slice_divisor total positive cache room)

theorem fresh_inverse_slice_le (cache : Cache) (output : Block) (fresh : UnusedOutput cache.entries output)
    {low width high : Nat} (total : high + width + low = 1600) (positive : 1 ≤ width)
    (room : cache.entries.length ≤ 2 ^ 121) (target : BitVec width) :
    Pr{let answer ← @uniformSample _ (cache.inverseSampler output fresh)}[answer.val.extractLsb' low width = target] ≤
      (1 : ENNReal) / 2 ^ (width - 1) := by
  have sampled := inverse_fresh_event_le cache output fresh {b | b.extractLsb' low width = target}
    (2 ^ (high + low)) (slice_fiber_size total target)
  exact sampled.trans (slice_divisor total positive cache room)

end TwoPermutationPrototype.Sampling
