import CommitGolfCandidate.TwoPermutationBindingLeaf

/-! Hit bounds for the four private coordinates in a reference transcript.
Each bound allows the guess to be fixed after observing the public digest. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp MeasureTheory
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

def saltWords (salt : BitVec 128) : Words 2 :=
  fun i => salt.extractLsb' (64 * i.val) 64

def hiddenFirstInput (index : Index) (message : Words 32) (salt : BitVec 128) : Block :=
  packBuffer (firstInput index.val (saltWords salt) message)

def hiddenSecondInput (index : Index) (message : Words 32) (firstReply : Block) : Block :=
  packBuffer (secondInput index.val (replyWords firstReply) message)

private theorem salt_words_injective : Function.Injective saltWords := by
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

theorem hidden_first_input_injective (index : Index) (message : Words 32) :
    Function.Injective (hiddenFirstInput index message) := by
  intro left right same
  apply salt_words_injective
  have words := packBuffer_injective same
  funext i
  let j : Fin 25 := ⟨i.val + 3, by omega⟩
  have chosen := congrFun words j
  have within : i.val + 3 < 5 := by omega
  have offset : i.val + 3 - 3 = i.val := by omega
  simpa [firstInput, header, j, within, offset] using chosen

theorem hidden_first_tag (index : Index) (message : Words 32) (salt : BitVec 128) :
    (hiddenFirstInput index message salt).extractLsb' 0 64 = firstTag index.val := by
  have tag := packed_word (firstInput index.val (saltWords salt) message) (0 : Fin 25)
  change (hiddenFirstInput index message salt).extractLsb' 0 64 = firstTag index.val at tag
  exact tag

theorem hidden_second_tag (index : Index) (message : Words 32) (firstReply : Block) :
    (hiddenSecondInput index message firstReply).extractLsb' 0 64 = secondTag index.val := by
  have tag := packed_word (secondInput index.val (replyWords firstReply) message) (0 : Fin 25)
  change (hiddenSecondInput index message firstReply).extractLsb' 0 64 = secondTag index.val at tag
  exact tag

theorem hidden_first_tag_indices {i j : Index} (same : firstTag i.val = firstTag j.val) : i = j :=
  Fin.ext (first_tag_injective i.isLt j.isLt same)

theorem hidden_second_tag_indices {i j : Index} (same : secondTag i.val = secondTag j.val) : i = j :=
  Fin.ext (second_tag_injective i.isLt j.isLt same)

private theorem uniform_injective_guess {β : Type} {width : Nat} (f : BitVec width → β)
    (unique : Function.Injective f) (guess : β) :
    Pr{let hidden ← $ᵗ BitVec width}[f hidden = guess] ≤ (1 : ENNReal) / 2 ^ width := by
  let : MeasurableSpace (BitVec width) := ⊤
  let event : Set (BitVec width) := {value | f value = guess}
  have size : event.encard ≤ (1 : ℕ∞) := by
    by_cases existsHit : ∃ value, f value = guess
    · obtain ⟨hit, found⟩ := existsHit
      apply (Set.encard_mono (b := {hit}) ?_).trans (by simp)
      intro value equal
      exact Set.mem_singleton_iff.mpr (unique (equal.trans found.symm))
    · have empty : event = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro value equal
        exact existsHit ⟨value, equal⟩
      simp [empty]
  have chance := SampleableType.evalDist_uniformSample_le_of_encard_le event 1 size
  rw [prEvent_eq_evalDist_of_discrete]
  simpa only [Nat.cast_one, Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat] using chance

theorem public_guess_first_input_le (index : Index) (message : Words 32) (guess : Block) :
    Pr{let salt ← $ᵗ BitVec 128}[hiddenFirstInput index message salt = guess] ≤
      (1 : ENNReal) / 2 ^ 128 :=
  uniform_injective_guess _ (hidden_first_input_injective index message) guess

private theorem uniform_block_slice {low width high : Nat} (total : high + width + low = 1600)
    (guess : BitVec width) :
    Pr{let hidden ← $ᵗ Block}[hidden.extractLsb' low width = guess] ≤ (1 : ENNReal) / 2 ^ width := by
  let : MeasurableSpace Block := ⊤
  have size := slice_fiber_size total guess
  have chance := SampleableType.evalDist_uniformSample_le_of_encard_le _ _ size
  rw [prEvent_eq_evalDist_of_discrete]
  refine chance.trans_eq ?_
  rw [Fintype.card_bitVec]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [show (2 : ENNReal) ^ 1600 = 2 ^ width * 2 ^ (high + low) by rw [← pow_add]; congr 1; omega]
  simpa only [one_mul] using
    (ENNReal.mul_div_mul_right (c := (2 : ENNReal) ^ (high + low))
      1 (2 ^ width) (by positivity) (by finiteness))

theorem public_guess_second_input_le (index : Index) (message : Words 32) (guess : Block) :
    Pr{let firstReply ← $ᵗ Block}[hiddenSecondInput index message firstReply = guess] ≤
      (1 : ENNReal) / 2 ^ 768 := by
  refine (prEvent_mono _ (p := fun firstReply => hiddenSecondInput index message firstReply = guess)
    (q := fun firstReply => outputSuffix firstReply = inputMiddle guess) ?_).trans
      (uniform_block_slice (low := 832) (width := 768) (high := 0) (by decide) (inputMiddle guess))
  intro firstReply equal
  exact (packed_second_join index firstReply message).trans (congrArg inputMiddle equal)

theorem public_guess_first_output_le (guess : Block) :
    Pr{let firstReply ← $ᵗ Block}[firstReply = guess] ≤ (1 : ENNReal) / 2 ^ 1600 :=
  uniform_injective_guess id Function.injective_id guess

theorem public_guess_second_output_le (digest : BitVec 256) (guess : Block) :
    Pr{let tail ← $ᵗ BitVec 1344}[tail ++ digest = guess] ≤ (1 : ENNReal) / 2 ^ 1344 := by
  apply uniform_injective_guess
  intro left right same
  have high := congrArg (fun reply : Block => reply.extractLsb' 256 1344) same
  exact BitVec.extractLsb'_append_eq_left.symm.trans (high.trans BitVec.extractLsb'_append_eq_left)


def plannedInput (messages : Index → Words 32) (salts : Index → BitVec 128)
    (firstReplies : Index → Block) (phaseIndex : Bool × Index) : Block :=
  if phaseIndex.1 then hiddenSecondInput phaseIndex.2 (messages phaseIndex.2) (firstReplies phaseIndex.2)
  else hiddenFirstInput phaseIndex.2 (messages phaseIndex.2) (salts phaseIndex.2)

theorem planned_inputs_distinct (messages : Index → Words 32) (salts : Index → BitVec 128)
    (firstReplies : Index → Block) :
    Function.Injective (plannedInput messages salts firstReplies) := by
  rintro ⟨leftPhase, left⟩ ⟨rightPhase, right⟩ equal
  have tag := congrArg (fun word : Block => word.extractLsb' 0 64) equal
  cases leftPhase <;> cases rightPhase
  · simp only [plannedInput, Bool.false_eq_true, ite_false, hidden_first_tag] at tag
    cases hidden_first_tag_indices tag
    rfl
  · simp only [plannedInput, Bool.false_eq_true, ite_false, ite_true, hidden_first_tag, hidden_second_tag] at tag
    exact (tags_disjoint left.isLt right.isLt tag).elim
  · simp only [plannedInput, Bool.false_eq_true, ite_false, ite_true, hidden_first_tag, hidden_second_tag] at tag
    exact (tags_disjoint right.isLt left.isLt tag.symm).elim
  · simp only [plannedInput, ite_true, hidden_second_tag] at tag
    cases hidden_second_tag_indices tag
    rfl

end TwoPermutationPrototype.Sampling
