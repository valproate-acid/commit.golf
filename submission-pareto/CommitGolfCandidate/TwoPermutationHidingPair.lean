import CommitGolfCandidate.TwoPermutationHidingTape

/-! Per-query detection bound after exposing the commitments of all leaves. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp MeasureTheory
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

set_option exponentiation.threshold 2048

abbrev HiddenIndex (positions : Positions) := {i : Index // i ∉ positions}

def hiddenFirstRow (messages : Index → Words 32) (i : Index) (key : PrivateLeafKey) : Row :=
  (hiddenFirstInput i (messages i) key.1, key.2.1)

def hiddenSecondRow (digests : DigestTape) (messages : Index → Words 32) (i : Index)
    (key : PrivateLeafKey) : Row :=
  (hiddenSecondInput i (messages i) key.2.1, key.2.2 ++ digests i)

def pairHitsHidden {positions : Positions} (digests : DigestTape) (messages : Index → Words 32)
    (query : Row) (hidden : HiddenTape positions) : Prop :=
  (∃ i : HiddenIndex positions, (hiddenFirstRow messages i (hidden i)).1 = query.1) ∨
  (∃ i : HiddenIndex positions, (hiddenSecondRow digests messages i (hidden i)).1 = query.1) ∨
  (∃ i : HiddenIndex positions, (hiddenFirstRow messages i (hidden i)).2 = query.2) ∨
  (∃ i : HiddenIndex positions, (hiddenSecondRow digests messages i (hidden i)).2 = query.2)

private theorem coordinate_probability {positions : Positions} (index : HiddenIndex positions)
    (event : PrivateLeafKey → Prop) :
    Pr{let hidden ← sampleHiddenTape positions}[event (hidden index)] =
      Pr{let key ← $ᵗ PrivateLeafKey}[event key] := by
  have sampled := uniform_tape_coordinate (ι := HiddenIndex positions) (α := PrivateLeafKey)
    (β := PrivateLeafKey) index (fun key => pure key)
  have eventEqual := sampled.prEvent_eq event
  rw [bind_pure_comp, prEvent_map, bind_pure] at eventEqual
  exact eventEqual

private theorem tagged_event_le {ι α : Type} (sample : ProbComp α)
    (event : ι → α → Prop) {tag : ι → Prop} (unique : ∀ i j, tag i → tag j → i = j)
    (impliesTag : ∀ i key, event i key → tag i) (rate : ENNReal)
    (bound : ∀ i, Pr{let key ← sample}[event i key] ≤ rate) :
    Pr{let key ← sample}[∃ i, event i key] ≤ rate := by
  classical
  by_cases hasTag : ∃ i, tag i
  · obtain ⟨selected, fitted⟩ := hasTag
    refine (prEvent_mono _ (p := fun key => ∃ i, event i key)
      (q := event selected) ?_).trans (bound selected)
    rintro key ⟨i, hit⟩
    rwa [← unique i selected (impliesTag i key hit) fitted]
  · have zero : Pr{let key ← sample}[∃ i, event i key] = 0 :=
      prEvent_eq_zero_of_forall_mem_support _ _ (fun key _ hit => by
        obtain ⟨i, hit⟩ := hit
        exact hasTag ⟨i, impliesTag i key hit⟩)
    rw [zero]
    exact zero_le

private theorem drop_independent_suffix {α β : Type} (left : ProbComp α) (right : ProbComp β) :
    (do let value ← left; let _ ← right; pure value) =ᵈ left := by
  trans (left >>= pure)
  · apply EvalDistEq.bind_right
    intro value
    let : MeasurableSpace α := ⊤
    exact EvalDistEq.of_evalDist_eq (evalDist_bind_const right (pure value))
  · rw [bind_pure]

private theorem key_first_input {positions : Positions} (i : HiddenIndex positions)
    (messages : Index → Words 32) (guess : Block) :
    Pr{let hidden ← sampleHiddenTape positions}[(hiddenFirstRow messages i (hidden i)).1 = guess] ≤
      (1 : ENNReal) / 2 ^ 128 := by
  rw [coordinate_probability i (fun key => (hiddenFirstRow messages i key).1 = guess)]
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [hiddenFirstRow]
  apply le_trans _ (public_guess_first_input_le i (messages i) guess)
  have equal := (drop_independent_suffix ($ᵗ BitVec 128) ($ᵗ (Block × BitVec 1344))).prEvent_eq
    (fun salt => hiddenFirstInput i (messages i) salt = guess)
  exact equal.le

private theorem key_second_input {positions : Positions} (i : HiddenIndex positions)
    (digests : DigestTape) (messages : Index → Words 32) (guess : Block) :
    Pr{let hidden ← sampleHiddenTape positions}[(hiddenSecondRow digests messages i (hidden i)).1 = guess] ≤
      (1 : ENNReal) / 2 ^ 768 := by
  rw [coordinate_probability i (fun key => (hiddenSecondRow digests messages i key).1 = guess)]
  rw [SampleableType.uniformSample_prod_eq_bind, SampleableType.uniformSample_prod_eq_bind]
  simp only [hiddenSecondRow, bind_assoc, pure_bind]
  apply prEvent_bind_le_of_forall_le_of_support
  intro salt _
  apply le_trans _ (public_guess_second_input_le i (messages i) guess)
  have equal := (drop_independent_suffix ($ᵗ Block) ($ᵗ BitVec 1344)).prEvent_eq
    (fun reply => hiddenSecondInput i (messages i) reply = guess)
  exact equal.le

private theorem key_first_output {positions : Positions} (i : HiddenIndex positions)
    (messages : Index → Words 32) (guess : Block) :
    Pr{let hidden ← sampleHiddenTape positions}[(hiddenFirstRow messages i (hidden i)).2 = guess] ≤
      (1 : ENNReal) / 2 ^ 1600 := by
  rw [coordinate_probability i (fun key => (hiddenFirstRow messages i key).2 = guess)]
  rw [SampleableType.uniformSample_prod_eq_bind, SampleableType.uniformSample_prod_eq_bind]
  simp only [hiddenFirstRow, bind_assoc, pure_bind]
  apply prEvent_bind_le_of_forall_le_of_support
  intro salt _
  apply le_trans _ (public_guess_first_output_le guess)
  have equal := (drop_independent_suffix ($ᵗ Block) ($ᵗ BitVec 1344)).prEvent_eq (· = guess)
  exact equal.le

private theorem key_second_output {positions : Positions} (i : HiddenIndex positions)
    (digests : DigestTape) (messages : Index → Words 32) (guess : Block) :
    Pr{let hidden ← sampleHiddenTape positions}[(hiddenSecondRow digests messages i (hidden i)).2 = guess] ≤
      (1 : ENNReal) / 2 ^ 1344 := by
  rw [coordinate_probability i (fun key => (hiddenSecondRow digests messages i key).2 = guess)]
  rw [SampleableType.uniformSample_prod_eq_bind, SampleableType.uniformSample_prod_eq_bind]
  simp only [hiddenSecondRow, bind_assoc, pure_bind]
  apply prEvent_bind_le_of_forall_le_of_support
  intro salt _
  apply prEvent_bind_le_of_forall_le_of_support
  intro firstReply _
  change Pr{let _ ← _}[_] ≤ _
  rw [bind_pure_comp, prEvent_map]
  exact public_guess_second_output_le (digests i) guess

noncomputable def hiddenPairRate : ENNReal :=
  1 / 2 ^ 128 + 1 / 2 ^ 768 + (2 ^ 24 : ENNReal) * (1 / 2 ^ 1600 + 1 / 2 ^ 1344)

theorem fixed_reference_pair_hit_le (positions : Positions) (digests : DigestTape)
    (messages : Index → Words 32) (query : Row) :
    Pr{let hidden ← sampleHiddenTape positions}[pairHitsHidden digests messages query hidden] ≤ hiddenPairRate := by
  classical
  let sample := sampleHiddenTape positions
  let firstInput : HiddenTape positions → Prop := fun hidden =>
    ∃ i : HiddenIndex positions, (hiddenFirstRow messages i (hidden i)).1 = query.1
  let secondInput : HiddenTape positions → Prop := fun hidden =>
    ∃ i : HiddenIndex positions, (hiddenSecondRow digests messages i (hidden i)).1 = query.1
  let firstOutput (i : HiddenIndex positions) (hidden : HiddenTape positions) :=
    (hiddenFirstRow messages i (hidden i)).2 = query.2
  let secondOutput (i : HiddenIndex positions) (hidden : HiddenTape positions) :=
    (hiddenSecondRow digests messages i (hidden i)).2 = query.2
  have aBound : Pr{let hidden ← sample}[firstInput hidden] ≤ (1 : ENNReal) / 2 ^ 128 := by
    apply tagged_event_le (tag := fun i : HiddenIndex positions => firstTag i.val.val = query.1.extractLsb' 0 64)
    · exact fun i j left right => Subtype.ext (hidden_first_tag_indices (left.trans right.symm))
    · intro i hidden hit
      have tag := hidden_first_tag i (messages i) (hidden i).1
      change hiddenFirstInput i (messages i) (hidden i).1 = query.1 at hit
      rw [hit] at tag
      exact tag.symm
    · intro i
      exact key_first_input i messages query.1
  have bBound : Pr{let hidden ← sample}[secondInput hidden] ≤ (1 : ENNReal) / 2 ^ 768 := by
    apply tagged_event_le (tag := fun i : HiddenIndex positions => secondTag i.val.val = query.1.extractLsb' 0 64)
    · exact fun i j left right => Subtype.ext (hidden_second_tag_indices (left.trans right.symm))
    · intro i hidden hit
      have tag := hidden_second_tag i (messages i) (hidden i).2.1
      change hiddenSecondInput i (messages i) (hidden i).2.1 = query.1 at hit
      rw [hit] at tag
      exact tag.symm
    · intro i
      exact key_second_input i digests messages query.1
  have number : Fintype.card (HiddenIndex positions) ≤ 2 ^ 24 := by
    have bound := Fintype.card_le_of_injective (fun i : HiddenIndex positions => i.val) Subtype.val_injective
    have indexSize : Fintype.card Index = 2 ^ 24 := Fintype.card_fin _
    exact bound.trans_eq indexSize
  have castNumber : (Fintype.card (HiddenIndex positions) : ENNReal) ≤ 2 ^ 24 := by
    have casted : (Fintype.card (HiddenIndex positions) : ENNReal) ≤ ((2 ^ 24 : Nat) : ENNReal) :=
      Nat.cast_le.mpr number
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using casted
  have output_cost {which : HiddenIndex positions → HiddenTape positions → Prop} (cost : ENNReal)
      (each : ∀ i, Pr{let hidden ← sample}[which i hidden] ≤ cost) :
      Pr{let hidden ← sample}[∃ i, which i hidden] ≤ (2 ^ 24 : ENNReal) * cost := by
    calc
      _ = Pr{let hidden ← sample}[∃ i ∈ (Finset.univ : Finset (HiddenIndex positions)), which i hidden] := by simp
      _ ≤ ∑ i : HiddenIndex positions, Pr{let hidden ← sample}[which i hidden] :=
        prEvent_exists_finset_le _ _ _
      _ ≤ ∑ _i : HiddenIndex positions, cost := Finset.sum_le_sum (fun i _ => each i)
      _ = (Fintype.card (HiddenIndex positions) : ENNReal) * cost := by simp [nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right castNumber zero_le
  have yBound := output_cost (which := firstOutput) (1 / 2 ^ 1600) (fun i => key_first_output i messages query.2)
  have zBound := output_cost (which := secondOutput) (1 / 2 ^ 1344)
    (fun i => key_second_output i digests messages query.2)
  let y := fun hidden => ∃ i, firstOutput i hidden
  let z := fun hidden => ∃ i, secondOutput i hidden
  have yz := (prEvent_or_le sample y z).trans (add_le_add yBound zBound)
  have byz := (prEvent_or_le sample secondInput (fun hidden => y hidden ∨ z hidden)).trans (add_le_add bBound yz)
  change Pr{let hidden ← sample}[firstInput hidden ∨ secondInput hidden ∨ y hidden ∨ z hidden] ≤ _
  refine (prEvent_or_le sample firstInput _).trans ((add_le_add aBound byz).trans_eq ?_)
  simp [hiddenPairRate, mul_add, add_assoc]


theorem fixed_reference_trace_hit_le (positions : Positions) (digests : DigestTape)
    (messages : Index → Words 32) (trace : List Row) :
    Pr{let hidden ← sampleHiddenTape positions}[∃ row ∈ trace, pairHitsHidden digests messages row hidden] ≤
      (trace.length : ENNReal) * hiddenPairRate :=
  prEvent_list_le trace (sampleHiddenTape positions) (fun row hidden => pairHitsHidden digests messages row hidden)
    hiddenPairRate (fun row _ => fixed_reference_pair_hit_le positions digests messages row)

end TwoPermutationPrototype.Sampling
