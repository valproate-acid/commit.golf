import CommitGolfCandidate.TwoPermutationTaglessOpened
import CommitGolfCandidate.TwoPermutationTaglessMargin

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp MeasureTheory CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 850000
set_option exponentiation.threshold 2048

local instance {α : Type} : MeasurableSpace α := ⊤

def taglessHiddenSecondRow (digests : DigestTape) (messages : Index → Words 32) (i : Index)
    (key : PrivateLeafKey) : Row :=
  (taglessSecondAddress messages i key.2.1, key.2.2 ++ digests i)

def taglessHiddenRowsFor {positions : Positions} (digests : DigestTape)
    (messages : Index → Words 32) (hidden : HiddenTape positions) (indices : List (HiddenIndex positions)) : List Row :=
  indices.flatMap (fun i => [hiddenFirstRow messages i.val (hidden i),
    taglessHiddenSecondRow digests messages i.val (hidden i)])

noncomputable def taglessHiddenRows {positions : Positions} (digests : DigestTape)
    (messages : Index → Words 32) (hidden : HiddenTape positions) : List Row :=
  taglessHiddenRowsFor digests messages hidden (hiddenIndices positions)

private theorem tagless_coordinate_hit_le {positions : Positions} (i : HiddenIndex positions)
    (messages : Index → Words 32) (guess : Block) :
    Pr{let hidden ← sampleHiddenTape positions}[
      taglessSecondAddress messages i.val (hidden i).2.1 = guess] ≤ (1 : ENNReal)/2^832 := by
  let event (key : PrivateLeafKey) := taglessSecondAddress messages i.val key.2.1 = guess
  have sampled := uniform_tape_coordinate (ι := HiddenIndex positions) (α := PrivateLeafKey)
    (β := PrivateLeafKey) i (fun key => pure key)
  have selected := sampled.prEvent_eq event
  rw [bind_pure_comp, prEvent_map, bind_pure] at selected
  change Pr{let hidden ← sampleHiddenTape positions}[event (hidden i)] ≤ _
  refine selected.le.trans ?_
  rw [SampleableType.uniformSample_prod_eq_bind, SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  apply prEvent_bind_le_of_forall_le_of_support
  intro salt _
  have extract : (do let reply ← $ᵗ Block; let _ ← $ᵗ BitVec 1344; pure reply) =ᵈ ($ᵗ Block) := by
    trans (($ᵗ Block) >>= pure)
    · apply EvalDistEq.bind_right
      intro reply
      exact EvalDistEq.of_evalDist_eq (evalDist_bind_const _ _)
    · rw [bind_pure]
  have same := extract.prEvent_eq (fun reply => taglessSecondAddress messages i.val reply = guess)
  simp only [prEvent_bind_eq_tsum, bind_pure_comp, prEvent_map] at same
  apply le_trans _ (tagless_proposal_address_hit (taglessMessageTail (messages i.val)) guess)
  simp only [event, prEvent_bind_eq_tsum, bind_pure_comp, prEvent_map]
  exact same.le

theorem tagless_fixed_reference_second_hit_le (positions : Positions)
    (messages : Index → Words 32) (guess : Block) :
    Pr{let hidden ← sampleHiddenTape positions}[∃ i : HiddenIndex positions,
      taglessSecondAddress messages i.val (hidden i).2.1 = guess] ≤
      (2 : ENNReal)^24 * (1/2^832) := by
  classical
  let event (i : HiddenIndex positions) (hidden : HiddenTape positions) :=
    taglessSecondAddress messages i.val (hidden i).2.1 = guess
  let all := hiddenIndices positions
  have bound := prEvent_list_le all (sampleHiddenTape positions) event (1/2^832)
    (fun i _ => tagless_coordinate_hit_le i messages guess)
  have count : all.length ≤ 2^24 := Nat.le.intro (hidden_index_count positions)
  have castCount : (all.length : ENNReal) ≤ 2^24 := by exact_mod_cast count
  apply le_trans (b := Pr{let hidden ← sampleHiddenTape positions}[∃ i ∈ all, event i hidden])
  · apply prEvent_mono
    rintro hidden ⟨i, hit⟩
    exact ⟨i, by simp [all, hiddenIndices], hit⟩
  · exact bound.trans (mul_le_mul_of_nonneg_right castCount zero_le)

noncomputable def taglessObserverCharge : ENNReal := hiddenPairRate + (2 : ENNReal)^24 * (1/2^832)

theorem tagless_observer_charge_real_le : taglessObserverCharge.toReal ≤ (1 : ℝ)/2^127 := by
  unfold taglessObserverCharge hiddenPairRate
  repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  repeat rw [ENNReal.toReal_mul]
  repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_pow]

private theorem tagless_row_hit_cases {positions : Positions} (digests : DigestTape)
    (messages : Index → Words 32) (hidden : HiddenTape positions) (query : Row)
    (hit : rowHits (taglessHiddenRows digests messages hidden) query = true) :
    pairHitsHidden digests messages query hidden ∨ ∃ i : HiddenIndex positions,
      taglessSecondAddress messages i.val (hidden i).2.1 = query.1 := by
  classical
  simp only [rowHits, List.any_eq_true, taglessHiddenRows, taglessHiddenRowsFor, hiddenIndices, List.mem_flatMap,
    Finset.mem_toList, Finset.mem_univ, true_and, List.mem_cons, List.not_mem_nil, or_false,
    decide_eq_true_eq] at hit
  rcases hit with ⟨row, ⟨i, rfl | rfl⟩, input | output⟩
  · exact Or.inl (Or.inl ⟨i, input.symm⟩)
  · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨i, output.symm⟩)))
  · exact Or.inr ⟨i, input.symm⟩
  · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨i, output.symm⟩)))

theorem tagless_fixed_reference_hit_le (positions : Positions) (digests : DigestTape)
    (messages : Index → Words 32) (query : Row) :
    Pr{let hidden ← sampleHiddenTape positions}[rowHits (taglessHiddenRows digests messages hidden) query = true] ≤
      taglessObserverCharge := by
  refine (prEvent_mono _ (p := fun hidden => rowHits (taglessHiddenRows digests messages hidden) query = true)
    (q := fun hidden => pairHitsHidden digests messages query hidden ∨ ∃ i : HiddenIndex positions,
      taglessSecondAddress messages i.val (hidden i).2.1 = query.1)
    (fun hidden => tagless_row_hit_cases digests messages hidden query)).trans ?_
  exact (prEvent_or_le _ _ _).trans (add_le_add (fixed_reference_pair_hit_le positions digests messages query)
    (tagless_fixed_reference_second_hit_le positions messages query.1))

theorem tagless_independent_observer_hits (positions : Positions) (digests : DigestTape)
    (messages : Index → Words 32) (compress : Compression) (p : BiPermutation Block)
    {α : Type} (observer : OracleComp World α) (budget : Nat) (bounded : QueryBounded observer budget) :
    Pr{let result ← (do let hidden ← sampleHiddenTape positions
                        let rows := taglessHiddenRows digests messages hidden
                        flaggedRun (fixedOracle compress p) (marksReferencePair p rows) observer)}[
      result.2.2 = true] ≤ (budget : ENNReal) * taglessObserverCharge := by
  classical
  let oracle := fixedOracle compress p
  let traced := fixedOracleRun oracle (tracePermutation observer)
  let flag (hidden : HiddenTape positions) (result : α × List Row) : α × Unit × Bool :=
    (result.1, (), result.2.any (rowHits (taglessHiddenRows digests messages hidden)))
  have reordered := EvalDistEq.of_evalDist_eq
    (distribution_bind_comm (sampleHiddenTape positions) traced (fun hidden result => pure (flag hidden result)))
  have eventEqual := reordered.prEvent_eq (fun flagged => flagged.2.2 = true)
  have expand (hidden : HiddenTape positions) :
      flaggedRun oracle (marksReferencePair p (taglessHiddenRows digests messages hidden)) observer =
        traced >>= fun result => pure (flag hidden result) := by
    unfold oracle traced flag
    rw [flagged_reference_trace]
    simp only [Bool.false_or, map_eq_bind_pure_comp]
    rfl
  simp only [← show oracle = fixedOracle compress p from rfl, expand]
  rw [eventEqual]
  apply prEvent_bind_le_of_forall_le_of_support
  intro result present
  simp only [bind_pure_comp, prEvent_map, flag, List.any_eq_true]
  have cost := prEvent_list_le result.2 (sampleHiddenTape positions)
    (fun row hidden => rowHits (taglessHiddenRows digests messages hidden) row = true)
    taglessObserverCharge (fun row _ => tagless_fixed_reference_hit_le positions digests messages row)
  refine cost.trans (mul_le_mul_of_nonneg_right ?_ zero_le)
  exact_mod_cast trace_permutation_length oracle observer budget bounded result present

theorem tagless_independent_observer_distance (positions : Positions) (digests : DigestTape)
    (messages : Index → Words 32) (compress : Compression) (p : BiPermutation Block)
    {α : Type} (observer : OracleComp World α) (budget : Nat) (bounded : QueryBounded observer budget) :
    measureTVDist
      (sampleHiddenTape positions >>= fun _ => fixedOracleRun (fixedOracle compress p) observer)
      (sampleHiddenTape positions >>= fun hidden => fixedOracleRun
        (fixedOracle compress (p.programRows (taglessHiddenRows digests messages hidden))) observer) ≤
      (budget : ℝ)/2^127 := by
  classical
  refine (distance_bind_le_averaged_bad (sampleHiddenTape positions) _ _
    (fun hidden => flaggedRun (fixedOracle compress p)
      (marksReferencePair p (taglessHiddenRows digests messages hidden)) observer)
    (fun hidden => programming_distance_le_reference_hit compress p (taglessHiddenRows digests messages hidden) observer)).trans ?_
  have hit := tagless_independent_observer_hits positions digests messages compress p observer budget bounded
  refine (ENNReal.toReal_mono (by unfold taglessObserverCharge hiddenPairRate; finiteness) hit).trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ← mul_one_div]
  exact mul_le_mul_of_nonneg_left tagless_observer_charge_real_le (by positivity)

end TwoPermutationPrototype.Sampling
