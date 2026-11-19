import CommitGolfCandidate.TwoPermutationHidingPair
import CommitGolfCandidate.TwoPermutationHidingTrace
import CommitGolfCandidate.HidingHiddenQuery

/-! Average the fixed-pair bound over the unchanged adaptive observer's entire
trace. The hidden tape is drawn independently of that trace. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

local instance observerDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

noncomputable def hiddenIndices (positions : Positions) : List (HiddenIndex positions) :=
  (Finset.univ : Finset (HiddenIndex positions)).toList

def hiddenRowsFor {positions : Positions} (digests : DigestTape)
    (messages : Index → Words 32) (hidden : HiddenTape positions) (indices : List (HiddenIndex positions)) : List Row :=
  indices.flatMap (fun index =>
    [hiddenFirstRow messages index.val (hidden index), hiddenSecondRow digests messages index.val (hidden index)])

noncomputable def hiddenRows {positions : Positions} (digests : DigestTape)
    (messages : Index → Words 32) (hidden : HiddenTape positions) : List Row :=
  hiddenRowsFor digests messages hidden (hiddenIndices positions)

private theorem rowHits_hidden_iff {positions : Positions} (digests : DigestTape)
    (messages : Index → Words 32) (hidden : HiddenTape positions) (query : Row) :
    rowHits (hiddenRows digests messages hidden) query = true ↔
      pairHitsHidden digests messages query hidden := by
  classical
  simp only [rowHits, List.any_eq_true, hiddenRows, hiddenRowsFor, hiddenIndices, List.mem_flatMap,
    Finset.mem_toList, Finset.mem_univ, true_and, List.mem_cons, List.not_mem_nil, or_false,
    decide_eq_true_eq, pairHitsHidden]
  constructor
  · rintro ⟨row, ⟨i, rfl | rfl⟩, input | output⟩
    · exact Or.inl ⟨i, input.symm⟩
    · exact Or.inr (Or.inr (Or.inl ⟨i, output.symm⟩))
    · exact Or.inr (Or.inl ⟨i, input.symm⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨i, output.symm⟩))
  · rintro (⟨i, input⟩ | ⟨i, input⟩ | ⟨i, output⟩ | ⟨i, output⟩)
    · exact ⟨_, ⟨i, Or.inl rfl⟩, Or.inl input.symm⟩
    · exact ⟨_, ⟨i, Or.inr rfl⟩, Or.inl input.symm⟩
    · exact ⟨_, ⟨i, Or.inl rfl⟩, Or.inr output.symm⟩
    · exact ⟨_, ⟨i, Or.inr rfl⟩, Or.inr output.symm⟩

theorem independent_hidden_observer_hits (positions : Positions) (digests : DigestTape)
    (messages : Index → Words 32) (compress : Compression) (p : BiPermutation Block)
    {α : Type} (observer : OracleComp World α) (budget : Nat) (bounded : QueryBounded observer budget) :
    Pr{let result ← (do let hidden ← sampleHiddenTape positions
                        let rows := hiddenRows digests messages hidden
                        flaggedRun (fixedOracle compress p) (marksReferencePair p rows) observer)}[
      result.2.2 = true] ≤ (budget : ENNReal) * hiddenPairRate := by
  classical
  let oracle := fixedOracle compress p
  let traced := fixedOracleRun oracle (tracePermutation observer)
  let flag (hidden : HiddenTape positions) (result : α × List Row) : α × Unit × Bool :=
    (result.1, (), result.2.any (rowHits (hiddenRows digests messages hidden)))
  have reordered := EvalDistEq.of_evalDist_eq
    (distribution_bind_comm (sampleHiddenTape positions) traced (fun hidden result => pure (flag hidden result)))
  have eventEqual := reordered.prEvent_eq (fun flagged => flagged.2.2 = true)
  have expand (hidden : HiddenTape positions) :
      flaggedRun oracle (marksReferencePair p (hiddenRows digests messages hidden)) observer =
        traced >>= fun result => pure (flag hidden result) := by
    unfold oracle traced flag
    rw [flagged_reference_trace]
    simp only [Bool.false_or, map_eq_bind_pure_comp]
    rfl
  simp only [← show oracle = fixedOracle compress p from rfl, expand]
  rw [eventEqual]
  apply prEvent_bind_le_of_forall_le_of_support
  intro result present
  simp only [bind_pure_comp, prEvent_map, flag, List.any_eq_true, rowHits_hidden_iff]
  have cost := fixed_reference_trace_hit_le positions digests messages result.2
  refine cost.trans (mul_le_mul_of_nonneg_right ?_ zero_le)
  exact_mod_cast trace_permutation_length oracle observer budget bounded result present

theorem independent_hidden_observer_distance (positions : Positions) (digests : DigestTape)
    (messages : Index → Words 32) (compress : Compression) (p : BiPermutation Block)
    {α : Type} (observer : OracleComp World α) (budget : Nat) (bounded : QueryBounded observer budget) :
    measureTVDist
      (sampleHiddenTape positions >>= fun _ => fixedOracleRun (fixedOracle compress p) observer)
      (sampleHiddenTape positions >>= fun hidden => fixedOracleRun
        (fixedOracle compress (p.programRows (hiddenRows digests messages hidden))) observer) ≤
      ((budget : ENNReal) * hiddenPairRate).toReal := by
  classical
  refine (distance_bind_le_averaged_bad (sampleHiddenTape positions) _ _
    (fun hidden => flaggedRun (fixedOracle compress p)
      (marksReferencePair p (hiddenRows digests messages hidden)) observer)
    (fun hidden => programming_distance_le_reference_hit compress p (hiddenRows digests messages hidden) observer)).trans ?_
  exact ENNReal.toReal_mono (by unfold hiddenPairRate; finiteness)
    (independent_hidden_observer_hits positions digests messages compress p observer budget bounded)

end TwoPermutationPrototype.Sampling
