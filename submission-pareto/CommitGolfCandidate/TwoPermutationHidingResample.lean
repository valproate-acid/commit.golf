import CommitGolfCandidate.TwoPermutationHidingProgramming
import CommitGolfCandidate.TwoPermutationHidingHits
import VCVio.OracleComp.EvalDist.Sum

/-! Couple a uniform full-domain proposal with a uniform fresh proposal.
On the accepted subset the coupling uses the exact same draw. -/
namespace TwoPermutationPrototype.Sampling
open OracleComp

def repairDraw {α : Type} (good : α → Prop) [DecidablePred good] (draw : α)
    (fallback : Subtype good) : Subtype good :=
  if inside : good draw then ⟨draw, inside⟩ else fallback

private def swapAccepted {α : Type} (good : α → Prop) [DecidablePred good]
    (pair : α × Subtype good) : α × Subtype good :=
  if inside : good pair.1 then (pair.2.val, ⟨pair.1, inside⟩) else pair

private theorem swap_accepted_involutive {α : Type} (good : α → Prop) [DecidablePred good] :
    Function.Involutive (swapAccepted good) := by
  rintro ⟨draw, fallback⟩
  by_cases inside : good draw
  · simp only [swapAccepted, inside, dite_true, fallback.property]
  · simp only [swapAccepted, inside, dite_false]

private def repairEquiv {α : Type} (good : α → Prop) [DecidablePred good] :
    Transport (α × Subtype good) (α × Subtype good) where
  toFun := swapAccepted good
  invFun := swapAccepted good
  leftInverse := swap_accepted_involutive good
  rightInverse := swap_accepted_involutive good

private theorem swap_second_is_repair {α : Type} (good : α → Prop) [DecidablePred good]
    (draw : α) (fallback : Subtype good) :
    (swapAccepted good (draw, fallback)).2 = repairDraw good draw fallback := by
  by_cases inside : good draw <;> simp [swapAccepted, repairDraw, inside]

theorem repair_uniform {α β : Type} [SampleableType α] (good : α → Prop) [DecidablePred good]
    [SampleableType (Subtype good)] (next : Subtype good → ProbComp β) :
    (do let draw ← $ᵗ α
        let fallback ← $ᵗ Subtype good
        next (repairDraw good draw fallback)) =ᵈ
      (do let accepted ← $ᵗ Subtype good; next accepted) := by
  have transport := (uniform_transport_bind (repairEquiv good) (fun pair => next pair.2)).symm
  refine EvalDistEq.trans ?repair (EvalDistEq.trans transport ?drop)
  case repair =>
    rw [SampleableType.uniformSample_prod_eq_bind]
    simp only [bind_assoc, pure_bind]
    apply EvalDistEq.bind_right
    intro draw
    apply EvalDistEq.bind_right
    intro fallback
    change next (repairDraw good draw fallback) =ᵈ next (swapAccepted good (draw, fallback)).2
    rw [swap_second_is_repair]
  case drop =>
    rw [SampleableType.uniformSample_prod_eq_bind]
    simp only [bind_assoc, pure_bind]
    let : MeasurableSpace β := ⊤
    exact EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_const _ _)


open MeasureTheory

local instance resampleDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

theorem repair_uniform_distance {α β : Type} [SampleableType α] (good : α → Prop) [DecidablePred good]
    [SampleableType (Subtype good)] (actual : Subtype good → ProbComp β) (ideal : α → ProbComp β)
    (agree : ∀ draw (valid : good draw), actual ⟨draw, valid⟩ =ᵈ ideal draw) :
    measureTVDist (($ᵗ Subtype good) >>= actual) (($ᵗ α) >>= ideal) ≤
      (Pr{let draw ← $ᵗ α}[¬ good draw]).toReal := by
  unfold measureTVDist
  rw [← (repair_uniform good actual).evalDist_eq]
  change measureTVDist (($ᵗ α) >>= fun draw => ($ᵗ Subtype good) >>= fun fallback =>
    actual (repairDraw good draw fallback)) (($ᵗ α) >>= ideal) ≤ _
  apply measureTVDist_bind_left_le_prEvent_of_evalDistEq
  intro draw notBad
  have valid := not_not.mp notBad
  simp only [repairDraw, valid, dite_true]
  exact (EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_const _ _)).trans (agree draw valid)

/-- Replacing the fresh answer for one new input by a full-domain uniform proposal
costs at most one collision with a previously assigned output. -/
theorem fresh_program_step_distance (cache : Cache) (input : Block) (fresh : UnusedInput cache.entries input)
    {β : Type} (next : Block → BiPermutation Block → ProbComp β) :
    measureTVDist
      (do let p ← cache.sample; next (p.val.forward input) p.val)
      (do let proposal ← $ᵗ Block
          let p ← cache.sample
          next proposal (p.val.program input proposal)) ≤
      ((cache.entries.length : ENNReal) / 2 ^ 1600).toReal := by
  classical
  let : SampleableType (RemainingOutputs cache.entries) := cache.forwardSampler input fresh
  have reveal := cache.forward_step_eq input next
  unfold PermutationCache.forward at reveal
  simp only [fresh, dite_true, bind_assoc, pure_bind] at reveal
  have repacked :
      (do let p ← cache.sample; next (p.val.forward input) p.val) =ᵈ
      (do let output ← $ᵗ RemainingOutputs cache.entries
          let p ← cache.sample
          next output.val (p.val.program input output.val)) := by
    refine reveal.trans (EvalDistEq.bind_right _ fun output => ?_)
    exact (program_uniform_completion cache input fresh output (next output.val)).symm
  unfold measureTVDist
  rw [repacked.evalDist_eq]
  change measureTVDist (($ᵗ RemainingOutputs cache.entries) >>= _) (($ᵗ Block) >>= _) ≤ _
  refine (repair_uniform_distance (UnusedOutput cache.entries) _ _ (fun _ _ => by rfl)).trans ?_
  apply ENNReal.toReal_mono (by finiteness)
  have bad : (fun proposal => ¬ UnusedOutput cache.entries proposal) =
      (fun proposal => ∃ row ∈ cache.entries, proposal = row.2) := by
    funext proposal
    simp [UnusedOutput, eq_comm]
  rw [bad]
  simpa only [mul_one_div] using
    prEvent_list_le cache.entries ($ᵗ Block) (fun row proposal => proposal = row.2)
      (1 / 2 ^ 1600) (fun row _ => public_guess_first_output_le row.2)

end TwoPermutationPrototype.Sampling
