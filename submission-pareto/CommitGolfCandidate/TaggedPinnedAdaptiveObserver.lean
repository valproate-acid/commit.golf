import CommitGolfCandidate.TaggedPinnedObserver
import CommitGolfCandidate.TwoPermutationHidingSequence

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
open scoped ENNReal
set_option maxRecDepth 8192

local instance pinnedAdaptiveDiscrete {α : Type} : MeasurableSpace α := ⊤

theorem pinned_adaptive_reference_hits {α : Type} (sample : ProbComp (List Row)) (rate : ENNReal)
    (compress : Compression) (p : BiPermutation Block) (observer : OracleComp World α)
    (budget : Nat) (bounded : QueryBounded observer budget)
    (fixed : ∀ row, Pr{let rows ← sample}[rowHits rows row = true] ≤ rate) :
    Pr{let flagged ← (do let rows ← sample
                         flaggedRun (fixedOracle compress p) (marksReferencePair p rows) observer)}[
      flagged.2.2 = true] ≤ (budget : ENNReal) * rate := by
  classical
  let oracle := fixedOracle compress p
  let traced := fixedOracleRun oracle (tracePermutation observer)
  let mark (rows : List Row) (result : α × List Row) : α × Unit × Bool :=
    (result.1, (), result.2.any (rowHits rows))
  have order := EvalDistEq.of_evalDist_eq
    (distribution_bind_comm sample traced (fun rows trace => pure (mark rows trace)))
  have expand (rows : List Row) :
      flaggedRun oracle (marksReferencePair p rows) observer =
        traced >>= fun result => pure (mark rows result) := by
    unfold oracle traced mark
    rw [flagged_reference_trace]
    simp only [Bool.false_or, map_eq_bind_pure_comp]
    rfl
  simp only [← show oracle = fixedOracle compress p from rfl, expand]
  rw [order.prEvent_eq (fun flagged => flagged.2.2 = true)]
  apply prEvent_bind_le_of_forall_le_of_support
  intro trace present
  simp only [bind_pure_comp, prEvent_map, mark, List.any_eq_true]
  have limit := trace_permutation_length oracle observer budget bounded trace present
  exact (prEvent_list_le trace.2 sample (fun row rows => rowHits rows row = true) rate (fun row _ => fixed row)).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast limit) zero_le)

theorem pinned_adaptive_programmed_distance {α : Type} (sample : ProbComp (List Row)) (rate : ENNReal)
    (finite : rate ≠ ∞) (compress : Compression) (p : BiPermutation Block) (observer : OracleComp World α)
    (budget : Nat) (bounded : QueryBounded observer budget)
    (fixed : ∀ row, Pr{let rows ← sample}[rowHits rows row = true] ≤ rate) :
    measureTVDist
      (fixedOracleRun (fixedOracle compress p) observer)
      (sample >>= fun rows => fixedOracleRun (fixedOracle compress (p.programRows rows)) observer) ≤
      ((budget : ENNReal) * rate).toReal := by
  have held := EvalDistEq.of_evalDist_eq (evalDist_bind_const sample (fixedOracleRun (fixedOracle compress p) observer))
  unfold measureTVDist
  rw [← held.evalDist_eq]
  change measureTVDist (sample >>= fun _ => fixedOracleRun (fixedOracle compress p) observer) _ ≤ _
  rw [measureTVDist_eq_toReal_measureETVDist]
  apply ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) finite)
  refine (distance_averaged_event sample _ _
    (fun rows => flaggedRun (fixedOracle compress p) (marksReferencePair p rows) observer)
    (fun result => result.2.2 = true) ?_).trans
    (pinned_adaptive_reference_hits sample rate compress p observer budget bounded fixed)
  intro rows
  have step := programming_distance_le_reference_hit compress p rows observer
  rw [measureTVDist_eq_toReal_measureETVDist] at step
  exact (ENNReal.toReal_le_toReal (measureETVDist_ne_top _ _)
    (ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ∞) (prEvent_le_one _))).mp step

end TwoPermutationPrototype.Sampling
