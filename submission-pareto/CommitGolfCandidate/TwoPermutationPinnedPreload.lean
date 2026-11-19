import CommitGolfCandidate.TaggedPinnedWorldEval

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

local instance {α : Type} : MeasurableSpace α := ⊤

theorem pinned_restrict_preload {α : Type} (cache : Cache) (addresses : List Block)
    (observe : BiPermutation Block → ProbComp α)
    (maximum : Nat) (room : cache.entries.length + addresses.length ≤ maximum) (cap : maximum ≤ 2^121) :
    measureTVDist
      (do let first ← runPinnedFull cache [] (pinnedConstantPlans addresses)
          let p ← first.2.sample
          observe p.val)
      (cache.sample >>= fun p => observe p.val) ≤
      (addresses.length : ℝ) * ((maximum : ℝ) / 2^1343) := by
  let plans := pinnedConstantPlans addresses
  have lengths : (plans.map pinnedLiftPlan).length = addresses.length := by
    simp [plans, pinnedConstantPlans]
  have comparison :=
    pinned_eager_tail_restriction cache [] (plans.map pinnedLiftPlan) (fun _ => observe)
      maximum (by simpa only [lengths] using room) cap
  rw [lengths] at comparison
  let next (last : Cache) := last.sample >>= fun p => observe p.val
  have low := pinned_full_from_restricted cache [] plans (fun _ => next)
  unfold next at low
  simp only [List.map_nil] at low
  have high : (cache.sample >>= fun p => runPlanned (fun _ => observe) p.val [] (plans.map pinnedLiftPlan)) =
      (cache.sample >>= fun p => observe p.val) := by
    apply bind_congr
    intro p
    exact pinned_constant_plans_run p.val [] addresses (fun _ => observe)
  simpa only [low, high, plans] using comparison

theorem pinned_nonadaptive_full_append (first second : List PinnedHighPlan)
    (cache : Cache) (answers : List (BitVec 1344)) :
    runPinnedFull cache answers (first ++ second) =
      (do let middle ← runPinnedFull cache answers first
          runPinnedFull middle.2 middle.1 second) := by
  induction first generalizing cache answers with
  | nil =>
    simp only [List.nil_append, runPinnedFull, pure_bind]
  | cons plan rest ih =>
    simp only [List.cons_append, runPinnedFull, bind_assoc]
    apply bind_congr
    intro result
    exact ih result.2 (pinnedOutputTail result.1 :: answers)

theorem pinned_constant_full_forget (addresses : List Block) (cache : Cache)
    (history : List (BitVec 1344)) :
    (Prod.snd <$> runPinnedFull cache history (pinnedConstantPlans addresses)) =
      (Prod.snd <$> runPinnedFull cache [] (pinnedConstantPlans addresses)) := by
  suffices same : ∀ (initial : Cache) (left right : List (BitVec 1344)),
      (Prod.snd <$> runPinnedFull initial left (pinnedConstantPlans addresses)) =
        (Prod.snd <$> runPinnedFull initial right (pinnedConstantPlans addresses)) by
    exact same cache history []
  induction addresses with
  | nil =>
    intro initial left right
    simp only [pinnedConstantPlans, List.map_nil, runPinnedFull, map_pure]
  | cons next rest ih =>
    intro initial left right
    simp only [pinnedConstantPlans, List.map_cons, runPinnedFull, map_bind]
    apply bind_congr
    intro result
    exact ih result.2 (pinnedOutputTail result.1 :: left) (pinnedOutputTail result.1 :: right)

end TwoPermutationPrototype.Sampling
