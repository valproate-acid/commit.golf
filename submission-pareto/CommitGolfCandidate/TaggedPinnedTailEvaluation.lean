import CommitGolfCandidate.TaggedPinnedTailCoupling
import CommitGolfCandidate.TwoPermutationHidingOpened

namespace TwoPermutationPrototype.Sampling
open OracleComp
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

local instance pinnedEvaluationDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

noncomputable def runPinnedRestricted (cache : Cache) (answers : List Block) :
    List InputPlan → ProbComp (List Block × Cache)
  | [] => pure (answers, cache)
  | plan :: rest => do
      let (reply, updated) ← pinnedRestrictedForward cache (plan answers)
      runPinnedRestricted updated (reply :: answers) rest

private theorem pinned_forward_cache_rows (cache : Cache) (input : Block) (result : Block × Cache)
    (present : result ∈ support (cache.forward input)) :
    result.2.entries.length ≤ cache.entries.length + 1 := by
  unfold PermutationCache.forward at present
  split at present
  · obtain ⟨reply, _, same⟩ := (mem_support_bind_iff _ _ _).mp present
    simp only [support_pure, Set.mem_singleton_iff] at same
    subst result
    rfl
  · simp only [support_pure, Set.mem_singleton_iff] at present
    subst result
    exact Nat.le_succ _

private theorem pinned_distance_support_le {β α : Type} (common : ProbComp β)
    (left right : β → ProbComp α) (cost : ℝ) (nonneg : 0 ≤ cost)
    (each : ∀ value ∈ support common, measureTVDist (left value) (right value) ≤ cost) :
    measureTVDist (common >>= left) (common >>= right) ≤ cost := by
  apply ENNReal.toReal_le_of_le_ofReal nonneg
  refine (measureETVDist_bind_left_le_tsum common left right).trans ?_
  calc
    _ ≤ ∑' x, Pr{let y ← common}[y = x] * ENNReal.ofReal cost := by
      apply ENNReal.tsum_le_tsum
      intro x
      by_cases present : x ∈ support common
      · exact mul_le_mul_of_nonneg_left
          ((ENNReal.le_ofReal_iff_toReal_le (measureETVDist_ne_top _ _) nonneg).2 (each x present)) zero_le
      · have zero : Pr{let y ← common}[y = x] = 0 :=
          (prEvent_eq_zero_iff common (· = x)).2 (fun y mem equal => present (equal ▸ mem))
        simp only [zero, zero_mul, le_refl]
    _ = _ := by rw [ENNReal.tsum_mul_right, tsum_prEvent_eq_one, one_mul]

/-- Every fresh forward restriction is charged only once through the full
adaptive execution. Plans can reuse cache rows and depend on all prior replies. -/
theorem pinned_adaptive_tail_restriction {α : Type} (cache : Cache) (answers : List Block)
    (plans : List InputPlan) (next : (List Block × Cache) → ProbComp α)
    (maximum : Nat) (room : cache.entries.length + plans.length ≤ maximum) (cap : maximum ≤ 2^121) :
    measureTVDist (runPinnedRestricted cache answers plans >>= next)
      (runPrepared cache answers plans >>= next) ≤
      (plans.length : ℝ) * ((maximum : ℝ)/2^1343) := by
  induction plans generalizing cache answers with
  | nil => simp [runPinnedRestricted, runPrepared]
  | cons plan rest ih =>
    let address := plan answers
    let restricted (result : Block × Cache) := runPinnedRestricted result.2 (result.1 :: answers) rest >>= next
    let normal (result : Block × Cache) := runPrepared result.2 (result.1 :: answers) rest >>= next
    let middle := cache.forward address >>= restricted
    have step : measureTVDist (pinnedRestrictedForward cache address >>= restricted) middle ≤
        (maximum : ℝ)/2^1343 := by
      have small : cache.entries.length ≤ maximum := by omega
      refine (pinned_restricted_forward_distance cache address (small.trans cap) restricted).trans ?_
      exact div_le_div_of_nonneg_right (by exact_mod_cast small) (by positivity)
    have tail : measureTVDist middle (cache.forward address >>= normal) ≤
        (rest.length : ℝ) * ((maximum : ℝ)/2^1343) := by
      refine pinned_distance_support_le (cache.forward address) _ _ _ (by positivity) ?_
      intro result present
      have grows := pinned_forward_cache_rows cache address result present
      have nextRoom : result.2.entries.length + rest.length ≤ maximum := by
        simp only [List.length_cons] at room
        omega
      exact ih result.2 (result.1 :: answers) nextRoom
    simp only [runPinnedRestricted, runPrepared, bind_assoc]
    change measureTVDist (pinnedRestrictedForward cache address >>= restricted)
      (cache.forward address >>= normal) ≤ _
    refine (measureTVDist_triangle _ middle _).trans ((add_le_add step tail).trans_eq ?_)
    rw [List.length_cons, Nat.cast_succ, add_mul, one_mul, add_comm]

theorem pinned_eager_tail_restriction {α : Type} (cache : Cache) (answers : List Block) (plans : List InputPlan)
    (next : List Block → BiPermutation Block → ProbComp α)
    (maximum : Nat) (room : cache.entries.length + plans.length ≤ maximum) (cap : maximum ≤ 2^121) :
    measureTVDist
      (do let prepared ← runPinnedRestricted cache answers plans
          let final ← prepared.2.sample
          next prepared.1 final.val)
      (do let original ← cache.sample
          runPlanned next original.val answers plans) ≤ (plans.length : ℝ) * ((maximum : ℝ)/2^1343) := by
  unfold measureTVDist
  rw [(prepared_posterior_equivalence next cache answers plans).evalDist_eq]
  exact pinned_adaptive_tail_restriction cache answers plans
    (fun prepared => prepared.2.sample >>= fun final => next prepared.1 final.val) maximum room cap

end TwoPermutationPrototype.Sampling
