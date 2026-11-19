import CommitGolfCandidate.TaggedPinnedPlanning
import CommitGolfCandidate.TaggedPinnedRestrictedFrame

namespace TwoPermutationPrototype.Sampling
open OracleComp
set_option maxRecDepth 8192

private theorem forward_grows_and_caches (cache : Cache) (input : Block) (result : Block × Cache)
    (possible : result ∈ support (cache.forward input)) :
    result.2.entries.length ≤ cache.entries.length + 1 ∧ ¬ UnusedInput result.2.entries input := by
  classical
  unfold PermutationCache.forward at possible
  split at possible
  · obtain ⟨reply, _, eq⟩ := (mem_support_bind_iff _ _ _).mp possible
    simp only [support_pure, Set.mem_singleton_iff] at eq
    subst result
    exact ⟨le_rfl,fun unused => unused (input,reply.val) List.mem_cons_self rfl⟩
  · rename_i known
    simp only [support_pure, Set.mem_singleton_iff] at possible
    subst result
    exact ⟨Nat.le_succ _,known⟩

theorem pinned_restricted_step_grows_and_caches (cache : Cache) (input : Block) (result : Block × Cache)
    (possible : result ∈ support (pinnedRestrictedForward cache input)) :
    result.2.entries.length ≤ cache.entries.length + 1 ∧ ¬ UnusedInput result.2.entries input := by
  classical
  unfold pinnedRestrictedForward at possible
  split at possible
  · split at possible
    · obtain ⟨reply, _, eq⟩ := (mem_support_bind_iff _ _ _).mp possible
      simp only [support_pure, Set.mem_singleton_iff] at eq
      subst result
      exact ⟨le_rfl,fun unused => unused (input,reply.val.val) List.mem_cons_self rfl⟩
    · exact forward_grows_and_caches cache input result possible
  · exact forward_grows_and_caches cache input result possible

theorem pinned_full_const_frame (cache : Cache) (answers : List (BitVec 1344)) (addresses : List Block)
    (result : List (BitVec 1344) × Cache)
    (possible : result ∈ support (runPinnedFull cache answers (pinnedConstantPlans addresses))) :
    result.2.entries.length ≤ cache.entries.length + addresses.length ∧
    (∀ row ∈ cache.entries, row ∈ result.2.entries) ∧
    ∀ address ∈ addresses, ¬ UnusedInput result.2.entries address := by
  induction addresses generalizing cache answers result with
  | nil =>
    simp only [pinnedConstantPlans,List.map_nil,runPinnedFull,support_pure,Set.mem_singleton_iff] at possible
    subst result
    simp
  | cons address rest ih =>
    have preserved := pinned_full_preserves_rows cache answers (pinnedConstantPlans (address :: rest)) result possible
    simp only [pinnedConstantPlans,List.map_cons,runPinnedFull] at possible
    obtain ⟨⟨answer,middle⟩,first,later⟩ := (mem_support_bind_iff _ _ _).mp possible
    have step := pinned_restricted_step_grows_and_caches cache address (answer,middle) first
    obtain ⟨growth,keep,cached⟩ := ih middle (pinnedOutputTail answer :: answers) result later
    refine ⟨?_,preserved,?_⟩
    · have size : middle.entries.length ≤ cache.entries.length+1 := step.1
      simp only [List.length_cons]
      omega
    · intro x seen
      rcases List.mem_cons.mp seen with rfl | remains
      · exact fun unused => step.2 (fun row present => unused row (keep row present))
      · exact cached x remains

end TwoPermutationPrototype.Sampling
