import CommitGolfCandidate.TaggedPinnedHighSupport

namespace TwoPermutationPrototype.Sampling
open OracleComp

private theorem pinned_forward_frame (cache : Cache) (input : Block) (result : Block × Cache)
    (possible : result ∈ support (cache.forward input)) :
    ∀ row ∈ cache.entries, row ∈ result.2.entries := by
  unfold PermutationCache.forward at possible
  split at possible
  · obtain ⟨reply, _, eq⟩ := (mem_support_bind_iff _ _ _).mp possible
    simp only [support_pure, Set.mem_singleton_iff] at eq
    subst result
    exact fun row available => List.mem_cons_of_mem _ available
  · simp only [support_pure, Set.mem_singleton_iff] at possible
    subst result
    exact fun _ => id

theorem pinned_restricted_step_frame (cache : Cache) (input : Block) (result : Block × Cache)
    (possible : result ∈ support (pinnedRestrictedForward cache input)) :
    ∀ row ∈ cache.entries, row ∈ result.2.entries := by
  unfold pinnedRestrictedForward at possible
  split at possible
  · split at possible
    · obtain ⟨reply, _, eq⟩ := (mem_support_bind_iff _ _ _).mp possible
      simp only [support_pure, Set.mem_singleton_iff] at eq
      subst result
      exact fun row present => List.mem_cons_of_mem _ present
    · exact pinned_forward_frame cache input result possible
  · exact pinned_forward_frame cache input result possible

theorem pinned_full_preserves_rows (cache : Cache) (answers : List (BitVec 1344)) (plans : List PinnedHighPlan)
    (result : List (BitVec 1344) × Cache)
    (possible : result ∈ support (runPinnedFull cache answers plans)) :
    ∀ row ∈ cache.entries, row ∈ result.2.entries := by
  induction plans generalizing cache answers result with
  | nil =>
    simp only [runPinnedFull, support_pure, Set.mem_singleton_iff] at possible
    subst result
    exact fun _ => id
  | cons plan rest ih =>
    simp only [runPinnedFull] at possible
    obtain ⟨⟨answer, middle⟩, first, second⟩ := (mem_support_bind_iff _ _ _).mp possible
    intro row present
    exact ih middle (pinnedOutputTail answer :: answers) result second row
      (pinned_restricted_step_frame cache (plan answers) (answer, middle) first row present)

end TwoPermutationPrototype.Sampling
