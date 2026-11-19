import CommitGolfCandidate.TaggedPinnedHighCache

namespace TwoPermutationPrototype.Sampling
open OracleComp
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

local instance pinnedHighStepDiscrete {α : Type} : MeasurableSpace α := ⊤

noncomputable def pinnedHighStep {base : Cache} (cache : PinnedHighCache base)
    (step : Nat) (input : Block) : ProbComp (BitVec 1344 × PinnedHighCache base) := by
  classical
  exact if fresh : UnusedInput cache.zero.entries input then
    if present : Nonempty (PinnedUnusedTails (pinnedCachedTails cache.zero)) then do
      let tail ← samplePinnedUnusedTails (pinnedCachedTails cache.zero) present
      pure (tail.val, cache.extend ⟨input, tail.val, step⟩ fresh tail.property)
    else pure (0, cache)
  else pure (pinnedOutputTail (cache.zero.example.val.forward input), cache)

private theorem pinned_tail_sampler_congr {α : Type} {a b : List (BitVec 1344)} (same : a = b)
    (ha : Nonempty (PinnedUnusedTails a)) (hb : Nonempty (PinnedUnusedTails b))
    (left : PinnedUnusedTails a → ProbComp α) (right : PinnedUnusedTails b → ProbComp α)
    (each : ∀ x y, x.val = y.val → left x =ᵈ right y) :
    (samplePinnedUnusedTails a ha >>= left) =ᵈ (samplePinnedUnusedTails b hb >>= right) := by
  subst b
  apply EvalDistEq.bind_right
  intro x
  exact each x x rfl

/-- High cache transitions do not inspect the private low tape. For a fresh row
the next low slot is filled independently; for a cache hit that draw is unused. -/
theorem pinned_split_high_step {α : Type} {base : Cache} (cache : PinnedHighCache base)
    (low : PinnedLowTape) (step : Nat) (input : Block)
    (earlier : ∀ row ∈ cache.added, row.slot < step) (room : cache.zero.entries.length ≤ 2 ^ 121)
    (next : BitVec 1344 → Cache → ProbComp α) :
    (do let (reply, updated) ← pinnedRestrictedForward (cache.realize low) input
        next (pinnedOutputTail reply) updated) =ᵈ
    (do let (tail, updated) ← pinnedHighStep cache step input
        let draw ← $ᵗ BitVec 256
        next tail (updated.realize (Function.update low step draw))) := by
  classical
  have roomLow : (cache.realize low).entries.length ≤ 2^121 := by
    simpa only [PinnedHighCache.zero, cache.entries_length] using room
  by_cases fresh : UnusedInput cache.zero.entries input
  · have freshLow : UnusedInput (cache.realize low).entries input :=
      (cache.input_unused input (fun _ => 0) low).mp fresh
    have present := pinned_current_tails_nonempty cache.zero room
    have sameTails : pinnedCachedTails (cache.realize low) = pinnedCachedTails cache.zero :=
      (cache.tails low).trans (cache.tails (fun _ => 0)).symm
    apply (pinned_restricted_forward_fresh_eq (cache.realize low) input freshLow roomLow
      (fun answer => next (pinnedOutputTail answer.1) answer.2)).trans
    simp only [pinnedHighStep, fresh, present, dite_true, bind_assoc, pure_bind]
    apply pinned_tail_sampler_congr sameTails
    intro real shell same
    apply EvalDistEq.bind_right
    intro draw
    have highRead : pinnedOutputTail (real.val ++ draw) = real.val :=
      BitVec.extractLsb'_append_eq_left
    have layout : ((cache.extend ⟨input, shell.val, step⟩ fresh shell.property).realize
        (Function.update low step draw)).entries =
        (input, (real.val ++ draw : Block)) :: (cache.realize low).entries := by
      change (input, (shell.val ++ Function.update low step draw step : Block)) ::
        (cache.realize (Function.update low step draw)).entries = _
      rw [Function.update_self, cache.unchanged_update low step draw earlier, same]
    have cacheMatch : (cache.realize low).extendForward input freshLow
        ⟨real.val ++ draw, pinned_unused_tail_unused_output (cache.realize low) _ (highRead.symm ▸ real.property)⟩ =
        (cache.extend ⟨input, shell.val, step⟩ fresh shell.property).realize (Function.update low step draw) :=
      pinned_cache_entries_ext layout.symm
    exact EvalDistEq.of_evalDist_eq (congrArg evalDist (congrArg₂ next (highRead.trans same) cacheMatch))
  · have freshLow : ¬ UnusedInput (cache.realize low).entries input := fun unseen =>
      fresh ((cache.input_unused input low (fun _ => 0)).mp unseen)
    simp only [pinnedHighStep, pinnedRestrictedForward, fresh, freshLow, dite_false, PermutationCache.forward, pure_bind]
    rw [cache.read_tail input fresh low]
    symm
    trans (($ᵗ BitVec 256) >>= fun _ => next (pinnedOutputTail (cache.zero.example.val.forward input)) (cache.realize low))
    · apply EvalDistEq.bind_right
      intro draw
      rw [cache.unchanged_update low step draw earlier]
    · exact EvalDistEq.of_evalDist_eq (evalDist_bind_const _ _)

theorem pinned_high_step_support {base : Cache} (cache : PinnedHighCache base) (step : Nat) (input : Block)
    (result : BitVec 1344 × PinnedHighCache base) (possible : result ∈ support (pinnedHighStep cache step input)) :
    result.2.added = cache.added ∨ ∃ row : PinnedHighRow,
      row.input = input ∧ row.upper = result.1 ∧ row.slot = step ∧ result.2.added = row :: cache.added := by
  classical
  unfold pinnedHighStep at possible
  split at possible
  · split at possible
    · obtain ⟨tail, _, eq⟩ := (mem_support_bind_iff _ _ _).mp possible
      simp only [support_pure, Set.mem_singleton_iff] at eq
      subst result
      exact Or.inr ⟨_, rfl, rfl, rfl, rfl⟩
    · simp only [support_pure, Set.mem_singleton_iff] at possible
      subst result
      exact Or.inl rfl
  · simp only [support_pure, Set.mem_singleton_iff] at possible
    subst result
    exact Or.inl rfl

end TwoPermutationPrototype.Sampling
