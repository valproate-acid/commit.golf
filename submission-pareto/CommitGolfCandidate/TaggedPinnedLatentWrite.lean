import CommitGolfCandidate.TaggedPinnedTargets
import CommitGolfCandidate.TaggedPinnedWrites

namespace TwoPermutationPrototype.Sampling
open OracleComp

local instance pinnedLatentWriteDiscrete {α : Type} : MeasurableSpace α := ⊤

theorem pinned_realize_updates_latent {base : Cache} {high : PinnedHighCache base} {slot : Nat}
    (valid : high.Valid slot) (target : PinnedHighRow) (listed : target ∈ high.added)
    (low : PinnedLowTape) (digest : BitVec 256) :
    swapCachedOutputs (high.realize low) (target.realize low).2 (target.upper ++ digest) =
      high.realize (Function.update low target.slot digest) := by
  classical
  let old := (target.realize low).2
  let replacement : Block := target.upper ++ digest
  let updated := Function.update low target.slot digest
  apply pinned_cache_entries_ext
  change swapCachedOutputRows (pinnedHighTable base high.added low) old replacement =
    pinnedHighTable base high.added updated
  simp only [swapCachedOutputRows, pinnedHighTable, List.map_append, List.map_map, Function.comp_def]
  congr 1
  · apply List.map_congr_left
    intro row found
    by_cases same : row = target
    · subst row
      have actual : (target.realize low).1 = target.input := rfl
      have selected : updated target.slot = digest := Function.update_self ..
      exact Prod.ext actual
        ((swap_first old replacement).trans (congrArg (fun v : BitVec 256 => (target.upper ++ v : Block)) selected.symm))
    · have different : row.slot ≠ target.slot := fun eq =>
        same (pinned_unique_mapped_key PinnedHighRow.slot valid.slotUnique found listed eq)
      have noTail : row.upper ≠ target.upper := fun eq =>
        same (pinned_unique_mapped_key PinnedHighRow.upper valid.tailUnique found listed eq)
      have newTail : pinnedOutputTail replacement = target.upper := BitVec.extractLsb'_append_eq_left
      have notOld : (row.realize low).2 ≠ old := by
        intro eq
        exact noTail ((pinned_high_row_tail row low).symm.trans
          ((congrArg pinnedOutputTail eq).trans (pinned_high_row_tail target low)))
      have notNew : (row.realize low).2 ≠ replacement := by
        intro eq
        exact noTail ((pinned_high_row_tail row low).symm.trans ((congrArg pinnedOutputTail eq).trans newTail))
      have unchanged : updated row.slot = low row.slot := Function.update_of_ne different ..
      exact Prod.ext rfl ((swap_other notOld notNew).trans
        (congrArg (fun bits : BitVec 256 => (row.upper ++ bits : Block)) unchanged.symm))
  · calc
      _ = base.entries.map id := by
        apply List.map_congr_left
        intro row previous
        have noTail : pinnedOutputTail row.2 ≠ target.upper := by
          intro eq
          exact valid.chooserTail target listed (List.mem_map.mpr ⟨row, previous, eq⟩)
        have notOld : row.2 ≠ old := fun eq =>
          noTail ((congrArg pinnedOutputTail eq).trans (pinned_high_row_tail target low))
        have notNew : row.2 ≠ replacement := fun eq =>
          noTail ((congrArg pinnedOutputTail eq).trans (show pinnedOutputTail replacement = target.upper from
            BitVec.extractLsb'_append_eq_left))
        exact Prod.ext rfl (swap_other notOld notNew)
      _ = _ := List.map_id _

theorem pinned_uniform_latent_low_update {α : Type} {base : Cache} {high : PinnedHighCache base} {slot : Nat}
    (valid : high.Valid slot) (target : PinnedHighRow) (listed : target ∈ high.added)
    (low : PinnedLowTape) (digest : BitVec 256) (next : BiPermutation Block → ProbComp α) :
    (do let p ← (high.realize low).sample
        next (p.val.program target.input (target.upper ++ digest))) =ᵈ
      (do let p ← (high.realize (Function.update low target.slot digest)).sample
          next p.val) := by
  let reply := (target.realize low).2
  let replacement : Block := target.upper ++ digest
  trans (do let p ← (high.realize low).sample; next (p.val.swapOutputs reply replacement))
  · apply EvalDistEq.bind_right
    intro p
    have stored := p.property (target.realize low) (List.mem_append_left _ (List.mem_map_of_mem listed))
    change p.val.forward target.input = reply at stored
    exact EvalDistEq.of_evalDist_eq
      (congrArg (fun old => evalDist (next (p.val.swapOutputs old replacement))) stored)
  · have transport := pinned_uniform_swap_cached_outputs (high.realize low) reply replacement next
    have table := pinned_realize_updates_latent valid target listed low digest
    rw [table] at transport
    exact transport

end TwoPermutationPrototype.Sampling
