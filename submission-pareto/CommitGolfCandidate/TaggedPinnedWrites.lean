import CommitGolfCandidate.TaggedPinnedTailCoupling

namespace TwoPermutationPrototype.Sampling
open OracleComp

/-- A write trace mixes retargeting an existing row and adding a fresh row.
Both cases yield a consistent target table for the next hidden position. -/
inductive PinnedWrites : Cache → Cache → Type
  | nil (cache : Cache) : PinnedWrites cache cache
  | reuse (cache final : Cache) (address old replacement : Block)
      (present : (address, old) ∈ cache.entries)
      (rest : PinnedWrites (swapCachedOutputs cache old replacement) final) : PinnedWrites cache final
  | fresh (cache final : Cache) (address : Block)
      (unused : UnusedInput cache.entries address) (reply : RemainingOutputs cache.entries)
      (rest : PinnedWrites (cache.extendForward address unused reply) final) : PinnedWrites cache final

noncomputable def PinnedWrites.rows {cache final : Cache} : PinnedWrites cache final → List Row
  | .nil _ => []
  | .reuse _ _ address _ replacement _ rest => (address, replacement) :: rest.rows
  | .fresh _ _ address _ reply rest => (address, reply.val) :: rest.rows

/-- This is the exact posterior for an arbitrary mixture of fresh B addresses
and B addresses that reuse a latent A row. The same programRows representation
can be used with the adaptive observer's forward/inverse mark rule. -/
theorem pinned_uniform_write_schedule {Output : Type} {cache final : Cache}
    (writes : PinnedWrites cache final) (next : BiPermutation Block → ProbComp Output) :
    (do let p ← cache.sample
        next (p.val.programRows writes.rows)) =ᵈ
    (do let p ← final.sample
        next p.val) := by
  induction writes with
  | nil cache => rfl
  | reuse cache final address old replacement present tail ih =>
    trans (do let p ← cache.sample
              next ((p.val.swapOutputs old replacement).programRows tail.rows))
    · apply EvalDistEq.bind_right
      intro p
      have oldValue : p.val.forward address = old := p.property (address, old) present
      change next ((p.val.program address replacement).programRows tail.rows) =ᵈ
        next ((p.val.swapOutputs old replacement).programRows tail.rows)
      rw [BiPermutation.program, oldValue]
    · exact (pinned_uniform_swap_cached_outputs cache old replacement
        (fun p => next (p.programRows tail.rows))).trans ih
  | fresh cache final address unused reply tail ih =>
    exact (program_uniform_completion cache address unused reply
      (fun p => next (p.programRows tail.rows))).trans ih

end TwoPermutationPrototype.Sampling
