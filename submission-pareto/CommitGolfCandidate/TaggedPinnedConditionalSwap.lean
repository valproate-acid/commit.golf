import CommitGolfCandidate.TaggedPinnedHiddenLows

namespace TwoPermutationPrototype.Sampling
open OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2048

noncomputable def samplePinnedLowFn (I : Type) [Fintype I] : ProbComp (I → BitVec 256) :=
  @uniformSample _ (@pinnedLowFunctionSampler I inferInstance)

theorem pinned_fin_low_fn_equivalence {α : Type} (count : Nat) (next : List (BitVec 256) → ProbComp α) :
    (samplePinnedLowFn (Fin count) >>= fun lows => next (List.ofFn lows)) =ᵈ
      (samplePinnedLows count >>= next) := by
  refine EvalDistEq.trans ?_ (pinned_fin_lows_equivalence count next)
  have same := @SampleableType.map_uniformSample_evalDistEq_of_bijective
    (Fin count → BitVec 256) (Fin count → BitVec 256)
    (@pinnedLowFunctionSampler (Fin count) inferInstance) inferInstance id Function.bijective_id
  simpa only [samplePinnedLowFn, id_map] using same.bind_left (fun lows => next (List.ofFn lows))

noncomputable def pinnedRunHiddenActual {α : Type} {base : Cache} {count : Nat}
    (state : PinnedOpenedState base count) [DecidablePred state.isRevealed]
    (opened : {i : Fin count // state.isRevealed i} → BitVec 256)
    (addresses : List Block) (next : (Fin addresses.length → BitVec 256) → BiPermutation Block → ProbComp α) :
    ProbComp α := do
  let priv ← samplePinnedLowFn state.PrivateSlot
  let result ← runPinnedFull (state.high.realize (pinnedFinLowTape (state.merge opened priv))) []
    (pinnedConstantPlans addresses)
  let p ← result.2.sample
  next (fun i => pinnedOutputDigest (p.val.forward addresses[i])) p.val

noncomputable def pinnedRunHiddenProgrammed {α : Type} {base : Cache} {count : Nat}
    (state : PinnedOpenedState base count) [DecidablePred state.isRevealed]
    (opened : {i : Fin count // state.isRevealed i} → BitVec 256)
    (addresses : List Block) (next : (Fin addresses.length → BitVec 256) → BiPermutation Block → ProbComp α) :
    ProbComp α := do
  let secret ← @uniformSample _ (pinnedDigestSampler state.PrivateSlot (Fin addresses.length))
  let p ← (state.high.realize (state.lowFromTape opened secret)).sample
  let result ← runPinnedHigh state.high count [] (pinnedConstantPlans addresses)
  let digest := pinnedDigestByAddress addresses (fun i => secret (.inr i))
  let rows := addresses.map (fun input => (input, pinnedCachedUpper result.2.zero input ++ digest input))
  next (fun i => secret (.inr i)) (p.val.programRows rows)

private theorem pinned_hidden_actual_factor {α : Type} {base : Cache} {count : Nat}
    (state : PinnedOpenedState base count) [DecidablePred state.isRevealed]
    (opened : {i : Fin count // state.isRevealed i} → BitVec 256)
    (addresses : List Block) (room : state.high.zero.entries.length + addresses.length ≤ 2^121)
    (next : (Fin addresses.length → BitVec 256) → BiPermutation Block → ProbComp α) :
    pinnedRunHiddenActual state opened addresses next =ᵈ
      (do let outcome ← runPinnedHigh state.high count [] (pinnedConstantPlans addresses)
          let secret ← @uniformSample _ (pinnedDigestSampler state.PrivateSlot (Fin addresses.length))
          let low := pinnedPlaceLows (state.lowFromTape opened secret) count (List.ofFn (fun i => secret (.inr i)))
          let p ← (outcome.2.realize low).sample
          next (fun i => pinnedOutputDigest (p.val.forward addresses[i])) p.val) := by
  let run := runPinnedHigh state.high count [] (pinnedConstantPlans addresses)
  let finish (priv : state.PrivateSlot → BitVec 256)
      (outcome : List (BitVec 1344) × PinnedHighCache base) (future : List (BitVec 256)) : ProbComp α := do
    let low := pinnedPlaceLows (pinnedFinLowTape (state.merge opened priv)) count future
    let p ← (outcome.2.realize low).sample
    next (fun i => pinnedOutputDigest (p.val.forward addresses[i])) p.val
  trans (do let priv ← samplePinnedLowFn state.PrivateSlot
            let outcome ← run
            let future ← samplePinnedLows addresses.length
            finish priv outcome future)
  · unfold pinnedRunHiddenActual
    apply EvalDistEq.bind_right
    intro priv
    change (runPinnedFull (state.high.realize (pinnedFinLowTape (state.merge opened priv))) []
          (pinnedConstantPlans addresses) >>= fun result =>
        result.2.sample >>= fun p => next (fun i => pinnedOutputDigest (p.val.forward addresses[i])) p.val) =ᵈ _
    simpa only [run, finish, pinnedConstantPlans, List.length_map] using
      pinned_full_high_low_equivalence state.high count (pinnedFinLowTape (state.merge opened priv))
        [] (pinnedConstantPlans addresses) state.slots (by simpa only [pinnedConstantPlans, List.length_map] using room)
        (fun _ cache => cache.sample >>= fun p => next (fun i => pinnedOutputDigest (p.val.forward addresses[i])) p.val)
  · apply (EvalDistEq.of_evalDist_eq (distribution_bind_comm (samplePinnedLowFn state.PrivateSlot) run
      (fun priv outcome => samplePinnedLows addresses.length >>= finish priv outcome))).trans
    apply EvalDistEq.bind_right
    intro outcome
    trans (do let priv ← samplePinnedLowFn state.PrivateSlot
              let future ← samplePinnedLowFn (Fin addresses.length)
              finish priv outcome (List.ofFn future))
    · apply EvalDistEq.bind_right
      intro priv
      exact (pinned_fin_low_fn_equivalence addresses.length (finish priv outcome)).symm
    · exact (pinned_uniform_digest_tape_split
        (fun priv future => finish priv outcome (List.ofFn future))).symm

/-- The complete hidden phase for any safe nonce tape is exactly a reference
permutation followed by programming. The observer receives independent digests. -/
theorem pinned_safe_hidden_programmed {α : Type} {base : Cache} {count : Nat}
    (state : PinnedOpenedState base count) [DecidablePred state.isRevealed]
    (valid : state.high.Valid count) (opened : {i : Fin count // state.isRevealed i} → BitVec 256)
    (addresses : List Block) (unique : addresses.Nodup) (away : ∀ addr ∈ addresses, addr ∉ state.opened)
    (outside : ∀ addr ∈ addresses, UnusedInput base.entries addr)
    (room : state.high.zero.entries.length + addresses.length ≤ 2^121)
    (next : (Fin addresses.length → BitVec 256) → BiPermutation Block → ProbComp α) :
    pinnedRunHiddenActual state opened addresses next =ᵈ pinnedRunHiddenProgrammed state opened addresses next := by
  let run := runPinnedHigh state.high count [] (pinnedConstantPlans addresses)
  let sample := @uniformSample _ (pinnedDigestSampler state.PrivateSlot (Fin addresses.length))
  let write (outcome : List (BitVec 1344) × PinnedHighCache base)
      (secret : PinnedDigestTape state.PrivateSlot (Fin addresses.length))
      (p : Completion (state.high.realize (state.lowFromTape opened secret)).entries) :=
    let d := pinnedDigestByAddress addresses (fun i => secret (.inr i))
    let rows := addresses.map (fun input => (input, pinnedCachedUpper outcome.2.zero input ++ d input))
    next (fun i => secret (.inr i)) (p.val.programRows rows)
  let old (secret : PinnedDigestTape state.PrivateSlot (Fin addresses.length)) :=
    (state.high.realize (state.lowFromTape opened secret)).sample
  apply (pinned_hidden_actual_factor state opened addresses room next).trans
  trans (run >>= fun outcome => sample >>= fun secret => old secret >>= write outcome secret)
  · apply EvalDistEq.bind_congr_of_support run
    intro outcome reached
    let target := state.hiddenAddressSlot valid addresses
    have distinct : PinnedTargetsDistinct target := pinned_targets_distinct state valid
      (fun i : Fin addresses.length => addresses[i]) unique.injective_get
    let after (secret : PinnedDigestTape state.PrivateSlot (Fin addresses.length)) : ProbComp α := do
      let low := pinnedPlaceLows (state.lowFromTape opened secret) count (List.ofFn (fun i => secret (.inr i)))
      let p ← (outcome.2.realize low).sample
      next (fun i => pinnedOutputDigest (p.val.forward addresses[i])) p.val
    apply (pinned_uniform_reassign_digests target distinct after).symm.trans
    apply EvalDistEq.bind_right
    intro secret
    have writeLaw := pinned_conditional_hidden_program_equivalence state valid opened addresses
      unique away outside room outcome reached secret (next (fun i => secret (.inr i)))
    apply EvalDistEq.trans ?_ writeLaw.symm
    apply EvalDistEq.bind_right
    intro p
    have reads : (fun i => pinnedOutputDigest (p.val.forward addresses[i])) = fun i => secret (.inr i) := by
      funext i
      exact pinned_swapped_hidden_digest_read state valid opened addresses unique away outside room outcome
        reached secret i p
    rw [reads]
  · apply (EvalDistEq.of_evalDist_eq (distribution_bind_comm run sample
      (fun outcome secret => old secret >>= write outcome secret))).trans
    apply EvalDistEq.bind_right
    intro secret
    exact EvalDistEq.of_evalDist_eq (distribution_bind_comm run (old secret) (fun outcome p => write outcome secret p))

end TwoPermutationPrototype.Sampling
