import CommitGolfCandidate.TaggedPinnedCommonEval

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048
attribute [local irreducible] pinnedFirstAddresses

local instance pinnedWorldEvalDiscrete {α : Type} : MeasurableSpace α := ⊤

noncomputable def pinnedOrderedPositions (positions : Positions) : List Index :=
  positions.toList ++ (hiddenIndices positions).map Subtype.val

theorem pinned_ordered_positions_length (positions : Positions) :
    (pinnedOrderedPositions positions).length = LENGTH := by
  simp only [pinnedOrderedPositions, List.length_append, List.length_map, Finset.length_toList]
  rw [Nat.add_comm]
  exact hidden_index_count positions

noncomputable def pinnedWorldSecondPlan (positions : Positions) (message : Message) (salts : CompleteSaltTape)
    (upper : Block → BitVec 1344) : List PinnedHighPlan :=
  pinnedConstantPlans ((pinnedOrderedPositions positions).map (fun i => pinnedPublicAddress message upper i (salts i)))

theorem pinned_world_second_plan_length (positions : Positions) (message : Message) (salts : CompleteSaltTape)
    (upper : Block → BitVec 1344) :
    (pinnedWorldSecondPlan positions message salts upper).length = LENGTH := by
  simp only [pinnedWorldSecondPlan, pinnedConstantPlans, List.length_map, pinned_ordered_positions_length]

noncomputable def pinnedCachedUpper (cache : Cache) (input : Block) : BitVec 1344 :=
  pinnedOutputTail (cache.example.val.forward input)

theorem pinned_cached_read_agree {cache : Cache} (p : Completion cache.entries) (address : Block)
    (known : ¬ UnusedInput cache.entries address) :
    p.val.forward address = cache.example.val.forward address := by
  classical
  have found : ∃ row ∈ cache.entries, row.1 = address := by
    by_contra missing
    exact known (fun row present same => missing ⟨row, present, same⟩)
  obtain ⟨row, present, same⟩ := found
  rw [← same, p.property row present, cache.example.property row present]

/-- Once all A addresses are memoized, every second address is a function of
those cached highs and the nonce. The remaining eager permutation experiment
can use restricted reads of those constant addresses. -/
theorem pinned_restrict_world_seconds {α : Type} (cache : Cache) (positions : Positions)
    (message : Message) (salts : CompleteSaltTape) (upper : Block → BitVec 1344)
    (cached : ∀ i, ¬ UnusedInput cache.entries (pinnedFirstAddress message i))
    (known : ∀ i, upper (pinnedFirstAddress message i) = pinnedCachedUpper cache (pinnedFirstAddress message i))
    (observe : DigestTape → BiPermutation Block → ProbComp α)
    (maximum : Nat) (room : cache.entries.length + LENGTH ≤ maximum) (cap : maximum ≤ 2^121) :
    measureTVDist
      (do let final ← runPinnedFull cache [] (pinnedWorldSecondPlan positions message salts upper)
          let p ← final.2.sample
          observe (fun i => outputDigest (p.val.forward (pinnedPublicAddress message upper i (salts i)))) p.val)
      (do let p ← cache.sample
          observe (pinnedFullLeafDigests p.val message salts) p.val) ≤
      (LENGTH : ℝ) * ((maximum : ℝ)/2^1343) := by
  let plans := pinnedWorldSecondPlan positions message salts upper
  let continuation (p : BiPermutation Block) :=
    observe (fun i => outputDigest (p.forward (pinnedPublicAddress message upper i (salts i)))) p
  have lengths : (plans.map pinnedLiftPlan).length = LENGTH := by
    simp only [plans, List.length_map, pinned_world_second_plan_length]
  have step := pinned_eager_tail_restriction cache [] (plans.map pinnedLiftPlan) (fun _ => continuation)
    maximum (by simpa only [lengths] using room) cap
  rw [lengths] at step
  let next (cache : Cache) : ProbComp α := cache.sample >>= fun p => continuation p.val
  have left := pinned_full_from_restricted cache [] plans (fun _ => next)
  have right : (do let original ← cache.sample
                   runPlanned (fun _ => continuation) original.val [] (plans.map pinnedLiftPlan)) =ᵈ
        (do let p ← cache.sample; observe (pinnedFullLeafDigests p.val message salts) p.val) := by
    apply EvalDistEq.bind_right
    intro p
    have tape : pinnedFullLeafDigests p.val message salts =
        fun i => outputDigest (p.val.forward (pinnedPublicAddress message upper i (salts i))) := by
      funext i
      apply pinned_leaf_digest_from_high
      exact (known i).trans (congrArg pinnedOutputTail (pinned_cached_read_agree p _ (cached i)).symm)
    have execution : runPlanned (fun _ => continuation) p.val [] (plans.map pinnedLiftPlan) = continuation p.val :=
      pinned_constant_plans_run p.val [] _ _
    rw [execution, tape]
  have equality : measureTVDist
       (do let prepared ← runPinnedRestricted cache [] (plans.map pinnedLiftPlan)
           let final ← prepared.2.sample
           continuation final.val)
       (do let original ← cache.sample
           runPlanned (fun _ => continuation) original.val [] (plans.map pinnedLiftPlan)) =
      measureTVDist
        (do let final ← runPinnedFull cache [] plans; next final.2)
        (do let p ← cache.sample; observe (pinnedFullLeafDigests p.val message salts) p.val) := by
    unfold measureTVDist
    rw [left, right.evalDist_eq]
    rfl
  rw [equality] at step
  exact step

end TwoPermutationPrototype.Sampling
