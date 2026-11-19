import CommitGolfCandidate.PentaHidingFinal

/-! Sharp (2^-121) form of `penta_final_reference_hiding`, as 31727a8 does for the pinned tree:
the other half of the 2^-120 budget pays for the nonce-chain replacement. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
set_option exponentiation.threshold 2048
attribute [local irreducible] pinnedFirstAddresses pinnedFullLeafDigests

noncomputable local instance pentaSharpFunSampleable {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

local instance pentaSharpDiscrete {α : Type} : MeasurableSpace α := ⊤

private theorem penta_sharp_observe_bound {State Output : Type} {openingSize budget : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (bounded : Hiding.QueryBound adversary budget)
    (compress : Compression) (prior : Hiding.HidingChallenge State openingSize × Cache)
    (reached : prior ∈ support (lazyRun compress adversary.choose (PermutationCache.empty Block)))
    (root : Commitment) (proof : Proof) :
    QueryBounded (adversary.observe prior.1.aux root proof) budget := by
  have projected : prior.1 ∈ support
      ((simulateQ (lazyHandler compress) adversary.choose).run' (PermutationCache.empty Block)) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨prior, reached, rfl⟩
  have possible := support_simulateQ_run'_subset (lazyHandler compress) adversary.choose _ projected
  have instrumented : prior.1 ∈ support (Prod.fst <$> Hiding.counted adversary.choose) := by
    rw [show Prod.fst <$> Hiding.counted adversary.choose = adversary.choose from
      fst_map_costDist adversary.choose ⟨Oracle.callCost⟩]
    exact possible
  rw [support_map] at instrumented
  obtain ⟨⟨challenge, calls⟩, counted, equal⟩ := instrumented
  change challenge = prior.1 at equal
  subst challenge
  exact (hiding_observe_query_bound adversary bounded (prior.1, calls) counted root proof).mono (Nat.sub_le _ _)

theorem penta_final_hiding_margin_sharp (budget : Nat) :
    2 * ((3 * LENGTH : ℝ) * (((budget : ℝ) + 3 * LENGTH) / 2^1343)) +
      2 * (((budget : ℝ)/2^128 + (budget : ℝ)*(2/2^128 + 2^25/2^1344)) + 2^24/2^319) ≤
      ((budget : ℝ) + 1) / 2^121 := by
  have nonneg : 0 ≤ (budget : ℝ) := Nat.cast_nonneg _
  have compares : (LENGTH : ℝ) = 2 ^ 24 := by norm_num [LENGTH, LOG_LENGTH]
  rw [compares]
  norm_num
  linarith

theorem penta_final_reference_hiding_sharp {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : PentaTranscriptBuilder)
    (compress : Compression) (budget : Nat) (bounded : Hiding.QueryBound adversary budget)
    (small : budget + 1 ≤ 2^120) :
    measureTVDist (pentaViewReference adversary build compress false)
      (pentaViewReference adversary build compress true) ≤ ((budget : ℝ) + 1) / 2^121 := by
  · let maximum := budget + 3 * LENGTH
    let err : ℝ := 2 * ((3 * LENGTH : ℝ) * ((maximum : ℝ) / 2^1343)) + 2 * pentaOneSideCharge budget
    have numeric : err ≤ ((budget : ℝ) + 1) / 2^121 := by
      unfold err maximum pentaOneSideCharge pinnedOneSideCharge
      push_cast
      exact penta_final_hiding_margin_sharp budget
    apply le_trans _ numeric
    have nonneg : 0 ≤ err := by unfold err pentaOneSideCharge pinnedOneSideCharge; positivity
    unfold measureTVDist
    rw [(penta_eager_posterior_eq adversary build compress false).evalDist_eq,
        (penta_eager_posterior_eq adversary build compress true).evalDist_eq]
    unfold pentaViewPosterior
    let chooser := lazyRun compress adversary.choose (PermutationCache.empty Block)
    change measureTVDist (chooser >>= _) (chooser >>= _) ≤ err
    apply pinned_restricted_bind_support_le chooser _ _ _ nonneg
    intro prior reached
    let challenge := prior.1
    let base := prior.2
    let choices := ($ᵗ OpenedSalts challenge.positions)
    have cacheLe : base.entries.length ≤ budget := by
      have length := lazy_cache_length compress adversary.choose (PermutationCache.empty Block) budget
        (hiding_choose_query_bound adversary bounded) prior reached
      simpa only [PermutationCache.empty, List.length_nil, Nat.zero_add] using length
    have room : base.entries.length + 3 * LENGTH ≤ maximum := by unfold maximum; omega
    have cap : maximum ≤ 2^121 := pinned_hiding_room budget small
    have agree : ∀ i ∈ challenge.positions, challenge.message₀ i = challenge.message₁ i := by
      intro i visible
      exact congrFun challenge.agree ⟨i, visible⟩
    change measureTVDist (choices >>= _) (choices >>= _) ≤ err
    apply measureTVDist_bind_left_le_of_forall_le choices _ _ nonneg
    intro opened
    let observer (tape : DigestTape) (penta : PentaFunction) :=
      let (root, proof) := build penta challenge.positions opened tape
      adversary.observe challenge.aux root proof
    let observe (tape : DigestTape) (p : BiPermutation Block) :=
      fixedOracleRun (fixedOracle compress p) (observer tape (pentaFunction p.forward))
    let left := challenge.message₀
    let right := challenge.message₁
    let restricted (which : Bool) :=
      pinnedRestrictedWorld base challenge.positions left right opened which observe
    let real (which : Bool) := do
      let closed ← samplePinnedHiddenNonces challenge.positions
      let p ← base.sample
      let message := if which then right else left
      observe (pinnedFullLeafDigests p.val message (mergeSaltTape opened closed)) p.val
    have boundObserver : ∀ tape penta, QueryBounded (observer tape penta) budget := by
      intro tape penta
      exact penta_sharp_observe_bound adversary bounded compress prior reached _ _
    have inner : measureTVDist (restricted false) (restricted true) ≤ 2 * pentaOneSideCharge budget :=
      penta_restricted_two_world base challenge.positions left right opened compress observer budget
        boundObserver cacheLe (room.trans cap)
    have each (which : Bool) : measureTVDist (restricted which) (real which) ≤
        (3 * LENGTH : ℝ) * ((maximum : ℝ) / 2^1343) := by
      unfold restricted real measureTVDist
      rw [(pinned_reorder_hidden_sampler base challenge.positions left right opened which observe).evalDist_eq]
      change measureTVDist (_ >>= _) (_ >>= _) ≤ _
      apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
      intro closed
      apply pinned_closed_restricted_world_near base challenge.positions left right opened closed which
        agree observe maximum room cap
      intro result reached
      obtain ⟨length, _, covered⟩ := pinned_full_const_frame base [] (pinnedFirstAddresses left right) result reached
      rw [pinned_first_addresses_length] at length
      exact ⟨length, covered⟩
    change measureTVDist (real false) (real true) ≤ err
    have one := measureTVDist_triangle (real false) (restricted false) (real true)
    have two := measureTVDist_triangle (restricted false) (restricted true) (real true)
    rw [measureTVDist_comm (real false) (restricted false)] at one
    exact one.trans ((add_le_add (each false) (two.trans (add_le_add inner (each true)))).trans_eq (by unfold err; ring))

end TwoPermutationPrototype.Sampling
