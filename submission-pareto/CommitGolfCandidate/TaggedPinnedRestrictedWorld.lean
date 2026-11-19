import CommitGolfCandidate.TaggedPinnedConditionalObserver
import CommitGolfCandidate.TaggedPinnedOpenedPreserve
import CommitGolfCandidate.TaggedPinnedRestrictedFrame

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2048
attribute [local irreducible] pinnedFirstAddresses pinnedCommonHigh

local instance pinnedRestrictedWorldDiscrete {α : Type} : MeasurableSpace α := ⊤

noncomputable def samplePinnedHiddenNonces (positions : Positions) : ProbComp (UnopenedSalts positions) :=
  @uniformSample _ (@pinnedConditionalFunctionSampler (HiddenIndex positions) (BitVec 128) inferInstance inferInstance inferInstance)

def pinnedHiddenFirst (positions : Positions) (message : Message) (upper : Block → BitVec 1344)
    (i : HiddenIndex positions) : Block :=
  upper (pinnedFirstAddress message i.val) ++ (0 : BitVec 256)

noncomputable def pinnedHiddenAddresses (positions : Positions) (message : Message) (upper : Block → BitVec 1344)
    (salt : UnopenedSalts positions) : List Block :=
  pinnedNonceAddresses Subtype.val (pinnedHiddenFirst positions message upper) (fun i => messageWords message i.val) salt

def pinnedOpenedDigestTape {positions : Positions} (message : Message) (upper : Block → BitVec 1344)
    (salts : OpenedSalts positions) (get : Block → Block) : OpenedDigests positions :=
  fun i => pinnedOutputDigest (get (pinnedPublicAddress message upper i.val (salts i)))

def pinnedHiddenDigestTape {positions : Positions} (message : Message) (upper : Block → BitVec 1344)
    (salts : UnopenedSalts positions) (get : Block → Block) : UnopenedDigestTape positions :=
  fun i => pinnedOutputDigest (get (pinnedPublicAddress message upper i.val (salts i)))

noncomputable def pinnedRestrictedAfterCommon {α : Type} (base : Cache) (positions : Positions)
    (left right : Message) (opened : OpenedSalts positions) (which : Bool) (upper : Block → BitVec 1344)
    (observe : DigestTape → BiPermutation Block → ProbComp α) : ProbComp α := do
  let message := if which then right else left
  let salts ← samplePinnedHiddenNonces positions
  let final ← runPinnedFull base [] (pinnedConstantPlans (pinnedHiddenAddresses positions message upper salts))
  let p ← final.2.sample
  observe (fullDigestTape (pinnedOpenedDigestTape left upper opened p.val.forward)
    (pinnedHiddenDigestTape message upper salts p.val.forward)) p.val

noncomputable def pinnedRestrictedWorld {α : Type} (base : Cache) (positions : Positions)
    (left right : Message) (opened : OpenedSalts positions) (which : Bool)
    (observe : DigestTape → BiPermutation Block → ProbComp α) : ProbComp α :=
  pinnedCommonFull base positions left right opened (fun upper seeded =>
    pinnedRestrictedAfterCommon seeded positions left right opened which upper observe)

theorem pinned_hidden_addresses_away {positions : Positions} (left message : Message)
    (upper full : Block → BitVec 1344) (salts : OpenedSalts positions) (nonce : UnopenedSalts positions)
    (address : Block) (located : address ∈ pinnedHiddenAddresses positions message upper nonce) :
    address ∉ pinnedOpenedAddresses positions left full salts := by
  obtain ⟨i, _, stored⟩ := List.mem_map.mp located
  have asAddress : pinnedPublicAddress message upper i.val (nonce i) = address := stored
  intro found
  obtain ⟨j, included, same⟩ := List.mem_map.mp found
  have eq := pinned_public_addresses_site _ _ _ _ _ _ _ _ (asAddress.trans same.symm)
  exact i.property (eq ▸ Finset.mem_toList.mp included)

theorem pinned_visible_observer_equivalence {α : Type} {base : Cache} {count : Nat}
    (state : PinnedOpenedState base count) [DecidablePred state.isRevealed] (positions : Positions)
    (left right : Message) (opened : OpenedSalts positions) (which : Bool) (upper : Block → BitVec 1344)
    (visible : {i : Fin count // state.isRevealed i} → BitVec 256)
    (seen : ∀ i : {i : Index // i ∈ positions}, pinnedPublicAddress left upper i.val (opened i) ∈ state.opened)
    (observe : DigestTape → BiPermutation Block → ProbComp α) :
    (samplePinnedLowFn state.PrivateSlot >>= fun privateLow =>
      pinnedRestrictedAfterCommon (state.high.realize (pinnedFinLowTape (state.merge visible privateLow)))
        positions left right opened which upper observe) =ᵈ
      pinnedConditionalActual state visible (Subtype.val : HiddenIndex positions → Index)
        (pinnedHiddenFirst positions (if which then right else left) upper)
        (fun i => messageWords (if which then right else left) i.val)
        (fun digest p => observe (fullDigestTape
          (pinnedOpenedDigestTape left upper opened (state.publicReply visible)) digest) p) := by
  let message := if which then right else left
  let resume (privateLow : state.PrivateSlot → BitVec 256) (salt : UnopenedSalts positions) : ProbComp α := do
    let seed := state.high.realize (pinnedFinLowTape (state.merge visible privateLow))
    let final ← runPinnedFull seed [] (pinnedConstantPlans (pinnedHiddenAddresses positions message upper salt))
    let p ← final.2.sample
    observe (fullDigestTape (pinnedOpenedDigestTape left upper opened p.val.forward)
      (pinnedHiddenDigestTape message upper salt p.val.forward)) p.val
  apply (EvalDistEq.of_evalDist_eq (distribution_bind_comm (samplePinnedLowFn state.PrivateSlot)
    (samplePinnedHiddenNonces positions) resume)).trans
  apply EvalDistEq.bind_right
  intro salt
  apply EvalDistEq.bind_right
  intro privateLow
  let addr := pinnedHiddenAddresses positions message upper salt
  let seed := state.high.realize (pinnedFinLowTape (state.merge visible privateLow))
  apply EvalDistEq.bind_congr_of_support (runPinnedFull seed [] (pinnedConstantPlans addr))
  intro final reached
  apply EvalDistEq.bind_right
  intro p
  let restricted : Completion seed.entries :=
    ⟨p.val, fun row h => p.property row (pinned_full_preserves_rows seed [] (pinnedConstantPlans addr) final reached row h)⟩
  have openTape : pinnedOpenedDigestTape left upper opened p.val.forward =
      pinnedOpenedDigestTape left upper opened (state.publicReply visible) := by
    funext i
    exact congrArg pinnedOutputDigest
      (pinned_reference_public_reply state visible privateLow _ (seen i) restricted)
  let readAt := pinnedNonceOrder (Subtype.val : HiddenIndex positions → Index)
    (pinnedHiddenFirst positions message upper) (fun i => messageWords message i.val) salt
  have hiddenTape : pinnedHiddenDigestTape message upper salt p.val.forward =
      fun i => pinnedOutputDigest (p.val.forward addr[readAt.symm i]) := by
    funext i
    have atIndex := pinned_nonce_address_at (Subtype.val : HiddenIndex positions → Index)
      (pinnedHiddenFirst positions message upper) (fun j => messageWords message j.val) salt (readAt.symm i)
    change addr[readAt.symm i] =
      pinnedPublicAddress message upper (readAt (readAt.symm i)).val (salt (readAt (readAt.symm i))) at atIndex
    rw [readAt.apply_symm_apply] at atIndex
    exact congrArg (pinnedOutputDigest ∘ p.val.forward) atIndex.symm
  change observe (fullDigestTape (pinnedOpenedDigestTape left upper opened p.val.forward)
      (pinnedHiddenDigestTape message upper salt p.val.forward)) p.val =ᵈ
    observe (fullDigestTape (pinnedOpenedDigestTape left upper opened (state.publicReply visible))
      (fun i => pinnedOutputDigest (p.val.forward addr[readAt.symm i]))) p.val
  rw [openTape, hiddenTape]

theorem pinned_restricted_bind_support_le {I α : Type} (sampler : ProbComp I)
    (left right : I → ProbComp α) (error : ℝ) (nonnegative : 0 ≤ error)
    (each : ∀ result ∈ support sampler, measureTVDist (left result) (right result) ≤ error) :
    measureTVDist (sampler >>= left) (sampler >>= right) ≤ error := by
  apply ENNReal.toReal_le_of_le_ofReal nonnegative
  refine (measureETVDist_bind_left_le_tsum sampler left right).trans ?_
  calc
    _ ≤ ∑' x, Pr{let value ← sampler}[value = x] * ENNReal.ofReal error := by
      apply ENNReal.tsum_le_tsum
      intro x
      by_cases present : x ∈ support sampler
      · exact mul_le_mul_of_nonneg_left
          ((ENNReal.le_ofReal_iff_toReal_le (measureETVDist_ne_top _ _) nonnegative).2 (each x present)) zero_le
      · have absent : Pr{let value ← sampler}[value = x] = 0 :=
          (prEvent_eq_zero_iff sampler (· = x)).2 (fun a found agrees => present (agrees ▸ found))
        simp only [absent, zero_mul, le_refl]
    _ = _ := by rw [ENNReal.tsum_mul_right, tsum_prEvent_eq_one, one_mul]

private theorem pinned_world_after_exposure {α : Type} {base : Cache} {count : Nat}
    (state : PinnedOpenedState base count) [DecidablePred state.isRevealed] (valid : state.high.Valid count)
    (positions : Positions) (left right : Message) (opened : OpenedSalts positions) (upper : Block → BitVec 1344)
    (seen : ∀ i : {i : Index // i ∈ positions}, pinnedPublicAddress left upper i.val (opened i) ∈ state.opened)
    (away : ∀ message nonce address, address ∈ pinnedHiddenAddresses positions message upper nonce →
        address ∉ state.opened)
    (hiddenRoom : state.high.zero.entries.length + Fintype.card (HiddenIndex positions) ≤ 2^121)
    (sites : Fintype.card (HiddenIndex positions) ≤ 2^24)
    (compress : Compression) (observer : DigestTape → OracleComp World α)
    (budget : Nat) (bounded : ∀ digest, QueryBounded (observer digest) budget) (before : base.entries.length ≤ budget) :
    let observe := fun digest p => fixedOracleRun (fixedOracle compress p) (observer digest)
    let resumed := fun which cache => pinnedRestrictedAfterCommon cache positions left right opened which upper observe
    measureTVDist
      (samplePinnedLows count >>= fun draws =>
        resumed false (state.high.realize (pinnedPlaceLows (fun _ => 0) 0 draws)))
      (samplePinnedLows count >>= fun draws =>
        resumed true (state.high.realize (pinnedPlaceLows (fun _ => 0) 0 draws))) ≤ 2 * pinnedOneSideCharge budget := by
  let observe := fun digest p => fixedOracleRun (fixedOracle compress p) (observer digest)
  let resumed (which : Bool) (cache : Cache) :=
    pinnedRestrictedAfterCommon cache positions left right opened which upper observe
  have f₀ := pinned_opened_lows_equivalence state (resumed false)
  have f₁ := pinned_opened_lows_equivalence state (resumed true)
  change measureTVDist
    (samplePinnedLows count >>= fun draws =>
      resumed false (state.high.realize (pinnedPlaceLows (fun _ => 0) 0 draws)))
    (samplePinnedLows count >>= fun draws =>
      resumed true (state.high.realize (pinnedPlaceLows (fun _ => 0) 0 draws))) ≤ _
  unfold measureTVDist
  rw [f₀.evalDist_eq, f₁.evalDist_eq]
  change measureTVDist (_ >>= _) (_ >>= _) ≤ _
  apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by unfold pinnedOneSideCharge; positivity)
  intro visible
  have l₀ := pinned_visible_observer_equivalence state positions left right opened false upper visible seen observe
  have l₁ := pinned_visible_observer_equivalence state positions left right opened true upper visible seen observe
  change measureTVDist (samplePinnedLowFn state.PrivateSlot >>= fun privateLow =>
    pinnedRestrictedAfterCommon (state.high.realize (pinnedFinLowTape (state.merge visible privateLow)))
      positions left right opened false upper observe)
    (samplePinnedLowFn state.PrivateSlot >>= fun privateLow =>
      pinnedRestrictedAfterCommon (state.high.realize (pinnedFinLowTape (state.merge visible privateLow)))
        positions left right opened true upper observe) ≤ _
  unfold measureTVDist
  rw [l₀.evalDist_eq, l₁.evalDist_eq]
  let observePublic (digest : UnopenedDigestTape positions) :=
    observer (fullDigestTape (pinnedOpenedDigestTape left upper opened (state.publicReply visible)) digest)
  let runPublic := fun digest p => fixedOracleRun (fixedOracle compress p) (observePublic digest)
  have proofSide (message : Message) :
      measureTVDist (pinnedConditionalActual state visible (Subtype.val : HiddenIndex positions → Index)
        (pinnedHiddenFirst positions message upper) (fun i => messageWords message i.val) runPublic)
        (pinnedConditionalReference state visible runPublic) ≤ pinnedOneSideCharge budget :=
    pinned_conditional_to_reference state valid visible Subtype.val Subtype.val_injective
      (pinnedHiddenFirst positions message upper) (fun i => messageWords message i.val) hiddenRoom
      (away message) compress observePublic budget (fun _ => bounded _) before sites
  let ref := pinnedConditionalReference state visible runPublic
  have middle := measureTVDist_triangle
    (pinnedConditionalActual state visible (Subtype.val : HiddenIndex positions → Index)
      (pinnedHiddenFirst positions left upper) (fun i => messageWords left i.val) runPublic)
    ref
    (pinnedConditionalActual state visible (Subtype.val : HiddenIndex positions → Index)
      (pinnedHiddenFirst positions right upper) (fun i => messageWords right i.val) runPublic)
  rw [measureTVDist_comm ref] at middle
  exact middle.trans ((add_le_add (proofSide left) (proofSide right)).trans_eq (by ring))

theorem pinned_restricted_two_world {α : Type} (base : Cache) (positions : Positions)
    (left right : Message) (opened : OpenedSalts positions)
    (compress : Compression) (observer : DigestTape → OracleComp World α)
    (budget : Nat) (bounded : ∀ digest, QueryBounded (observer digest) budget)
    (before : base.entries.length ≤ budget) (room : base.entries.length + 3 * LENGTH ≤ 2^121) :
    let observe := fun digest p => fixedOracleRun (fixedOracle compress p) (observer digest)
    measureTVDist (pinnedRestrictedWorld base positions left right opened false observe)
      (pinnedRestrictedWorld base positions left right opened true observe) ≤ 2 * pinnedOneSideCharge budget := by
  classical
  let observe := fun digest p => fixedOracleRun (fixedOracle compress p) (observer digest)
  have nonneg : 0 ≤ 2 * pinnedOneSideCharge budget := by unfold pinnedOneSideCharge; positivity
  have cardinality : Fintype.card (HiddenIndex positions) + positions.card = LENGTH := by
    have exactCount := hidden_index_count positions
    rw [hiddenIndices, Finset.length_toList, Finset.card_univ] at exactCount
    exact exactCount
  have prepRoom : base.entries.length + 2*LENGTH + positions.card ≤ 2^121 := by omega
  have e₀ := pinned_common_full_separates base positions left right opened prepRoom
    (fun upper seeded => pinnedRestrictedAfterCommon seeded positions left right opened false upper observe)
  have e₁ := pinned_common_full_separates base positions left right opened prepRoom
    (fun upper seeded => pinnedRestrictedAfterCommon seeded positions left right opened true upper observe)
  change measureTVDist (pinnedRestrictedWorld base positions left right opened false observe)
    (pinnedRestrictedWorld base positions left right opened true observe) ≤ _
  unfold pinnedRestrictedWorld measureTVDist
  rw [e₀.evalDist_eq, e₁.evalDist_eq]
  let finish (which : Bool) (common : PinnedCommonHigh base) : ProbComp α := do
    let draws ← samplePinnedLows (2 * LENGTH + positions.card)
    pinnedRestrictedAfterCommon (common.final.realize (pinnedPlaceLows (fun _ => 0) 0 draws))
      positions left right opened which (pinnedBoundedHigh (pinnedFirstAddresses left right) common.first.zero) observe
  change measureTVDist (pinnedCommonHigh base positions left right opened >>= finish false)
    (pinnedCommonHigh base positions left right opened >>= finish true) ≤ _
  refine pinned_restricted_bind_support_le (pinnedCommonHigh base positions left right opened)
    (finish false) (finish true) _ nonneg ?_
  intro common reached
  have facts := pinned_common_high_facts base positions left right opened prepRoom common reached
  let state := PinnedCommonHigh.openedState facts
  let upper := pinnedBoundedHigh (pinnedFirstAddresses left right) common.first.zero
  have hiddenRoom : state.high.zero.entries.length + Fintype.card (HiddenIndex positions) ≤ 2^121 := by
    have size := facts.tableBound
    change state.high.zero.entries.length ≤ _ at size
    omega
  have sites : Fintype.card (HiddenIndex positions) ≤ 2^24 := by
    have : LENGTH = 2^24 := rfl
    omega
  have openMatches : pinnedOpenedAddresses positions left upper opened = state.opened := by
    rw [show state.opened = common.opened from rfl, facts.openedShape]
    apply pinned_bound_high_opened
    intro i _
    exact pinned_first_address_mem left right false i
  have seen (i : {i : Index // i ∈ positions}) :
      pinnedPublicAddress left upper i.val (opened i) ∈ state.opened := by
    rw [← openMatches]
    have member := Finset.mem_toList.mpr i.property
    refine List.mem_map.mpr ⟨i.val, member, ?_⟩
    simp only [publicOpenedSalts, dite_eq_left i.property]
  have away (message : Message) (nonce : UnopenedSalts positions) (address : Block)
      (included : address ∈ pinnedHiddenAddresses positions message upper nonce) :
      address ∉ state.opened := by
    rw [← openMatches]
    exact pinned_hidden_addresses_away left message upper upper opened nonce address included
  exact pinned_world_after_exposure state facts.valid positions left right opened upper seen away hiddenRoom sites
    compress observer budget bounded before

end TwoPermutationPrototype.Sampling
