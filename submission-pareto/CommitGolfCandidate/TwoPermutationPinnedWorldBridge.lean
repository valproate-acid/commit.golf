import CommitGolfCandidate.TwoPermutationPinnedPreload
import CommitGolfCandidate.TaggedPinnedRestrictedWorld

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2048
attribute [local irreducible] pinnedFirstAddresses pinnedFullLeafDigests

local instance {α : Type} : MeasurableSpace α := ⊤

theorem pinned_digest_from_separated_addresses (positions : Positions) (left right : Message)
    (opened : OpenedSalts positions) (closed : UnopenedSalts positions) (which : Bool)
    (upper : Block → BitVec 1344) (p : BiPermutation Block)
    (messages : ∀ i ∈ positions, left i = right i)
    (known : ∀ i, upper (pinnedFirstAddress (if which then right else left) i) =
      pinnedOutputTail (p.forward (pinnedFirstAddress (if which then right else left) i))) :
    pinnedFullLeafDigests p (if which then right else left) (mergeSaltTape opened closed) =
      fullDigestTape (pinnedOpenedDigestTape left upper opened p.forward)
        (pinnedHiddenDigestTape (if which then right else left) upper closed p.forward) := by
  funext i
  rw [pinned_leaf_digest_from_high p _ _ upper i (known i)]
  unfold fullDigestTape mergeSaltTape
  by_cases visible : i ∈ positions
  · simp only [visible, dite_true, pinnedOpenedDigestTape]
    cases which
    · rfl
    · have words : messageWords right i = messageWords left i :=
        congrArg (fun entry : Entry => fun word : Fin 32 => entry.extractLsb' (64 * word.val) 64)
          (messages i visible).symm
      simp only [show (true : Bool) = true from rfl, ite_true, pinnedPublicAddress, pinnedFirstAddress,
        pinnedSecondFromHigh, words]
      rfl
  · simp only [visible, dite_false, pinnedHiddenDigestTape]
    rfl

theorem pinned_combined_second_addresses_size (positions : Positions) (left message : Message)
    (opened : OpenedSalts positions) (closed : UnopenedSalts positions) (upper : Block → BitVec 1344) :
    (pinnedOpenedAddresses positions left upper opened ++
      pinnedHiddenAddresses positions message upper closed).length = LENGTH := by
  have card := hidden_index_count positions
  rw [hiddenIndices, Finset.length_toList, Finset.card_univ] at card
  simp only [List.length_append, pinned_opened_addresses_length, pinnedHiddenAddresses,
    pinned_nonce_addresses_length]
  exact (Nat.add_comm ..).trans card

theorem pinned_split_constant_second {α : Type} (start : Cache) (first second : List Block)
    (observe : Cache → ProbComp α) :
    (runPinnedFull start [] (pinnedConstantPlans (first ++ second)) >>= fun result => observe result.2) =
      (do let a ← runPinnedFull start [] (pinnedConstantPlans first)
          let b ← runPinnedFull a.2 [] (pinnedConstantPlans second)
          observe b.2) := by
  have appendPlans : pinnedConstantPlans (first ++ second) =
      pinnedConstantPlans first ++ pinnedConstantPlans second := List.map_append ..
  rw [appendPlans, pinned_nonadaptive_full_append]
  simp only [bind_assoc]
  apply bind_congr
  intro result
  simp only [← bind_map_left]
  rw [pinned_constant_full_forget]

noncomputable def pinnedClosedRestrictedWorld {α : Type} (base : Cache) (positions : Positions)
    (left right : Message) (opened : OpenedSalts positions) (closed : UnopenedSalts positions) (which : Bool)
    (observe : DigestTape → BiPermutation Block → ProbComp α) : ProbComp α :=
  pinnedCommonFull base positions left right opened (fun upper seeded => do
    let message := if which then right else left
    let final ← runPinnedFull seeded [] (pinnedConstantPlans (pinnedHiddenAddresses positions message upper closed))
    let p ← final.2.sample
    observe (fullDigestTape (pinnedOpenedDigestTape left upper opened p.val.forward)
      (pinnedHiddenDigestTape message upper closed p.val.forward)) p.val)

theorem pinned_closed_restricted_world_near {α : Type} (base : Cache) (positions : Positions)
    (left right : Message) (opened : OpenedSalts positions) (closed : UnopenedSalts positions) (which : Bool)
    (messages : ∀ i ∈ positions, left i = right i)
    (observe : DigestTape → BiPermutation Block → ProbComp α)
    (maximum : Nat) (room : base.entries.length + 3 * LENGTH ≤ maximum) (cap : maximum ≤ 2^121)
    (frame : ∀ result ∈ support (runPinnedFull base [] (pinnedConstantPlans (pinnedFirstAddresses left right))),
      result.2.entries.length ≤ base.entries.length + 2 * LENGTH ∧
      ∀ address ∈ pinnedFirstAddresses left right, ¬ UnusedInput result.2.entries address) :
    measureTVDist (pinnedClosedRestrictedWorld base positions left right opened closed which observe)
      (base.sample >>= fun p => observe
        (pinnedFullLeafDigests p.val (if which then right else left) (mergeSaltTape opened closed)) p.val) ≤
      (3 * LENGTH : ℝ) * ((maximum : ℝ) / 2^1343) := by
  let front := pinnedFirstAddresses left right
  let prepared := runPinnedFull base [] (pinnedConstantPlans front)
  let message := if which then right else left
  let observeReal (p : BiPermutation Block) :=
    observe (pinnedFullLeafDigests p message (mergeSaltTape opened closed)) p
  let half := prepared >>= fun a => a.2.sample >>= fun p => observeReal p.val
  have before : measureTVDist half (base.sample >>= fun p => observeReal p.val) ≤
      (2 * LENGTH : ℝ) * ((maximum : ℝ) / 2^1343) := by
    have firstFits : base.entries.length + front.length ≤ maximum := by
      rw [show front.length = 2 * LENGTH from pinned_first_addresses_length left right]
      omega
    have raw := pinned_restrict_preload base front observeReal maximum firstFits cap
    simpa only [front, pinned_first_addresses_length, Nat.cast_mul, Nat.cast_ofNat, half, prepared] using raw
  have after : measureTVDist (pinnedClosedRestrictedWorld base positions left right opened closed which observe) half ≤
      (LENGTH : ℝ) * ((maximum : ℝ) / 2^1343) := by
    unfold pinnedClosedRestrictedWorld pinnedCommonFull
    change measureTVDist (prepared >>= _) (prepared >>= _) ≤ _
    apply pinned_restricted_bind_support_le prepared _ _ _ (by positivity)
    intro a reached
    have facts := frame a reached
    let upper := pinnedBoundedHigh front a.2
    let publicAddr := pinnedOpenedAddresses positions left upper opened
    let privateAddr := pinnedHiddenAddresses positions message upper closed
    have length : (publicAddr ++ privateAddr).length = LENGTH :=
      pinned_combined_second_addresses_size positions left message opened closed upper
    have secondFits : a.2.entries.length + (publicAddr ++ privateAddr).length ≤ maximum := by
      rw [length]
      omega
    have compare := pinned_restrict_preload a.2 (publicAddr ++ privateAddr) observeReal maximum secondFits cap
    rw [length] at compare
    let readTape (p : BiPermutation Block) := observe (fullDigestTape
      (pinnedOpenedDigestTape left upper opened p.forward) (pinnedHiddenDigestTape message upper closed p.forward)) p
    let recheck := fun (last : Cache) => last.sample >>= fun val => readTape val.val
    have secondEffect : (runPinnedFull a.2 [] (pinnedConstantPlans (publicAddr ++ privateAddr)) >>= fun result =>
        result.2.sample >>= fun p => observeReal p.val) =ᵈ
      (runPinnedFull a.2 [] (pinnedConstantPlans (publicAddr ++ privateAddr)) >>= fun result => recheck result.2) := by
      apply EvalDistEq.bind_congr_of_support
      intro result resultReached
      apply EvalDistEq.bind_right
      intro p
      let original : Completion a.2.entries := ⟨p.val, fun row present =>
        p.property row (pinned_full_preserves_rows a.2 [] _ result resultReached row present)⟩
      have known : ∀ i, upper (pinnedFirstAddress message i) =
          pinnedOutputTail (p.val.forward (pinnedFirstAddress message i)) := by
        intro i
        have member : pinnedFirstAddress message i ∈ front := pinned_first_address_mem left right which i
        have cached := facts.2 _ member
        unfold upper pinnedBoundedHigh
        rw [if_pos member, pinned_cached_read_agree original _ cached]
      unfold observeReal readTape
      rw [pinned_digest_from_separated_addresses positions left right opened closed which upper p.val messages known]
    rw [pinned_split_constant_second a.2 publicAddr privateAddr recheck] at secondEffect
    unfold measureTVDist at compare ⊢
    rw [secondEffect.evalDist_eq] at compare
    exact compare
  refine (measureTVDist_triangle _ half _).trans ((add_le_add after before).trans_eq ?_)
  ring

theorem pinned_reorder_hidden_sampler {α : Type} (base : Cache) (positions : Positions)
    (left right : Message) (opened : OpenedSalts positions) (which : Bool)
    (observe : DigestTape → BiPermutation Block → ProbComp α) :
    pinnedRestrictedWorld base positions left right opened which observe =ᵈ
      (samplePinnedHiddenNonces positions >>= fun closed =>
        pinnedClosedRestrictedWorld base positions left right opened closed which observe) := by
  let addresses := pinnedFirstAddresses left right
  let first := runPinnedFull base [] (pinnedConstantPlans addresses)
  let upper (cache : Cache) := pinnedBoundedHigh addresses cache
  let openedRun (cache : Cache) :=
    runPinnedFull cache [] (pinnedConstantPlans (pinnedOpenedAddresses positions left (upper cache) opened))
  let resume (cache : Cache) (closed : UnopenedSalts positions) (seed : Cache) := do
    let message := if which then right else left
    let final ← runPinnedFull seed [] (pinnedConstantPlans (pinnedHiddenAddresses positions message (upper cache) closed))
    let p ← final.2.sample
    observe (fullDigestTape (pinnedOpenedDigestTape left (upper cache) opened p.val.forward)
      (pinnedHiddenDigestTape message (upper cache) closed p.val.forward)) p.val
  let sample := samplePinnedHiddenNonces positions
  trans (do let a ← first
            let closed ← sample
            let b ← openedRun a.2
            resume a.2 closed b.2)
  · unfold pinnedRestrictedWorld pinnedCommonFull
    apply EvalDistEq.bind_right first
    intro a
    exact (EvalDistEq.of_evalDist_eq (distribution_bind_comm sample (openedRun a.2)
      (fun closed b => resume a.2 closed b.2))).symm
  · exact (EvalDistEq.of_evalDist_eq (distribution_bind_comm sample first
      (fun closed a => openedRun a.2 >>= fun b => resume a.2 closed b.2))).symm

end TwoPermutationPrototype.Sampling
