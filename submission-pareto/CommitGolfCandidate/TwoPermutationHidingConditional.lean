import CommitGolfCandidate.TwoPermutationHidingIndependent
import CommitGolfCandidate.TwoPermutationHidingMargin

/-! The two-message experiment after the common public history, including
the opened rows. This theorem is independent of how the transcript is encoded. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

noncomputable local instance conditionalFunctionSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

local instance conditionalDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

def readSecondDigests : List Block → List (BitVec 256)
  | _first :: second :: rest => outputDigest second :: readSecondDigests rest
  | _ => []

noncomputable def unpackUnopenedDigests (positions : Positions) (tape : List Block) : UnopenedDigestTape positions :=
  fun i => (readSecondDigests tape)[(hiddenIndices positions).idxOf i]?.getD 0

theorem read_second_digests (pairs : List ReplyPair) :
    readSecondDigests (serializeReplyPairs pairs) = pairs.map fun pair => outputDigest pair.2 := by
  induction pairs with
  | nil => rfl
  | cons head tail ih =>
    change outputDigest head.2 :: readSecondDigests (serializeReplyPairs tail) = _
    rw [ih]
    rfl

theorem unpack_hidden_tape {positions : Positions} (opened : OpenedDigests positions)
    (closed : UnopenedDigestTape positions) (hidden : HiddenTape positions) :
    unpackUnopenedDigests positions
      (serializeReplyPairs ((hiddenIndices positions).map (hiddenReplyPairs (fullDigestTape opened closed) hidden))) =
      closed := by
  funext i
  have belongs : i ∈ hiddenIndices positions := by simp [hiddenIndices]
  unfold unpackUnopenedDigests
  rw [read_second_digests, List.map_map]
  simp only [List.getElem?_map, List.getElem?_idxOf belongs, Option.map_some, Option.getD_some, Function.comp_apply]
  have hit : fullDigestTape opened closed i.val = closed i := by
    unfold fullDigestTape
    exact dite_eq_right i.property
  change outputDigest ((hidden i).2.2 ++ fullDigestTape opened closed i.val) = closed i
  rw [hit]
  exact BitVec.extractLsb'_append_eq_right

noncomputable def conditionalGame {α : Type} {positions : Positions} (cache : Cache)
    (messages : Index → Words 32) (opened : OpenedDigests positions) (compress : Compression)
    (observer : DigestTape → OracleComp World α) (proposed : Bool) : ProbComp α := do
  let salts ← $ᵗ UnopenedSalts positions
  let p ← cache.sample
  let next := fun reverse p => fixedOracleRun (fixedOracle compress p)
    (observer (fullDigestTape opened (unpackUnopenedDigests positions reverse.reverse)))
  let plans := unopenedPlans positions messages (publicSaltTape salts)
  if proposed then runProposed next p.val [] plans else runPlanned next p.val [] plans

noncomputable def conditionalReference {α : Type} {positions : Positions} (cache : Cache)
    (opened : OpenedDigests positions) (compress : Compression)
    (observer : DigestTape → OracleComp World α) : ProbComp α := do
  let digests ← $ᵗ UnopenedDigestTape positions
  let p ← cache.sample
  let _ ← sampleHiddenTape positions
  fixedOracleRun (fixedOracle compress p.val) (observer (fullDigestTape opened digests))

noncomputable def conditionalProgrammed {α : Type} {positions : Positions} (cache : Cache)
    (messages : Index → Words 32) (opened : OpenedDigests positions) (compress : Compression)
    (observer : DigestTape → OracleComp World α) : ProbComp α := do
  let digests ← $ᵗ UnopenedDigestTape positions
  let p ← cache.sample
  let hidden ← sampleHiddenTape positions
  let all := fullDigestTape opened digests
  fixedOracleRun (fixedOracle compress (p.val.programRows (hiddenRows all messages hidden))) (observer all)

theorem conditional_programmed_eq {α : Type} {positions : Positions} (cache : Cache)
    (messages : Index → Words 32) (opened : OpenedDigests positions) (compress : Compression)
    (observer : DigestTape → OracleComp World α) :
    conditionalGame cache messages opened compress observer true =ᵈ
      conditionalProgrammed cache messages opened compress observer := by
  let indices := hiddenIndices positions
  let run (salts : Index → BitVec 128) (tape : List Block) (p : Completion cache.entries) : ProbComp α :=
    fixedOracleRun (fixedOracle compress (p.val.programRows
      (plannedRows [] (unopenedPlans positions messages salts) tape)))
      (observer (fullDigestTape opened (unpackUnopenedDigests positions tape)))
  let finish (salts : Index → BitVec 128) (tape : List Block) : ProbComp α :=
    cache.sample >>= run salts tape
  trans (do let salts ← $ᵗ UnopenedSalts positions
            let tape ← sampleProposalTape (2 * indices.length)
            finish (publicSaltTape salts) tape)
  · unfold conditionalGame
    apply EvalDistEq.bind_right
    intro salts
    simp only [ite_true]
    let plans := unopenedPlans positions messages (publicSaltTape salts)
    have length : plans.length = 2 * indices.length := by
      simp [plans, unopenedPlans, indices, leaf_plans_length]
    dsimp only [plans] at length
    simp only [proposed_from_full_tape, length, List.append_nil, List.reverse_reverse]
    exact (EvalDistEq.of_evalDist_eq
      (distribution_bind_comm (sampleProposalTape (2 * indices.length)) cache.sample (run (publicSaltTape salts)))).symm
  · apply (independent_honest_proposals positions opened finish).trans
    unfold conditionalProgrammed
    apply EvalDistEq.bind_right
    intro digests
    let observeProgrammed (secret : HiddenTape positions) (p : Completion cache.entries) : ProbComp α :=
      fixedOracleRun (fixedOracle compress (p.val.programRows
        (hiddenRows (fullDigestTape opened digests) messages secret)))
        (observer (fullDigestTape opened digests))
    trans (do let secret ← sampleHiddenTape positions
              let p ← cache.sample
              observeProgrammed secret p)
    · apply EvalDistEq.bind_right
      intro secret
      have rows := hidden_rows_match_plans (fullDigestTape opened digests) messages secret indices []
      have recovered := unpack_hidden_tape opened digests secret
      simp only [finish, run, observeProgrammed]
      simp only [indices, unopenedPlans, hiddenRows] at rows ⊢
      rw [rows, recovered]
    · exact EvalDistEq.of_evalDist_eq
        (distribution_bind_comm (sampleHiddenTape positions) cache.sample observeProgrammed)

theorem conditional_precharge {α : Type} {positions : Positions} (cache : Cache)
    (messages : Index → Words 32) (opened : OpenedDigests positions) (compress : Compression)
    (observer : DigestTape → OracleComp World α) (firstStage openedRows : List Row) (budget : Nat)
    (seed : cache.entries = openedRows ++ firstStage) (firstCount : firstStage.length ≤ budget)
    (openedCount : openedRows.length ≤ 2 * positions.card)
    (tags : ∀ row ∈ openedRows, exposedInputTag positions row.1) :
    measureTVDist (conditionalGame cache messages opened compress observer false)
      (conditionalGame cache messages opened compress observer true) ≤
      (budget : ℝ) * hiddenPairRate.toReal + 2 ^ 25 * ((budget : ℝ) + 2 ^ 25) / 2 ^ 1600 := by
  let charge := (budget : ENNReal) * hiddenPairRate + (2 ^ 25 : ENNReal) * (((budget : ENNReal) + 2 ^ 25) / 2 ^ 1600)
  have stepBound : measureETVDist (conditionalGame cache messages opened compress observer false)
      (conditionalGame cache messages opened compress observer true) ≤ charge := by
    unfold conditionalGame
    refine (distance_averaged_event ($ᵗ UnopenedSalts positions) _ _
      (fun salts => proposedConflict cache [] (unopenedPlans positions messages (publicSaltTape salts))) (· = true) ?_).trans
      (honest_proposal_conflict_le cache messages opened firstStage openedRows budget seed firstCount openedCount tags)
    intro salts
    simp only [Bool.false_eq_true, ite_false, ite_true]
    apply planned_vs_proposed_distance
  rw [measureTVDist_eq_toReal_measureETVDist]
  refine (ENNReal.toReal_mono (by unfold charge hiddenPairRate; finiteness) stepBound).trans_eq ?_
  unfold charge
  rw [ENNReal.toReal_add (by unfold hiddenPairRate; finiteness) (by finiteness)]
  simp [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_add]
  ring

theorem conditional_observer_bound {α : Type} {positions : Positions} (cache : Cache)
    (messages : Index → Words 32) (opened : OpenedDigests positions) (compress : Compression)
    (observer : DigestTape → OracleComp World α) (budget : Nat)
    (bounded : ∀ tape, QueryBounded (observer tape) budget) :
    measureTVDist (conditionalReference cache opened compress observer)
      (conditionalProgrammed cache messages opened compress observer) ≤
      (budget : ℝ) * hiddenPairRate.toReal := by
  unfold conditionalReference conditionalProgrammed
  apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
  intro digests
  apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
  intro p
  have each := independent_hidden_observer_distance positions (fullDigestTape opened digests) messages compress p.val
    (observer (fullDigestTape opened digests)) budget (bounded _)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using each

/-- All opening sizes are covered, conditional on a shared first-stage trace
and the opened rows. The observation may depend on the entire digest tape. -/
theorem conditional_two_message_hiding {α : Type} {positions : Positions} (cache : Cache)
    (messages₀ messages₁ : Index → Words 32) (opened : OpenedDigests positions) (compress : Compression)
    (observer : DigestTape → OracleComp World α) (firstStage openedRows : List Row) (budget : Nat)
    (seed : cache.entries = openedRows ++ firstStage) (firstCount : firstStage.length ≤ budget)
    (openedCount : openedRows.length ≤ 2 * positions.card)
    (tags : ∀ row ∈ openedRows, exposedInputTag positions row.1)
    (bounded : ∀ tape, QueryBounded (observer tape) budget) :
    measureTVDist (conditionalGame cache messages₀ opened compress observer false)
      (conditionalGame cache messages₁ opened compress observer false) ≤ min 1 (((budget : ℝ) + 1) / 2 ^ 120) := by
  have precharge (message : Index → Words 32) :
      measureTVDist (conditionalGame cache message opened compress observer false)
        (conditionalProgrammed cache message opened compress observer) ≤
        (budget : ℝ) * hiddenPairRate.toReal + 2 ^ 25 * ((budget : ℝ) + 2 ^ 25) / 2 ^ 1600 := by
    unfold measureTVDist
    rw [← (conditional_programmed_eq cache message opened compress observer).evalDist_eq]
    exact conditional_precharge cache message opened compress observer firstStage openedRows budget
      seed firstCount openedCount tags
  exact two_message_via_reference budget _ _ _ _ _ (precharge messages₀) (precharge messages₁)
    (conditional_observer_bound cache messages₀ opened compress observer budget bounded)
    (conditional_observer_bound cache messages₁ opened compress observer budget bounded)

end TwoPermutationPrototype.Sampling
