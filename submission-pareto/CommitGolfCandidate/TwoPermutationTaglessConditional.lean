import CommitGolfCandidate.TwoPermutationTaglessProposals
import CommitGolfCandidate.TwoPermutationTaglessObserver

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp MeasureTheory CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 900000
set_option exponentiation.threshold 2048

noncomputable local instance {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

local instance {α : Type} : MeasurableSpace α := ⊤

theorem tagless_hidden_rows_match_plans {positions : Positions} (digests : DigestTape) (messages : Index → Words 32)
    (hidden : HiddenTape positions) (indices : List (HiddenIndex positions)) (answers : List Block) :
    plannedRows answers (taglessLeafPlans messages (hiddenSalts hidden) (indices.map Subtype.val))
      (serializeReplyPairs (indices.map (hiddenReplyPairs digests hidden))) =
      taglessHiddenRowsFor digests messages hidden indices := by
  induction indices generalizing answers with
  | nil => rfl
  | cons index rest ih =>
    have salt : hiddenSalts hidden index.val = (hidden index).1 := by
      unfold hiddenSalts
      exact dite_eq_left index.property
    change (hiddenFirstInput index.val (messages index.val) (hiddenSalts hidden index.val), (hidden index).2.1) ::
      (taglessSecondAddress messages index.val (hidden index).2.1,
        (hidden index).2.2 ++ digests index.val) ::
      plannedRows (((hidden index).2.2 ++ digests index.val) :: (hidden index).2.1 :: answers)
        (taglessLeafPlans messages (hiddenSalts hidden) (rest.map Subtype.val))
        (serializeReplyPairs (rest.map (hiddenReplyPairs digests hidden))) =
      hiddenFirstRow messages index.val (hidden index) ::
      taglessHiddenSecondRow digests messages index.val (hidden index) :: taglessHiddenRowsFor digests messages hidden rest
    rw [salt, ih]
    rfl

noncomputable def taglessConditionalGame {α : Type} {positions : Positions} (cache : Cache)
    (messages : Index → Words 32) (opened : OpenedDigests positions) (compress : Compression)
    (observer : DigestTape → OracleComp World α) (proposed : Bool) : ProbComp α := do
  let salts ← $ᵗ UnopenedSalts positions
  let p ← cache.sample
  let next := fun reverse p => fixedOracleRun (fixedOracle compress p)
    (observer (fullDigestTape opened (unpackUnopenedDigests positions reverse.reverse)))
  let plans := taglessHiddenPlans positions messages (publicSaltTape salts)
  if proposed then runProposed next p.val [] plans else runPlanned next p.val [] plans

noncomputable def taglessConditionalProgrammed {α : Type} {positions : Positions} (cache : Cache)
    (messages : Index → Words 32) (opened : OpenedDigests positions) (compress : Compression)
    (observer : DigestTape → OracleComp World α) : ProbComp α := do
  let digests ← $ᵗ UnopenedDigestTape positions
  let p ← cache.sample
  let hidden ← sampleHiddenTape positions
  let all := fullDigestTape opened digests
  fixedOracleRun (fixedOracle compress (p.val.programRows (taglessHiddenRows all messages hidden))) (observer all)

theorem tagless_conditional_programmed_eq {α : Type} {positions : Positions} (cache : Cache)
    (messages : Index → Words 32) (opened : OpenedDigests positions) (compress : Compression)
    (observer : DigestTape → OracleComp World α) :
    taglessConditionalGame cache messages opened compress observer true =ᵈ
      taglessConditionalProgrammed cache messages opened compress observer := by
  let indices := hiddenIndices positions
  let run (salts : Index → BitVec 128) (tape : List Block) (p : Completion cache.entries) : ProbComp α :=
    fixedOracleRun (fixedOracle compress (p.val.programRows
      (plannedRows [] (taglessHiddenPlans positions messages salts) tape)))
      (observer (fullDigestTape opened (unpackUnopenedDigests positions tape)))
  let finish (salts : Index → BitVec 128) (tape : List Block) : ProbComp α :=
    cache.sample >>= run salts tape
  trans (do let salts ← $ᵗ UnopenedSalts positions
            let tape ← sampleProposalTape (2 * indices.length)
            finish (publicSaltTape salts) tape)
  · unfold taglessConditionalGame
    apply EvalDistEq.bind_right
    intro salts
    simp only [ite_true]
    let plans := taglessHiddenPlans positions messages (publicSaltTape salts)
    have length : plans.length = 2 * indices.length := by
      simp [plans, taglessHiddenPlans, indices, tagless_leaf_plans_length]
    dsimp only [plans] at length
    simp only [proposed_from_full_tape, length, List.append_nil, List.reverse_reverse]
    exact (EvalDistEq.of_evalDist_eq
      (distribution_bind_comm (sampleProposalTape (2 * indices.length)) cache.sample (run (publicSaltTape salts)))).symm
  · apply (independent_honest_proposals positions opened finish).trans
    unfold taglessConditionalProgrammed
    apply EvalDistEq.bind_right
    intro digests
    let observeProgrammed (secret : HiddenTape positions) (p : Completion cache.entries) : ProbComp α :=
      fixedOracleRun (fixedOracle compress (p.val.programRows
        (taglessHiddenRows (fullDigestTape opened digests) messages secret)))
        (observer (fullDigestTape opened digests))
    trans (do let secret ← sampleHiddenTape positions
              let p ← cache.sample
              observeProgrammed secret p)
    · apply EvalDistEq.bind_right
      intro secret
      have rows := tagless_hidden_rows_match_plans (fullDigestTape opened digests) messages secret indices []
      have recovered := unpack_hidden_tape opened digests secret
      simp only [finish, run, observeProgrammed]
      simp only [indices, taglessHiddenPlans, taglessHiddenRows] at rows ⊢
      rw [rows, recovered]
    · exact EvalDistEq.of_evalDist_eq
        (distribution_bind_comm (sampleHiddenTape positions) cache.sample observeProgrammed)

theorem tagless_conditional_observer_bound {α : Type} {positions : Positions} (cache : Cache)
    (messages : Index → Words 32) (opened : OpenedDigests positions) (compress : Compression)
    (observer : DigestTape → OracleComp World α) (budget : Nat)
    (bounded : ∀ tape, QueryBounded (observer tape) budget) :
    measureTVDist (conditionalReference cache opened compress observer)
      (taglessConditionalProgrammed cache messages opened compress observer) ≤
      (budget : ℝ) / 2 ^ 127 := by
  unfold conditionalReference taglessConditionalProgrammed
  apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
  intro digests
  apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
  intro p
  have each := tagless_independent_observer_distance positions (fullDigestTape opened digests) messages compress p.val
    (observer (fullDigestTape opened digests)) budget (bounded _)
  exact each

theorem tagless_proposal_rate_real (budget : Nat) : (taglessProposalRate budget).toReal = taglessProposalError budget := by
  unfold taglessProposalRate taglessProposalError
  repeat first
    | rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    | rw [ENNReal.toReal_mul]
    | rw [ENNReal.toReal_div]
    | rw [ENNReal.toReal_pow]
  simp only [ENNReal.toReal_ofNat, ENNReal.toReal_one, ENNReal.toReal_natCast]
  ring

theorem tagless_conditional_precharge {α : Type} {positions : Positions} (cache : Cache)
    (messages : Index → Words 32) (opened : OpenedDigests positions) (compress : Compression)
    (observer : DigestTape → OracleComp World α) (firstStage openedRows : List Row) (budget : Nat)
    (seed : cache.entries = openedRows ++ firstStage) (firstCount : firstStage.length ≤ budget)
    (openedCount : openedRows.length ≤ 2 * positions.card)
    (guard : ∀ row ∈ openedRows, taglessOpenedAddress positions row.1) :
    measureTVDist (taglessConditionalGame cache messages opened compress observer false)
      (taglessConditionalProgrammed cache messages opened compress observer) ≤ taglessProposalError budget := by
  rw [measureTVDist_eq_toReal_measureETVDist, ← tagless_proposal_rate_real]
  apply ENNReal.toReal_mono (by unfold taglessProposalRate; finiteness)
  have eq := tagless_conditional_programmed_eq cache messages opened compress observer
  unfold measureETVDist
  rw [← eq.evalDist_eq]
  change measureETVDist (taglessConditionalGame cache messages opened compress observer false)
    (taglessConditionalGame cache messages opened compress observer true) ≤ _
  unfold taglessConditionalGame
  refine (distance_averaged_event ($ᵗ UnopenedSalts positions) _ _
    (fun salts => proposedConflict cache [] (taglessHiddenPlans positions messages (publicSaltTape salts))) (· = true) ?_).trans
    (tagless_hidden_conflict_le cache messages firstStage openedRows budget seed firstCount openedCount guard)
  intro salts
  simp only [Bool.false_eq_true, ite_false, ite_true]
  apply planned_vs_proposed_distance

noncomputable def taglessConditionalError (budget : Nat) : ℝ :=
  2 * taglessProposalError budget + 2 * (budget : ℝ) / 2 ^ 127

theorem tagless_conditional_hiding {α : Type} {positions : Positions} (cache : Cache)
    (messages₀ messages₁ : Index → Words 32) (opened : OpenedDigests positions) (compress : Compression)
    (observer : DigestTape → OracleComp World α) (firstStage openedRows : List Row) (budget : Nat)
    (seed : cache.entries = openedRows ++ firstStage) (firstCount : firstStage.length ≤ budget)
    (openedCount : openedRows.length ≤ 2 * positions.card)
    (guard : ∀ row ∈ openedRows, taglessOpenedAddress positions row.1)
    (bounded : ∀ tape, QueryBounded (observer tape) budget) :
    measureTVDist (taglessConditionalGame cache messages₀ opened compress observer false)
      (taglessConditionalGame cache messages₁ opened compress observer false) ≤ taglessConditionalError budget := by
  let game (messages : Index → Words 32) := taglessConditionalGame cache messages opened compress observer false
  let programmed (messages : Index → Words 32) := taglessConditionalProgrammed cache messages opened compress observer
  let reference := conditionalReference cache opened compress observer
  have precharge (messages : Index → Words 32) :
      measureTVDist (game messages) (programmed messages) ≤ taglessProposalError budget :=
    tagless_conditional_precharge cache messages opened compress observer firstStage openedRows budget
      seed firstCount openedCount guard
  have observed (messages : Index → Words 32) :
      measureTVDist reference (programmed messages) ≤ (budget : ℝ) / 2^127 :=
    tagless_conditional_observer_bound cache messages opened compress observer budget bounded
  have first := measureTVDist_triangle (game messages₀) (programmed messages₀) reference
  rw [measureTVDist_comm (programmed messages₀) reference] at first
  have last := measureTVDist_triangle reference (programmed messages₁) (game messages₁)
  rw [measureTVDist_comm (programmed messages₁) (game messages₁)] at last
  apply (measureTVDist_triangle (game messages₀) reference (game messages₁)).trans
  unfold taglessConditionalError
  linarith [precharge messages₀, precharge messages₁, observed messages₀, observed messages₁]

end TwoPermutationPrototype.Sampling
