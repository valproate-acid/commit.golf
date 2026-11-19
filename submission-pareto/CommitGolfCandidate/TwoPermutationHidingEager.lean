import CommitGolfCandidate.TwoPermutationHidingTwoStage

/-! Express the staged experiment with a single sampled full permutation and a
single position-indexed salt vector. This is the machine refinement target. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option exponentiation.threshold 2048

noncomputable local instance eagerFunctionSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

local instance eagerDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

def leafOracleReplies (p : BiPermutation Block) (messages : Index → Words 32)
    (salts : Index → BitVec 128) (i : Index) : ReplyPair :=
  let first := p.forward (hiddenFirstInput i (messages i) (salts i))
  (first, p.forward (hiddenSecondInput i (messages i) first))

theorem real_planned_leaf_replies {α : Type} (next : List Block → BiPermutation Block → ProbComp α)
    (p : BiPermutation Block) (messages : Index → Words 32) (salts : Index → BitVec 128)
    (indices : List Index) (answers : List Block) :
    runPlanned next p answers (leafPlans messages salts indices) =
      next ((serializeReplyPairs (indices.map (leafOracleReplies p messages salts))).reverse ++ answers) p := by
  induction indices generalizing answers with
  | nil => rfl
  | cons i rest ih =>
    have plans : leafPlans messages salts (i :: rest) =
        [fun _ => hiddenFirstInput i (messages i) (salts i),
         fun previous => hiddenSecondInput i (messages i) (previous.headD 0)] ++ leafPlans messages salts rest := rfl
    rw [plans]
    simp only [List.cons_append, List.nil_append, runPlanned, List.headD_cons]
    rw [ih]
    simp only [List.map_cons, serializeReplyPairs, List.flatMap_cons,
      List.cons_append, List.nil_append, List.reverse_cons, List.append_assoc, leafOracleReplies]

theorem eager_opened_digests (positions : Positions) (p : BiPermutation Block)
    (messages : Index → Words 32) (salts : Index → BitVec 128) :
    readOpenedDigests positions (serializeReplyPairs (positions.toList.map (leafOracleReplies p messages salts))) =
      fun i => outputDigest (leafOracleReplies p messages salts i.val).2 := by
  funext i
  unfold readOpenedDigests
  rw [read_second_digests, List.map_map]
  simp only [List.getElem?_map, List.getElem?_idxOf (Finset.mem_toList.mpr i.property), Option.map_some,
    Option.getD_some, Function.comp_apply]

theorem eager_unopened_digests (positions : Positions) (p : BiPermutation Block)
    (messages : Index → Words 32) (salts : Index → BitVec 128) :
    unpackUnopenedDigests positions (serializeReplyPairs
      (((hiddenIndices positions).map Subtype.val).map (leafOracleReplies p messages salts))) =
      fun i => outputDigest (leafOracleReplies p messages salts i.val).2 := by
  funext i
  unfold unpackUnopenedDigests
  rw [read_second_digests, List.map_map, List.map_map]
  have present : i ∈ hiddenIndices positions := by simp [hiddenIndices]
  simp only [List.getElem?_map, List.getElem?_idxOf present, Option.map_some, Option.getD_some, Function.comp_apply]

private theorem opened_message_same {State : Type} {openingSize : Nat}
    (challenge : Hiding.HidingChallenge State openingSize) (index : {i : Index // i ∈ challenge.positions}) :
    messageWords challenge.message₀ index.val = messageWords challenge.message₁ index.val := by
  have values := congrFun challenge.agree index
  exact congrArg (fun entry : Entry => fun word : Fin 32 => entry.extractLsb' (64 * word.val) 64) values

abbrev CompleteSaltTape := Index → BitVec 128

noncomputable def completeSaltSampler : SampleableType CompleteSaltTape := inferInstance

noncomputable def sampleCompleteSaltTape : ProbComp CompleteSaltTape :=
  @uniformSample _ completeSaltSampler

def mergeSaltTape {positions : Positions} (opened : OpenedSalts positions) (closed : UnopenedSalts positions) :
    CompleteSaltTape :=
  fun i => if selected : i ∈ positions then opened ⟨i, selected⟩ else closed ⟨i, selected⟩

theorem split_salt_tape {α : Type} (positions : Positions) (next : CompleteSaltTape → ProbComp α) :
    (($ᵗ CompleteSaltTape) >>= next) =ᵈ
      (do let opened ← $ᵗ OpenedSalts positions
          let closed ← $ᵗ UnopenedSalts positions
          next (mergeSaltTape opened closed)) := by
  let split := Equiv.piEquivPiSubtypeProd (· ∈ positions) (fun _ : Index => BitVec 128)
  apply (uniform_transport_bind (transportOfEquiv split) next).trans
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  rfl

theorem reunited_digest_tape {State : Type} {openingSize : Nat}
    (challenge : Hiding.HidingChallenge State openingSize) (p : BiPermutation Block)
    (openSalts : OpenedSalts challenge.positions) (closedSalts : UnopenedSalts challenge.positions)
    (which : Bool) :
    let m := if which then challenge.message₁ else challenge.message₀
    fullDigestTape (positions := challenge.positions)
      (fun i => outputDigest (leafOracleReplies p (messageWords challenge.message₀) (publicOpenedSalts openSalts) i.val).2)
      (fun i => outputDigest (leafOracleReplies p (messageWords m) (publicSaltTape closedSalts) i.val).2) =
    fun i => outputDigest (leafOracleReplies p (messageWords m) (mergeSaltTape openSalts closedSalts) i).2 := by
  funext i
  by_cases selected : i ∈ challenge.positions
  · have same := opened_message_same challenge ⟨i, selected⟩
    change messageWords challenge.message₀ i = messageWords challenge.message₁ i at same
    cases which <;>
      simp [fullDigestTape, leafOracleReplies, publicOpenedSalts, mergeSaltTape, selected, ← same]
  · simp [fullDigestTape, leafOracleReplies, publicSaltTape, mergeSaltTape, selected]


def fullLeafDigests (p : BiPermutation Block) (message : Message) (salts : CompleteSaltTape) : DigestTape :=
  fun i => outputDigest (leafOracleReplies p (messageWords message) salts i).2

def honestView (build : TranscriptBuilder) (compress : Compression) (p : BiPermutation Block)
    (message : Message) (positions : Positions) (salts : CompleteSaltTape) : Commitment × Proof :=
  build compress positions (fun i => salts i.val) (fullLeafDigests p message salts)

def observeHonestView {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (challenge : Hiding.HidingChallenge State openingSize) (which : Bool)
    (p : BiPermutation Block) (salts : CompleteSaltTape) : ProbComp Output :=
  let message := if which then challenge.message₁ else challenge.message₀
  let (root, proof) := honestView build compress p message challenge.positions salts
  fixedOracleRun (fixedOracle compress p) (adversary.observe challenge.aux root proof)

noncomputable def eagerFullReference {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (which : Bool) : ProbComp Output := do
  let p ← (PermutationCache.empty Block).sample
  let challenge ← eagerRun compress p.val adversary.choose
  let salts ← sampleCompleteSaltTape
  observeHonestView adversary build compress challenge which p.val salts

private def observeTape {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (challenge : Hiding.HidingChallenge State openingSize)
    (opened : OpenedSalts challenge.positions) (tape : DigestTape) : OracleComp World Output :=
  let (root, proof) := build compress challenge.positions opened tape
  adversary.observe challenge.aux root proof

private theorem staged_eager_view {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (challenge : Hiding.HidingChallenge State openingSize) (which : Bool)
    (p : BiPermutation Block) (opened : OpenedSalts challenge.positions)
    (closed : UnopenedSalts challenge.positions) :
    let message := if which then challenge.message₁ else challenge.message₀
    let plans := leafPlans (messageWords challenge.message₀) (publicOpenedSalts opened) challenge.positions.toList
    let continuation := fun raw p =>
      let openedDigests := readOpenedDigests challenge.positions raw.reverse
      let hiddenPhase := unopenedPlans challenge.positions (messageWords message) (publicSaltTape closed)
      runPlanned (fun remaining p => fixedOracleRun (fixedOracle compress p)
        (observeTape adversary build compress challenge opened
          (fullDigestTape openedDigests (unpackUnopenedDigests challenge.positions remaining.reverse)))) p [] hiddenPhase
    runPlanned continuation p [] plans =
      observeHonestView adversary build compress challenge which p (mergeSaltTape opened closed) := by
  dsimp only
  rw [real_planned_leaf_replies]
  simp only [List.append_nil, List.reverse_reverse, eager_opened_digests, unopenedPlans]
  rw [real_planned_leaf_replies]
  simp only [List.append_nil, List.reverse_reverse, eager_unopened_digests, reunited_digest_tape]
  have openCoin : (fun i : {i : Index // i ∈ challenge.positions} => mergeSaltTape opened closed i.val) = opened := by
    funext i
    unfold mergeSaltTape
    exact dite_eq_left i.property
  unfold observeHonestView honestView
  rw [openCoin]
  unfold observeTape fullLeafDigests
  dsimp only

theorem eager_reference_equivalence {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (which : Bool) :
    eagerFullReference adversary build compress which =ᵈ
      twoPhaseReference adversary build compress which := by
  let finish := fun challenge p => ($ᵗ CompleteSaltTape) >>= observeHonestView adversary build compress challenge which p
  apply (adaptive_posterior_equivalence compress adversary.choose (PermutationCache.empty Block) finish).trans
  unfold twoPhaseReference
  apply EvalDistEq.bind_right
  rintro ⟨challenge, initial⟩
  let message := if which then challenge.message₁ else challenge.message₀
  let plan (opened : OpenedSalts challenge.positions) :=
    leafPlans (messageWords challenge.message₀) (publicOpenedSalts opened) challenge.positions.toList
  let closedRun (opened : OpenedSalts challenge.positions) (raw : List Block) (p : BiPermutation Block)
      (closed : UnopenedSalts challenge.positions) :=
    runPlanned (fun remaining p => fixedOracleRun (fixedOracle compress p)
      (observeTape adversary build compress challenge opened
        (fullDigestTape (readOpenedDigests challenge.positions raw.reverse)
          (unpackUnopenedDigests challenge.positions remaining.reverse)))) p []
      (unopenedPlans challenge.positions (messageWords message) (publicSaltTape closed))
  let readOpened (opened : OpenedSalts challenge.positions) (p : Completion initial.entries) :=
    runPlanned (fun raw p => ($ᵗ UnopenedSalts challenge.positions) >>= closedRun opened raw p) p.val [] (plan opened)
  trans (do let p ← initial.sample
            let opened ← $ᵗ OpenedSalts challenge.positions
            readOpened opened p)
  · apply EvalDistEq.bind_right
    intro p
    dsimp only [finish]
    apply (split_salt_tape challenge.positions
      (observeHonestView adversary build compress challenge which p.val)).trans
    apply EvalDistEq.bind_right
    intro opened
    unfold readOpened
    rw [real_planned_leaf_replies]
    apply EvalDistEq.bind_right
    intro closed
    have same := staged_eager_view adversary build compress challenge which p.val opened closed
    dsimp only at same
    rw [real_planned_leaf_replies] at same
    exact (EvalDistEq.of_evalDist_eq (congrArg evalDist same)).symm
  · apply (EvalDistEq.of_evalDist_eq
      (distribution_bind_comm ($ᵗ OpenedSalts challenge.positions) initial.sample readOpened)).symm.trans
    apply EvalDistEq.bind_right
    intro opened
    apply (prepared_posterior_equivalence
      (fun raw p => ($ᵗ UnopenedSalts challenge.positions) >>= closedRun opened raw p) initial [] (plan opened)).trans
    apply EvalDistEq.bind_right
    rintro ⟨raw, posterior⟩
    have comm := distribution_bind_comm ($ᵗ UnopenedSalts challenge.positions) posterior.sample
      (fun closed p => closedRun opened raw p.val closed)
    exact (EvalDistEq.of_evalDist_eq comm).symm

theorem eager_two_stage_hiding {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (budget : Nat) (bounded : Hiding.QueryBound adversary budget) :
    measureTVDist (eagerFullReference adversary build compress false)
      (eagerFullReference adversary build compress true) ≤ min 1 (((budget : ℝ) + 1) / 2 ^ 120) := by
  unfold measureTVDist
  rw [(eager_reference_equivalence adversary build compress false).evalDist_eq,
    (eager_reference_equivalence adversary build compress true).evalDist_eq]
  exact two_phase_reference_hiding adversary build compress budget bounded

end TwoPermutationPrototype.Sampling
