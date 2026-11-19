import CommitGolfCandidate.TwoPermutationTaglessTwoStage
import CommitGolfCandidate.TwoPermutationHidingEager

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 900000
set_option exponentiation.threshold 2048

noncomputable local instance {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

local instance {α : Type} : MeasurableSpace α := ⊤

def taglessLeafOracleReplies (p : BiPermutation Block) (messages : Index → Words 32)
    (salts : Index → BitVec 128) (i : Index) : ReplyPair :=
  let first := p.forward (taglessFirstAddress messages salts i)
  (first, p.forward (taglessSecondAddress messages i first))

theorem tagless_real_planned_leaf_replies {α : Type} (next : List Block → BiPermutation Block → ProbComp α)
    (p : BiPermutation Block) (messages : Index → Words 32) (salts : Index → BitVec 128)
    (indices : List Index) (answers : List Block) :
    runPlanned next p answers (taglessLeafPlans messages salts indices) =
      next ((serializeReplyPairs (indices.map (taglessLeafOracleReplies p messages salts))).reverse ++ answers) p := by
  induction indices generalizing answers with
  | nil => rfl
  | cons i rest ih =>
    have plans : taglessLeafPlans messages salts (i :: rest) =
        [fun _ => taglessFirstAddress messages salts i,
         fun previous => taglessSecondAddress messages i (previous.headD 0)] ++ taglessLeafPlans messages salts rest := rfl
    rw [plans]
    simp only [List.cons_append, List.nil_append, runPlanned, List.headD_cons]
    rw [ih]
    simp only [List.map_cons, serializeReplyPairs, List.flatMap_cons,
      List.cons_append, List.nil_append, List.reverse_cons, List.append_assoc, taglessLeafOracleReplies]

theorem tagless_eager_opened_digests (positions : Positions) (p : BiPermutation Block)
    (messages : Index → Words 32) (salts : Index → BitVec 128) :
    readOpenedDigests positions (serializeReplyPairs (positions.toList.map (taglessLeafOracleReplies p messages salts))) =
      fun i => outputDigest (taglessLeafOracleReplies p messages salts i.val).2 := by
  funext i
  unfold readOpenedDigests
  rw [read_second_digests, List.map_map]
  simp only [List.getElem?_map, List.getElem?_idxOf (Finset.mem_toList.mpr i.property), Option.map_some,
    Option.getD_some, Function.comp_apply]

theorem tagless_eager_unopened_digests (positions : Positions) (p : BiPermutation Block)
    (messages : Index → Words 32) (salts : Index → BitVec 128) :
    unpackUnopenedDigests positions (serializeReplyPairs
      (((hiddenIndices positions).map Subtype.val).map (taglessLeafOracleReplies p messages salts))) =
      fun i => outputDigest (taglessLeafOracleReplies p messages salts i.val).2 := by
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

theorem tagless_reunited_digest_tape {State : Type} {openingSize : Nat}
    (challenge : Hiding.HidingChallenge State openingSize) (p : BiPermutation Block)
    (openSalts : OpenedSalts challenge.positions) (closedSalts : UnopenedSalts challenge.positions)
    (which : Bool) :
    let m := if which then challenge.message₁ else challenge.message₀
    fullDigestTape (positions := challenge.positions)
      (fun i => outputDigest (taglessLeafOracleReplies p (messageWords challenge.message₀) (publicOpenedSalts openSalts) i.val).2)
      (fun i => outputDigest (taglessLeafOracleReplies p (messageWords m) (publicSaltTape closedSalts) i.val).2) =
    fun i => outputDigest (taglessLeafOracleReplies p (messageWords m) (mergeSaltTape openSalts closedSalts) i).2 := by
  funext i
  by_cases selected : i ∈ challenge.positions
  · have same := opened_message_same challenge ⟨i, selected⟩
    change messageWords challenge.message₀ i = messageWords challenge.message₁ i at same
    cases which <;>
      simp [fullDigestTape, taglessLeafOracleReplies, taglessFirstAddress, taglessSecondAddress, publicOpenedSalts, mergeSaltTape, selected, ← same]
  · simp [fullDigestTape, taglessLeafOracleReplies, taglessFirstAddress, taglessSecondAddress, publicSaltTape, mergeSaltTape, selected]


def taglessEagerLeafDigests (p : BiPermutation Block) (message : Message) (salts : CompleteSaltTape) : DigestTape :=
  fun i => outputDigest (taglessLeafOracleReplies p (messageWords message) salts i).2

theorem tagless_eager_leaf_digest_row (p : BiPermutation Block) (message : Message)
    (salts : CompleteSaltTape) (i : Index) :
    taglessEagerLeafDigests p message salts i =
      let a := firstRow p.forward i (saltWords (salts i)) (messageWords message i)
      outputDigest (taglessSecondRow p.forward (messageWords message i) a.2).2 := by
  let reply := (firstRow p.forward i (saltWords (salts i)) (messageWords message i)).2
  exact congrArg (fun input : Block => outputDigest (p.forward input))
    (tagless_second_block_exact reply (messageWords message i)).symm

def taglessEagerHonestView (build : TranscriptBuilder) (compress : Compression) (p : BiPermutation Block)
    (message : Message) (positions : Positions) (salts : CompleteSaltTape) : Commitment × Proof :=
  build compress positions (fun i => salts i.val) (taglessEagerLeafDigests p message salts)

def taglessObserveEagerView {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (challenge : Hiding.HidingChallenge State openingSize) (which : Bool)
    (p : BiPermutation Block) (salts : CompleteSaltTape) : ProbComp Output :=
  let message := if which then challenge.message₁ else challenge.message₀
  let (root, proof) := taglessEagerHonestView build compress p message challenge.positions salts
  fixedOracleRun (fixedOracle compress p) (adversary.observe challenge.aux root proof)

noncomputable def taglessEagerFullReference {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (which : Bool) : ProbComp Output := do
  let p ← (PermutationCache.empty Block).sample
  let challenge ← eagerRun compress p.val adversary.choose
  let salts ← sampleCompleteSaltTape
  taglessObserveEagerView adversary build compress challenge which p.val salts

private def observeTape {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (challenge : Hiding.HidingChallenge State openingSize)
    (opened : OpenedSalts challenge.positions) (tape : DigestTape) : OracleComp World Output :=
  let (root, proof) := build compress challenge.positions opened tape
  adversary.observe challenge.aux root proof

private theorem tagless_staged_eager_view {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (challenge : Hiding.HidingChallenge State openingSize) (which : Bool)
    (p : BiPermutation Block) (opened : OpenedSalts challenge.positions)
    (closed : UnopenedSalts challenge.positions) :
    let message := if which then challenge.message₁ else challenge.message₀
    let plans := taglessLeafPlans (messageWords challenge.message₀) (publicOpenedSalts opened) challenge.positions.toList
    let continuation := fun raw p =>
      let openedDigests := readOpenedDigests challenge.positions raw.reverse
      let hiddenPhase := taglessHiddenPlans challenge.positions (messageWords message) (publicSaltTape closed)
      runPlanned (fun remaining p => fixedOracleRun (fixedOracle compress p)
        (observeTape adversary build compress challenge opened
          (fullDigestTape openedDigests (unpackUnopenedDigests challenge.positions remaining.reverse)))) p [] hiddenPhase
    runPlanned continuation p [] plans =
      taglessObserveEagerView adversary build compress challenge which p (mergeSaltTape opened closed) := by
  dsimp only
  rw [tagless_real_planned_leaf_replies]
  simp only [List.append_nil, List.reverse_reverse, tagless_eager_opened_digests, taglessHiddenPlans]
  rw [tagless_real_planned_leaf_replies]
  simp only [List.append_nil, List.reverse_reverse, tagless_eager_unopened_digests, tagless_reunited_digest_tape]
  have openCoin : (fun i : {i : Index // i ∈ challenge.positions} => mergeSaltTape opened closed i.val) = opened := by
    funext i
    unfold mergeSaltTape
    exact dite_eq_left i.property
  unfold taglessObserveEagerView taglessEagerHonestView
  rw [openCoin]
  unfold observeTape taglessEagerLeafDigests
  dsimp only

theorem tagless_eager_reference_equivalence {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (which : Bool) :
    taglessEagerFullReference adversary build compress which =ᵈ
      taglessTwoPhaseReference adversary build compress which := by
  let finish := fun challenge p => ($ᵗ CompleteSaltTape) >>= taglessObserveEagerView adversary build compress challenge which p
  apply (adaptive_posterior_equivalence compress adversary.choose (PermutationCache.empty Block) finish).trans
  simp only [taglessTwoPhaseReference, taglessOpenedMix, bind_assoc, pure_bind]
  apply EvalDistEq.bind_right
  rintro ⟨challenge, initial⟩
  let message := if which then challenge.message₁ else challenge.message₀
  let plan (opened : OpenedSalts challenge.positions) :=
    taglessLeafPlans (messageWords challenge.message₀) (publicOpenedSalts opened) challenge.positions.toList
  let closedRun (opened : OpenedSalts challenge.positions) (raw : List Block) (p : BiPermutation Block)
      (closed : UnopenedSalts challenge.positions) :=
    runPlanned (fun remaining p => fixedOracleRun (fixedOracle compress p)
      (observeTape adversary build compress challenge opened
        (fullDigestTape (readOpenedDigests challenge.positions raw.reverse)
          (unpackUnopenedDigests challenge.positions remaining.reverse)))) p []
      (taglessHiddenPlans challenge.positions (messageWords message) (publicSaltTape closed))
  let readOpened (opened : OpenedSalts challenge.positions) (p : Completion initial.entries) :=
    runPlanned (fun raw p => ($ᵗ UnopenedSalts challenge.positions) >>= closedRun opened raw p) p.val [] (plan opened)
  trans (do let p ← initial.sample
            let opened ← $ᵗ OpenedSalts challenge.positions
            readOpened opened p)
  · apply EvalDistEq.bind_right
    intro p
    dsimp only [finish]
    apply (split_salt_tape challenge.positions
      (taglessObserveEagerView adversary build compress challenge which p.val)).trans
    apply EvalDistEq.bind_right
    intro opened
    unfold readOpened
    rw [tagless_real_planned_leaf_replies]
    apply EvalDistEq.bind_right
    intro closed
    have same := tagless_staged_eager_view adversary build compress challenge which p.val opened closed
    dsimp only at same
    rw [tagless_real_planned_leaf_replies] at same
    exact (EvalDistEq.of_evalDist_eq (congrArg evalDist same)).symm
  · apply (EvalDistEq.of_evalDist_eq
      (distribution_bind_comm ($ᵗ OpenedSalts challenge.positions) initial.sample readOpened)).symm.trans
    apply EvalDistEq.bind_right
    intro opened
    apply (tagless_opened_posterior (messageWords challenge.message₀) (publicOpenedSalts opened) initial []
      challenge.positions.toList (fun raw p => ($ᵗ UnopenedSalts challenge.positions) >>= closedRun opened raw p)).trans
    apply EvalDistEq.bind_right
    intro result
    have comm := distribution_bind_comm ($ᵗ UnopenedSalts challenge.positions) result.cache.sample
      (fun closed p => closedRun opened result.replies p.val closed)
    exact (EvalDistEq.of_evalDist_eq comm).symm

theorem tagless_eager_two_stage_hiding {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (budget : Nat) (bounded : Hiding.QueryBound adversary budget) :
    measureTVDist (taglessEagerFullReference adversary build compress false)
      (taglessEagerFullReference adversary build compress true) ≤ min 1 (((budget : ℝ) + 1) / 2 ^ 120) := by
  unfold measureTVDist
  rw [(tagless_eager_reference_equivalence adversary build compress false).evalDist_eq,
    (tagless_eager_reference_equivalence adversary build compress true).evalDist_eq]
  exact tagless_two_phase_hiding adversary build compress budget bounded

end TwoPermutationPrototype.Sampling
