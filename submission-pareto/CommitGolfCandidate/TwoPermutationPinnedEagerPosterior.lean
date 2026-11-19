import CommitGolfCandidate.TwoPermutationPinnedHidingTransport

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
attribute [local irreducible] pinnedFullLeafDigests

noncomputable local instance {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

noncomputable def pinnedObserveTape {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (challenge : Hiding.HidingChallenge State openingSize)
    (opened : OpenedSalts challenge.positions) (digest : DigestTape) (p : BiPermutation Block) :
    ProbComp Output :=
  let (root, proof) := build compress challenge.positions opened digest
  fixedOracleRun (fixedOracle compress p) (adversary.observe challenge.aux root proof)

noncomputable def pinnedViewPosterior {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (which : Bool) : ProbComp Output := do
  let (challenge, initial) ← lazyRun compress adversary.choose (PermutationCache.empty Block)
  let opened ← $ᵗ OpenedSalts challenge.positions
  let closed ← $ᵗ UnopenedSalts challenge.positions
  let p ← initial.sample
  let message := if which then challenge.message₁ else challenge.message₀
  let digest := pinnedFullLeafDigests p.val message (mergeSaltTape opened closed)
  pinnedObserveTape adversary build compress challenge opened digest p.val

theorem pinned_eager_posterior_eq {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (which : Bool) :
    pinnedViewReference adversary build compress which =ᵈ pinnedViewPosterior adversary build compress which := by
  let finish := fun challenge p => sampleCompleteSaltTape >>= fun salts =>
    observeTranscriptView adversary (pinnedHonestView build) compress challenge which p salts
  apply (adaptive_posterior_equivalence compress adversary.choose (PermutationCache.empty Block) finish).trans
  unfold pinnedViewPosterior
  apply EvalDistEq.bind_right
  rintro ⟨challenge, initial⟩
  let observe (p : Completion initial.entries) (salts : CompleteSaltTape) :=
    observeTranscriptView adversary (pinnedHonestView build) compress challenge which p.val salts
  apply (EvalDistEq.bind_right initial.sample (fun p => split_salt_tape challenge.positions (observe p))).trans
  let runOpened (opened : OpenedSalts challenge.positions) (p : Completion initial.entries) :=
    ($ᵗ UnopenedSalts challenge.positions) >>= fun closed => observe p (mergeSaltTape opened closed)
  trans (do let p ← initial.sample
            let opened ← $ᵗ OpenedSalts challenge.positions
            runOpened opened p)
  · apply EvalDistEq.bind_right initial.sample
    intro p
    apply EvalDistEq.bind_right ($ᵗ OpenedSalts challenge.positions)
    intro opened
    rfl
  have reorderOpened := EvalDistEq.of_evalDist_eq (distribution_bind_comm initial.sample
    ($ᵗ OpenedSalts challenge.positions) (fun p opened => runOpened opened p))
  refine reorderOpened.trans ?_
  dsimp only
  apply EvalDistEq.bind_right ($ᵗ OpenedSalts challenge.positions)
  intro opened
  unfold runOpened
  have reorderClosed := EvalDistEq.of_evalDist_eq (distribution_bind_comm initial.sample
    ($ᵗ UnopenedSalts challenge.positions) (fun p closed => observe p (mergeSaltTape opened closed)))
  refine reorderClosed.trans ?_
  apply EvalDistEq.bind_right ($ᵗ UnopenedSalts challenge.positions)
  intro closed
  apply EvalDistEq.bind_right initial.sample
  intro p
  have salt_eq : (fun i : {i : Index // i ∈ challenge.positions} => mergeSaltTape opened closed i.val) = opened := by
    funext i
    exact dite_eq_left i.property
  unfold observe observeTranscriptView pinnedHonestView pinnedObserveTape
  rw [salt_eq]

end TwoPermutationPrototype.Sampling
