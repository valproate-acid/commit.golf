import CommitGolfCandidate.TwoPermutationPinnedTranscript

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 650000
set_option exponentiation.threshold 2048

local instance pinnedTransportDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

noncomputable def pinnedViewReference {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (which : Bool) : ProbComp Output := do
  let permutation ← (PermutationCache.empty Block).sample
  let challenge ← eagerRun compress permutation.val adversary.choose
  let salts ← sampleCompleteSaltTape
  observeTranscriptView adversary (pinnedHonestView build) compress challenge which permutation.val salts

theorem pinned_sampled_reference_eq {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (which : Bool) :
    sampledReferenceView adversary (pinnedHonestView build) which =ᵈ
      (($ᵗ Compression) >>= fun compress => pinnedViewReference adversary build compress which) := by
  unfold sampledReferenceView Oracle.sample
  simp only [bind_assoc, pure_bind]
  apply EvalDistEq.bind_right ($ᵗ Compression)
  intro compress
  let : SampleableType (Completion (PermutationCache.empty Block).entries) :=
    (PermutationCache.empty Block).completionSampler
  let next (permutation : Perm) := do
    let challenge ← fixedOracleRun ⟨compress, permutation⟩ adversary.choose
    let salts ← sampleCompleteSaltTape
    observeTranscriptView adversary (pinnedHonestView build) compress challenge which
      (BiPermutation.equiv Block permutation) salts
  apply (uniform_transport_bind emptyTransport next).trans
  unfold pinnedViewReference
  apply EvalDistEq.bind_right
  intro completion
  simp only [next, ← eager_fixed_handler, emptyTransport, Equiv.apply_symm_apply]
  rfl

theorem scheme_hiding_of_pinned_transcript (scheme : Scheme) (build : TranscriptBuilder)
    (refines : PinnedTranscriptRefines scheme build)
    (referenceBound : ∀ {State Output : Type} {openingSize : Nat}
      (adversary : Hiding.HidingAdversary State Output openingSize) (compress : Compression) (budget : Nat),
      Hiding.QueryBound adversary budget →
      measureTVDist (pinnedViewReference adversary build compress false)
        (pinnedViewReference adversary build compress true) ≤ min 1 (((budget : ℝ) + 1) / 2 ^ 120)) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) := by
  apply scheme_hiding_of_transcript_view scheme (pinnedHonestView build) refines
  intro State Output openingSize adversary budget bounded
  unfold measureTVDist
  rw [(pinned_sampled_reference_eq adversary build false).evalDist_eq,
    (pinned_sampled_reference_eq adversary build true).evalDist_eq]
  apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
  intro compress
  exact referenceBound adversary compress budget bounded

end TwoPermutationPrototype.Sampling
