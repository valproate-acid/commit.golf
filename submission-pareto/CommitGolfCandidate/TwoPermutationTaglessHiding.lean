import CommitGolfCandidate.TwoPermutationTaglessHidingTransport
import CommitGolfCandidate.TwoPermutationTaglessEager

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate

private theorem view_eq (build : TranscriptBuilder) (compress : Compression) (p : BiPermutation Block)
    (message : Message) (positions : Positions) (salts : CompleteSaltTape) :
    taglessHonestView build compress p message positions salts =
      taglessEagerHonestView build compress p message positions salts := by
  unfold taglessHonestView taglessEagerHonestView
  have digests : taglessFullLeafDigests p message salts = taglessEagerLeafDigests p message salts := by
    funext index
    exact (tagless_eager_leaf_digest_row p message salts index).symm
  rw [digests]

private theorem reference_eq {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (which : Bool) :
    taglessViewReference adversary build compress which = taglessEagerFullReference adversary build compress which := by
  simp only [taglessViewReference, taglessEagerFullReference, observeTranscriptView, taglessObserveEagerView, view_eq]

theorem tagless_hiding_of_transcript (scheme : Scheme) (build : TranscriptBuilder)
    (refines : TaglessTranscriptRefines scheme build) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) := by
  apply scheme_hiding_of_tagless_transcript scheme build refines
  intro State Output openingSize adversary compress budget bounded
  rw [reference_eq adversary build compress false, reference_eq adversary build compress true]
  exact tagless_eager_two_stage_hiding adversary build compress budget bounded

end TwoPermutationPrototype.Sampling
