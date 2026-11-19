import CommitGolfCandidate.QuadHidingFinal

/-! Hiding for the quad design: the 8d2a211 pinned leaves feed a 4-ary permutation node layer
`quadFunction p.forward` over the SAME permutation. The proof follows
`pinned_final_reference_hiding` / `scheme_hiding_of_pinned_transcript`; the observer additionally
sees the quad node function, and the only changed step (`quad_conditional_to_reference`) pays
`2^24 · 2^-575` per side for programmed hidden rows whose preimage would land in the quad domain. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 650000
set_option exponentiation.threshold 2048

local instance quadHidingDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

/-- Hiding of any scheme whose executable commit-and-open transcript is the quad honest view. -/
theorem quad_hiding_of_transcript (scheme : Scheme) (build : QuadTranscriptBuilder)
    (refines : QuadTranscriptRefines scheme build) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) := by
  apply scheme_hiding_of_transcript_view scheme (quadHonestView build) refines
  intro State Output openingSize adversary budget bounded
  unfold measureTVDist
  rw [(quad_sampled_reference_eq adversary build false).evalDist_eq,
    (quad_sampled_reference_eq adversary build true).evalDist_eq]
  apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
  intro compress
  exact quad_final_reference_hiding adversary build compress budget bounded

end TwoPermutationPrototype.Sampling
