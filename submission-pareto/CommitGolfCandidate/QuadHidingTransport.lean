import CommitGolfCandidate.TwoPermutationQuadSpec
import CommitGolfCandidate.TwoPermutationPinnedHidingTransport

/-! Quad analogue of `pinnedViewReference` / `pinned_sampled_reference_eq`. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 650000
set_option exponentiation.threshold 2048

local instance quadTransportDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

noncomputable def quadViewReference {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : QuadTranscriptBuilder)
    (compress : Compression) (which : Bool) : ProbComp Output := do
  let permutation ← (PermutationCache.empty Block).sample
  let challenge ← eagerRun compress permutation.val adversary.choose
  let salts ← sampleCompleteSaltTape
  observeTranscriptView adversary (quadHonestView build) compress challenge which permutation.val salts

theorem quad_sampled_reference_eq {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : QuadTranscriptBuilder)
    (which : Bool) :
    sampledReferenceView adversary (quadHonestView build) which =ᵈ
      (($ᵗ Compression) >>= fun compress => quadViewReference adversary build compress which) := by
  unfold sampledReferenceView Oracle.sample
  simp only [bind_assoc, pure_bind]
  apply EvalDistEq.bind_right ($ᵗ Compression)
  intro compress
  let : SampleableType (Completion (PermutationCache.empty Block).entries) :=
    (PermutationCache.empty Block).completionSampler
  let next (permutation : Perm) := do
    let challenge ← fixedOracleRun ⟨compress, permutation⟩ adversary.choose
    let salts ← sampleCompleteSaltTape
    observeTranscriptView adversary (quadHonestView build) compress challenge which
      (BiPermutation.equiv Block permutation) salts
  apply (uniform_transport_bind emptyTransport next).trans
  unfold quadViewReference
  apply EvalDistEq.bind_right
  intro completion
  simp only [next, ← eager_fixed_handler, emptyTransport, Equiv.apply_symm_apply]
  rfl

end TwoPermutationPrototype.Sampling
