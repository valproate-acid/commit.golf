import CommitGolfCandidate.TaggedPinnedModel
import CommitGolfCandidate.TwoPermutationTranscript

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate OracleComp

def pinnedHonestView (build : TranscriptBuilder) (compress : Compression) (p : BiPermutation Block)
    (message : Message) (positions : Positions) (salts : CompleteSaltTape) : Commitment × Proof :=
  build compress positions (fun index => salts index.val) (pinnedFullLeafDigests p message salts)

abbrev PinnedTranscriptRefines (scheme : Scheme) (build : TranscriptBuilder) :=
  TranscriptRefinesView scheme (pinnedHonestView build)

end TwoPermutationPrototype.Sampling
