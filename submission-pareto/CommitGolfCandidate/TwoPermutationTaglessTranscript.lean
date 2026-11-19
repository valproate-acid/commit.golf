import CommitGolfCandidate.TwoPermutationTaglessBinding
import CommitGolfCandidate.TwoPermutationTranscript

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate OracleComp

def taglessFullLeafDigests (p : BiPermutation Block) (message : Message)
    (salts : CompleteSaltTape) : DigestTape :=
  fun index =>
    let words := messageWords message index
    let first := firstRow p.forward index (saltWords (salts index)) words
    outputDigest (taglessSecondRow p.forward words first.2).2

def taglessHonestView (build : TranscriptBuilder) (compress : Compression) (p : BiPermutation Block)
    (message : Message) (positions : Positions) (salts : CompleteSaltTape) : Commitment × Proof :=
  build compress positions (fun index => salts index.val) (taglessFullLeafDigests p message salts)

def TaglessTranscriptRefines (scheme : Scheme) (build : TranscriptBuilder) : Prop :=
  ∀ (oracle : Oracle) (message : Message) (positions : Positions),
    fixedOracleRun oracle (executableTranscript scheme message positions) =ᵈ
      (do let salts ← sampleCompleteSaltTape
          pure (taglessHonestView build oracle.compression (BiPermutation.equiv Block oracle.permutation)
            message positions salts))

end TwoPermutationPrototype.Sampling
