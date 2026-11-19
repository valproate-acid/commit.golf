import CommitGolfCandidate.TwoPermutationBindingBridge
import CommitGolfCandidate.TaggedPinnedModel

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate OracleComp

def PinnedLeafWitness (rows : List PublicRow) : Prop :=
  ∃ (perm : Block → Block) (index : Index) (nonce₀ nonce₁ : Words 2) (message₀ message₁ : Words 32),
    let a₀ := pinnedFirstRow perm message₀
    let a₁ := pinnedFirstRow perm message₁
    let b₀ := pinnedSecondRow perm index nonce₀ a₀.2 message₀
    let b₁ := pinnedSecondRow perm index nonce₁ a₁.2 message₁
    PublicRow.permutation a₀.1 a₀.2 ∈ rows ∧ PublicRow.permutation a₁.1 a₁.2 ∈ rows ∧
      PublicRow.permutation b₀.1 b₀.2 ∈ rows ∧ PublicRow.permutation b₁.1 b₁.2 ∈ rows ∧
      outputDigest b₀.2 = outputDigest b₁.2 ∧ message₀ ≠ message₁

def PinnedReplayEvidence (rows : List PublicRow) : Prop :=
  CompressionWitness rows ∨ PinnedLeafWitness rows

abbrev PinnedReplayBound :=
  ∀ (program : OracleComp World Unit) (q calls : Nat),
    1 ≤ q → q ≤ 2 ^ 120 → calls ≤ q + 2 ^ 31 → PublicQueryBound (recordRows program) calls →
    Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
      PinnedReplayEvidence result.2] ≤ (q : ENNReal) / 2 ^ 120

theorem PinnedReplayEvidence.mono {earlier later : List PublicRow} (contained : ∀ row ∈ earlier, row ∈ later)
    (evidence : PinnedReplayEvidence earlier) : PinnedReplayEvidence later := by
  rcases evidence with ⟨x,y,a,b,left,right,different,equal⟩ |
    ⟨perm,index,nonce₀,nonce₁,msg₀,msg₁,a₀,a₁,b₀,b₁,digest,conflict⟩
  · exact Or.inl ⟨x,y,a,b,contained _ left,contained _ right,different,equal⟩
  · exact Or.inr ⟨perm,index,nonce₀,nonce₁,msg₀,msg₁,
      contained _ a₀,contained _ a₁,contained _ b₀,contained _ b₁,digest,conflict⟩

end TwoPermutationPrototype.Sampling
