import CommitGolfCandidate.TwoPermutationQuadSpec
import CommitGolfCandidate.NonceChainLayout

/-! Quad design + 31727a8 NonceChain salt generator: interface.

The honest salts are no longer an independent uniform tape `sampleCompleteSaltTape`; they are
`actualNonces π k` for a uniform 192-bit seed `k`: the forward orbit of `seedState k` under the
public permutation `π`, each reply giving eleven 128-bit salts (the 192-bit suffix stays hidden),
projected onto the first `LENGTH` coordinates. Opening/check/layout are those of the quad design
(`TwoPermutationQuadSpec`, unchanged); only the commit distribution changes. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
open CommitGolfCandidate.Permutation.NonceChain (Key actualNonces)

/-- Executable commit-and-open transcript = quad honest view with nonce-chain salts. -/
def QuadNonceTranscriptRefines (scheme : Scheme) (build : QuadTranscriptBuilder) : Prop :=
  ∀ (oracle : Oracle) (message : Message) (positions : Positions),
    fixedOracleRun oracle (executableTranscript scheme message positions) =ᵈ
      (do let k ← $ᵗ Key
          pure (quadHonestView build oracle.compression (BiPermutation.equiv Block oracle.permutation)
            message positions (actualNonces oracle.permutation k)))

/-- The builder reads the quad node function only on the `LENGTH/4` honest group inputs. -/
def QuadBuildLocal (build : QuadTranscriptBuilder) : Prop :=
  ∀ (compress : Compression) (quad quad' : QuadFunction) (positions : Positions)
    (salts : OpenedSalts positions) (leaves : DigestTape),
    (∀ g, g < LENGTH / 4 → quad (quadGroupLeaves leaves g) = quad' (quadGroupLeaves leaves g)) →
      build compress quad positions salts leaves = build compress quad' positions salts leaves

theorem reference_heap_congr (compress : Compression) (leafCount : Nat)
    (leaf leaf' : Nat → Digest) (same : ∀ g, g < leafCount → leaf g = leaf' g) :
    ∀ node, referenceHeap compress leafCount leaf node = referenceHeap compress leafCount leaf' node := by
  intro node
  induction hm : 2 * leafCount - node using Nat.strong_induction_on generalizing node with
  | _ m ih =>
    rw [referenceHeap.eq_def compress leafCount leaf node, referenceHeap.eq_def compress leafCount leaf' node]
    split_ifs with branch range
    · rw [ih (2 * leafCount - 2 * node) (by omega) (2 * node) rfl,
        ih (2 * leafCount - (2 * node + 1)) (by omega) (2 * node + 1) rfl]
    · exact same _ (by omega)
    · rfl

theorem quad_heap_congr (compress : Compression) (quad quad' : QuadFunction) (leaves : DigestTape)
    (same : ∀ g, g < LENGTH / 4 → quad (quadGroupLeaves leaves g) = quad' (quadGroupLeaves leaves g)) :
    quadHeap compress quad leaves = quadHeap compress quad' leaves := by
  unfold quadHeap
  funext node
  exact reference_heap_congr _ _ _ _ same node

theorem quad_transcript_builder_local : QuadBuildLocal quadTranscriptBuilder := by
  intro compress quad quad' positions salts leaves same
  unfold quadTranscriptBuilder
  rw [quad_heap_congr compress quad quad' leaves same]

/-- What the commit side must deliver for quad + NonceChain (replaces `QuadCommitTranscript`):
the trapdoor is a function of the seed `k`, and every salt/leaf/heap fact holds for the
chain salts `actualNonces oracle.permutation k`. -/
structure QuadNonceCommitTranscript (s : Submission) where
  trapdoor : Oracle → Message → Key → BitVec (8 * s.sizes.trapdoor)
  distribution : ∀ oracle message,
    fixedOracleRun oracle (s.scheme.commit message) =ᵈ
      (do let k ← $ᵗ Key
          pure (quadPublicTree oracle message (actualNonces oracle.permutation k) 1, trapdoor oracle message k))
  nonce : ∀ oracle message k index,
    quadTrapdoorSalt (trapdoor oracle message k) index = actualNonces oracle.permutation k index
  leaf : ∀ oracle message k index,
    quadTrapdoorLeaf (trapdoor oracle message k) index =
      quadPublicLeaves oracle message (actualNonces oracle.permutation k) index
  heap : ∀ oracle message k node, 0 < node → node < LENGTH / 2 →
    quadTrapdoorHeap (trapdoor oracle message k) node =
      quadPublicTree oracle message (actualNonces oracle.permutation k) node

end TwoPermutationPrototype.Sampling
