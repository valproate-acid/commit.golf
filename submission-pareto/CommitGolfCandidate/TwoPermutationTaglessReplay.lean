import CommitGolfCandidate.TwoPermutationBindingBridge
import CommitGolfCandidate.TwoPermutationTaglessBinding

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate OracleComp.DeferredSampling
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

def TaglessLeafWitness (rows : List PublicRow) : Prop :=
  ∃ (perm : Block → Block) (index : Index) (nonce₀ nonce₁ : Words 2) (message₀ message₁ : Words 32),
    let a₀ := firstRow perm index nonce₀ message₀
    let a₁ := firstRow perm index nonce₁ message₁
    let b₀ := taglessSecondRow perm message₀ a₀.2
    let b₁ := taglessSecondRow perm message₁ a₁.2
    PublicRow.permutation a₀.1 a₀.2 ∈ rows ∧ PublicRow.permutation a₁.1 a₁.2 ∈ rows ∧
      PublicRow.permutation b₀.1 b₀.2 ∈ rows ∧ PublicRow.permutation b₁.1 b₁.2 ∈ rows ∧
      outputDigest b₀.2 = outputDigest b₁.2 ∧ message₀ ≠ message₁

def TaglessReplayEvidence (rows : List PublicRow) : Prop :=
  CompressionWitness rows ∨ TaglessLeafWitness rows

theorem TaglessReplayEvidence.mono {earlier later : List PublicRow} (contained : ∀ row ∈ earlier, row ∈ later)
    (evidence : TaglessReplayEvidence earlier) : TaglessReplayEvidence later := by
  rcases evidence with ⟨x,y,a,b,left,right,different,equal⟩ |
    ⟨perm,index,nonce₀,nonce₁,msg₀,msg₁,a₀,a₁,b₀,b₁,digest,conflict⟩
  · exact Or.inl ⟨x,y,a,b,contained _ left,contained _ right,different,equal⟩
  · exact Or.inr ⟨perm,index,nonce₀,nonce₁,msg₀,msg₁,
      contained _ a₀,contained _ a₁,contained _ b₀,contained _ b₁,digest,conflict⟩

private theorem leaf_witness_stored (rows : List PublicRow) (cache : Cache)
    (stores : ∀ row ∈ rows, permutationStored cache row) (hit : TaglessLeafWitness rows) :
    HasTaglessReplayedLeafCollision cache := by
  obtain ⟨perm,index,nonce₀,nonce₁,msg₀,msg₁,a₀,a₁,b₀,b₁,digest,conflict⟩ := hit
  exact ⟨perm,index,nonce₀,nonce₁,msg₀,msg₁,stores _ a₀,stores _ a₁,stores _ b₀,stores _ b₁,digest,conflict⟩

private theorem fixed_compression_tagless_bound {α : Type} (compress : Compression)
    (program : OracleComp World α) (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120)
    (withReplay : calls ≤ q + 2 ^ 31) (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress, p⟩ (recordRows program))}[
      TaglessLeafWitness result.2] ≤ (q : ENNReal) / 2 ^ 122 := by
  simp only [fixed_run_eq_simulate]
  rw [(adaptive_cache_from_empty compress (recordRows program)).prEvent_eq
    (fun result => TaglessLeafWitness result.2), prEvent_map]
  refine (prEvent_mono_of_support _ _ _ (fun result reached hit => ?_)).trans
    (tagless_replayed_leaf_collision_le compress (recordRows program) q calls positive small withReplay bounded)
  exact leaf_witness_stored result.1.2 result.2
    (permutation_replay_stored compress program (PermutationCache.empty Block) result reached) hit

private theorem sampled_tagless_replay_bound {α : Type} (program : OracleComp World α)
    (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
      TaglessReplayEvidence result.2] ≤ (q : ENNReal) / 2 ^ 120 := by
  unfold TaglessReplayEvidence
  refine (prEvent_or_le _ _ _).trans ((add_le_add ?_ ?_).trans_eq (event_budget_sum q))
  · have exchanged := EvalDistEq.of_evalDist_eq
      (distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm) (fun compress perm =>
        fixedOracleRun ⟨compress, perm⟩ (recordRows program)))
    simp only [Oracle.sample, bind_assoc, pure_bind]
    rw [exchanged.prEvent_eq (fun result => CompressionWitness result.2)]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun p _ =>
      fixed_permutation_projected_bound p program q calls positive small withReplay bounded
  · simp only [Oracle.sample, bind_assoc, pure_bind]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun compress _ =>
      fixed_compression_tagless_bound compress program q calls positive small withReplay bounded

theorem scheme_binding_of_tagless_replay (scheme : Scheme)
    (spec : BindingReplayEvidence scheme TaglessReplayEvidence) : scheme.Binding :=
  scheme_binding_of_replay_with scheme spec (fun included evidence => evidence.mono included)
    sampled_tagless_replay_bound

end TwoPermutationPrototype.Sampling
