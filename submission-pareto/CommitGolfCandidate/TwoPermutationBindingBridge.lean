import CommitGolfCandidate.TwoPermutationBindingTrace
import CommitGolfCandidate.ProjectedCollisionROM
import CommitGolfCandidate.HidingReprogram

/-! The executable reduction supplies a checker replay and its deterministic
evidence theorem. This module pays for replay and applies both oracle bounds. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate OracleComp.DeferredSampling
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

def CompressionWitness (rows : List PublicRow) : Prop :=
  ∃ (input₀ input₁ : BitVec 512) (reply₀ reply₁ : BitVec 256),
    PublicRow.compression input₀ reply₀ ∈ rows ∧ PublicRow.compression input₁ reply₁ ∈ rows ∧
      input₀ ≠ input₁ ∧ low240 reply₀ = low240 reply₁

def LeafWitness (rows : List PublicRow) : Prop :=
  ∃ (perm : Block → Block) (index : Index) (nonce₀ nonce₁ : Words 2) (message₀ message₁ : Words 32),
    let a₀ := firstRow perm index nonce₀ message₀
    let a₁ := firstRow perm index nonce₁ message₁
    let b₀ := secondRow perm index message₀ a₀.2
    let b₁ := secondRow perm index message₁ a₁.2
    PublicRow.permutation a₀.1 a₀.2 ∈ rows ∧ PublicRow.permutation a₁.1 a₁.2 ∈ rows ∧
      PublicRow.permutation b₀.1 b₀.2 ∈ rows ∧ PublicRow.permutation b₁.1 b₁.2 ∈ rows ∧
      outputDigest b₀.2 = outputDigest b₁.2 ∧ message₀ ≠ message₁

def ReplayEvidence (rows : List PublicRow) : Prop :=
  CompressionWitness rows ∨ LeafWitness rows

theorem ReplayEvidence.mono {earlier later : List PublicRow} (contained : ∀ row ∈ earlier, row ∈ later)
    (evidence : ReplayEvidence earlier) : ReplayEvidence later := by
  rcases evidence with ⟨x, y, value, value', left, right, different, equal⟩ |
    ⟨perm, index, nonce₀, nonce₁, msg₀, msg₁, a₀, a₁, b₀, b₁, digest, conflict⟩
  · exact Or.inl ⟨x, y, value, value', contained _ left, contained _ right, different, equal⟩
  · exact Or.inr ⟨perm, index, nonce₀, nonce₁, msg₀, msg₁,
      contained _ a₀, contained _ a₁, contained _ b₀, contained _ b₁, digest, conflict⟩

/-- Replay may execute both verifier images. Its public queries must fit the
fixed overhead on every path, and its actual recorded replies must expose
one of the two witness types whenever both conflicting openings are accepted. -/
structure BindingReplayEvidence (scheme : Scheme) (witness : List PublicRow → Prop) where
  replay : Scheme.Claim → OracleComp World Unit
  bounded : ∀ claim, PublicQueryBound (replay claim) (2 ^ 31)
  extracts : ∀ oracle claim, scheme.Breaks oracle claim →
    ∀ result ∈ support (fixedOracleRun oracle (recordRows (replay claim))), witness result.2

abbrev BindingReplayRefines (scheme : Scheme) := BindingReplayEvidence scheme ReplayEvidence

def replayOption (replay : Scheme.Claim → OracleComp World Unit) : Option Scheme.Claim → OracleComp World Unit
  | none => pure ()
  | some claim => replay claim

def boundedReplay (replay : Scheme.Claim → OracleComp World Unit) (adversary : Scheme.Adversary)
    (budget : Nat) : OracleComp World Unit :=
  limitPublicQueries adversary budget >>= replayOption replay

theorem bounded_replay_queries (scheme : Scheme) {witness : List PublicRow → Prop}
    (spec : BindingReplayEvidence scheme witness)
    (adversary : Scheme.Adversary) (budget : Nat) :
    PublicQueryBound (recordRows (boundedReplay spec.replay adversary budget)) (budget + 2 ^ 31) := by
  apply record_rows_bound
  apply public_query_bound_bind (limit_public_bound adversary budget)
  intro limited
  cases limited with
  | none => trivial
  | some claim => exact spec.bounded claim

private theorem projected_witness_stored (rows : List PublicRow) (cache : CompressionCache)
    (stores : ∀ row ∈ rows, compressionStored cache row) (hit : CompressionWitness rows) :
    ProjectedCollision cache := by
  obtain ⟨x, y, a, b, left, right, different, equal⟩ := hit
  have query₀ : cache x = some a := stores _ left
  have query₁ : cache y = some b := stores _ right
  refine ⟨x, y, low240 a, low240 b, different, ?_, ?_, heq_of_eq equal⟩
  · change Option.map low240 (cache x) = some (low240 a)
    rw [query₀]
    rfl
  · change Option.map low240 (cache y) = some (low240 b)
    rw [query₁]
    rfl

private theorem leaf_witness_stored (rows : List PublicRow) (cache : Cache)
    (stores : ∀ row ∈ rows, permutationStored cache row) (hit : LeafWitness rows) :
    HasReplayedLeafCollision cache := by
  obtain ⟨perm, index, nonce₀, nonce₁, msg₀, msg₁, a₀, a₁, b₀, b₁, digest, conflict⟩ := hit
  exact ⟨perm, index, nonce₀, nonce₁, msg₀, msg₁,
    stores _ a₀, stores _ a₁, stores _ b₀, stores _ b₁, digest, conflict⟩

private theorem replay_dominated (scheme : Scheme) {witness : List PublicRow → Prop}
    (spec : BindingReplayEvidence scheme witness)
    (preserves : ∀ {earlier later}, (∀ row ∈ earlier, row ∈ later) → witness earlier → witness later)
    (oracle : Oracle) (adversary : Scheme.Adversary) (budget : Nat) :
    Pr{let result ← oracle.run adversary}[scheme.Breaks oracle result.1 ∧ result.2 ≤ budget] ≤
      Pr{let result ← fixedOracleRun oracle (recordRows (boundedReplay spec.replay adversary budget))}[
        witness result.2] := by
  classical
  let limited := limitPublicQueries adversary budget
  let start := fixedOracleRun oracle (recordRows limited)
  let good (limited : Option Scheme.Claim) := ∃ claim, limited = some claim ∧ scheme.Breaks oracle claim
  have projected : Prod.fst <$> start = fixedOracleRun oracle limited := by
    rw [← fixed_oracle_run_map, record_rows_erase]
  have prefixWin :
      Pr{let result ← start}[good result.1] =
        Pr{let result ← oracle.run adversary}[scheme.Breaks oracle result.1 ∧ result.2 ≤ budget] := by
    rw [← limit_public_probability oracle adversary budget (scheme.Breaks oracle)]
    have event := congrArg (fun x : ProbComp (Option Scheme.Claim) => Pr{let result ← x}[good result]) projected
    simpa only [prEvent_map, fixedOracleRun, Function.comp_def, good, limited] using event
  rw [← prefixWin]
  unfold boundedReplay
  rw [record_rows_bind, fixed_oracle_run_bind]
  change Pr{let result ← start}[good result.1] ≤ _
  rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  rintro ⟨outcome, trace⟩
  by_cases winning : good outcome
  · obtain ⟨claim, fixed, breaks⟩ := winning
    subst outcome
    have sure :
      Pr{let result ← fixedOracleRun oracle (recordRows (replayOption spec.replay (some claim)) >>= fun next =>
        pure (next.1, trace ++ next.2))}[witness result.2] = 1 := by
      rw [fixed_oracle_run_bind]
      apply prEvent_eq_one_of_forall_mem_support
      intro result reached
      obtain ⟨next, called, same⟩ := (mem_support_bind_iff _ _ _).mp reached
      rw [fixed_oracle_run_pure] at same
      simp only [support_pure, Set.mem_singleton_iff] at same
      subst result
      exact preserves (fun _ present => List.mem_append_right trace present) (spec.extracts oracle claim breaks next called)
    have win : good (some claim) := ⟨claim, rfl, breaks⟩
    simp only [win, ite_true, sure, mul_one, start, limited]
    exact le_rfl
  · simp [winning]

theorem fixed_compression_leaf_bound {α : Type} (compress : Compression) (program : OracleComp World α)
    (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress, p⟩ (recordRows program))}[
      LeafWitness result.2] ≤ (q : ENNReal) / 2 ^ 122 := by
  simp only [fixed_run_eq_simulate]
  rw [(adaptive_cache_from_empty compress (recordRows program)).prEvent_eq (fun result => LeafWitness result.2),
    prEvent_map]
  refine (prEvent_mono_of_support _ _ _ (fun result reached hit => ?_)).trans
    (replayed_leaf_collision_le compress (recordRows program) q calls positive small withReplay bounded)
  exact leaf_witness_stored result.1.2 result.2
    (permutation_replay_stored compress program (PermutationCache.empty Block) result reached) hit

theorem fixed_permutation_projected_bound {α : Type} (p : Perm) (program : OracleComp World α)
    (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (do let compress ← $ᵗ Compression; fixedOracleRun ⟨compress, p⟩ (recordRows program))}[
      CompressionWitness result.2] ≤ 3 * (q : ENNReal) / (4 * 2 ^ 120) := by
  have equivalent := (EvalDistEq.of_evalDist_eq (compression_sampling_empty p (recordRows program))).prEvent_eq
    (fun result => CompressionWitness result.2)
  rw [← equivalent, prEvent_map]
  refine (prEvent_mono_of_support _ _ _ (fun result reached hit => ?_)).trans
    ((projected_collision_bound p (recordRows program) calls bounded).trans
      (projected_quarter_reserve q calls positive small withReplay))
  exact projected_witness_stored result.1.2 result.2 (compression_replay_stored p program ∅ result reached) hit

theorem event_budget_sum (q : Nat) :
    3 * (q : ENNReal) / (4 * 2 ^ 120) + (q : ENNReal) / 2 ^ 122 = (q : ENNReal) / 2 ^ 120 := by
  have same : (2 : ENNReal) ^ 122 = 4 * 2 ^ 120 := by
    rw [show (122 : Nat) = 2 + 120 by decide, pow_add]
    norm_num
  rw [same, ← ENNReal.add_div]
  have scaled : 3 * (q : ENNReal) + (q : ENNReal) = 4 * (q : ENNReal) := by ring
  rw [scaled, mul_comm 4 (q : ENNReal), mul_comm 4 ((2 : ENNReal) ^ 120)]
  exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)

theorem sampled_replay_bound {α : Type} (program : OracleComp World α)
    (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
      ReplayEvidence result.2] ≤ (q : ENNReal) / 2 ^ 120 := by
  unfold ReplayEvidence
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
      fixed_compression_leaf_bound compress program q calls positive small withReplay bounded

/-- The exact all-q binding clause follows from executable checker replay.
For smaller budgets the detector counts each replay query. Once q reaches
2^120 the requested upper bound is at least one. -/
theorem scheme_binding_of_replay_with (scheme : Scheme) {witness : List PublicRow → Prop}
    (spec : BindingReplayEvidence scheme witness)
    (preserves : ∀ {earlier later}, (∀ row ∈ earlier, row ∈ later) → witness earlier → witness later)
    (collisionBound : ∀ (program : OracleComp World Unit) (q calls : Nat),
      1 ≤ q → q ≤ 2 ^ 120 → calls ≤ q + 2 ^ 31 → PublicQueryBound (recordRows program) calls →
      Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
        witness result.2] ≤ (q : ENNReal) / 2 ^ 120) : scheme.Binding := by
  intro adversary budget positive
  by_cases large : 2 ^ BINDING_SECURITY_BITS ≤ budget
  · apply (prEvent_le_one _).trans
    apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by finiteness))).mpr
    simpa using (show ((2 ^ BINDING_SECURITY_BITS : Nat) : ENNReal) ≤ budget from Nat.cast_le.mpr large)
  · have small : budget ≤ 2 ^ 120 := by
      change ¬ 2 ^ 120 ≤ budget at large
      omega
    have reduced :
        Pr{let (oracle, claim, calls) ← Scheme.bindingGame adversary}[
          scheme.Breaks oracle claim ∧ calls ≤ budget] ≤
        Pr{let result ← (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (recordRows (boundedReplay spec.replay adversary budget)))}[
          witness result.2] := by
      simp only [Scheme.bindingGame, bind_pure_comp]
      rw [prEvent_bind_eq_tsum, prEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro oracle
      apply mul_le_mul_of_nonneg_left _ zero_le
      simp only [prEvent_map]
      exact replay_dominated scheme spec preserves oracle adversary budget
    exact reduced.trans (collisionBound (boundedReplay spec.replay adversary budget) budget (budget + 2 ^ 31)
      positive small le_rfl (bounded_replay_queries scheme spec adversary budget))

theorem scheme_binding_of_replay (scheme : Scheme) (spec : BindingReplayRefines scheme) : scheme.Binding :=
  scheme_binding_of_replay_with scheme spec (fun included evidence => evidence.mono included) sampled_replay_bound

end TwoPermutationPrototype.Sampling
