import CommitGolfCandidate.CompressionROM

/-! Birthday bound for collisions in the low 240 bits of compression replies.
The sampled oracle still returns the full 256 bits to every adversary. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec
set_option maxRecDepth 4096

abbrev ProjectedCompressionSpec := BitVec 512 →ₒ BitVec 240

def low240 (value : BitVec 256) : BitVec 240 := value.extractLsb' 0 240

def projectCache (cache : CompressionCache) : ProjectedCompressionSpec.QueryCache :=
  ⟨fun key => (cache key).map low240⟩

def ProjectedCollision (cache : CompressionCache) : Prop := CacheHasCollision (projectCache cache)

private theorem project_update (cache : CompressionCache) (key : BitVec 512) (value : BitVec 256) :
    projectCache (cache.cacheQuery key value) = (projectCache cache).cacheQuery key (low240 value) := by
  apply QueryCache.ext
  intro k
  by_cases same : k = key
  · subst k
    rw [QueryCache.cacheQuery_self]
    change Option.map low240 ((cache.cacheQuery key value) key) = some _
    rw [QueryCache.cacheQuery_self cache key value]
    rfl
  · rw [QueryCache.cacheQuery_of_ne (projectCache cache) (low240 value) same]
    exact congrArg (Option.map low240) (QueryCache.cacheQuery_of_ne cache value same)

private def joinDigest : BitVec 16 × BitVec 240 ≃ BitVec 256 where
  toFun := fun ⟨high, low⟩ => high ++ low
  invFun := fun value => (value.extractLsb' 240 16, low240 value)
  left_inv := by
    rintro ⟨high, low⟩
    exact Prod.ext (BitVec.extractLsb'_append_eq_left (a := high) (b := low))
      (BitVec.extractLsb'_append_eq_right (a := high) (b := low))
  right_inv := by
    intro value
    unfold low240
    exact BitVec.extractLsb'_append_extractLsb' (w := 16) (len := 240)

/-- Each fresh full-width answer contributes a collision probability of at
most one in 2^240 per previously queried input, even after its high bits
are disclosed. -/
theorem fresh_projected_collision_bound (cache : CompressionCache) (input : CompressionSpec.Domain)
    (keys : Finset CompressionSpec.Domain) (noCollision : ¬ ProjectedCollision cache)
    (covers : ∀ key, cache key ≠ none → key ∈ keys) :
    (prEvent ((fun answer => ProjectedCollision (cache.cacheQuery input answer)) <$>
      ($ᵗ CompressionSpec.Range input))) ≤ (keys.card : ENNReal) / 2 ^ 240 := by
  classical
  change Pr{let value ← $ᵗ BitVec 256}[ProjectedCollision (cache.cacheQuery input value)] ≤ _
  rw [← SampleableType.prEvent_uniformSample_equiv joinDigest]
  apply SampleableType.prEvent_uniformSample_prod_le_of_forall_fst
  intro high
  have projectedCovers : ∀ key, projectCache cache key ≠ none → key ∈ keys := by
    intro key populated
    apply covers
    intro missing
    exact populated (by change Option.map low240 (cache key) = none; rw [missing]; rfl)
  have count := card_responses_creating_cacheCollision_le (t := input)
    (cache₀ := projectCache cache) noCollision projectedCovers
  have charge (low : BitVec 240) :
      ProjectedCollision (cache.cacheQuery input (joinDigest (high, low))) =
        CacheHasCollision ((projectCache cache).cacheQuery input low) := by
    unfold ProjectedCollision
    apply congrArg CacheHasCollision
    refine (project_update cache input (joinDigest (high, low))).trans ?_
    have extract : low240 (joinDigest (high, low)) = low :=
      BitVec.extractLsb'_append_eq_right (a := high) (b := low)
    rw [extract]
  simp_rw [charge]
  rw [SampleableType.prEvent_uniformSample]
  have denom : Fintype.card (BitVec 240) = 2^240 := by simp
  rw [denom, Nat.cast_pow, Nat.cast_ofNat]
  apply ENNReal.div_le_div_right
  exact Nat.cast_le.mpr count

/-- Adaptive birthday induction with unrestricted private coins and access to both
permutation directions. `known` bounds the populated keys in the starting cache. -/
theorem projected_collision_bound_from_cache (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget known : Nat)
    (bounded : PublicQueryBound computation budget) (cache : CompressionCache)
    (noCollision : ¬ ProjectedCollision cache)
    (covered : ∃ keys : Finset CompressionSpec.Domain, keys.card ≤ known ∧
      ∀ key, cache key ≠ none → key ∈ keys) :
    (prEvent ((fun result => ProjectedCollision result.2) <$> (compressionRun permutation computation cache))) ≤
      ∑ step ∈ Finset.range budget, ((known + step : Nat) : ENNReal) / 2 ^ 240 := by
  classical
  induction computation using OracleComp.inductionOn generalizing budget known cache with
  | pure value =>
    rw [compression_run_pure]
    simp only [prEvent_pure, noCollision, ite_false]
    exact zero_le
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    rcases query with coins | publicQuery
    · rw [compression_run_private]
      apply prEvent_bind_le_of_forall_le_of_support
      intro answer _
      exact ih answer budget known (by simpa only [Oracle.callCost, Nat.sub_zero] using bounded.2 answer)
        cache noCollision covered
    · have positive : 1 ≤ budget := bounded.1
      have tails : ∀ answer, PublicQueryBound (next answer) (budget - 1) := bounded.2
      have smaller : (∑ step ∈ Finset.range (budget - 1), ((known + step : Nat) : ENNReal) / 2 ^ 240) ≤
          ∑ step ∈ Finset.range budget, ((known + step : Nat) : ENNReal) / 2 ^ 240 :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.sub_le budget 1))
      rcases publicQuery with input | permQuery
      · rw [compression_run_compress]
        cases cached : cache input with
        | some answer =>
          exact (ih answer (budget - 1) known (tails answer) cache noCollision covered).trans smaller
        | none =>
          have fresh : (prEvent ((fun answer => ProjectedCollision (cache.cacheQuery input answer)) <$> (($ᵗ CompressionSpec.Range input)))) ≤ (known : ENNReal) / 2 ^ 240 := by
            obtain ⟨keys, size, covers⟩ := covered
            exact (fresh_projected_collision_bound cache input keys noCollision covers).trans
              (ENNReal.div_le_div_right (Nat.cast_le.mpr size) _)
          have continuation : ∀ answer ∈ support ($ᵗ CompressionSpec.Range input),
              ¬ ProjectedCollision (cache.cacheQuery input answer) →
              (prEvent ((fun result => ProjectedCollision result.2) <$> (compressionRun permutation (next answer) (cache.cacheQuery input answer)))) ≤
                ∑ step ∈ Finset.range (budget - 1), ((known + 1 + step : Nat) : ENNReal) / 2 ^ 240 := by
            intro answer _ safe
            apply ih answer (budget - 1) (known + 1) (tails answer) _ safe
            obtain ⟨keys, size, covers⟩ := covered
            refine ⟨insert input keys, (Finset.card_insert_le _ _).trans (by omega), ?_⟩
            intro key populated
            by_cases same : key = input
            · exact same ▸ Finset.mem_insert_self _ _
            · rw [QueryCache.cacheQuery_of_ne _ _ same] at populated
              exact Finset.mem_insert_of_mem (covers key populated)
          have combined := (prEvent_bind_le_prEvent_add_of_support
            ($ᵗ CompressionSpec.Range input)
            (fun answer => compressionRun permutation (next answer) (cache.cacheQuery input answer))
            (fun answer => ProjectedCollision (cache.cacheQuery input answer))
            (fun result => ProjectedCollision result.2) continuation).trans
              (add_le_add fresh le_rfl)
          apply combined.trans_eq
          conv_rhs => rw [show budget = (budget - 1) + 1 from by omega]
          rw [Finset.sum_range_succ']
          simp only [Nat.add_zero]
          rw [add_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro step _
          rw [show known + 1 + step = known + (step + 1) from by omega]
      · rcases permQuery with input | input
        · rw [compression_run_permute]
          exact (ih _ (budget - 1) known (tails _) cache noCollision covered).trans smaller
        · rw [compression_run_inverse]
          exact (ih _ (budget - 1) known (tails _) cache noCollision covered).trans smaller

/-- Tight birthday bound for the compression cache, even when the adversary also
uses fresh private coins and the fixed ideal permutation in both directions. -/
theorem projected_collision_bound (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget : Nat) (bounded : PublicQueryBound computation budget) :
    (prEvent ((fun result => ProjectedCollision result.2) <$> (compressionRun permutation computation ∅))) ≤
      ((budget * (budget - 1) : Nat) : ENNReal) / (2 * 2 ^ 240) := by
  have estimate := projected_collision_bound_from_cache permutation computation budget 0 bounded ∅
    (by rintro ⟨_, _, _, _, _, impossible, _⟩; change none = some _ at impossible; cases impossible)
    ⟨∅, by simp, fun key populated => (populated rfl).elim⟩
  simp only [Nat.zero_add, div_eq_mul_inv] at estimate
  exact estimate.trans_eq (ENNReal.gauss_sum_inv_eq budget ((2 : ENNReal) ^ 240))


/-- The full cap detector replays both adversarial openings, including its
reply-recording probes. The factor of two in the exact birthday denominator
is needed at this digest width for the largest nontrivial budgets. -/
theorem projected_cap_birthday_arithmetic (q : Nat) (positive : 1 ≤ q) (small : q ≤ 2^120) :
    (q + 1610613756) * (q + 1610613756 - 1) ≤ 2 * q * 2^120 := by
  have quadratic := Nat.mul_le_mul_left q small
  have floor := Nat.mul_le_mul_right (1610613756^2) positive
  have linear := Nat.mul_le_mul_left q (by decide : 1610613756^2 + 2*1610613756 ≤ 2^120)
  apply (Nat.mul_le_mul_left _ (Nat.sub_le _ 1)).trans
  nlinarith

theorem projected_cap_birthday_target (q : Nat) (positive : 1 ≤ q) (small : q ≤ 2^120) :
    (((q + 1610613756) * (q + 1610613756 - 1) : Nat) : ENNReal) / (2 * 2 ^ 240) ≤
      (q : ENNReal) / 2 ^ 120 := by
  calc
    _ ≤ ((2 * q * 2^120 : Nat) : ENNReal) / (2 * 2 ^ 240) :=
      ENNReal.div_le_div_right (Nat.cast_le.mpr (projected_cap_birthday_arithmetic q positive small)) _
    _ = _ := by
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [show (2 : ENNReal) * 2^240 = 2^120 * (2 * 2^120) by ring]
      rw [show 2 * (q : ENNReal) * 2^120 = q * (2 * 2^120) by ring]
      exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)

/-- Up to 2^31 paid checks and probes leave a quarter of the binding
target for an independent bad event, such as a permutation collision. -/
theorem projected_quarter_reserve_arithmetic (q m : Nat) (positive : 1 ≤ q)
    (small : q ≤ 2^120) (overhead : m ≤ q + 2^31) :
    2 * (m * (m - 1)) ≤ 3 * q * 2^120 := by
  have quadratic := Nat.mul_le_mul_left q small
  have floor := Nat.mul_le_mul_right (2^31 * 2^31) positive
  have reserve := Nat.mul_le_mul_left q (by decide : 2 * (2^31 * 2^31 + 2*2^31) ≤ 2^120)
  have bound := Nat.mul_le_mul overhead ((Nat.sub_le m 1).trans overhead)
  nlinarith

theorem projected_quarter_reserve (q m : Nat) (positive : 1 ≤ q)
    (small : q ≤ 2^120) (overhead : m ≤ q + 2^31) :
    ((m * (m - 1) : Nat) : ENNReal) / (2 * 2^240) ≤
      (3 * (q : ENNReal)) / (4 * 2^120) := by
  have base : 2 * ((m * (m-1) : Nat) : ENNReal) ≤ 3 * (q : ENNReal) * 2^120 := by
    exact_mod_cast projected_quarter_reserve_arithmetic q m positive small overhead
  calc
    _ = (2 * ((m * (m-1) : Nat) : ENNReal)) / ((2 * 2^240) * 2) := by
      rw [mul_comm 2 (((m * (m-1) : Nat) : ENNReal))]
      exact (ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)).symm
    _ ≤ (3 * (q : ENNReal) * 2^120) / ((2 * 2^240) * 2) := ENNReal.div_le_div_right base _
    _ = _ := by
      rw [show ((2 : ENNReal) * 2^240) * 2 = (4 * 2^120) * 2^120 by ring]
      exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)

/-- One full-width leaf sibling, fifteen internal siblings, and a cap frontier. -/
theorem projected_batch_bytes (boundary : Nat) (bound : boundary ≤ 128) :
    128 * (24 + 32 + 15 * 30) + boundary * 30 ≤ 68608 := by omega

end CommitGolfCandidate
