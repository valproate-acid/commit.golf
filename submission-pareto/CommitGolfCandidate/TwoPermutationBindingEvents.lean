import CommitGolfCandidate.TwoPermutationProjectionEvent

/-! A conservative search for all permutation binding failures. We compare with
every earlier row, which avoids conditioning a fresh reply on its query origin. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp MeasureTheory
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

abbrev Row := Block × Block

def outputDigest (output : Block) : BitVec 256 := output.extractLsb' 0 256
def outputSuffix (output : Block) : BitVec 768 := output.extractLsb' 832 768
def inputMiddle (input : Block) : BitVec 768 := input.extractLsb' 64 768

def forwardProjection (rows : List Row) (output : Block) : Prop :=
  (∃ row ∈ rows, outputDigest output = outputDigest row.2) ∨
  (∃ row ∈ rows, outputSuffix output = outputSuffix row.2) ∨
  (∃ row ∈ rows, outputSuffix output = inputMiddle row.1)

def inverseJoin (rows : List Row) (input : Block) : Prop :=
  ∃ row ∈ rows, inputMiddle input = outputSuffix row.2

def newForwardProjection (cache : Cache) (result : Block × Cache) : Prop :=
  cache.entries.length < result.2.entries.length ∧ forwardProjection cache.entries result.1

def newInverseJoin (cache : Cache) (result : Block × Cache) : Prop :=
  cache.entries.length < result.2.entries.length ∧ inverseJoin cache.entries result.1

def newInverseProjection (cache : Cache) (result : Block × Cache) : Prop :=
  newInverseFirst cache result ∨ newInverseJoin cache result

noncomputable def permutationRate (rows : Nat) : ENNReal :=
  ((rows : ENNReal) / 2 ^ 255 + (rows : ENNReal) / 2 ^ 767 + (rows : ENNReal) / 2 ^ 767) + 1 / 2 ^ 167

theorem prEvent_list_le {ι α : Type} (rows : List ι) (sample : ProbComp α)
    (event : ι → α → Prop) (cost : ENNReal)
    (each : ∀ row ∈ rows, Pr{let x ← sample}[event row x] ≤ cost) :
    Pr{let x ← sample}[∃ row ∈ rows, event row x] ≤ (rows.length : ENNReal) * cost := by
  classical
  let indices := rows.toFinset
  calc
    _ = Pr{let x ← sample}[∃ row ∈ indices, event row x] := by simp [indices]
    _ ≤ ∑ row ∈ indices, Pr{let x ← sample}[event row x] := prEvent_exists_finset_le _ _ _
    _ ≤ ∑ _row ∈ indices, cost := by
      apply Finset.sum_le_sum
      intro row present
      exact each row (by simpa [indices] using present)
    _ = (indices.card : ENNReal) * cost := by simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast List.toFinset_card_le rows) zero_le

theorem forward_projection_step_le (cache : Cache) (input : Block)
    (room : cache.entries.length ≤ 2 ^ 121) :
    Pr{let result ← cache.forward input}[newForwardProjection cache result] ≤ permutationRate cache.entries.length := by
  classical
  unfold PermutationCache.forward
  split
  · rename_i fresh
    simp only [bind_pure_comp, prEvent_map, newForwardProjection, PermutationCache.extendForward,
      List.length_cons, Nat.lt_succ_self, true_and]
    let sample : ProbComp (RemainingOutputs cache.entries) := @uniformSample _ (cache.forwardSampler input fresh)
    let hitsDigest (answer : RemainingOutputs cache.entries) :=
      ∃ row ∈ cache.entries, outputDigest answer.val = outputDigest row.2
    let hitsSuffix (answer : RemainingOutputs cache.entries) :=
      ∃ row ∈ cache.entries, outputSuffix answer.val = outputSuffix row.2
    let hitsMiddle (answer : RemainingOutputs cache.entries) :=
      ∃ row ∈ cache.entries, outputSuffix answer.val = inputMiddle row.1
    have digestBound : Pr{let answer ← sample}[hitsDigest answer] ≤ (cache.entries.length : ENNReal) / 2 ^ 255 := by
      simpa only [hitsDigest, mul_one_div] using
        prEvent_list_le cache.entries sample (fun row answer => outputDigest answer.val = outputDigest row.2)
          (1 / 2 ^ 255) (fun row _ => fresh_forward_slice_le cache input fresh (low := 0) (width := 256)
            (high := 1344) (by decide) (by decide) room (outputDigest row.2))
    have suffixBound : Pr{let answer ← sample}[hitsSuffix answer] ≤ (cache.entries.length : ENNReal) / 2 ^ 767 := by
      simpa only [hitsSuffix, mul_one_div] using
        prEvent_list_le cache.entries sample (fun row answer => outputSuffix answer.val = outputSuffix row.2)
          (1 / 2 ^ 767) (fun row _ => fresh_forward_slice_le cache input fresh (low := 832) (width := 768)
            (high := 0) (by decide) (by decide) room (outputSuffix row.2))
    have middleBound : Pr{let answer ← sample}[hitsMiddle answer] ≤ (cache.entries.length : ENNReal) / 2 ^ 767 := by
      simpa only [hitsMiddle, mul_one_div] using
        prEvent_list_le cache.entries sample (fun row answer => outputSuffix answer.val = inputMiddle row.1)
          (1 / 2 ^ 767) (fun row _ => fresh_forward_slice_le cache input fresh (low := 832) (width := 768)
            (high := 0) (by decide) (by decide) room (inputMiddle row.1))
    have pair := (prEvent_or_le sample hitsSuffix hitsMiddle).trans (add_le_add suffixBound middleBound)
    change Pr{let answer ← sample}[hitsDigest answer ∨ hitsSuffix answer ∨ hitsMiddle answer] ≤ _
    exact (prEvent_or_le sample hitsDigest (fun answer => hitsSuffix answer ∨ hitsMiddle answer)).trans
      ((add_le_add digestBound pair).trans (by
        rw [← add_assoc]
        exact le_add_of_nonneg_right zero_le))
  · simp [newForwardProjection]

theorem inverse_join_step_le (cache : Cache) (output : Block)
    (room : cache.entries.length ≤ 2 ^ 121) :
    Pr{let result ← cache.inverse output}[newInverseJoin cache result] ≤ (cache.entries.length : ENNReal) / 2 ^ 767 := by
  classical
  unfold PermutationCache.inverse
  split
  · rename_i fresh
    simp only [bind_pure_comp, prEvent_map, newInverseJoin, PermutationCache.extendInverse,
      List.length_cons, Nat.lt_succ_self, true_and]
    let sample : ProbComp (RemainingInputs cache.entries) := @uniformSample _ (cache.inverseSampler output fresh)
    simpa only [inverseJoin, mul_one_div] using
      prEvent_list_le cache.entries sample (fun row answer => inputMiddle answer.val = outputSuffix row.2)
        (1 / 2 ^ 767) (fun row _ => fresh_inverse_slice_le cache output fresh (low := 64) (width := 768)
          (high := 768) (by decide) (by decide) room (outputSuffix row.2))
  · simp [newInverseJoin]

theorem inverse_projection_step_le (cache : Cache) (output : Block)
    (room : cache.entries.length ≤ 2 ^ 121) :
    Pr{let result ← cache.inverse output}[newInverseProjection cache result] ≤ permutationRate cache.entries.length := by
  unfold newInverseProjection
  refine (prEvent_or_le (cache.inverse output) _ _).trans ((add_le_add (inverse_step_first_domain_le cache output room)
    (inverse_join_step_le cache output room)).trans ?_)
  unfold permutationRate
  rw [add_comm ((1 : ENNReal) / 2 ^ 167)]
  apply add_le_add_left
  exact (le_add_of_nonneg_left zero_le).trans (le_add_of_nonneg_right zero_le)

theorem permutation_rate_mono {left right : Nat} (le : left ≤ right) : permutationRate left ≤ permutationRate right := by
  unfold permutationRate
  have w255 : (left : ENNReal) / 2 ^ 255 ≤ (right : ENNReal) / 2 ^ 255 :=
    ENNReal.div_le_div (by exact_mod_cast le) le_rfl
  have w767 : (left : ENNReal) / 2 ^ 767 ≤ (right : ENNReal) / 2 ^ 767 :=
    ENNReal.div_le_div (by exact_mod_cast le) le_rfl
  exact add_le_add (add_le_add (add_le_add w255 w767) w767) le_rfl

noncomputable def scanPermutation {α : Type} (compress : Compression) (program : OracleComp World α) :
    Cache → ProbComp Bool := by
  classical
  exact OracleComp.recOn program
    (fun _ _ => pure false)
    (fun query _ next cache => match query with
      | .inl coins => (liftM (unifSpec.query coins) : ProbComp _) >>= fun answer => next answer cache
      | .inr (.inl input) => next (compress input) cache
      | .inr (.inr (.inl input)) => cache.forward input >>= fun result =>
          if newForwardProjection cache result then pure true else next result.1 result.2
      | .inr (.inr (.inr input)) => cache.inverse input >>= fun result =>
          if newInverseProjection cache result then pure true else next result.1 result.2)

private theorem step_union_bound (sample : ProbComp (Block × Cache))
    (isBad : Block × Cache → Prop) [DecidablePred isBad] (resume : Block × Cache → ProbComp Bool) (budget : Nat)
    (positive : 1 ≤ budget) (rate : ENNReal)
    (step : Pr{let result ← sample}[isBad result] ≤ rate)
    (tail : ∀ result ∈ support sample, ¬ isBad result → Pr{let found ← resume result}[found = true] ≤
      ((budget - 1 : Nat) : ENNReal) * rate) :
    Pr{let found ← (sample >>= fun result => if isBad result then pure true else resume result)}[found = true] ≤
      (budget : ENNReal) * rate := by
  classical
  let guarded (result : Block × Cache) := if isBad result then pure true else resume result
  have safeTail (result : Block × Cache) (reached : result ∈ support sample) (safe : ¬ isBad result) :
      Pr{let found ← guarded result}[found = true] ≤ ((budget - 1 : Nat) : ENNReal) * rate := by
    simpa only [guarded, safe, ↓reduceIte] using tail result reached safe
  have union := prEvent_bind_le_prEvent_add_of_support sample guarded isBad (fun found => found = true) safeTail
  refine union.trans ((add_le_add step le_rfl).trans_eq ?_)
  calc
    _ = (1 + ((budget - 1 : Nat) : ENNReal)) * rate := by rw [add_mul, one_mul]
    _ = _ := by
      congr 1
      exact_mod_cast (show 1 + (budget - 1) = budget by omega)

/-- All three projected collision and join checks, together with the inverse
first-domain check, are bounded starting from any consistent shared history. -/
theorem scan_permutation_probability {α : Type} (compress : Compression) (program : OracleComp World α)
    (cache : Cache) (budget maximum : Nat) (bounded : QueryBounded program budget)
    (room : cache.entries.length + budget ≤ maximum) (maximumBound : maximum ≤ 2 ^ 121) :
    Pr{let found ← scanPermutation compress program cache}[found = true] ≤
      (budget : ENNReal) * permutationRate maximum := by
  classical
  induction program using OracleComp.inductionOn generalizing cache budget with
  | pure value =>
    change Pr{let found ← (pure false : ProbComp Bool)}[found = true] ≤ _
    simp
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, QueryBounded (next answer) (budget - Oracle.callCost query)) at bounded
    rcases query with coins | publicQuery
    · change Pr{let found ← ((liftM (unifSpec.query coins) : ProbComp _) >>= fun answer =>
        scanPermutation compress (next answer) cache)}[found = true] ≤ _
      exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun answer _ =>
        ih answer cache budget (by simpa only [Oracle.callCost, Nat.sub_zero] using bounded.2 answer) room
    · have positive : 1 ≤ budget := bounded.1
      have tailBound (answer : World.Range (.inr publicQuery)) := bounded.2 answer
      have roomNow : cache.entries.length ≤ 2 ^ 121 := by omega
      have rateNow : permutationRate cache.entries.length ≤ permutationRate maximum :=
        permutation_rate_mono (by omega)
      rcases publicQuery with input | permQuery
      · change Pr{let found ← scanPermutation compress (next (compress input)) cache}[found = true] ≤ _
        have tail := ih (compress input) cache (budget - 1) (tailBound (compress input)) (by omega)
        exact tail.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le budget 1) zero_le)
      · rcases permQuery with input | input
        · change Pr{let found ← (cache.forward input >>= fun result =>
            if newForwardProjection cache result then pure true
            else scanPermutation compress (next result.1) result.2)}[found = true] ≤ _
          apply step_union_bound _ _ _ budget positive (permutationRate maximum)
            ((forward_projection_step_le cache input roomNow).trans rateNow)
          intro result reached _
          have growth := forward_cache_growth cache input result reached
          exact ih result.1 result.2 (budget - 1) (tailBound result.1) (by omega)
        · change Pr{let found ← (cache.inverse input >>= fun result =>
            if newInverseProjection cache result then pure true
            else scanPermutation compress (next result.1) result.2)}[found = true] ≤ _
          apply step_union_bound _ _ _ budget positive (permutationRate maximum)
            ((inverse_projection_step_le cache input roomNow).trans rateNow)
          intro result reached _
          have growth := inverse_cache_growth cache input result reached
          exact ih result.1 result.2 (budget - 1) (tailBound result.1) (by omega)

private theorem rescale_power_divisor (value : ENNReal) (base offset : Nat) :
    value / 2 ^ base = (value * 2 ^ offset) / 2 ^ (base + offset) := by
  rw [pow_add]
  exact (ENNReal.mul_div_mul_right (c := (2 : ENNReal) ^ offset) _ _ (by positivity) (by finiteness)).symm

theorem all_permutation_replay_margin {q calls : Nat} (positive : 1 ≤ q) (small : q ≤ 2 ^ 120)
    (withReplay : calls ≤ q + 2 ^ 31) :
    (calls : ENNReal) * permutationRate calls ≤ (q : ENNReal) / 2 ^ 122 := by
  obtain ⟨linear, square, _⟩ := replay_budget_arithmetic positive small withReplay
  have numerator : calls * calls * 2 ^ 513 + calls * calls * 2 + calls * calls * 2 +
      calls * 2 ^ 601 ≤ q * 2 ^ 646 := by omega
  calc
    _ = (((calls : ENNReal) * calls) / 2 ^ 255 + ((calls : ENNReal) * calls) / 2 ^ 767 +
         ((calls : ENNReal) * calls) / 2 ^ 767) + (calls : ENNReal) / 2 ^ 167 := by
      simp [permutationRate, mul_add, div_eq_mul_inv, mul_assoc]
    _ = ((calls : ENNReal) * calls * 2 ^ 513 + (calls : ENNReal) * calls * 2 +
          (calls : ENNReal) * calls * 2 + (calls : ENNReal) * 2 ^ 601) / 2 ^ 768 := by
      rw [rescale_power_divisor _ 255 513, rescale_power_divisor _ 767 1,
        rescale_power_divisor _ 167 601, ← ENNReal.add_div, ← ENNReal.add_div, ← ENNReal.add_div]
      simp
    _ ≤ ((q : ENNReal) * 2 ^ 646) / 2 ^ 768 := ENNReal.div_le_div (by exact_mod_cast numerator) le_rfl
    _ = _ := (rescale_power_divisor (q : ENNReal) 122 646).symm

theorem scan_permutation_with_replay {α : Type} (compress : Compression) (program : OracleComp World α)
    (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31)
    (bounded : QueryBounded program calls) :
    Pr{let found ← scanPermutation compress program (PermutationCache.empty Block)}[found = true] ≤
      (q : ENNReal) / 2 ^ 122 := by
  have maximum := (replay_budget_arithmetic positive small withReplay).2.2
  exact (scan_permutation_probability compress program (PermutationCache.empty Block) calls calls bounded
      (by simp [PermutationCache.empty]) maximum).trans
    (all_permutation_replay_margin positive small withReplay)

end TwoPermutationPrototype.Sampling
