import CommitGolfCandidate.TaggedPinnedTailCoupling

namespace TwoPermutationPrototype.Sampling
open CommitGolf
set_option exponentiation.threshold 2048
set_option maxRecDepth 8192

theorem pinned_final_hiding_margin (budget : Nat) :
    2 * ((3 * LENGTH : ℝ) * (((budget : ℝ) + 3 * LENGTH) / 2^1343)) +
      2 * ((budget : ℝ)/2^128 + (budget : ℝ)*(2/2^128 + 2^25/2^1344)) ≤
      ((budget : ℝ) + 1) / 2^120 := by
  have nonneg : 0 ≤ (budget : ℝ) := Nat.cast_nonneg _
  have compares : (LENGTH : ℝ) = 2 ^ 24 := by norm_num [LENGTH, LOG_LENGTH]
  rw [compares]
  norm_num
  linarith

theorem pinned_hiding_room (budget : Nat) (small : budget + 1 ≤ 2^120) :
    budget + 3 * LENGTH ≤ 2^121 := by
  change budget + 3 * 2^24 ≤ 2^121
  omega

end TwoPermutationPrototype.Sampling
