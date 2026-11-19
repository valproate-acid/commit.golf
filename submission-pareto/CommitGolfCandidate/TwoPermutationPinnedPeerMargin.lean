import Mathlib.Tactic

/-! The exact pinned-leaf event bound has room for the paid checker replay. -/
namespace TwoPermutationPrototype.Sampling

set_option exponentiation.threshold 2048
set_option maxHeartbeats 1000000

theorem pinned_peer_collision_margin (q queries : ℕ) (positive : 1 ≤ q)
    (small : q ≤ 2^120) (count : queries ≤ q + 2^31 + 4) :
    (((queries : ℝ) * ((queries : ℝ)-1)/2) * (2^1345 + 2^897) + (queries : ℝ)*2^896) /
      (2^1600 - (queries : ℝ)) ≤ (q : ℝ)/2^122 := by
  have qOne : (1 : ℝ) ≤ q := by exact_mod_cast positive
  have qUpper : (q : ℝ) ≤ 2^120 := by exact_mod_cast small
  have qNonneg : (0 : ℝ) ≤ q := by positivity
  have nonneg : (0 : ℝ) ≤ queries := by positivity
  have terms : (queries : ℝ) ≤ (q : ℝ) + 2^31 + 4 := by exact_mod_cast count
  have queriesUpper : (queries : ℝ) ≤ 2^121 := by
    have threshold : (2 : ℝ)^120 + 2^31 + 4 ≤ 2^121 := by norm_num
    linarith
  have denominator : (2 : ℝ)^1599 ≤ 2^1600-(queries : ℝ) := by
    have threshold : (2 : ℝ)^1599 + 2^121 ≤ 2^1600 := by norm_num
    linarith
  have denominatorPos : (0 : ℝ) < 2^1600-(queries : ℝ) :=
    lt_of_lt_of_le (by positivity : (0 : ℝ)<2^1599) denominator
  have squareBound : (queries : ℝ)^2 ≤ (q : ℝ)*2^122 := by
    let extra : ℝ := 2^31+4
    have leSum : (queries : ℝ) ≤ q + extra := by linarith [show extra = (2:ℝ)^31+4 from rfl]
    have sq := mul_nonneg (sub_nonneg.mpr leSum) (by positivity : 0 ≤ (q : ℝ) + extra + queries)
    have qsq := mul_le_mul_of_nonneg_right qUpper qNonneg
    have esq : 2*extra^2 ≤ 2^65 := by norm_num [extra]
    have nq := mul_le_mul_of_nonneg_right qOne (by positivity : (0 : ℝ) ≤ 2^65)
    have slack : (2 : ℝ)^121 + 2^65 ≤ 2^122 := by norm_num
    have pad := mul_le_mul_of_nonneg_right slack qNonneg
    nlinarith [sq_nonneg ((q : ℝ) - extra)]
  have linearBound : (queries : ℝ) ≤ (q : ℝ)*2^33 := by
    have extra : (2 : ℝ)^31 + 4 ≤ 2^32 := by norm_num
    have some := mul_le_mul_of_nonneg_right qOne (by positivity : (0 : ℝ) ≤ 2^32)
    have slack : (1 : ℝ)+2^32 ≤ 2^33 := by norm_num
    have pad := mul_le_mul_of_nonneg_right slack qNonneg
    nlinarith
  have pairs : ((queries : ℝ) * ((queries : ℝ)-1)/2) * (2^1345 + 2^897) ≤
      (queries : ℝ)^2 * 2^1345 := by
    have scale : (2 : ℝ)^1345 + 2^897 ≤ 2*2^1345 := by norm_num
    by_cases under : (queries : ℝ) < 1
    · have low : queries < 1 := by exact_mod_cast under
      have zero : queries=0 := by omega
      simp [zero]
    · have nonnegPair : 0 ≤ (queries : ℝ) * ((queries : ℝ)-1)/2 :=
        div_nonneg (mul_nonneg nonneg (sub_nonneg.mpr (le_of_not_gt under))) (by norm_num)
      have changed := mul_le_mul_of_nonneg_left scale nonnegPair
      have factor : (queries : ℝ) * ((queries : ℝ)-1) ≤ (queries : ℝ)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right factor (by positivity : (0 : ℝ)≤2^1345)]
  have pairBound := mul_le_mul_of_nonneg_right squareBound (by positivity : (0 : ℝ) ≤ 2^1345)
  have tailBound := mul_le_mul_of_nonneg_right linearBound (by positivity : (0 : ℝ) ≤ 2^896)
  have lower := mul_le_mul_of_nonneg_left denominator (by positivity : (0 : ℝ)≤(q : ℝ)/2^122)
  have unified : (2 : ℝ)^122*2^1345 + 2^33*2^896 ≤ 2^1599/2^122 := by norm_num
  have factor := mul_le_mul_of_nonneg_left unified qNonneg
  apply (div_le_iff₀ denominatorPos).2
  nlinarith

end TwoPermutationPrototype.Sampling
