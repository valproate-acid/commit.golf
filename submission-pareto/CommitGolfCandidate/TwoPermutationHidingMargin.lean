import CommitGolfCandidate.TwoPermutationHidingObserver
import CommitGolfCandidate.TwoPermutationHidingResample

/-! Numerical allowance for two reference hops before and after the challenge,
including a conservative allowance for output collisions in both worlds. -/
namespace TwoPermutationPrototype.Sampling
set_option exponentiation.threshold 2048

theorem hidden_pair_rate_real_le : hiddenPairRate.toReal ≤ (1 : ℝ) / 2 ^ 127 := by
  unfold hiddenPairRate
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_pow]

/-- Four times the per-pair charge allows each of the two worlds to charge up to
the full budget separately before and after the challenge. The programming
allowance covers up to twice the vector length in either world. -/
theorem two_message_margin (budget : Nat) :
    4 * (budget : ℝ) * hiddenPairRate.toReal +
        4 * 2 ^ 24 * ((budget : ℝ) + 2 ^ 25) / 2 ^ 1600 ≤
      ((budget : ℝ) + 1) / 2 ^ 120 := by
  have nonnegative : 0 ≤ (budget : ℝ) := by positivity
  apply le_trans (add_le_add_left (mul_le_mul_of_nonneg_left hidden_pair_rate_real_le (by positivity)) _)
  norm_num
  linarith


open OracleComp

local instance marginDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

/-- Two worlds with a common reference transcript meet the challenge error once
the proposed-row conflicts and the observer hits have been bounded. -/
theorem two_message_via_reference {α : Type} (budget : Nat)
    (real₀ programmed₀ reference programmed₁ real₁ : ProbComp α)
    (first₀ : measureTVDist real₀ programmed₀ ≤
      (budget : ℝ) * hiddenPairRate.toReal + 2 ^ 25 * ((budget : ℝ) + 2 ^ 25) / 2 ^ 1600)
    (first₁ : measureTVDist real₁ programmed₁ ≤
      (budget : ℝ) * hiddenPairRate.toReal + 2 ^ 25 * ((budget : ℝ) + 2 ^ 25) / 2 ^ 1600)
    (observe₀ : measureTVDist reference programmed₀ ≤ (budget : ℝ) * hiddenPairRate.toReal)
    (observe₁ : measureTVDist reference programmed₁ ≤ (budget : ℝ) * hiddenPairRate.toReal) :
    measureTVDist real₀ real₁ ≤ min 1 (((budget : ℝ) + 1) / 2 ^ 120) := by
  refine le_min (measureTVDist_le_one _ _) ?_
  have fromFirst := measureTVDist_triangle real₀ programmed₀ reference
  rw [measureTVDist_comm programmed₀ reference] at fromFirst
  have fromSecond := measureTVDist_triangle reference programmed₁ real₁
  rw [measureTVDist_comm programmed₁ real₁] at fromSecond
  have total := measureTVDist_triangle real₀ reference real₁
  calc
    _ ≤ 4 * (budget : ℝ) * hiddenPairRate.toReal +
          4 * 2 ^ 24 * ((budget : ℝ) + 2 ^ 25) / 2 ^ 1600 := by
      norm_num at first₀ first₁ ⊢
      linarith
    _ ≤ _ := two_message_margin budget

end TwoPermutationPrototype.Sampling
