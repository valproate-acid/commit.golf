import CommitGolfCandidate.TwoPermutationHidingMargin

namespace TwoPermutationPrototype.Sampling

set_option exponentiation.threshold 2048
set_option maxRecDepth 4096

/-- This many disclosed rows suffice for the finite, without-replacement step. -/
theorem tagless_opened_history_room (t count : Nat)
    (nontrivial : t + 1 ≤ 2^120) (opened : count ≤ 2^24) :
    t+2*count ≤ 2^121 := by omega

noncomputable def taglessOpenedGuard (t : Nat) : ℝ :=
  (t : ℝ)/2^128 + 2^24/2^167

noncomputable def taglessProposalError (t : Nat) : ℝ :=
  (t : ℝ)/2^128 + 2^24/2^168 +
    2^24*((t : ℝ)+2^25)/2^832 +
    2^25*((t : ℝ)+2^25)/2^1600

noncomputable def taglessObserverRate : ℝ :=
  1/2^128 + 2^24*(1/2^832 + 1/2^1600 + 1/2^1344)

theorem tagless_observer_rate_le : taglessObserverRate ≤ (1 : ℝ)/2^127 := by
  norm_num [taglessObserverRate]

/-- One common opened guard and two independent proposal and observer hops fit
with 32-fold slack. This also covers a zero-query observer. -/
theorem tagless_hiding_margin (t : Nat) :
    taglessOpenedGuard t + 2*taglessProposalError t + 2*(t : ℝ)*taglessObserverRate ≤
      ((t : ℝ)+1)/2^125 := by
  have nonneg : 0 ≤ (t : ℝ) := by positivity
  apply le_trans (add_le_add (le_refl (taglessOpenedGuard t + 2*taglessProposalError t))
    (mul_le_mul_of_nonneg_left tagless_observer_rate_le (by positivity : 0 ≤ 2*(t : ℝ))))
  unfold taglessOpenedGuard taglessProposalError
  norm_num
  linarith

theorem tagless_challenge_error (t : Nat) :
    min 1 (taglessOpenedGuard t + 2*taglessProposalError t + 2*(t : ℝ)*taglessObserverRate) ≤
      min 1 (((t : ℝ)+1)/2^120) := by
  apply min_le_min le_rfl
  apply (tagless_hiding_margin t).trans
  have et : 0 ≤ (t : ℝ) := by positivity
  norm_num
  linarith

end TwoPermutationPrototype.Sampling
