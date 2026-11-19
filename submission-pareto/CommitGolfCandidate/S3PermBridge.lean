import CommitGolfCandidate.S3PermStrat
import CommitGolfCandidate.S3PermEager

/-! The contract's experiment with a uniformly sampled permutation and one fixed compression
function has exactly the event probabilities of the lazy `Strat` model. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec
open CommitGolfCandidate.Permutation

theorem ofReal_ind (p : Prop) [Decidable p] : ENNReal.ofReal (ind p) = if p then 1 else 0 := by
  by_cases h : p
  · rw [ind_pos h, if_pos h, ENNReal.ofReal_one]
  · rw [ind_neg h, if_neg h, ENNReal.ofReal_zero]

/-- A uniform finite average of real numbers, as a weighted sum of extended reals. -/
theorem sum_inv_card_mul_ofReal {ι : Type} [Fintype ι] [Nonempty ι] (g : ι → ℝ)
    (nonneg : ∀ i, 0 ≤ g i) :
    ∑ i, (Fintype.card ι : ENNReal)⁻¹ * ENNReal.ofReal (g i) =
      ENNReal.ofReal (avg Finset.univ g) := by
  have positive : (0 : ℝ) < (Finset.univ : Finset ι).card := by
    exact_mod_cast Finset.card_pos.2 Finset.univ_nonempty
  unfold avg
  rw [ENNReal.ofReal_div_of_pos positive, ENNReal.ofReal_sum_of_nonneg fun i _ => nonneg i,
    ENNReal.ofReal_natCast, ← Finset.mul_sum, Finset.card_univ, div_eq_mul_inv, mul_comm]

/-- For one fixed oracle pair, the run is the eager run of its strategy. -/
theorem fixed_run_prob (compression : Compression) (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (event : α → Prop) (state : PState PermState) :
    prEvent (event <$> fixedOracleRun ⟨compression, permutation⟩ computation) =
      ENNReal.ofReal ((toStrat compression computation).eager permutation state
        fun value _ => ind (event value)) := by
  classical
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
    rw [fixed_oracle_run_pure, to_strat_pure]
    simp only [Strat.eager]
    rw [prEvent_pure, ofReal_ind]
  | query_bind query next ih =>
    rcases query with coins | input | input | input
    · rw [fixed_oracle_run_private, to_strat_coins]
      simp only [Strat.eager]
      rw [prEvent_bind_eq_sum_fintype]
      have mass : ∀ answer : Fin (coins + 1),
          prEvent ((fun drawn => drawn = answer) <$>
            (liftM (unifSpec.query coins) : ProbComp (Fin (coins + 1)))) =
            (Fintype.card (Fin (coins + 1)) : ENNReal)⁻¹ := by
        intro answer
        have counted := prEvent_liftM_query_eq_card_div (spec := unifSpec) coins
          (fun drawn : Fin (coins + 1) => drawn = answer)
        refine counted.trans ?_
        simp [Finset.filter_eq']
      rw [← sum_inv_card_mul_ofReal _ fun answer =>
        Strat.eager_nonneg permutation (fun _ _ => ind_nonneg _) _ _]
      refine Finset.sum_congr rfl fun answer _ => ?_
      rw [mass answer, ih answer state]
    · rw [fixed_oracle_run_public, to_strat_compress]
      exact ih _ state
    · rw [fixed_oracle_run_public, to_strat_permute]
      simp only [Strat.eager]
      exact ih _ _
    · rw [fixed_oracle_run_public, to_strat_inverse]
      simp only [Strat.eager]
      exact ih _ _

/-- **Eager uniform permutation = lazy table**, for every fixed compression function. -/
theorem perm_sampling_prob (compression : Compression) {α : Type}
    (computation : OracleComp World α) (event : α → Prop) :
    prEvent (event <$> (($ᵗ Perm) >>= fun permutation =>
        fixedOracleRun ⟨compression, permutation⟩ computation)) =
      ENNReal.ofReal ((toStrat compression computation).prob PState.init
        fun value _ => event value) := by
  classical
  rw [prEvent_bind_eq_sum_fintype]
  unfold Strat.prob
  rw [← Strat.avg_eager, ← sum_inv_card_mul_ofReal _ fun permutation =>
    Strat.eager_nonneg permutation (fun _ _ => ind_nonneg _) _ _]
  refine Finset.sum_congr rfl fun permutation _ => ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton,
    fixed_run_prob compression permutation computation event PState.init]

end CommitGolfCandidate
