import CommitGolfCandidate.NonceChainLayout
import CommitGolfCandidate.S3PermBridge
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-! Permutation-averaged replacement of the nonce array in the oracle world.
The bounded continuation may use both public primitives and every nonce. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec Permutation Permutation.NonceChain
local instance chainDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
set_option linter.unusedSectionVars false
set_option maxRecDepth 12000

private theorem le_add_ofReal_of_toReal {a b : ENNReal} {ε : ℝ} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (hε : 0 ≤ ε) (h : a.toReal ≤ b.toReal + ε) : a ≤ b + ENNReal.ofReal ε := by
  calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal ha).symm
    _ ≤ ENNReal.ofReal (b.toReal + ε) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal b.toReal + ENNReal.ofReal ε := ENNReal.ofReal_add ENNReal.toReal_nonneg hε
    _ = b + ENNReal.ofReal ε := by rw [ENNReal.ofReal_toReal hb]

/-- Total variation is the largest event discrepancy. -/
theorem tv_le_of_events {α : Type} (mx my : ProbComp α) (ε : ℝ) (nonneg : 0 ≤ ε)
    (close : ∀ event : α → Prop,
      |(prEvent (event <$> mx)).toReal - (prEvent (event <$> my)).toReal| ≤ ε) :
    measureTVDist mx my ≤ ε := by
  rw [measureTVDist_eq_toReal_measureETVDist]
  apply ENNReal.toReal_le_of_le_ofReal nonneg
  rw [measureETVDist, MeasureTheory.Measure.etvDist]
  refine iSup_le fun set => ?_
  have left := prEvent_eq_evalDist_of_discrete mx (fun value => value ∈ set.1)
  have right := prEvent_eq_evalDist_of_discrete my (fun value => value ∈ set.1)
  simp only [Set.setOf_mem_eq] at left right
  have bound := abs_sub_le_iff.mp (close (fun value => value ∈ set.1))
  rw [← left, ← right, ENNReal.absDiff_le_iff]
  exact ⟨le_add_ofReal_of_toReal (prEvent_ne_top _) (prEvent_ne_top _) nonneg (by linarith [bound.1]),
    le_add_ofReal_of_toReal (prEvent_ne_top _) (prEvent_ne_top _) nonneg (by linarith [bound.2])⟩

theorem iid_nonce_marginal (f : (Index → Nonce) → ℝ) :
    mean f = mean (fun p : Fin blocks → Block => f (nonceAt p)) := by
  have prod := mean_prod (fun r (_ : Fin 512 → Nonce) => f r)
  simp only [mean, avg_const Finset.univ_nonempty] at prod
  exact prod.symm.trans (mean_equiv projectTape (fun z => f z.1)).symm


variable {α : Type}
abbrev SaltArray := Index → BitVec 128

noncomputable def chainNonceGame (c : Compression) (g : SaltArray → OracleComp World α) : ProbComp α := do
  let π ← $ᵗ Perm
  let k ← $ᵗ Key
  fixedOracleRun ⟨c,π⟩ (g (actualNonces π k))

def iidNonceGame (c : Compression) (g : SaltArray → OracleComp World α) : ProbComp α := do
  let r ← $ᵗ SaltArray
  let π ← $ᵗ Perm
  fixedOracleRun ⟨c,π⟩ (g r)

private theorem uniform_mean {X : Type} [Fintype X] [SampleableType X]
    (f : X → ProbComp α) (event : α → Prop) :
    (prEvent (event <$> (($ᵗ X) >>= f))).toReal =
      mean (fun x => (prEvent (event <$> f x)).toReal) := by
  classical
  have ex : prEvent (event <$> (($ᵗ X) >>= f)) =
      ENNReal.ofReal (mean (fun x => (prEvent (event <$> f x)).toReal)) := by
    rw [prEvent_bind_eq_sum_fintype, ← sum_inv_card_mul_ofReal _ fun _ => ENNReal.toReal_nonneg]
    apply Finset.sum_congr rfl
    intro x _
    rw [SampleableType.prEvent_uniformSample_eq_singleton, ENNReal.ofReal_toReal (prEvent_ne_top _)]
  rw [ex, ENNReal.toReal_ofReal (avg_nonneg fun _ _ => ENNReal.toReal_nonneg)]

open Classical in
private noncomputable def eventStrategy (c : Compression) (g : SaltArray → OracleComp World α)
    (event : α → Prop) (p : Fin blocks → Block) : Strat Word1600 Bool :=
  (toStrat c (g (nonceAt p))).bind (fun a => Strat.done (decide (event a)))

private theorem eager_event (π : Perm) (st : Strat Word1600 α) (event : α → Prop)
    [DecidablePred event] (s : PState Word1600) :
    (st.bind (fun a => .done (decide (event a)))).eager π s (fun b _ => accept b) =
      st.eager π s (fun a _ => ind (event a)) := by
  induction st generalizing s with
  | done a => by_cases h : event a <;> simp [Strat.bind,Strat.eager,accept,h,ind]
  | fwd x k ih => exact ih _ _
  | inv y k ih => exact ih _ _
  | rand m k ih => exact avg_congr (fun i _ => ih i _)

private theorem sample_event (c : Compression) (π : Perm) (g : SaltArray → OracleComp World α)
    (event : α → Prop) (p : Fin blocks → Block) :
    (prEvent (event <$> fixedOracleRun ⟨c,π⟩ (g (nonceAt p)))).toReal =
      (eventStrategy c g event p).eager π PState.init (fun b _ => accept b) := by
  classical
  rw [fixed_run_prob c π _ event PState.init,
    ENNReal.toReal_ofReal (Strat.eager_nonneg _ (fun _ _ => ind_nonneg _) _ _)]
  exact (eager_event π (toStrat c (g (nonceAt p))) event PState.init).symm

private theorem real_event (c : Compression) (g : SaltArray → OracleComp World α) (e : α → Prop) :
    (prEvent (e <$> chainNonceGame c g)).toReal =
      realProb blockEquiv seedState (eventStrategy c g e) := by
  unfold chainNonceGame realProb
  rw [uniform_mean]
  apply avg_congr
  intro π _
  rw [uniform_mean]
  apply avg_congr
  intro k _
  exact sample_event c π g e _

private theorem ideal_event (c : Compression) (g : SaltArray → OracleComp World α) (e : α → Prop) :
    (prEvent (e <$> iidNonceGame c g)).toReal = idealProb (eventStrategy c g e) := by
  unfold iidNonceGame idealProb
  rw [uniform_mean]
  let f := fun r : SaltArray =>
    (prEvent (e <$> (($ᵗ Perm) >>= fun π => fixedOracleRun ⟨c,π⟩ (g r)))).toReal
  rw [iid_nonce_marginal f]
  apply avg_congr
  intro p _
  dsimp only [f]
  rw [uniform_mean,← Strat.avg_eager]
  apply avg_congr
  intro π _
  exact sample_event c π g e p

noncomputable def chainError (q : Nat) : ℝ := ((blocks+1 : Nat) : ℝ) * ((2*q+(blocks+1) : ℝ)/2^192)

theorem nonce_chain_oracle_distance (c : Compression) (g : SaltArray → OracleComp World α) (q : Nat)
    (bound : ∀ r, PublicQueryBound (g r) q) :
    measureTVDist (chainNonceGame c g) (iidNonceGame c g) ≤ chainError q := by
  classical
  have event (e : α → Prop) :
      (prEvent (e <$> iidNonceGame c g)).toReal ≤
        (prEvent (e <$> chainNonceGame c g)).toReal + chainError q := by
    rw [real_event,ideal_event]
    have B (p : Fin blocks → Block) : (eventStrategy c g e p).QB q :=
      (to_strat_QB c (bound (nonceAt p))).bind (fun a =>
        Strat.QB.done (decide (e a)) 0)
    have h := ideal_le_real blockEquiv seedState seed_injective (eventStrategy c g e) q B
    have card : Fintype.card Key = 2^192 := by rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
    simpa only [chainError,card,Nat.cast_pow,Nat.cast_ofNat] using h
  apply tv_le_of_events _ _ _ (by unfold chainError; positivity)
  intro e
  have upper := event (fun a => ¬e a)
  rw [prEvent_not_eq_one_sub,prEvent_not_eq_one_sub,ENNReal.toReal_sub_of_le (prEvent_le_one _) ENNReal.one_ne_top,
    ENNReal.toReal_sub_of_le (prEvent_le_one _) ENNReal.one_ne_top,ENNReal.toReal_one] at upper
  have lower := event e
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

end CommitGolfCandidate
