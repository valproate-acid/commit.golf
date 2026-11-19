import CommitGolfCandidate.TwoPermutationTaglessConditional

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp MeasureTheory CommitGolfCandidate
open scoped ENNReal
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2048

noncomputable local instance {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

local instance {α : Type} : MeasurableSpace α := ⊤

noncomputable def taglessOpenedMix (positions : Positions) (messages : Index → Words 32)
    (cache : Cache) : ProbComp (OpenedSalts positions × TaglessOpenedResult) := do
  let salts ← $ᵗ OpenedSalts positions
  let result ← runTaglessOpened messages (publicOpenedSalts salts) cache [] positions.toList
  pure (salts, result)

noncomputable def taglessTwoPhaseReference {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (which : Bool) : ProbComp Output := do
  let (challenge, initial) ← lazyRun compress adversary.choose (PermutationCache.empty Block)
  let (salts, opened) ← taglessOpenedMix challenge.positions (messageWords challenge.message₀) initial
  let observer := fun tape =>
    let (root, proof) := build compress challenge.positions salts tape
    adversary.observe challenge.aux root proof
  let message := if which then challenge.message₁ else challenge.message₀
  taglessConditionalGame opened.cache (messageWords message)
    (readOpenedDigests challenge.positions opened.replies.reverse) compress observer false

/-- In a shared mixture a bad common history is paid for once. Its probability
needs no conditioning on either world's private continuation. -/
theorem tagless_distance_bind_guard_le {ι α : Type} (common : ProbComp ι)
    (left right : ι → ProbComp α) (bad : ι → Prop) (error : ℝ) (nonneg : 0 ≤ error)
    (each : ∀ value ∈ support common, ¬ bad value → measureTVDist (left value) (right value) ≤ error) :
    measureTVDist (common >>= left) (common >>= right) ≤
      error + (Pr{let value ← common}[bad value]).toReal := by
  classical
  let weight (seed : ι) := Pr{let value ← common}[value = seed]
  have eventFinite : Pr{let value ← common}[bad value] ≠ ∞ :=
    ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ∞) (prEvent_le_one _)
  have bound : measureETVDist (common >>= left) (common >>= right) ≤
      ENNReal.ofReal error + Pr{let value ← common}[bad value] := by
    refine (measureETVDist_bind_left_le_tsum common left right).trans ?_
    calc
      _ ≤ ∑' seed : ι, (weight seed * ENNReal.ofReal error + if bad seed then weight seed else 0) := by
        apply ENNReal.tsum_le_tsum
        intro seed
        by_cases badSeed : bad seed
        · simp only [badSeed, ite_true]
          exact (mul_le_mul_of_nonneg_left (measureETVDist_le_one _ _) zero_le).trans
            (by rw [mul_one]; exact le_add_of_nonneg_left zero_le)
        · simp only [badSeed, ite_false, add_zero]
          by_cases present : seed ∈ support common
          · exact mul_le_mul_of_nonneg_left
              ((ENNReal.le_ofReal_iff_toReal_le (measureETVDist_ne_top _ _) nonneg).2 (each seed present badSeed)) zero_le
          · have zero : Pr{let y ← common}[y = seed] = 0 :=
              (prEvent_eq_zero_iff common (· = seed)).2 (fun value mem equal => present (equal ▸ mem))
            simp [weight, zero]
      _ = _ := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, show (∑' seed, weight seed) = 1 from tsum_prEvent_eq_one common,
          one_mul, prEvent_eq_tsum_ite]
  rw [measureTVDist_eq_toReal_measureETVDist]
  apply (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, eventFinite⟩) bound).trans_eq
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top eventFinite, ENNReal.toReal_ofReal nonneg]

private theorem tagless_observe_bound {State Output : Type} {openingSize budget : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (bounded : Hiding.QueryBound adversary budget)
    (compress : Compression) (result : Hiding.HidingChallenge State openingSize × Cache)
    (reached : result ∈ support (lazyRun compress adversary.choose (PermutationCache.empty Block)))
    (root : Commitment) (proof : Proof) :
    QueryBounded (adversary.observe result.1.aux root proof) budget := by
  have projected : result.1 ∈ support
      ((simulateQ (lazyHandler compress) adversary.choose).run' (PermutationCache.empty Block)) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨result, reached, rfl⟩
  have possible := support_simulateQ_run'_subset (lazyHandler compress) adversary.choose _ projected
  have instrumented : result.1 ∈ support (Prod.fst <$> Hiding.counted adversary.choose) := by
    rw [show Prod.fst <$> Hiding.counted adversary.choose = adversary.choose from
      fst_map_costDist adversary.choose ⟨Oracle.callCost⟩]
    exact possible
  rw [support_map] at instrumented
  obtain ⟨⟨challenge, calls⟩, counted, equal⟩ := instrumented
  change challenge = result.1 at equal
  subst challenge
  exact (hiding_observe_query_bound adversary bounded (result.1, calls) counted root proof).mono
    (Nat.sub_le _ _)

private theorem tagless_conditional_error_nonneg (budget : Nat) : 0 ≤ taglessConditionalError budget := by
  unfold taglessConditionalError taglessProposalError
  positivity

theorem tagless_combined_margin (budget : Nat) :
    taglessOpenedGuard budget + taglessConditionalError budget ≤ ((budget : ℝ) + 1) / 2^125 := by
  have nonneg : 0 ≤ (budget : ℝ) := Nat.cast_nonneg budget
  unfold taglessOpenedGuard taglessConditionalError taglessProposalError
  norm_num
  linarith

theorem tagless_two_phase_hiding {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (budget : Nat) (bounded : Hiding.QueryBound adversary budget) :
    measureTVDist (taglessTwoPhaseReference adversary build compress false)
      (taglessTwoPhaseReference adversary build compress true) ≤ min 1 (((budget : ℝ) + 1) / 2 ^ 120) := by
  classical
  refine le_min (measureTVDist_le_one _ _) ?_
  by_cases small : budget + 1 ≤ 2 ^ 120
  · have combined := tagless_combined_margin budget
    have limit : ((budget : ℝ) + 1) / 2^125 ≤ ((budget : ℝ) + 1) / 2^120 := by
      have nonneg : 0 ≤ (budget : ℝ) := Nat.cast_nonneg budget
      norm_num
      linarith
    refine le_trans ?_ (combined.trans limit)
    unfold taglessTwoPhaseReference
    let chooser := lazyRun compress adversary.choose (PermutationCache.empty Block)
    apply le_trans (b := (taglessConditionalError budget + taglessOpenedGuard budget) +
      (Pr{let value ← chooser}[False]).toReal)
    · refine tagless_distance_bind_guard_le chooser _ _ (fun _ => False)
        (taglessConditionalError budget + taglessOpenedGuard budget)
        (add_nonneg (tagless_conditional_error_nonneg budget) (by unfold taglessOpenedGuard; positivity)) ?_
      intro first inFirst _
      have before : first.2.entries.length ≤ budget := by
        have length := lazy_cache_length compress adversary.choose (PermutationCache.empty Block) budget
          (hiding_choose_query_bound adversary bounded) first inFirst
        simpa only [PermutationCache.empty, List.length_nil, Nat.zero_add] using length
      let positions := first.1.positions
      let messages := messageWords first.1.message₀
      let common := taglessOpenedMix positions messages first.2
      let bad (result : OpenedSalts positions × TaglessOpenedResult) :=
        taglessOpenedBad messages first.2 result.1 result.2
      have sites : positions.card ≤ 2 ^ 24 := by
        have count := hidden_index_count positions
        omega
      have room : first.2.entries.length + 2 * positions.card ≤ 2 ^ 121 :=
        (Nat.add_le_add_right before _).trans (tagless_opened_history_room budget positions.card small sites)
      have guard : (Pr{let result ← common}[bad result]).toReal ≤ taglessOpenedGuard budget := by
        have exactBound := tagless_opened_tape_guard_le positions messages first.2 room
        have enlarged : Pr{let result ← common}[bad result] ≤
            (budget : ENNReal)/2^128 + (2 : ENNReal)^24/2^167 :=
          exactBound.trans (add_le_add (ENNReal.div_le_div_right (by exact_mod_cast before) _)
            (ENNReal.div_le_div_right (by exact_mod_cast sites) _))
        have real := ENNReal.toReal_mono (by finiteness) enlarged
        rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at real
        simpa [taglessOpenedGuard, ENNReal.toReal_div, ENNReal.toReal_pow] using real
      refine (tagless_distance_bind_guard_le common _ _ bad (taglessConditionalError budget)
        (tagless_conditional_error_nonneg budget) ?_).trans (add_le_add (le_refl _) guard)
      rintro ⟨salts, opened⟩ possible safe
      have inRun : opened ∈ support (runTaglessOpened messages (publicOpenedSalts salts) first.2 [] positions.toList) := by
        simp only [common, taglessOpenedMix, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at possible
        obtain ⟨salts', _, opened', reached, equal⟩ := possible
        cases equal
        exact reached
      have good : opened.bad = false := by
        have notTrue : ¬ opened.bad = true := fun isTrue => safe (Or.inr isTrue)
        simpa using notTrue
      obtain ⟨rows, seed, count, tags⟩ := tagless_opened_rows positions messages (publicOpenedSalts salts)
        first.2 [] positions.toList (fun i included => Finset.mem_toList.mp included) opened inRun good
      simp only [Bool.false_eq_true, ite_false, ite_true]
      apply tagless_conditional_hiding _ _ _ _ _ _ first.2.entries rows budget seed before
        (by simpa only [Finset.length_toList] using count) tags
      intro tape
      exact tagless_observe_bound adversary bounded compress first inFirst _ _
    · simp [prEvent_false, add_comm]
  · apply (measureTVDist_le_one _ _).trans
    have large : (2 ^ 120 : ℝ) ≤ (budget : ℝ) + 1 := by
      exact_mod_cast (show 2 ^ 120 ≤ budget + 1 by omega)
    exact (le_div_iff₀ (by positivity)).mpr (by simpa using large)

end TwoPermutationPrototype.Sampling
