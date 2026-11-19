import CommitGolfCandidate.PentaHidingRows

/-! The one step of the pinned hiding proof that needs the observer in oracle form, generalized to
observers that also receive the penta node function `pentaFunction p.forward` of the same permutation.

Programming the hidden second-call rows changes `pentaFunction` only if a programmed output has its
preimage in `D2`; that costs at most `|I| · 2^-575`. With the penta function frozen at the base
permutation, the existing adaptive-programming bound applies unchanged. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2048
set_option linter.constructorNameAsVariable false

local instance pentaConditionalDiscrete {α : Type} : MeasurableSpace α := ⊤

section PentaConditional
variable {I : Type} [Fintype I]
variable {base : Cache} {count : Nat} (state : PinnedOpenedState base count) [DecidablePred state.isRevealed]
variable (opened : {i : Fin count // state.isRevealed i} → BitVec 256)
variable (position : I → Index) (first : I → Block) (message : I → Words 32)

theorem pinned_hidden_rows_length {base : Cache} (cache : PinnedHighCache base) (slot : Nat)
    (digests : I → BitVec 256) (rows : List Row)
    (reached : rows ∈ support (samplePinnedHiddenRows cache slot position first message digests)) :
    rows.length ≤ Fintype.card I := by
  classical
  unfold samplePinnedHiddenRows at reached
  obtain ⟨nonce, _, rest⟩ := (mem_support_bind_iff _ _ _).mp reached
  let addresses := pinnedNonceAddresses position first message nonce
  by_cases new : ∀ input ∈ addresses, UnusedInput base.entries input
  · rw [ite_eq_left new] at rest
    obtain ⟨final, _, made⟩ := (mem_support_bind_iff _ _ _).mp rest
    simp only [support_pure, Set.mem_singleton_iff] at made
    subst rows
    simp
  · rw [ite_eq_right new] at rest
    simp only [support_pure, Set.mem_singleton_iff] at rest
    subst rows
    simp

noncomputable def pentaProgrammedPairs (digest : I → BitVec 256) :
    ProbComp (BiPermutation Block × List Row) := do
  let perm ← samplePinnedBasePermutation state opened
  let rows ← samplePinnedHiddenRows state.high count position first message digest
  pure (perm, rows)

def pentaProgramBad (pair : BiPermutation Block × List Row) : Prop :=
  ∃ row ∈ pair.2, row.1 ∈ PentaDomain ∨ pair.1.inverse row.2 ∈ PentaDomain

theorem penta_programmed_bad_le [DecidableEq I] (valid : state.high.Valid count)
    (room : state.high.zero.entries.length + Fintype.card I ≤ 2^121) (digest : I → BitVec 256) :
    Pr{let pair ← pentaProgrammedPairs state opened position first message digest}[pentaProgramBad pair] ≤
      (Fintype.card I : ENNReal) / 2^319 := by
  classical
  let perms := samplePinnedBasePermutation state opened
  let rowsSampler := samplePinnedHiddenRows state.high count position first message digest
  have swapped := EvalDistEq.of_evalDist_eq (distribution_bind_comm perms rowsSampler
    (fun perm rows => (pure (perm, rows) : ProbComp (BiPermutation Block × List Row))))
  unfold pentaProgrammedPairs
  rw [swapped.prEvent_eq]
  apply prEvent_bind_le_of_forall_le_of_support
  intro rows reached
  have safe (low : PinnedLowTape) :=
    pinned_hidden_rows_output_safe state.high count valid position first message digest room rows reached low
  rw [bind_pure_comp, prEvent_map]
  have each : ∀ row ∈ rows, Pr{let perm ← perms}[row.1 ∈ PentaDomain ∨ perm.inverse row.2 ∈ PentaDomain] ≤
      (1 : ENNReal) / 2^319 := by
    intro row present
    refine (prEvent_mono perms _ (fun perm => perm.inverse row.2 ∈ PentaDomain)
      (fun perm hit => hit.resolve_left (safe (fun _ => 0) row present).1)).trans ?_
    unfold perms samplePinnedBasePermutation
    apply prEvent_bind_le_of_forall_le_of_support
    intro priv _
    rw [bind_pure_comp, prEvent_map]
    let cache := state.high.realize (pinnedFinLowTape (state.merge opened priv))
    have length : cache.entries.length ≤ 2^121 := by
      have same : cache.entries.length = state.high.zero.entries.length := by
        unfold cache PinnedHighCache.zero
        rw [PinnedHighCache.entries_length, PinnedHighCache.entries_length]
      omega
    exact sample_inverse_quad_le cache row.2 length
      ((safe (pinnedFinLowTape (state.merge opened priv)) row present).2)
  have total := prEvent_list_le rows perms
    (fun row perm => row.1 ∈ PentaDomain ∨ perm.inverse row.2 ∈ PentaDomain) _ each
  refine le_trans (le_of_eq ?_) (total.trans ?_)
  · rfl
  · have shorter : (rows.length : ENNReal) ≤ Fintype.card I := by
      exact_mod_cast pinned_hidden_rows_length position first message state.high count digest rows reached
    calc (rows.length : ENNReal) * (1 / 2^319) ≤ (Fintype.card I : ENNReal) * (1 / 2^319) :=
          mul_le_mul_of_nonneg_right shorter zero_le
      _ = _ := by rw [mul_one_div]

set_option maxHeartbeats 4000000 in
theorem penta_conditional_to_reference [DecidableEq I] {Output : Type}
    (valid : state.high.Valid count) (unique : Function.Injective position)
    (room : state.high.zero.entries.length + Fintype.card I ≤ 2^121)
    (disjoint : ∀ nonce addr, addr ∈ pinnedNonceAddresses position first message nonce → addr ∉ state.opened)
    (compress : Compression) (observer : (I → BitVec 256) → PentaFunction → OracleComp World Output)
    (budget : Nat) (bounded : ∀ digest penta, QueryBounded (observer digest penta) budget)
    (before : base.entries.length ≤ budget) (sites : Fintype.card I ≤ 2^24) :
    let execute := fun digest p =>
      fixedOracleRun (fixedOracle compress p) (observer digest (pentaFunction p.forward))
    measureTVDist (pinnedConditionalActual state opened position first message execute)
      (pinnedConditionalReference state opened execute) ≤ pinnedOneSideCharge budget + 2^24 / 2^319 := by
  let execute := fun digest p =>
    fixedOracleRun (fixedOracle compress p) (observer digest (pentaFunction p.forward))
  let actual := pinnedConditionalActual state opened position first message execute
  let programmed := pinnedConditionalProgrammed state opened position first message execute
  let reference := pinnedConditionalReference state opened execute
  let frozen : ProbComp Output := do
    let digest ← samplePinnedLowFn I
    let perm ← samplePinnedBasePermutation state opened
    let rows ← samplePinnedHiddenRows state.high count position first message digest
    fixedOracleRun (fixedOracle compress (perm.programRows rows)) (observer digest (pentaFunction perm.forward))
  have pre : measureTVDist actual programmed ≤ (budget : ℝ)/2^128 :=
    (pinned_conditional_actual_programmed_distance state opened position first message execute valid unique room disjoint).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast before) (by positivity))
  let pairs (digest : I → BitVec 256) := pentaProgrammedPairs state opened position first message digest
  let programmedPairs : ProbComp Output := do
    let digest ← samplePinnedLowFn I
    let pair ← pairs digest
    execute digest (pair.1.programRows pair.2)
  let frozenPairs : ProbComp Output := do
    let digest ← samplePinnedLowFn I
    let pair ← pairs digest
    fixedOracleRun (fixedOracle compress (pair.1.programRows pair.2)) (observer digest (pentaFunction pair.1.forward))
  have programmedEq : programmed = programmedPairs := by
    simp only [programmed, programmedPairs, pairs, pentaProgrammedPairs, pinnedConditionalProgrammed,
      bind_assoc, pure_bind]
  have frozenEq : frozen = frozenPairs := by
    simp only [frozen, frozenPairs, pairs, pentaProgrammedPairs, bind_assoc, pure_bind]
  have freeze : measureTVDist programmed frozen ≤ 2^24 / 2^319 := by
    rw [programmedEq, frozenEq]
    apply measureTVDist_bind_left_le_of_forall_le (samplePinnedLowFn I) _ _ (by positivity)
    intro digest
    have distance := measureTVDist_bind_left_le_prEvent_of_evalDistEq (pairs digest)
      (fun pair => execute digest (pair.1.programRows pair.2))
      (fun pair => fixedOracleRun (fixedOracle compress (pair.1.programRows pair.2))
        (observer digest (pentaFunction pair.1.forward))) pentaProgramBad (by
      intro pair good
      have away : ∀ row ∈ pair.2, row.1 ∉ PentaDomain ∧ pair.1.inverse row.2 ∉ PentaDomain := by
        intro row present
        exact not_or.mp (fun hit => good ⟨row, present, hit⟩)
      have same := penta_function_program_rows pair.1 pair.2 away
      change fixedOracleRun (fixedOracle compress (pair.1.programRows pair.2))
          (observer digest (pentaFunction (pair.1.programRows pair.2).forward)) =ᵈ
        fixedOracleRun (fixedOracle compress (pair.1.programRows pair.2)) (observer digest (pentaFunction pair.1.forward))
      rw [same])
    refine distance.trans ?_
    have bound := penta_programmed_bad_le state opened position first message valid room digest
    have cardBound : (Fintype.card I : ENNReal) / 2^319 ≤ 2^24 / 2^319 := by
      gcongr
      exact_mod_cast sites
    have real := ENNReal.toReal_mono (by finiteness) (bound.trans cardBound)
    simpa only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat] using real
  let rate : ENNReal := (1 : ENNReal)/2^128 + 1/2^128 + (Fintype.card I : ENNReal)/2^1343
  have rateBound : rate.toReal ≤ (2 : ℝ)/2^128 + 2^25/2^1344 := by
    unfold rate
    repeat first
      | rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      | rw [ENNReal.toReal_div]
      | rw [ENNReal.toReal_pow]
    simp only [ENNReal.toReal_natCast, ENNReal.toReal_one, ENNReal.toReal_ofNat]
    have cardBound : (Fintype.card I : ℝ) ≤ 2^24 := by exact_mod_cast sites
    norm_num
    linarith
  have post : measureTVDist frozen reference ≤ (budget : ℝ)*(2/2^128 + 2^25/2^1344) := by
    rw [measureTVDist_comm]
    apply measureTVDist_bind_left_le_of_forall_le (samplePinnedLowFn I) _ _ (by positivity)
    intro digest
    apply measureTVDist_bind_left_le_of_forall_le (samplePinnedBasePermutation state opened) _ _ (by positivity)
    intro permutation
    have payment := pinned_adaptive_programmed_distance
      (samplePinnedHiddenRows state.high count position first message digest) rate (by unfold rate; finiteness)
      compress permutation (observer digest (pentaFunction permutation.forward)) budget (bounded _ _)
      (fun row => pinned_hidden_rows_hit_le state.high count valid position unique first message digest room row)
    apply payment.trans
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
    exact mul_le_mul_of_nonneg_left rateBound (by positivity)
  have chain := (measureTVDist_triangle actual programmed reference).trans
    (add_le_add pre ((measureTVDist_triangle programmed frozen reference).trans (add_le_add freeze post)))
  refine chain.trans (le_of_eq ?_)
  unfold pinnedOneSideCharge
  ring

end PentaConditional

end TwoPermutationPrototype.Sampling
