import CommitGolfCandidate.TaggedPinnedEnumeration

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2048

local instance pinnedConditionalObserverDiscrete {α : Type} : MeasurableSpace α := ⊤

noncomputable local instance pinnedConditionalFunctionSampler {I V : Type} [Fintype I] [Fintype V] [Nonempty V] :
    SampleableType (I → V) := by
  classical
  exact SampleableType.ofFintype _

noncomputable def samplePinnedBasePermutation {base : Cache} {count : Nat}
    (state : PinnedOpenedState base count) [DecidablePred state.isRevealed]
    (opened : {i : Fin count // state.isRevealed i} → BitVec 256) : ProbComp (BiPermutation Block) := do
  let priv ← samplePinnedLowFn state.PrivateSlot
  let p ← (state.high.realize (pinnedFinLowTape (state.merge opened priv))).sample
  pure p.val

section Conditional
variable {I : Type} [Fintype I]
variable {base : Cache} {count : Nat} (state : PinnedOpenedState base count) [DecidablePred state.isRevealed]
variable (opened : {i : Fin count // state.isRevealed i} → BitVec 256)
variable (position : I → Index) (first : I → Block) (message : I → Words 32)
variable {Output : Type} (observe : (I → BitVec 256) → BiPermutation Block → ProbComp Output)

noncomputable def pinnedActualNonce (nonce : I → BitVec 128) : ProbComp Output :=
  let addresses := pinnedNonceAddresses position first message nonce
  let order := pinnedNonceOrder position first message nonce
  pinnedRunHiddenActual state opened addresses (fun digests p => observe (fun i => digests (order.symm i)) p)

noncomputable def pinnedRowsNonce (digest : I → BitVec 256) (nonce : I → BitVec 128) : ProbComp (List Row) := by
  classical
  let addresses := pinnedNonceAddresses position first message nonce
  exact if ∀ input ∈ addresses, UnusedInput base.entries input then do
    let final ← runPinnedHigh state.high count [] (pinnedConstantPlans addresses)
    pure ((Finset.univ : Finset I).toList.map fun i =>
      let input := pinnedPrivateSecond (position i) (first i) (message i) (nonce i)
      (input, pinnedCachedUpper final.2.zero input ++ digest i))
  else pure []

noncomputable def pinnedProgrammedNonce (nonce : I → BitVec 128) : ProbComp Output := do
  let digest ← samplePinnedLowFn I
  let perm ← samplePinnedBasePermutation state opened
  let rows ← pinnedRowsNonce state position first message digest nonce
  observe digest (perm.programRows rows)

theorem pinned_actual_nonce_programmed (valid : state.high.Valid count) (unique : Function.Injective position)
    (nonce : I → BitVec 128)
    (room : state.high.zero.entries.length + Fintype.card I ≤ 2^121)
    (disjoint : ∀ addr ∈ pinnedNonceAddresses position first message nonce, addr ∉ state.opened)
    (safe : ∀ addr ∈ pinnedNonceAddresses position first message nonce, UnusedInput base.entries addr) :
    pinnedActualNonce state opened position first message observe nonce =ᵈ
      pinnedProgrammedNonce state opened position first message observe nonce := by
  classical
  let addresses := pinnedNonceAddresses position first message nonce
  let order := pinnedNonceOrder position first message nonce
  let program := runPinnedHigh state.high count [] (pinnedConstantPlans addresses)
  let finish (priv : state.PrivateSlot → BitVec 256) (digest : Fin addresses.length → BitVec 256) : ProbComp Output := do
    let p ← (state.high.realize (pinnedFinLowTape (state.merge opened priv))).sample
    let generated ← program
    let rows : List Row := addresses.map (fun input => (input, (pinnedCachedUpper generated.2.zero input ++
      pinnedDigestByAddress addresses digest input : Block)))
    observe (fun i => digest (order.symm i)) (p.val.programRows rows)
  have validLen : state.high.zero.entries.length + addresses.length ≤ 2^121 := by
    simpa only [addresses, pinned_nonce_addresses_length] using room
  apply (pinned_safe_hidden_programmed state valid opened addresses
    (pinned_nonce_addresses_nodup position unique first message nonce) disjoint safe validLen
    (fun digests p => observe (fun i => digests (order.symm i)) p)).trans
  apply (pinned_uniform_digest_tape_split finish).trans
  trans (do let priv ← samplePinnedLowFn state.PrivateSlot
            let digest ← samplePinnedLowFn I
            finish priv (fun i => digest (order i)))
  · apply EvalDistEq.bind_right
    intro priv
    exact pinned_low_function_order order (finish priv)
  · apply (EvalDistEq.of_evalDist_eq (distribution_bind_comm (samplePinnedLowFn state.PrivateSlot)
      (samplePinnedLowFn I) (fun priv digest => finish priv (fun i => digest (order i))))).trans
    unfold pinnedProgrammedNonce samplePinnedBasePermutation
    simp only [bind_assoc, pure_bind]
    apply EvalDistEq.bind_right
    intro digest
    apply EvalDistEq.bind_right
    intro priv
    apply EvalDistEq.bind_right
    intro p
    let made (generated : List (BitVec 1344) × PinnedHighCache base) : List Row :=
      (Finset.univ : Finset I).toList.map fun i =>
        let input := pinnedPrivateSecond (position i) (first i) (message i) (nonce i)
        (input, (pinnedCachedUpper generated.2.zero input ++ digest i : Block))
    have branch : pinnedRowsNonce state position first message digest nonce = (made <$> program) := by
      rw [map_eq_bind_pure_comp]
      change (if ∀ addr ∈ addresses, UnusedInput base.entries addr then program >>= (pure ∘ made) else pure []) = _
      exact ite_eq_left safe
    have resumed : (pinnedRowsNonce state position first message digest nonce >>= fun rows =>
        observe digest (p.val.programRows rows)) =
        (program >>= fun generated => observe digest (p.val.programRows (made generated))) := by
      simp only [branch, bind_map_left]
    rw [resumed]
    apply EvalDistEq.bind_right
    intro generated
    have rows := pinned_nonce_program_rows_match position unique first message nonce digest
      (pinnedCachedUpper generated.2.zero)
    have data : (fun i => digest (order (order.symm i))) = digest := by
      funext i
      rw [order.apply_symm_apply]
    let result := (Finset.univ : Finset I).toList.map fun i =>
      let input := pinnedPrivateSecond (position i) (first i) (message i) (nonce i)
      (input, (pinnedCachedUpper generated.2.zero input ++ digest i : Block))
    change observe (fun i => digest (order (order.symm i))) (p.val.programRows
      (addresses.map (fun input => (input, (pinnedCachedUpper generated.2.zero input ++
        pinnedDigestByAddress addresses (fun i => digest (order i)) input : Block))))) =ᵈ
      observe digest (p.val.programRows result)
    rw [data]
    exact EvalDistEq.of_evalDist_eq (congrArg (fun rows => evalDist (observe digest (p.val.programRows rows))) rows)

noncomputable def pinnedConditionalActual : ProbComp Output :=
  ($ᵗ (I → BitVec 128)) >>= pinnedActualNonce state opened position first message observe

noncomputable def pinnedConditionalReference : ProbComp Output := do
  let digest ← samplePinnedLowFn I
  let perm ← samplePinnedBasePermutation state opened
  observe digest perm

noncomputable def pinnedConditionalProgrammed : ProbComp Output := do
  let digest ← samplePinnedLowFn I
  let perm ← samplePinnedBasePermutation state opened
  let rows ← samplePinnedHiddenRows state.high count position first message digest
  observe digest (perm.programRows rows)

private theorem pinned_programmed_reorder :
    (($ᵗ (I → BitVec 128)) >>= pinnedProgrammedNonce state opened position first message observe) =ᵈ
      pinnedConditionalProgrammed state opened position first message observe := by
  let nonces := ($ᵗ (I → BitVec 128))
  let digests := samplePinnedLowFn I
  let perm := samplePinnedBasePermutation state opened
  let tail (nonce : I → BitVec 128) (digest : I → BitVec 256) (p : BiPermutation Block) := do
    let rows ← pinnedRowsNonce state position first message digest nonce
    observe digest (p.programRows rows)
  apply (EvalDistEq.of_evalDist_eq (distribution_bind_comm nonces digests
    (fun nonce digest => perm >>= tail nonce digest))).trans
  apply EvalDistEq.bind_right
  intro digest
  have exchange := distribution_bind_comm nonces perm (fun nonce p => tail nonce digest p)
  exact EvalDistEq.of_evalDist_eq (exchange.trans (by
    unfold samplePinnedHiddenRows
    simp only [tail, nonces, perm, pinnedRowsNonce, bind_assoc]))

theorem pinned_conditional_actual_programmed_distance [DecidableEq I]
    (valid : state.high.Valid count) (unique : Function.Injective position)
    (room : state.high.zero.entries.length + Fintype.card I ≤ 2^121)
    (disjoint : ∀ nonce addr, addr ∈ pinnedNonceAddresses position first message nonce → addr ∉ state.opened) :
    measureTVDist (pinnedConditionalActual state opened position first message observe)
      (pinnedConditionalProgrammed state opened position first message observe) ≤ (base.entries.length : ℝ)/2^128 := by
  classical
  let safe (nonce : I → BitVec 128) := ∀ addr ∈ pinnedNonceAddresses position first message nonce,
    UnusedInput base.entries addr
  let bad (nonce : I → BitVec 128) := ¬ safe nonce
  have before := measureTVDist_bind_left_le_prEvent_of_evalDistEq ($ᵗ (I → BitVec 128))
    (pinnedActualNonce state opened position first message observe)
    (pinnedProgrammedNonce state opened position first message observe) bad (fun nonce unbroken =>
      pinned_actual_nonce_programmed state opened position first message observe valid unique nonce room (disjoint nonce)
        (Classical.not_not.mp unbroken))
  have bound := pinned_known_address_hit_le position unique first message (base.entries.map Prod.fst)
  have enlarged : Pr{let nonce ← $ᵗ (I → BitVec 128)}[bad nonce] ≤ (base.entries.length : ENNReal)/2^128 := by
    rw [List.length_map] at bound
    refine (prEvent_mono _ (p := bad)
      (q := fun nonce => ∃ addr ∈ base.entries.map Prod.fst, ∃ i,
        pinnedPrivateSecond (position i) (first i) (message i) (nonce i) = addr) ?_).trans bound
    intro nonce broken
    have event : ∃ addr ∈ pinnedNonceAddresses position first message nonce, ∃ row ∈ base.entries, row.1 = addr := by
      by_contra no
      apply broken
      intro addr present row known same
      exact no ⟨addr, present, row, known, same⟩
    obtain ⟨addr, found, row, known, eq⟩ := event
    obtain ⟨i, _, hit⟩ := List.mem_map.mp found
    exact ⟨row.1, List.mem_map_of_mem known, i, hit.trans eq.symm⟩
  unfold pinnedConditionalActual measureTVDist
  rw [← (pinned_programmed_reorder state opened position first message observe).evalDist_eq]
  refine before.trans ?_
  simpa only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
    using ENNReal.toReal_mono (by finiteness) enlarged

end Conditional

noncomputable def pinnedOneSideCharge (budget : Nat) : ℝ :=
  (budget : ℝ)/2^128 + (budget : ℝ)*(2/2^128 + 2^25/2^1344)

theorem pinned_conditional_to_reference {I Output : Type} [Fintype I] [DecidableEq I]
    {base : Cache} {count : Nat} (state : PinnedOpenedState base count) [DecidablePred state.isRevealed]
    (valid : state.high.Valid count) (opened : {i : Fin count // state.isRevealed i} → BitVec 256)
    (position : I → Index) (unique : Function.Injective position) (first : I → Block) (message : I → Words 32)
    (room : state.high.zero.entries.length + Fintype.card I ≤ 2^121)
    (disjoint : ∀ nonce addr, addr ∈ pinnedNonceAddresses position first message nonce → addr ∉ state.opened)
    (compress : Compression) (observer : (I → BitVec 256) → OracleComp World Output)
    (budget : Nat) (bounded : ∀ digest, QueryBounded (observer digest) budget)
    (before : base.entries.length ≤ budget) (sites : Fintype.card I ≤ 2^24) :
    let execute := fun digest p => fixedOracleRun (fixedOracle compress p) (observer digest)
    measureTVDist (pinnedConditionalActual state opened position first message execute)
      (pinnedConditionalReference state opened execute) ≤ pinnedOneSideCharge budget := by
  let execute := fun digest p => fixedOracleRun (fixedOracle compress p) (observer digest)
  let actual := pinnedConditionalActual state opened position first message execute
  let programmed := pinnedConditionalProgrammed state opened position first message execute
  let reference := pinnedConditionalReference state opened execute
  have pre : measureTVDist actual programmed ≤ (budget : ℝ)/2^128 :=
    (pinned_conditional_actual_programmed_distance state opened position first message execute valid unique room disjoint).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast before) (by positivity))
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
  have post : measureTVDist programmed reference ≤ (budget : ℝ)*(2/2^128 + 2^25/2^1344) := by
    rw [measureTVDist_comm]
    apply measureTVDist_bind_left_le_of_forall_le (samplePinnedLowFn I) _ _ (by positivity)
    intro digest
    apply measureTVDist_bind_left_le_of_forall_le (samplePinnedBasePermutation state opened) _ _ (by positivity)
    intro permutation
    have payment := pinned_adaptive_programmed_distance
      (samplePinnedHiddenRows state.high count position first message digest) rate (by unfold rate; finiteness)
      compress permutation (observer digest) budget (bounded digest)
      (fun row => pinned_hidden_rows_hit_le state.high count valid position unique first message digest room row)
    apply payment.trans
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
    exact mul_le_mul_of_nonneg_left rateBound (by positivity)
  exact (measureTVDist_triangle actual programmed reference).trans (add_le_add pre post)

end TwoPermutationPrototype.Sampling
