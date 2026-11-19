import CommitGolfCandidate.TwoPermutationAdaptive
import CommitGolfCandidate.TwoPermutationLeaf
import ToMathlib.Data.BitVec
import VCVio.OracleComp.QueryTracking.QueryBound

/-! First deferred-sampling binding event. Condition on any consistent table,
including one chosen adaptively through both public directions. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp MeasureTheory
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem remaining_input_count {α : Type} [Fintype α] [DecidableEq α] (table : List (α × α))
    [Fintype (RemainingInputs table)] :
    Fintype.card α - table.length ≤ Fintype.card (RemainingInputs table) := by
  classical
  let seen := (table.map Prod.fst).toFinset
  let correspondence : RemainingInputs table ≃ ↥(Finset.univ \ seen) :=
    Equiv.subtypeEquivRight fun address => by
      simp only [seen, Finset.mem_sdiff, Finset.mem_univ, List.mem_toFinset, true_and, UnusedInput]
      constructor
      · intro fresh present
        obtain ⟨row, inTable, equal⟩ := List.mem_map.mp present
        exact fresh row inTable equal
      · intro fresh row inTable same
        exact fresh (List.mem_map.mpr ⟨row, inTable, same⟩)
  have seenCount : seen.card ≤ table.length := by
    simpa only [seen, List.length_map] using List.toFinset_card_le (table.map Prod.fst)
  rw [Fintype.card_congr correspondence, Fintype.card_coe, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  exact Nat.sub_le_sub_left seenCount _

theorem inverse_fresh_event_le {α : Type} [Fintype α] [DecidableEq α]
    (cache : PermutationCache α) (output : α) (fresh : UnusedOutput cache.entries output)
    (bad : Set α) (size : Nat) (bound : bad.encard ≤ (size : ℕ∞)) :
    Pr{let answer ← @uniformSample _ (cache.inverseSampler output fresh)}[answer.val ∈ bad] ≤
      (size : ENNReal) / (Fintype.card α - cache.entries.length : Nat) := by
  let : MeasurableSpace (RemainingInputs cache.entries) := ⊤
  let : Fintype (RemainingInputs cache.entries) := Fintype.ofFinite _
  let : SampleableType (RemainingInputs cache.entries) := cache.inverseSampler output fresh
  let event : Set (RemainingInputs cache.entries) := {answer | answer.val ∈ bad}
  have smaller : event.encard ≤ bad.encard :=
    Set.encard_le_encard_of_injOn (f := Subtype.val) (fun _ present => present) Subtype.val_injective.injOn
  have probability := SampleableType.evalDist_uniformSample_le_of_encard_le event size (smaller.trans bound)
  rw [prEvent_eq_evalDist_of_discrete]
  refine probability.trans (ENNReal.div_le_div le_rfl ?_)
  exact_mod_cast remaining_input_count (α := α) cache.entries

def firstDomainBlock (value : Fin (2 ^ 24) × BitVec 1408) : Block :=
  (value.2 ++ (0#128)) ++ firstTag value.1.val

def firstDomain : Set Block := Set.range firstDomainBlock

theorem domain_of_header (block : Block) (index : Fin (2 ^ 24))
    (headerMatches : block.extractLsb' 0 192 = (0#128) ++ firstTag index.val) : block ∈ firstDomain := by
  refine ⟨(index, block.extractLsb' 192 1408), ?_⟩
  change ((block.extractLsb' 192 1408 ++ (0#128)) ++ firstTag index.val) = block
  have joined : (block.extractLsb' 192 1408 ++ ((0#128) ++ firstTag index.val)) = block := by
    rw [← headerMatches]
    exact BitVec.extractLsb'_append_extractLsb'
  rw [BitVec.append_assoc]
  exact joined

theorem first_domain_size : firstDomain.encard ≤ ((2 ^ 1432 : Nat) : ℕ∞) := by
  unfold firstDomain
  rw [← Set.image_univ]
  refine (Set.encard_image_le firstDomainBlock Set.univ).trans_eq ?_
  rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_prod, Fintype.card_fin]
  simp only [Fintype.card_bitVec, ← Nat.pow_add]

theorem fresh_inverse_first_domain_le (cache : Cache) (output : Block)
    (fresh : UnusedOutput cache.entries output) (length : cache.entries.length ≤ 2 ^ 121) :
    Pr{let answer ← @uniformSample _ (cache.inverseSampler output fresh)}[answer.val ∈ firstDomain] ≤
      (1 : ENNReal) / 2 ^ 167 := by
  have generic := inverse_fresh_event_le cache output fresh firstDomain (2 ^ 1432) first_domain_size
  have count : Fintype.card Block = 2 ^ 1600 := Fintype.card_bitVec 1600
  rw [count] at generic
  have remaining : 2 ^ 1599 ≤ (2 ^ 1600 : Nat) - cache.entries.length := by omega
  have reduced := generic.trans (ENNReal.div_le_div (le_refl _) (show (2 ^ 1599 : ENNReal) ≤
      ((2 ^ 1600 : Nat) - cache.entries.length : Nat) by exact_mod_cast remaining))
  simp only [Nat.cast_pow, Nat.cast_ofNat] at reduced
  exact reduced.trans_eq (by
    rw [show (2 : ENNReal) ^ 1599 = 2 ^ 167 * 2 ^ 1432 from pow_add (2 : ENNReal) 167 1432]
    simpa only [one_mul] using
      ENNReal.mul_div_mul_right (c := (2 : ENNReal) ^ 1432) 1 (2 ^ 167) (by positivity) (by finiteness))

def newInverseFirst (cache : Cache) (result : Block × Cache) : Prop :=
  cache.entries.length < result.2.entries.length ∧ result.1 ∈ firstDomain

theorem inverse_step_first_domain_le (cache : Cache) (output : Block)
    (length : cache.entries.length ≤ 2 ^ 121) :
    Pr{let result ← cache.inverse output}[newInverseFirst cache result] ≤ (1 : ENNReal) / 2 ^ 167 := by
  classical
  unfold PermutationCache.inverse
  split
  · rename_i fresh
    simp only [bind_pure_comp, prEvent_map, newInverseFirst,
      PermutationCache.extendInverse, List.length_cons, Nat.lt_succ_self, true_and]
    exact fresh_inverse_first_domain_le cache output fresh length
  · simp [newInverseFirst]

theorem inverse_replay_margin {q calls : Nat} (positive : 1 ≤ q) (small : q ≤ 2 ^ 120)
    (withReplay : calls ≤ q + 2 ^ 31) :
    (calls : ENNReal) / 2 ^ 167 ≤ (q : ENNReal) / 2 ^ 135 := by
  have count := (replay_budget_arithmetic positive small withReplay).1
  calc
    _ ≤ (2 ^ 32 * (q : ENNReal)) / 2 ^ 167 := ENNReal.div_le_div (by exact_mod_cast count) le_rfl
    _ = ((q : ENNReal) * 2 ^ 32) / (2 ^ 135 * 2 ^ 32) := by
      rw [mul_comm (2 ^ 32), ← pow_add]
    _ = _ := ENNReal.mul_div_mul_right (c := (2 : ENNReal) ^ 32) _ _ (by positivity) (by finiteness)

theorem forward_cache_growth (cache : Cache) (input : Block) (result : Block × Cache)
    (reaches : result ∈ support (cache.forward input)) : result.2.entries.length ≤ cache.entries.length + 1 := by
  unfold PermutationCache.forward at reaches
  split at reaches
  · obtain ⟨answer, _, identity⟩ := (mem_support_bind_iff _ _ _).mp reaches
    simp only [support_pure, Set.mem_singleton_iff] at identity
    subst result
    exact le_rfl
  · simp only [support_pure, Set.mem_singleton_iff] at reaches
    subst result
    change cache.entries.length ≤ cache.entries.length + 1
    omega

theorem inverse_cache_growth (cache : Cache) (input : Block) (result : Block × Cache)
    (reaches : result ∈ support (cache.inverse input)) : result.2.entries.length ≤ cache.entries.length + 1 := by
  unfold PermutationCache.inverse at reaches
  split at reaches
  · obtain ⟨answer, _, identity⟩ := (mem_support_bind_iff _ _ _).mp reaches
    simp only [support_pure, Set.mem_singleton_iff] at identity
    subst result
    exact le_rfl
  · simp only [support_pure, Set.mem_singleton_iff] at reaches
    subst result
    change cache.entries.length ≤ cache.entries.length + 1
    omega

def QueryBounded {α : Type} (program : OracleComp World α) (budget : Nat) : Prop :=
  IsQueryBound program budget (fun query left => Oracle.callCost query ≤ left)
    (fun query left => left - Oracle.callCost query)

noncomputable def scanInverse {α : Type} (compress : Compression) (program : OracleComp World α) :
    Cache → ProbComp Bool := by
  classical
  exact OracleComp.recOn program
    (fun _ _ => pure false)
    (fun query _ next cache => match query with
      | .inl coins => (liftM (unifSpec.query coins) : ProbComp _) >>= fun answer => next answer cache
      | .inr (.inl input) => next (compress input) cache
      | .inr (.inr (.inl input)) => cache.forward input >>= fun result => next result.1 result.2
      | .inr (.inr (.inr input)) => cache.inverse input >>= fun result =>
          if newInverseFirst cache result then pure true else next result.1 result.2)

/-- Every adaptive suffix, including one selected after any old valid transcript,
accumulates at most the number of remaining public calls times the fresh-event cost. -/
theorem scan_inverse_probability {α : Type} (compress : Compression) (program : OracleComp World α)
    (cache : Cache) (budget : Nat) (bounded : QueryBounded program budget)
    (room : cache.entries.length + budget ≤ 2 ^ 121) :
    Pr{let found ← scanInverse compress program cache}[found = true] ≤ (budget : ENNReal) / 2 ^ 167 := by
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
        scanInverse compress (next answer) cache)}[found = true] ≤ _
      exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun answer _ =>
        ih answer cache budget (by simpa only [Oracle.callCost, Nat.sub_zero] using bounded.2 answer) room
    · have positive : 1 ≤ budget := bounded.1
      have tailBound (answer : World.Range (.inr publicQuery)) := bounded.2 answer
      have smaller : ((budget - 1 : Nat) : ENNReal) / 2 ^ 167 ≤ (budget : ENNReal) / 2 ^ 167 := by
        exact ENNReal.div_le_div (by exact_mod_cast Nat.sub_le budget 1) le_rfl
      rcases publicQuery with input | permQuery
      · change Pr{let found ← scanInverse compress (next (compress input)) cache}[found = true] ≤ _
        have tail := ih (compress input) cache (budget - 1) (tailBound (compress input)) (by omega)
        exact tail.trans smaller
      · rcases permQuery with input | input
        · change Pr{let found ← (cache.forward input >>= fun result =>
            scanInverse compress (next result.1) result.2)}[found = true] ≤ _
          apply le_trans _ smaller
          apply prEvent_bind_le_of_forall_le_of_support
          intro result reached
          have growth := forward_cache_growth cache input result reached
          exact ih result.1 result.2 (budget - 1) (tailBound result.1) (by omega)
        · let nextRun : Block × Cache → ProbComp Bool := fun result =>
            if newInverseFirst cache result then pure true else scanInverse compress (next result.1) result.2
          change Pr{let found ← (cache.inverse input >>= nextRun)}[found = true] ≤ _
          have tails (result : Block × Cache) (reached : result ∈ support (cache.inverse input))
              (safe : ¬ newInverseFirst cache result) :
              Pr{let found ← nextRun result}[found = true] ≤ ((budget - 1 : Nat) : ENNReal) / 2 ^ 167 := by
            have growth := inverse_cache_growth cache input result reached
            simp only [nextRun, safe, ↓reduceIte]
            exact ih result.1 result.2 (budget - 1) (tailBound result.1) (by omega)
          have union := prEvent_bind_le_prEvent_add_of_support (cache.inverse input) nextRun
            (newInverseFirst cache) (fun found => found = true) tails
          refine union.trans ((add_le_add (inverse_step_first_domain_le cache input (by omega)) le_rfl).trans_eq ?_)
          rw [← ENNReal.add_div]
          congr 1
          exact_mod_cast (show 1 + (budget - 1) = budget by omega)

theorem scan_inverse_with_replay {α : Type} (compress : Compression) (program : OracleComp World α)
    (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31)
    (bounded : QueryBounded program calls) :
    Pr{let found ← scanInverse compress program (PermutationCache.empty Block)}[found = true] ≤
      (q : ENNReal) / 2 ^ 135 := by
  have maximum := (replay_budget_arithmetic positive small withReplay).2.2
  exact (scan_inverse_probability compress program (PermutationCache.empty Block) calls bounded (by simpa [PermutationCache.empty] using maximum)).trans
    (inverse_replay_margin positive small withReplay)

end TwoPermutationPrototype.Sampling
