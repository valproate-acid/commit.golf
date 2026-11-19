import CommitGolfCandidate.TaggedPinnedConditionalObserver
import CommitGolfCandidate.TwoPermutationQuadSpec
import CommitGolfCandidate.TwoPermutationBindingLeaf

/-! Facts about the quad domain `D2 = {x | low 576 bits of x are 0}` used by the quad hiding proof.

* Every quad node input `quadInput c` lies in `D2`; no hidden second-call input does (word 0 is the
  nonzero position tag).
* Programming hidden rows leaves `quadFunction` unchanged unless some programmed output has its
  preimage in `D2`.
* For a hidden-row output `y`, every cached row with output `y` has the row's own input, so the
  completion sampler puts the preimage of `y` into `D2` with probability at most `2^-575`. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2048
set_option linter.constructorNameAsVariable false

local instance quadRowsDiscrete {α : Type} : MeasurableSpace α := ⊤

def QuadDomain : Set Block := {x | x.extractLsb' 0 576 = 0}

theorem quad_input_mem (c : Fin 4 → BitVec 256) : quadInput c ∈ QuadDomain := by
  change (quadInput c).extractLsb' 0 576 = 0
  unfold quadInput
  exact BitVec.extractLsb'_append_eq_right

theorem quad_domain_word_zero {x : Block} (inside : x ∈ QuadDomain) : x.extractLsb' 0 64 = 0 := by
  change x.extractLsb' 0 576 = 0 at inside
  have sub : x.extractLsb' 0 64 = (x.extractLsb' 0 576).extractLsb' 0 64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro bit inside
    simp [inside]
  rw [sub, inside]
  rfl

theorem pinned_private_second_outside (i : Index) (reply : Block) (message : Words 32) (salt : BitVec 128) :
    pinnedPrivateSecond i reply message salt ∉ QuadDomain := by
  intro inside
  have zero := quad_domain_word_zero inside
  have word := packed_word (pinnedSecondInput i (saltWords salt) (replyWords reply) message) ⟨0, by decide⟩
  change (pinnedPrivateSecond i reply message salt).extractLsb' 0 64 = pinnedPositionTag i at word
  rw [zero] at word
  have bound : i.val < 2^24 := i.isLt
  have nat := congrArg BitVec.toNat word
  change (0#64).toNat = (BitVec.ofNat 64 (4152 + 256 * i.val)).toNat at nat
  have small : (4152 + 256 * i.val) % 2^64 = 4152 + 256 * i.val := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, small, Nat.zero_mod] at nat
  omega

theorem quad_function_program_rows (p : BiPermutation Block) (rows : List Row)
    (away : ∀ row ∈ rows, row.1 ∉ QuadDomain ∧ p.inverse row.2 ∉ QuadDomain) :
    quadFunction (p.programRows rows).forward = quadFunction p.forward := by
  funext c
  unfold quadFunction
  rw [p.program_rows_forward_unchanged rows (quadInput c) (fun row present => by
    have inside := quad_input_mem c
    refine ⟨fun same => (away row present).1 (same ▸ inside), fun same => (away row present).2 ?_⟩
    rw [← same, p.leftInverse]
    exact inside)]

def quadDomainBlock (v : BitVec 1024) : Block := v ++ 0#576

theorem quad_domain_size : QuadDomain.encard ≤ ((2 ^ 1024 : Nat) : ℕ∞) := by
  have range : QuadDomain ⊆ Set.range quadDomainBlock := by
    intro x inside
    change x.extractLsb' 0 576 = 0 at inside
    refine ⟨x.extractLsb' 576 1024, ?_⟩
    have joined : x.extractLsb' 576 1024 ++ x.extractLsb' 0 576 = x := BitVec.extractLsb'_append_extractLsb'
    rw [inside] at joined
    exact joined
  refine (Set.encard_le_encard range).trans ?_
  rw [← Set.image_univ]
  refine (Set.encard_image_le _ Set.univ).trans_eq ?_
  rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_bitVec]

private theorem fresh_inverse_quad_le (cache : Cache) (output : Block)
    (fresh : UnusedOutput cache.entries output) (length : cache.entries.length ≤ 2 ^ 121) :
    Pr{let answer ← @uniformSample _ (cache.inverseSampler output fresh)}[answer.val ∈ QuadDomain] ≤
      (1 : ENNReal) / 2 ^ 575 := by
  have generic := inverse_fresh_event_le cache output fresh QuadDomain (2 ^ 1024) quad_domain_size
  have count : Fintype.card Block = 2 ^ 1600 := Fintype.card_bitVec 1600
  rw [count] at generic
  have remaining : 2 ^ 1599 ≤ (2 ^ 1600 : Nat) - cache.entries.length := by omega
  have reduced := generic.trans (ENNReal.div_le_div (le_refl _) (show (2 ^ 1599 : ENNReal) ≤
      ((2 ^ 1600 : Nat) - cache.entries.length : Nat) by exact_mod_cast remaining))
  simp only [Nat.cast_pow, Nat.cast_ofNat] at reduced
  exact reduced.trans_eq (by
    rw [show (2 : ENNReal) ^ 1599 = 2 ^ 575 * 2 ^ 1024 from pow_add (2 : ENNReal) 575 1024]
    simpa only [one_mul] using
      ENNReal.mul_div_mul_right (c := (2 : ENNReal) ^ 1024) 1 (2 ^ 575) (by positivity) (by finiteness))

/-- The completion sampler maps a target into `D2` rarely, unless a cached row already does. -/
theorem sample_inverse_quad_le (cache : Cache) (output : Block) (length : cache.entries.length ≤ 2 ^ 121)
    (safe : ∀ entry ∈ cache.entries, entry.2 = output → entry.1 ∉ QuadDomain) :
    Pr{let p ← cache.sample}[p.val.inverse output ∈ QuadDomain] ≤ (1 : ENNReal) / 2 ^ 575 := by
  classical
  by_cases fresh : UnusedOutput cache.entries output
  · have step := cache.inverse_step_eq output (fun answer _ => (pure answer : ProbComp Block))
    have drop : (do let p ← cache.sample; (pure (p.val.inverse output) : ProbComp Block)) =ᵈ
        (Subtype.val <$> @uniformSample _ (cache.inverseSampler output fresh)) := by
      refine step.trans ?_
      unfold PermutationCache.inverse
      rw [dite_eq_left fresh]
      simp only [bind_assoc, pure_bind, map_eq_bind_pure_comp]
      apply EvalDistEq.bind_right
      intro answer
      exact EvalDistEq.bind_const _ _
    have left : Pr{let p ← cache.sample}[p.val.inverse output ∈ QuadDomain] =
        Pr{let answer ← (do let p ← cache.sample; (pure (p.val.inverse output) : ProbComp Block))}[
          answer ∈ QuadDomain] := by
      rw [bind_pure_comp, prEvent_map]
    rw [left, drop.prEvent_eq, prEvent_map]
    exact fresh_inverse_quad_le cache output fresh length
  · have found : ∃ entry ∈ cache.entries, entry.2 = output := by
      by_contra missing
      exact fresh (fun entry present same => missing ⟨entry, present, same⟩)
    obtain ⟨entry, present, same⟩ := found
    have never : Pr{let p ← cache.sample}[p.val.inverse output ∈ QuadDomain] = 0 := by
      apply (prEvent_eq_zero_iff _ _).2
      intro p _ inside
      have agrees := p.property entry present
      have back : p.val.inverse output = entry.1 := by
        rw [← same, ← agrees, p.val.leftInverse]
      exact safe entry present same (back ▸ inside)
    rw [never]
    exact zero_le

variable {I : Type} [Fintype I]

theorem pinned_high_run_keeps_added {base : Cache} (cache : PinnedHighCache base) (slot : Nat)
    (answers : List (BitVec 1344)) (plans : List PinnedHighPlan)
    (result : List (BitVec 1344) × PinnedHighCache base)
    (possible : result ∈ support (runPinnedHigh cache slot answers plans)) :
    ∀ row ∈ cache.added, row ∈ result.2.added := by
  induction plans generalizing cache slot answers result with
  | nil =>
    simp only [runPinnedHigh, support_pure, Set.mem_singleton_iff] at possible
    subst result
    exact fun _ present => present
  | cons plan rest ih =>
    simp only [runPinnedHigh] at possible
    obtain ⟨⟨answer, middle⟩, head, tail⟩ := (mem_support_bind_iff _ _ _).mp possible
    have later := ih middle (slot + 1) (answer :: answers) result tail
    intro row present
    apply later
    rcases pinned_high_step_support cache slot (plan answers) (answer, middle) head with same | ⟨_, _, _, _, grows⟩
    · change middle.added = cache.added at same
      rw [same]
      exact present
    · change middle.added = _ at grows
      rw [grows]
      exact List.mem_cons_of_mem _ present

/-- Every cached row with the same output as a hidden row is that hidden row's own input. -/
theorem pinned_hidden_rows_output_safe [DecidableEq I] {base : Cache} (cache : PinnedHighCache base) (slot : Nat)
    (valid : cache.Valid slot) (position : I → Index) (first : I → Block) (message : I → Words 32)
    (digests : I → BitVec 256) (room : cache.zero.entries.length + Fintype.card I ≤ 2^121)
    (rows : List Row) (reached : rows ∈ support (samplePinnedHiddenRows cache slot position first message digests))
    (low : PinnedLowTape) :
    ∀ row ∈ rows, row.1 ∉ QuadDomain ∧
      ∀ entry ∈ (cache.realize low).entries, entry.2 = row.2 → entry.1 ∉ QuadDomain := by
  classical
  unfold samplePinnedHiddenRows at reached
  obtain ⟨nonce, _, rest⟩ := (mem_support_bind_iff _ _ _).mp reached
  let addresses := pinnedNonceAddresses position first message nonce
  by_cases new : ∀ input ∈ addresses, UnusedInput base.entries input
  · rw [ite_eq_left new] at rest
    obtain ⟨final, finalReached, made⟩ := (mem_support_bind_iff _ _ _).mp rest
    simp only [support_pure, Set.mem_singleton_iff] at made
    subst rows
    have fact := pinned_high_const_support cache slot [] addresses valid
      (by simpa only [addresses, pinned_nonce_addresses_length] using room) final finalReached
    have keeps := pinned_high_run_keeps_added cache slot [] (pinnedConstantPlans addresses) final finalReached
    intro row present
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp present
    let b := pinnedPrivateSecond (position i) (first i) (message i) (nonce i)
    have outside : b ∉ QuadDomain := pinned_private_second_outside _ _ _ _
    refine ⟨outside, ?_⟩
    have here : b ∈ addresses := List.mem_map.mpr ⟨i, by simp, rfl⟩
    obtain ⟨stored, appears, equal⟩ := pinned_row_from_covers final.2 b (fact.2.2.2 b here) (new _ here)
    have top := pinned_high_cached_upper_of_row final.2 stored appears
    rw [equal] at top
    intro entry located same
    change entry ∈ pinnedHighTable base cache.added low at located
    change entry.2 = pinnedCachedUpper final.2.zero b ++ digests i at same
    rw [top] at same
    have tails : pinnedOutputTail entry.2 = stored.upper := by
      rw [same]
      exact BitVec.extractLsb'_append_eq_left
    rcases List.mem_append.mp located with recent | original
    · obtain ⟨older, olderIn, rfl⟩ := List.mem_map.mp recent
      have olderTail : older.upper = stored.upper := (pinned_high_row_tail older low).symm.trans tails
      have identical := pinned_unique_mapped_key PinnedHighRow.upper fact.1.tailUnique (keeps older olderIn)
        appears olderTail
      change older.input ∉ QuadDomain
      rw [identical, equal]
      exact outside
    · have unused := fact.1.chooserTail stored appears
      exact (unused (by rw [← tails]; exact List.mem_map_of_mem original)).elim
  · rw [ite_eq_right new] at rest
    simp only [support_pure, Set.mem_singleton_iff] at rest
    subst rows
    simp

end TwoPermutationPrototype.Sampling
