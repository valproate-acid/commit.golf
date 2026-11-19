import CommitGolfCandidate.TaggedPinnedHighRun

namespace TwoPermutationPrototype.Sampling
open OracleComp

set_option maxRecDepth 8192

noncomputable local instance pinnedOpenedLowSampler {I : Type} [Fintype I] :
    SampleableType (I → BitVec 256) := by
  classical
  exact SampleableType.ofFintype _

local instance pinnedOpenedLowDiscrete {α : Type} : MeasurableSpace α := ⊤

theorem pinned_fin_lows_equivalence {α : Type} (count : Nat) (next : List (BitVec 256) → ProbComp α) :
    (do let lows ← $ᵗ (Fin count → BitVec 256); next (List.ofFn lows)) =ᵈ
      (samplePinnedLows count >>= next) := by
  induction count generalizing next with
  | zero =>
    simp only [List.ofFn_zero, samplePinnedLows, pure_bind]
    exact EvalDistEq.of_evalDist_eq (evalDist_bind_const _ _)
  | succ count ih =>
    let vec := Fin.consEquiv (fun _ : Fin (count + 1) => BitVec 256)
    apply (uniform_transport_bind (transportOfEquiv vec.symm)
      (fun lows => next (List.ofFn lows))).trans
    rw [SampleableType.uniformSample_prod_eq_bind, samplePinnedLows]
    simp only [bind_assoc, pure_bind]
    apply EvalDistEq.bind_right
    intro head
    change (do let rest ← $ᵗ (Fin count → BitVec 256)
               next (List.ofFn (Fin.cons head rest))) =ᵈ _
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
    exact ih (fun tail => next (head :: tail))

theorem pinned_low_draw_length {count : Nat} {draws : List (BitVec 256)}
    (reached : draws ∈ support (samplePinnedLows count)) : draws.length = count := by
  induction count generalizing draws with
  | zero =>
    simp only [samplePinnedLows, support_pure, Set.mem_singleton_iff] at reached
    subst draws
    rfl
  | succ count ih =>
    simp only [samplePinnedLows, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
    obtain ⟨head, _, tail, possible, rfl⟩ := reached
    simp only [List.length_cons, ih possible]

theorem pinned_lows_sum (left right : Nat) :
    samplePinnedLows (left+right) = (do
      let head ← samplePinnedLows left
      let tail ← samplePinnedLows right
      pure (head ++ tail)) := by
  induction left with
  | zero => simp [samplePinnedLows]
  | succ left ih =>
    rw [Nat.succ_add, samplePinnedLows, ih]
    simp only [samplePinnedLows, bind_assoc, pure_bind, List.cons_append]

theorem pinned_place_low_append (old : PinnedLowTape) (slot : Nat) (left right : List (BitVec 256)) :
    pinnedPlaceLows old slot (left ++ right) =
    pinnedPlaceLows (pinnedPlaceLows old slot left) (slot+left.length) right := by
  induction left generalizing old slot with
  | nil => simp [pinnedPlaceLows]
  | cons head rest ih =>
    simp only [List.cons_append, pinnedPlaceLows, List.length_cons]
    rw [ih, show slot + (rest.length+1) = (slot+1)+rest.length by omega]

theorem pinned_place_below (low : PinnedLowTape) (step : Nat) (draws : List (BitVec 256))
    (slot : Nat) (earlier : slot < step) : pinnedPlaceLows low step draws slot = low slot := by
  induction draws generalizing low step with
  | nil => rfl
  | cons draw rest ih =>
    change pinnedPlaceLows (Function.update low step draw) (step+1) rest slot = _
    rw [ih _ _ (by omega), Function.update_of_ne (by omega)]

theorem pinned_place_fin (low : PinnedLowTape) (step : Nat) {count : Nat} (draws : Fin count → BitVec 256)
    (i : Fin count) : pinnedPlaceLows low step (List.ofFn draws) (step + i.val) = draws i := by
  induction count generalizing step low with
  | zero => exact Fin.elim0 i
  | succ count ih =>
    refine Fin.cases ?_ (fun prior => ?_) i
    · simp only [List.ofFn_succ, Fin.val_zero, Nat.add_zero, pinnedPlaceLows]
      rw [pinned_place_below _ _ _ _ (Nat.lt_succ_self _), Function.update_self]
    · simp only [List.ofFn_succ, pinnedPlaceLows, Fin.val_succ]
      rw [show step + (prior.val + 1) = (step+1) + prior.val by omega]
      exact ih (Function.update low step (draws 0)) (step+1) _ prior

def pinnedFinLowTape {count : Nat} (draws : Fin count → BitVec 256) : PinnedLowTape :=
  fun i => if room : i < count then draws ⟨i, room⟩ else 0

theorem pinned_realize_fin_lows {base : Cache} (state : PinnedHighCache base) {count : Nat}
    (slots : ∀ row ∈ state.added, row.slot < count) (draws : Fin count → BitVec 256) :
    state.realize (pinnedPlaceLows (fun _ => 0) 0 (List.ofFn draws)) = state.realize (pinnedFinLowTape draws) := by
  apply state.same_realization
  intro row seen
  have n := pinned_place_fin (fun _ => 0) 0 draws ⟨row.slot, slots row seen⟩
  simpa [pinnedFinLowTape, slots row seen] using n

structure PinnedOpenedState (base : Cache) (count : Nat) where
  high : PinnedHighCache base
  slots : ∀ row ∈ high.added, row.slot < count
  opened : List Block
  present : ∀ address ∈ opened, ¬ UnusedInput high.zero.entries address

def PinnedOpenedState.isRevealed {base : Cache} {count : Nat}
    (state : PinnedOpenedState base count) (slot : Fin count) : Prop :=
  ∃ row ∈ state.high.added, row.slot = slot.val ∧ row.input ∈ state.opened

noncomputable def PinnedOpenedState.merge {base : Cache} {count : Nat} (state : PinnedOpenedState base count)
    [DecidablePred state.isRevealed]
    (visible : {i : Fin count // state.isRevealed i} → BitVec 256)
    (privateLow : {i : Fin count // ¬ state.isRevealed i} → BitVec 256) : Fin count → BitVec 256 :=
  fun i => if revealed : state.isRevealed i then visible ⟨i, revealed⟩ else privateLow ⟨i, revealed⟩

theorem pinned_opened_reply_only_revealed {base : Cache} {count : Nat} (state : PinnedOpenedState base count)
    (left right : Fin count → BitVec 256)
    (same : ∀ i, state.isRevealed i → left i = right i)
    (address : Block) (opened : address ∈ state.opened) :
    (state.high.realize (pinnedFinLowTape left)).example.val.forward address =
      (state.high.realize (pinnedFinLowTape right)).example.val.forward address := by
  classical
  have existsRow : ∃ row ∈ state.high.zero.entries, row.1 = address := by
    by_contra missing
    exact state.present address opened (fun row included equal => missing ⟨row, included, equal⟩)
  obtain ⟨row, present, eq⟩ := existsRow
  change row ∈ pinnedHighTable base state.high.added (fun _ => 0) at present
  rcases List.mem_append.mp present with added | initial
  · obtain ⟨stored, included, rfl⟩ := List.mem_map.mp added
    change stored.input = address at eq
    have seen : state.isRevealed ⟨stored.slot, state.slots stored included⟩ :=
      ⟨stored, included, rfl, eq.symm ▸ opened⟩
    have lowWords : pinnedFinLowTape left stored.slot = pinnedFinLowTape right stored.slot := by
      simpa only [pinnedFinLowTape, state.slots stored included, dite_true] using
        same ⟨stored.slot, state.slots stored included⟩ seen
    have a := (state.high.realize (pinnedFinLowTape left)).example.property
      (stored.realize (pinnedFinLowTape left)) (List.mem_append_left _ (List.mem_map_of_mem included))
    have b := (state.high.realize (pinnedFinLowTape right)).example.property
      (stored.realize (pinnedFinLowTape right)) (List.mem_append_left _ (List.mem_map_of_mem included))
    change (state.high.realize (pinnedFinLowTape left)).example.val.forward stored.input = _ at a
    change (state.high.realize (pinnedFinLowTape right)).example.val.forward stored.input = _ at b
    rw [← eq, a, b, PinnedHighRow.realize, PinnedHighRow.realize, lowWords]
  · have a := (state.high.realize (pinnedFinLowTape left)).example.property row (List.mem_append_right _ initial)
    have b := (state.high.realize (pinnedFinLowTape right)).example.property row (List.mem_append_right _ initial)
    rw [← eq, a, b]

/-- For a fixed common high history, the exact lows of opened B rows are the
only fresh low coordinates needed to read all opened replies. -/
theorem pinned_opened_lows_equivalence {α : Type} {base : Cache} {count : Nat}
    (state : PinnedOpenedState base count) [DecidablePred state.isRevealed] (next : Cache → ProbComp α) :
    (samplePinnedLows count >>= fun draws =>
      next (state.high.realize (pinnedPlaceLows (fun _ => 0) 0 draws))) =ᵈ
    (do let opened ← $ᵗ ({i : Fin count // state.isRevealed i} → BitVec 256)
        let unopened ← $ᵗ ({i : Fin count // ¬state.isRevealed i} → BitVec 256)
        next (state.high.realize (pinnedFinLowTape (state.merge opened unopened)))) := by
  classical
  apply (pinned_fin_lows_equivalence count
    (fun draws => next (state.high.realize (pinnedPlaceLows (fun _ => 0) 0 draws)))).symm.trans
  trans (($ᵗ (Fin count → BitVec 256)) >>= fun draws => next (state.high.realize (pinnedFinLowTape draws)))
  · apply EvalDistEq.bind_right
    intro draws
    rw [pinned_realize_fin_lows state.high state.slots]
  · let finish := fun draws : Fin count → BitVec 256 => next (state.high.realize (pinnedFinLowTape draws))
    trans ((@uniformSample _ (@pinnedLowFunctionSampler (Fin count) inferInstance)) >>= finish)
    · have same := @SampleableType.map_uniformSample_evalDistEq_of_bijective
        (Fin count → BitVec 256) (Fin count → BitVec 256) inferInstance
        (@pinnedLowFunctionSampler (Fin count) inferInstance) id Function.bijective_id
      simpa using same.bind_left finish
    · exact pinned_split_revealed_lows state.isRevealed finish

end TwoPermutationPrototype.Sampling
