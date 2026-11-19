import CommitGolfCandidate.TwoPermutationHidingProgramming
import CommitGolfCandidate.TwoPermutationHidingMargin

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp MeasureTheory
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

@[instance_reducible] private noncomputable def pinnedSampleFrom {α : Type} [Finite α] (inhabited : Nonempty α) :
    SampleableType α := by
  letI : Nonempty α := inhabited
  letI : Fintype α := Fintype.ofFinite α
  exact SampleableType.ofFintype α

def pinnedOutputTail (answer : Block) : BitVec 1344 := answer.extractLsb' 256 1344

def pinnedOutputDigest (answer : Block) : BitVec 256 := answer.extractLsb' 0 256

def pinnedUnusedTail (known : List (BitVec 1344)) (tail : BitVec 1344) : Prop := tail ∉ known

abbrev PinnedUnusedTails (known : List (BitVec 1344)) := {tail : BitVec 1344 // pinnedUnusedTail known tail}

noncomputable def samplePinnedUnusedTails (known : List (BitVec 1344))
    (present : Nonempty (PinnedUnusedTails known)) : ProbComp (PinnedUnusedTails known) :=
  @uniformSample _ (pinnedSampleFrom present)

private def pinnedUnusedTailsEquiv (known : List (BitVec 1344)) :
    PinnedUnusedTails known ≃ RemainingOutputs (known.map fun tail => (tail, tail)) :=
  Equiv.subtypeEquivRight fun tail => by
    constructor
    · intro unused row possible equal
      obtain ⟨old, inKnown, rfl⟩ := List.mem_map.mp possible
      exact unused (equal ▸ inKnown)
    · intro unused possible
      exact unused (tail, tail) (List.mem_map_of_mem possible) rfl

theorem pinned_unused_tail_count (known : List (BitVec 1344)) [Fintype (PinnedUnusedTails known)] :
    2^1344 - known.length ≤ Fintype.card (PinnedUnusedTails known) := by
  classical
  let : Fintype (RemainingOutputs (known.map fun tail => (tail, tail))) := Fintype.ofFinite _
  rw [Fintype.card_congr (pinnedUnusedTailsEquiv known)]
  simpa only [Fintype.card_bitVec, List.length_map] using
    remaining_output_count (α := BitVec 1344) (known.map fun tail => (tail, tail))

theorem pinned_unused_tail_guess_le (known : List (BitVec 1344)) (room : known.length ≤ 2^121)
    (anchor : PinnedUnusedTails known) (guess : BitVec 1344) :
    Pr{let tail ← @uniformSample _ (pinnedSampleFrom ⟨anchor⟩)}[tail.val = guess] ≤ (1 : ENNReal)/2^1343 := by
  let : SampleableType (PinnedUnusedTails known) := pinnedSampleFrom ⟨anchor⟩
  let : Fintype (PinnedUnusedTails known) := Fintype.ofFinite _
  let : MeasurableSpace (PinnedUnusedTails known) := ⊤
  let event : Set (PinnedUnusedTails known) := {tail | tail.val = guess}
  have count : event.encard ≤ (1 : ℕ∞) := by
    by_cases hit : ∃ tail : PinnedUnusedTails known, tail.val = guess
    · obtain ⟨one, fits⟩ := hit
      have subset : event ⊆ {one} := fun tail (equal : tail.val = guess) =>
        Set.mem_singleton_iff.mpr (Subtype.ext (equal.trans fits.symm))
      exact (Set.encard_mono subset).trans (by simp)
    · have empty : event = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr (fun tail found => hit ⟨tail, found⟩)
      simp [empty]
  have enough : 2^1343 ≤ Fintype.card (PinnedUnusedTails known) :=
    (by omega : 2^1343 ≤ 2^1344 - known.length).trans (pinned_unused_tail_count known)
  have chance := SampleableType.evalDist_uniformSample_le_of_encard_le event 1 count
  rw [prEvent_eq_evalDist_of_discrete]
  refine chance.trans ?_
  simp only [Nat.cast_one]
  apply ENNReal.div_le_div le_rfl
  exact_mod_cast enough

theorem pinned_sample_tail_guess_le (known : List (BitVec 1344)) (room : known.length ≤ 2^121)
    (present : Nonempty (PinnedUnusedTails known)) (guess : BitVec 1344) :
    Pr{let tail ← samplePinnedUnusedTails known present}[tail.val = guess] ≤ (1 : ENNReal)/2^1343 := by
  classical
  exact pinned_unused_tail_guess_le known room (Classical.choice present) guess

def pinnedTailSplit (known : List (BitVec 1344)) :
    Transport {answer : Block // pinnedUnusedTail known (pinnedOutputTail answer)}
      ({upper : BitVec 1344 // pinnedUnusedTail known upper} × BitVec 256) where
  toFun answer := (⟨pinnedOutputTail answer.val, answer.property⟩, pinnedOutputDigest answer.val)
  invFun pair := ⟨pair.1.val ++ pair.2, by
    have tail : pinnedOutputTail (pair.1.val ++ pair.2) = pair.1.val :=
      BitVec.extractLsb'_append_eq_left
    exact tail.symm ▸ pair.1.property⟩
  leftInverse answer := by
    apply Subtype.ext
    exact BitVec.extractLsb'_append_extractLsb'
  rightInverse pair := by
    apply Prod.ext
    · apply Subtype.ext
      exact BitVec.extractLsb'_append_eq_left
    · exact BitVec.extractLsb'_append_eq_right

/-- Excluding occupied high tails leaves the low digest bits independent. -/
theorem pinned_tail_sample_split {α : Type} (known : List (BitVec 1344))
    (anchor : {upper : BitVec 1344 // pinnedUnusedTail known upper}) (next : Block → ProbComp α) :
    (do let answer ← @uniformSample _ (pinnedSampleFrom ⟨(pinnedTailSplit known).invFun (anchor, 0)⟩)
        next answer.val) =ᵈ
    (do let tail ← @uniformSample _ (pinnedSampleFrom ⟨anchor⟩)
        let digest ← $ᵗ BitVec 256
        next (tail.val ++ digest)) := by
  let : SampleableType {answer : Block // pinnedUnusedTail known (pinnedOutputTail answer)} :=
    pinnedSampleFrom ⟨(pinnedTailSplit known).invFun (anchor, 0)⟩
  let : SampleableType {upper : BitVec 1344 // pinnedUnusedTail known upper} := pinnedSampleFrom ⟨anchor⟩
  apply (uniform_transport_bind (pinnedTailSplit known) (fun answer => next answer.val)).trans
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  rfl

theorem pinned_fresh_tail_hit_le (cache : Cache) (input : Block)
    (fresh : UnusedInput cache.entries input) (room : cache.entries.length ≤ 2 ^ 121)
    (known : List (BitVec 1344)) :
    Pr{let answer ← @uniformSample _ (cache.forwardSampler input fresh)}[pinnedOutputTail answer.val ∈ known] ≤
      (known.length : ENNReal)/2^1343 := by
  let sample := @uniformSample _ (cache.forwardSampler input fresh)
  refine (prEvent_mono sample (p := fun answer => pinnedOutputTail answer.val ∈ known)
    (q := fun answer => ∃ tail ∈ known, pinnedOutputTail answer.val = tail)
    (fun answer hit => ⟨pinnedOutputTail answer.val, hit, rfl⟩)).trans ?_
  simpa only [mul_one_div] using prEvent_list_le known sample
    (fun tail answer => pinnedOutputTail answer.val = tail) (1/2^1343) (fun tail _ =>
      fresh_forward_slice_le cache input fresh (low := 256) (width := 1344) (high := 0)
        (by decide) (by decide) room tail)

theorem pinned_unused_tail_unused_output (cache : Cache) (block : Block)
    (unused : pinnedUnusedTail (cache.entries.map (pinnedOutputTail ∘ Prod.snd)) (pinnedOutputTail block)) :
    UnusedOutput cache.entries block := by
  intro row present same
  apply unused
  exact List.mem_map.mpr ⟨row, present, congrArg pinnedOutputTail same⟩

local instance pinnedTailDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

theorem pinned_restrict_fresh_tail_distance {α : Type} (cache : Cache) (input : Block)
    (fresh : UnusedInput cache.entries input) (room : cache.entries.length ≤ 2 ^ 121)
    (anchor : Block)
    (unused : pinnedUnusedTail (cache.entries.map (pinnedOutputTail ∘ Prod.snd)) (pinnedOutputTail anchor))
    (next : RemainingOutputs cache.entries → ProbComp α) :
    let good (answer : RemainingOutputs cache.entries) :=
      pinnedUnusedTail (cache.entries.map (pinnedOutputTail ∘ Prod.snd)) (pinnedOutputTail answer.val)
    measureTVDist
      (do let draw ← @uniformSample _ (pinnedSampleFrom
            ⟨(⟨⟨anchor, pinned_unused_tail_unused_output cache anchor unused⟩, unused⟩ : Subtype good)⟩)
          next draw.val)
      (do let draw ← @uniformSample _ (cache.forwardSampler input fresh)
          next draw) ≤ ((cache.entries.length : ENNReal)/2^1343).toReal := by
  classical
  intro good
  let : SampleableType (RemainingOutputs cache.entries) := cache.forwardSampler input fresh
  let : SampleableType (Subtype good) := pinnedSampleFrom
    ⟨⟨⟨anchor, pinned_unused_tail_unused_output cache anchor unused⟩, unused⟩⟩
  refine (repair_uniform_distance good (fun draw => next draw.val) next (fun _ _ => by rfl)).trans ?_
  apply ENNReal.toReal_mono (by finiteness)
  simpa only [good, pinnedUnusedTail, not_not, List.length_map] using
    pinned_fresh_tail_hit_le cache input fresh room (cache.entries.map (pinnedOutputTail ∘ Prod.snd))

def pinnedCachedTails (cache : Cache) : List (BitVec 1344) :=
  cache.entries.map (pinnedOutputTail ∘ Prod.snd)

def pinnedAdmitted (cache : Cache) (reply : RemainingOutputs cache.entries) : Prop :=
  pinnedUnusedTail (pinnedCachedTails cache) (pinnedOutputTail reply.val)

private def pinnedAdmittedTransport (cache : Cache) :
    Transport (Subtype (pinnedAdmitted cache))
      {reply : Block // pinnedUnusedTail (pinnedCachedTails cache) (pinnedOutputTail reply)} where
  toFun reply := ⟨reply.val.val, reply.property⟩
  invFun reply := ⟨⟨reply.val, pinned_unused_tail_unused_output cache reply.val reply.property⟩, reply.property⟩
  leftInverse _ := rfl
  rightInverse _ := rfl

theorem pinned_admitted_split {α : Type} (cache : Cache) (anchor : Subtype (pinnedAdmitted cache))
    (next : RemainingOutputs cache.entries → ProbComp α) :
    (do let value ← @uniformSample _ (pinnedSampleFrom ⟨anchor⟩)
        next value.val) =ᵈ
    (do let tail ← @uniformSample _ (pinnedSampleFrom
          ⟨(⟨pinnedOutputTail anchor.val.val, anchor.property⟩ : PinnedUnusedTails (pinnedCachedTails cache))⟩)
        let low ← $ᵗ BitVec 256
        let reply : Block := tail.val ++ low
        have notKnown : pinnedUnusedTail (pinnedCachedTails cache) (pinnedOutputTail reply) := by
          have chunk : pinnedOutputTail reply = tail.val := BitVec.extractLsb'_append_eq_left
          exact chunk.symm ▸ tail.property
        next ⟨reply, pinned_unused_tail_unused_output cache reply notKnown⟩) := by
  let : SampleableType (Subtype (pinnedAdmitted cache)) := pinnedSampleFrom ⟨anchor⟩
  let upper : PinnedUnusedTails (pinnedCachedTails cache) := ⟨pinnedOutputTail anchor.val.val, anchor.property⟩
  let : SampleableType (PinnedUnusedTails (pinnedCachedTails cache)) := pinnedSampleFrom ⟨upper⟩
  let layout := (pinnedAdmittedTransport cache).trans (pinnedTailSplit (pinnedCachedTails cache))
  apply (uniform_transport_bind layout (fun reply => next reply.val)).trans
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  rfl

theorem pinned_admitted_nonempty (cache : Cache) (room : cache.entries.length ≤ 2^121) :
    Nonempty (Subtype (pinnedAdmitted cache)) := by
  classical
  let : Fintype (PinnedUnusedTails (pinnedCachedTails cache)) := Fintype.ofFinite _
  have bound : 0 < 2^1344 - (pinnedCachedTails cache).length := by
    simp only [pinnedCachedTails, List.length_map]
    omega
  obtain ⟨tail⟩ := Fintype.card_pos_iff.mp (bound.trans_le (pinned_unused_tail_count (pinnedCachedTails cache)))
  let block : Block := tail.val ++ (0 : BitVec 256)
  have eq : pinnedOutputTail block = tail.val := BitVec.extractLsb'_append_eq_left
  have allowed : pinnedUnusedTail (pinnedCachedTails cache) (pinnedOutputTail block) := eq.symm ▸ tail.property
  exact ⟨⟨⟨block, pinned_unused_tail_unused_output cache block allowed⟩, allowed⟩⟩

theorem pinned_current_tails_nonempty (cache : Cache) (room : cache.entries.length ≤ 2^121) :
    Nonempty (PinnedUnusedTails (pinnedCachedTails cache)) := by
  obtain ⟨value⟩ := pinned_admitted_nonempty cache room
  exact ⟨⟨pinnedOutputTail value.val.val, value.property⟩⟩

noncomputable def pinnedRestrictedForward (cache : Cache) (input : Block) : ProbComp (Block × Cache) := by
  classical
  exact if fresh : UnusedInput cache.entries input then
    if allowed : Nonempty (Subtype (pinnedAdmitted cache)) then do
      let answer ← @uniformSample _ (pinnedSampleFrom allowed)
      pure (answer.val.val, cache.extendForward input fresh answer.val)
    else cache.forward input
  else cache.forward input

theorem pinned_restricted_forward_fresh_eq {α : Type} (cache : Cache) (input : Block)
    (fresh : UnusedInput cache.entries input) (room : cache.entries.length ≤ 2^121)
    (next : Block × Cache → ProbComp α) :
    (pinnedRestrictedForward cache input >>= next) =ᵈ
      (do let tail ← samplePinnedUnusedTails (pinnedCachedTails cache) (pinned_current_tails_nonempty cache room)
          let low ← $ᵗ BitVec 256
          let value : Block := tail.val ++ low
          have unused : pinnedUnusedTail (pinnedCachedTails cache) (pinnedOutputTail value) := by
            have eq : pinnedOutputTail value = tail.val := BitVec.extractLsb'_append_eq_left
            exact eq.symm ▸ tail.property
          let reply : RemainingOutputs cache.entries :=
            ⟨value, pinned_unused_tail_unused_output cache value unused⟩
          next (value, cache.extendForward input fresh reply)) := by
  classical
  let anchor := Classical.choice (pinned_admitted_nonempty cache room)
  simp only [pinnedRestrictedForward, fresh, pinned_admitted_nonempty cache room, dite_true, bind_assoc, pure_bind]
  exact pinned_admitted_split cache anchor (fun reply => next (reply.val, cache.extendForward input fresh reply))

theorem pinned_restricted_forward_distance {α : Type} (cache : Cache) (input : Block)
    (room : cache.entries.length ≤ 2^121) (next : Block × Cache → ProbComp α) :
    measureTVDist (pinnedRestrictedForward cache input >>= next) (cache.forward input >>= next) ≤
      (cache.entries.length : ℝ)/2^1343 := by
  classical
  by_cases fresh : UnusedInput cache.entries input
  · let anchor := Classical.choice (pinned_admitted_nonempty cache room)
    have allowed : Nonempty (Subtype (pinnedAdmitted cache)) := ⟨anchor⟩
    let resume (reply : RemainingOutputs cache.entries) : ProbComp α :=
      next (reply.val, cache.extendForward input fresh reply)
    have step := pinned_restrict_fresh_tail_distance cache input fresh room anchor.val.val anchor.property resume
    unfold pinnedRestrictedForward PermutationCache.forward
    simp only [fresh, allowed, dite_true, bind_assoc, pure_bind]
    simp only [resume, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at step
    exact step
  · unfold pinnedRestrictedForward
    simp only [fresh, dite_false, measureTVDist_self]
    positivity

def swapCachedOutputRows {β : Type} [DecidableEq β] (rows : List (β × β)) (old new : β) :
    List (β × β) :=
  rows.map fun row => (row.1, swap old new row.2)

def swapCachedOutputsTransport {β : Type} [DecidableEq β] (rows : List (β × β)) (old new : β) :
    Transport (Completion rows) (Completion (swapCachedOutputRows rows old new)) where
  toFun p := ⟨p.val.swapOutputs old new, by
    intro row present
    obtain ⟨before, belongs, rfl⟩ := List.mem_map.mp present
    exact congrArg (swap old new) (p.property before belongs)⟩
  invFun p := ⟨p.val.swapOutputs old new, by
    intro row present
    have updated := p.property _ (List.mem_map_of_mem
      (f := fun pair : β × β => (pair.1, swap old new pair.2)) present)
    change swap old new (p.val.forward row.1) = row.2
    exact (congrArg (swap old new) updated).trans (swap_involution old new row.2)⟩
  leftInverse p := Subtype.ext (p.val.swapOutputs_twice old new)
  rightInverse p := Subtype.ext (p.val.swapOutputs_twice old new)

noncomputable def swapCachedOutputs {β : Type} [DecidableEq β]
    (cache : PermutationCache β) (old new : β) : PermutationCache β :=
  ⟨swapCachedOutputRows cache.entries old new,
    ⟨(swapCachedOutputsTransport cache.entries old new).toFun cache.example⟩⟩

/-- A transposition transports the uniform completion when a known row is
replaced. The target table is exact even if the outputs coincide. -/
theorem pinned_uniform_swap_cached_outputs {α β : Type} [Fintype β] [DecidableEq β]
    (cache : PermutationCache β) (old new : β) (next : BiPermutation β → ProbComp α) :
    (do let p ← cache.sample; next (p.val.swapOutputs old new)) =ᵈ
      (do let p ← (swapCachedOutputs cache old new).sample; next p.val) := by
  let : SampleableType (Completion cache.entries) := cache.completionSampler
  let : SampleableType (Completion (swapCachedOutputRows cache.entries old new)) :=
    (swapCachedOutputs cache old new).completionSampler
  have transported := uniform_transport_bind (swapCachedOutputsTransport cache.entries old new).symm
    (fun p => next p.val)
  exact transported.symm

theorem pinned_distinct_tail_frame (rows : List Row) (old : Block) (low : BitVec 256)
    (unique : ∀ row ∈ rows, pinnedOutputTail row.2 = pinnedOutputTail old → row.2 = old) :
    swapCachedOutputRows rows old (pinnedOutputTail old ++ low) =
      rows.map (fun row => if row.2 = old then (row.1, pinnedOutputTail old ++ low) else row) := by
  apply List.map_congr_left
  intro row present
  by_cases atRow : row.2 = old
  · simp only [atRow]
    exact congrArg (fun reply : Block => (row.1, reply)) (swap_first old (pinnedOutputTail old ++ low))
  · have notNew : row.2 ≠ pinnedOutputTail old ++ low := by
      intro same
      have tail : pinnedOutputTail (pinnedOutputTail old ++ low) = pinnedOutputTail old :=
        BitVec.extractLsb'_append_eq_left
      exact atRow (unique row present ((congrArg pinnedOutputTail same).trans tail))
    simp [atRow, swap_other atRow notNew]

noncomputable def pinnedTaggedHidingCharge (budget : Nat) : ℝ :=
  2 ^ 28 * ((budget : ℝ) + 2 ^ 26) / 2 ^ 1344 +
    2 * (budget : ℝ) / 2 ^ 128 +
    2 * (budget : ℝ) * (2 / 2 ^ 128 + 2 ^ 25 / 2 ^ 1344)

/-- The tail-restriction, public seed, and observer allowances fit the TV limit
with at least 32-fold slack. -/
theorem pinned_tagged_hiding_margin (budget : Nat) :
    pinnedTaggedHidingCharge budget ≤ ((budget : ℝ) + 1) / 2 ^ 125 := by
  have nonneg : 0 ≤ (budget : ℝ) := Nat.cast_nonneg _
  unfold pinnedTaggedHidingCharge
  norm_num
  linarith

end TwoPermutationPrototype.Sampling
