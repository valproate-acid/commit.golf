import CommitGolfCandidate.TaggedPinnedTailEvaluation
import CommitGolfCandidate.TaggedPinnedDigestTape

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

abbrev PinnedLowTape := Nat → BitVec 256

structure PinnedHighRow where
  input : Block
  upper : BitVec 1344
  slot : Nat

instance pinnedHighRowCountable : Countable PinnedHighRow :=
  Function.Injective.countable (f := fun row : PinnedHighRow => (row.input, row.upper, row.slot)) (by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ same
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl, rfl⟩ := same
    rfl)

def PinnedHighRow.realize (row : PinnedHighRow) (low : PinnedLowTape) : Row :=
  (row.input, row.upper ++ low row.slot)

def pinnedHighTable (base : Cache) (rows : List PinnedHighRow) (low : PinnedLowTape) : List Row :=
  rows.map (fun row => row.realize low) ++ base.entries

theorem pinned_high_row_tail (row : PinnedHighRow) (low : PinnedLowTape) :
    pinnedOutputTail (row.realize low).2 = row.upper :=
  BitVec.extractLsb'_append_eq_left

theorem pinned_high_row_digest (row : PinnedHighRow) (low : PinnedLowTape) :
    pinnedOutputDigest (row.realize low).2 = low row.slot :=
  BitVec.extractLsb'_append_eq_right

structure PinnedHighCache (base : Cache) where
  added : List PinnedHighRow
  consistent : ∀ low : PinnedLowTape, Nonempty (Completion (pinnedHighTable base added low))

instance pinnedHighCacheCountable (base : Cache) : Countable (PinnedHighCache base) :=
  Function.Injective.countable (f := PinnedHighCache.added) (by
    rintro ⟨rows, _⟩ ⟨other, _⟩ same
    change rows = other at same
    subst other
    rfl)

def PinnedHighCache.empty (base : Cache) : PinnedHighCache base :=
  ⟨[], fun _ => base.consistent⟩

def PinnedHighCache.realize {base : Cache} (cache : PinnedHighCache base) (low : PinnedLowTape) : Cache :=
  ⟨pinnedHighTable base cache.added low, cache.consistent low⟩

def PinnedHighCache.zero {base : Cache} (cache : PinnedHighCache base) : Cache :=
  cache.realize (fun _ => 0)

theorem pinned_cache_entries_ext {left right : Cache} (entries : left.entries = right.entries) : left = right := by
  cases left
  cases right
  cases entries
  rfl

@[simp] theorem PinnedHighCache.empty_realize (base : Cache) (low : PinnedLowTape) :
    (PinnedHighCache.empty base).realize low = base :=
  pinned_cache_entries_ext rfl

theorem PinnedHighCache.entries_length {base : Cache} (cache : PinnedHighCache base) (low : PinnedLowTape) :
    (cache.realize low).entries.length = cache.added.length + base.entries.length := by
  simp [PinnedHighCache.realize, pinnedHighTable]

theorem PinnedHighCache.tails {base : Cache} (cache : PinnedHighCache base) (low : PinnedLowTape) :
    pinnedCachedTails (cache.realize low) = cache.added.map PinnedHighRow.upper ++ pinnedCachedTails base := by
  simp [pinnedCachedTails, PinnedHighCache.realize, pinnedHighTable, List.map_map, Function.comp_def,
    pinned_high_row_tail]

theorem PinnedHighCache.input_unused {base : Cache} (cache : PinnedHighCache base)
    (input : Block) (left right : PinnedLowTape) :
    UnusedInput (cache.realize left).entries input ↔ UnusedInput (cache.realize right).entries input := by
  have mono (left right : PinnedLowTape) (unused : UnusedInput (cache.realize left).entries input) :
      UnusedInput (cache.realize right).entries input := by
    intro row present
    change row ∈ pinnedHighTable base cache.added right at present
    rcases List.mem_append.mp present with fresh | old
    · obtain ⟨stored, seen, rfl⟩ := List.mem_map.mp fresh
      exact unused (stored.realize left) (List.mem_append_left _ (List.mem_map_of_mem seen))
    · exact unused row (List.mem_append_right _ old)
  exact ⟨mono left right, mono right left⟩

theorem PinnedHighCache.same_realization {base : Cache} (cache : PinnedHighCache base) (left right : PinnedLowTape)
    (same : ∀ row ∈ cache.added, left row.slot = right row.slot) : cache.realize left = cache.realize right := by
  apply pinned_cache_entries_ext
  change pinnedHighTable base cache.added left = pinnedHighTable base cache.added right
  unfold pinnedHighTable
  apply congrArg (· ++ base.entries)
  apply List.map_congr_left
  intro row seen
  unfold PinnedHighRow.realize
  rw [same row seen]

theorem PinnedHighCache.unchanged_update {base : Cache} (cache : PinnedHighCache base)
    (low : PinnedLowTape) (step : Nat) (draw : BitVec 256)
    (earlier : ∀ row ∈ cache.added, row.slot < step) :
    cache.realize (Function.update low step draw) = cache.realize low := by
  apply cache.same_realization
  intro row present
  have different : row.slot ≠ step := by have := earlier row present; omega
  simp [Function.update_of_ne, different]

noncomputable def PinnedHighCache.extend {base : Cache} (cache : PinnedHighCache base) (row : PinnedHighRow)
    (fresh : UnusedInput cache.zero.entries row.input)
    (newTail : pinnedUnusedTail (pinnedCachedTails cache.zero) row.upper) : PinnedHighCache base where
  added := row :: cache.added
  consistent low := by
    have available : UnusedInput (cache.realize low).entries row.input :=
      (cache.input_unused row.input (fun _ => 0) low).mp fresh
    have tailFree : pinnedUnusedTail (pinnedCachedTails (cache.realize low))
        (pinnedOutputTail (row.realize low).2) := by
      rw [pinned_high_row_tail, cache.tails]
      exact (cache.tails (fun _ => 0)) ▸ newTail
    let updated := (cache.realize low).extendForward row.input available
      ⟨(row.realize low).2, pinned_unused_tail_unused_output (cache.realize low) (row.realize low).2 tailFree⟩
    exact updated.consistent

theorem PinnedHighCache.extend_realize {base : Cache} (cache : PinnedHighCache base) (row : PinnedHighRow) (fresh)
    (newTail) (low : PinnedLowTape) (available : UnusedInput (cache.realize low).entries row.input)
    (answer : RemainingOutputs (cache.realize low).entries) (value : answer.val = (row.realize low).2) :
    (cache.extend row fresh newTail).realize low = (cache.realize low).extendForward row.input available answer := by
  apply pinned_cache_entries_ext
  change (row.realize low) :: (cache.realize low).entries = (row.input, answer.val) :: (cache.realize low).entries
  rw [value]
  rfl

theorem PinnedHighCache.read_tail {base : Cache} (cache : PinnedHighCache base) (input : Block)
    (known : ¬ UnusedInput cache.zero.entries input) (low : PinnedLowTape) :
    pinnedOutputTail ((cache.realize low).example.val.forward input) =
      pinnedOutputTail (cache.zero.example.val.forward input) := by
  classical
  have existsRow : ∃ row ∈ cache.zero.entries, row.1 = input := by
    by_contra missing
    apply known
    exact fun row present same => missing ⟨row, present, same⟩
  obtain ⟨row, present, same⟩ := existsRow
  change row ∈ pinnedHighTable base cache.added (fun _ => 0) at present
  rcases List.mem_append.mp present with fresh | old
  · obtain ⟨stored, included, rfl⟩ := List.mem_map.mp fresh
    have a := (cache.realize low).example.property (stored.realize low)
      (List.mem_append_left _ (List.mem_map_of_mem included))
    have b := cache.zero.example.property (stored.realize (fun _ => 0))
      (List.mem_append_left _ (List.mem_map_of_mem included))
    change stored.input = input at same
    change (cache.realize low).example.val.forward stored.input = (stored.realize low).2 at a
    change cache.zero.example.val.forward stored.input = (stored.realize (fun _ => 0)).2 at b
    rw [← same, a, b, pinned_high_row_tail, pinned_high_row_tail]
  · have a := (cache.realize low).example.property row (List.mem_append_right _ old)
    have b := cache.zero.example.property row (List.mem_append_right _ old)
    rw [← same, a, b]

end TwoPermutationPrototype.Sampling
