import CommitGolfCandidate.TaggedPinnedLatentWrite
import CommitGolfCandidate.TaggedPinnedWorldEval

namespace TwoPermutationPrototype.Sampling
open OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option exponentiation.threshold 2048

theorem pinned_high_cache_ext {base : Cache} {first last : PinnedHighCache base}
    (eq : first.added = last.added) : first = last := by
  cases first
  cases last
  cases eq
  rfl

theorem pinned_high_cached_upper_of_row {base : Cache} (cache : PinnedHighCache base)
    (row : PinnedHighRow) (present : row ∈ cache.added) :
    pinnedCachedUpper cache.zero row.input = row.upper := by
  have received := cache.zero.example.property (row.realize (fun _ => 0))
    (List.mem_append_left _ (List.mem_map_of_mem present))
  exact (congrArg pinnedOutputTail received).trans (pinned_high_row_tail row _)

private theorem pinned_write_rows_cast {a b final : Cache} (same : a = b) (tail : PinnedWrites b final) :
    (same.symm ▸ tail : PinnedWrites a final).rows = tail.rows := by
  cases same
  rfl

theorem pinned_row_from_covers {base : Cache} (cache : PinnedHighCache base)
    (input : Block) (covered : cache.Covers input) (notChooser : UnusedInput base.entries input) :
    ∃ row ∈ cache.added, row.input = input := by
  obtain ⟨row, present, read⟩ := covered
  change row ∈ pinnedHighTable base cache.added (fun _ => 0) at present
  rcases List.mem_append.mp present with recent | original
  · obtain ⟨R, included, rfl⟩ := List.mem_map.mp recent
    exact ⟨R, included, read⟩
  · exact (notChooser row original read).elim

private theorem pinned_realize_insert_with_digest {base : Cache} {cache : PinnedHighCache base} {slot : Nat}
    (valid : cache.Valid slot) (row : PinnedHighRow) (here : row.slot = slot)
    (fresh : UnusedInput cache.zero.entries row.input)
    (newTail : pinnedUnusedTail (pinnedCachedTails cache.zero) row.upper) (low : PinnedLowTape)
    (digest : BitVec 256) :
    ∃ (unused : UnusedInput (cache.realize low).entries row.input)
      (reply : RemainingOutputs (cache.realize low).entries),
      reply.val = (row.upper ++ digest : Block) ∧
        (cache.realize low).extendForward row.input unused reply =
          (cache.extend row fresh newTail).realize (Function.update low row.slot digest) := by
  let value : Block := row.upper ++ digest
  have presentTail : pinnedOutputTail value = row.upper := BitVec.extractLsb'_append_eq_left
  have unusedTail : pinnedUnusedTail (pinnedCachedTails (cache.realize low)) (pinnedOutputTail value) := by
    rw [presentTail, cache.tails]
    exact (cache.tails (fun _ => 0)) ▸ newTail
  have unused := (cache.input_unused row.input (fun _ => 0) low).mp fresh
  let reply : RemainingOutputs (cache.realize low).entries :=
    ⟨value, pinned_unused_tail_unused_output (cache.realize low) value unusedTail⟩
  refine ⟨unused, reply, rfl, ?_⟩
  apply pinned_cache_entries_ext
  change (row.input, value) :: (cache.realize low).entries =
    (row.input, (row.upper ++ Function.update low row.slot digest row.slot : Block)) ::
      (cache.realize (Function.update low row.slot digest)).entries
  have stage : cache.realize (Function.update low row.slot digest) = cache.realize low := by
    rw [here]
    exact cache.unchanged_update low slot digest valid.slotRoom
  rw [Function.update_self, stage]
  rfl

/-- Every hidden address has a write in the exact sampled high schedule. The
resulting low tape preserves all unaddressed slots and places the requested
independent digest at the unique slot whose row is addressed. -/
theorem pinned_build_hidden_writes {base : Cache} (start : PinnedHighCache base) (slot : Nat)
    (answers : List (BitVec 1344)) (addresses : List Block) (valid : start.Valid slot)
    (room : start.zero.entries.length + addresses.length ≤ 2^121)
    (distinct : addresses.Nodup) (outside : ∀ address ∈ addresses, UnusedInput base.entries address)
    (final : List (BitVec 1344) × PinnedHighCache base)
    (possible : final ∈ support (runPinnedHigh start slot answers (pinnedConstantPlans addresses)))
    (low : PinnedLowTape) (digest : Block → BitVec 256) :
    ∃ post : PinnedLowTape, ∃ writes : PinnedWrites (start.realize low) (final.2.realize post),
      writes.rows = addresses.map (fun addr => (addr, pinnedCachedUpper final.2.zero addr ++ digest addr)) ∧
      ∀ row ∈ final.2.added, post row.slot =
        if row.input ∈ addresses then digest row.input else low row.slot := by
  classical
  induction addresses generalizing start slot answers final low with
  | nil =>
    simp only [pinnedConstantPlans, List.map_nil, runPinnedHigh, support_pure, Set.mem_singleton_iff] at possible
    subst final
    exact ⟨low, .nil _, rfl, fun row _ => by simp⟩
  | cons address rest ih =>
    have finValid :=
      (pinned_high_const_support start slot answers (address :: rest) valid room final possible).1
    simp only [pinnedConstantPlans, List.map_cons, runPinnedHigh] at possible
    obtain ⟨⟨hit, middle⟩, step, tail⟩ := (mem_support_bind_iff _ _ _).mp possible
    let res : BitVec 1344 × PinnedHighCache base := (hit, middle)
    have stepRoom : start.zero.entries.length ≤ 2^121 := by omega
    have middleValid := pinned_high_step_valid valid address res step stepRoom
    have grows := pinned_high_step_length start slot address res step
    have nextRoom : middle.zero.entries.length + rest.length ≤ 2^121 := by
      change middle.zero.entries.length ≤ start.zero.entries.length + 1 at grows
      simp only [List.length_cons] at room
      omega
    have distinctRest := List.nodup_cons.mp distinct
    have nextOutside : ∀ a ∈ rest, UnusedInput base.entries a :=
      fun a h => outside a (List.mem_cons_of_mem _ h)
    have extendTrace (row : PinnedHighRow) (middleRow : row ∈ middle.added) (isAddress : row.input = address)
        (put : ∀ post : PinnedLowTape, ∀ writes : PinnedWrites
            (middle.realize (Function.update low row.slot (digest address))) (final.2.realize post),
          ∃ all : PinnedWrites (start.realize low) (final.2.realize post),
            all.rows = (address, row.upper ++ digest address) :: writes.rows) :
        ∃ post : PinnedLowTape, ∃ all : PinnedWrites (start.realize low) (final.2.realize post),
          all.rows = (address :: rest).map (fun addr => (addr, pinnedCachedUpper final.2.zero addr ++ digest addr)) ∧
          ∀ entry ∈ final.2.added, post entry.slot =
            if entry.input ∈ address :: rest then digest entry.input else low entry.slot := by
      obtain ⟨post, suffix, rows, assignment⟩ := ih middle (slot+1) (hit :: answers) middleValid nextRoom
        distinctRest.2 nextOutside final tail (Function.update low row.slot (digest address))
      obtain ⟨all, linked⟩ := put post suffix
      have retained : row ∈ final.2.added :=
        pinned_high_rows_keep middle (slot+1) (hit :: answers) (pinnedConstantPlans rest) final tail row middleRow
      refine ⟨post, all, ?_, ?_⟩
      · rw [linked, rows, List.map_cons]
        have read := pinned_high_cached_upper_of_row final.2 row retained
        rw [isAddress] at read
        exact congrArg (fun hi : BitVec 1344 =>
          (address, (hi ++ digest address : Block)) ::
            rest.map (fun addr => (addr, pinnedCachedUpper final.2.zero addr ++ digest addr))) read.symm
      · intro entry present
        rw [assignment entry present]
        by_cases same : entry.input = address
        · have rowEq : entry = row :=
            pinned_unique_mapped_key PinnedHighRow.input finValid.inputUnique present retained (same.trans isAddress.symm)
          subst entry
          simp only [isAddress, distinctRest.1, ite_false, Function.update_self, List.mem_cons_self, ite_true]
        · have differentSlot : entry.slot ≠ row.slot := fun eq =>
            same ((congrArg PinnedHighRow.input
              (pinned_unique_mapped_key PinnedHighRow.slot finValid.slotUnique present retained eq)).trans isAddress)
          simp only [List.mem_cons, same, false_or, Function.update_of_ne differentSlot]
    rcases pinned_high_step_provenance start slot address res step stepRoom with ⟨same, known⟩ |
        ⟨row, isAddress, _, here, added, fresh, newTail⟩
    · obtain ⟨row, present, isAddress⟩ := pinned_row_from_covers start address known (outside address List.mem_cons_self)
      have sameState : middle = start := pinned_high_cache_ext same
      have middleRow : row ∈ middle.added := sameState.symm ▸ present
      apply extendTrace row middleRow isAddress
      intro post suffix
      have stored : (row.input, (row.realize low).2) ∈ (start.realize low).entries :=
        List.mem_append_left _ (List.mem_map_of_mem present)
      have adjust := pinned_realize_updates_latent valid row present low (digest address)
      rw [isAddress] at stored
      have sameStart := adjust.trans (congrArg (fun s : PinnedHighCache base =>
        s.realize (Function.update low row.slot (digest address))) sameState.symm)
      let copy := sameStart.symm ▸ suffix
      refine ⟨.reuse _ _ address _ _ stored copy, ?_⟩
      change (address, (row.upper ++ digest address : Block)) :: copy.rows = _
      rw [pinned_write_rows_cast sameStart suffix]
    · have middleRow : row ∈ middle.added := added.symm ▸ List.mem_cons_self
      apply extendTrace row middleRow isAddress
      intro post suffix
      have middleState : middle = start.extend row fresh newTail := pinned_high_cache_ext added
      obtain ⟨unused, reply, value, adjust⟩ :=
        pinned_realize_insert_with_digest valid row here fresh newTail low (digest address)
      have sameStart := adjust.trans (congrArg (fun s : PinnedHighCache base =>
        s.realize (Function.update low row.slot (digest address))) middleState.symm)
      let copy := sameStart.symm ▸ suffix
      let writes : PinnedWrites (start.realize low) (final.2.realize post) := .fresh _ _ row.input unused reply copy
      refine ⟨writes, ?_⟩
      change (row.input, reply.val) :: copy.rows = _
      exact congrArg₂ (List.cons (α := Row)) (Prod.ext isAddress value) (pinned_write_rows_cast sameStart suffix)

end TwoPermutationPrototype.Sampling
