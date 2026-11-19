import CommitGolfCandidate.TaggedPinnedHiddenWrites

namespace TwoPermutationPrototype.Sampling
open OracleComp
set_option maxRecDepth 8192

theorem pinned_program_rows_agree {before after : Cache}
    (schedule : PinnedWrites before after) (p : Completion before.entries) :
    Agrees after.entries (p.val.programRows schedule.rows) := by
  induction schedule with
  | nil cache => exact p.property
  | reuse cache final address old replacement present body ih =>
    have known : p.val.forward address = old := p.property (address, old) present
    let replaced := (swapCachedOutputsTransport cache.entries old replacement).toFun p
    change Agrees final.entries ((p.val.program address replacement).programRows body.rows)
    rw [BiPermutation.program, known]
    exact ih replaced
  | fresh cache final address unused reply body ih =>
    have keep := p.val.program_preserves cache.entries p.property unused reply.property
    let enlarged : Completion (cache.extendForward address unused reply).entries :=
      ⟨p.val.program address reply.val, keep⟩
    exact ih enlarged

noncomputable def PinnedOpenedState.publicReply {base : Cache} {count : Nat} (state : PinnedOpenedState base count)
    [DecidablePred state.isRevealed] (opened : {i : Fin count // state.isRevealed i} → BitVec 256)
    (address : Block) : Block :=
  (state.high.realize (pinnedFinLowTape (state.merge opened (fun _ => 0)))).example.val.forward address

theorem pinned_reference_public_reply {base : Cache} {count : Nat}
    (state : PinnedOpenedState base count) [DecidablePred state.isRevealed]
    (opened : {i : Fin count // state.isRevealed i} → BitVec 256) (privateLow : state.PrivateSlot → BitVec 256)
    (address : Block) (openAddress : address ∈ state.opened)
    (p : Completion (state.high.realize (pinnedFinLowTape (state.merge opened privateLow))).entries) :
    p.val.forward address = state.publicReply opened address := by
  have known : ¬ UnusedInput (state.high.realize (pinnedFinLowTape (state.merge opened privateLow))).entries address :=
    fun fresh => state.present address openAddress
      ((state.high.input_unused address (pinnedFinLowTape (state.merge opened privateLow)) (fun _ => 0)).mp fresh)
  apply (pinned_cached_read_agree p address known).trans
  apply pinned_opened_reply_only_revealed state _ _ _ address openAddress
  intro i read
  simp only [PinnedOpenedState.merge, dite_eq_left read]

theorem pinned_program_preserves_unaddressed_cached {base : Cache}
    (start : PinnedHighCache base) (slot : Nat) (addresses : List Block)
    (valid : start.Valid slot) (unique : addresses.Nodup) (outside : ∀ a ∈ addresses, UnusedInput base.entries a)
    (room : start.zero.entries.length + addresses.length ≤ 2^121)
    (result : List (BitVec 1344) × PinnedHighCache base)
    (possible : result ∈ support (runPinnedHigh start slot [] (pinnedConstantPlans addresses)))
    (low : PinnedLowTape) (p : Completion (start.realize low).entries) (digests : Block → BitVec 256)
    (address : Block) (known : start.Covers address) (unaddressed : address ∉ addresses) :
    (p.val.programRows (addresses.map (fun target =>
      (target, pinnedCachedUpper result.2.zero target ++ digests target)))).forward address =
      p.val.forward address := by
  obtain ⟨post, schedule, rows, placement⟩ := pinned_build_hidden_writes start slot [] addresses
    valid room unique outside result possible low digests
  have finalized := pinned_program_rows_agree schedule p
  rw [rows] at finalized
  obtain ⟨row, present, actual⟩ := known
  change row ∈ pinnedHighTable base start.added (fun _ => 0) at present
  rcases List.mem_append.mp present with added | initial
  · obtain ⟨stored, prior, rfl⟩ := List.mem_map.mp added
    have remains := pinned_high_rows_keep start slot [] (pinnedConstantPlans addresses) result possible stored prior
    change stored.input = address at actual
    have no := fun present : stored.input ∈ addresses => unaddressed (actual ▸ present)
    have stayed : post stored.slot = low stored.slot := by
      have set := placement stored remains
      rwa [ite_eq_right no] at set
    have newValue := finalized (stored.realize post)
      (List.mem_append_left _ (List.mem_map_of_mem remains))
    have oldValue := p.property (stored.realize low) (List.mem_append_left _ (List.mem_map_of_mem prior))
    exact ((congrArg _ actual).symm.trans newValue).trans
      ((congrArg (fun bits : BitVec 256 => (stored.upper ++ bits : Block)) stayed).trans
        (oldValue.symm.trans (congrArg p.val.forward actual)))
  · have newValue := finalized row (List.mem_append_right _ initial)
    have oldValue := p.property row (List.mem_append_right _ initial)
    exact ((congrArg _ actual).symm.trans newValue).trans (oldValue.symm.trans (congrArg p.val.forward actual))

end TwoPermutationPrototype.Sampling
