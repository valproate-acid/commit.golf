import CommitGolfCandidate.TwoPermutationCollectInput
import CommitGolfCandidate.TwoPermutationCheckerCapHash
import CommitGolfCandidate.TwoPermutationCheckerMarkSweep

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling

theorem honest_index_sorted (positions : Positions) (ordinal : Nat) (present : ordinal < positions.card) :
    (honestIndex positions ordinal present).val = Opening.sortedIndex positions ordinal present :=
  check_input_value_index ⟨0,positions,fun _ => 0,[]⟩ ordinal present

theorem record_groups_next (input : CheckInput) (ordinal : Nat) (present : ordinal < input.positions.card) :
    Opening.groupsBefore input.positions (ordinal+1) =
      Opening.groupsBefore input.positions ordinal ++ [capGroup (honestIndex input.positions ordinal present).val] := by
  rw [Opening.groups_before_next input.positions ordinal present, honest_index_sorted]

theorem record_groups_length (input : CheckInput) (ordinal : Nat) (bounded : ordinal ≤ input.positions.card) :
    (Opening.groupsBefore input.positions ordinal).length = ordinal := by
  simp [Opening.groupsBefore, Nat.min_eq_left bounded]

theorem collected_group_present (input : CheckInput) (ordinal earlier : Nat)
    (seen : earlier < ordinal) (present : earlier < input.positions.card) :
    capGroup (honestIndex input.positions earlier present).val ∈ Opening.groupsBefore input.positions ordinal := by
  rw [honest_index_sorted]
  apply List.mem_map.mpr
  let index := Opening.sortedIndex input.positions earlier present
  refine ⟨index, ?_, rfl⟩
  have inside : earlier < ((input.positions.sort (· ≤ ·)).take ordinal).length := by
    simp only [List.length_take, Finset.length_sort, Nat.lt_min]
    exact ⟨seen, present⟩
  apply List.mem_iff_getElem.mpr
  exact ⟨earlier, inside, List.getElem_take⟩

/-- The accepted prefix and the cap groups its records authenticate. -/
structure CollectedTable (oracle : Oracle) (input : CheckInput) (ordinal : Nat) (state : MachineState)
    (rows : List PublicRow) : Prop where
  marks : ∀ group < 512, machineMarks state group =
    if group ∈ Opening.groupsBefore input.positions ordinal then 1 else 0
  evidence : ∀ earlier < ordinal, ∀ present : earlier < input.positions.card,
    let index := honestIndex input.positions earlier present
    Nonempty (RecordedLower oracle index.val (input.values index)
      (capRootAt state (capGroup index.val)) rows)
  honest : ∀ (message : Message) (salts : CompleteSaltTape),
    input = honestCheckInput oracle message input.positions salts →
    ∀ group ∈ Opening.groupsBefore input.positions ordinal,
      capRootAt state group = honestHeap oracle message salts group

theorem checker_marks_as_word (state : MachineState) (group : Nat) :
    machineMarks state group = memoryView state (512+group) := by
  unfold machineMarks Opening.markBase memoryView wordAddress
  rw [show 4096+8*group=8*(512+group) by omega]

theorem collected_table_empty (oracle : Oracle) (input : CheckInput) (state : MachineState)
    (memory : state.mem = (Assembly.submission.initialState .check input).mem) :
    CollectedTable oracle input 0 state [] := by
  constructor
  · intro group inside
    have framed := congrFun memory (wordAddress (512+group))
    have mark := check_mark_zero input group inside
    have clean : machineMarks state group = 0 := (checker_marks_as_word _ _).trans (framed.trans mark)
    simpa only [Opening.groupsBefore, List.take_zero, List.map_nil, List.not_mem_nil, ite_false] using clean
  · intro earlier before
    omega
  · intro message salts honest group belongs
    simp [Opening.groupsBefore] at belongs

theorem record_lower_preserves_cap (oracle : Oracle) {state : MachineState} {source nonce : Nat} {index : Index}
    (ready : CheckRecordReady state source nonce index) (sourceAbove : 4096 ≤ source)
    (group : Nat) (inside : group < 512) :
    let lower := (recordLower oracle state source index).state
    machineMarks lower group = machineMarks state group ∧
      capRootAt lower group = capRootAt state group := by
  have frame := (record_lower_frame oracle ready).2
  constructor
  · rw [checker_marks_as_word, checker_marks_as_word]
    exact frame (512+group) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  · change readBuffer _ (8*(2048+4*group)) 32 = readBuffer _ (8*(2048+4*group)) 32
    apply aligned_digest_frame
    intro offset bounded
    exact frame _ (by omega) (Or.inl (by omega)) (Or.inr (by omega))

theorem collected_table_append (oracle : Oracle) (input : CheckInput) (ordinal : Nat) (present : ordinal < input.positions.card)
    (state next : MachineState) (rows extra : List PublicRow) (table : CollectedTable oracle input ordinal state rows)
    (nextMarks : ∀ group < 512,
      machineMarks next group = if group = capGroup (honestIndex input.positions ordinal present).val
        then 1 else machineMarks state group)
    (otherRoots : ∀ group < 512, group ≠ capGroup (honestIndex input.positions ordinal present).val →
      capRootAt next group = capRootAt state group)
    (sameRoot : capGroup (honestIndex input.positions ordinal present).val ∈ Opening.groupsBefore input.positions ordinal →
      capRootAt next (capGroup (honestIndex input.positions ordinal present).val) =
        capRootAt state (capGroup (honestIndex input.positions ordinal present).val))
    (latest : let idx := honestIndex input.positions ordinal present
      Nonempty (RecordedLower oracle idx.val (input.values idx) (capRootAt next (capGroup idx.val)) extra))
    (honestLatest : ∀ (message : Message) (salts : CompleteSaltTape),
      input = honestCheckInput oracle message input.positions salts →
      capRootAt next (capGroup (honestIndex input.positions ordinal present).val) =
        honestHeap oracle message salts (capGroup (honestIndex input.positions ordinal present).val)) :
    CollectedTable oracle input (ordinal+1) next (rows++extra) := by
  let group := capGroup (honestIndex input.positions ordinal present).val
  have preserved (node : Nat) (inside : node < 512)
      (existing : node ∈ Opening.groupsBefore input.positions ordinal) :
      capRootAt next node = capRootAt state node := by
    by_cases equal : node = group
    · subst node
      exact sameRoot existing
    · exact otherRoots node inside equal
  constructor
  · intro node inside
    rw [nextMarks node inside, table.marks node inside, record_groups_next input ordinal present]
    by_cases same : node = group
    · simp [group, same]
    · simp only [group] at same
      simp [List.mem_append, same]
  · intro earlier seen earlierPresent
    by_cases current : earlier = ordinal
    · subst earlier
      obtain ⟨path⟩ := latest
      exact ⟨path.mono fun _ => List.mem_append_right _⟩
    · have before : earlier < ordinal := by omega
      have already := collected_group_present input ordinal earlier before earlierPresent
      have bound := (checker_cap_group (honestIndex input.positions earlier earlierPresent).val).2
      have authentic := table.evidence earlier before earlierPresent
      dsimp only at authentic
      obtain ⟨path⟩ := authentic
      have retained := preserved _ bound already
      dsimp only
      rw [retained]
      exact ⟨path.mono fun _ => List.mem_append_left _⟩
  · intro message salts honest node seen
    rw [record_groups_next input ordinal present] at seen
    rcases List.mem_append.mp seen with old | singleton
    · have bound : node < 512 := by
        obtain ⟨idx,_,rfl⟩ := List.mem_map.mp old
        exact (checker_cap_group idx).2
      rw [preserved node bound old]
      exact table.honest message salts honest node old
    · have equal : node = group := List.mem_singleton.mp singleton
      subst node
      exact honestLatest message salts honest

theorem collect_authenticated_index (oracle : Oracle) (input : CheckInput) (state : MachineState)
    (rows : List PublicRow)
    (table : CollectedTable oracle input input.positions.card state rows) (index : {i // i ∈ input.positions}) :
    let group := capGroup index.val
    group ∈ Opening.groupsBefore input.positions input.positions.card ∧
      Nonempty (RecordedLower oracle index.val (input.values index) (capRootAt state group) rows) := by
  have appears : index ∈ honestOrder input.positions := by
    simp [honestOrder]
  obtain ⟨ordinal, within, selected⟩ := List.mem_iff_getElem.mp appears
  have present : ordinal < input.positions.card := by simpa only [honest_order_length] using within
  change honestIndex input.positions ordinal present = index at selected
  have seen := collected_group_present input input.positions.card ordinal present present
  have evidence := table.evidence ordinal present present
  dsimp only at evidence
  rw [selected] at seen evidence
  exact ⟨seen,evidence⟩

end TwoPermutationPrototype.Checker
