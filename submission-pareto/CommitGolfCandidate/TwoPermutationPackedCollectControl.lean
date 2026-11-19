import CommitGolfCandidate.TwoPermutationPackedRecordInterface

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (GroupAccepted groupMemory group_memory_other group_memory_mark group_memory_root
  RecordInputFrame checkIndexWord checkSourceWord record_input_frame_step checker_positions_bound
  aligned_digest_frame aligned_buffer_frame honestIndex checker_cap_group
  check_recorded_map machineMarks capRootAt checker_marks_as_word)
open TwoPermutationPrototype.PackedCertificate (honestCheckInput)
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

theorem group_after_record_ready (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (state : MachineState)
    (cursor : RecordCursor input ordinal state) (block : RecordBlock)
    (facts : RecordBlockFacts oracle input ordinal present state block) :
    GroupReady (capGroup (honestIndex input.positions ordinal present).val)
      (input.positions.card-(ordinal+1)) block.state := by
  obtain ⟨lo, hi⟩ := checker_cap_group (honestIndex input.positions ordinal present).val
  have bounded := checker_positions_bound input
  refine ⟨facts.pc, facts.node, lo, hi,
    (facts.saved .x23 (by decide)).trans cursor.digest,
    (facts.saved .x25 (by decide)).trans cursor.capRoots,
    (facts.saved .x26 (by decide)).trans cursor.marks, ?_, by omega⟩
  rw [facts.saved .x18 (by decide), cursor.remaining,
    show input.positions.card-ordinal=input.positions.card-(ordinal+1)+1 by omega]

theorem group_after_record_cursor (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (state : MachineState)
    (cursor : RecordCursor input ordinal state) (block : RecordBlock)
    (facts : RecordBlockFacts oracle input ordinal present state block) :
    let index := (honestIndex input.positions ordinal present).val
    GroupAccepted block.state (capGroup index) →
    RecordCursor input (ordinal+1) (groupRun block.state (capGroup index)).1 := by
  let index := (honestIndex input.positions ordinal present).val
  let next := (groupRun block.state (capGroup index)).1
  have phase := group_after_record_ready oracle input ordinal present state cursor block facts
  have frame := group_run_state block.state (capGroup index) (input.positions.card-(ordinal+1)) phase
  change GroupAccepted block.state (capGroup index) → RecordCursor input (ordinal+1) next
  intro accepted
  obtain ⟨indices, values, remaining⟩ := frame.advanced accepted
  have keep (r : Reg) (a : RecordSaved r) (b : GroupSaved r) :
      next.getReg r = state.getReg r := (frame.saved r b).trans (facts.saved r a)
  refine ⟨?_, ?_, ?_, ?_, remaining, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [frame.pc, ite_eq_left accepted]
    simp only [show input.positions.card-(ordinal+1)=0 ↔ ordinal+1=input.positions.card by omega]
  · rw [indices, facts.saved .x8 (by decide), cursor.index]
    change wordAddress (checkIndexWord ordinal) + wordAddress 1 = _
    rw [← wordAddress_add]
    congr 1
  · rw [values, facts.saved .x19 (by decide), cursor.value]
    change wordAddress (checkSourceWord ordinal) + wordAddress 32 = _
    rw [← wordAddress_add]
    congr 1
  · exact (frame.saved .x21 (by unfold GroupSaved; decide)).trans facts.proof
  all_goals first
    | exact (keep _ (by decide) (by unfold GroupSaved; decide)).trans cursor.tag
    | exact (keep _ (by decide) (by unfold GroupSaved; decide)).trans cursor.commitment
    | exact (keep _ (by decide) (by unfold GroupSaved; decide)).trans cursor.challengeLength
    | exact (keep _ (by decide) (by unfold GroupSaved; decide)).trans cursor.proofEnd
    | exact (keep _ (by decide) (by unfold GroupSaved; decide)).trans cursor.digest
    | exact (keep _ (by decide) (by unfold GroupSaved; decide)).trans cursor.pair
    | exact (keep _ (by decide) (by unfold GroupSaved; decide)).trans cursor.capRoots
    | exact (keep _ (by decide) (by unfold GroupSaved; decide)).trans cursor.marks
    | exact (keep _ (by decide) (by unfold GroupSaved; decide)).trans cursor.capCount
    | exact (keep _ (by decide) (by unfold GroupSaved; decide)).trans cursor.selector
    | exact (keep _ (by decide) (by unfold GroupSaved; decide)).trans cursor.nonceScratch

theorem execute_record_group (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (state : MachineState)
    (cursor : RecordCursor input ordinal state) (block : RecordBlock)
    (facts : RecordBlockFacts oracle input ordinal present state block) (fuel : Nat) :
    let index := (honestIndex input.positions ordinal present).val
    let group := groupRun block.state (capGroup index)
    let tail := checkEvaluation oracle (recordRows (execute packedImage fuel group.1 false))
    checkEvaluation oracle (recordRows (execute packedImage (block.steps+group.2+fuel) state false)) =
      ((tail.1.1.charge (block.cycles+group.2) 18, block.rows ++ tail.1.2), 18+tail.2) := by
  let index := (honestIndex input.positions ordinal present).val
  let group := groupRun block.state (capGroup index)
  have phase := group_after_record_ready oracle input ordinal present state cursor block facts
  have run := group_run_execute block.state (capGroup index) (input.positions.card-(ordinal+1)) phase fuel
  dsimp only
  rw [show block.steps+group.2+fuel=block.steps+(group.2+fuel) by omega, facts.run (group.2+fuel), run]
  simp only [bind_pure_comp, check_recorded_map, Execution.charge, Nat.add_assoc, Nat.zero_add]
  rfl

theorem record_preserves_cap (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (state : MachineState) (block : RecordBlock)
    (facts : RecordBlockFacts oracle input ordinal present state block)
    (group : Nat) (inside : group < 512) :
    machineMarks block.state group = machineMarks state group ∧
      capRootAt block.state group = capRootAt state group := by
  have sourceAbove : 4096 ≤ checkSourceWord ordinal := by unfold checkSourceWord; omega
  constructor
  · rw [checker_marks_as_word, checker_marks_as_word]
    exact facts.frame (512+group) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  · change readBuffer _ (8*(2048+4*group)) 32 = readBuffer _ (8*(2048+4*group)) 32
    apply aligned_digest_frame
    intro offset bounded
    exact facts.frame _ (by omega) (Or.inl (by omega)) (Or.inr (by omega))

theorem group_accepts_honest (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (state : MachineState)
    (block : RecordBlock) (facts : RecordBlockFacts oracle input ordinal present state block)
    (rows : List PublicRow) (table : CollectedTable oracle input ordinal state rows)
    (message : Message) (salts : CompleteSaltTape)
    (canonical : input = honestCheckInput oracle message input.positions salts) :
    let index := (honestIndex input.positions ordinal present).val
    GroupAccepted block.state (capGroup index) := by
  let index := (honestIndex input.positions ordinal present).val
  let group := capGroup index
  have bound := (checker_cap_group index).2
  obtain ⟨sameMark, sameRoot⟩ :=
    record_preserves_cap oracle input ordinal present state block facts group bound
  change GroupAccepted block.state group
  by_cases member : group ∈ Opening.groupsBefore input.positions ordinal
  · right
    exact sameRoot.trans ((table.honest message salts canonical group member).trans
      (facts.honest message salts canonical).symm)
  · left
    change memoryView block.state (512+group) = 0
    rw [← checker_marks_as_word, sameMark, table.marks group bound, ite_eq_right member]

theorem group_collect_transition (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (state : MachineState)
    (cursor : RecordCursor input ordinal state) (loaded : RecordInputFrame input ordinal state)
    (block : RecordBlock) (facts : RecordBlockFacts oracle input ordinal present state block)
    (rows : List PublicRow) (table : CollectedTable oracle input ordinal state rows) :
    let index := (honestIndex input.positions ordinal present).val
    let group := groupRun block.state (capGroup index)
    GroupAccepted block.state (capGroup index) →
    RecordCursor input (ordinal+1) group.1 ∧ RecordInputFrame input (ordinal+1) group.1 ∧
      CollectedTable oracle input (ordinal+1) group.1 (rows++block.rows) := by
  let attached := honestIndex input.positions ordinal present
  let index := attached.val
  let group := capGroup index
  let next := (groupRun block.state group).1
  have phase := group_after_record_ready oracle input ordinal present state cursor block facts
  have physical := group_run_state block.state group (input.positions.card-(ordinal+1)) phase
  have bound := (checker_cap_group index).2
  have lowerCap := record_preserves_cap oracle input ordinal present state block facts
  have nextWord (word : Nat) : memoryView next word = memoryView (groupMemory block.state group) word :=
    congrFun physical.memory (wordAddress word)
  have same (word : Nat) (fit : word < 2^61) (mark : word ≠ 512+group)
      (roots : word < 2048+4*group ∨ 2048+4*group+4 ≤ word) :
      memoryView next word = memoryView block.state word :=
    (nextWord word).trans (group_memory_other block.state group word bound fit mark roots)
  change GroupAccepted block.state group → RecordCursor input (ordinal+1) next ∧
    RecordInputFrame input (ordinal+1) next ∧
    CollectedTable oracle input (ordinal+1) next (rows++block.rows)
  intro accepted
  refine ⟨group_after_record_cursor oracle input ordinal present state cursor block facts accepted, ?_, ?_⟩
  · apply record_input_frame_step input ordinal state next loaded
    intro word fit used
    have above : 4096 ≤ word := by
      rcases used with h | h | h
      · omega
      · unfold checkIndexWord at h
        omega
      · unfold checkSourceWord at h
        omega
    obtain ⟨source, scratch⟩ := packed_input_address_after input ordinal word used
    exact (same word (by omega) (by omega) (Or.inr (by omega))).trans
      (facts.frame word fit source (Or.inr scratch))
  have targetRoot : capRootAt next group = readBuffer block.state 12288 32 :=
    (read_buffer_memory_congr _ _ physical.memory _ _).trans (group_memory_root block.state group bound accepted)
  have oldMark : memoryView block.state (512+group) =
      if group ∈ Opening.groupsBefore input.positions ordinal then 1 else 0 := by
    rw [← checker_marks_as_word, (lowerCap group bound).1, table.marks group bound]
  apply collected_table_append oracle input ordinal present state next rows block.rows table
  · intro node inside
    by_cases hit : node = group
    · subst node
      have observed : memoryView next (512+group) =
          if memoryView block.state (512+group) = 0 then 1 else memoryView block.state (512+group) :=
        (nextWord _).trans (group_memory_mark block.state group)
      rw [checker_marks_as_word, observed]
      simp only [show capGroup (honestIndex input.positions ordinal present).val = group from rfl, ite_true]
      by_cases seen : group ∈ Opening.groupsBefore input.positions ordinal
      · simp [oldMark, seen]
      · simp [oldMark, seen]
    · rw [ite_eq_right hit, checker_marks_as_word, checker_marks_as_word state]
      exact (same _ (by omega) (by omega) (Or.inl (by omega))).trans
        ((checker_marks_as_word _ _).symm.trans ((lowerCap node inside).1.trans (checker_marks_as_word _ _)))
  · intro node inside outside
    have separate : node ≠ group := outside
    change readBuffer next (8*(2048+4*node)) 32 = capRootAt state node
    refine (aligned_digest_frame block.state next _ ?_).trans (lowerCap node inside).2
    intro offset small
    apply same _ (by omega) (by omega)
    omega
  · intro seen
    have used : block.state.getMem (wordAddress (512+group)) ≠ 0 := by
      change memoryView block.state (512+group) ≠ 0
      rw [oldMark, ite_eq_left seen]
      decide
    have eq : (groupMemory block.state group).mem = block.state.mem := by
      unfold groupMemory
      rw [ite_eq_right used]
    exact (read_buffer_memory_congr _ _ (physical.memory.trans eq) _ _).trans (lowerCap group bound).2
  · dsimp only
    rw [targetRoot]
    exact facts.trace
  · intro message salts canonical
    exact targetRoot.trans (facts.honest message salts canonical)

end TwoPermutationPrototype.Packed.Checker
