import CommitGolfCandidate.TwoPermutationOpeningRecordLoop
import CommitGolfCandidate.TwoPermutationOpeningCapEntry

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.Sampling RiscvZkvm.Rv64

attribute [local irreducible] recordMachine recordDataMachine

def groupsBefore (positions : Positions) (ordinal : Nat) : List Nat :=
  ((positions.sort (· ≤ ·)).take ordinal).map capGroup

theorem groups_before_next (positions : Positions) (ordinal : Nat) (present : ordinal < positions.card) :
    groupsBefore positions (ordinal + 1) =
      groupsBefore positions ordinal ++ [capGroup (sortedIndex positions ordinal present)] := by
  have inside : ordinal < (positions.sort (· ≤ ·)).length := by simpa using present
  unfold groupsBefore sortedIndex
  rw [List.take_succ_eq_append_getElem inside, List.map_append]
  rfl

private theorem observed_fixed_mark (before after : MachineState) (target node : Nat)
    (targetBound : target < 512) (nodeBound : node < 512)
    (memory : after.mem = (before.setMem (BitVec.ofNat 64 (markBase + 8 * target)) 1#64).mem) :
    machineMarks after node = if node = target then 1 else machineMarks before node := by
  have point := congrFun memory (BitVec.ofNat 64 (markBase + 8 * node))
  unfold machineMarks
  refine point.trans ?_
  by_cases equal : node = target
  · subst node
    simp [MachineState.getMem, MachineState.setMem]
  · have different : BitVec.ofNat 64 (markBase + 8 * node) ≠
        BitVec.ofNat 64 (markBase + 8 * target) := by
      intro same
      unfold markBase at same
      have eq := nat_address_injective (by omega) (by omega) same
      omega
    simp [MachineState.getMem, MachineState.setMem, equal, different]

theorem record_group_update (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal node : Nat) (present : ordinal < positions.card)
    (bounded : node < 512) (boundary : RecordBoundary s trapdoor positions state ordinal) :
    machineMarks (recordMachine state) node =
      if node = capGroup (sortedIndex positions ordinal present) then 1 else machineMarks state node := by
  let index := sortedIndex positions ordinal present
  have prepared := boundary.start present
  have memory := record_mark_memory s layout trapdoor positions state ordinal present prepared
    boundary.marks boundary.one
  have capBound := (lower_cap_range index).2
  have update := observed_fixed_mark (recordDataMachine state) (recordMachine state)
    (lowerNode index 16) node capBound bounded memory
  have stable : machineMarks (recordDataMachine state) node = machineMarks state node := by
    have low := marks_before_trapdoor
    have middle : trapdoorBase ≤ proofBase := by decide
    have high : markBase + 8*node < recordBase ordinal := by unfold recordBase; omega
    have fit : markBase + 8*node < 2^64 := by unfold markBase; omega
    exact record_data_before s layout trapdoor positions state ordinal (markBase+8*node)
      present prepared high fit
  rw [update, stable, lower_node_cap_group]

def RecordMarks (positions : Positions) (state : MachineState) (ordinal : Nat) : Prop :=
  ∀ node < 512, machineMarks state node = if node ∈ groupsBefore positions ordinal then 1 else 0

theorem records_marks_next (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) (present : ordinal < positions.card)
    (boundary : RecordBoundary s trapdoor positions state ordinal) (marks : RecordMarks positions state ordinal) :
    RecordMarks positions (recordMachine state) (ordinal + 1) := by
  intro node bounded
  rw [record_group_update s layout trapdoor positions state ordinal node present bounded boundary,
    marks node bounded, groups_before_next positions ordinal present]
  by_cases same : node = capGroup (sortedIndex positions ordinal present)
  · simp [same]
  · simp [List.mem_append, same]

theorem records_marks (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal remaining : Nat)
    (limit : ordinal + remaining ≤ positions.card)
    (boundary : RecordBoundary s trapdoor positions state ordinal)
    (marks : RecordMarks positions state ordinal) :
    RecordMarks positions (recordsMachine state remaining) (ordinal + remaining) := by
  induction remaining generalizing state ordinal with
  | zero => simpa only [recordsMachine, Nat.add_zero] using marks
  | succ remaining ih =>
    have present : ordinal < positions.card := by omega
    have next := record_boundary_next s layout trapdoor positions state ordinal present boundary
    have updated := records_marks_next s layout trapdoor positions state ordinal present boundary marks
    have all := ih (recordMachine state) (ordinal + 1) (by omega) next updated
    simpa only [recordsMachine, show ordinal + (remaining + 1) = ordinal + 1 + remaining by omega] using all

theorem initial_record_marks (s : Submission) (layout : OpeningLayout s)
    (image : s.image .opening = openingImage) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) :
    RecordMarks positions (setupPrefix (s.initialState .opening (trapdoor, positions)) 13) 0 := by
  let initial := s.initialState .opening (trapdoor, positions)
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,memory⟩ := setup_registers initial
  intro node bounded
  have content := congrFun memory (BitVec.ofNat 64 (markBase + 8*node))
  change machineMarks (setupPrefix initial 13) node = machineMarks initial node at content
  rw [content]
  simpa [groupsBefore, machineMarks, initial] using initial_mark_word s layout image trapdoor positions node bounded

end TwoPermutationPrototype.Opening
