import CommitGolfCandidate.TwoPermutationOpeningRecordLoop

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64

attribute [local irreducible] readBuffer recordMachine recordDataMachine
set_option maxRecDepth 4096

private theorem earlier_proof_word (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal address : Nat) (present : ordinal < positions.card)
    (boundary : RecordBoundary s trapdoor positions state ordinal)
    (before : address < recordBase ordinal) (above : trapdoorBase ≤ address) (fit : address < 2 ^ 64) :
    (recordMachine state).getMem (BitVec.ofNat 64 address) = state.getMem (BitVec.ofNat 64 address) := by
  have ready := boundary.start present
  exact (record_mark_outside s layout trapdoor positions state ordinal address present ready
    boundary.marks boundary.one above fit).trans
    (record_data_before s layout trapdoor positions state ordinal address present ready before fit)

private theorem record_address_limit (ordinal : Nat) (admitted : ordinal ≤ LENGTH) :
    recordBase ordinal < 2 ^ 64 := by
  have fit := proof_fits_memory
  unfold recordBase proofCapacity MEMORY_BYTES at *
  omega

private theorem earlier_proof_slice (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal address words : Nat) (present : ordinal < positions.card)
    (boundary : RecordBoundary s trapdoor positions state ordinal)
    (aligned : address % 8 = 0) (short : words ≤ 8)
    (before : address + 8 * words ≤ recordBase ordinal) (above : trapdoorBase ≤ address) :
    readBuffer (recordMachine state) address (8 * words) = readBuffer state address (8 * words) := by
  apply copied_buffer _ _ address address words aligned aligned short
  intro j within
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have naturalBefore : address + 8*j < recordBase ordinal := by omega
  have low : trapdoorBase ≤ address + 8*j := above.trans (by omega)
  have fit := naturalBefore.trans (record_address_limit ordinal (by omega))
  exact earlier_proof_word s layout trapdoor positions state ordinal (address+8*j) present boundary
    naturalBefore low fit

/-- Every ordinal earlier than the current record still has its exact original bytes. -/
theorem earlier_record_preserved (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal prior : Nat) (present : ordinal < positions.card)
    (earlier : prior < ordinal) (priorPresent : prior < positions.card)
    (boundary : RecordBoundary s trapdoor positions state ordinal)
    (contents : LowerContents s trapdoor positions state (sortedIndex positions prior priorPresent) prior 16) :
    LowerContents s trapdoor positions (recordMachine state) (sortedIndex positions prior priorPresent) prior 16 := by
  let index := sortedIndex positions prior priorPresent
  have cap : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have after := record_final_contents s layout trapdoor positions state ordinal present
    (boundary.start present) boundary.marks boundary.one
  have below : trapdoorBase ≤ proofBase := by decide
  refine ⟨after.input, ?_, ?_⟩
  · have ⟨_, aligned, _, _⟩ := ordinal_nonce_geometry index prior (by omega)
    have stable := earlier_proof_slice s layout trapdoor positions state ordinal (recordBase prior) 2
      present boundary aligned (by decide) (by unfold recordBase; omega) (by unfold recordBase; omega)
    exact stable.trans contents.nonce
  · intro level inside
    have ⟨_, aligned, _, _⟩ := ordinal_sibling_geometry index prior level (by omega) inside
    have stable := earlier_proof_slice s layout trapdoor positions state ordinal (siblingDest prior level) 4
      present boundary aligned (by decide) (by unfold siblingDest recordBase; omega)
      (by unfold siblingDest recordBase; omega)
    exact stable.trans (contents.sibling level inside)

def CompletedRecords (s : Submission) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) (state : MachineState) (ordinal : Nat) : Prop :=
  ∀ prior (priorPresent : prior < positions.card), prior < ordinal →
    LowerContents s trapdoor positions state (sortedIndex positions prior priorPresent) prior 16

theorem records_contents_next (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) (present : ordinal < positions.card)
    (boundary : RecordBoundary s trapdoor positions state ordinal)
    (contents : CompletedRecords s trapdoor positions state ordinal) :
    CompletedRecords s trapdoor positions (recordMachine state) (ordinal + 1) := by
  intro prior priorPresent earlier
  by_cases exactOrdinal : prior = ordinal
  · subst prior
    exact record_final_contents s layout trapdoor positions state ordinal present
      (boundary.start present) boundary.marks boundary.one
  · have prev : prior < ordinal := by omega
    exact earlier_record_preserved s layout trapdoor positions state ordinal prior present prev priorPresent
      boundary (contents prior priorPresent prev)

/-- The loop leaves the complete exact proof prefix in memory for all requested
positions, with the cap still to be appended. -/
theorem records_contents (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal remaining : Nat)
    (limit : ordinal + remaining ≤ positions.card)
    (boundary : RecordBoundary s trapdoor positions state ordinal)
    (contents : CompletedRecords s trapdoor positions state ordinal) :
    CompletedRecords s trapdoor positions (recordsMachine state remaining) (ordinal + remaining) := by
  induction remaining generalizing state ordinal with
  | zero => simpa only [recordsMachine, Nat.add_zero] using contents
  | succ remaining ih =>
    have present : ordinal < positions.card := by omega
    have next := record_boundary_next s layout trapdoor positions state ordinal present boundary
    have bytes := records_contents_next s layout trapdoor positions state ordinal present boundary contents
    have all := ih (recordMachine state) (ordinal + 1) (by omega) next bytes
    simpa only [recordsMachine, show ordinal + (remaining + 1) = ordinal + 1 + remaining by omega] using all

end TwoPermutationPrototype.Opening
