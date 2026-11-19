import CommitGolfCandidate.TwoPermutationPackedOpeningRecordsAPI

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Opening (OpeningLayout sortedIndex SameOpeningInput trapdoorBase proofBase RecordMarks)

attribute [local irreducible] execute

private theorem records_cost_next (size ordinal count : Nat) (limit : ordinal+(count+1) ≤ size) :
    recordsCost size ordinal (count+1) =
      recordCost (decide (ordinal+1=size))+recordsCost size (ordinal+1) count := by
  have sum : ordinal+(count+1)=ordinal+1+count := by omega
  by_cases last : ordinal+1=size
  · have empty : count = 0 := by omega
    subst count
    simp [recordsCost, recordCost, last]
  · by_cases finished : ordinal+(count+1)=size
    · have now : 0<count+1 ∧ ordinal+(count+1)=size := ⟨by omega, finished⟩
      have later : 0<count ∧ ordinal+1+count=size := ⟨by omega, by omega⟩
      simp only [recordsCost, ite_eq_left now, ite_eq_left later, recordCost,
        decide_eq_false last, Bool.false_eq_true, ite_false]
      omega
    · have now : ¬ (0<count+1 ∧ ordinal+(count+1)=size) := fun h => finished h.2
      have later : ¬ (0<count ∧ ordinal+1+count=size) := by omega
      simp only [recordsCost, ite_eq_right now, ite_eq_right later, recordCost,
        decide_eq_false last, Bool.false_eq_true, ite_false]
      omega

theorem same_input_byte {before after : MachineState} (unchanged : SameOpeningInput before after)
    (address : Nat) (above : trapdoorBase ≤ address) (below : address < proofBase) :
    after.getByte (BitVec.ofNat 64 address) = before.getByte (BitVec.ofNat 64 address) := by
  let aligned := alignToDword (BitVec.ofNat 64 address)
  have upper : aligned.toNat ≤ address := by
    unfold aligned alignToDword
    have limit : proofBase < 2^64 := by decide
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : address < 2^64)]
    exact Nat.and_le_left
  have lower : trapdoorBase ≤ aligned.toNat := by
    apply aligned_dword_above trapdoorBase address (by decide) above
    have : proofBase+8 ≤ 2^64 := by decide
    omega
  have stable := unchanged aligned.toNat lower (by omega)
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at stable
  change extractByte (after.getMem aligned) _ = _
  rw [stable]
  rfl

private theorem collected_record (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (before after : MachineState) (ordinal : Nat)
    (present : ordinal < positions.card) (start : RecordBoundary s trapdoor positions before ordinal)
    (step : OneRecord s trapdoor positions before after ordinal present)
    (earlier : CompletedRecords s trapdoor positions before ordinal) :
    CompletedRecords s trapdoor positions after (ordinal+1) := by
  intro prior priorPresent first
  let index := sortedIndex positions prior priorPresent
  have len : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have baseOrder : trapdoorBase ≤ proofBase := by decide
  by_cases current : prior = ordinal
  · subst prior
    constructor
    · intro byte hb
      have low : trapdoorBase ≤ nonceAddress index+byte := by
        unfold nonceAddress Opening.nonceBase
        omega
      have high : nonceAddress index+byte < proofBase := by
        have indexBound := index.isLt
        have tapeEnd := Opening.nonces_end_at_indices
        have order := Opening.indices_before_records
        unfold nonceAddress
        omega
      exact (step.nonce byte hb).trans (same_input_byte start.input _ low high)
    · intro level hl byte hb
      have low : trapdoorBase ≤ siblingAddress index level+byte := by unfold siblingAddress; omega
      have high : siblingAddress index level+byte < proofBase := by
        have bound := Opening.lower_swap_bound index level
        have heapEnd := Opening.heap_before_nonces
        have tapeEnd := Opening.nonces_end_at_indices
        have order := Opening.indices_before_records
        have widthBound : siblingWidth level ≤ 32 := by unfold siblingWidth; split <;> decide
        unfold siblingAddress
        omega
      exact (step.sibling level hl byte hb).trans (same_input_byte start.input _ low high)
  · have older : prior < ordinal := by omega
    obtain ⟨oldNonce, oldPath⟩ := earlier prior priorPresent older
    constructor
    · intro byte hb
      have limit := all_record_ends_fit ordinal (by omega)
      have low : trapdoorBase ≤ recordBase prior+byte := by unfold recordBase; omega
      have high : recordBase prior+byte < recordBase ordinal := by unfold recordBase recordBytes; omega
      have memory : recordBase ordinal ≤ MEMORY_BYTES := by
        unfold recordBase recordBytes at *
        omega
      exact (step.frame _ (by omega) low (Or.inl high)).trans (oldNonce byte hb)
    · intro level hl byte hb
      have fit := (all_sibling_copies_fit index prior level (by omega) hl).2.2.2
      have inPrior : siblingDestination prior level+byte < recordBase (prior+1) := by
        have stepOrder := destination_mono prior (show level+1 ≤ 16 by omega)
        rw [record_end] at stepOrder
        have successor : siblingDestination prior (level+1) =
            siblingDestination prior level + siblingWidth level := by
          simp only [siblingDestination, sibling_offset_next, Nat.add_assoc]
        omega
      have earlierThan : recordBase (prior+1) ≤ recordBase ordinal := by
        unfold recordBase recordBytes
        omega
      exact (step.frame _ (by omega) (by unfold siblingDestination recordBase; omega)
        (Or.inl (by omega))).trans (oldPath level hl byte hb)

theorem execute_records_from_step (execute_record : RecordExecute) (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal count : Nat) (limit : ordinal+count ≤ positions.card)
    (start : RecordBoundary s trapdoor positions state ordinal)
    (marks : RecordMarks positions state ordinal)
    (bytes : CompletedRecords s trapdoor positions state ordinal) :
    RecordsFinished s trapdoor positions state (runRecords positions.card ordinal count state) ordinal count := by
  induction count generalizing ordinal state with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro fuel coins
      simp [runRecords, recordsCost, Execution.charge]
    · simpa only [runRecords, Nat.add_zero] using start
    · simpa only [runRecords, Nat.add_zero] using marks
    · simpa only [runRecords, Nat.add_zero] using bytes
  | succ count ih =>
    have present : ordinal < positions.card := by omega
    let next := runRecord state (decide (ordinal+1=positions.card))
    have step := execute_record s layout trapdoor positions state ordinal present start
    have withMark : RecordMarks positions next (ordinal+1) := by
      intro node bounded
      rw [step.marks node bounded, marks node bounded, Opening.groups_before_next positions ordinal present]
      by_cases same : node = Sampling.capGroup (sortedIndex positions ordinal present)
      · simp [same]
      · simp [List.mem_append, same]
    have withBytes := collected_record s trapdoor positions state next ordinal present start step bytes
    have rest := ih next (ordinal+1) (by omega) step.next withMark withBytes
    have shift : ordinal+(count+1)=ordinal+1+count := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [records_cost_next _ _ _ limit]
      exact step.run.next rest.run
    · rw [shift]
      exact rest.boundary
    · rw [shift]
      exact rest.marks
    · rw [shift]
      exact rest.bytes

end TwoPermutationPrototype.PackedOpening
