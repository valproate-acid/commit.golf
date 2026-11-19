import CommitGolfCandidate.TwoPermutationPackedOpeningRecordsAPI

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Opening (OpeningLayout RecordMarks groupsBefore machineMarks markBase trapdoorBase indicesBase
  proofBase nat_address_injective)

/-- The cap occupancy array begins zero in the trusted ABI before any record. -/
theorem initial_mark_word (s : Submission) (layout : OpeningLayout s)
    (image : s.image .opening = openingImage) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) (node : Nat) (bounded : node < 512) :
    (s.initialState .opening (trapdoor, positions)).getMem
      (BitVec.ofNat 64 (markBase + 8 * node)) = 0 := by
  erw [initial_input_word s .opening (trapdoor, positions) _ (by
    unfold markBase
    omega)]
  have zero (j : Nat) (hj : j < 8) :
      inputByte s .opening (trapdoor, positions) (markBase + 8 * node + j) = 0 := by
    have before : ¬trapdoorBase ≤ markBase + 8 * node + j := by
      norm_num [markBase, trapdoorBase, LENGTH, LOG_LENGTH]
      omega
    have beforeIndices : ¬indicesBase ≤ markBase + 8 * node + j := by
      unfold indicesBase
      omega
    have beforeData : ¬dataBase openingImage ≤ markBase + 8 * node + j := by
      change ¬ MEMORY_BYTES ≤ markBase+8*node+j
      norm_num [MEMORY_BYTES, markBase]
      omega
    simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, positionsBuffer,
      layout.trapdoor, layout.indices, before, beforeIndices, false_and, decide_false,
      List.find?_nil, image, beforeData, ite_false]
  have total : (∑ j ∈ Finset.range 8,
      (inputByte s .opening (trapdoor, positions) (markBase + 8 * node + j)).toNat *
        2 ^ (8 * j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [zero j (Finset.mem_range.mp hj)]
    simp
  rw [total]
  rfl

theorem nonempty_count (positions : Positions) (nonempty : 0 < positions.card) :
    BitVec.ofNat 64 positions.card ≠ 0#64 := by
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  intro empty
  have zero := nat_address_injective (left := positions.card) (right := 0)
    (by norm_num [LENGTH, LOG_LENGTH] at cardinal; omega) (by decide) empty
  omega

theorem opening_first_boundary (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (nonempty : 0 < positions.card) :
    let initial := s.initialState .opening (trapdoor, positions)
    RecordBoundary s trapdoor positions (setupPrefix initial 13) 0 := by
  let initial := s.initialState .opening (trapdoor, positions)
  have start : initial.pc = 0x1000 := rfl
  have trapPointer : initial.getReg .x12 = BitVec.ofNat 64 trapdoorBase :=
    congrArg (BitVec.ofNat 64) layout.trapdoor
  have indexPointer : initial.getReg .x13 = BitVec.ofNat 64 indicesBase :=
    congrArg (BitVec.ofNat 64) layout.indices
  have proofPointer : initial.getReg .x15 = BitVec.ofNat 64 proofBase :=
    congrArg (BitVec.ofNat 64) layout.proof
  have countValue : initial.getReg .x16 = BitVec.ofNat 64 positions.card := rfl
  have ⟨proofStart, dest, ordinal, heap, count, size, nonce, one, capHeap, marks, capLeaves, memory⟩ :=
    setup_registers initial
  refine ⟨?_, heap.trans trapPointer, ?_, ?_, ?_, size, ?_, ?_, marks, one,
    capHeap.trans trapPointer, capLeaves, proofStart.trans proofPointer⟩
  · rw [ite_eq_right (show (0 : Nat) ≠ positions.card by omega)]
    exact setup_pc initial start (countValue ▸ nonempty_count positions nonempty)
  · simpa using ordinal.trans indexPointer
  · rw [nonce, trapPointer, ← BitVec.ofNat_add]
    rfl
  · simpa [recordBase] using dest.trans proofPointer
  · intro address _ _
    exact congrFun memory (BitVec.ofNat 64 address)
  · simpa using count.trans countValue

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

end TwoPermutationPrototype.PackedOpening
